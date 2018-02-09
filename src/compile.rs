// Copyright 2014-2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::collections::HashMap;
use std::iter;
use std::result;
use std::sync::Arc;

// Flip to true for debugging
const TRACE: bool = false;
macro_rules! trace {
    ($($tts:tt)*) => {
        if TRACE {
            println!($($tts)*);
        }
    }
}

use analisys::branches_have_inter_tsets;

use syntax::{
    Expr, Repeater, CharClass, ClassRange, ByteClass, ByteRange,
    is_word_byte, Literals, Lit, SyntaxVisitor, SyntaxVisitable
};
use utf8_ranges::{Utf8Range, Utf8Sequence, Utf8Sequences};

use prog::{
    Program, Inst, InstPtr, EmptyLook,
    InstSave, InstSplit, InstEmptyLook, InstChar, InstRanges, InstBytes,
    SkipInst, RUN_QUEUE_RING_SIZE, InstScanLiteral, InstByte, InstSkip
};

use literals::{LiteralSearcher};

use re_builder::{RegexOptions};

use Error;

type Result = result::Result<Patch, Error>;

#[derive(Debug)]
struct Patch {
    hole: Hole,
    entry: InstPtr,
}

/// A compiler translates a regular expression AST to a sequence of
/// instructions. The sequence of instructions represents an NFA.
pub struct Compiler {
    insts: Vec<MaybeInst<Inst, InstHole>>,
    skip_insts: Vec<MaybeInst<SkipInst, SkipInstHole>>,
    compiled: Program,
    capture_name_idx: HashMap<String, usize>,
    num_exprs: usize,
    suffix_cache: SuffixCache,
    utf8_seqs: Option<Utf8Sequences>,
    byte_classes: ByteClassSet,
    options: RegexOptions,
}

impl Compiler {
    /// Create a new regular expression compiler.
    ///
    /// Various options can be set before calling `compile` on an expression.
    pub fn new(options: RegexOptions) -> Self {
        Compiler {
            insts: vec![],
            skip_insts: vec![],
            compiled: Program::new(),
            capture_name_idx: HashMap::new(),
            num_exprs: 0,
            suffix_cache: SuffixCache::new(1000),
            utf8_seqs: Some(Utf8Sequences::new('\x00', '\x00')),
            byte_classes: ByteClassSet::new(),
            options: options,
        }
    }

    /// Make a new copy of the compiler with all the same configuration
    /// information, but an empty instruction list.
    fn copy_config(&self) -> Self {
        let c = Compiler {
            insts: vec![],
            skip_insts: vec![],
            compiled: Program::new(),
            capture_name_idx: HashMap::new(),
            num_exprs: self.num_exprs,
            suffix_cache: SuffixCache::new(1000),
            utf8_seqs: Some(Utf8Sequences::new('\x00', '\x00')),
            byte_classes: ByteClassSet::new(),
            options: self.options.clone(),
        };
        c
    }

    /// The size of the resulting program is limited by size_limit. If
    /// the program approximately exceeds the given size (in bytes), then
    /// compilation will stop and return an error.
    pub fn size_limit(mut self, size_limit: usize) -> Self {
        self.options.size_limit = size_limit;
        self
    }

    /// If true, the compiler will generate skip instructions.
    /// Defaults to false.
    pub fn has_skip_insts(mut self, has_skip_insts: bool) -> Self {
        self.options.skip_mode = has_skip_insts;
        self
    }

    /// If bytes is true, then the program is compiled as a byte based
    /// automaton, which incorporates UTF-8 decoding into the machine. If it's
    /// false, then the automaton is Unicode scalar value based, e.g., an
    /// engine utilizing such an automaton is resposible for UTF-8 decoding.
    ///
    /// The specific invariant is that when returning a byte based machine,
    /// the neither the `Char` nor `Ranges` instructions are produced.
    /// Conversely, when producing a Unicode scalar value machine, the `Bytes`
    /// instruction is never produced.
    ///
    /// Note that `dfa(true)` implies `bytes(true)`.
    pub fn bytes(mut self, yes: bool) -> Self {
        self.compiled.is_bytes = yes;
        self
    }

    /// When disabled, the program compiled may match arbitrary bytes.
    ///
    /// When enabled (the default), all compiled programs exclusively match
    /// valid UTF-8 bytes.
    pub fn only_utf8(mut self, yes: bool) -> Self {
        self.compiled.only_utf8 = yes;
        self
    }

    /// When set, the machine returned is suitable for use in the DFA matching
    /// engine.
    ///
    /// In particular, this ensures that if the regex is not anchored in the
    /// beginning, then a preceding `.*?` is included in the program. (The NFA
    /// based engines handle the preceding `.*?` explicitly, which is difficult
    /// or impossible in the DFA engine.)
    pub fn dfa(mut self, yes: bool) -> Self {
        self.compiled.is_dfa = yes;
        self
    }

    /// When set, the machine returned is suitable for matching text in
    /// reverse. In particular, all concatenations are flipped.
    pub fn reverse(mut self, yes: bool) -> Self {
        self.compiled.is_reverse = yes;
        self
    }

    /// Compile a regular expression given its AST.
    ///
    /// The compiler is guaranteed to succeed unless the program exceeds the
    /// specified size limit. If the size limit is exceeded, then compilation
    /// stops and returns an error.
    ///
    /// TODO(ethan): consider hiding skip compilation behind a flag
    /// like the .nfa() and .dfa() flags. Right now it is just piggybacking
    /// on the NFA (or actually possibly on both the NFA and the DFA).
    pub fn compile(
        mut self,
        exprs: &[Expr],
    ) -> result::Result<Program, Error> {
        trace!("::compile skip_flags={:?}", self.options.skip_flags);
        debug_assert!(exprs.len() >= 1);
        self.num_exprs = exprs.len();
        let res = if exprs.len() == 1 {
            self.compile_one(&exprs[0])
        } else {
            self.compile_many(exprs)
        };
        trace!("::compile finished");
        res
    }

    fn compile_one(mut self, expr: &Expr) -> result::Result<Program, Error> {
        // If we're compiling a forward DFA and we aren't anchored, then
        // add a `.*?` before the first capture group.
        // Other matching engines handle this by baking the logic into the
        // matching engine itself.
        // println!("Compiling: {:?}", expr);
        let mut dotstar_patch = Patch { hole: Hole::None, entry: 0 };
        self.compiled.is_anchored_start = expr.is_anchored_start();
        self.compiled.is_anchored_end = expr.is_anchored_end();
        if self.compiled.needs_dotstar() {
            dotstar_patch = try!(self.c_dotstar());
            self.compiled.start = dotstar_patch.entry;
        }
        self.compiled.captures = vec![None];
        let patch = try!(self.c_capture(0, expr));
        if self.compiled.needs_dotstar() {
            self.fill(dotstar_patch.hole, patch.entry);
        } else {
            self.compiled.start = patch.entry;
        }
        self.fill_to_next(patch.hole);
        self.compiled.matches = vec![self.insts.len()];
        self.push_compiled(Inst::Match(0));

        if self.options.skip_mode {
            try!(self.sc_compile_one(expr));
        }

        let res = self.compile_finish();
        trace!("::compile_one finished");
        res
    }

    fn sc_compile_one(&mut self, expr: &Expr) -> result::Result<(), Error> {
        trace!("::sc_compile_one {:?}", expr);

        // if required, start the party with a dotstar
        let mut sc_dotstar_patch = Patch { hole: Hole::None, entry: 0 };
        if self.compiled.needs_dotstar() {
            sc_dotstar_patch = try!(self.sc_dotstar(INIT_SC_CTX));
        }

        // compile the actual expression
        let sc_patch = try!(self.sc_capture(INIT_SC_CTX, 0, |c| {
            c.sc(INIT_SC_CTX, expr)
        }));

        // fuse the leading dotstar with the inner expression,
        // if required.
        if self.compiled.needs_dotstar() {
            self.sc_fill(sc_dotstar_patch.hole, sc_patch.entry);
        } else {
            self.compiled.skip_start = sc_patch.entry;
        }

        // wind down the proceedings with a match instruction.
        let sc_next = self.sc_push_compiled(SkipInst::SkipMatch(0));
        self.sc_continue(sc_patch, sc_next);

        trace!("::sc_compile_one finished");
        Ok(())
    }

    fn compile_many(
        mut self,
        exprs: &[Expr],
    ) -> result::Result<Program, Error> {
        debug_assert!(exprs.len() > 1);

        self.compiled.is_anchored_start =
            exprs.iter().all(|e| e.is_anchored_start());
        self.compiled.is_anchored_end =
            exprs.iter().all(|e| e.is_anchored_end());
        let mut dotstar_patch = Patch { hole: Hole::None, entry: 0 };
        if self.compiled.needs_dotstar() {
            dotstar_patch = try!(self.c_dotstar());
            self.compiled.start = dotstar_patch.entry;
        } else {
            self.compiled.start = 0; // first instruction is always split
        }
        self.fill_to_next(dotstar_patch.hole);

        let mut prev_hole = Hole::None;
        for (i, expr) in exprs[0..exprs.len() - 1].iter().enumerate() {
            self.fill_to_next(prev_hole);
            let split = self.push_split_hole();
            let Patch { hole, entry } = try!(self.c_capture(0, expr));
            self.fill_to_next(hole);
            self.compiled.matches.push(self.insts.len());
            self.push_compiled(Inst::Match(i));
            prev_hole = self.fill_split(split, Some(entry), None);
        }
        let i = exprs.len() - 1;
        let Patch { hole, entry } = try!(self.c_capture(0, &exprs[i]));
        self.fill(prev_hole, entry);
        self.fill_to_next(hole);
        self.compiled.matches.push(self.insts.len());
        self.push_compiled(Inst::Match(i));
        self.compile_finish()
    }

    fn compile_finish(mut self) -> result::Result<Program, Error> {
        self.compiled.insts =
            self.insts.into_iter().map(|inst| inst.unwrap()).collect();
        self.compiled.skip_insts =
            self.skip_insts.into_iter().map(|si| si.unwrap()).collect();
        self.compiled.byte_classes = self.byte_classes.byte_classes();
        self.compiled.capture_name_idx = Arc::new(self.capture_name_idx);
        self.compiled.has_skip_insts = self.options.skip_mode;
        Ok(self.compiled)
    }

    fn c(&mut self, expr: &Expr) -> Result {
        use prog;
        use syntax::Expr::*;

        try!(self.check_size());
        match *expr {
            Empty => Ok(Patch { hole: Hole::None, entry: self.insts.len() }),
            Literal { ref chars, casei } => self.c_literal(chars, casei),
            LiteralBytes { ref bytes, casei } => self.c_bytes(bytes, casei),
            AnyChar => self.c_class(&[ClassRange {
                start: '\x00',
                end: '\u{10ffff}',
            }]),
            AnyCharNoNL => {
                self.c_class(&[
                    ClassRange { start: '\x00', end: '\x09' },
                    ClassRange { start: '\x0b', end: '\u{10ffff}' },
                ])
            }
            AnyByte => {
                self.c_class_bytes(&[ByteRange { start: 0, end: 0xFF }])
            }
            AnyByteNoNL => {
                self.c_class_bytes(&[
                    ByteRange { start: 0, end: 0x9 },
                    ByteRange { start: 0xB, end: 0xFF },
                ])
            }
            Class(ref cls) => {
                self.c_class(cls)
            }
            ClassBytes(ref cls) => {
                self.c_class_bytes(cls)
            }
            StartLine if self.compiled.is_reverse => {
                self.byte_classes.set_range(b'\n', b'\n');
                self.c_empty_look(prog::EmptyLook::EndLine)
            }
            StartLine => {
                self.byte_classes.set_range(b'\n', b'\n');
                self.c_empty_look(prog::EmptyLook::StartLine)
            }
            EndLine if self.compiled.is_reverse => {
                self.byte_classes.set_range(b'\n', b'\n');
                self.c_empty_look(prog::EmptyLook::StartLine)
            }
            EndLine => {
                self.byte_classes.set_range(b'\n', b'\n');
                self.c_empty_look(prog::EmptyLook::EndLine)
            }
            StartText if self.compiled.is_reverse => {
                self.c_empty_look(prog::EmptyLook::EndText)
            }
            StartText => {
                self.c_empty_look(prog::EmptyLook::StartText)
            }
            EndText if self.compiled.is_reverse => {
                self.c_empty_look(prog::EmptyLook::StartText)
            }
            EndText => {
                self.c_empty_look(prog::EmptyLook::EndText)
            }
            WordBoundary => {
                self.compiled.has_unicode_word_boundary = true;
                self.byte_classes.set_word_boundary();
                self.c_empty_look(prog::EmptyLook::WordBoundary)
            }
            NotWordBoundary => {
                self.compiled.has_unicode_word_boundary = true;
                self.byte_classes.set_word_boundary();
                self.c_empty_look(prog::EmptyLook::NotWordBoundary)
            }
            WordBoundaryAscii => {
                self.byte_classes.set_word_boundary();
                self.c_empty_look(prog::EmptyLook::WordBoundaryAscii)
            }
            NotWordBoundaryAscii => {
                self.byte_classes.set_word_boundary();
                self.c_empty_look(prog::EmptyLook::NotWordBoundaryAscii)
            }
            Group { ref e, i: None, name: None } => self.c(e),
            Group { ref e, i, ref name } => {
                // it's impossible to have a named capture without an index
                let i = i.expect("capture index");
                if i >= self.compiled.captures.len() {
                    self.compiled.captures.push(name.clone());
                    if let Some(ref name) = *name {
                        self.capture_name_idx.insert(name.to_owned(), i);
                    }
                }
                self.c_capture(2 * i, e)
            }
            Concat(ref es) => {
                if self.compiled.is_reverse {
                    self.c_concat(es.iter().rev())
                } else {
                    self.c_concat(es)
                }
            }
            Alternate(ref es) => self.c_alternate(&**es),
            Repeat { ref e, r, greedy } => self.c_repeat(e, r, greedy),
        }
    }

    fn sc(&mut self, ctx: SkipCompilerContext, expr: &Expr) -> Result {
        use syntax::Expr::*;

        trace!("::sc expr={:?}", expr);

        try!(self.check_size());
        match *expr {
            Empty => Ok(Patch { hole: Hole::None, entry: self.insts.len() }),
            Literal { ref chars, casei } =>
                self.sc_literal(ctx, chars, casei),
            LiteralBytes { ref bytes, casei } =>
                self.sc_bytes(ctx, bytes, casei),
            Repeat { ref e, r, greedy } => self.sc_repeat(ctx, e, r, greedy),
            AnyChar => self.sc_class(ctx, &[ClassRange {
                // For now we just support ascii. In the event that we
                // add unicode support, this range should be fixed to
                // refelct that.
                //
                // TODO(ethan):unicode
                start: '\x00',
                end: '\x7F'
            }]),

            // TODO(ethan):unicode
            AnyCharNoNL => self.sc_class(ctx, &[ClassRange {
                start: '\x00',
                end: '\x09'
            }, ClassRange { // ranges are inclusive on both ends
                start: '\x0B',
                end: '\x7F'
            }]),
            AnyByte => self.sc_class_bytes(ctx, &[
                ByteRange { start: 0, end: 0xFF, }
            ]),
            AnyByteNoNL => self.sc_class_bytes(ctx, &[
                ByteRange { start: 0x00, end: 0x09, },
                ByteRange { start: 0x0B, end: 0xFF, }
            ]),
            Concat(ref es) => {
                if self.compiled.is_reverse {
                    self.sc_concat(ctx, es.iter().rev())
                } else {
                    self.sc_concat(ctx, es)
                }
            }
            Group { ref e, i: None, name: None } => self.sc(ctx, e),
            Group { ref e, i, ref name } => {
                // it's impossible to have a named capture without an index
                let i = i.expect("capture index");
                if i >= self.compiled.captures.len() {
                    self.compiled.captures.push(name.clone());
                    if let Some(ref name) = *name {
                        self.capture_name_idx.insert(name.to_owned(), i);
                    }
                }
                self.sc_capture(ctx, 2 * i, |c| { c.sc(ctx, e) })
            }
            Alternate(ref es) => self.sc_alternate(ctx, &**es),
            Class(ref class) => self.sc_class(ctx, class),
            ClassBytes(ref class) => self.sc_class_bytes(ctx, class),
            ref e => unreachable!("Unimplimented instruction: {:?}", e),
        }
    }

    fn c_capture(&mut self, first_slot: usize, expr: &Expr) -> Result {
        if self.num_exprs > 1 || self.compiled.is_dfa {
            // Don't ever compile Save instructions for regex sets because
            // they are never used. They are also never used in DFA programs
            // because DFAs can't handle captures.
            self.c(expr)
        } else {
            let entry = self.insts.len();
            let hole = self.push_hole(InstHole::Save { slot: first_slot });
            let patch = try!(self.c(expr));
            self.fill(hole, patch.entry);
            self.fill_to_next(patch.hole);
            let hole = self.push_hole(InstHole::Save { slot: first_slot + 1 });
            Ok(Patch { hole: hole, entry: entry })
        }
    }

    fn sc_capture<F>(
        &mut self,
        _ctx: SkipCompilerContext,
        first_slot: usize,
        compile_inner: F,
    ) -> Result
        where F: FnOnce(&mut Self) -> Result
    {
        trace!("::sc_capture first_slot={}", first_slot);

        if self.num_exprs > 1 || self.compiled.is_dfa {
            compile_inner(self)
        } else {
            let p = self.sc_push_one(SkipInstHole::Save {
                slot: first_slot
            });

            let next = try!(compile_inner(self));
            let p = self.sc_continue(p, next);

            let next = self.sc_push_one(SkipInstHole:: Save {
                slot: first_slot + 1
            });
            Ok(self.sc_continue(p, next))
        }
    }

    fn c_dotstar(&mut self) -> Result {
        Ok(if !self.compiled.only_utf8() {
            try!(self.c(&Expr::Repeat {
                e: Box::new(Expr::AnyByte),
                r: Repeater::ZeroOrMore,
                greedy: false,
            }))
        } else {
            try!(self.c(&Expr::Repeat {
                e: Box::new(Expr::AnyChar),
                r: Repeater::ZeroOrMore,
                greedy: false,
            }))
        })
    }

    /// compile .*? onto the Skip Regex
    fn sc_dotstar(&mut self, ctx: SkipCompilerContext) -> Result {
        trace!("::sc_dotstar");

        Ok(if !self.compiled.only_utf8() {
            try!(self.sc(ctx, &Expr::Repeat {
                e: Box::new(Expr::AnyByte),
                r: Repeater::ZeroOrMore,
                greedy: false,
            }))
        } else {
            try!(self.sc(ctx, &Expr::Repeat {
                e: Box::new(Expr::AnyChar),
                r: Repeater::ZeroOrMore,
                greedy: false,
            }))
        })
    }

    fn c_literal(&mut self, chars: &[char], casei: bool) -> Result {
        debug_assert!(!chars.is_empty());
        let mut chars: Box<Iterator<Item=&char>> =
            if self.compiled.is_reverse {
                Box::new(chars.iter().rev())
            } else {
                Box::new(chars.iter())
            };
        let first = *chars.next().expect("non-empty literal");
        let Patch { mut hole, entry } = try!(self.c_char(first, casei));
        for &c in chars {
            let p = try!(self.c_char(c, casei));
            self.fill(hole, p.entry);
            hole = p.hole;
        }
        Ok(Patch { hole: hole, entry: entry })
    }

    /// Compile a literal into a skip. This routine must not
    /// be used to compile a literal at the start of a branch.
    fn sc_literal(
        &mut self,
        ctx: SkipCompilerContext,
        chars: &[char],
        casei: bool,
    ) -> Result {
        trace!("::sc_literal chars={:?}", chars);
        // TODO(ethan):casei does not support case insensitivity

        let bytes = chars.into_iter().map(|c| {
            if c.is_ascii() {
                let mut b = [0; 1];
                c.encode_utf8(&mut b);
                Some(b[0])
            } else {
                None
            }
        }).collect::<Option<Vec<u8>>>();

        match bytes {
            Some(b) => self.sc_bytes(ctx, &b, casei),
            None => Err(Error::SkipUnsupported(String::from("utf8"))),
        }
    }

    fn c_char(&mut self, c: char, casei: bool) -> Result {
        if casei {
            self.c_class(&CharClass::new(vec![
                ClassRange { start: c, end: c },
            ]).case_fold())
        } else {
            self.c_class(&[ClassRange { start: c, end: c }])
        }
    }

    fn c_class(&mut self, ranges: &[ClassRange]) -> Result {
        assert!(!ranges.is_empty());
        if self.compiled.uses_bytes() {
            CompileClass {
                c: self,
                ranges: ranges,
            }.compile()
        } else {
            let ranges: Vec<(char, char)> =
                ranges.iter().map(|r| (r.start, r.end)).collect();
            let hole = if ranges.len() == 1 && ranges[0].0 == ranges[0].1 {
                self.push_hole(InstHole::Char { c: ranges[0].0 })
            } else {
                self.push_hole(InstHole::Ranges { ranges: ranges })
            };
            Ok(Patch { hole: hole, entry: self.insts.len() - 1 })
        }
    }

    fn sc_class(
        &mut self, 
        ctx: SkipCompilerContext,
        ranges: &[ClassRange]
    ) -> Result {
        trace!("::sc_class {:?}", ranges);
        debug_assert!(!ranges.is_empty());

        let ranges: Vec<ByteRange> = try!(ranges.iter().map(|r| {
            if !(r.start.is_ascii() && r.end.is_ascii()) {
                return Err(Error::SkipUnsupported(String::from("utf8")));
            }

            let mut b1 = [0; 1];
            r.start.encode_utf8(&mut b1);

            let mut b2 = [0; 1];
            r.end.encode_utf8(&mut b2);

            Ok(ByteRange { start: b1[0], end: b2[0] })
        }).collect::<result::Result<Vec<ByteRange>, Error>>());

        self.sc_class_bytes(ctx, &ranges)
    }

    fn c_bytes(&mut self, bytes: &[u8], casei: bool) -> Result {
        debug_assert!(!bytes.is_empty());
        let mut bytes: Box<Iterator<Item=&u8>> =
            if self.compiled.is_reverse {
                Box::new(bytes.iter().rev())
            } else {
                Box::new(bytes.iter())
            };
        let first = *bytes.next().expect("non-empty literal");
        let Patch { mut hole, entry } = try!(self.c_byte(first, casei));
        for &b in bytes {
            let p = try!(self.c_byte(b, casei));
            self.fill(hole, p.entry);
            hole = p.hole;
        }
        Ok(Patch { hole: hole, entry: entry })
    }

    /// Compile a literal into a skip. This routine must not
    /// be used to compile a literal at the start of a branch.
    fn sc_bytes(
        &mut self,
        ctx: SkipCompilerContext,
        bytes: &[u8],
        _casei: bool,
    ) -> Result {
        trace!("::sc_bytes chars={:?}", bytes);
        // TODO(ethan):casei does not support case insensitivity

        let max_skip = RUN_QUEUE_RING_SIZE - 1;

        let mut p = Patch { hole: Hole::None, entry: self.sc_next() };

        if ctx.branch_type == BranchType::Intersecting 
            || !self.options.skip_flags.skip_lit {
            // If we are in an intersecting branch situation, we have to
            // fall back to the default behavior.
            for b in bytes {
                let next = self.sc_push_one(SkipInstHole::Byte { c: *b });
                p = self.sc_continue(p, next);
            }
        } else {
            // If we are in a NoBranch or NonIntersecting situation,
            // literals compile down to a skip (possibly with a test
            // for the first char).
            let mut skip_start = 0;

            if ctx.branch_type == BranchType::NonIntersecting {
                let next = self.sc_push_one(SkipInstHole::Byte { c: bytes[0] });
                p = self.sc_continue(p, next);
                skip_start += 1;
            }

            while skip_start < bytes.len() {
                let next = self.sc_push_one(SkipInstHole::Skip {
                    skip: if bytes.len() - skip_start > max_skip {
                              max_skip
                          } else {
                              bytes.len() - skip_start
                          }
                });
                p = self.sc_continue(p, next);

                skip_start += max_skip;
            }
        }

        Ok(p)
    }

    fn c_byte(&mut self, b: u8, casei: bool) -> Result {
        if casei {
            self.c_class_bytes(&ByteClass::new(vec![
                ByteRange { start: b, end: b },
            ]).case_fold())
        } else {
            self.c_class_bytes(&[ByteRange { start: b, end: b }])
        }
    }

    fn c_class_bytes(&mut self, ranges: &[ByteRange]) -> Result {
        debug_assert!(!ranges.is_empty());

        let first_split_entry = self.insts.len();
        let mut holes = vec![];
        let mut prev_hole = Hole::None;
        for r in &ranges[0..ranges.len() - 1] {
            self.fill_to_next(prev_hole);
            let split = self.push_split_hole();
            let next = self.insts.len();
            self.byte_classes.set_range(r.start, r.end);
            holes.push(self.push_hole(InstHole::Bytes {
                start: r.start, end: r.end,
            }));
            prev_hole = self.fill_split(split, Some(next), None);
        }
        let next = self.insts.len();
        let r = &ranges[ranges.len() - 1];
        self.byte_classes.set_range(r.start, r.end);
        holes.push(self.push_hole(InstHole::Bytes {
            start: r.start, end: r.end,
        }));
        self.fill(prev_hole, next);
        Ok(Patch { hole: Hole::Many(holes), entry: first_split_entry })
    }

    fn sc_class_bytes(
        &mut self, 
        _ctx: SkipCompilerContext,
        ranges: &[ByteRange]
    ) -> Result {
        trace!("::sc_class_bytes {:?}", ranges);
        debug_assert!(!ranges.is_empty());

        if ranges.len() == 1 && ranges[0].start == ranges[0].end {
            return Ok(self.sc_push_one(SkipInstHole::Byte {
                c: ranges[0].start
            }));
        }
            
        let mut holes = vec![];

        let mut p = Patch { hole: Hole::None, entry: self.sc_next() };
        for r in ranges[0..ranges.len() - 1].iter() {
            let Patch { hole: split_hole, entry: split_entry } =
                    self.sc_push_split_patch();

            let inner = self.sc_push_one(SkipInstHole::Bytes {
                start: r.start,
                end: r.end,
            });
            let half_split =
                self.sc_fill_split(split_hole, Some(inner.entry), None);
            holes.push(inner.hole);

            p = self.sc_continue(p, Patch {
                hole: half_split,
                entry: split_entry
            });
        }

        trace!("::sc_class_bytes wired together ranges");

        // the last expression does not get a branch
        let last_r = &ranges[ranges.len() - 1];
        let next = self.sc_push_one(SkipInstHole::Bytes {
            start: last_r.start,
            end: last_r.end,
        });
        p = self.sc_continue(p, next);
        holes.push(p.hole);

        trace!("::sc_class_bytes finished last range");

        Ok(Patch { hole: Hole::Many(holes), entry: p.entry })
    }

    fn c_empty_look(&mut self, look: EmptyLook) -> Result {
        let hole = self.push_hole(InstHole::EmptyLook { look: look });
        Ok(Patch { hole: hole, entry: self.insts.len() - 1 })
    }

    fn c_concat<'a, I>(&mut self, exprs: I) -> Result
            where I: IntoIterator<Item=&'a Expr> {
        let mut exprs = exprs.into_iter();
        let first = match exprs.next() {
            Some(expr) => expr,
            None => {
                return Ok(Patch { hole: Hole::None, entry: self.insts.len() })
            }
        };
        let Patch { mut hole, entry } = try!(self.c(first));
        for e in exprs {
            let p = try!(self.c(e));
            self.fill(hole, p.entry);
            hole = p.hole;
        }
        Ok(Patch { hole: hole, entry: entry })
    }

    fn sc_concat<'a, I>(
        &mut self, 
        mut ctx: SkipCompilerContext,
        exprs: I
    ) -> Result
        where I: IntoIterator<Item=&'a Expr>
    {
        trace!("::sc_concat");
        use syntax::Expr::*;

        // we don't have to do any skip fusion here because the
        // literal parser has already done that for us.
        let mut p = Patch { hole: Hole::None, entry: self.sc_next() };

        // We don't immediatly compile repetitions because they might
        // have a terminator that we can scan forward to. Instead we
        // accumulate them in a vector.
        let mut repeats = vec![];
        for (i, e) in exprs.into_iter().enumerate() {
            match e {
                rep @ &Repeat { e: _, r: _, greedy: _ } => {
                    repeats.push(rep);
                }
                _ => {
                    if repeats.len() > 0 {
                        let next = try!(self.sc_terminated_repeats(ctx, &repeats, e));
                        p = self.sc_continue(p, next);
                        repeats.clear();
                    } else {
                        let next = try!(self.sc(ctx, e));
                        p = self.sc_continue(p, next);
                    }
                }
            }

            // After we've compiled the first char, we can revert
            // NonIntersecting branches to NoBranch branches
            if i == 0 {
                ctx.branch_type = match ctx.branch_type {
                    BranchType::NonIntersecting => BranchType::NoBranch,
                    bt => bt,
                };
            }
        }

        // drain any unterminated repetitions
        for r in repeats {
            let next = try!(self.sc(ctx, r));
            p = self.sc_continue(p, next);
        }

        Ok(p)
    }

    /// If a repetition is terminated by a literal, we can always
    /// just scan forward for that literal and then non-deterministicly
    /// continue scanning from the start of the repetition (in case that
    /// literal showed up inside the repeated string) and the end of
    /// the literal.
    ///
    /// If we can prove that the literal cannot appear within the repetition
    /// we can even drop the non-determinism and just start scanning from
    /// the end of the literal.
    ///
    /// The default case:
    ///   *-scan_to_end_of_term-*
    ///   ^                     |
    ///   |---------------------|
    ///
    /// The optimal case:
    ///   *-scan_to_end_of_term-*
    ///
    fn sc_terminated_repeats(
        &mut self,
        ctx: SkipCompilerContext,
        repeats: &[&Expr],
        term: &Expr
    ) -> Result {
        trace!("::sc_terminated_repeats");
        use std::ops::Deref;
        use syntax::Expr::*;

        let greedy = match repeats.last() {
            Some(& &Repeat { e: _, r: _, greedy: g }) => g,
            _ => unreachable!("last repeat is not a repeat after all!"),
        };

        // for program analisys, not for the final result
        let repeats_program = try!(self.compile_repeats_prog(repeats));

        let can_opt_dotstar_term = 
            self.options.skip_flags.dotstar_term
            && repeats.iter().all(|e| self.expr_is_repeated_any(e));
        trace!("::sc_terminated_repeats can_opt_dotstar_term={}",
                can_opt_dotstar_term);

        let mut p = Patch { hole: Hole::None, entry: self.sc_next() };

        // if any of the repetitions contain a capture, we can't handle it.
        let can_scan = ! repeats.iter()
                                .any(|e| ContainsCaptureVisitor::check(*e));
        let can_scan = can_scan && match term {
            // TODO(ethan): case sensativity
            &Literal { ref chars, casei: _ } => {
                trace!("::sc_terminated_repeats literal branch");
                if !can_opt_dotstar_term
                    && try!(self.lit_in_repeats(&repeats_program, &term)) {
                    false
                } else {
                    let next = self.sc_literal_scan(
                        ctx, chars, false, can_opt_dotstar_term, greedy);
                    p = self.sc_continue(p, next);
                    true
                }
            }
            &Group { ref e, i: Some(idx), ref name } => {
                trace!("::sc_terminated_repeats group branch");
                match e.deref() {
                    &Literal { ref chars, casei } => {
                        trace!("::sc_terminated_repeats group-literal branch");
                        if !can_opt_dotstar_term
                            && try!(self.lit_in_repeats(&repeats_program, &term)) {
                            false
                        } else {
                            if idx >= self.compiled.captures.len() {
                                self.compiled.captures.push(name.clone());
                                if let Some(ref name) = *name {
                                    self.capture_name_idx
                                        .insert(name.to_owned(), idx);
                                }
                            }

                            // First emit the literal scan, asking the scanner
                            // to drop us right at the start of the literal
                            let next = self.sc_literal_scan(
                                ctx, chars, true, can_opt_dotstar_term, greedy);
                            p = self.sc_continue(p, next);

                            let mut nb_ctx = ctx;
                            nb_ctx.branch_type = BranchType::NoBranch;

                            // Now emit the capturing scan while jumping
                            // over the literal itself.
                            let next = try!(self.sc_capture(ctx, 2 * idx, |c| {
                                // We can never be in branch position here.
                                // We already found the literal.
                                c.sc_literal(nb_ctx, chars, casei)
                            }));
                            p = self.sc_continue(p, next);

                            true
                        }
                    }
                    _ => false
                }
            }
            // TODO(ethan): Add support for terminating literal sets,
            //              like /a*(bbbbb|ccccc)/ OR /a*bbbbb|ccccc/
            _ => false
        };

        trace!("::sc_terminated_repeats compiled scan ({})", can_scan);

        if !can_scan {
            // Set up the list of expressions in branch position, and
            // check them for intersections
            let mut branches: Vec<&Expr> =
                repeats.into_iter().map(|x| *x).collect();
            branches.push(&term);
            let mut new_ctx = ctx;
            new_ctx.branch_type = ctx.branch_type.try_promote(
                if branches_have_inter_tsets(&branches) {
                    BranchType::Intersecting
                } else {
                    BranchType::NonIntersecting
                });

            // a list of just repetitions (no terminator) will terminate the
            // mutal recursion.
            let next = try!(self.sc_concat(new_ctx, repeats.into_iter().map(|x| *x)));
            p = self.sc_continue(p, next);

            // The expression which terminates a repeat instruction is
            // in branch position.
            let next = try!(self.sc(new_ctx, term));
            p = self.sc_continue(p, next);
        }

        Ok(p)
    }

    fn lit_in_repeats(
        &self,
        repeats: &Option<Program>,
        lit: &Expr
    ) -> result::Result<bool, Error> {
        trace!("::lit_in_repeats");
        use syntax::Expr::{Concat, AnyChar, Repeat};

        // We can turn off the /e*term/ optimization by just
        // claiming that the terminator is always contained
        // in the repetition program.
        if !self.options.skip_flags.estar_term {
            return Ok(true)
        }

        match repeats {
            // /.*/ is represented as None to avoid an infinite
            // recursion. It can always contain any literal.
            // This case shouldn't come up unless the .* optimization
            // is turned off.
            &None => Ok(true),
            &Some(ref repeats_prog) => {
                let dotstar = Repeat {
                    e: Box::new(AnyChar),
                    r: Repeater::ZeroOrMore,
                    greedy: true
                };

                let lit_program = try!(self.copy_config()
                    .compile_one(&Concat(vec![
                         dotstar.clone(),
                         (*lit).clone(),
                         dotstar])));

                Ok(!Program::intersection_is_empty(
                            repeats_prog, &lit_program))
            }
        }
    }

    /// Given a list of repetition expressions, compile its program.
    ///
    /// If `repeats` == /.*/, we return None. This repetition is special
    /// because we wrap the literals in dotstars when checking intersection,
    /// so we need to avoid an infinite recursion.
    fn compile_repeats_prog(
        &self,
        repeats: &[&Expr]
    ) -> result::Result<Option<Program>, Error> {
        use syntax::Expr::{Concat};

        if repeats.len() == 1 && self.expr_is_repeated_any(repeats[0]) {
            return Ok(None);
        }

        self.copy_config()
            .compile_one(&Concat(repeats.iter()
                .map(|x| (**x).clone())
                .collect())).map(Some)
    }

    /// A predicate to test if an expression is a repetition of
    /// AnyChar (/.*/, /.+/, /.*?/, /.+?/).
    fn expr_is_repeated_any(&self, e: &Expr) -> bool {
        use syntax::Expr::{Repeat, AnyChar, AnyCharNoNL, AnyByte, AnyByteNoNL};
        use syntax::Repeater::{ZeroOrMore, OneOrMore};

        match e {
            &Repeat { e: ref inner, r, greedy: _ }
                if (**inner == AnyChar || **inner == AnyCharNoNL
                    || **inner == AnyByte || **inner == AnyByteNoNL)
                  && (r == ZeroOrMore || r == OneOrMore) => true,
            _ => false,
        }
    }

    /// Emit a literal scan instruction and various window dressing
    /// depending on the flags below.
    ///
    /// `chars` - The literal to scan forward to.
    /// `start` - If true, drop us off at the start of the literal at
    ///           the end of the scan (drop us off at the end otherwise).
    /// `branch` - If true, non-deterministicly branch back to the start
    ///            after a scan.
    /// `greedy` - True if the last repeat before the literal is a greedy
    ///            repetition. Determines the order of the branch gotos.
    fn sc_literal_scan(
        &mut self,
        _ctx: SkipCompilerContext,
        chars: &Vec<char>,
        start: bool,
        branch: bool,
        greedy: bool, 
        ) -> Patch
    {
        trace!("::sc_literal_scan");
        // First, emit the scan instruction.
        let mut lits = Literals::empty();
        lits.add(Lit::new(Vec::from(
                     chars.into_iter().collect::<String>().as_bytes())));
        let scan = self.sc_push_one(SkipInstHole::ScanLiteral {
            literal: LiteralSearcher::prefixes(lits),
            start: start,
        });

        if branch {
            // Now non-deterministicly branch back to the start.
            let Patch { hole: split_hole, entry: split_entry } =
                self.sc_push_split_patch();

            let split_hole = if greedy {
                self.sc_fill_split(split_hole, Some(scan.entry), None)
            } else {
                self.sc_fill_split(split_hole, None, Some(scan.entry))
            };

            self.sc_continue(scan, Patch {
                hole: split_hole,
                entry: split_entry,
            })
        } else {
            scan
        }
    }


    fn c_alternate(&mut self, exprs: &[Expr]) -> Result {
        debug_assert!(
            exprs.len() >= 2, "alternates must have at least 2 exprs");

        // Initial entry point is always the first split.
        let first_split_entry = self.insts.len();

        // Save up all of the holes from each alternate. They will all get
        // patched to point to the same location.
        let mut holes = vec![];

        let mut prev_hole = Hole::None;
        for e in &exprs[0..exprs.len() - 1] {
            self.fill_to_next(prev_hole);
            let split = self.push_split_hole();
            let Patch { hole, entry } = try!(self.c(e));
            holes.push(hole);
            prev_hole = self.fill_split(split, Some(entry), None);
        }
        let Patch { hole, entry } = try!(self.c(&exprs[exprs.len() - 1]));
        holes.push(hole);
        self.fill(prev_hole, entry);
        Ok(Patch { hole: Hole::Many(holes), entry: first_split_entry })
    }

    /// compile expr1|expr2|expr3| ... |exprn
    ///
    /// Each expression is prefixed with a split. One branch
    /// points to the next expression, while the other points
    /// to the start of next expression. The tail goto of each
    /// expression points to the end of the alt.
    ///
    /// The last expression is handled a little differently, because
    /// we don't want to provide a split path around it.
    fn sc_alternate(
        &mut self, 
        ctx: SkipCompilerContext,
        exprs: &[Expr]
    ) -> Result {
        trace!("::sc_alternate");
        debug_assert!(
            exprs.len() >= 2, "alternates must have at least 2 exprs");

        let mut holes = vec![];

        let mut new_ctx = ctx;
        new_ctx.branch_type = ctx.branch_type.try_promote(
            if branches_have_inter_tsets(&exprs.iter().collect::<Vec<_>>()) {
                BranchType::Intersecting
            } else {
                BranchType::NonIntersecting
            });

        trace!("::sc_alternate branch-type={:?}", new_ctx.branch_type);

        let mut p = Patch { hole: Hole::None, entry: self.sc_next() };
        for e in exprs[0..exprs.len() - 1].iter() {
            let Patch { hole: split_hole, entry: split_entry } =
                    self.sc_push_split_patch();

            let inner = try!(self.sc(new_ctx, e));
            let half_split =
                self.sc_fill_split(split_hole, Some(inner.entry), None);
            holes.push(inner.hole);

            p = self.sc_continue(p, Patch {
                hole: half_split,
                entry: split_entry
            });
        }

        // the last expression does not get a branch
        // TODO(ethan): in some cases we don't have to compile the
        //              last expression as a skip.
        let last_e = &exprs[exprs.len() - 1];
        let next = try!(self.sc(new_ctx, last_e));
        p = self.sc_continue(p, next);
        holes.push(p.hole);

        Ok(Patch { hole: Hole::Many(holes), entry: p.entry })
    }

    fn c_repeat(
        &mut self,
        expr: &Expr,
        kind: Repeater,
        greedy: bool,
    ) -> Result {
        match kind {
            Repeater::ZeroOrOne => self.c_repeat_zero_or_one(expr, greedy),
            Repeater::ZeroOrMore => self.c_repeat_zero_or_more(expr, greedy),
            Repeater::OneOrMore => self.c_repeat_one_or_more(expr, greedy),
            Repeater::Range { min, max: None } => {
                self.c_repeat_range_min_or_more(expr, greedy, min)
            }
            Repeater::Range { min, max: Some(max) } => {
                self.c_repeat_range(expr, greedy, min, max)
            }
        }
    }

    fn sc_repeat(
        &mut self,
        ctx: SkipCompilerContext,
        expr: &Expr,
        kind: Repeater,
        greedy: bool,
    ) -> Result {
        trace!("::sc_repeat");
        match kind {
            Repeater::ZeroOrOne => self.sc_repeat_zero_or_one(ctx, expr, greedy),
            Repeater::ZeroOrMore => self.sc_repeat_zero_or_more(ctx, expr, greedy),
            Repeater::OneOrMore => self.sc_repeat_one_or_more(ctx, expr, greedy),
            Repeater::Range { min, max: None } => {
                self.sc_repeat_range_min_or_more(ctx, expr, greedy, min)
            }
            Repeater::Range { min, max: Some(max) } => {
                self.sc_repeat_range(ctx, expr, greedy, min, max)
            }
        }
    }

    fn c_repeat_zero_or_one(
        &mut self,
        expr: &Expr,
        greedy: bool,
    ) -> Result {
        let split_entry = self.insts.len();
        let split = self.push_split_hole();
        let Patch { hole: hole_rep, entry: entry_rep } = try!(self.c(expr));

        let split_hole = if greedy {
            self.fill_split(split, Some(entry_rep), None)
        } else {
            self.fill_split(split, None, Some(entry_rep))
        };
        let holes = vec![hole_rep, split_hole];
        Ok(Patch { hole: Hole::Many(holes), entry: split_entry })
    }

    /// compile expr? if greedy else expr??
    ///
    /// ```ignore
    ///    *-expr-*
    ///    |      ^
    ///    |      |
    ///    --------
    /// ```
    fn sc_repeat_zero_or_one(
        &mut self,
        ctx: SkipCompilerContext,
        expr: &Expr,
        greedy: bool,
    ) -> Result {
        trace!("::sc_repeat_zero_or_one");
        let Patch { hole: split_hole, entry: split_entry } =
            self.sc_push_split_patch();

        let mut ni_ctx = ctx;
        ni_ctx.branch_type =
            ctx.branch_type.try_promote(BranchType::NonIntersecting);
        let inner = try!(self.sc(ni_ctx, expr));

        let split_hole = if greedy {
            self.sc_fill_split(split_hole, Some(inner.entry), None)
        } else {
            self.sc_fill_split(split_hole, None, Some(inner.entry))
        };
        Ok(Patch {
            hole: Hole::Many(vec![split_hole, inner.hole]),
            entry: split_entry
        })
    }

    fn c_repeat_zero_or_more(
        &mut self,
        expr: &Expr,
        greedy: bool,
    ) -> Result {
        let split_entry = self.insts.len();
        let split = self.push_split_hole();
        let Patch { hole: hole_rep, entry: entry_rep } = try!(self.c(expr));

        self.fill(hole_rep, split_entry);
        let split_hole = if greedy {
            self.fill_split(split, Some(entry_rep), None)
        } else {
            self.fill_split(split, None, Some(entry_rep))
        };
        Ok(Patch { hole: split_hole, entry: split_entry })
    }

    /// Compile expr* if greedy else expr*?
    ///
    /// ```ignore
    ///    *-expr-*
    ///    ^      ^
    ///    |      |
    ///    --------
    /// ```
    ///
    fn sc_repeat_zero_or_more(
        &mut self,
        ctx: SkipCompilerContext,
        expr: &Expr,
        greedy: bool,
    ) -> Result {
        trace!("::sc_repeat_zero_or_more");
        let Patch { hole: split_hole, entry: split_entry} =
            self.sc_push_split_patch();

        let mut ni_ctx = ctx;
        ni_ctx.branch_type =
            ctx.branch_type.try_promote(BranchType::NonIntersecting);
        let inner = try!(self.sc(ni_ctx, expr));

        // establish the loopback epsilon transition
        self.sc_fill(inner.hole, split_entry);

        // extablish the forward epsilon transition
        let split_hole = if greedy {
            self.sc_fill_split(split_hole, Some(inner.entry), None)
        } else {
            self.sc_fill_split(split_hole, None, Some(inner.entry))
        };

        Ok(Patch { hole: split_hole, entry: split_entry })
    }

    fn c_repeat_one_or_more(
        &mut self,
        expr: &Expr,
        greedy: bool,
    ) -> Result {
        let Patch { hole: hole_rep, entry: entry_rep } = try!(self.c(expr));
        self.fill_to_next(hole_rep);
        let split = self.push_split_hole();

        let split_hole = if greedy {
            self.fill_split(split, Some(entry_rep), None)
        } else {
            self.fill_split(split, None, Some(entry_rep))
        };
        Ok(Patch { hole: split_hole, entry: entry_rep })
    }

    /// Compile expr+ if greedy else expr+?
    ///
    /// ```ignore
    ///    *-expr-*
    ///    ^      |
    ///    |      |
    ///    --------
    /// ```
    ///
    fn sc_repeat_one_or_more(
        &mut self,
        ctx: SkipCompilerContext,
        expr: &Expr,
        greedy: bool,
    ) -> Result {
        trace!("::sc_repeat_one_or_more");

        let mut ni_ctx = ctx;
        ni_ctx.branch_type =
            ctx.branch_type.try_promote(BranchType::NonIntersecting);
        let inner = try!(self.sc(ni_ctx, expr));
        let Patch { hole: split_hole, entry: split_entry } =
            self.sc_push_split_patch();

        // extablish the loopback epsilon transition
        let split_hole = if greedy {
            self.sc_fill_split(split_hole, Some(inner.entry), None)
        } else {
            self.sc_fill_split(split_hole, None, Some(inner.entry))
        };

        let patch = self.sc_continue(inner, Patch {
            hole: split_hole,
            entry: split_entry,
        });

        Ok(patch)
    }

    fn c_repeat_range_min_or_more(
        &mut self,
        expr: &Expr,
        greedy: bool,
        min: u32,
    ) -> Result {
        let min = u32_to_usize(min);
        let patch_concat = try!(self.c_concat(iter::repeat(expr).take(min)));
        let patch_rep = try!(self.c_repeat_zero_or_more(expr, greedy));
        self.fill(patch_concat.hole, patch_rep.entry);
        Ok(Patch { hole: patch_rep.hole, entry: patch_concat.entry })
    }

    /// Compile expr{min}expr*
    fn sc_repeat_range_min_or_more(
        &mut self,
        ctx: SkipCompilerContext,
        expr: &Expr,
        greedy: bool,
        min: u32,
    ) -> Result {
        trace!("::sc_repeat_range_min_or_more");
        let p = try!(self.sc_concat(ctx, iter::repeat(expr).take(u32_to_usize(min))));

        let next = try!(self.sc_repeat_zero_or_more(ctx, expr, greedy));
        Ok(self.sc_continue(p, next))
    }

    fn c_repeat_range(
        &mut self,
        expr: &Expr,
        greedy: bool,
        min: u32,
        max: u32,
    ) -> Result {
        let (min, max) = (u32_to_usize(min), u32_to_usize(max));
        let patch_concat = try!(self.c_concat(iter::repeat(expr).take(min)));
        let initial_entry = patch_concat.entry;
        if min == max {
            return Ok(patch_concat);
        }
        // It is much simpler to compile, e.g., `a{2,5}` as:
        //
        //     aaa?a?a?
        //
        // But you end up with a sequence of instructions like this:
        //
        //     0: 'a'
        //     1: 'a',
        //     2: split(3, 4)
        //     3: 'a'
        //     4: split(5, 6)
        //     5: 'a'
        //     6: split(7, 8)
        //     7: 'a'
        //     8: MATCH
        //
        // This is *incredibly* inefficient because the splits end
        // up forming a chain, which has to be resolved everything a
        // transition is followed.
        let mut holes = vec![];
        let mut prev_hole = patch_concat.hole;
        for _ in min..max {
            self.fill_to_next(prev_hole);
            let split = self.push_split_hole();
            let Patch { hole, entry } = try!(self.c(expr));
            prev_hole = hole;
            if greedy {
                holes.push(self.fill_split(split, Some(entry), None));
            } else {
                holes.push(self.fill_split(split, None, Some(entry)));
            }
        }
        holes.push(prev_hole);
        Ok(Patch { hole: Hole::Many(holes), entry: initial_entry })
    }

    /// Compile expr{min,max}
    ///
    /// ```ignore
    ///                  min-reps           max-reps
    ///    *-expr-expr-...-expr-expr-expr-...-expr-*
    ///                         |    |             ^
    ///                         |    |             |
    ///                         |    --------------|
    ///                         |                  |
    ///                         -------------------|
    /// ```
    fn sc_repeat_range(
        &mut self,
        ctx: SkipCompilerContext,
        expr: &Expr,
        greedy: bool,
        min: u32,
        max: u32,
    ) -> Result {
        trace!("::sc_repeat_range");
        let (min, max) = (u32_to_usize(min), u32_to_usize(max));
        let mut p = try!(self.sc_concat(ctx, iter::repeat(expr).take(min)));

        if min == max {
            return Ok(p);
        }

        let mut ni_ctx = ctx;
        ni_ctx.branch_type =
            ctx.branch_type.try_promote(BranchType::NonIntersecting);

        let mut holes = vec![];
        for _ in min..max {
            let split = self.sc_push_split_patch();
            let expr_next = try!(self.sc(ni_ctx, expr));
            if greedy {
                holes.push(self.sc_fill_split(
                        split.hole, Some(expr_next.entry), None));
            } else {
                holes.push(self.sc_fill_split(
                        split.hole, None, Some(expr_next.entry)));
            }

            p = self.sc_continue(p, Patch {
                hole: expr_next.hole,
                entry: split.entry
            });
        }
        holes.push(p.hole);

        Ok(Patch { hole: Hole::Many(holes), entry: p.entry })
    }

    fn sc_fill(&mut self, hole: Hole, goto: InstPtr) {
        match hole {
            Hole::None => {}
            Hole::One(pc) => {
                self.skip_insts[pc].fill(goto);
            }
            Hole::Many(holes) => {
                for hole in holes {
                    self.sc_fill(hole, goto);
                }
            }
        }
    }

    fn sc_next(&self) -> InstPtr {
        self.skip_insts.len()
    }

    fn fill(&mut self, hole: Hole, goto: InstPtr) {
        match hole {
            Hole::None => {}
            Hole::One(pc) => {
                self.insts[pc].fill(goto);
            }
            Hole::Many(holes) => {
                for hole in holes {
                    self.fill(hole, goto);
                }
            }
        }
    }

    fn fill_to_next(&mut self, hole: Hole) {
        let next = self.insts.len();
        self.fill(hole, next);
    }

    fn fill_split(
        &mut self,
        hole: Hole,
        goto1: Option<InstPtr>,
        goto2: Option<InstPtr>,
    ) -> Hole {
        match hole {
            Hole::None => Hole::None,
            Hole::One(pc) => {
                match (goto1, goto2) {
                    (Some(goto1), Some(goto2)) => {
                        self.insts[pc].fill_split(goto1, goto2);
                        Hole::None
                    }
                    (Some(goto1), None) => {
                        self.insts[pc].half_fill_split_goto1(goto1);
                        Hole::One(pc)
                    }
                    (None, Some(goto2)) => {
                        self.insts[pc].half_fill_split_goto2(goto2);
                        Hole::One(pc)
                    }
                    (None, None) => unreachable!("at least one of the split \
                                                  holes must be filled"),
                }
            }
            Hole::Many(holes) => {
                let mut new_holes = vec![];
                for hole in holes {
                    new_holes.push(self.fill_split(hole, goto1, goto2));
                }
                if new_holes.is_empty() {
                    Hole::None
                } else if new_holes.len() == 1 {
                    new_holes.pop().unwrap()
                } else {
                    Hole::Many(new_holes)
                }
            }
        }
    }

    fn sc_fill_split(
        &mut self,
        hole: Hole,
        goto1: Option<InstPtr>,
        goto2: Option<InstPtr>,
    ) -> Hole {
        match hole {
            Hole::None => Hole::None,
            Hole::One(pc) => {
                match (goto1, goto2) {
                    (Some(goto1), Some(goto2)) => {
                        self.skip_insts[pc].fill_split(goto1, goto2);
                        Hole::None
                    }
                    (Some(goto1), None) => {
                        self.skip_insts[pc].half_fill_split_goto1(goto1);
                        Hole::One(pc)
                    }
                    (None, Some(goto2)) => {
                        self.skip_insts[pc].half_fill_split_goto2(goto2);
                        Hole::One(pc)
                    }
                    (None, None) => unreachable!("at least one of the split \
                                                  holes must be filled"),
                }
            }
            Hole::Many(holes) => {
                let mut new_holes = vec![];
                for hole in holes {
                    new_holes.push(self.sc_fill_split(hole, goto1, goto2));
                }
                if new_holes.is_empty() {
                    Hole::None
                } else if new_holes.len() == 1 {
                    new_holes.pop().unwrap()
                } else {
                    Hole::Many(new_holes)
                }
            }
        }
    }

    fn sc_push_compiled(&mut self, inst: SkipInst) -> Patch {
        let entry = self.sc_next();
        self.skip_insts.push(MaybeInst::Compiled(inst));
        Patch { hole: Hole::None, entry: entry }
    }

    /// Push a single instruction, returning the patch describing
    /// it. Returns a patch for easy composability with sc_continue.
    fn sc_push_one(&mut self, inst: SkipInstHole) -> Patch {
        let hole = self.sc_next();
        self.skip_insts.push(MaybeInst::Uncompiled(inst));
        Patch { hole: Hole::One(hole), entry: hole }
    }

    /// Compile the given instruction and fill the given hole with
    /// the new instruction.
    fn sc_continue(
        &mut self,
        last: Patch,
        next: Patch,
    ) -> Patch {
        self.sc_fill(last.hole, next.entry);
        Patch { hole: next.hole, entry: last.entry }
    }

    fn push_compiled(&mut self, inst: Inst) {
        self.insts.push(MaybeInst::Compiled(inst));
    }

    fn push_hole(&mut self, inst: InstHole) -> Hole {
        let hole = self.insts.len();
        self.insts.push(MaybeInst::Uncompiled(inst));
        Hole::One(hole)
    }

    fn push_split_hole(&mut self) -> Hole {
        let hole = self.insts.len();
        self.insts.push(MaybeInst::Split);
        Hole::One(hole)
    }

    /// Push a new split patch onto the skip instruction list
    fn sc_push_split_patch(&mut self) -> Patch {
        let split_entry = self.sc_next();
        self.skip_insts.push(MaybeInst::Split);
        Patch { entry: split_entry, hole: Hole::One(split_entry) }
    }

    fn check_size(&self) -> result::Result<(), Error> {
        use std::mem::size_of;

        let size = (self.insts.len() * size_of::<Inst>())
                 + (self.skip_insts.len() * size_of::<SkipInst>());

        if size > self.options.size_limit {
            Err(Error::CompiledTooBig(self.options.size_limit))
        } else {
            Ok(())
        }
    }
}

#[derive(Debug)]
enum Hole {
    None,
    One(InstPtr),
    Many(Vec<Hole>),
}

/// Internal metadata to track the compilation context for
/// skip compilation. Introduced to deal with tracking
/// branch position.
#[derive(Debug, Copy, Clone)]
struct SkipCompilerContext {
    branch_type: BranchType,
}

const INIT_SC_CTX: SkipCompilerContext = SkipCompilerContext {
    branch_type: BranchType::NoBranch
};

/// A flag to indicate the branch context of the current compilation.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum BranchType {
    /// Compile the expression as if it is not part of a branch
    /// at all. This is the default.
    NoBranch,

    /// Compile the expression as if it is part of a non-intersecting
    /// branch pattern such as `/axxx|bxx/`. That is, the first char must
    /// be checked so that the proper thread dies, but the skips can
    /// be used afterwards. So we would compile the first branch in
    /// the given example to
    ///
    /// ```text
    /// char 'a'
    /// skip 3
    /// ```
    NonIntersecting,

    /// Compile a branch with a trigger set that intersects with
    /// the trigger sets of other branches. The trigger set can
    /// be thought of as the 1-preview of the regex. For example
    /// `/axxx|axx/` is a regex with an intersecting branch.
    /// The first branch would have to be compiled as:
    ///
    /// ```text
    /// char 'a'
    /// char 'x'
    /// char 'x'
    /// char 'x'
    /// ```
    Intersecting,
}

impl BranchType {
    /// BranchTypes exist in a hierarchy, which this method enforces
    ///
    /// You can always move down in the hierarchy to a more limited
    /// optimization level, but you can never go back up without
    /// leaving the expression in question via recursion or by
    /// moving forward in a concatenation expression.
    ///
    /// 0. NoBranch
    /// 1. NonIntersecting
    /// 2. Intersecting
    fn try_promote(&self, new: BranchType) -> BranchType {
        if new.rank() > self.rank() {
            new
        } else {
            *self
        }
    }

    fn rank(&self) -> usize {
        match *self {
            BranchType::NoBranch => 0,
            BranchType::NonIntersecting => 1,
            BranchType::Intersecting => 2,
        }
    }
}

#[derive(Clone, Debug)]
enum MaybeInst<I, H> {
    Compiled(I),
    Uncompiled(H),
    Split,
    Split1(InstPtr),
    Split2(InstPtr),
}

impl MaybeInst<Inst, InstHole> {
    fn fill(&mut self, goto: InstPtr) {
        let filled = match *self {
            MaybeInst::Uncompiled(ref inst) => inst.fill(goto),
            MaybeInst::Split1(goto1) => {
                Inst::Split(InstSplit { goto1: goto1, goto2: goto })
            }
            MaybeInst::Split2(goto2) => {
                Inst::Split(InstSplit { goto1: goto, goto2: goto2 })
            }
            _ => unreachable!("not all instructions were compiled! \
                               found uncompiled instruction: {:?}", self),
        };
        *self = MaybeInst::Compiled(filled);
    }

    fn fill_split(&mut self, goto1: InstPtr, goto2: InstPtr) {
        let filled = match *self {
            MaybeInst::Split => {
                Inst::Split(InstSplit { goto1: goto1, goto2: goto2 })
            }
            _ => unreachable!("must be called on Split instruction, \
                               instead it was called on: {:?}", self),
        };
        *self = MaybeInst::Compiled(filled);
    }

    fn half_fill_split_goto1(&mut self, goto1: InstPtr) {
        let half_filled = match *self {
            MaybeInst::Split => goto1,
            _ => unreachable!("must be called on Split instruction, \
                               instead it was called on: {:?}", self),
        };
        *self = MaybeInst::Split1(half_filled);
    }

    fn half_fill_split_goto2(&mut self, goto2: InstPtr) {
        let half_filled = match *self {
            MaybeInst::Split => goto2,
            _ => unreachable!("must be called on Split instruction, \
                               instead it was called on: {:?}", self),
        };
        *self = MaybeInst::Split2(half_filled);
    }

    fn unwrap(self) -> Inst {
        match self {
            MaybeInst::Compiled(inst) => inst,
            _ => unreachable!("must be called on a compiled instruction, \
                               instead it was called on: {:?}", self),
        }
    }
}

trait FillTo<Tgt> {
    fn fill(&self, goto: InstPtr) -> Tgt;
}

#[derive(Clone, Debug)]
enum InstHole {
    Save { slot: usize },
    EmptyLook { look: EmptyLook },
    Char { c: char },
    Ranges { ranges: Vec<(char, char)> },
    Bytes { start: u8, end: u8 },
}

impl FillTo<Inst> for InstHole {
    fn fill(&self, goto: InstPtr) -> Inst {
        match *self {
            InstHole::Save { slot } => Inst::Save(InstSave {
                goto: goto,
                slot: slot,
            }),
            InstHole::EmptyLook { look } => Inst::EmptyLook(InstEmptyLook {
                goto: goto,
                look: look,
            }),
            InstHole::Char { c } => Inst::Char(InstChar {
                goto: goto,
                c: c,
            }),
            InstHole::Ranges { ref ranges } => Inst::Ranges(InstRanges {
                goto: goto,
                ranges: ranges.clone(),
            }),
            InstHole::Bytes { start, end } => Inst::Bytes(InstBytes {
                goto: goto,
                start: start,
                end: end,
            }),
        }
    }
}

// This code duplication is gross, but I didn't want to keep mucking
// about with higher kinded types. TODO(ethan): refactor.
impl MaybeInst<SkipInst, SkipInstHole> {
    fn fill(&mut self, goto: InstPtr) -> () {
        let patched = match *self {
            MaybeInst::Uncompiled(ref si) => si.fill(goto),
            MaybeInst::Split1(goto1) => {
                SkipInst::SkipSplit(InstSplit { goto1: goto1, goto2: goto })
            },
            MaybeInst::Split2(goto2) => {
                SkipInst::SkipSplit(InstSplit { goto1: goto, goto2: goto2 })
            },
            _ => unreachable!("not all instructions were compiled! \
                               found uncompiled instruction: {:?}", self),
        };
        *self = MaybeInst::Compiled(patched);
    }

    fn fill_split(&mut self, goto1: InstPtr, goto2: InstPtr) {
        let filled = match *self {
            MaybeInst::Split => {
                SkipInst::SkipSplit(InstSplit { goto1: goto1, goto2: goto2 })
            }
            _ => unreachable!("must be called on Split instruction, \
                               instead it was called on: {:?}", self),
        };
        *self = MaybeInst::Compiled(filled);
    }

    fn half_fill_split_goto1(&mut self, goto1: InstPtr) {
        let half_filled = match *self {
            MaybeInst::Split => goto1,
            _ => unreachable!("must be called on Split instruction, \
                               instead it was called on: {:?}", self),
        };
        *self = MaybeInst::Split1(half_filled);
    }

    fn half_fill_split_goto2(&mut self, goto2: InstPtr) {
        let half_filled = match *self {
            MaybeInst::Split => goto2,
            _ => unreachable!("must be called on Split instruction, \
                               instead it was called on: {:?}", self),
        };
        *self = MaybeInst::Split2(half_filled);
    }

    fn unwrap(self) -> SkipInst {
        match self {
            MaybeInst::Compiled(inst) => inst,
            _ => unreachable!("must be called on a compiled instruction, \
                               instead it was called on: {:?}", self),
        }
    }
}

#[derive(Clone, Debug)]
enum SkipInstHole {
    Save { slot: usize },
    Byte { c: u8 },
    Bytes { start: u8, end: u8 },
    Skip { skip: usize },
    ScanLiteral { literal: LiteralSearcher, start: bool },
}

impl FillTo<SkipInst> for SkipInstHole {
    fn fill(&self, goto: InstPtr) -> SkipInst {
        match *self {
            SkipInstHole::Save { slot } => SkipInst::SkipSave(InstSave {
                goto: goto,
                slot: slot,
            }),
            SkipInstHole::Skip { skip } => SkipInst::SkipSkip(InstSkip {
                goto: goto,
                skip: skip,
            }),
            SkipInstHole::Byte { c } =>
                SkipInst::SkipByte(InstByte {
                    goto: goto,
                    c: c,
                }),
            SkipInstHole::Bytes { start, end } =>
                SkipInst::SkipBytes(InstBytes {
                    goto: goto,
                    start: start,
                    end: end,
                }),
            SkipInstHole::ScanLiteral { ref literal, start } =>
                SkipInst::SkipScanLiteral(InstScanLiteral {
                    goto: goto,
                    literal: literal.clone(),
                    start: start
                }),
        }
    }
}

struct CompileClass<'a, 'b> {
    c: &'a mut Compiler,
    ranges: &'b [ClassRange],
}

impl<'a, 'b> CompileClass<'a, 'b> {
    fn compile(mut self) -> Result {
        let mut holes = vec![];
        let mut initial_entry = None;
        let mut last_split = Hole::None;
        let mut utf8_seqs = self.c.utf8_seqs.take().unwrap();
        self.c.suffix_cache.clear();

        for (i, range) in self.ranges.iter().enumerate() {
            let is_last_range = i + 1 == self.ranges.len();
            utf8_seqs.reset(range.start, range.end);
            let mut it = (&mut utf8_seqs).peekable();
            loop {
                let utf8_seq = match it.next() {
                    None => break,
                    Some(utf8_seq) => utf8_seq,
                };
                if is_last_range && it.peek().is_none() {
                    let Patch { hole, entry } = try!(self.c_utf8_seq(&utf8_seq));
                    holes.push(hole);
                    self.c.fill(last_split, entry);
                    last_split = Hole::None;
                    if initial_entry.is_none() {
                        initial_entry = Some(entry);
                    }
                } else {
                    if initial_entry.is_none() {
                        initial_entry = Some(self.c.insts.len());
                    }
                    self.c.fill_to_next(last_split);
                    last_split = self.c.push_split_hole();
                    let Patch { hole, entry } = try!(self.c_utf8_seq(&utf8_seq));
                    holes.push(hole);
                    last_split = self.c.fill_split(last_split, Some(entry), None);
                }
            }
        }
        self.c.utf8_seqs = Some(utf8_seqs);
        Ok(Patch {
            hole: Hole::Many(holes),
            entry: initial_entry.unwrap(),
        })
    }

    fn c_utf8_seq(&mut self, seq: &Utf8Sequence) -> Result {
        if self.c.compiled.is_reverse {
            self.c_utf8_seq_(seq)
        } else {
            self.c_utf8_seq_(seq.into_iter().rev())
        }
    }

    fn c_utf8_seq_<'r, I>(&mut self, seq: I) -> Result
            where I: IntoIterator<Item=&'r Utf8Range> {
        // The initial instruction for each UTF-8 sequence should be the same.
        let mut from_inst = ::std::usize::MAX;
        let mut last_hole = Hole::None;
        for byte_range in seq {
            let key = SuffixCacheKey {
                from_inst: from_inst,
                start: byte_range.start,
                end: byte_range.end,
            };
            {
                let pc = self.c.insts.len();
                if let Some(cached_pc) = self.c.suffix_cache.get(key, pc) {
                    from_inst = cached_pc;
                    continue;
                }
            }
            self.c.byte_classes.set_range(byte_range.start, byte_range.end);
            if from_inst == ::std::usize::MAX {
                last_hole = self.c.push_hole(InstHole::Bytes {
                    start: byte_range.start,
                    end: byte_range.end,
                });
            } else {
                self.c.push_compiled(Inst::Bytes(InstBytes {
                    goto: from_inst,
                    start: byte_range.start,
                    end: byte_range.end,
                }));
            }
            from_inst = self.c.insts.len().checked_sub(1).unwrap();
            debug_assert!(from_inst < ::std::usize::MAX);
        }
        debug_assert!(from_inst < ::std::usize::MAX);
        Ok(Patch { hole: last_hole, entry: from_inst })
    }
}

/// `SuffixCache` is a simple bounded hash map for caching suffix entries in
/// UTF-8 automata. For example, consider the Unicode range \u{0}-\u{FFFF}.
/// The set of byte ranges looks like this:
///
/// [0-7F]
/// [C2-DF][80-BF]
/// [E0][A0-BF][80-BF]
/// [E1-EC][80-BF][80-BF]
/// [ED][80-9F][80-BF]
/// [EE-EF][80-BF][80-BF]
///
/// Each line above translates to one alternate in the compiled regex program.
/// However, all but one of the alternates end in the same suffix, which is
/// a waste of an instruction. The suffix cache facilitates reusing them across
/// alternates.
///
/// Note that a HashMap could be trivially used for this, but we don't need its
/// overhead. Some small bounded space (LRU style) is more than enough.
struct SuffixCache {
    table: Vec<SuffixCacheEntry>,
    // Every time the cache is cleared, we increment the version number instead
    // of actually zeroing memory. Since we store a copy of the current version
    // in every element, all we need to do is make sure to invalidate any stale
    // entries upon access. This saves quite a bit of time!
    version: usize,
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
struct SuffixCacheEntry {
    key: SuffixCacheKey,
    pc: InstPtr,
    version: usize,
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
struct SuffixCacheKey {
    from_inst: InstPtr,
    start: u8,
    end: u8,
}

impl SuffixCache {
    fn new(size: usize) -> Self {
        SuffixCache {
            table: vec![SuffixCacheEntry::default(); size],
            version: 0,
        }
    }

    fn get(&mut self, key: SuffixCacheKey, pc: InstPtr) -> Option<InstPtr> {
        let h = self.hash(&key);
        let e = self.table[h];
        if e.key == key && e.version == self.version {
            Some(e.pc)
        } else {
            self.table[h] = SuffixCacheEntry {
                key: key,
                pc: pc,
                version: self.version,
            };
            None
        }
    }

    fn clear(&mut self) {
        self.version += 1;
    }

    fn hash(&self, suffix: &SuffixCacheKey) -> usize {
        // Basic FNV-1a hash as described:
        // https://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function
        const FNV_PRIME: u64 = 1099511628211;
        let mut h = 14695981039346656037;
        h = (h ^ (suffix.from_inst as u64)).wrapping_mul(FNV_PRIME);
        h = (h ^ (suffix.start as u64)).wrapping_mul(FNV_PRIME);
        h = (h ^ (suffix.end as u64)).wrapping_mul(FNV_PRIME);
        (h as usize) % self.table.len()
    }
}

struct ByteClassSet([bool; 256]);

impl ByteClassSet {
    fn new() -> Self {
        ByteClassSet([false; 256])
    }

    fn set_range(&mut self, start: u8, end: u8) {
        debug_assert!(start <= end);
        if start > 0 {
            self.0[start as usize - 1] = true;
        }
        self.0[end as usize] = true;
    }

    fn set_word_boundary(&mut self) {
        // We need to mark all ranges of bytes whose pairs result in
        // evaluating \b differently.
        let iswb = is_word_byte;
        let mut b1: u16 = 0;
        let mut b2: u16;
        while b1 <= 255 {
            b2 = b1 + 1;
            while b2 <= 255 && iswb(b1 as u8) == iswb(b2 as u8) {
                b2 += 1;
            }
            self.set_range(b1 as u8, (b2 - 1) as u8);
            b1 = b2;
        }
    }

    fn byte_classes(&self) -> Vec<u8> {
        // N.B. If you're debugging the DFA, it's useful to simply return
        // `(0..256).collect()`, which effectively removes the byte classes
        // and makes the transitions easier to read.
        // (0usize..256).map(|x| x as u8).collect()
        let mut byte_classes = vec![0; 256];
        let mut class = 0u8;
        let mut i = 0;
        loop {
            byte_classes[i] = class as u8;
            if i >= 255 {
                break;
            }
            if self.0[i] {
                class = class.checked_add(1).unwrap();
            }
            i += 1;
        }
        byte_classes
    }
}

fn u32_to_usize(n: u32) -> usize {
    // In case usize is less than 32 bits, we need to guard against overflow.
    // On most platforms this compiles to nothing.
    // TODO Use `std::convert::TryFrom` once it's stable.
    if (n as u64) > (::std::usize::MAX as u64) {
        panic!("BUG: {} is too big to be pointer sized", n)
    }
    n as usize
}

/// A visitor to decide if a given expression contains a capture.
struct ContainsCaptureVisitor(bool);
impl ContainsCaptureVisitor {
    /// Returns true if the given AST node contains a capture
    /// group, false otherwise.
    fn check<V>(node: &V) -> bool 
        where V: SyntaxVisitable
    {
        let mut ccv = ContainsCaptureVisitor(false);
        node.visit_node(&mut ccv);
        ccv.0
    }
}
impl SyntaxVisitor for ContainsCaptureVisitor {
    fn visit_expr(&mut self, expr: &Expr) {
        match expr {
            &Expr::Group { e: _, i: _, name: _ } => self.0 = true,
            e => e.visit_children(self),
        }
    }
}


#[cfg(test)]
mod tests {
    use super::ByteClassSet;

    #[test]
    fn byte_classes() {
        let mut set = ByteClassSet::new();
        set.set_range(b'a', b'z');
        let classes = set.byte_classes();
        assert_eq!(classes[0], 0);
        assert_eq!(classes[1], 0);
        assert_eq!(classes[2], 0);
        assert_eq!(classes[b'a' as usize - 1], 0);
        assert_eq!(classes[b'a' as usize], 1);
        assert_eq!(classes[b'm' as usize], 1);
        assert_eq!(classes[b'z' as usize], 1);
        assert_eq!(classes[b'z' as usize + 1], 2);
        assert_eq!(classes[254], 2);
        assert_eq!(classes[255], 2);

        let mut set = ByteClassSet::new();
        set.set_range(0, 2);
        set.set_range(4, 6);
        let classes = set.byte_classes();
        assert_eq!(classes[0], 0);
        assert_eq!(classes[1], 0);
        assert_eq!(classes[2], 0);
        assert_eq!(classes[3], 1);
        assert_eq!(classes[4], 2);
        assert_eq!(classes[5], 2);
        assert_eq!(classes[6], 2);
        assert_eq!(classes[7], 3);
        assert_eq!(classes[255], 3);
    }

    #[test]
    fn full_byte_classes() {
        let mut set = ByteClassSet::new();
        for i in 0..256u16 {
            set.set_range(i as u8, i as u8);
        }
        assert_eq!(set.byte_classes().len(), 256);
    }
}

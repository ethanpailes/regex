// Copyright 2014-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// This is the backtracking matching engine. It has the same exact capability
// as the full NFA simulation, except it is artificially restricted to small
// regexes on small inputs because of its memory requirements.
//
// In particular, this is a *bounded* backtracking engine. It retains worst
// case linear time by keeping track of the states that it has visited (using a
// bitmap). Namely, once a state is visited, it is never visited again. Since a
// state is keyed by `(instruction index, input index)`, we have that its time
// complexity is `O(mn)` (i.e., linear in the size of the search text).
//
// The backtracking engine can beat out the NFA simulation on small
// regexes/inputs because it doesn't have to keep track of multiple copies of
// the capture groups. In benchmarks, the backtracking engine is roughly twice
// as fast as the full NFA simulation. Note though that its performance doesn't
// scale, even if you're willing to live with the memory requirements. Namely,
// the bitset has to be zeroed on each execution, which becomes quite expensive
// on large bitsets.

use exec::ProgramCache;
use input::{Input};
use prog::{Program, InstPtr};
use re_trait::Slot;

type Bits = u32;

const BIT_SIZE: usize = 32;
const MAX_SIZE_BYTES: usize = 256 * (1 << 10); // 256 KB

/// Returns true iff the given regex and input should be executed by this
/// engine with reasonable memory usage.
pub fn should_exec(num_insts: usize, text_len: usize) -> bool {
    // Total memory usage in bytes is determined by:
    //
    //   ((len(insts) * (len(input) + 1) + bits - 1) / bits) * (size_of(u32))
    //
    // The actual limit picked is pretty much a heuristic.
    // See: https://github.com/rust-lang/regex/issues/215
    let size = ((num_insts * (text_len + 1) + BIT_SIZE - 1) / BIT_SIZE) * 4;
    size <= MAX_SIZE_BYTES
}

/// A backtracking matching engine.
#[derive(Debug)]
pub struct Bounded<'a, 'r, 's, I> {
    prog: &'r Program,
    input: I,
    slots: &'s mut [Slot],
    m: &'a mut Cache,
}

/// Shared cached state between multiple invocations of a backtracking engine
/// in the same thread.
#[derive(Clone, Debug)]
pub struct Cache {
    jobs: Vec<Job>,
    visited: Vec<Bits>,
}

impl Cache {
    /// Create new empty cache for the backtracking engine.
    pub fn new(_prog: &Program) -> Self {
        Cache { jobs: vec![], visited: vec![] }
    }
}

/// A job is an explicit unit of stack space in the backtracking engine.
///
/// The "normal" representation is a single state transition, which corresponds
/// to an NFA state and a character in the input. However, the backtracking
/// engine must keep track of old capture group values. We use the explicit
/// stack to do it.
#[derive(Clone, Copy, Debug)]
enum Job {
    Inst { ip: InstPtr, sp: usize },
    SaveRestore { slot: usize, old_pos: Option<usize> },
}

impl<'a, 'r, 's, I: Input> Bounded<'a, 'r, 's, I> {
    /// Execute the backtracking matching engine.
    ///
    /// If there's a match, `exec` returns `true` and populates the given
    /// captures accordingly.
    pub fn exec(
        prog: &'r Program,
        cache: &ProgramCache,
        slots: &'s mut [Slot],
        input: I,
        start: usize,
    ) -> bool {
        let mut cache = cache.borrow_mut();
        let cache = &mut cache.skip_backtrack;
        let start = input.at(start).pos();
        let mut b = Bounded {
            prog: prog,
            input: input,
            slots: slots,
            m: cache,
        };
        b.exec_(start)
    }

    /// Clears the cache such that the backtracking engine can be executed
    /// on some input of fixed length.
    fn clear(&mut self) {
        // Reset the job memory so that we start fresh.
        self.m.jobs.clear();

        // Now we need to clear the bit state set.
        // We do this by figuring out how much space we need to keep track
        // of the states we've visited.
        // Then we reset all existing allocated space to 0.
        // Finally, we request more space if we need it.
        //
        // This is all a little circuitous, but doing this unsafely
        // doesn't seem to have a measurable impact on performance.
        // (Probably because backtracking is limited to such small
        // inputs/regexes in the first place.)
        let visited_len =
            (self.prog.skip_insts.len() * (self.input.len() + 1) + BIT_SIZE - 1)
            /
            BIT_SIZE;
        self.m.visited.truncate(visited_len);
        for v in &mut self.m.visited {
            *v = 0;
        }
        if visited_len > self.m.visited.len() {
            let len = self.m.visited.len();
            self.m.visited.reserve_exact(visited_len - len);
            for _ in 0..(visited_len - len) {
                self.m.visited.push(0);
            }
        }
    }

    /// Start backtracking at the given position in the input, but also look
    /// for literal prefixes.
    fn exec_(&mut self, mut sp: usize) -> bool {
        self.clear();
        // If this is an anchored regex at the beginning of the input, then
        // we're either already done or we only need to try backtracking once.
        if self.prog.is_anchored_start {
            return if sp != 0 {
                false
            } else {
                self.backtrack(sp)
            };
        }
        
        // It's not anchored so we have to try the parse at every
        // point in the input.
        loop {
            if !self.prog.prefixes.is_empty() {
                sp = match self.prog.prefixes
                               .find(&self.input.as_bytes()[sp..])
                               .map(|(s, _)| sp + s) {
                    None => break,
                    Some(sp) => sp,
                };
            }
            if self.backtrack(sp) {
                return true;
            }
            if sp >= self.input.len() {
                break;
            }
            sp += 1;
        }
        false
    }

    /// The main backtracking loop starting at the given input position.
    fn backtrack(&mut self, start: usize) -> bool {
        // N.B. We use an explicit stack to avoid recursion.
        // To avoid excessive pushing and popping, most transitions are handled
        // in the `step` helper function, which only pushes to the stack when
        // there's a capture or a branch.
        self.m.jobs.push(Job::Inst { ip: 0, sp: start });
        while let Some(job) = self.m.jobs.pop() {
            match job {
                Job::Inst { ip, sp } => {
                    if self.step(ip, sp) {
                        return true;
                    }
                }
                Job::SaveRestore { slot, old_pos } => {
                    if slot < self.slots.len() {
                        self.slots[slot] = old_pos;
                    }
                }
            }
        }

        false
    }

    fn step(&mut self, mut ip: InstPtr, mut sp: usize) -> bool {
        use prog::SkipInst::*;
        loop {
            // This loop is an optimization to avoid constantly pushing/popping
            // from the stack. Namely, if we're pushing a job only to run it
            // next, avoid the push and just mutate `ip` (and possibly `at`)
            // in place.
            if self.has_visited(ip, sp) {
                return false;
            }
            match self.prog.skip_insts[ip] {
                SkipMatch(_) => {
                    return true;
                }
                SkipSave(ref inst) => {
                    if let Some(&old_pos) = self.slots.get(inst.slot) {
                        // If this path doesn't work out, then we save the old
                        // capture index (if one exists) in an alternate
                        // job. If the next path fails, then the alternate
                        // job is popped and the old capture index is restored.
                        self.m.jobs.push(Job::SaveRestore {
                            slot: inst.slot,
                            old_pos: old_pos,
                        });
                        self.slots[inst.slot] = Some(sp);
                    }
                    ip = inst.goto;
                }
                SkipSplit(ref inst) => {
                    self.m.jobs.push(Job::Inst { ip: inst.goto2, sp: sp });
                    ip = inst.goto1;
                }
                SkipByte(ref inst) => {
                    if inst.c == self.input.as_bytes()[sp] {
                        ip = inst.goto;
                        sp += 1;
                    } else {
                        return false;
                    }
                }
                SkipBytes(ref inst) => {
                    if inst.matches(self.input.as_bytes()[sp]) {
                        ip = inst.goto;
                        sp += 1;
                    } else {
                        return false;
                    }
                }
                SkipSkip(ref inst) => {
                    unreachable!("unimpl")
                }
                SkipScanLiteral(ref inst) => {
                    unreachable!("unimpl")
                }
            }
        }
    }

    fn has_visited(&mut self, ip: InstPtr, sp: usize) -> bool {
        let k = ip * (self.input.len() + 1) + sp;
        let k1 = k / BIT_SIZE;
        let k2 = usize_to_u32(1 << (k & (BIT_SIZE - 1)));
        if self.m.visited[k1] & k2 == 0 {
            self.m.visited[k1] |= k2;
            false
        } else {
            true
        }
    }
}

fn usize_to_u32(n: usize) -> u32 {
    if (n as u64) > (::std::u32::MAX as u64) {
        panic!("BUG: {} is too big to fit into u32", n)
    }
    n as u32
}

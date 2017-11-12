// Copyright 2014-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// This module implements the a modified Pike VM for Skip Regex.
// That is, it guarantees linear time search of a regex on any text
// with O(n m) memory use, where n is the size of the regex and m is
// the size of the input.

use prog::{Program, RUN_QUEUE_RING_SIZE};
use pikevm::{Threads, FollowEpsilon};
use input::{Input};
use re_trait::{Slot};
use exec::ProgramCache;

// Flip to true for debugging
const TRACE: bool = true;
macro_rules! trace {
    ($($tts:tt)*) => {
        if TRACE {
            println!($($tts)*);
        }
    }
}

/// A Skip NFA simulation matching engine. See pikevm.rs::Fsm for more details
///
/// We only parameterize over input in order to match the interface of
/// the existing code more closely. We are just going to call input.as_bytes()
/// immediately when we execute the VM.
#[derive(Debug)]
pub struct Fsm<'r, I> {
    prog: &'r Program,
    stack: &'r mut Vec<FollowEpsilon>,

    // TODO(ethan): benchmark to see if storing this as an Input matters,
    //              or if I need to store it as a byte slice.
    input: I,
}

/// The list of runnable threads at a given offset.
#[derive(Clone, Debug)]
struct RunQueue {
    /// A ring buffer of the Threads objects
    thread_queues: Vec<Threads>,

    /// An index into `thread_queues` indicating the current thread list.
    current_queue: usize,

    /// The string offset of the current queue
    current_string_offset: usize,

    /// An index into the thread queue indicated by `current_queue`
    /// indicating the next thread to be returned by `pop`
    next_thread: usize,
}

/// The ring-buffer run queue employed by the skip pikeVM engine.
/// This can be thought of as a generalization of the occilating
/// clist and nlist lists in the normal pikeVM.
impl RunQueue {
    fn new() -> Self {
        let mut qs = Vec::with_capacity(RUN_QUEUE_RING_SIZE);
        for _ in 0..RUN_QUEUE_RING_SIZE {
            qs.push(Threads::new());
        }
        RunQueue {
            thread_queues: qs,
            current_queue: 0,
            current_string_offset: 0,
            next_thread: 0,
        }
    }

    /// Resize the RunQueue for a regex with `num_insts` instructions
    /// and `ncaps` capture groups.
    fn resize(&mut self, num_insts: usize, ncaps: usize) {
        for q in &mut self.thread_queues {
            q.resize(num_insts, ncaps);
        }
    }

    /// Tell the ring where in the string we are operating from.
    /// This is used to support the case where we want to start
    /// looking for a match in the middle of slice.
    fn set_string_pointer(&mut self, string_pointer: usize) {
        self.current_string_offset = string_pointer;
    }

    /// Put a thread into the run queue at the given string and instruction
    /// pointer.
    ///
    /// O(1)
    fn put(&mut self, ip: usize, sp: usize) {
        let idx = self._sp_to_offset(sp);
        let q = &mut self.thread_queues[idx];
        if !q.set.contains(ip) {
            q.set.insert(ip);
        }
    }


    /// Pop a thread off the runqueue.
    ///
    /// The thread is indicated by a tuple of (ip, sp)
    ///
    /// Worst case O(n) in the size of the ring. (Basically O(1)).
    fn pop(&mut self) -> Option<(usize, usize)> {
        if self.next_thread >= self._cq().set.len() {
            return None;
        }

        let ip = self._cq().set[self.next_thread];
        self.next_thread = self.next_thread + 1;
        Some((ip, self.current_string_offset))
    }

    /// The capture range for the most recently pop'd thread
    fn caps(&mut self, ip: usize) -> &mut [Option<usize>] {
        self._cq().caps(ip)
    }

    fn copy_caps_to(&mut self, from_ip: usize, to_ip: usize, to_sp: usize) {
        let slots_per_thread = self._cq().slots_per_thread;
        debug_assert_eq!(slots_per_thread,
                         self.thread_queues[self._sp_to_offset(to_sp)]
                             .slots_per_thread);

        let from = from_ip * slots_per_thread;
        let to = to_ip * slots_per_thread;

        for i in 0..slots_per_thread {
            let to_idx = self._sp_to_offset(to_sp);
            self.thread_queues[to_idx].caps[to + i] =
                self.thread_queues[self.current_queue].caps[from + i];
        }
    }

    // Normally I would just stuff this in a local variable, but
    // the borrow checker does not seem to like that. I really don't
    // like repeated deep array accesses, so I'm compromising with
    // a somewhat cryptically named helper method.
    // I'm still not hapy with the style.
    #[inline]
    fn _cq(&mut self) -> &mut Threads {
        &mut self.thread_queues[self.current_queue]
    }

    fn advance(&mut self) -> bool {
        let start = self.current_queue;
        self._cq().set.clear();
        self.next_thread = 0;

        while self.thread_queues[self.current_queue].set.is_empty() {
            self.current_queue = (self.current_queue + 1) % RUN_QUEUE_RING_SIZE;
            self.current_string_offset += 1;

            if self.current_queue == start {
                return false;
            }
        }
        true
    }

    #[inline]
    fn _sp_to_offset(&self, sp: usize) -> usize {
        // We had better not be trying to index futher ahead than the
        // ring buffer can handle.
        debug_assert!((sp - self.current_string_offset) < RUN_QUEUE_RING_SIZE);

        // TODO(ethan): check that this really compiles down to a bitshift.
        // when RUN_QUEUE_RING_SIZE is a multiple of 2
        ((sp - self.current_string_offset) + self.current_queue)
            % RUN_QUEUE_RING_SIZE
    }
}

// The reusable cache for this PikeVM. It should probably use a
// memory pool in order to actually re-use RunQueues.
//
// Perhaps I could just leave the runqueues in the array backing
// the binary heap. First let's make this work, then I can make
// it fast.
#[derive(Clone, Debug)]
pub struct Cache {
    queue: RunQueue,
    stack: Vec<FollowEpsilon>,
}

impl Cache {
    pub fn new() -> Self {
        Cache {
            queue: RunQueue::new(),
            stack: vec![],
        }
    }
}

impl<'r, I: Input> Fsm<'r, I> {

    /// Execute the skip regex with a SkipPikeVM
    ///
    /// Unlike other `exec` functions, this guy does not return
    /// a boolean value because it is a logic error to execute
    /// a skip engine when the input does not match.
    pub fn exec(
        prog: &'r Program,
        cache: &ProgramCache,
        slots: &mut [Slot], // capture group output variable
        input: I,
        start: usize,
    ) {
        let mut cache = cache.borrow_mut();
        let cache = &mut cache.skip_pikevm;

        trace!("");
        trace!("======================== PROG =============================");
        if TRACE {
            for (inst, i) in prog.skip_insts.iter().zip(0..) {
                trace!("{:04}: {:?}", i, inst);
            }
        }
        trace!("====================== END PROG ============================");
        trace!("");

        Fsm {
            prog: prog,
            stack: &mut cache.stack,
            input: input,
        }.exec_(&mut cache.queue, slots, start)
    }

    /// Internal exec function
    fn exec_(
        &mut self,
        run_queue: &mut RunQueue,
        mut slots: &mut [Slot],
        string_pointer: usize,
    ) {
        // Set up the queue.
        run_queue.resize(self.prog.skip_insts.len(), self.prog.captures.len());
        run_queue.set_string_pointer(string_pointer);

        // Push the first thread.
        self.add(run_queue, 0, 0, string_pointer);

        // TODO(ethan):opt advance() should return the new string pointer
        //                 and pop should just return the instruction pointer
        //                 again.

        // Main execution loop
        loop {
            while let Some((ip, sp)) = run_queue.pop() {
                // We can nope out of here for the current string
                // pointer, but we have finish execution of the remaining
                // threads for greedy matching support.
                if self.step(run_queue, ip, sp, &mut slots) {
                    break;
                }
            }

            if !run_queue.advance() {
                break;
            }
        }
        println!("slots={:?}", slots);
    }

    // Step is the guy who actually does all the work.
    // He does his best to avoid touching the runqueue as much
    // as possible.
    fn step(
        &mut self,
        run_queue: &mut RunQueue,
        ip: usize,
        sp: usize,
        slots: &mut [Slot],
    ) -> bool {
        use prog::SkipInst::*;
        trace!("step: (ip={} sp={})", ip, sp);

        match self.prog.skip_insts[ip] {
            SkipMatch(_) => { // same as normal pikevm
                // TODO(ethan):regexset
                trace!("step: MATCH");
                let thread_caps = run_queue.caps(ip);
                for (slot, val) in slots.iter_mut().zip(thread_caps.iter()) {
                    *slot = *val;
                }
                true
            },

            // control flow should always be handled by `add`
            SkipSplit(_) | SkipSave(_) => false,

            // instructions that need to look at the input get a bounds
            // check
            _ => {
                if sp >= self.input.as_bytes().len() {
                    return false;
                }

                match self.prog.skip_insts[ip] {
                    SkipSkipByte(ref inst) => {
                        if inst.c == self.input.as_bytes()[sp] {
                            self.add(run_queue, ip, inst.goto, sp + inst.skip);
                        }
                        false
                    },
                    SkipSkipRanges(ref inst) => {
                        let c = self.input.as_bytes()[sp];
                        if inst.ranges.iter()
                               .any(|&(start, end)| start <= c && c <= end) {
                            self.add(run_queue, ip, inst.goto, sp + inst.skip);
                        }
                        false
                    }
                    ref inst => unreachable!("unhandled inst: {:?}", inst),
                }
            }
        }
    }

    /// Very simmilar to the normal PikeVM add.
    fn add(
        &mut self,
        run_queue: &mut RunQueue,

        // The ip with the capture groups we want to forward
        // This guy's capture group slice will be used as
        // mutable scratch space for while we walk the branching
        // tree of instructions reachable from ip_root_nodet.
        ip_caps: usize,

        // the ip which is the root of the the nondeterminsitic
        // tree we want to trace and add to the runqueue
        ip_root_nodet: usize,
        sp: usize,
    ) {
        trace!("add: (ip_caps={} ip_root={} sp={}) caps={:?}",
                    ip_caps, ip_root_nodet, sp, run_queue.caps(ip_caps));

        self.stack.push(FollowEpsilon::IP(ip_root_nodet));
        while let Some(frame) = self.stack.pop() {
            match frame {
                FollowEpsilon::IP(ip) => {
                    self.add_step(run_queue, ip_caps, ip, sp);
                }
                FollowEpsilon::Capture { slot, pos } => {
                    // TODO(ethan): I don't like recomputing caps here, but
                    // I don't know how to get at it and still keep the
                    // borrow checker happy.
                    run_queue.caps(ip_caps)[slot] = pos;
                }
            }
        }
    }

    fn add_step(
        &mut self,
        run_queue: &mut RunQueue,

        // the root instruction pointer which has the capture groups
        // we should forward.
        ip_caps: usize,

        // the current ip
        mut ip: usize,
        sp: usize,
    ) {
        use prog::SkipInst::*;
        // trace!("add_step: (ip_caps={} ip={} sp={})", ip_caps, ip, sp);

        loop {
            // put internally makes sure that we don't double
            // push something.

            match self.prog.skip_insts[ip] {
                SkipSave(ref inst) => {
                    // TODO(ethan): How do I cache this outside of the loop?
                    let thread_caps = run_queue.caps(ip_caps);

                    if inst.slot < thread_caps.len() {
                        self.stack.push(FollowEpsilon::Capture {
                            slot: inst.slot,
                            pos: thread_caps[inst.slot],
                        });
                        thread_caps[inst.slot] = Some(sp);
                        trace!("add_step: (ip_caps={} ip={} sp={}) save caps={:?}",
                                ip_caps, ip, sp, thread_caps);
                    }
                    ip = inst.goto;
                }
                SkipSplit(ref inst) => {
                    self.stack.push(FollowEpsilon::IP(inst.goto2));
                    trace!("add_step: (ip_caps={} ip={} sp={}) split g1={} g2={}",
                                ip_caps, ip, sp, inst.goto1, inst.goto2);
                    ip = inst.goto1;
                }
                SkipMatch(_) | SkipSkipByte(_) | SkipSkipRanges(_) => {
                    run_queue.put(ip, sp);
                    trace!("add_step: (ip_caps={} ip={} sp={}) adding leaf thread",
                                ip_caps, ip, sp);
                    run_queue.copy_caps_to(ip_caps, ip, sp);
                    return;
                }
            }
        }
    }
}

// TODO(ethan): The normal bounded backtracker is faster in small cases
//              mostly because it does not have to copy captures around.
//              The PikeVM only starts to win when the backtracker goes
//              exponential (aka on large inputs). After finishing the
//              SkipPikeVM, I should see about implimenting a
//              SkipBoundedBacktracker.
#[cfg(test)]
mod tests {
    use super::{RunQueue, RUN_QUEUE_RING_SIZE};

    #[test]
    fn rq_putpop() {
        let mut rq = RunQueue::new();
        rq.resize(10, 2);

        rq.put(0, 0);
        match rq.pop() {
            Some((ip, sp)) => {
                assert_eq!(0, sp);
                assert_eq!(0, ip);
            }
            None => assert!(false),
        }
    }

    #[test]
    fn rq_ordering() {
        let mut rq = RunQueue::new();
        rq.resize(10, 2);

        let mut xs: Vec<usize> = vec![5, 4, 0, 8, 6, 1];

        for x in &xs {
            rq.put(*x, *x);
        }

        let mut ys = vec![];
        loop {
            while let Some((y, _)) = rq.pop() {
                ys.push(y);
            }
            if !rq.advance() {
                break;
            }
        }

        xs.sort();
        assert_eq!(xs, ys);
    }

    // put is idempotent within string offsets
    #[test]
    fn rq_idempotent_put() {
        let mut rq = RunQueue::new();
        rq.resize(10, 2);

        rq.put(0, 0);
        rq.put(0, 1);
        rq.put(1, 2);
        rq.put(1, 2);

        let mut ys = vec![];
        loop {
            while let Some((y, _)) = rq.pop() {
                ys.push(y);
            }
            if !rq.advance() {
                break;
            }
        }

        assert_eq!(vec![0, 0, 1], ys);
    }

    #[should_panic]
    #[test]
    fn rq_out_of_bounds_sp() {
        let mut rq = RunQueue::new();
        rq.resize(10, 2);
        rq.put(0, RUN_QUEUE_RING_SIZE + 1);
    }

    #[should_panic]
    #[test]
    fn rq_out_of_bounds_ip() {
        let mut rq = RunQueue::new();
        rq.resize(10, 2);
        rq.put(11, 0);
    }

    #[test]
    fn rq_putpop_nonzero() {
        let mut rq = RunQueue::new();
        rq.resize(10, 2);
        rq.put(1, 1);

        assert_eq!(None, rq.pop());

        rq.advance(); // Now it is in position.

        if let Some((ip, sp)) = rq.pop() {
            assert_eq!(1, sp);
            assert_eq!(1, ip);
        } else {
            assert!(false);
        }
    }

    #[test]
    fn rq_putcaps() {
        let mut rq = RunQueue::new();
        rq.resize(10, 2);
        rq.put(0, 0);
        rq.caps(0);
    }
}

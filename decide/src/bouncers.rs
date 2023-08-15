use crate::{Certificate, Decider};
use crate::turing::{Command, Configuration, Dir, TM, OutOfSpace};
use crate::memo::Memo;
use enum_map::Enum;
use itertools::Itertools;
use bumpalo::Bump;
use std::collections::VecDeque;
use std::fmt;

const SPACE_LIMIT: usize = 1024;
const TIME_LIMIT: u32 = 250000;

#[derive(Clone, Debug)]
pub struct Cert {
    run_steps: u32,
}

pub fn decide_bouncer(tm: &TM) -> Result<Cert, FailReason> {
    let mut buf = [false; SPACE_LIMIT];
    let mut detector = RecordDetect::new(Configuration::new(&mut buf));

    let mut records = vec![];
    let reason = loop {
        match detector.next_record(tm) {
            Ok(record) => records.push(record),
            Err(reason) => break reason,
        }
    };

    let mut shift_buf = vec![];

    for progression in find_progressions(&records) {
        let state = progression[1].state;
        let dir = progression[1].dir;
        if let Some(symbolic) = split_tapes(progression) {
            let Some(cert) = SymbolicTM::with(tm, &symbolic, state, dir, |mut tm|
            {
                // `initial` is like `symbolic`, but aligned
                let initial = tm.tape.clone();

                while let Ok(()) = tm.step(&mut shift_buf) {
                    if tm.state == state &&
                        tm.is_on_edge(dir) &&
                        tm.is_special_case_of(initial.iter().copied())
                    {
                        return Some(Cert {
                            run_steps: progression[1].steps_taken,
                        });
                    }
                }

                None
            }) else { continue };

            return Ok(cert);
        }
    }

    Err(reason)
}

// Check whether `tape` is a special-case of `stencil`, assuming both
// are left-aligned.
fn is_special_case_left<'a, 'b>(
    tape: impl Iterator<Item = Segment<'a>> + DoubleEndedIterator,
    stencil: impl Iterator<Item = Segment<'b>> + DoubleEndedIterator,
) -> bool {
    let mut tape = tape.rev().peekable();
    let mut stencil = stencil.rev().peekable();

    while let Some(seg) = tape.peek() {
        match seg {
            Segment::Repeat(_) => {
                if stencil.next() != tape.next() {
                    return false;
                }
            }
            Segment::Sym(_) => {
                match stencil.peek() {
                    None => return false,
                    Some(Segment::Sym(_)) => {
                        if tape.next() != stencil.next() {
                            return false;
                        }
                    }
                    Some(Segment::Repeat(seg)) => {
                        for s in seg.iter().copied().rev() {
                            if tape.next() != Some(Segment::Sym(s)) {
                                return false;
                            }
                        }
                    }
                    Some(Segment::End) => unreachable!(),
                }
            }
            Segment::End => unreachable!(),
        }
    }

    stencil.next().is_none()
}

// Check whether `tape` is a special-case of `stencil`, assuming both
// are right-aligned.
fn is_special_case_right<'a, 'b>(
    tape: impl Iterator<Item = Segment<'a>>,
    stencil: impl Iterator<Item = Segment<'b>>,
) -> bool {
    let mut tape = tape.peekable();
    let mut stencil = stencil.peekable();

    while let Some(seg) = tape.peek() {
        match seg {
            Segment::Repeat(_) => {
                if stencil.next() != tape.next() {
                    return false;
                }
            }
            Segment::Sym(_) => {
                match stencil.peek() {
                    None => return false,
                    Some(Segment::Sym(_)) => {
                        if tape.next() != stencil.next() {
                            return false;
                        }
                    }
                    Some(Segment::Repeat(seg)) => {
                        for s in seg.iter().copied() {
                            if tape.next() != Some(Segment::Sym(s)) {
                                return false;
                            }
                        }
                    }
                    Some(Segment::End) => unreachable!(),
                }
            }
            Segment::End => unreachable!(),
        }
    }

    stencil.next().is_none()
}

#[derive(Debug)]
struct SymbolicTM<'a> {
    tm: &'a TM,
    bump: &'a Bump,
    tape: VecDeque<Segment<'a>>,
    state: u8,
    dir: Dir,
    pos: usize,
    steps_taken: u32,
}

impl<'bump> SymbolicTM<'bump> {
    fn with<U>(
        tm: &TM,
        tape: &[Segment<'_>],
        state: u8,
        dir: Dir,
        f: impl for<'a> FnOnce(SymbolicTM<'a>) -> U,
    ) -> U {
        let bump = Bump::new();
        let pos = match dir {
            Dir::L => 0,
            Dir::R => tape.len(),
        };

        let mut tm = SymbolicTM {
            tm,
            bump: &bump,
            tape: tape.iter().copied().collect(),
            state,
            dir,
            pos,
            steps_taken: 0,
        };

        tm.align();

        f(tm)
    }

    fn is_special_case_of<'a>(
        &self,
        stencil: impl Iterator<Item = Segment<'a>> + DoubleEndedIterator,
    ) -> bool {
        match self.dir {
            Dir::L => is_special_case_right(self.tape.iter().copied(), stencil),
            Dir::R => is_special_case_left(self.tape.iter().copied(), stencil),
        }
    }

    fn is_on_edge(&self, dir: Dir) -> bool {
        if dir != self.dir {
            return false;
        }

        match dir {
            Dir::L => self.pos == 0,
            Dir::R => self.pos == self.tape.len(),
        }
    }

    /// Given a `Segment::Repeat` at index `i`, shift it left as far as possible.
    fn align_segment_left(&mut self, i: usize) {
        let Segment::Repeat(seg) = self.tape[i] else {
            panic!("align_segment_left: invalid index");
        };

        let shift = self.tape.iter().copied()
            .take(i).rev()
            .zip(seg.iter().copied().rev().cycle())
            .take_while(|&(seg, s)| seg == Segment::Sym(s))
            .count();

        if shift == 0 {
            return;
        }

        for k in (i - shift..i).rev() {
            self.tape[k + 1] = self.tape[k];
        }

        let seg = self.bump.alloc_slice_copy(seg);
        seg.rotate_right(shift % seg.len());

        self.tape[i - shift] = Segment::Repeat(seg);
    }

    /// Given a `Segment::Repeat` at index `i`, shift it right as far as possible.
    fn align_segment_right(&mut self, i: usize) {
        let Segment::Repeat(seg) = self.tape[i] else {
            panic!("align_segment_right: invalid index");
        };

        let shift = self.tape.iter().copied()
            .skip(i + 1)
            .zip(seg.iter().copied().cycle())
            .take_while(|&(seg, s)| seg == Segment::Sym(s))
            .count();

        if shift == 0 {
            return;
        }

        for k in i..i + shift {
            self.tape[k] = self.tape[k + 1];
        }

        let seg = self.bump.alloc_slice_copy(seg);
        seg.rotate_left(shift % seg.len());

        self.tape[i + shift] = Segment::Repeat(seg);
    }

    fn align(&mut self) {
        for i in 0..self.pos {
            if let Segment::Repeat(_) = self.tape[i] {
                self.align_segment_left(i);
            }
        }

        for i in (self.pos..self.tape.len()).rev() {
            if let Segment::Repeat(_) = self.tape[i] {
                self.align_segment_right(i);
            }
        }
    }

    fn head_segment(&mut self) -> Segment<'_> {
        match self.dir {
            Dir::L => {
                if self.pos == 0 {
                    self.tape.push_front(Segment::Sym(false));
                    self.pos = 1;
                }

                self.tape[self.pos - 1]
            }
            Dir::R => {
                if self.pos == self.tape.len() {
                    self.tape.push_back(Segment::Sym(false));
                }

                self.tape[self.pos]
            }
        }
    }

    fn tape_pos(&self) -> usize {
        match self.dir {
            Dir::L => self.pos - 1,
            Dir::R => self.pos,
        }
    }

    fn write_head(&mut self, seg: Segment<'bump>) {
        let pos = self.tape_pos();
        self.tape[pos] = seg;
    }

    fn move_head(&mut self, dir: Dir) {
        if dir != self.dir {
            self.dir = dir;
        } else {
            match dir {
                Dir::L => self.pos -= 1,
                Dir::R => self.pos += 1,
            }
        }
    }

    fn take_step(&mut self) -> Result<(), ()> {
        self.steps_taken += 1;

        if self.steps_taken > TIME_LIMIT {
            return Err(());
        }

        Ok(())
    }

    fn step(&mut self, shift_buf: &mut Vec<bool>) -> Result<(), ()> {
        self.take_step()?;
        let seg = self.head_segment();

        match seg {
            Segment::Sym(sym) => {
                match self.tm.code[self.state as usize][sym as usize] {
                    Command::Halt => return Err(()),
                    Command::Step { write, dir, next } => {
                        self.write_head(Segment::Sym(write));
                        self.move_head(dir);
                        self.state = next;
                    }
                }
            }
            Segment::Repeat(seg) => {
                let seg_len = seg.len();
                let (l, r) = self.shift_range();
                let mut config = self.slice_config(l, r, shift_buf);
                let initial_pos = config.pos;
                let mut leftmost = config.pos as isize;
                let mut rightmost = config.pos as isize;
                while let Ok(true) = config.step(self.tm) {
                    leftmost = leftmost.min(config.pos as isize);
                    rightmost = rightmost.max(config.pos as isize);
                    self.take_step()?;
                }

                if config.state != self.state {
                    return Err(());
                }

                let leftmost = leftmost as usize;
                let rightmost = rightmost as usize;

                match self.dir {
                    Dir::L => {
                        if config.pos != usize::MAX {
                            return Err(());
                        }

                        let tail_len = rightmost - initial_pos;
                        let tail = config.tape.iter().copied().take(tail_len)
                            .map(Segment::Sym);
                        if !self.tape.range(self.pos..self.pos + tail_len)
                                .copied()
                                .eq(tail.clone())
                        {
                            return Err(());
                        }

                        self.move_head(Dir::L);
                        self.tape.range_mut(self.pos..self.pos + tail_len)
                            .zip(tail).for_each(|(pos, sym)| *pos = sym);
                        let seg = &config.tape[tail_len..tail_len + seg_len];
                        let seg = self.bump.alloc_slice_copy(seg);
                        self.tape[self.pos + tail_len] = Segment::Repeat(seg);
                        self.align_segment_right(self.pos + tail_len);
                    }
                    Dir::R => {
                        if config.pos != config.tape.len() {
                            return Err(());
                        }

                        let tail_len = initial_pos - leftmost;
                        let tail_pos = config.tape.len() - tail_len;
                        let tail = config.tape.iter().copied().skip(tail_pos)
                            .map(Segment::Sym);
                        if !self.tape.range(self.pos - tail_len..self.pos)
                            .copied()
                            .eq(tail.clone())
                        {
                            return Err(());
                        }

                        self.move_head(Dir::R);
                        self.tape.range_mut(self.pos - tail_len..self.pos)
                            .zip(tail).for_each(|(pos, sym)| *pos = sym);
                        let seg = &config.tape[tail_pos - seg_len..tail_pos];
                        let seg = self.bump.alloc_slice_copy(seg);
                        self.tape[self.pos - tail_len - 1] = Segment::Repeat(seg);
                        self.align_segment_left(self.pos - tail_len - 1);
                    }
                }

                /*
                let if config.pos == usize::MAX {
                    if self.dir != Dir::L {
                        return Err(());
                    }
                } else if config.pos == config.tape.len() {
                    if self.dir != Dir::R {
                        return Err(());
                    }
                } else {
                    unreachable!();
                }
                */
            }
            Segment::End => unreachable!(),
        }

        Ok(())
    }

    /// Find the segment of the tape that can be used during a shift rule.
    fn shift_range(&self) -> (usize, usize) {
        match self.dir {
            Dir::L => {
                let pos = self.tape_pos();
                let tail = self.tape.range(pos + 1..)
                    .take_while(|seg| matches!(seg, Segment::Sym(_))).count();
                (pos, pos + tail + 1)
            }
            Dir::R => {
                let pos = self.tape_pos();
                let tail = self.tape.range(0..pos).rev()
                    .take_while(|seg| matches!(seg, Segment::Sym(_))).count();
                (pos - tail, pos + 1)
            }
        }
    }

    /// Return a `Configuration` matching `self.tape[l..r]`
    fn slice_config<'buf>(
        &mut self,
        l: usize,
        r: usize,
        buf: &'buf mut Vec<bool>,
    ) -> Configuration<'buf> {
        buf.clear();
        assert!((l..=r).contains(&self.pos));

        let mut pos = None;

        for (i, seg) in (l..r).zip(self.tape.range(l..r)) {
            if i == self.pos {
                pos = Some(buf.len());
            }

            match *seg {
                Segment::Sym(sym) => {
                    buf.push(sym);
                }
                Segment::Repeat(seg) => {
                    buf.extend_from_slice(seg);
                }
                Segment::End => unreachable!(),
            }
        }

        let pos = pos.unwrap_or(buf.len());
        let pos = match self.dir {
            Dir::L => pos - 1,
            Dir::R => pos,
        };

        Configuration {
            state: self.state,
            pos,
            tape: buf,
        }
    }
}

impl fmt::Display for SymbolicTM<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for seg in self.tape.range(0..self.pos) {
            write!(f, "{seg} ")?;
        }

        let state = b"ABCDE"[self.state as usize] as char;

        match self.dir {
            Dir::L => write!(f, "<{state}")?,
            Dir::R => write!(f, "{state}>")?,
        }

        for seg in self.tape.range(self.pos..) {
            write!(f, " {seg}")?;
        }

        Ok(())
    }
}

/// Given a list of tape records achieved by the Turing machine, find sequences
/// that match the heuristic that:
///  - the tape lengths are in an arithmetic progression
///  - the step counts are in a quadratic progression
///  - the pattern extends until the end of the list of records
fn find_progressions(records: &[Record]) -> Vec<[&Record; 3]> {
    let mut progressions = vec![];

    for k in 1..=(records.len() / 3) {
        for i0 in 0..k {
            let mut i = i0;
            while i < records.len() {
                let state = records[i].state;
                let dir = records[i].dir;

                let mut diffs = records.iter().skip(i)
                    .step_by(k)
                    .take_while(|record| {
                        record.state == state && record.dir == dir
                    })
                    .map(|record| record.steps_taken)
                    .tuple_windows()
                    .map(|(a, b)| b - a)
                    .tuple_windows()
                    .map(|(a, b)| b - a);
                let Some(diff) = diffs.next() else { break };
                let length = diffs.take_while(|&d| d == diff).count();
                // The index that would be included if we wanted to extend
                // the progression.
                let next_index = i + (length + 4) * k;

                if length > 0 && next_index >= records.len() {
                    let records = records.iter()
                        .skip(i).step_by(k).take(3);
                    let records = array_init::from_iter(records).unwrap();
                    progressions.push(records);
                }

                // We allow for an overlap of two elements, since that is the
                // maximum two different quadratic progressions can overlap by.
                i += k * (length + 1);
            }
        }
    }

    progressions
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Segment<'a> {
    Repeat(&'a [bool]),
    Sym(bool),
    End,
}

impl fmt::Display for Segment<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Segment::Sym(false) => f.write_str("0"),
            Segment::Sym(true) => f.write_str("1"),
            Segment::Repeat(seg) => {
                f.write_str("(")?;
                for s in seg {
                    match s {
                        false => f.write_str("0")?,
                        true => f.write_str("1")?,
                    }
                }
                f.write_str(")")
            }
            Segment::End => f.write_str("$"),
        }
    }
}

/// Find a symbolic tape matching a sequence of 3 records meeting the heuristic.
fn split_tapes(records: [&Record; 3]) -> Option<Vec<Segment<'_>>> {
    let s0 = &records[0].tape;
    let s1 = &records[1].tape;
    let s2 = &records[2].tape;

    // We index the DP array by the pair of
    //   (symbols consumed from s0, symbols used in repeaters).
    // The indices into all three tapes can be recovered from this.
    let f = |(i0, d), memo: &Memo<Option<Segment>, _, _>| -> Option<Segment> {
        let i1 = i0 + d;
        let i2 = i0 + 2 * d;

        // If i0 and i1 point to the end, then i2 also does
        if i0 == s0.len() && i1 == s1.len() {
            return Some(Segment::End);
        }

        if i0 < s0.len() && i1 < s1.len() && i2 < s2.len() &&
            s0[i0] == s1[i1] && s1[i1] == s2[i2] &&
            memo.get((i0 + 1, d)).is_some()
        {
            return Some(Segment::Sym(s0[i0]));
        }

        let mut best = None;
        let remaining_s0 = s0.len() - i0;
        let remaining_s1 = s1.len() - i1;
        for k in 1..=remaining_s1 - remaining_s0 {
            if i1 + k > s1.len() || i2 + 2 * k > s2.len() {
                break;
            }

            if s1[i1 + k - 1] != s2[i2 + k - 1] {
                break;
            }

            if s2[i2..i2 + k] == s2[i2 + k..i2 + 2 * k] &&
                memo.get((i0, d + k)).is_some()
            {
                best = Some(Segment::Repeat(&s2[i2..i2 + k]));
            }
        }

        best
    };

    let memo = Memo::new((s0.len() + 1, s1.len() - s0.len() + 1), &f);
    let mut result = vec![];
    let mut i0 = 0;
    let mut d = 0;

    loop {
        match memo.get((i0, d))? {
            Segment::Sym(s) => {
                i0 += 1;
                result.push(Segment::Sym(s));
            }
            Segment::Repeat(seg) => {
                d += seg.len();
                result.push(Segment::Repeat(seg));
            }
            Segment::End => break
        }
    }

    Some(result)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Enum)]
pub enum FailReason {
    OutOfSpace,
    OutOfTime,
    Halted,
}

struct RecordDetect<'a> {
    conf: Configuration<'a>,
    steps_taken: u32,
    // invariant: record_left <= record_right
    record_left: usize,
    record_right: usize,
}

#[derive(Debug)]
struct Record {
    dir: Dir,
    steps_taken: u32,
    state: u8,
    tape: Vec<bool>,
}

impl<'a> RecordDetect<'a> {
    fn new(conf: Configuration<'a>) -> Self {
        let pos = conf.pos;
        Self {
            conf,
            steps_taken: 0,
            record_left: pos,
            record_right: pos,
        }
    }

    fn make_record(&mut self, dir: Dir) -> Record {
        Record {
            dir,
            tape: self.conf.tape[self.record_left..=self.record_right].to_vec(),
            steps_taken: self.steps_taken,
            state: self.conf.state,
        }
    }

    fn next_record(&mut self, tm: &TM) -> Result<Record, FailReason> {
        while self.steps_taken < TIME_LIMIT {
            self.steps_taken += 1;

            match self.conf.step(tm) {
                Ok(false) => return Err(FailReason::Halted),
                Ok(true) => (),
                Err(OutOfSpace) => return Err(FailReason::OutOfSpace),
            }

            let pos = self.conf.pos;

            if self.record_right < pos {
                let record = self.make_record(Dir::R);
                self.record_right = pos;
                return Ok(record);
            } else if pos < self.record_left {
                let record = self.make_record(Dir::L);
                self.record_left = pos;
                return Ok(record);
            }
        }

        Err(FailReason::OutOfTime)
    }
}

impl Cert {
    pub fn to_bytes(&self) -> [u8; 4] {
        self.run_steps.to_be_bytes()
    }
}

pub struct Bouncers;

impl Decider for Bouncers {
    type Error = FailReason;
    const NAME: &'static str = "Bouncers";

    fn decide(tm: &TM) -> Result<Certificate, FailReason> {
        decide_bouncer(tm).map(From::from)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

/*
    #[test]
    fn check_segment_size() {
        #[derive(Clone, Copy, Debug, PartialEq)]
        enum Segment<'a> {
            Repeat(&'a [bool]),
            Sym(Option<bool>),
        }
        assert_eq!(std::mem::size_of::<Segment<'_>>(), 16);
    }
    */

    #[test]
    fn basic_bouncer() {
        let tm: TM = "1RB1LE_1RC0LC_1LD0RA_0LA1RA_---0LB".parse().unwrap();
        assert!(decide_bouncer(&tm).is_ok());
    }

    #[test]
    fn four_partitions_bouncer() {
        let tm: TM = "1RB0RD_1LC1LE_1RA1LB_---0RC_1LB0LE".parse().unwrap();
        assert!(decide_bouncer(&tm).is_ok());
    }

    #[test]
    fn moving_bouncer() {
        let tm: TM = "1RB0LC_0LA1RC_0LD0LE_1LA1RA_---1LC".parse().unwrap();
        assert!(decide_bouncer(&tm).is_ok());
    }

    #[test]
    fn asymmetric_bouncer() {
        let tm: TM = "1RB---_0RC0RA_0LD0RD_1LE0LE_0LA0LB".parse().unwrap();
        assert!(decide_bouncer(&tm).is_ok());
    }
}

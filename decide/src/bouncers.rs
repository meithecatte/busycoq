use crate::turing::{Command, Configuration, Dir, TM, OutOfSpace};
use crate::memo::Memo;
use enum_map::Enum;
use itertools::Itertools;
use bumpalo::Bump;
use std::collections::VecDeque;
use std::fmt;

const SPACE_LIMIT: usize = 1024;
const TIME_LIMIT: u32 = 20000;

pub fn decide_bouncer(tm: &TM) {
    let mut buf = [false; SPACE_LIMIT];
    let mut detector = RecordDetect::new(Configuration::new(&mut buf));

    let mut records = vec![];
    while let Ok(record) = detector.next_record(tm) {
        records.push(record);
    }

    for progression in find_progressions(&records) {
        let state = progression[1].state;
        let dir = progression[1].direction;
        if let Some(symbolic) = split_tapes(progression) {
            SymbolicTM::with(tm, &symbolic, state, dir, |mut tm|
                -> Result<(), ()>
            {
                println!("{tm}");

                while let Ok(()) = tm.step() {
                    println!("{tm}");
                }

                Ok(())
            }).unwrap();
            break;
        }
    }
}

#[derive(Debug)]
struct SymbolicTM<'a> {
    tm: &'a TM,
    bump: &'a Bump,
    tape: VecDeque<Segment<'a>>,
    state: u8,
    direction: Dir,
    position: usize,
    shift_buf: Vec<bool>,
}

impl<'bump> SymbolicTM<'bump> {
    fn with<U>(
        tm: &TM,
        tape: &[Segment<'_>],
        state: u8,
        direction: Dir,
        f: impl for<'a> FnOnce(SymbolicTM<'a>) -> U,
    ) -> U {
        let bump = Bump::new();
        let position = match direction {
            Dir::L => 0,
            Dir::R => tape.len(),
        };

        let mut tm = SymbolicTM {
            tm,
            bump: &bump,
            tape: tape.iter().copied().collect(),
            state,
            direction,
            position,
            shift_buf: vec![],
        };

        tm.align();

        f(tm)
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
        for i in 0..self.position {
            if let Segment::Repeat(_) = self.tape[i] {
                self.align_segment_left(i);
            }
        }

        for i in (self.position..self.tape.len()).rev() {
            if let Segment::Repeat(_) = self.tape[i] {
                self.align_segment_right(i);
            }
        }
    }

    fn head_segment(&mut self) -> Segment<'_> {
        match self.direction {
            Dir::L => {
                if self.position == 0 {
                    self.tape.push_front(Segment::Sym(false));
                    self.position = 1;
                }

                self.tape[self.position - 1]
            }
            Dir::R => {
                if self.position == self.tape.len() {
                    self.tape.push_back(Segment::Sym(false));
                }

                self.tape[self.position]
            }
        }
    }

    fn write_head(&mut self, seg: Segment<'bump>) {
        match self.direction {
            Dir::L => self.tape[self.position - 1] = seg,
            Dir::R => self.tape[self.position] = seg,
        }
    }

    fn move_head(&mut self, dir: Dir) {
        if dir != self.direction {
            self.direction = dir;
        } else {
            match dir {
                Dir::L => self.position -= 1,
                Dir::R => self.position += 1,
            }
        }
    }

    fn step(&mut self) -> Result<(), ()> {
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
                todo!()
            }
            Segment::End => unreachable!(),
        }

        Ok(())
    }
}

impl fmt::Display for SymbolicTM<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for seg in self.tape.range(0..self.position) {
            write!(f, "{seg} ")?;
        }

        let state = b"ABCDE"[self.state as usize] as char;

        match self.direction {
            Dir::L => write!(f, "<{state}")?,
            Dir::R => write!(f, "{state}>")?,
        }

        for seg in self.tape.range(self.position..) {
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
                let direction = records[i].direction;

                let mut diffs = records.iter().skip(i)
                    .step_by(k)
                    .take_while(|record| {
                        record.state == state && record.direction == direction
                    })
                    .map(|record| record.steps_taken)
                    .tuple_windows()
                    .map(|(a, b)| b - a)
                    .tuple_windows()
                    .map(|(a, b)| b - a);
                let Some(diff) = diffs.next() else { break };
                let length = diffs.take_while(|&d| d == diff).count();
                let next_index = i + (length + 4) * k;

                if length > 0 && next_index >= records.len() {
                    let records = records.iter()
                        .skip(i).step_by(k).take(3);
                    let records = array_init::from_iter(records).unwrap();
                    progressions.push(records);
                }

                // length = 1 => 4 elements
                i += length + 1;
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

    let f = |(i0, i1), memo: &Memo<Option<Segment>, _, _>| -> Option<Segment> {
        if i0 == s0.len() && i1 == s1.len() {
            return Some(Segment::End);
        }

        let i2 = i1 + (i1 - i0);
        if i0 < s0.len() && i1 < s1.len() &&
            s0[i0] == s1[i1] && s1[i1] == s2[i2] &&
            memo.get((i0 + 1, i1 + 1)).is_some()
        {
            return Some(Segment::Sym(s0[i0]));
        }

        for k in 1.. {
            if i1 + k > s1.len() || i2 + 2 * k > s2.len() {
                break;
            }

            if s1[i1 + k - 1] != s2[i2 + k - 1] {
                break;
            }

            if s2[i2..i2 + k] == s2[i2 + k..i2 + 2 * k] &&
                memo.get((i0, i1 + k)).is_some()
            {
                return Some(Segment::Repeat(&s2[i2..i2 + k]));
            }
        }

        None
    };

    let memo = Memo::new((s0.len() + 1, s1.len() + 1), &f);
    let mut result = vec![];
    let mut pos = (0, 0);

    loop {
        match memo.get(pos)? {
            Segment::Sym(s) => {
                pos = (pos.0 + 1, pos.1 + 1);
                result.push(Segment::Sym(s));
            }
            Segment::Repeat(seg) => {
                pos.1 += seg.len();
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
    direction: Dir,
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

    fn make_record(&mut self, direction: Dir) -> Record {
        Record {
            direction,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_bouncer() {
        let tm: TM = "1RB1LE_1RC0LC_1LD0RA_0LA1RA_---0LB".parse().unwrap();

        decide_bouncer(&tm);
        panic!("show us the output :<")
    }
}

use crate::turing::{Configuration, Dir, TM, OutOfSpace};
use crate::memo::Memo;
use enum_map::Enum;
use itertools::Itertools;

const SPACE_LIMIT: usize = 1024;
const TIME_LIMIT: u32 = 20000;

pub fn decide_bouncer(tm: &TM) {
    let conf = Configuration::new(SPACE_LIMIT);
    let mut detector = RecordDetect::new(conf);

    let mut records = vec![];
    while let Ok(record) = detector.next_record(tm) {
        records.push(record);
    }

    for progression in find_progressions(&records) {
        if let Some(symbolic) = split_tapes(progression) {
            dbg!(symbolic);
            break;
        }
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

#[derive(Clone, Copy, Debug)]
enum Segment<'a> {
    Repeat(&'a [bool]),
    Sym(bool),
    End,
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

#[derive(Clone)]
struct RecordDetect {
    conf: Configuration,
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

impl RecordDetect {
    fn new(conf: Configuration) -> Self {
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
                self.record_right = pos;
                return Ok(self.make_record(Dir::R));
            } else if pos < self.record_left {
                self.record_left = pos;
                return Ok(self.make_record(Dir::L))
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

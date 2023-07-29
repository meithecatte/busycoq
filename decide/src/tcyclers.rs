use crate::{Certificate, Decider};
use crate::turing::{Configuration, Dir, Limit, OutOfSpace, TM};
use byteorder::{BE, WriteBytesExt};
use enum_map::Enum;
use std::io::Cursor;

const SPACE_LIMIT: usize = 4096;
const TIME_LIMIT: u32 = 1000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cert {
    /// The side of the tape the record is on.
    dir: Dir,
    /// Number of steps taken before first reaching the record.
    n0: u32,
    /// Number of steps in the cycle.
    n1: u32,
    /// Number of relevant tape cells.
    k: u32,
}

#[derive(Clone)]
struct RecordDetect {
    conf: Configuration,
    num_records: usize,
    // invariant: record_left <= record_right
    record_left: usize,
    record_right: usize,
    leftmost_since_record: usize,
    rightmost_since_record: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Enum)]
pub enum FailReason {
    OutOfSpace,
    OutOfTime,
    Halted,
    NotApplicable,
}

struct Record {
    direction: Dir,
    record_index: usize,
    accessed_since_previous: (usize, usize),
}

impl Record {
    fn pos(&self) -> usize {
        match self.direction {
            Dir::L => self.accessed_since_previous.0,
            Dir::R => self.accessed_since_previous.1,
        }
    }
}

impl RecordDetect {
    fn new(conf: Configuration) -> Self {
        let pos = conf.pos;
        Self {
            conf,
            num_records: 0,
            record_left: pos,
            record_right: pos,
            leftmost_since_record: pos,
            rightmost_since_record: pos,
        }
    }

    fn make_record(&mut self, direction: Dir) -> Record {
        let range = (self.leftmost_since_record, self.rightmost_since_record);
        let pos = self.conf.pos;
        self.leftmost_since_record = pos;
        self.rightmost_since_record = pos;

        let record_index = self.num_records;
        self.num_records += 1;

        Record {
            direction,
            record_index,
            accessed_since_previous: range,
        }
    }

    fn step(&mut self, tm: &TM) -> Result<Option<Record>, FailReason> {
        match self.conf.step(tm) {
            Ok(false) => return Err(FailReason::Halted),
            Ok(true) => (),
            Err(OutOfSpace) => return Err(FailReason::OutOfSpace),
        }

        let pos = self.conf.pos;
        running_min(&mut self.leftmost_since_record, pos);
        running_max(&mut self.rightmost_since_record, pos);

        if self.record_right < pos {
            self.record_right = pos;
            Ok(Some(self.make_record(Dir::R)))
        } else if pos < self.record_left {
            self.record_left = pos;
            Ok(Some(self.make_record(Dir::L)))
        } else {
            Ok(None)
        }
    }
}

fn find_k(history: &[(usize, usize)], tortoise: &Record, hare: &Record) -> usize {
    let l = tortoise.record_index + 1;
    let r = hare.record_index;
    let segment = &history[l..=r];

    match hare.direction {
        Dir::L => {
            let far = segment.iter().map(|x| x.1).max().unwrap();
            far - tortoise.pos()
        }
        Dir::R => {
            let far = segment.iter().map(|x| x.0).min().unwrap();
            tortoise.pos() - far
        }
    }
}

fn compare_segment(
    dir: Dir,
    k: usize,
    a: &Configuration,
    b: &Configuration,
) -> bool {
    match dir {
        Dir::L => a.tape[a.pos..=a.pos + k] == b.tape[b.pos..=b.pos + k],
        Dir::R => a.tape[a.pos - k..=a.pos] == b.tape[b.pos - k..=b.pos],
    }
}

fn decide_tcyclers(tm: &TM) -> Result<Cert, FailReason> {
    if tm.limit == Limit::Time {
        return Err(FailReason::NotApplicable);
    }

    let mut tortoise = RecordDetect::new(Configuration::new(SPACE_LIMIT));
    let mut hare = RecordDetect::new(Configuration::new(SPACE_LIMIT));

    // Records the range of cells that were visited between two consecutive
    // records.
    let mut record_history = Vec::with_capacity(512);

    for n in 1..=TIME_LIMIT {
        let tortoise_record = tortoise.step(tm)?;
        if let Some(r) = hare.step(tm)? {
            record_history.push(r.accessed_since_previous);
        }

        if let Some(hare_record) = hare.step(tm)? {
            record_history.push(hare_record.accessed_since_previous);

            let Some(tortoise_record) = tortoise_record else { continue };
            if hare_record.direction != tortoise_record.direction { continue }
            if tortoise.conf.state != hare.conf.state { continue }
            let k = find_k(&record_history, &tortoise_record, &hare_record);
            let dir = hare_record.direction;
            if compare_segment(dir, k, &tortoise.conf, &hare.conf) {
                return Ok(Cert {
                    dir,
                    n0: n,
                    n1: n,
                    k: k as u32,
                });
            }
        }
    }

    Err(FailReason::OutOfTime)
}

fn running_min(x: &mut usize, y: usize) {
    *x = y.min(*x);
}

fn running_max(x: &mut usize, y: usize) {
    *x = y.max(*x);
}

impl Cert {
    pub fn to_bytes(self) -> [u8; 13] {
        let mut cursor = Cursor::new([0; 13]);
        cursor.write_u8(self.dir.into()).unwrap();
        cursor.write_u32::<BE>(self.n0).unwrap();
        cursor.write_u32::<BE>(self.n1).unwrap();
        cursor.write_u32::<BE>(self.k).unwrap();
        cursor.into_inner()
    }
}

pub struct TCyclers;

impl Decider for TCyclers {
    type Error = FailReason;
    const NAME: &'static str = "Translated Cyclers";

    fn decide(tm: &TM) -> Result<Certificate, FailReason> {
        decide_tcyclers(tm).map(From::from)
    }
}

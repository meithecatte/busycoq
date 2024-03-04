use crate::{Certificate, Decider, running_min, running_max};
use crate::database::DatabaseEntry;
use crate::turing::{Configuration, Dir, Limit, OutOfSpace, Sym, TM};
use enum_map::Enum;
use binrw::binrw;

const SPACE_LIMIT: usize = 4096;
const TIME_LIMIT: u32 = 20000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[binrw]
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Enum)]
pub enum FailReason {
    OutOfSpace,
    OutOfTime,
    Halted,
    NotApplicable,
}

struct RecordDetect<'a> {
    conf: Configuration<'a>,
    num_records: usize,
    steps_taken: u32,
    // invariant: record_left <= record_right
    record_left: usize,
    record_right: usize,
    leftmost_since_record: usize,
    rightmost_since_record: usize,
}

#[derive(Debug)]
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

impl<'a> RecordDetect<'a> {
    fn new(conf: Configuration<'a>) -> Self {
        let pos = conf.pos;
        Self {
            conf,
            num_records: 0,
            steps_taken: 0,
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

    fn next_record(&mut self, tm: &TM) -> Result<Record, FailReason> {
        while self.steps_taken < TIME_LIMIT {
            self.steps_taken += 1;

            match self.conf.step(tm) {
                Ok(false) => return Err(FailReason::Halted),
                Ok(true) => (),
                Err(OutOfSpace) => return Err(FailReason::OutOfSpace),
            }

            let pos = self.conf.pos;
            // bail out now, and not when we take the next step
            if pos >= SPACE_LIMIT {
                return Err(FailReason::OutOfSpace);
            }

            running_min(&mut self.leftmost_since_record, pos);
            running_max(&mut self.rightmost_since_record, pos);

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

pub fn decide_tcyclers(tm: &TM) -> Result<Cert, FailReason> {
    let mut tortoise = [Sym::S0; SPACE_LIMIT];
    let mut tortoise = RecordDetect::new(Configuration::new(&mut tortoise));
    let mut hare = [Sym::S0; SPACE_LIMIT];
    let mut hare = RecordDetect::new(Configuration::new(&mut hare));

    // Records the range of cells that were visited between two consecutive
    // records.
    let mut record_history = Vec::with_capacity(512);

    loop {
        let tortoise_record = tortoise.next_record(tm)?;
        let hare_record = hare.next_record(tm)?;
        record_history.push(hare_record.accessed_since_previous);
        let hare_record = hare.next_record(tm)?;
        record_history.push(hare_record.accessed_since_previous);

        if hare_record.direction != tortoise_record.direction { continue }
        if tortoise.conf.state != hare.conf.state { continue }
        let k = find_k(&record_history, &tortoise_record, &hare_record);
        let dir = hare_record.direction;
        if compare_segment(dir, k, &tortoise.conf, &hare.conf) {
            return Ok(Cert {
                dir,
                n0: tortoise.steps_taken,
                n1: hare.steps_taken - tortoise.steps_taken,
                k: k as u32,
            });
        }
    }
}

pub struct TCyclers;

impl Decider for TCyclers {
    type Error = FailReason;
    const NAME: &'static str = "Translated Cyclers";

    fn decide(tm: &DatabaseEntry) -> Result<Certificate, FailReason> {
        if tm.limit == Limit::Time {
            return Err(FailReason::NotApplicable);
        }

        decide_tcyclers(&tm.tm).map(From::from)
    }
}

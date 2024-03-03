use crate::{Certificate, Decider};
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
    last_visited: [u32; SPACE_LIMIT],
    steps_taken: u32,
    // invariant: record_left <= record_right
    record_left: usize,
    record_right: usize,
}

impl<'a> RecordDetect<'a> {
    fn new(conf: Configuration<'a>) -> Self {
        let pos = conf.pos;
        Self {
            conf,
            last_visited: [0; SPACE_LIMIT],
            steps_taken: 0,
            record_left: pos,
            record_right: pos,
        }
    }

    fn next_record(&mut self, tm: &TM) -> Result<Dir, FailReason> {
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

            self.last_visited[pos] = self.steps_taken;

            if self.record_right < pos {
                self.record_right = pos;
                return Ok(Dir::R);
            } else if pos < self.record_left {
                self.record_left = pos;
                return Ok(Dir::L)
            }
        }

        Err(FailReason::OutOfTime)
    }
}

fn find_k(
    dir: Dir,
    tortoise: &RecordDetect<'_>,
    hare: &RecordDetect<'_>,
) -> Option<usize> {
    match dir {
        Dir::L => {
            let it = hare.last_visited[tortoise.conf.pos..].iter()
                .take_while(|&&t| t >= tortoise.steps_taken)
                .zip(hare.conf.tape[hare.conf.pos..].iter())
                .zip(tortoise.conf.tape[tortoise.conf.pos..].iter());
            let mut k = 0;
            for ((_, a), b) in it {
                if a != b {
                    return None;
                }

                k += 1;
            }

            Some(k)
        }
        Dir::R => {
            let it = hare.last_visited[..tortoise.conf.pos].iter().rev()
                .take_while(|&&t| t >= tortoise.steps_taken)
                .zip(hare.conf.tape[..hare.conf.pos].iter().rev())
                .zip(tortoise.conf.tape[..tortoise.conf.pos].iter().rev());
            let mut k = 0;
            for ((_, a), b) in it {
                if a != b {
                    return None;
                }

                k += 1;
            }

            Some(k)
        }
    }
}

fn decide_tcyclers(tm: &TM) -> Result<Cert, FailReason> {
    let mut tortoise = [Sym::S0; SPACE_LIMIT];
    let mut tortoise = RecordDetect::new(Configuration::new(&mut tortoise));
    let mut hare = [Sym::S0; SPACE_LIMIT];
    let mut hare = RecordDetect::new(Configuration::new(&mut hare));

    loop {
        let tortoise_dir = tortoise.next_record(tm)?;
        let _ = hare.next_record(tm)?;
        let hare_dir = hare.next_record(tm)?;

        if hare_dir != tortoise_dir { continue }
        let dir = hare_dir;

        if tortoise.conf.state != hare.conf.state { continue }
        if let Some(k) = find_k(dir, &tortoise, &hare) {
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

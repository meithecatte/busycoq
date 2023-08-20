use crate::{Certificate, Decider};
use crate::turing::{Configuration, Limit, TM, OutOfSpace};
use enum_map::Enum;
use binrw::binrw;

const SPACE_LIMIT: usize = 2048;
const TIME_LIMIT: u32 = 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[binrw]
pub struct Cert {
    n: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Enum)]
pub enum FailReason {
    OutOfSpace,
    OutOfTime,
    Halted,
    NotApplicable,
}

fn check(s: Result<bool, OutOfSpace>) -> Result<(), FailReason> {
    match s {
        Ok(true) => Ok(()),
        Ok(false) => Err(FailReason::Halted),
        Err(OutOfSpace) => Err(FailReason::OutOfSpace),
    }
}

fn decide_cyclers(tm: &TM) -> Result<Cert, FailReason> {
    // If the Turing machine ran out of the 12k cell space limit,
    // then it must've done that before the first repeated configuration.
    // Thus, we would need to run the machine for at least 12k steps, and
    // we use a much lower count for that.
    //
    // Not to mention, we don't allocate 12k cells of space, so we would run
    // out of that too.
    if tm.limit == Limit::Space {
        return Err(FailReason::NotApplicable);
    }

    let mut tortoise = [false; SPACE_LIMIT];
    let mut tortoise = Configuration::new(&mut tortoise);

    let mut hare = [false; SPACE_LIMIT];
    let mut hare = Configuration::new(&mut hare);

    for n in 1..=TIME_LIMIT {
        check(tortoise.step(tm))?;
        check(hare.step(tm))?;
        check(hare.step(tm))?;

        if tortoise == hare {
            return Ok(Cert { n });
        }
    }

    Err(FailReason::OutOfTime)
}

pub struct Cyclers;

impl Decider for Cyclers {
    type Error = FailReason;
    const NAME: &'static str = "Cyclers";

    fn decide(tm: &TM) -> Result<Certificate, FailReason> {
        decide_cyclers(tm).map(From::from)
    }
}

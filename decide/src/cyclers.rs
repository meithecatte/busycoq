use crate::Certificate;
use crate::turing::{Configuration, TM, OutOfSpace};
use enum_map::Enum;

const SPACE_LIMIT: usize = 2048;
const TIME_LIMIT: u32 = 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cert {
    n: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Enum)]
pub enum FailReason {
    OutOfSpace,
    OutOfTime,
    Halted,
}

fn check(s: Result<bool, OutOfSpace>) -> Result<(), FailReason> {
    match s {
        Ok(true) => Ok(()),
        Ok(false) => Err(FailReason::Halted),
        Err(OutOfSpace) => Err(FailReason::OutOfSpace),
    }
}

fn decide_cyclers(tm: &TM) -> Result<Cert, FailReason> {
    let mut tortoise = Configuration::new(SPACE_LIMIT);
    let mut hare = Configuration::new(SPACE_LIMIT);

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

impl Cert {
    pub fn to_bytes(self) -> [u8; 4] {
        self.n.to_be_bytes()
    }
}

pub struct Cyclers;

impl crate::Decider for Cyclers {
    type Error = FailReason;
    const NAME: &'static str = "Cyclers";

    fn decide(tm: &TM) -> Result<Certificate, FailReason> {
        decide_cyclers(tm).map(From::from)
    }
}

use crate::turing::{Configuration, TM, OutOfSpace};
use enum_map::Enum;

const SPACE_LIMIT: usize = 2048;
const TIME_LIMIT: u32 = 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Certificate {
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

pub fn decide_cyclers(tm: &TM) -> Result<Certificate, FailReason> {
    let mut tortoise = Configuration::new(SPACE_LIMIT);
    let mut hare = Configuration::new(SPACE_LIMIT);

    for n in 1..=TIME_LIMIT {
        check(tortoise.step(tm))?;
        check(hare.step(tm))?;
        check(hare.step(tm))?;

        if tortoise == hare {
            return Ok(Certificate { n });
        }
    }

    Err(FailReason::OutOfTime)
}

impl Certificate {
    pub fn to_bytes(self) -> [u8; 4] {
        self.n.to_be_bytes()
    }
}

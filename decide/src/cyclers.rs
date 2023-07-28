use crate::turing::{Configuration, TM, OutOfSpace};
use enum_map::Enum;
use std::io::Cursor;
use byteorder::{BE, WriteBytesExt};

const SPACE_LIMIT: usize = 2048;
const TIME_LIMIT: u32 = 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Certificate {
    n: u32,
    k: u32,
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

    for _ in 1..=TIME_LIMIT {
        check(tortoise.step(tm))?;
        check(hare.step(tm))?;
        check(hare.step(tm))?;

        if tortoise == hare {
            tortoise = Configuration::new(SPACE_LIMIT);
            let mut n = 0;
            while tortoise != hare {
                tortoise.step(tm).unwrap();
                hare.step(tm).unwrap();
                n += 1;
            }

            hare = tortoise.clone();
            hare.step(tm).unwrap();
            let mut k = 1;
            while tortoise != hare {
                hare.step(tm).unwrap();
                k += 1;
            }

            return Ok(Certificate { n, k });
        }
    }

    Err(FailReason::OutOfTime)
}

impl Certificate {
    pub fn to_bytes(self) -> [u8; 8] {
        let mut cursor = Cursor::new([0; 8]);
        cursor.write_u32::<BE>(self.n).unwrap();
        cursor.write_u32::<BE>(self.k).unwrap();
        cursor.into_inner()
    }
}

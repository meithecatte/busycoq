use std::io::{Cursor, Error, ErrorKind, Result};
use std::fs::File;
use std::path::Path;
use byteorder::{BE, ReadBytesExt};
use crate::turing::{Limit, TM};
use memmap2::Mmap;

const HEADER_LEN: usize = 30;
const TM_SIZE: usize = 30;

#[derive(Debug)]
pub struct Database {
    pub num_timelimit: u32,
    pub num_spacelimit: u32,
    pub num_total: u32,
    pub sorted: bool,
    mmap: Mmap,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DatabaseEntry {
    /// Records the index of this Turing machine in the database.
    pub index: u32,
    /// Records which limit the machine triggered during the initial
    /// evaluation.
    pub limit: Limit,
    pub tm: TM,
}

impl Database {
    pub fn open(path: impl AsRef<Path>) -> Result<Self> {
        let file = File::open(path)?;
        let mmap = unsafe { Mmap::map(&file)? };
        let mut reader = Cursor::new(&*mmap);

        let num_timelimit = reader.read_u32::<BE>()?;
        let num_spacelimit = reader.read_u32::<BE>()?;
        let num_total = reader.read_u32::<BE>()?;
        let sorted = match reader.read_u8()? {
            0 => false,
            1 => true,
            _ => return Err(Error::new(ErrorKind::Other, "invalid value for sorted flag")),
        };

        assert_eq!(num_timelimit + num_spacelimit, num_total);

        Ok(Self {
            num_timelimit,
            num_spacelimit,
            num_total,
            sorted,
            mmap,
        })
    }

    pub fn get(&self, index: u32) -> DatabaseEntry {
        let limit = if index < self.num_timelimit {
            Limit::Time
        } else {
            Limit::Space
        };

        let offset = HEADER_LEN + TM_SIZE * index as usize;
        let data = self.mmap[offset..offset+30].try_into().unwrap();
        DatabaseEntry {
            index,
            limit,
            tm: TM::from_bytes(data),
        }
    }
}

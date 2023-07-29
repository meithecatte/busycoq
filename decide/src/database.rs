use std::io::prelude::*;
use std::io::{BufReader, Error, ErrorKind, Result};
use std::fs::File;
use std::path::Path;
use byteorder::{BE, ReadBytesExt};
use crate::turing::{Limit, TM};

#[derive(Debug)]
pub struct Database {
    pub num_timelimit: u32,
    pub num_spacelimit: u32,
    pub num_total: u32,
    pub sorted: bool,
    reader: BufReader<File>,
}

pub struct Iter<'a> {
    db: &'a mut Database,
    index: u32,
}

impl Database {
    pub fn open(path: impl AsRef<Path>) -> Result<Self> {
        let file = File::open(path)?;
        Self::from_reader(BufReader::new(file))
    }

    fn from_reader(mut reader: BufReader<File>) -> Result<Self> {
        let num_timelimit = reader.read_u32::<BE>()?;
        let num_spacelimit = reader.read_u32::<BE>()?;
        let num_total = reader.read_u32::<BE>()?;
        let sorted = match reader.read_u8()? {
            0 => false,
            1 => true,
            _ => return Err(Error::new(ErrorKind::Other, "invalid value for sorted flag")),
        };

        reader.seek_relative(30 - 13)?;

        assert_eq!(num_timelimit + num_spacelimit, num_total);

        Ok(Self {
            num_timelimit,
            num_spacelimit,
            num_total,
            sorted,
            reader,
        })
    }

    pub fn iter(&mut self) -> Iter<'_> {
        let position = self.reader.stream_position().unwrap();
        assert_eq!(position % 30, 0);
        assert!(position >= 30);
        let index = position / 30 - 1;
        Iter {
            db: self,
            index: index.try_into().unwrap(),
        }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = TM;

    fn next(&mut self) -> Option<TM> {
        let mut buf = [0; 30];
        match self.db.reader.read_exact(&mut buf) {
            Ok(()) => {},
            Err(e) if e.kind() == ErrorKind::UnexpectedEof => return None,
            Err(e) => panic!("{e}"),
        }

        let limit = if self.index < self.db.num_timelimit {
            Limit::Time
        } else {
            Limit::Space
        };

        let tm = TM::from_bytes(self.index, limit, &buf);
        self.index += 1;
        Some(tm)
    }

    fn nth(&mut self, n: usize) -> Option<TM> {
        self.index += n as u32;
        self.db.reader.seek_relative(30 * n as i64).unwrap();
        self.next()
    }
}

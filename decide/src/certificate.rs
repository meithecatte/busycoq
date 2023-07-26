use std::io::prelude::*;
use std::io::Result;
use std::io::BufWriter;
use std::fs::File;
use std::path::Path;
use byteorder::{BE, WriteBytesExt};
use crate::cyclers;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Certificate {
    Cyclers(cyclers::Certificate),
}

pub struct CertList {
    writer: BufWriter<File>,
}

impl CertList {
    pub fn create(path: impl AsRef<Path>) -> Result<Self> {
        Ok(CertList {
            writer: BufWriter::new(File::create(path)?),
        })
    }

    pub fn write_entry(&mut self, index: u32, cert: &Certificate) -> Result<()> {
        self.writer.write_u32::<BE>(index)?;
        use Certificate::*;
        match cert {
            Cyclers(cert) => {
                self.writer.write_u32::<BE>(0)?;
                self.writer.write_all(&cert.to_bytes())?;
            }
        }

        Ok(())
    }
}

impl From<cyclers::Certificate> for Certificate {
    fn from(cert: cyclers::Certificate) -> Certificate {
        Certificate::Cyclers(cert)
    }
}

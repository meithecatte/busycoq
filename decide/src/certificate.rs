use std::io::BufWriter;
use std::fs::File;
use std::path::Path;
use anyhow::Result;
use binrw::{BinWrite, binrw};
use binrw::io::NoSeek;
use byteorder::{BE, WriteBytesExt};
use crate::cyclers;
use crate::tcyclers;
use crate::backwards;
use crate::bouncers;

#[derive(Clone, Debug)]
#[binrw]
#[brw(big)]
pub enum Certificate {
    #[brw(magic = 0u8)] Cyclers(cyclers::Cert),
    #[brw(magic = 1u8)] TCyclers(tcyclers::Cert),
    #[brw(magic = 2u8)] Backwards(backwards::Cert),
    #[brw(magic = 3u8)] Bouncers(bouncers::Cert),
    #[brw(magic = 254u8)] ClosedSubset,
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
        cert.write(&mut NoSeek::new(&mut self.writer))?;
        Ok(())
    }
}

impl From<cyclers::Cert> for Certificate {
    fn from(cert: cyclers::Cert) -> Certificate {
        Certificate::Cyclers(cert)
    }
}

impl From<tcyclers::Cert> for Certificate {
    fn from(cert: tcyclers::Cert) -> Certificate {
        Certificate::TCyclers(cert)
    }
}

impl From<backwards::Cert> for Certificate {
    fn from(cert: backwards::Cert) -> Certificate {
        Certificate::Backwards(cert)
    }
}

impl From<bouncers::Cert> for Certificate {
    fn from(cert: bouncers::Cert) -> Certificate {
        Certificate::Bouncers(cert)
    }
}

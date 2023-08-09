use std::io::prelude::*;
use std::io::Result;
use std::io::BufWriter;
use std::fs::File;
use std::path::Path;
use byteorder::{BE, WriteBytesExt};
use crate::cyclers;
use crate::tcyclers;
use crate::backwards;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Certificate {
    Cyclers(cyclers::Cert),
    TCyclers(tcyclers::Cert),
    Backwards(backwards::Cert),
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
                self.writer.write_u8(0)?;
                self.writer.write_all(&cert.to_bytes())?;
            }
            TCyclers(cert) => {
                self.writer.write_u8(1)?;
                self.writer.write_all(&cert.to_bytes())?;
            }
            Backwards(cert) => {
                self.writer.write_u8(2)?;
                self.writer.write_all(&cert.to_bytes())?;
            }
        }

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

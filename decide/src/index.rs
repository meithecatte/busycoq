use std::io::{BufReader, BufWriter, ErrorKind, Result};
use std::fs::File;
use std::path::{Path, PathBuf};
use argh::FromArgs;
use byteorder::{BE, ReadBytesExt, WriteBytesExt};
use itertools::{EitherOrBoth, Itertools};

/// Reads a sequence of `u32`s without regard for any structure in the values
/// (unlike [`IndexReader`], which expects the values to be sorted.
#[derive(Debug)]
struct RawReader {
    reader: BufReader<File>,
}

impl RawReader {
    pub fn open(path: impl AsRef<Path>) -> Result<Self> {
        let file = File::open(&path)?;
        Ok(Self {
            reader: BufReader::new(file),
        })
    }
}

impl Iterator for RawReader {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        match self.reader.read_u32::<BE>() {
            Ok(v) => Some(v),
            Err(e) if e.kind() == ErrorKind::UnexpectedEof => None,
            Err(e) => panic!("{e}"),
        }
    }
}

#[derive(Debug)]
pub struct IndexReader {
    previous: Option<u32>,
    path: PathBuf,
    reader: RawReader,
}

impl IndexReader {
    pub fn open(path: impl AsRef<Path>) -> Result<Self> {
        Ok(Self {
            previous: None,
            path: path.as_ref().into(),
            reader: RawReader::open(&path)?,
        })
    }
}

impl Iterator for IndexReader {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        let v = self.reader.next()?;
        if let Some(prev) = self.previous {
            if prev == v {
                panic!("{:?}: duplicate value {v}", self.path);
            } else if prev > v {
                panic!("{:?}: not sorted: {prev} -> {v}", self.path);
            }
        }

        self.previous = Some(v);
        Some(v)
    }
}

#[derive(Debug)]
pub struct IndexWriter {
    previous: Option<u32>,
    writer: BufWriter<File>,
}

impl IndexWriter {
    pub fn create(path: impl AsRef<Path>) -> Result<Self> {
        let file = File::create(path)?;

        Ok(Self {
            previous: None,
            writer: BufWriter::new(file),
        })
    }

    pub fn write(&mut self, v: u32) -> Result<()> {
        if let Some(prev) = self.previous {
            assert!(prev < v);
        }

        self.previous = Some(v);
        self.writer.write_u32::<BE>(v)
    }
}

#[derive(FromArgs)]
#[argh(subcommand, name = "merge")]
/// Merge index files
pub struct Merge {
    /// output file
    #[argh(option, short = 'o')]
    out: PathBuf,

    /// input files
    #[argh(positional)]
    inputs: Vec<PathBuf>,

    /// allow unsorted inputs
    #[argh(switch, short = 'u')]
    unsorted: bool,
}

impl Merge {
    fn handle_inputs(&self, inputs: impl Iterator<Item=impl Iterator<Item=u32>>) {
        let mut output = IndexWriter::create(&self.out).unwrap();

        let mut duplicates = 0;
        let mut total = 0;
        for (count, value) in inputs.kmerge().dedup_with_count() {
            total += 1;

            if count > 1 {
                duplicates += 1;
            }

            output.write(value).unwrap();
        }

        println!("Wrote {total} indices");
        if duplicates > 0 {
            println!("Note: {duplicates} values occured in more than one file");
        }
    }

    pub fn run(&self) {
        if self.unsorted {
            let inputs = self.inputs.iter()
                .map(|path| {
                    let mut data = RawReader::open(path).unwrap().collect_vec();
                    data.sort();
                    data.into_iter()
                });

            self.handle_inputs(inputs);
        } else {
            let inputs = self.inputs.iter()
                .map(|path| IndexReader::open(path).unwrap().peekable());

            self.handle_inputs(inputs);
        }
    }
}

#[derive(FromArgs)]
#[argh(subcommand, name = "diff")]
/// Show differences between index files
pub struct Diff {
    #[argh(positional)]
    input1: PathBuf,

    #[argh(positional)]
    input2: PathBuf,

    /// output the indices unique for the first input to file
    #[argh(option, short = 'l')]
    output1: Option<PathBuf>,

    /// output the indices unique for the second input to file
    #[argh(option, short = 'r')]
    output2: Option<PathBuf>,

    /// don't output diff to standard output
    #[argh(switch, short = 'q')]
    quiet: bool,
}

impl Diff {
    pub fn run(&self) {
        let input1 = IndexReader::open(&self.input1).unwrap();
        let input2 = IndexReader::open(&self.input2).unwrap();

        let mut output1 = self.output1.as_ref()
            .map(|path| IndexWriter::create(path).unwrap());
        let mut output2 = self.output2.as_ref()
            .map(|path| IndexWriter::create(path).unwrap());

        for x in input1.merge_join_by(input2, |i, j| i.cmp(j)) {
            match x {
                EitherOrBoth::Both(_, _) => (),
                EitherOrBoth::Left(i) => {
                    if !self.quiet {
                        println!("< {i}");
                    }

                    if let Some(output) = &mut output1 {
                        output.write(i).unwrap();
                    }
                }
                EitherOrBoth::Right(i) => {
                    if !self.quiet {
                        println!("> {i}");
                    }

                    if let Some(output) = &mut output2 {
                        output.write(i).unwrap();
                    }
                }
            }
        }
    }
}

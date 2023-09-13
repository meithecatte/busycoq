mod api;
mod certificate;
mod database;
mod decider;
mod index;
mod memo;
mod turing;
mod undo;

use certificate::{Certificate, CertList};
use database::{Database, DatabaseEntry};
use index::IndexReader;
use decider::*;

use argh::FromArgs;
use bitvec::bitvec;
use enum_map::{EnumArray, EnumMap, enum_map};
use indicatif::{ProgressBar, ProgressStyle};
use itertools::Itertools;
use std::fmt;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU32, Ordering};
use std::thread;
use std::time::Duration;
use rayon::prelude::*;

trait Decider {
    type Error: Clone + Copy + fmt::Debug + EnumArray<AtomicU32>;
    const NAME: &'static str;

    fn decide(tm: &DatabaseEntry) -> Result<Certificate, Self::Error>;
}

struct DeciderStats<D: Decider> {
    skip: bool,
    decided: AtomicU32,
    fail_stats: EnumMap<D::Error, AtomicU32>,
}

impl<D: Decider> fmt::Display for DeciderStats<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let decided = self.decided.load(Ordering::Relaxed);
        if decided < 10000 {
            write!(f, "{decided}")
        } else {
            write!(f, "{}k", decided / 1000)
        }
    }
}

impl<D: Decider> DeciderStats<D> {
    fn new(skip: bool) -> Self {
        Self {
            skip,
            decided: AtomicU32::new(0),
            fail_stats: enum_map! { _ => AtomicU32::new(0) },
        }
    }

    fn decide(&self, tm: &DatabaseEntry) -> Option<Certificate> {
        if self.skip {
            return None;
        }

        match D::decide(tm) {
            Ok(cert) => {
                self.decided.fetch_add(1, Ordering::Relaxed);
                Some(cert)
            }
            Err(e) => {
                self.fail_stats[e].fetch_add(1, Ordering::Relaxed);
                None
            }
        }
    }

    fn print_stats(&self) {
        if !self.skip {
            println!("{}:", D::NAME);
            println!("  {:8?} Decided", self.decided);
            for (k, v) in self.fail_stats.iter() {
                println!("  {v:8?} {k:?}");
            }
        }
    }
}

#[derive(FromArgs)]
/// Busy beaver decision tool
struct TopLevel {
    #[argh(subcommand)]
    cmd: SubCommand,
}

#[derive(FromArgs)]
#[argh(subcommand)]
enum SubCommand {
    Decide(Decide),
    Merge(index::Merge),
    Diff(index::Diff),
    Query(api::Query),
}

#[derive(FromArgs)]
#[argh(subcommand, name = "decide")]
/// Run deciders and produce a certificate file
struct Decide {
    /// path to the seed database file
    #[argh(positional)]
    database: PathBuf,

    /// path to the output certificate file
    #[argh(positional)]
    certs: PathBuf,

    /// list of indices to skip
    #[argh(option, short='x')]
    exclude: Option<PathBuf>,

    /// list of indices to check
    #[argh(option, short='i')]
    indices: Option<PathBuf>,

    /// check a specific machine index
    #[argh(option, short='a')]
    ad_hoc: Vec<u32>,

    /// don't run the Cyclers decider
    #[argh(switch)]
    no_cyclers: bool,

    /// don't run the Translated Cyclers decider
    #[argh(switch)]
    no_tcyclers: bool,

    /// don't run the Backwards Reasoning decider
    #[argh(switch)]
    no_backwards: bool,

    /// don't run the Bouncers decider
    #[argh(switch)]
    no_bouncers: bool,
}

fn main() {
    let args: TopLevel = argh::from_env();
    match args.cmd {
        SubCommand::Decide(decide) => decide.run(),
        SubCommand::Merge(merge) => merge.run(),
        SubCommand::Diff(diff) => diff.run(),
        SubCommand::Query(query) => query.run(),
    }
}

impl Decide {
    fn run(self) {
        if self.exclude.is_some() && self.indices.is_some() {
            eprintln!("Cannot use both --exclude and --indices");
            return;
        }

        let db = Database::open(&self.database).unwrap();
        let indices: Vec<u32> = {
            if let Some(indices) = &self.indices {
                let mut indices = IndexReader::open(indices).unwrap()
                    .collect_vec();
                indices.extend_from_slice(&self.ad_hoc);
                indices
            } else if let Some(exclude) = &self.exclude {
                if !self.ad_hoc.is_empty() {
                    eprintln!("Cannot use both --exclude and --ad-hoc");
                }

                let mut skiplist = bitvec![0; db.num_total as usize];

                for idx in IndexReader::open(exclude).unwrap() {
                    skiplist.set(idx as usize, true);
                }

                (0..db.num_total).filter(|&x| !skiplist[x as usize]).collect()
            } else if self.ad_hoc.is_empty() {
                (0..db.num_total).collect()
            } else {
                self.ad_hoc
            }
        };

        let mut certfile = CertList::create(&self.certs).unwrap();

        let processed = AtomicU32::new(0);

        let cyclers = DeciderStats::<Cyclers>::new(self.no_cyclers);
        let tcyclers = DeciderStats::<TCyclers>::new(self.no_tcyclers);
        let backwards = DeciderStats::<BackwardsReasoning>::new(self.no_backwards);
        let bouncers = DeciderStats::<Bouncers>::new(self.no_bouncers);

        let undecided = thread::scope(|s| {
            let progress_thread = s.spawn(|| {
                let style = ProgressStyle::with_template(
                    "[{elapsed_precise}] {bar:30.cyan} {pos:>8}/{len:8} {msg} ETA {eta}"
                ).unwrap();
                let bar = ProgressBar::new(indices.len() as u64)
                    .with_style(style);
                loop {
                    let processed = processed.load(Ordering::Relaxed);
                    bar.set_message(format!("C {} TC {} BR {} B {}",
                        cyclers, tcyclers, backwards, bouncers));
                    bar.set_position(processed as u64);
                    if processed == indices.len() as u32 {
                        return;
                    }

                    thread::park_timeout(Duration::from_millis(250));
                }
            });

            let certs = indices.par_iter().with_max_len(1).map(|&index| {
                let tm = db.get(index);
                let cert = cyclers.decide(&tm)
                    .or_else(|| tcyclers.decide(&tm))
                    .or_else(|| backwards.decide(&tm))
                    .or_else(|| bouncers.decide(&tm));
                processed.fetch_add(1, Ordering::Relaxed);
                (tm.index, cert)
            }).collect::<Vec<_>>();

            let mut undecided = 0;
            for (index, cert) in certs {
                if let Some(cert) = cert {
                    certfile.write_entry(index, &cert).unwrap();
                } else {
                    undecided += 1;
                }
            }

            progress_thread.thread().unpark();
            undecided
        });

        cyclers.print_stats();
        tcyclers.print_stats();
        backwards.print_stats();
        bouncers.print_stats();
        println!("\n  {undecided:8} Undecided");
    }
}

fn running_min(x: &mut usize, y: usize) {
    *x = y.min(*x);
}

fn running_max(x: &mut usize, y: usize) {
    *x = y.max(*x);
}

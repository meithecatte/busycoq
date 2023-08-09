mod api;
mod backwards;
mod certificate;
mod cyclers;
mod database;
mod index;
mod tcyclers;
mod turing;
mod undo;

use backwards::BackwardsReasoning;
use certificate::{Certificate, CertList};
use cyclers::Cyclers;
use database::Database;
use index::IndexReader;
use tcyclers::TCyclers;
use turing::TM;

use argh::FromArgs;
use bitvec::bitvec;
use std::collections::HashMap;
use std::fmt;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;
use rayon::prelude::*;
use enum_map::{EnumArray, EnumMap, enum_map};
use indicatif::{ProgressBar, ProgressStyle};

trait Decider {
    type Error: Clone + Copy + fmt::Debug + EnumArray<AtomicU32>;
    const NAME: &'static str;

    fn decide(tm: &TM) -> Result<Certificate, Self::Error>;
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

    fn decide(&self, tm: &TM) -> Option<Certificate> {
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

    /// list of indexes to skip
    #[argh(option, short='x')]
    exclude: Option<PathBuf>,

    /// don't run the Cyclers decider
    #[argh(switch)]
    no_cyclers: bool,

    /// don't run the Translated Cyclers decider
    #[argh(switch)]
    no_tcyclers: bool,

    /// don't run the Backwards Reasoning decider
    #[argh(switch)]
    no_backwards: bool,
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
    fn run(&self) {
        let mut db = Database::open(&self.database).unwrap();
        let mut total_count = db.num_total;
        let mut skiplist = bitvec![0; db.num_total as usize];

        if let Some(exclude) = &self.exclude {
            for idx in IndexReader::open(exclude).unwrap() {
                skiplist.set(idx as usize, true);
                total_count -= 1;
            }
        }

        let indices = (0..db.num_total).filter(|&x| !skiplist[x as usize]);
        let mut certs = CertList::create(&self.certs).unwrap();
        let (tx, rx) = mpsc::channel();

        let processed = AtomicU32::new(0);

        let cyclers = DeciderStats::<Cyclers>::new(self.no_cyclers);
        let tcyclers = DeciderStats::<TCyclers>::new(self.no_tcyclers);
        let backwards = DeciderStats::<BackwardsReasoning>::new(self.no_backwards);

        thread::scope(|s| {
            s.spawn({
                let indices = indices.clone();
                move || {
                    let mut indices = indices.peekable();
                    let mut staging = HashMap::new();
                    for (index, cert) in rx {
                        staging.insert(index, cert);
                        while let Some(&index) = indices.peek() {
                            if let Some(cert) = staging.remove(&index) {
                                if let Some(cert) = cert {
                                    certs.write_entry(index, &cert).unwrap();
                                }

                                indices.next();
                            } else {
                                break
                            }
                        }
                    }
                }
            });

            let progress_thread = s.spawn(|| {
                let style = ProgressStyle::with_template(
                    "[{elapsed_precise}] {bar:30.cyan} {pos:>8}/{len:8} {msg} ETA {eta}"
                ).unwrap();
                let bar = ProgressBar::new(total_count as u64)
                    .with_style(style);
                loop {
                    let processed = processed.load(Ordering::Relaxed);
                    bar.set_message(format!("C {} TC {} BR {}",
                        cyclers, tcyclers, backwards));
                    bar.set_position(processed as u64);
                    if processed == total_count {
                        return;
                    }

                    thread::park_timeout(Duration::from_millis(250));
                }
            });

            db.indices(indices).par_bridge().for_each(|tm| {
                let cert = cyclers.decide(&tm)
                    .or_else(|| tcyclers.decide(&tm))
                    .or_else(|| backwards.decide(&tm));
                processed.fetch_add(1, Ordering::Relaxed);
                tx.send((tm.index, cert)).unwrap();
            });

            drop(tx);
            progress_thread.thread().unpark();
        });

        cyclers.print_stats();
        tcyclers.print_stats();
        backwards.print_stats();
    }
}

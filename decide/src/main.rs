mod certificate;
mod cyclers;
mod database;
mod index;
mod tcyclers;
mod turing;

use certificate::{Certificate, CertList};
use cyclers::Cyclers;
use database::Database;
use tcyclers::TCyclers;
use turing::TM;

use argh::FromArgs;
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
    fn new() -> Self {
        Self {
            decided: AtomicU32::new(0),
            fail_stats: enum_map! { _ => AtomicU32::new(0) },
        }
    }

    fn decide(&self, tm: &TM) -> Option<Certificate> {
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
        println!("{}:", D::NAME);
        println!("  {:8?} Decided", self.decided);
        for (k, v) in self.fail_stats.iter() {
            println!("  {v:8?} {k:?}");
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
}

fn main() {
    let args: TopLevel = argh::from_env();
    match args.cmd {
        SubCommand::Decide(decide) => decide.run(),
        SubCommand::Merge(merge) => merge.run(),
        SubCommand::Diff(diff) => diff.run(),
    }
}

impl Decide {
    fn run(&self) {
        let mut db = Database::open(&self.database).unwrap();
        let mut certs = CertList::create(&self.certs).unwrap();
        let (tx, rx) = mpsc::channel();
        let write_certs = thread::spawn(move || {
            let mut staging = HashMap::new();
            let mut next = 0;
            for (index, cert) in rx {
                staging.insert(index, cert);
                while let Some(cert) = staging.remove(&next) {
                    if let Some(cert) = cert {
                        certs.write_entry(next, &cert).unwrap();
                    }

                    next += 1;
                }
            }
        });

        let processed = AtomicU32::new(0);
        let num = db.num_total;

        let cyclers = DeciderStats::<Cyclers>::new();
        let tcyclers = DeciderStats::<TCyclers>::new();

        thread::scope(|s| {
            let progress_thread = s.spawn(|| {
                let style = ProgressStyle::with_template(
                    "[{elapsed_precise}] {bar:30.cyan} {pos:>8}/{len:8} {msg}"
                ).unwrap();
                let bar = ProgressBar::new(num as u64)
                    .with_style(style);
                loop {
                    let processed = processed.load(Ordering::Relaxed);
                    bar.set_message(format!("C {cyclers} TC {tcyclers}"));
                    bar.set_position(processed as u64);
                    if processed == num {
                        return;
                    }

                    thread::park_timeout(Duration::from_millis(250));
                }
            });

            db.iter().par_bridge().for_each(|tm| {
                let cert = cyclers.decide(&tm)
                    .or_else(|| tcyclers.decide(&tm));
                processed.fetch_add(1, Ordering::Relaxed);
                tx.send((tm.index, cert)).unwrap();
            });

            progress_thread.thread().unpark();
        });

        drop(tx);
        write_certs.join().unwrap();

        cyclers.print_stats();
        tcyclers.print_stats();
    }
}

mod certificate;
mod cyclers;
mod database;
mod turing;

use certificate::CertList;
use cyclers::decide_cyclers;
use database::Database;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;
use rayon::prelude::*;
use enum_map::enum_map;
use indicatif::ProgressBar;

fn main() {
    let mut db = Database::open("../seed.dat").unwrap();
    let mut certs = CertList::create("../certs.dat").unwrap();
    let (tx, rx) = mpsc::channel();
    let write_certs = thread::spawn(move || {
        for (index, cert) in rx {
            certs.write_entry(index, &cert).unwrap();
        }
    });

    let stats = enum_map! { _ => AtomicU32::new(0) };
    let decided = AtomicU32::new(0);
    let processed = AtomicU32::new(0);
    let num = db.num_timelimit;

    thread::scope(|s| {
        let progress_thread = s.spawn(|| {
            let bar = ProgressBar::new(num as u64);
            loop {
                let processed = processed.load(Ordering::Relaxed);
                bar.set_position(processed as u64);
                if processed == num {
                    return;
                }

                thread::park_timeout(Duration::from_millis(250));
            }
        });

        db.iter().take(num as usize).par_bridge().for_each(|tm| {
            match decide_cyclers(&tm) {
                Ok(cert) => {
                    decided.fetch_add(1, Ordering::Relaxed);
                    tx.send((tm.index, cert.into())).unwrap()
                }
                Err(e) => {
                    stats[e].fetch_add(1, Ordering::Relaxed);
                }
            }

            processed.fetch_add(1, Ordering::Relaxed);
        });

        progress_thread.thread().unpark();
    });

    drop(tx);
    write_certs.join().unwrap();

    println!("Decided {decided:?}");
    for (k, v) in stats.iter() {
        println!("{k:?} {v:?}");
    }
}

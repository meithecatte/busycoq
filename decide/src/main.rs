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
use rayon::prelude::*;
use enum_map::enum_map;

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
    let num = db.num_timelimit as usize;

    db.iter().take(num).par_bridge().for_each(|tm| {
        match decide_cyclers(&tm) {
            Ok(cert) => {
                tx.send((tm.index, cert.into())).unwrap()
            }
            Err(e) => {
                stats[e].fetch_add(1, Ordering::Relaxed);
            }
        }
    });

    drop(tx);
    write_certs.join().unwrap();
}

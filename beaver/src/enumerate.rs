use crate::turing::{Command, Configuration, Dir, Limit, OutOfSpace, State, Sym, TM};
use argh::FromArgs;
use itertools::Itertools;
use strum::IntoEnumIterator;
use enum_map::{enum_map, Enum, EnumMap};
use std::mem;
use std::thread;
use std::time::Duration;
use indicatif::{ProgressBar, ProgressStyle};
use std::sync::atomic::{AtomicU32, Ordering};
use rayon::prelude::*;

const TIME_LIMIT: u32 = 47_176_870;
const BUFFER_SIZE: usize = 32_768;
const SPACE_LIMIT: usize = 12_289;
const BB4: u32 = 107;
const SPLIT_LEVEL: usize = 6;

impl TM {
    fn blank() -> TM {
        TM { code: enum_map! { _ => enum_map! { _ => Command::Halt } } }
    }

    /// Return the level of the enumeration tree on which this TM is, i.e.
    /// the number of non-halting transitions that have been defined.
    fn level(&self) -> usize {
        self.code.values()
            .flat_map(|cmds| cmds.values().copied())
            .filter(|&cmd| cmd != Command::Halt)
            .count()
    }

    /// Checks whether we can replace a halting transition without creating
    /// a trivially never halting TM.
    fn can_extend(&self) -> bool {
        self.code.values()
            .flat_map(|cmds| cmds.values().copied())
            .filter(|&cmd| cmd == Command::Halt)
            .count() > 1
    }

    pub fn state_has_trans(&self, q: State) -> bool {
        self.code[q].values().any(|&cmd| cmd != Command::Halt)
    }

    pub fn state_has_halt(&self, q: State) -> bool {
        self.code[q].values().any(|&cmd| cmd == Command::Halt)
    }

    fn states_are_equiv(&self, a: State, b: State) -> bool {
        let is_either = |q| q == a || q == b;
        let state_eqv = |q1, q2| q1 == q2 || (is_either(q1) && is_either(q2));
        self.code[a].values().zip(self.code[b].values()).all(|cmds| {
            match cmds {
                (&Command::Step { write: s1, dir: d1, next: q1 },
                 &Command::Step { write: s2, dir: d2, next: q2 }) => {
                    s1 == s2 && d1 == d2 && state_eqv(q1, q2)
                }
                _ => false
            }
        })
    }

    fn should_prune(&self, a: State) -> bool {
        State::iter().any(|b| a != b && self.states_are_equiv(a, b))
    }

    fn children(&self, q: State, s: Sym) -> impl Iterator<Item = TM> + '_ {
        State::iter()
            .take_while_inclusive(move |&next| {
                // don't treat the state we're about to fill as empty
                next == q || self.state_has_trans(next)
            })
            .cartesian_product(Sym::iter())
            .cartesian_product(Dir::iter())
            .map(move |((next, write), dir)| {
                let mut tm = self.clone();
                tm.code[q][s] = Command::Step { write, dir, next };
                tm
            })
    }
}

#[derive(Debug, Enum)]
enum Prune {
    BB4,
    StateEquiv,
}

#[derive(Debug)]
enum RunResult {
    Limit(Limit),
    Halted(State, Sym, u32),
    Prune(Prune),
}

fn run(tm: &TM) -> RunResult {
    let mut tape = [Sym::S0; BUFFER_SIZE];
    let mut conf = Configuration::new(&mut tape);
    let mut l = conf.pos;
    let mut r = conf.pos;

    for t in 0..TIME_LIMIT {
        if t == BB4 && !tm.state_has_trans(State::E) {
            return RunResult::Prune(Prune::BB4);
        }

        l = l.min(conf.pos);
        r = r.max(conf.pos);
        if r - l >= SPACE_LIMIT {
            return RunResult::Limit(Limit::Space);
        }

        match conf.step(tm) {
            Ok(false) => {
                let Ok(sym) = conf.head_symbol() else {
                    eprintln!("border of tape reached. this shouldn't happen. {tm}");
                    // ...because 2 * SPACE_LIMIT < BUFFER_SIZE
                    return RunResult::Limit(Limit::Space);
                };

                return RunResult::Halted(conf.state, sym, t);
            }
            Ok(true) => continue,
            Err(OutOfSpace) => {
                return RunResult::Limit(Limit::Space);
            }
        }
    }

    RunResult::Limit(Limit::Time)
}

#[derive(Default)]
struct EnumerationResults {
    undecided: EnumMap<Limit, Vec<TM>>,
    nonhalting: u64,
    pruned: EnumMap<Prune, u64>,
    halted_count: u64,
    time_record: u32,
    best_beaver: Option<TM>,
    max_split: u32,

    /// Subtrees that are still yet to be explored
    postponed: Vec<TM>,
}

impl EnumerationResults {
    fn merge_with(&mut self, other: Self) {
        for (limit, undecided) in other.undecided {
            self.undecided[limit].extend(undecided);
        }

        self.nonhalting += other.nonhalting;

        for (prune, count) in other.pruned {
            self.pruned[prune] += count;
        }

        self.halted_count += other.halted_count;

        if other.time_record > self.time_record {
            self.time_record = other.time_record;
            self.best_beaver = other.best_beaver;
        }

        self.max_split = self.max_split.max(other.max_split);
        self.postponed.extend(other.postponed);
    }

    fn enumerate_at(&mut self, tm: TM, postpone_level: usize) {
        if tm.level() == postpone_level {
            self.postponed.push(tm);
            return;
        }

        if crate::decider::decide_fast(&tm) {
            self.nonhalting += 1;
            return;
        }

        let behavior = run(&tm);
        //println!("{}{tm} {behavior:?}", " ".repeat(tm.level() - 1));

        match behavior {
            RunResult::Limit(limit) => {
                self.undecided[limit].push(tm);
            }
            RunResult::Prune(prune) => {
                self.pruned[prune] += 1;
            }
            RunResult::Halted(q, s, t) => {
                if tm.can_extend() {
                    self.max_split = self.max_split.max(t);
                    tm.children(q, s)
                        .for_each(|tm| {
                            if tm.should_prune(q) {
                                self.pruned[Prune::StateEquiv] += 1;
                                return;
                            }

                            self.enumerate_at(tm, postpone_level);
                        });
                } else {
                    self.halted_count += 1;

                    if t > self.time_record {
                        self.time_record = t;
                        self.best_beaver = Some(tm);
                        //println!("new record: {tm} halts in {t} steps");
                    }
                }
            }
        }
    }
}

#[derive(FromArgs)]
#[argh(subcommand, name = "enumerate")]
/// Enumerate Turing machines and generate the seed database
pub struct Enumerate {
}

impl Enumerate {
    pub fn run(self) {
        let mut tm = TM::blank();
        let mut results = EnumerationResults::default();

        tm.code[State::A][Sym::S0] = Command::Step {
            write: Sym::S1,
            dir: Dir::R,
            next: State::B,
        };

        tm.code[State::B][Sym::S0] = Command::Step {
            write: Sym::S1,
            dir: Dir::R,
            next: State::C,
        };

        tm.code[State::C][Sym::S0] = Command::Step {
            write: Sym::S1,
            dir: Dir::R,
            next: State::D,
        };

        results.enumerate_at(tm, SPLIT_LEVEL);

        let tasks = mem::take(&mut results.postponed);
        let processed = AtomicU32::new(0);

        thread::scope(|s| {
            let progress_thread = s.spawn(|| {
                let style = ProgressStyle::with_template(
                    "[{elapsed_precise}] {bar:30.cyan} {pos:>8}/{len:8} {msg} ETA {eta}"
                ).unwrap();
                let bar = ProgressBar::new(tasks.len() as u64)
                    .with_style(style);
                loop {
                    let processed = processed.load(Ordering::Relaxed);
                    bar.set_position(processed as u64);
                    if processed == tasks.len() as u32 {
                        return;
                    }

                    thread::park_timeout(Duration::from_millis(250));
                }
            });

            let parts: Vec<_> = tasks.par_iter().with_max_len(1).map(|tm| {
                let mut part = EnumerationResults::default();
                part.enumerate_at(*tm, 10);
                processed.fetch_add(1, Ordering::Relaxed);
                part
            }).collect();

            for part in parts {
                results.merge_with(part);
            }

            assert!(results.postponed.is_empty());
            progress_thread.thread().unpark();
        });

        for (limit, machines) in &results.undecided {
            println!("{:10} {limit:?}", machines.len());
        }

        let total_undecided: usize = results.undecided.values().map(Vec::len).sum();
        println!("{:10} total undecided", total_undecided);

        for (prune, count) in &results.pruned {
            println!("{count:10} pruned by {prune:?}");
        }

        let total_pruned: u64 = results.pruned.values().sum();

        println!("{:10} total pruned", total_pruned);

        println!("{:10} halted", results.halted_count);
        println!("{:10} non-halting", results.nonhalting);
        println!("{:10} time record", results.time_record);
        println!("max split: {}", results.max_split);
    }
}

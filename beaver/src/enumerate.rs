use crate::turing::{Command, Configuration, Dir, Limit, OutOfSpace, State, Sym, TM};
use argh::FromArgs;
use itertools::Itertools;
use strum::IntoEnumIterator;
use enum_map::{enum_map, Enum, EnumMap};

const TIME_LIMIT: u32 = 47_176_870;
const BUFFER_SIZE: usize = 32_768;
const SPACE_LIMIT: usize = 12_289;
const BB4: u32 = 107;
const SPLIT_LEVEL: usize = 5;

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
    pruned: EnumMap<Prune, u64>,
    halted_count: u64,
    time_record: u32,
    best_beaver: Option<TM>,
    tasks: u32,
    max_split: u32,
}

impl EnumerationResults {
    fn enumerate_at(&mut self, tm: TM) {
        use RunResult::*;

        if tm.level() == SPLIT_LEVEL {
            self.tasks += 1;
            return;
        }

        let behavior = run(&tm);
        //println!("{}{tm} {behavior:?}", " ".repeat(tm.level() - 1));

        match behavior {
            Limit(limit) => {
                self.undecided[limit].push(tm);
            }
            Prune(prune) => {
                self.pruned[prune] += 1;
            }
            Halted(q, s, t) => {
                if tm.can_extend() {
                    self.max_split = self.max_split.max(t);
                    tm.children(q, s)
                        .for_each(|tm| self.enumerate_at(tm));
                } else {
                    self.halted_count += 1;

                    if t > self.time_record {
                        self.time_record = t;
                        self.best_beaver = Some(tm);
                        println!("new record: {tm} halts in {t} steps");
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

        results.enumerate_at(tm);

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
        println!("{:10} time record", results.time_record);
        println!("task split: {}", results.tasks);
        println!("max split: {}", results.max_split);
    }
}

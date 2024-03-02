use crate::turing::{Command, Configuration, Dir, Limit, OutOfSpace, State, Sym, TM};
use argh::FromArgs;
use itertools::Itertools;
use strum::IntoEnumIterator;
use enum_map::{enum_map, EnumMap};

const TIME_LIMIT: u32 = 50_000_000;
const SPACE_LIMIT: usize = 32768;

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

    fn children(&self, q: State, s: Sym) -> impl Iterator<Item = TM> + '_ {
        State::iter()
            .take_while_inclusive(move |&next| {
                // don't treat the state we're about to fill as empty
                if next == q {
                    return true;
                }

                self.code[next].values()
                    .any(|&cmd| cmd != Command::Halt)
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

#[derive(Debug)]
enum RunResult {
    Limit(Limit),
    Halted(State, Sym, u32),
}

fn run(tm: &TM) -> RunResult {
    let mut tape = [Sym::S0; SPACE_LIMIT];
    let mut conf = Configuration::new(&mut tape);

    for t in 0..TIME_LIMIT {
        match conf.step(tm) {
            Ok(false) => {
                let Ok(sym) = conf.head_symbol() else {
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
    halted_count: u64,
    time_record: u32,
    best_beaver: Option<TM>,
}

impl EnumerationResults {
    fn enumerate_at(&mut self, tm: TM) {
        use RunResult::*;

        let behavior = run(&tm);
        //println!("{}{tm} {behavior:?}", " ".repeat(tm.level() - 1));

        match behavior {
            Limit(limit) => {
                self.undecided[limit].push(tm);
            }
            Halted(q, s, t) => {
                if tm.can_extend() {
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

        for (limit, machines) in results.undecided {
            println!("{:10} {limit:?}", machines.len());
        }

        println!("{:10} halted", results.halted_count);
        println!("{:10} time record", results.time_record);
    }
}

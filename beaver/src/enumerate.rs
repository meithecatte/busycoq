use crate::turing::{Command, Configuration, Dir, Limit, OutOfSpace, State, Sym, TM};
use argh::FromArgs;
use itertools::Itertools;
use strum::IntoEnumIterator;
use enum_map::{enum_map, EnumMap};

const TIME_LIMIT: usize = 5000;
const SPACE_LIMIT: usize = 32768;

impl TM {
    fn blank() -> TM {
        TM { code: enum_map! { _ => enum_map! { _ => Command::Halt } } }
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
            .take_while_inclusive(|&next| {
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
    Halted(State, Sym),
}

fn run(tm: &TM) -> RunResult {
    let mut tape = [Sym::S0; SPACE_LIMIT];
    let mut conf = Configuration::new(&mut tape);

    for _ in 0..TIME_LIMIT {
        match conf.step(tm) {
            Ok(false) => {
                let Ok(sym) = conf.head_symbol() else {
                    return RunResult::Limit(Limit::Space);
                };

                return RunResult::Halted(conf.state, sym);
            }
            Ok(true) => continue,
            Err(OutOfSpace) => {
                return RunResult::Limit(Limit::Space);
            }
        }
    }

    RunResult::Limit(Limit::Time)
}

struct EnumerationResults {
    undecided: EnumMap<Limit, Vec<TM>>,
}

impl EnumerationResults {
    fn enumerate_at(&mut self, tm: TM) {
        use RunResult::*;

        match run(&tm) {
            Limit(limit) => {
                self.undecided[limit].push(tm);
            }
            Halted(q, s) => {
                if tm.can_extend() {
                    tm.children(q, s)
                        .for_each(|tm| self.enumerate_at(tm));
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
        let mut results = EnumerationResults {
            undecided: Default::default(),
        };

        for write in Sym::iter() {
            tm.code[State::A][Sym::S0] = Command::Step {
                write,
                dir: Dir::R,
                next: State::B, 
            };

            results.enumerate_at(tm.clone());
        }

        for (limit, machines) in results.undecided {
            println!("{:8} {limit:?}", machines.len());
        }
    }
}

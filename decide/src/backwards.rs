use crate::{Certificate, Decider};
use crate::turing::{Command, Dir, TM};
use crate::undo::UndoArray;
use enum_map::Enum;
use std::cell::Cell;
use binrw::binrw;

// These are very small parameters, but nevertheless the decider is maximally
// effective
const EXPLORE_LIMIT: u32 = 100;
const SPACE_LIMIT: usize = 64;

type Tape = UndoArray<bool, SPACE_LIMIT>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[binrw]
pub struct Cert {
    depth: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Enum)]
pub enum FailReason {
    OutOfSpace,
    OutOfTime,
}

struct Backwards<'a> {
    tm: &'a TM,
    configs_visited: Cell<u32>,
}

impl Backwards<'_> {
    /// Checks whether a particular configuration leads to a contradiction.
    ///
    /// `tape[l..=r]` is specified, rest can be arbitrary.
    ///
    /// `0 <= l <= pos <= r < SPACE_LIMIT` holds.
    ///
    /// Returns the search depth necessary, or `None` if contradiction hasn't
    /// been found.
    fn visit(
        &self,
        tape: &mut Tape,
        l: usize,
        r: usize,
        pos: usize,
        state: u8,
    ) -> Result<u32, FailReason> {
        self.configs_visited.set(self.configs_visited.get() + 1);

        if self.configs_visited.get() >= EXPLORE_LIMIT {
            return Err(FailReason::OutOfTime);
        }

        let mut max_depth = 0;

        for (prev_state, cmds) in self.tm.code.iter().enumerate() {
            for (prev_symbol, &cmd) in cmds.iter().enumerate() {
                let Command::Step { write, next, dir } = cmd else { continue };

                if next != state { continue }

                match dir {
                    Dir::L if pos != r => {
                        if tape[pos + 1] != write { continue }
                    }
                    Dir::R if pos != l => {
                        if tape[pos - 1] != write { continue }
                    }
                    _ => {}
                }

                let pos = match dir {
                    Dir::L => {
                        if pos == SPACE_LIMIT - 1 {
                            return Err(FailReason::OutOfSpace);
                        }

                        pos + 1
                    }
                    Dir::R => {
                        if pos == 0 {
                            return Err(FailReason::OutOfSpace);
                        }

                        pos - 1
                    }
                };

                let l = l.min(pos);
                let r = r.max(pos);

                let depth = tape.with(pos, prev_symbol != 0, |tape| {
                    self.visit(tape, l, r, pos, prev_state as u8)
                })?;

                max_depth = max_depth.max(depth);
            }
        }

        Ok(max_depth + 1)
    }
}

fn decide_backwards(tm: &TM) -> Result<Cert, FailReason> {
    let backwards = Backwards {
        tm,
        configs_visited: Cell::new(0),
    };

    let mut tape = UndoArray::new([false; SPACE_LIMIT]);
    let pos = SPACE_LIMIT / 2;
    let mut max_depth = 0;

    for (state, cmds) in tm.code.iter().enumerate() {
        for (symbol, &cmd) in cmds.iter().enumerate() {
            if cmd != Command::Halt { continue }

            let depth = tape.with(pos, symbol != 0, |tape| {
                backwards.visit(tape, pos, pos, pos, state as u8)
            })?;

            max_depth = max_depth.max(depth);
        }
    }

    Ok(Cert { depth: max_depth })
}

pub struct BackwardsReasoning;

impl Decider for BackwardsReasoning {
    type Error = FailReason;
    const NAME: &'static str = "Backwards Reasoning";

    fn decide(tm: &TM) -> Result<Certificate, FailReason> {
        decide_backwards(tm).map(From::from)
    }
}

//! This attempts to decide machines by "static analysis" – if in the state
//! transition graph, there is no path from a particular state to a halting
//! transition, then the state is a "non-halting state".
//!
//! Due to how the database is constructed, all non-halting transitions are
//! guaranteed to be reachable. As such, we don't even need to execute the
//! machines.

use crate::{Certificate, Decider};
use crate::turing::{Command, NUM_STATES, TM};
use enum_map::enum_map;

pub fn decide_closed_subset(tm: &TM) -> Result<(), ()> {
    let mut haltable = 0_u8;
    let mut transitions = enum_map! { _ => 0_u8 };

    for (state, cmds) in tm.code.iter() {
        for &cmd in cmds.values() {
            match cmd {
                Command::Halt => {
                    haltable |= 1 << state as u8;
                }
                Command::Step { next, .. } => {
                    transitions[state] |= 1 << next as u8;
                }
            }
        }
    }

    loop {
        let prev_haltable = haltable;
        for (state, nexts) in transitions.iter() {
            if haltable & (1 << state as u8) != 0 {
                continue;
            }

            if nexts & haltable != 0 {
                haltable |= 1 << state as u8;
            }
        }

        if prev_haltable == haltable {
            break;
        }
    }

    if haltable == (1 << NUM_STATES) - 1 {
        Err(())
    } else {
        Ok(())
    }
}

pub struct ClosedSubset;

impl Decider for ClosedSubset {
    type Error = ();
    const NAME: &'static str = "Closed Subset";

    fn decide(tm: &TM) -> Result<Certificate, ()> {
        decide_closed_subset(tm).map(|_| Certificate::ClosedSubset)
    }
}

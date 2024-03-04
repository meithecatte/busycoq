use crate::{Certificate, Decider};
use crate::database::DatabaseEntry;
use crate::turing::{TM, Command};
use enum_map::{Enum, enum_map};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Enum)]
pub enum FailReason {
    NotApplicable,
}

/// This implements the decider described here:
/// https://discuss.bbchallenge.org/t/closed-state-transition-cluster/74
///
/// TL;DR: if we have a closed set of states S (i.e. where for each state in S,
/// the next state of all commands is also in S), then the machine can't ever
/// reach a halting transition if it enters S at any point.
/// 
/// The enumeration algorithm guarantees that each defined transition (i.e. all
/// but Halt) are eventually reached by the machine. Therefore, we only need
/// to detect the existence of the set S, and the machine is guaranteed to get
/// stuck in it at some point.
pub fn decide_syntactic(tm: &TM) -> Result<(), FailReason> {
    let mut can_reach_halt = enum_map! { q => tm.state_has_halt(q) };
    loop {
        let mut made_progress = false;
        let mut all_can_reach = true;
        for (q, cmds) in tm.code.iter() {
            if can_reach_halt[q] {
                continue;
            }

            if cmds.values().any(|&cmd| match cmd {
                Command::Step { next, .. } => can_reach_halt[next],
                _ => false,
            }) {
                can_reach_halt[q] = true;
                made_progress = true;
            } else {
                all_can_reach = false;
            }
        }

        if !made_progress {
            if all_can_reach {
                return Err(FailReason::NotApplicable);
            } else {
                return Ok(());
            }
        }
    }
}

pub struct Syntactic;

impl Decider for Syntactic {
    type Error = FailReason;
    const NAME: &'static str = "Syntactic";

    fn decide(tm: &DatabaseEntry) -> Result<Certificate, FailReason> {
        decide_syntactic(&tm.tm)?;
        Ok(Certificate::Syntactic)
    }
}

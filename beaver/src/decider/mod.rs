pub mod syntactic;
pub mod cyclers;
pub mod tcyclers;
pub mod backwards;
pub mod bouncers;
pub mod inductive;

pub use syntactic::Syntactic;
pub use cyclers::Cyclers;
pub use tcyclers::TCyclers;
pub use backwards::BackwardsReasoning;
pub use bouncers::Bouncers;

use crate::turing::TM;

pub fn decide_fast(tm: &TM) -> bool {
    if syntactic::decide_syntactic(tm).is_ok() {
        return true;
    }

    match cyclers::decide_cyclers(tm) {
        Ok(_) => return true,
        Err(cyclers::FailReason::Halted) => return false,
        _ => {}
    }

    tcyclers::decide_tcyclers(tm).is_ok()
        || backwards::decide_backwards(tm).is_ok()
}

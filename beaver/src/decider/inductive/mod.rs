mod tape;

use argh::FromArgs;
use std::fmt;
use tape::*;
use crate::turing::{Command, Dir, State, Sym, TM};

struct Config {
    left: Side,
    right: Side,
    state: State,
    dir: Dir,
}

struct Context {
    tm: TM,
    intern: ChunkIntern,
}

impl Config {
    fn new() -> Self {
        Self {
            left: Side::new(),
            right: Side::new(),
            state: State::A,
            dir: Dir::R,
        }
    }

    fn base_step(&mut self, ctx: &mut Context) -> bool {
        let sym = match self.dir {
            Dir::L => self.left.pop_base(&ctx.intern),
            Dir::R => self.right.pop_base(&ctx.intern),
        };

        let sym = sym.unwrap_or(Sym::S0);
        match ctx.tm.code[self.state][sym] {
            Command::Halt => return false,
            Command::Step { write, dir, next } => {
                match dir {
                    Dir::L => self.right.push(&mut ctx.intern, Symbol::Base(write)),
                    Dir::R => self.left.push(&mut ctx.intern, Symbol::Base(write)),
                }

                self.dir = dir;
                self.state = next;
                return true;
            }
        }
    }

    fn display<'a>(&'a self, ctx: &'a Context) -> DisplayConfig<'a> {
        DisplayConfig {
            config: self,
            intern: &ctx.intern,
        }
    }
}

struct DisplayConfig<'a> {
    config: &'a Config,
    intern: &'a ChunkIntern,
}

impl<'a> fmt::Display for DisplayConfig<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let left = self.config.left.display_left(self.intern);
        let right = self.config.right.display_right(self.intern);
        let state = self.config.state;
        match self.config.dir {
            Dir::L => write!(f, "{left} <{state} {right}"),
            Dir::R => write!(f, "{left} {state}> {right}"),
        }
    }
}

pub fn inductive(tm: TM) {
    let mut ctx = Context {
        tm,
        intern: ChunkIntern::new(),
    };

    let mut config = Config::new();
    for _ in 0..1000 {
        config.base_step(&mut ctx);
        println!("{}", config.display(&ctx));
    }
}

#[derive(FromArgs)]
#[argh(subcommand, name = "inductive")]
/// Run the inductive prover
pub struct Inductive {
    /// machine code
    #[argh(positional)]
    tm: TM,
}

impl Inductive {
    pub fn run(&self) {
        inductive(self.tm);
    }
}

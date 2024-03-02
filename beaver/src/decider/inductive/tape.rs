//! This module is responsible for maintaining the compressed tape
//! representation.

use std::fmt::{self, Write};
use std::num::NonZeroU32;
use indexmap::IndexSet;
use crate::turing;

/// Maximum segment length for which we'll check.
///
/// There's probably a smart text processing algorithm that would allow
/// removing this limit without sacrificing performance...
const MAX_SEGMENT_LEN: usize = 16;

/// An interned sequence of [`Symbol`]s.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Chunk(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Symbol {
    Base(turing::Sym),
    Repeated(Chunk, NonZeroU32),
}

/// One side of a compressed tape.
#[derive(Clone, Debug)]
pub struct Side {
    symbols: Vec<Symbol>,
}

pub struct DisplaySide<'a> {
    side: &'a Side,
    intern: &'a ChunkIntern,
    flip: bool,
}

impl Side {
    pub fn new() -> Self {
        Self {
            symbols: Vec::new(),
        }
    }

    pub fn push(&mut self, intern: &mut ChunkIntern, sym: Symbol) {
        self.symbols.push(sym);
        while self.try_compress(intern) {}
    }

    pub fn pop_base(&mut self, intern: &ChunkIntern) -> Option<turing::Sym> {
        loop {
            match self.symbols.pop()? {
                Symbol::Repeated(chunk, count) => {
                    if count.get() > 1 {
                        let count = NonZeroU32::new(count.get() - 1).unwrap();
                        self.symbols.push(Symbol::Repeated(chunk, count));
                    }

                    self.symbols.extend_from_slice(intern.get(chunk));
                }
                Symbol::Base(sym) => return Some(sym),
            }
        }
    }

    fn try_compress(&mut self, intern: &mut ChunkIntern) -> bool {
        let n = self.symbols.len();

        for k in 2..=MAX_SEGMENT_LEN.min(n / 2) {
            if &self.symbols[n - k..n] == &self.symbols[n - 2*k..n - k] {
                let chunk = intern.intern(&self.symbols[n - k..n]);
                self.symbols.truncate(n - 2*k);
                let count = NonZeroU32::new(2).unwrap();
                self.symbols.push(Symbol::Repeated(chunk, count));
                return true;
            }
        }

        for k in 2..=MAX_SEGMENT_LEN.min(n - 1) {
            let chunk_at = n - k - 1;
            if let Symbol::Repeated(chunk, count) = self.symbols[chunk_at] {
                if &self.symbols[n - k..n] == intern.get(chunk) {
                    self.symbols.truncate(n - k);
                    let count = count.checked_add(1).unwrap();
                    self.symbols[chunk_at] = Symbol::Repeated(chunk, count);
                    return true;
                }
            }
        }

        false
    }

    /// Returns a struct that, when [`Display`][fmt::Display]ed, will print
    /// the contents of this [`Side`] as if it is the left side of the tape.
    pub fn display_left<'a>(&'a self, intern: &'a ChunkIntern) -> DisplaySide<'a> {
        DisplaySide {
            side: self,
            intern,
            flip: false,
        }
    }

    /// Returns a struct that, when [`Display`][fmt::Display]ed, will print
    /// the contents of this [`Side`] as if it is the right side of the tape.
    pub fn display_right<'a>(&'a self, intern: &'a ChunkIntern) -> DisplaySide<'a> {
        DisplaySide {
            side: self,
            intern,
            flip: true,
        }
    }
}

pub struct ChunkIntern {
    chunks: IndexSet<Vec<Symbol>>,
}

impl ChunkIntern {
    pub fn new() -> Self {
        Self {
            chunks: IndexSet::new(),
        }
    }

    fn intern(&mut self, chunk: &[Symbol]) -> Chunk {
        let n = match self.chunks.get_index_of(chunk) {
            Some(n) => n,
            None => self.chunks.insert_full(chunk.to_vec()).0,
        };

        Chunk(n.try_into().unwrap())
    }

    fn get(&self, chunk: Chunk) -> &[Symbol] {
        self.chunks.get_index(chunk.0 as usize).unwrap().as_slice()
    }
}

impl<'a> fmt::Display for DisplaySide<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.flip {
            for sym in self.side.symbols.iter().rev() {
                sym.write_fmt(f, self.intern, self.flip)?;
            }
        } else {
            for sym in self.side.symbols.iter() {
                sym.write_fmt(f, self.intern, self.flip)?;
            }
        }

        Ok(())
    }
}

impl Symbol {
    fn write_fmt(
        self,
        f: &mut fmt::Formatter<'_>,
        intern: &ChunkIntern,
        flip: bool,
    ) -> fmt::Result {
        match self {
            Symbol::Base(sym) => write!(f, "{sym}"),
            Symbol::Repeated(chunk, exp) => {
                f.write_char('(')?;
                chunk.write_fmt(f, intern, flip)?;
                f.write_char(')')?;
                fmt_exponent(f, exp.get())?;
                Ok(())
            }
        }
    }
}

impl Chunk {
    fn write_fmt(
        self,
        f: &mut fmt::Formatter<'_>,
        intern: &ChunkIntern,
        flip: bool,
    ) -> fmt::Result {
        let syms = intern.get(self);
        if flip {
            for sym in syms.iter().rev() {
                sym.write_fmt(f, intern, flip)?;
            }
        } else {
            for sym in syms {
                sym.write_fmt(f, intern, flip)?;
            }
        }

        Ok(())
    }
}

fn fmt_exponent(f: &mut fmt::Formatter<'_>, n: u32) -> fmt::Result {
    const SUPS: [char; 10] = ['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹'];
    for c in n.to_string().bytes() {
        f.write_char(SUPS[(c - b'0') as usize])?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_chunking() {
        let mut intern = ChunkIntern::new();
        let mut side = Side::new();
        use turing::Sym::*;

        for x in [S1, S0, S0, S1, S1, S0, S1, S1, S0, S1, S1] {
            side.push(&mut intern, Symbol::Base(x));
        }

        assert_eq!(side.symbols, [
            Symbol::Base(S1),
            Symbol::Base(S0),
            Symbol::Repeated(Chunk(0), NonZeroU32::new(3).unwrap()),
        ]);

        assert_eq!(intern.get(Chunk(0)), [
            Symbol::Base(S0),
            Symbol::Base(S1),
            Symbol::Base(S1),
        ]);
    }

    #[test]
    fn chunking_edge() {
        let mut intern = ChunkIntern::new();
        let mut side = Side::new();
        use turing::Sym::*;

        for x in [S0, S1, S1, S1, S1] {
            side.push(&mut intern, Symbol::Base(x));
        }

        assert_eq!(side.symbols, [
            Symbol::Base(S0),
            Symbol::Repeated(Chunk(0), NonZeroU32::new(2).unwrap()),
        ]);

        assert_eq!(intern.get(Chunk(0)), [
            Symbol::Base(S1),
            Symbol::Base(S1),
        ]);
    }


    #[test]
    fn display() {
        let mut intern = ChunkIntern::new();
        let mut side = Side::new();
        use turing::Sym::*;

        for x in [S1, S0, S0, S1, S1, S0, S1, S1] {
            side.push(&mut intern, Symbol::Base(x));
        }

        assert_eq!(side.display_left(&intern).to_string(), "10(011)²");
        assert_eq!(side.display_right(&intern).to_string(), "(110)²01");
    }
}

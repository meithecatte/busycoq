use std::array;
use std::fmt;
use std::str::FromStr;
use binrw::binrw;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OutOfSpace;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[binrw]
pub enum Dir {
    #[brw(magic = 1u8)] L,
    #[brw(magic = 0u8)] R,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Limit {
    Time,
    Space,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Command {
    Halt,
    Step {
        write: bool,
        dir: Dir,
        next: u8,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TM {
    /// Records the index of this Turing machine in the database.
    pub index: u32,
    /// Records which limit the machine triggered during the initial
    /// evaluation.
    pub limit: Limit,
    pub code: [[Command; 2]; 5],
}

#[derive(Debug, PartialEq, Eq)]
pub struct Configuration<'a> {
    pub state: u8,
    pub pos: usize,
    pub tape: &'a mut [bool],
}

impl TM {
    pub fn from_bytes(index: u32, limit: Limit, data: &[u8; 30]) -> TM {
        TM {
            index,
            limit,
            code: array::from_fn(|st| {
                array::from_fn(|read| {
                    let offset = 6 * st + 3 * read;
                    let segment: [u8; 3] = data[offset..offset+3]
                        .try_into().unwrap();
                    segment.try_into().unwrap()
                })
            })
        }
    }

    pub fn compact(&self) -> String {
        self.code.iter()
            .map(|[a, b]| format!("{a}{b}"))
            .collect::<Vec<_>>()
            .join("_")
    }
}

impl<'a> Configuration<'a> {
    pub fn new(buf: &'a mut [bool]) -> Self {
        Self {
            state: 0,
            pos: buf.len() / 2,
            tape: buf,
        }
    }

    pub fn head_symbol(&self) -> Result<bool, OutOfSpace> {
        self.tape.get(self.pos).copied().ok_or(OutOfSpace)
    }

    pub fn write_at_head(&mut self, symbol: bool) {
        self.tape[self.pos] = symbol;
    }

    pub fn move_head(&mut self, dir: Dir) {
        // If we're running out of buffer space, move out of bounds and let it
        // be detected at the next step. This allows `Configuration` to be used
        // when we want to be able to represent "the head is pointing outside
        // of the tape buffer" in the "head with direction" view.
        self.pos = match dir {
            Dir::L => self.pos.wrapping_sub(1),
            Dir::R => self.pos + 1,
        };
    }

    pub fn step(&mut self, tm: &TM) -> Result<bool, OutOfSpace> {
        let cmd = tm.code[self.state as usize][self.head_symbol()? as usize];
        match cmd {
            Command::Halt => Ok(false),
            Command::Step { write, dir, next } => {
                self.write_at_head(write);
                self.move_head(dir);
                self.state = next;
                Ok(true)
            }
        }
    }
}

impl fmt::Display for Configuration<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.pos != usize::MAX {
            for &sym in self.tape.iter().take(self.pos) {
                write!(f, "{} ", if sym { "1" } else { "0" })?;
            }
        }

        let state = b"ABCDE"[self.state as usize] as char;
        match self.tape.get(self.pos) {
            Some(&sym) => write!(f, "{state}[{}]", if sym { "1" } else { "0" })?,
            None => write!(f, "{state}[]")?,
        }

        for &sym in self.tape.iter().skip(self.pos + 1) {
            write!(f, "{} ", if sym { "1" } else { "0" })?;
        }

        Ok(())
    }
}

impl TryFrom<u8> for Dir {
    type Error = &'static str;

    fn try_from(x: u8) -> Result<Dir, &'static str> {
        match x {
            0 => Ok(Dir::R),
            1 => Ok(Dir::L),
            _ => Err("invalid byte for direction"),
        }
    }
}

impl From<Dir> for u8 {
    fn from(x: Dir) -> u8 {
        match x {
            Dir::R => 0,
            Dir::L => 1,
        }
    }
}

impl TryFrom<[u8; 3]> for Command {
    type Error = &'static str;

    fn try_from(x: [u8; 3]) -> Result<Command, &'static str> {
        let write = match x[0] {
            0 => false,
            1 => true,
            _ => return Err("invalid byte for written symbol"),
        };

        let dir = x[1].try_into()?;
        match x[2] {
            0 => Ok(Command::Halt),
            k => Ok(Command::Step {
                write,
                dir,
                next: k - 1,
            }),
        }
    }
}

impl fmt::Display for Dir {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Dir::L => f.write_str("L"),
            Dir::R => f.write_str("R"),
        }
    }
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Command::Halt => f.write_str("---"),
            Command::Step { write, dir, next } => {
                let write = write as u8;
                let next = b"ABCDE"[next as usize] as char;
                write!(f, "{write}{dir}{next}")
            }
        }
    }
}

impl fmt::Display for TM {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{} {}", self.index, self.compact())
    }
}

impl FromStr for TM {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, ()> {
        let code = s.split('_').map(|state| {
            state.as_bytes().chunks(3).map(|cmd| {
                match cmd {
                    b"---" => Command::Halt,
                    _ => {
                        let write = match cmd[0] {
                            b'0' => false,
                            b'1' => true,
                            _ => panic!(),
                        };

                        let dir = match cmd[1] {
                            b'L' => Dir::L,
                            b'R' => Dir::R,
                            _ => panic!(),
                        };

                        let next = match cmd[2] {
                            b'A' => 0,
                            b'B' => 1,
                            b'C' => 2,
                            b'D' => 3,
                            b'E' => 4,
                            _ => panic!(),
                        };

                        Command::Step { write, dir, next }
                    }
                }
            }).collect::<Vec<_>>().try_into().unwrap()
        }).collect::<Vec<_>>().try_into().unwrap();

        Ok(TM { 
            index: 0,
            limit: Limit::Time,
            code,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bb5_record() {
        // NOTE: instead of the 1RZ transition, which counts as a step, we use ---,
        // which doesn't count as a step. Thus the machine takes one step less than
        // if we count using the usual convention.
        let tm: TM = "1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA".parse().unwrap();
        let mut tape = [false; 32768];
        let mut conf = Configuration::new(&mut tape);

        for _ in 0..47_176_869 {
            assert_eq!(conf.step(&tm), Ok(true));
        }

        assert_eq!(conf.step(&tm), Ok(false));
    }
}

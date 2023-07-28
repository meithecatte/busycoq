use std::array;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OutOfSpace;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dir {
    L,
    R,
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
    code: [[Command; 2]; 5],
}

#[derive(Clone, PartialEq, Eq)]
pub struct Configuration {
    pub state: u8,
    pub pos: usize,
    tape: Box<[bool]>,
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

impl Configuration {
    pub fn new(size: usize) -> Self {
        Self {
            state: 0,
            pos: size / 2,
            tape: vec![false; size].into_boxed_slice(),
        }
    }

    pub fn head_symbol(&self) -> bool {
        self.tape[self.pos]
    }

    pub fn write_at_head(&mut self, symbol: bool) {
        self.tape[self.pos] = symbol;
    }

    pub fn move_head(&mut self, dir: Dir) -> Result<(), OutOfSpace> {
        match dir {
            Dir::L => {
                if self.pos == 0 {
                    Err(OutOfSpace)
                } else {
                    self.pos -= 1;
                    Ok(())
                }
            }
            Dir::R => {
                if self.pos + 1 == self.tape.len() {
                    Err(OutOfSpace)
                } else {
                    self.pos += 1;
                    Ok(())
                }
            }
        }
    }

    pub fn step(&mut self, tm: &TM) -> Result<bool, OutOfSpace> {
        let cmd = tm.code[self.state as usize][self.head_symbol() as usize];
        match cmd {
            Command::Halt => Ok(false),
            Command::Step { write, dir, next } => {
                self.write_at_head(write);
                self.move_head(dir)?;
                self.state = next;
                Ok(true)
            }
        }
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

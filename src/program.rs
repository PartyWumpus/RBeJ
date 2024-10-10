use rand_derive2::RandGen;
use std::fs;

#[derive(Copy, Clone, Debug, RandGen, Hash, PartialEq, Eq)]
pub enum Direction {
    North = 0,
    South = 1,
    East = 2,
    West = 3,
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct Location(pub usize, pub usize);

pub struct Program {
    chars: Vec<u64>,
    pub height: usize,
    pub width: usize,
}

/*
impl std::fmt::Debug for BefungeProgram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Point")
            .field(
                "Chars",
                &self
                    .chars
                    .chunks(self.width)
                    .map(|x| x.iter().map(|x| *x as char).collect::<Vec<char>>())
                    .collect::<Vec<Vec<char>>>(),
            )
            .field("Height", &self.height)
            .field("Width", &self.width)
            .finish()
    }
}
*/

impl Program {
    pub fn new(str: &str) -> Self {
        let mut state = Vec::new();
        let mut width = 0;
        for line in str.lines() {
            if line.len() > width {
                width = line.len();
            };
        }

        for line in str.lines() {
            // TODO: catch failures here
            let mut chars: Vec<u64> = line.chars().map(|x| x as u64).collect();

            chars.resize(width, b' '.into());
            state.append(&mut chars);
        }
        Self {
            height: (state.len() - 1) / width,
            chars: state,
            width: width - 1,
        }
    }

    fn new_from_file(file_path: &str) -> Self {
        let str = fs::read_to_string(file_path).expect("Should have been able to read the file");
        Self::new(&str)
    }

    pub const fn calc_index(&self, loc: &Location) -> usize {
        loc.0 + loc.1 * (self.width + 1)
    }

    pub fn get(&self, loc: &Location) -> Option<u64> {
        if loc.0 > self.width || loc.1 > self.height {
            None
        } else {
            let index = self.calc_index(loc);
            Some(self.chars[index])
        }
    }

    pub fn get_unchecked(&self, loc: &Location) -> u64 {
        if loc.0 > self.width || loc.1 > self.height {
            panic!("get {loc:?} is out of bounds");
        } else {
            self.chars[self.calc_index(loc)]
        }
    }

    pub fn set_if_valid(&mut self, loc: &Location, value: u64) -> bool {
        if loc.0 > self.width || loc.1 > self.height {
            println!("put failed by the wayyy");
            false
        } else {
            let index = self.calc_index(loc);
            self.chars[index] = value;
            true
        }
    }
}

pub const fn step_with_wrap(
    width: usize,
    height: usize,
    dir: Direction,
    loc: Location,
) -> Location {
    match dir {
        Direction::North => {
            if loc.1 == 0 {
                Location(loc.0, height - 1)
            } else {
                Location(loc.0, loc.1 - 1)
            }
        }
        Direction::South => {
            if loc.1 >= height {
                Location(loc.0, 0)
            } else {
                Location(loc.0, loc.1 + 1)
            }
        }
        Direction::East => {
            if loc.0 >= width {
                Location(0, loc.1)
            } else {
                Location(loc.0 + 1, loc.1)
            }
        }
        Direction::West => {
            if loc.0 == 0 {
                Location(width - 1, loc.1)
            } else {
                Location(loc.0 - 1, loc.1)
            }
        }
    }
}

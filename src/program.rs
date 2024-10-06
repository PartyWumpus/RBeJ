use rand_derive2::RandGen;

#[derive(Copy, Clone, Debug, RandGen, Hash, PartialEq, Eq)]
pub enum Direction {
    North,
    South,
    East,
    West,
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct Location(pub usize, pub usize);

pub struct BefungeProgram {
    chars: Vec<u64>,
    height: usize,
    width: usize,
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

impl BefungeProgram {
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

    pub fn get(&self, loc: &Location) -> Option<u64> {
        if loc.0 > self.width || loc.1 > self.height {
            None
        } else {
            Some(self.chars[loc.0 + loc.1 * (self.width + 1)])
        }
    }

    pub fn get_unchecked(&self, loc: &Location) -> u64 {
        if loc.0 > self.width || loc.1 > self.height {
            panic!("get {loc:?} is out of bounds");
        } else {
            self.chars[loc.0 + loc.1 * (self.width + 1)]
        }
    }

    pub fn set_if_valid(&mut self, loc: &Location, value: u64) {
        if loc.0 > self.width || loc.1 > self.height {
            println!("put failed by the wayyy");
            // if it is out of bounds, we just silently fail
        } else {
            self.chars[loc.0 + loc.1 * (self.width + 1)] = value;
        };
    }

    pub const fn step_with_wrap(&self, dir: Direction, loc: Location) -> Location {
        match dir {
            Direction::North => {
                if loc.1 == 0 {
                    Location(loc.0, self.height - 1)
                } else {
                    Location(loc.0, loc.1 - 1)
                }
            }
            Direction::South => {
                if loc.1 >= self.height {
                    Location(loc.0, 0)
                } else {
                    Location(loc.0, loc.1 + 1)
                }
            }
            Direction::East => {
                if loc.0 >= self.width {
                    Location(0, loc.1)
                } else {
                    Location(loc.0 + 1, loc.1)
                }
            }
            Direction::West => {
                if loc.0 == 0 {
                    Location(self.width - 1, loc.1)
                } else {
                    Location(loc.0 - 1, loc.1)
                }
            }
        }
    }
}

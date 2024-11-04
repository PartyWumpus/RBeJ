use rand_derive2::RandGen;

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

impl std::fmt::Debug for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            &self
                .chars
                .chunks(self.width + 1)
                .map(|x| {
                    x.iter()
                        .map(|x| char::from_u32(*x as u32).unwrap())
                        .collect::<String>()
                })
                .fold(String::new(), |a, b| a + "\n" + &b),
        )
    }
}

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

    pub const fn calc_index(loc: &Location, width: usize) -> usize {
        loc.0 + loc.1 * (width + 1)
    }

    pub fn get(&self, loc: &Location) -> Option<u64> {
        if loc.0 > self.width || loc.1 > self.height {
            None
        } else {
            let index = Self::calc_index(loc, self.width);
            Some(self.chars[index])
        }
    }

    pub fn get_unchecked(&self, loc: &Location) -> u64 {
        if loc.0 > self.width || loc.1 > self.height {
            panic!("get {loc:?} is out of bounds");
        } else {
            self.chars[Self::calc_index(loc, self.width)]
        }
    }

    pub fn set_if_valid(&mut self, loc: &Location, value: u64) -> bool {
        if loc.0 > self.width || loc.1 > self.height {
            println!("put failed by the wayyy");
            false
        } else {
            let index = Self::calc_index(loc, self.width);
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

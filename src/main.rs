use inkwell::builder::{self, Builder};
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, FunctionLookupError, JitFunction};
use inkwell::module::Module;
use inkwell::types::{BasicType, PointerType};
use inkwell::values::{AnyValue, FunctionValue, IntValue, PointerValue};
use inkwell::{AddressSpace, OptimizationLevel};
use rand::distributions::{Alphanumeric, DistString};

use std::error::Error;

#[macro_use]
extern crate rand_derive2;

const STACK_SIZE: usize = 100;
type BefungeFunc = unsafe extern "C" fn() -> u64;

#[derive(Copy, Clone, Debug, RandGen)]
enum Direction {
    North,
    South,
    East,
    West,
}

#[derive(Copy, Clone)]
struct Location(usize, usize);

#[derive(Copy, Clone)]
enum BefungeStatus {
    Okay = 0,
    GoLeft = 2,
    GoRight = 3,
    GoUp = 4,
    GoDown = 5,
}

struct BefungeProgram {
    chars: Vec<u8>,
    height: usize,
    width: usize,
}

impl BefungeProgram {
    fn new(str: &str) -> Self {
        let mut state = Vec::new();
        let mut width = None;
        for line in str.lines() {
            // TODO: catch failures here
            let mut chars: Vec<u8> = line.chars().map(|x| x as u8).collect();
            if width.is_none() {
                width = Some(chars.len());
            };
            state.append(&mut chars)
        }
        Self {
            height: state.len(),
            chars: state,
            width: width.unwrap(),
        }
    }

    fn get(&self, loc: &Location) -> u8 {
        if loc.0 > self.width || loc.1 > self.height {
            panic!("location out of bounds :(")
        } else {
            return self.chars[loc.0 + loc.1 * self.width];
        }
    }

    fn set(&mut self, loc: &Location, value: u8) {
        if loc.0 > self.width || loc.1 > self.height {
            panic!("location out of bounds :(")
        } else {
            self.chars[loc.0 + loc.1 * self.width] = value;
        };
    }

    fn step(&self, dir: Direction, loc: Location) -> Location {
        // TODO: wrapping
        match dir {
            Direction::North => Location(loc.0, loc.1 - 1),
            Direction::South => Location(loc.0, loc.1 + 1),
            Direction::East => Location(loc.0 + 1, loc.1),
            Direction::West => Location(loc.0 - 1, loc.1),
        }
    }
}

struct BefungeState {
    program: BefungeProgram,
    location: Location,
    direction: Direction,
}

impl BefungeState {
    fn new(str: &str) -> Self {
        Self {
            program: BefungeProgram::new(str),
            location: Location(0, 0),
            direction: Direction::East,
        }
    }

    fn step(&mut self) {
        self.location = self.program.step(self.direction, self.location);
    }
}

struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    execution_engine: ExecutionEngine<'ctx>,
}

impl<'ctx> CodeGen<'ctx> {
    /// GENERAL UTILITY

    fn prelude(&self) {
        let i8_type = self.context.i8_type();
        let stack_type = i8_type.vec_type(STACK_SIZE as u32);

        let zero = i8_type.const_int(0, false);
        let stack_zero = stack_type.const_zero();

        let ptr = self.module.add_global(i8_type, None, "stack_counter");
        ptr.set_initializer(&zero);

        let stack = self.module.add_global(stack_type, None, "stack");
        stack.set_initializer(&stack_zero);

        let ptr = self.context.ptr_type(AddressSpace::default());

        let fn_value = self
            .module
            .add_function("wahoo", i8_type.fn_type(&[], false), None);
        let entry = self.context.append_basic_block(fn_value, "entry");
        self.builder.position_at_end(entry);
        self.builder.build_return(None).unwrap();

        unsafe {
            self.builder.build_global_string("%d\n", "int_str").unwrap();
        }
        let printf_type = self.context.i32_type().fn_type(&[ptr.into()], true);
        self.module.add_function("printf", printf_type, None);
    }

    // %w = getelementptr [1 x i8], [1 x i8]* @int_str, i64 0, i64 0
    // call i32 (i8*, ...) @printf(i8* %w, i32 %val)
    fn printf_int(&self, int: IntValue) {
        //let str = self
        //    .module
        //    .get_global("int_str")
        //    .unwrap()
        //    .as_pointer_value();

        let str;
        unsafe {
            str = self
                .builder
                .build_global_string("%d\n", "int_str")
                .unwrap()
                .as_pointer_value();
        }

        let printf = self.module.get_function("printf").unwrap();

        self.builder
            .build_call(printf, &[str.into(), int.into()], "printy")
            .unwrap();
    }

    fn get_stack_counter_ptr(&self) -> PointerValue<'_> {
        self.module
            .get_global("stack_counter")
            .unwrap()
            .as_pointer_value()
    }

    fn get_stack_ptr(&self) -> PointerValue<'_> {
        self.module.get_global("stack").unwrap().as_pointer_value()
    }

    fn increment_stack_counter(&self) {
        let i8_type = self.context.i8_type();
        let one = i8_type.const_int(1, false);

        let ptr = self.get_stack_counter_ptr();

        let stack_counter = self
            .builder
            .build_load(i8_type, ptr, "count")
            .unwrap()
            .into_int_value();

        let stack_counter = self
            .builder
            .build_int_add(stack_counter, one, "count")
            .unwrap();

        self.builder.build_store(ptr, stack_counter).unwrap();
    }

    fn decrement_stack_counter(&self) {
        let i8_type = self.context.i8_type();
        let minus_one = i8_type.const_int(u64::MAX, false); // ;)

        let ptr = self.get_stack_counter_ptr();

        let stack_counter = self
            .builder
            .build_load(i8_type, ptr, "count")
            .unwrap()
            .into_int_value();

        let stack_counter = self
            .builder
            .build_int_add(stack_counter, minus_one, "count")
            .unwrap();

        self.builder.build_store(ptr, stack_counter).unwrap();
    }

    fn peek_ptr(&self) -> PointerValue<'_> {
        let i8_type = self.context.i8_type();
        let stack_type = i8_type.vec_type(STACK_SIZE as u32);
        let zero = i8_type.const_zero();

        let stack_ptr = self.get_stack_ptr();
        let counter_ptr = self.get_stack_counter_ptr();
        let counter = self
            .builder
            .build_load(i8_type, counter_ptr, "count")
            .unwrap()
            .into_int_value();

        unsafe {
            self.builder
                .build_in_bounds_gep(stack_type, stack_ptr, &[zero, counter], "val")
                .unwrap()
        }
    }

    fn peek_stack(&self) -> IntValue<'_> {
        let i8_type = self.context.i8_type();
        let ptr = self.peek_ptr();

        let res = self
            .builder
            .build_load(i8_type, ptr, "stack_val")
            .unwrap()
            .into_int_value();

        return res;
    }

    fn pop_stack(&self) -> IntValue<'_> {
        let i8_type = self.context.i8_type();
        let ptr = self.peek_ptr();

        let res = self
            .builder
            .build_load(i8_type, ptr, "stack_val")
            .unwrap()
            .into_int_value();

        self.decrement_stack_counter();

        return res;
    }

    fn push_stack(&self, val: IntValue<'_>) {
        self.increment_stack_counter();
        let ptr = self.peek_ptr();

        self.builder.build_store(ptr, val).unwrap();
    }

    /// OPERATIONS

    // numbers

    fn push_static_number(&self, int: u64) {
        let i8_type = self.context.i8_type();
        let int = i8_type.const_int(int, false);

        self.push_stack(int);
    }

    // normal operations

    fn addition(&self) {
        let a = self.pop_stack();
        let b = self.pop_stack();

        let res = self.builder.build_int_add(a, b, "math").unwrap();
        self.push_stack(res);
    }

    fn subtraction(&self) {
        let a = self.pop_stack();
        let b = self.pop_stack();

        let res = self.builder.build_int_sub(b, a, "math").unwrap();
        self.push_stack(res);
    }

    fn multiplication(&self) {
        panic!("no impled yet D:")
    }
    fn division(&self) {
        panic!("no impled yet D:")
    }
    fn modulo(&self) {
        panic!("no impled yet D:")
    }
    fn not(&self) {
        panic!("no impled yet D:")
    }
    fn greater_than(&self) {
        panic!("no impled yet D:")
    }
    fn duplicate(&self) {
        panic!("no impled yet D:")
    }
    fn swap(&self) {
        panic!("no impled yet D:")
    }
    fn pop_and_discard(&self) {
        panic!("no impled yet D:")
    }

    // put
    fn put(&self) {
        let y = self.pop_stack();
        let x = self.pop_stack();
        let value = self.pop_stack();

        // BIT PACK YEAAAAA!!
        // pack format: first 8 bits y, then x, then value
        // so y << 0, x << 8, value << 16

        let eight = self.context.i8_type().const_int(8, false);
        let x = self.builder.build_left_shift(x, eight, "x").unwrap();

        let sixteen = self.context.i8_type().const_int(16, false);
        let value = self.builder.build_left_shift(value, sixteen, "v").unwrap();

        let res = self.builder.build_int_add(y, x, "res").unwrap();
        let res = self.builder.build_int_add(res, value, "res").unwrap();
        self.builder.build_return(Some(&res)).unwrap();
    }

    // return

    fn return_pop_stack(&self) {
        let x = self.pop_stack();
        let x = self
            .builder
            .build_int_s_extend(x, self.context.i64_type(), "res")
            .unwrap();
        self.builder.build_return(Some(&x)).unwrap();
    }

    fn return_zero(&self) {
        let zero = self.context.i64_type().const_zero();
        self.builder.build_return(Some(&zero)).unwrap();
    }

    /// JIT TIME

    fn jit_befunge(&self, mut befunge_state: BefungeState) {
        loop {
            let (func, last_char) = self.jit_one_expression(&mut befunge_state);
            // that func is cacheable baybee :)
            let status;
            unsafe { status = func.call() };
            println!("status: {}, char: '{}'", status, last_char as char);
            match last_char {
                b'@' => {
                    return;
                }
                b'?' => {
                    befunge_state.direction = rand::random();
                }
                b'_' => {
                    if status == 0 {
                        befunge_state.direction = Direction::East
                    } else {
                        befunge_state.direction = Direction::West
                    }
                    befunge_state.step();
                }
                b'|' => {
                    if status == 0 {
                        befunge_state.direction = Direction::South
                    } else {
                        befunge_state.direction = Direction::North
                    }
                    befunge_state.step();
                }
                b'p' => {
                    // in this situation status is bit packed
                    let y = status as u8;
                    let x = (status >> 8) as u8;
                    let value = (status >> 16) as u8;

                    // TODO: invalidate cache here
                    befunge_state
                        .program
                        .set(&Location(x as usize, y as usize), value)
                }
                _ => (),
            }
        }
    }

    fn jit_one_expression(
        &self,
        befunge_state: &mut BefungeState,
    ) -> (JitFunction<BefungeFunc>, u8) {
        let module = self.context.create_module("befunger");
        self.execution_engine.add_module(&module).unwrap();
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[], false);

        // FIXME: safety last, chance of name collision is lowTM ;)
        let func_name = Alphanumeric.sample_string(&mut rand::thread_rng(), 16);
        let function = module.add_function(&func_name, fn_type, None);
        let basic_block = self.context.append_basic_block(function, "entry");

        self.builder.position_at_end(basic_block);

        let mut char;

        loop {
            char = befunge_state.program.get(&befunge_state.location);
            //println!("op: {}", char as char);
            match char {
                // TODO: rest o the numbers :)
                b'0'..=b'9' => self.push_static_number((char - b'0') as u64),

                // normal operations
                b'+' => self.addition(),
                b'-' => self.subtraction(),
                b'*' => self.multiplication(),
                b'/' => self.division(),
                b'%' => self.modulo(),
                b'!' => self.not(),
                b'`' => self.greater_than(),
                b':' => self.duplicate(),
                b'\\' => self.swap(),
                b'$' => self.pop_and_discard(),

                // static moves (don't worry about these JIT)
                b'>' => befunge_state.direction = Direction::East,
                b'<' => befunge_state.direction = Direction::West,
                b'^' => befunge_state.direction = Direction::North,
                b'v' => befunge_state.direction = Direction::South,
                b'#' => befunge_state.step(), // skip forwards one

                // dynamic moves (sorry JIT, we've gotta pause here)
                // logic for where to go is handled later because the JIT
                // doesn't know about runtime state
                b'?' | b'_' | b'|' => {
                    self.return_pop_stack();
                    break;
                }

                // string mode
                b'"' => panic!("unimplemented"),

                // put (this is the big one!)
                b'p' => self.put(),
                // get
                b'g' => panic!("unimplemented"),

                // input
                b'&' => panic!("unimplemented"),
                b'~' => panic!("unimplemented"),

                // output
                b'.' => panic!("unimplemented"),
                b',' => panic!("unimplemented"),

                // halt
                b'@' => {
                    self.return_zero();
                    break;
                }

                // noop
                b' ' => (),

                char => panic!("UNKNOWN FUNC :( {:?}", char as char),
            }
            befunge_state.step();
            // TODO: put a debug info here
            //let res = self.peek_stack();
            //self.printf_int(res);
        }

        println!(
            "-- LLVM IR begin: \n{}-- LLVM IR end:\n",
            module.print_to_string().to_string()
        );

        let func: JitFunction<BefungeFunc>;
        unsafe {
            //self.execution_engine.run_function(function, &[]);
            // want to be able to cache later so cannot use run_function :(
            func = self.execution_engine.get_function(&func_name).unwrap();
        }

        return (func, char);
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let context = Context::create();
    let module = context.create_module("befunge");
    let execution_engine = module.create_jit_execution_engine(OptimizationLevel::None)?;

    let codegen = CodeGen {
        context: &context,
        module,
        builder: context.create_builder(),
        execution_engine,
    };
    codegen.prelude();
    /*
    println!(
        "-- LLVM IR PRELUDE begin: \n{}-- LLVM IR PRELUDE end:\n",
        codegen.module.print_to_string().to_string()
    );
    */

    let x = r#"
2 2 +v
@ _+4<"#
        .chars()
        .skip(1)
        .collect::<String>(); //skip first line :)
                              //
    let befunge = BefungeState::new(&x);
    codegen.jit_befunge(befunge);

    return Ok(());
}

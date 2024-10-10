#![allow(clippy::cast_possible_truncation, clippy::needless_raw_string_hashes)]
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::execution_engine::ExecutionEngine;
use inkwell::module::Module;
use inkwell::values::{FunctionValue, IntValue, PointerValue};
use inkwell::{AddressSpace, OptimizationLevel};
use rand::distributions::{Alphanumeric, DistString};

//use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
//use gxhash::{HashMap, HashSet};
//use std::collections::{HashMap, HashSet};
use ahash::{AHashMap as HashMap, AHashSet as HashSet};

mod program;

use crate::program::{Direction, Location, Program};
use std::error::Error;
use std::io;
use std::io::Read;

// TODO:
// pop zero from stack when empty (and don't decrement stack counter)
// catch stack overflow in llvm IR, and return if so?
// read from file
// figure out a good debug info system

const STACK_SIZE: usize = 256;
const PRINT_LLVM_IR: bool = false;

#[repr(C)]
#[derive(Debug, Clone, Copy)]
struct BefungeReturn(u64, u64, u64);

type BefungeFunc = unsafe extern "C" fn() -> *const BefungeReturn;
type BefungePutFunc = unsafe extern "C" fn(u64) -> ();

struct FunctionEffects {
    last_char: u8,
    func: BefungeFunc,
    state_after: BefungeState,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct BefungeState {
    location: Location,
    direction: Direction,
}

impl BefungeState {
    const fn get_index(&self, program: &Program) -> usize {
        self.direction as usize + program.calc_index(&self.location) * 4
    }
}

struct Cache {
    data: Vec<Option<FunctionEffects>>,
}

impl Cache {
    fn new(program: &Program) -> Self {
        let mut x = Vec::new();
        x.resize_with(program.width * (program.height + 1) * 4, || None);
        Self { data: x }
    }

    fn get(&self, program: &Program, key: &BefungeState) -> Option<&FunctionEffects> {
        let index = key.get_index(program);
        let x = self.data.get(index);
        x.and_then(std::convert::Into::into)
    }

    fn set(&mut self, program: &Program, key: BefungeState, val: FunctionEffects) {
        self.data[key.get_index(program)] = Some(val);
    }

    fn delete(&mut self, program: &Program, key: &BefungeState) {
        self.data[key.get_index(program)] = None;
    }
}

impl BefungeState {
    const fn new() -> Self {
        Self {
            location: Location(0, 0),
            direction: Direction::East,
        }
    }

    fn step(&mut self, program: &Program) {
        self.location = program.step_with_wrap(self.direction, self.location);
    }
}

struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    execution_engine: ExecutionEngine<'ctx>,
}

/// PRELUDE
impl<'ctx> CodeGen<'ctx> {
    fn prelude(&self) -> Result<(), Box<dyn Error>> {
        let i64_type = self.context.i64_type();
        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let stack_type = i64_type.vec_type(STACK_SIZE as u32);
        let status_type = self
            .context
            .struct_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);

        let zero = i64_type.const_int(0, false);
        let stack_zero = stack_type.const_zero();
        let status_zero = status_type.const_zero();

        let stack_counter = self.module.add_global(i64_type, None, "stack_counter");
        stack_counter.set_initializer(&zero);

        let stack = self.module.add_global(stack_type, None, "stack");
        stack.set_initializer(&stack_zero);

        let status = self.module.add_global(status_type, None, "status");
        status.set_initializer(&status_zero);

        let printf_type = self.context.i32_type().fn_type(&[ptr_type.into()], true);
        let printf = self.module.add_function("printf", printf_type, None);

        self.prelude_build_printf_int(printf)?;
        self.prelude_build_printf_char(printf)?;
        self.prelude_build_put_int()?;
        Ok(())
    }

    fn prelude_build_printf_int(&self, printf: FunctionValue) -> Result<(), Box<dyn Error>> {
        let i64_type = self.context.i64_type();
        let func_type = self.context.void_type().fn_type(&[i64_type.into()], false);
        let function = self.module.add_function("printf_int", func_type, None);
        let basic_block = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(basic_block);
        let str = unsafe {
            self.builder
                .build_global_string("%d ", "int_str")?
                .as_pointer_value()
        };
        let val = function
            .get_nth_param(0)
            .expect("printf_int function has one arg")
            .into_int_value();
        self.builder
            .build_call(printf, &[str.into(), val.into()], "printy")?;
        self.builder.build_return(None)?;
        Ok(())
    }

    fn prelude_build_printf_char(&self, printf: FunctionValue) -> Result<(), Box<dyn Error>> {
        let i64_type = self.context.i64_type();
        let func_type = self.context.void_type().fn_type(&[i64_type.into()], false);
        let function = self.module.add_function("printf_char", func_type, None);
        let basic_block = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(basic_block);
        let str = unsafe {
            self.builder
                .build_global_string("%c ", "int_str")
                .expect("printf_char function has one arg")
                .as_pointer_value()
        };
        let val = function.get_nth_param(0).unwrap().into_int_value();
        self.builder
            .build_call(printf, &[str.into(), val.into()], "printy")?;
        self.builder.build_return(None)?;
        Ok(())
    }

    fn prelude_build_put_int(&self) -> Result<(), Box<dyn Error>> {
        let i64_type = self.context.i64_type();
        let func_type = self.context.void_type().fn_type(&[i64_type.into()], false);
        let function = self.module.add_function("put_int", func_type, None);
        let basic_block = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(basic_block);
        let val = function
            .get_nth_param(0)
            .expect("put_int has one arg")
            .into_int_value();
        self.push_stack(val)?;
        self.builder.build_return(None)?;
        Ok(())
    }
}

/// GENERAL UTILITY
impl<'ctx> CodeGen<'ctx> {
    fn printf_int(&self, int: IntValue) -> Result<(), Box<dyn Error>> {
        let printf = self
            .module
            .get_function("printf_int")
            .expect("printf_int exists globally");

        self.builder
            .build_call(printf, &[int.into()], "print_int")?;
        Ok(())
    }

    fn printf_char(&self, int: IntValue) -> Result<(), Box<dyn Error>> {
        let printf = self
            .module
            .get_function("printf_char")
            .expect("printf_char exists globally");

        self.builder
            .build_call(printf, &[int.into()], "print_char")?;
        Ok(())
    }

    fn get_put_int_fn_ptr(&self) -> BefungePutFunc {
        unsafe {
            self.execution_engine
                .get_function("put_int")
                .expect("put_int exists globally")
                .into_raw()
        }
    }

    fn get_stack_counter_ptr(&self) -> PointerValue<'_> {
        self.module
            .get_global("stack_counter")
            .expect("stack_counter exists globally")
            .as_pointer_value()
    }

    fn get_stack_ptr(&self) -> PointerValue<'_> {
        self.module
            .get_global("stack")
            .expect("stack exists globally")
            .as_pointer_value()
    }

    fn get_status_ptr(&self) -> PointerValue<'_> {
        self.module
            .get_global("status")
            .expect("status exists globally")
            .as_pointer_value()
    }

    fn increment_stack_counter(&self) -> Result<(), Box<dyn Error>> {
        let i64_type = self.context.i64_type();
        let one = i64_type.const_int(1, false);

        let ptr = self.get_stack_counter_ptr();

        let stack_counter = self
            .builder
            .build_load(i64_type, ptr, "count")?
            .into_int_value();

        let stack_counter = self.builder.build_int_add(stack_counter, one, "count")?;

        self.builder.build_store(ptr, stack_counter)?;
        Ok(())
    }

    fn decrement_stack_counter(&self) -> Result<(), Box<dyn Error>> {
        let i64_type = self.context.i64_type();
        let minus_one = i64_type.const_int(u64::MAX, false); // ;)

        let ptr = self.get_stack_counter_ptr();

        let stack_counter = self
            .builder
            .build_load(i64_type, ptr, "count")?
            .into_int_value();

        let stack_counter = self
            .builder
            .build_int_add(stack_counter, minus_one, "count")?;

        self.builder.build_store(ptr, stack_counter)?;
        Ok(())
    }

    fn peek_ptr(&self) -> Result<PointerValue<'_>, Box<dyn Error>> {
        let i64_type = self.context.i64_type();
        let stack_type = i64_type.vec_type(STACK_SIZE as u32);
        let zero = i64_type.const_zero();

        let stack_ptr = self.get_stack_ptr();
        let counter_ptr = self.get_stack_counter_ptr();
        let counter = self
            .builder
            .build_load(i64_type, counter_ptr, "count")?
            .into_int_value();

        unsafe {
            Ok(self
                .builder
                .build_in_bounds_gep(stack_type, stack_ptr, &[zero, counter], "val")?)
        }
    }

    fn peek_stack(&self) -> Result<IntValue<'_>, Box<dyn Error>> {
        let i64_type = self.context.i64_type();
        let ptr = self.peek_ptr()?;

        let res = self
            .builder
            .build_load(i64_type, ptr, "stack_val")?
            .into_int_value();

        Ok(res)
    }

    fn pop_stack(&self) -> Result<IntValue<'_>, Box<dyn Error>> {
        let res = self.peek_stack()?;
        self.decrement_stack_counter()?;

        Ok(res)
    }

    fn push_stack(&self, val: IntValue<'_>) -> Result<(), Box<dyn Error>> {
        self.increment_stack_counter()?;
        let ptr = self.peek_ptr()?;

        self.builder.build_store(ptr, val)?;
        Ok(())
    }
}

/// OPERATIONS
impl<'ctx> CodeGen<'ctx> {
    // numbers

    fn push_static_number(&self, int: u64) -> Result<(), Box<dyn Error>> {
        let i64_type = self.context.i64_type();
        let int = i64_type.const_int(int, false);

        self.push_stack(int)?;
        Ok(())
    }

    // normal operations

    fn addition(&self) -> Result<(), Box<dyn Error>> {
        let a = self.pop_stack()?;
        let b = self.pop_stack()?;

        let res = self.builder.build_int_add(a, b, "add")?;
        self.push_stack(res)?;
        Ok(())
    }

    fn subtraction(&self) -> Result<(), Box<dyn Error>> {
        let a = self.pop_stack()?;
        let b = self.pop_stack()?;

        let res = self.builder.build_int_sub(b, a, "sub")?;
        self.push_stack(res)?;
        Ok(())
    }

    fn multiplication(&self) -> Result<(), Box<dyn Error>> {
        let a = self.pop_stack()?;
        let b = self.pop_stack()?;
        let res = self.builder.build_int_mul(b, a, "mult")?;
        self.push_stack(res)?;
        Ok(())
    }

    fn division(&self) -> Result<(), Box<dyn Error>> {
        let a = self.pop_stack()?;
        let b = self.pop_stack()?;
        let res = self.builder.build_int_signed_div(b, a, "div")?;
        self.push_stack(res)?;
        Ok(())
    }

    fn modulo(&self) -> Result<(), Box<dyn Error>> {
        let a = self.pop_stack()?;
        let b = self.pop_stack()?;
        // FIXME: check what to do on negative/zero b!!
        let res = self.builder.build_int_signed_rem(b, a, "modulo")?;
        self.push_stack(res)?;
        Ok(())
    }

    // if zero, set to 1, else set to zero
    fn not(&self, func: FunctionValue) -> Result<(), Box<dyn Error>> {
        let zero = self.context.i64_type().const_zero();
        let a = self.pop_stack()?;

        let cond = self
            .builder
            .build_int_compare(inkwell::IntPredicate::EQ, a, zero, "iszero")
            .unwrap();

        let zero_block = self.context.append_basic_block(func, "zero");
        let not_zero_block = self.context.append_basic_block(func, "not_zero");
        let cont_block = self.context.append_basic_block(func, "cont");

        self.builder
            .build_conditional_branch(cond, zero_block, not_zero_block)
            .unwrap();

        self.builder.position_at_end(zero_block);
        self.push_static_number(1)?;
        self.builder.build_unconditional_branch(cont_block).unwrap();

        self.builder.position_at_end(not_zero_block);
        self.push_static_number(0)?;
        self.builder.build_unconditional_branch(cont_block).unwrap();

        self.builder.position_at_end(cont_block);
        Ok(())
    }

    fn greater_than(&self, func: FunctionValue) -> Result<(), Box<dyn Error>> {
        let a = self.pop_stack()?;
        let b = self.pop_stack()?;

        let cond = self
            .builder
            .build_int_compare(inkwell::IntPredicate::SGE, b, a, "isgreater")?;

        let greater_block = self.context.append_basic_block(func, "a_greater");
        let not_greater_block = self.context.append_basic_block(func, "a_not_greater");
        let cont_block = self.context.append_basic_block(func, "cont");

        self.builder
            .build_conditional_branch(cond, greater_block, not_greater_block)?;

        self.builder.position_at_end(greater_block);
        self.push_static_number(1)?;
        self.builder.build_unconditional_branch(cont_block)?;

        self.builder.position_at_end(not_greater_block);
        self.push_static_number(0)?;
        self.builder.build_unconditional_branch(cont_block)?;

        self.builder.position_at_end(cont_block);
        Ok(())
    }

    fn duplicate(&self) -> Result<(), Box<dyn Error>> {
        let a = self.peek_stack()?;
        self.push_stack(a)?;
        Ok(())
    }

    fn swap(&self) -> Result<(), Box<dyn Error>> {
        let a = self.pop_stack()?;
        let b = self.pop_stack()?;
        self.push_stack(a)?;
        self.push_stack(b)?;
        Ok(())
    }

    fn pop_and_discard(&self) -> Result<(), Box<dyn Error>> {
        self.pop_stack()?;
        Ok(())
    }

    // return

    fn return_data(&self, vals: &[IntValue; 3]) -> Result<(), Box<dyn Error>> {
        let ptr = self.get_status_ptr();
        let i64_type = self.context.i64_type();
        let status_type = self
            .context
            .struct_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);

        let status = status_type.const_zero();
        let status = self.builder.build_insert_value(status, vals[0], 0, "out")?;
        let status = self.builder.build_insert_value(status, vals[1], 1, "out")?;
        let status = self.builder.build_insert_value(status, vals[2], 2, "out")?;

        self.builder.build_store(ptr, status)?;

        self.builder.build_return(Some(&ptr))?;
        Ok(())
    }

    fn return_pop_three(&self) -> Result<(), Box<dyn Error>> {
        let y = self.pop_stack()?;
        let x = self.pop_stack()?;
        let value = self.pop_stack()?;

        self.return_data(&[x, y, value])?;
        Ok(())
    }

    fn return_pop_two(&self) -> Result<(), Box<dyn Error>> {
        let zero = self.context.i64_type().const_zero();

        let y = self.pop_stack()?;
        let x = self.pop_stack()?;

        self.return_data(&[x, y, zero])?;
        Ok(())
    }

    fn return_pop_one(&self) -> Result<(), Box<dyn Error>> {
        let zero = self.context.i64_type().const_zero();

        let x = self.pop_stack()?;

        self.return_data(&[x, zero, zero])?;
        Ok(())
    }

    fn return_zero(&self) -> Result<(), Box<dyn Error>> {
        let zero = self.context.i64_type().const_zero();
        self.return_data(&[zero, zero, zero])?;
        Ok(())
    }
}

/// JIT TIME
impl<'ctx> CodeGen<'ctx> {
    fn jit_befunge(
        &self,
        mut program: Program,
        init_state: Option<BefungeState>,
    ) -> Result<(), Box<dyn Error>> {
        let put_int = self.get_put_int_fn_ptr();

        let mut cache_ratio = (0, 0); // FOR DEBUGGING

        let mut state = init_state.unwrap_or_else(BefungeState::new);
        //let mut cache: HashMap<BefungeState, FunctionEffects> = HashMap::default();
        let mut cache: Cache = Cache::new(&program);
        let mut visited: HashMap<Location, HashSet<BefungeState>> = HashMap::default();
        loop {
            let func;
            let last_char;
            if let Some(cached_state) = cache.get(&program, &state) {
                func = cached_state.func;
                last_char = cached_state.last_char;
                state = cached_state.state_after;
                cache_ratio.0 += 1;
            } else {
                //println!("generating uncached function");
                let start_state = state;
                (func, state, last_char) =
                    self.jit_one_expression(&program, state, &mut visited)?;
                cache.set(
                    &program,
                    start_state,
                    FunctionEffects {
                        last_char,
                        func,
                        state_after: state,
                    },
                );
                cache_ratio.1 += 1;
            }
            //println!("{} cached vs {} uncached", cache_count.0, cache_count.1);
            let status = unsafe { *func() };
            //println!("status: {status:?}, char: '{}'", last_char as char);
            match last_char {
                b'@' => {
                    return Ok(());
                }
                b'?' => {
                    state.direction = rand::random();
                }
                b'_' => {
                    let status = status.0;
                    if status == 0 {
                        state.direction = Direction::East;
                    } else {
                        state.direction = Direction::West;
                    }
                }
                b'|' => {
                    let status = status.0;
                    if status == 0 {
                        state.direction = Direction::South;
                    } else {
                        state.direction = Direction::North;
                    }
                }
                b'p' => {
                    let y = status.0;
                    let x = status.1;
                    let value = status.2;

                    let loc = Location(x as usize, y as usize);
                    let success = program.set_if_valid(&loc, value);
                    if success {
                        if let Some(visitors) = visited.get(&loc) {
                            for visitor in visitors {
                                cache.delete(&program, visitor);
                            }
                        };
                    };
                }
                b'g' => {
                    let y = status.0;
                    let x = status.1;

                    let val = program
                        .get(&Location(x as usize, y as usize))
                        .unwrap_or_else(|| b' '.into());
                    unsafe { put_int(val) };
                }
                b'&' => {
                    let mut input_line = String::new();
                    io::stdin()
                        .read_line(&mut input_line)
                        .expect("Failed to read line");
                    let x: u64 = input_line.trim().parse().expect("Input not an integer");
                    unsafe { put_int(x) };
                }
                b'~' => {
                    let input = io::stdin()
                        .bytes()
                        .next()
                        .and_then(std::result::Result::ok)
                        .map(u64::from)
                        .expect("Input not a character");
                    unsafe { put_int(input) };
                }
                _ => unreachable!(),
            }
            state.step(&program);
        }
    }

    fn jit_one_expression(
        &self,
        program: &Program,
        initial_state: BefungeState,
        visited: &mut HashMap<Location, HashSet<BefungeState>>,
    ) -> Result<(BefungeFunc, BefungeState, u8), Box<dyn Error>> {
        let mut state = initial_state;

        let module = self.context.create_module("befunger");
        self.execution_engine
            .add_module(&module)
            .expect("Adding a module to the execution engine should not fail as the module was just instanciated and so cannot already be in any execution engine");
        let ptr_type = self.context.ptr_type(AddressSpace::default());

        // see BefungeFunc
        let fn_type = ptr_type.fn_type(&[], true);

        // FIXME: safety last, chance of name collision is lowTM ;)
        let func_name = Alphanumeric.sample_string(&mut rand::thread_rng(), 16);
        let function = module.add_function(&func_name, fn_type, None);
        let basic_block = self.context.append_basic_block(function, "entry");

        self.builder.position_at_end(basic_block);

        let mut char: u8;

        loop {
            let maybe_char = program.get_unchecked(&state.location).try_into();
            // TODO: make not panic!()
            char = maybe_char.expect("Char should be a valid operation");
            //println!("op: {}, loc: {:?}", char as char, state.location);
            match visited.get_mut(&state.location) {
                None => {
                    let mut visitors = HashSet::default();
                    visitors.insert(initial_state);
                    visited.insert(state.location, visitors);
                }
                Some(visitors) => {
                    visitors.insert(initial_state);
                }
            };

            match char {
                // string mode
                b'"' => {
                    // read all characters directly onto stack until next "
                    loop {
                        state.step(program);
                        let char = program.get_unchecked(&state.location);
                        if char == b'"'.into() {
                            break;
                        }
                        self.push_static_number(char)?;
                    }
                }

                b'0'..=b'9' => self.push_static_number((char - b'0').into())?,

                // normal operations
                b'+' => self.addition()?,
                b'-' => self.subtraction()?,
                b'*' => self.multiplication()?,
                b'/' => self.division()?,
                b'%' => self.modulo()?,
                b'!' => self.not(function)?,
                b'`' => self.greater_than(function)?,
                b':' => self.duplicate()?,
                b'\\' => self.swap()?,
                b'$' => self.pop_and_discard()?,

                // static moves (don't worry about these JIT)
                b'>' => state.direction = Direction::East,
                b'<' => state.direction = Direction::West,
                b'^' => state.direction = Direction::North,
                b'v' => state.direction = Direction::South,
                b'#' => state.step(program), // skip forwards one

                // dynamic moves (sorry JIT, we've gotta pause here)
                // logic for where to go is handled later because the JIT
                // doesn't know about runtime state
                b'?' | b'_' | b'|' => {
                    self.return_pop_one()?;
                    break;
                }

                // put (this is the big one!)
                b'p' => {
                    self.return_pop_three()?;
                    break;
                }

                // get
                b'g' => {
                    self.return_pop_two()?;
                    break;
                }

                // input or halt
                b'@' | b'&' | b'~' => {
                    self.return_zero()?;
                    break;
                }

                // output
                b'.' => self.printf_int(self.pop_stack()?)?,
                b',' => self.printf_char(self.pop_stack()?)?,

                // noop
                b' ' => (),

                char => panic!("UNKNOWN FUNC :( {:?}", char as char),
            }
            state.step(program);
            // TODO: put a debug info here
            //self.printf_int(self.peek_stack());
        }

        if PRINT_LLVM_IR {
            println!(
                "-- LLVM IR begin: \n{}-- LLVM IR end:\n",
                module.print_to_string().to_string()
            );
        }

        //println!("{:?}", program);

        // inkwell provides no get_function by FunctionValue
        // so we will just pass around this FunctionValue
        // and call it ourselves

        let func = unsafe { self.execution_engine.get_function(&func_name)?.into_raw() };

        Ok((func, state, char))
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let context = Context::create();
    let module = context.create_module("befunge");
    let execution_engine = module.create_jit_execution_engine(OptimizationLevel::Aggressive)?;

    let codegen = CodeGen {
        context: &context,
        module,
        builder: context.create_builder(),
        execution_engine,
    };
    codegen.prelude()?;
    if PRINT_LLVM_IR {
        println!(
            "-- LLVM IR PRELUDE begin: \n{}-- LLVM IR PRELUDE end:\n",
            codegen.module.print_to_string().to_string()
        );
    }
    // https://github.com/Mikescher/BefungePrograms?tab=readme-ov-file
    let windmill = r##"
0".omed s"v                                          
          "                       >v
          i                        8
                                   4
          s             >       > ^*
          i    >99+0g1+#^_77+0g#^_188+0p099+0p>  v
          h    ^        <          #            <
          T    >88+0g1+#^_66+0g#^_088+0p01-99+0p^
          "    ^        <         <#             #<
>         v    >99+0g1-#^_77+0g8-#^_01-88+0p099+0p^
|   >#:>#,<    ^        <         <#            <2
               >88+0g1-#^_66+0g8-#^_088+0p199+0p^2
>0>:"#"\0p:5 v ^                   $             g
v_^#!\+1\!`+4< ^p0+77+g0+99g0+77<  >66+0g1+v     v
>1-:"#"\v      >66+0g88+0g+66+0p^  v+1g0+77<     8
|`0:p+19<      ^                   g             4
>:"#"\0\p:v>   ^<                  -             *
|\+1\!`+45<^p0+<               v" "_"@"v         -
>1-:"#"\ v>p099^^     <        >66+v+66<         #
|`0:p\+19<^0+88<^      p+1g0+77+1g0<       >" " #< v
$>-66+0p077+0p1^ vp+2g0+67+2g0+56 < pp0+67:0+560<|#<
01               :    #    v    p0 +76+1g< >"#" #< ^
>^               >65+0g6- #v_01-65+0p67+0^
                      ^ $ <>76+0gv#
                          ^     <> 7-v
                                ^_v#!<
                                  #
                           >+56+0p^
                           ^1g0+56<"##
        .chars()
        .skip(1)
        .collect::<String>(); //skip first line :)
    let countdown = r##"
v       vg00p00<
9    >:.>:.1-: |
9    *         .
9    *         @
9    *
9    *
>99**^     "##
        .chars()
        .skip(1)
        .collect::<String>();
    let primes = r##"
v     works for    0 < n < 1,373,653
 


  v                                                                                                              <<
                                                                                                                 ,
                                         >             >             >      >$0v                                 +
                                                >             >              $1v                                 5
>0>1+:                              :2\`#^_:2-!#^_:2%!#^_:9\`#^_:3%!#^_:5%!#^_1 :v                               5
                                    v\                      p13:+1g13:_v#-3 <p1 3<                               .
                                    >:11p1-0\>:2% !#v_v    v ++!!+1-g< #    ^ <                                  :
                                             ^\+1\/2< \    >3-#v_$$  1>31g\  !|>                                 |
                                     vp01p03p04 g11p12<        >:*11v1 >$1   #$^                                 >^
                                     >120pv        v%g04*<v-1\    %g<^ \!!-1:<$0 
                                     vg030<  v-1\  < >10g^   >\:::*11  g%1-!\^>^ 
                                         >$1\> :#v_ $ 21g >:#^_$1-!!  ^
                                     >:!#^_\1+\2v\ ^_^#!%2/\g03p<
                                     ^p02*2g02/ <>:*40g%20g2/:20^


"##.chars().skip(1).collect::<String>();
    let quine = r##">:# 0# g# ,# 1# +# 0#_ #! _0#1 "this crap writes itself!" #0 #_ #! _#0 :# 3# 5# *# 7# *# #?# %# _@"##;
    let wasd = r##">~:,1-,@"##;
    //let program = Program::new(&countdown);
    let program = Program::new(&primes);
    //let program = Program::new(&wasd);

    codegen.jit_befunge(program, None)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn example() {
        assert_eq!(5, 5);
    }
}

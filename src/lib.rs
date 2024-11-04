#![allow(clippy::cast_possible_truncation, clippy::needless_raw_string_hashes)]
use inkwell::builder::{Builder, BuilderError};
use inkwell::context::Context;
use inkwell::execution_engine::ExecutionEngine;
use inkwell::module::Module;
use inkwell::support::LLVMString;
use inkwell::values::{FunctionValue, IntValue, PointerValue};
use inkwell::{AddressSpace, OptimizationLevel};
use rand::distributions::{Alphanumeric, DistString};

use ahash::{AHashMap as HashMap, AHashSet as HashSet};

mod program;
use program::step_with_wrap;

pub use crate::program::{Direction, Location, Program};
use core::slice;
use std::io::{self, Read};

use thiserror::Error;

#[derive(Error, Debug)]
pub enum BefungeError {
    #[error("The JIT compiler failed to initialize")]
    JitInitializeFailure(LLVMString),
    #[error("An error occured while trying to convert the befunge to llvm IR")]
    InkwellCompileError(#[from] BuilderError),
    #[error("The execution reached an invalid instruction: {0}")]
    InvalidInstruction(u64),
}

// TODO:
// pop zero from stack when empty (and don't decrement stack counter)
// catch stack overflow in llvm IR, and return if so?
// cleanup function pointers n stuff currently they dangle i think
// figure out a good debug info system
// allow file as positional arg as well as flag

const STACK_SIZE: usize = 500;

#[repr(C)]
#[derive(Debug, Clone, Copy)]
struct BefungeReturn(u64, u64, u64);

type BefungeFunc = unsafe extern "C" fn() -> *const BefungeReturn;
type PutIntFunc = unsafe extern "C" fn(u64) -> ();

struct CachedFunction {
    last_char: u8,
    func: BefungeFunc,
    pos_after: BefungePosition,
}

/// Current location and direction of execution
/// Used as keys for getting cached compiled functions
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BefungePosition {
    pub location: Location,
    pub direction: Direction,
}

impl Default for BefungePosition {
    fn default() -> Self {
        Self {
            location: Location(0, 0),
            direction: Direction::East,
        }
    }
}

impl BefungePosition {
    const fn get_index(&self, width: usize) -> usize {
        self.direction as usize + Program::calc_index(&self.location, width) * 4
    }
}

struct FunctionCache {
    data: Vec<Option<CachedFunction>>,
    width: usize,
}

impl FunctionCache {
    fn new(width: usize, height: usize) -> Self {
        let mut x = Vec::new();
        x.resize_with((width + 1) * (height + 1) * 4, || None);
        Self { data: x, width }
    }

    fn get(&self, key: &BefungePosition) -> Option<&CachedFunction> {
        let index = key.get_index(self.width);
        let x = self.data.get(index);
        x.and_then(std::convert::Into::into)
    }

    fn set(&mut self, key: BefungePosition, val: CachedFunction) {
        self.data[key.get_index(self.width)] = Some(val);
    }

    fn delete(&mut self, key: &BefungePosition) {
        self.data[key.get_index(self.width)] = None;
    }
}

struct CodeGen<'ctx> {
    config: JitOptions,
    context: &'ctx Context,
    base_module: Module<'ctx>,
    builder: Builder<'ctx>,
    execution_engine: ExecutionEngine<'ctx>,
}

impl<'ctx> CodeGen<'ctx> {
    fn new(context: &'ctx Context, config: &JitOptions) -> Result<Self, BefungeError> {
        let base_module = context.create_module("befunge");
        let execution_engine = base_module
            .create_jit_execution_engine(config.opt_level)
            .map_err(BefungeError::JitInitializeFailure)?;

        let codegen = CodeGen {
            config: config.clone(),
            builder: context.create_builder(),
            context,
            base_module,
            execution_engine,
        };
        codegen.build_prelude()?;

        if config.print_llvm_ir {
            println!(
                "-- LLVM IR PRELUDE begin: \n{}-- LLVM IR PRELUDE end:\n",
                codegen.base_module.print_to_string().to_string()
            );
        }

        Ok(codegen)
    }
}

/// PRELUDE
impl<'ctx> CodeGen<'ctx> {
    fn build_prelude(&self) -> Result<(), BefungeError> {
        let i64_type = self.context.i64_type();
        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let stack_type = i64_type.vec_type(STACK_SIZE as u32);
        let status_type = self
            .context
            .struct_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);

        let minus_one = i64_type.const_int(u64::MAX, false);
        let stack_zero = stack_type.const_zero();
        let status_zero = status_type.const_zero();

        let stack_counter = self.base_module.add_global(i64_type, None, "stack_counter");
        stack_counter.set_initializer(&minus_one);

        let stack = self.base_module.add_global(stack_type, None, "stack");
        stack.set_initializer(&stack_zero);

        let status = self.base_module.add_global(status_type, None, "status");
        status.set_initializer(&status_zero);

        let printf_type = self.context.i32_type().fn_type(&[ptr_type.into()], true);
        let printf = self.base_module.add_function("printf", printf_type, None);

        self.prelude_build_printf_int(printf)?;
        self.prelude_build_printf_char(printf)?;
        self.prelude_build_put_int()?;
        self.prelude_build_get_stack()?;
        Ok(())
    }

    fn prelude_build_printf_int(&self, printf: FunctionValue) -> Result<(), BefungeError> {
        let i64_type = self.context.i64_type();
        let func_type = self.context.void_type().fn_type(&[i64_type.into()], false);
        let function = self.base_module.add_function("printf_int", func_type, None);
        let basic_block = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(basic_block);
        let str = unsafe {
            self.builder
                .build_global_string("%d ", "int_str")?
                .as_pointer_value()
        };
        let val = function
            .get_nth_param(0)
            .expect("printf_int function has one param")
            .into_int_value();
        self.builder
            .build_call(printf, &[str.into(), val.into()], "printy")?;
        self.builder.build_return(None)?;
        Ok(())
    }

    fn prelude_build_printf_char(&self, printf: FunctionValue) -> Result<(), BefungeError> {
        let i64_type = self.context.i64_type();
        let func_type = self.context.void_type().fn_type(&[i64_type.into()], false);
        let function = self
            .base_module
            .add_function("printf_char", func_type, None);
        let basic_block = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(basic_block);
        let str = unsafe {
            self.builder
                .build_global_string("%c ", "int_str")
                .expect("printf_char function has one arg")
                .as_pointer_value()
        };
        let val = function
            .get_nth_param(0)
            .expect("printf_char function has one param")
            .into_int_value();
        self.builder
            .build_call(printf, &[str.into(), val.into()], "printy")?;
        self.builder.build_return(None)?;
        Ok(())
    }

    fn prelude_build_put_int(&self) -> Result<(), BefungeError> {
        let i64_type = self.context.i64_type();
        let func_type = self.context.void_type().fn_type(&[i64_type.into()], false);

        let function = self.base_module.add_function("put_int", func_type, None);
        let basic_block = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(basic_block);
        let val = function
            .get_nth_param(0)
            .expect("put_int has one param")
            .into_int_value();
        self.build_push_stack(val)?;
        self.builder.build_return(None)?;
        Ok(())
    }

    fn prelude_build_get_stack(&self) -> Result<(), BefungeError> {
        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let func_type = ptr_type.fn_type(&[], false);
        let function = self
            .base_module
            .add_function("return_stack_ptr", func_type, None);
        let basic_block = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(basic_block);
        self.build_return_stack_pointer()?;
        Ok(())
    }
}

/// GENERAL UTILITY
impl<'ctx> CodeGen<'ctx> {
    fn build_printf_int(&self, int: IntValue) -> Result<(), BefungeError> {
        let printf = self
            .base_module
            .get_function("printf_int")
            .expect("printf_int exists globally");

        self.builder
            .build_call(printf, &[int.into()], "print_int")?;
        Ok(())
    }

    fn build_printf_char(&self, int: IntValue) -> Result<(), BefungeError> {
        let printf = self
            .base_module
            .get_function("printf_char")
            .expect("printf_char exists globally");

        self.builder
            .build_call(printf, &[int.into()], "print_char")?;
        Ok(())
    }

    fn get_fn_ptr_put_int(&self) -> PutIntFunc {
        unsafe {
            self.execution_engine
                .get_function("put_int")
                .expect("put_int exists globally")
                .into_raw()
        }
    }

    fn get_fn_ptr_return_stack(&self) -> BefungeFunc {
        unsafe {
            self.execution_engine
                .get_function("return_stack_ptr")
                .expect("return_stack_ptr exists globally")
                .into_raw()
        }
    }

    fn stack_counter_ptr(&self) -> PointerValue<'_> {
        self.base_module
            .get_global("stack_counter")
            .expect("stack_counter exists globally")
            .as_pointer_value()
    }

    fn stack_ptr(&self) -> PointerValue<'_> {
        self.base_module
            .get_global("stack")
            .expect("stack exists globally")
            .as_pointer_value()
    }

    fn status_ptr(&self) -> PointerValue<'_> {
        self.base_module
            .get_global("status")
            .expect("status exists globally")
            .as_pointer_value()
    }

    fn build_increment_stack_counter(&self) -> Result<(), BefungeError> {
        let i64_type = self.context.i64_type();
        let one = i64_type.const_int(1, false);

        let ptr = self.stack_counter_ptr();

        let stack_counter = self
            .builder
            .build_load(i64_type, ptr, "count")?
            .into_int_value();

        let stack_counter = self.builder.build_int_add(stack_counter, one, "count")?;

        self.builder.build_store(ptr, stack_counter)?;
        Ok(())
    }

    fn build_decrement_stack_counter(&self) -> Result<(), BefungeError> {
        let i64_type = self.context.i64_type();
        let minus_one = i64_type.const_int(u64::MAX, false); // ;)

        let ptr = self.stack_counter_ptr();

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

    /** Returns a pointer to the current top of the stack */
    fn build_peek_stack_ptr(&self) -> Result<PointerValue<'_>, BefungeError> {
        let i64_type = self.context.i64_type();
        let stack_type = i64_type.vec_type(STACK_SIZE as u32);
        let zero = i64_type.const_zero();

        let stack_ptr = self.stack_ptr();
        let counter_ptr = self.stack_counter_ptr();
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

    fn build_peek_stack(&self) -> Result<IntValue<'_>, BefungeError> {
        let i64_type = self.context.i64_type();
        let ptr = self.build_peek_stack_ptr()?;

        let res = self
            .builder
            .build_load(i64_type, ptr, "stack_val")?
            .into_int_value();

        Ok(res)
    }

    //TODO: If the stack counter is currently zero, we return zero instead of popping
    fn build_pop_stack(&self) -> Result<IntValue<'_>, BefungeError> {
        //let i64_type = self.context.i64_type();

        //let ptr = self.stack_counter_ptr();

        //let stack_counter = self
        //    .builder
        //    .build_load(i64_type, ptr, "count")?
        //    .into_int_value();

        //let cond = self.builder.build_int_compare(
        //    inkwell::IntPredicate::SLT,
        //    stack_counter,
        //    i64_type.const_zero(),
        //    "iszero",
        //);

        //let zero_block = self.context.append_basic_block(func, "zero");
        //let normal_block = self.context.append_basic_block(func, "nonzero");
        //let cont_block = self.context.append_basic_block(func, "cont");

        let res = self.build_peek_stack()?;
        self.build_decrement_stack_counter()?;

        Ok(res)
    }

    fn build_push_stack(&self, val: IntValue<'_>) -> Result<(), BefungeError> {
        // FIXME: if counter > STACK_SIZE, crash?
        self.build_increment_stack_counter()?;
        let ptr = self.build_peek_stack_ptr()?;

        self.builder.build_store(ptr, val)?;
        Ok(())
    }
}

/// OPERATIONS
impl<'ctx> CodeGen<'ctx> {
    /// numbers

    fn build_push_static_number(&self, int: u64) -> Result<(), BefungeError> {
        let i64_type = self.context.i64_type();
        let int = i64_type.const_int(int, false);

        self.build_push_stack(int)?;
        Ok(())
    }

    /// normal operations

    fn build_addition(&self) -> Result<(), BefungeError> {
        let a = self.build_pop_stack()?;
        let b = self.build_pop_stack()?;

        let res = self.builder.build_int_add(a, b, "add")?;
        self.build_push_stack(res)?;
        Ok(())
    }

    fn build_subtraction(&self) -> Result<(), BefungeError> {
        let a = self.build_pop_stack()?;
        let b = self.build_pop_stack()?;

        let res = self.builder.build_int_sub(b, a, "sub")?;
        self.build_push_stack(res)?;
        Ok(())
    }

    fn build_multiplication(&self) -> Result<(), BefungeError> {
        let a = self.build_pop_stack()?;
        let b = self.build_pop_stack()?;
        let res = self.builder.build_int_mul(b, a, "mult")?;
        self.build_push_stack(res)?;
        Ok(())
    }

    fn build_division(&self) -> Result<(), BefungeError> {
        let a = self.build_pop_stack()?;
        let b = self.build_pop_stack()?;
        let res = self.builder.build_int_signed_div(b, a, "div")?;
        self.build_push_stack(res)?;
        Ok(())
    }

    fn build_modulo(&self) -> Result<(), BefungeError> {
        let a = self.build_pop_stack()?;
        let b = self.build_pop_stack()?;
        // FIXME: check what to do on negative/zero b!!
        let res = self.builder.build_int_signed_rem(b, a, "modulo")?;
        self.build_push_stack(res)?;
        Ok(())
    }

    // if zero, set to 1, else set to zero
    fn build_not(&self, func: FunctionValue) -> Result<(), BefungeError> {
        let zero = self.context.i64_type().const_zero();
        let a = self.build_pop_stack()?;

        let cond = self
            .builder
            .build_int_compare(inkwell::IntPredicate::EQ, a, zero, "iszero")?;

        let zero_block = self.context.append_basic_block(func, "zero");
        let not_zero_block = self.context.append_basic_block(func, "not_zero");
        let cont_block = self.context.append_basic_block(func, "cont");

        self.builder
            .build_conditional_branch(cond, zero_block, not_zero_block)?;

        self.builder.position_at_end(zero_block);
        self.build_push_static_number(1)?;
        self.builder.build_unconditional_branch(cont_block)?;

        self.builder.position_at_end(not_zero_block);
        self.build_push_static_number(0)?;
        self.builder.build_unconditional_branch(cont_block)?;

        self.builder.position_at_end(cont_block);
        Ok(())
    }

    fn build_greater_than(&self, func: FunctionValue) -> Result<(), BefungeError> {
        let a = self.build_pop_stack()?;
        let b = self.build_pop_stack()?;

        let cond = self
            .builder
            .build_int_compare(inkwell::IntPredicate::SGE, b, a, "isgreater")?;

        let greater_block = self.context.append_basic_block(func, "a_greater");
        let not_greater_block = self.context.append_basic_block(func, "a_not_greater");
        let cont_block = self.context.append_basic_block(func, "cont");

        self.builder
            .build_conditional_branch(cond, greater_block, not_greater_block)?;

        self.builder.position_at_end(greater_block);
        self.build_push_static_number(1)?;
        self.builder.build_unconditional_branch(cont_block)?;

        self.builder.position_at_end(not_greater_block);
        self.build_push_static_number(0)?;
        self.builder.build_unconditional_branch(cont_block)?;

        self.builder.position_at_end(cont_block);
        Ok(())
    }

    fn build_duplicate(&self) -> Result<(), BefungeError> {
        let a = self.build_peek_stack()?;
        self.build_push_stack(a)?;
        Ok(())
    }

    fn build_swap(&self) -> Result<(), BefungeError> {
        let a = self.build_pop_stack()?;
        let b = self.build_pop_stack()?;
        self.build_push_stack(a)?;
        self.build_push_stack(b)?;
        Ok(())
    }

    fn build_pop_and_discard(&self) -> Result<(), BefungeError> {
        self.build_pop_stack()?;
        Ok(())
    }

    /// return

    fn build_return_data(&self, vals: &[IntValue; 3]) -> Result<(), BefungeError> {
        let ptr = self.status_ptr();
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

    fn build_return_pop_three(&self) -> Result<(), BefungeError> {
        let y = self.build_pop_stack()?;
        let x = self.build_pop_stack()?;
        let value = self.build_pop_stack()?;

        self.build_return_data(&[x, y, value])?;
        Ok(())
    }

    fn build_return_pop_two(&self) -> Result<(), BefungeError> {
        let zero = self.context.i64_type().const_zero();

        let y = self.build_pop_stack()?;
        let x = self.build_pop_stack()?;

        self.build_return_data(&[x, y, zero])?;
        Ok(())
    }

    fn build_return_pop_one(&self) -> Result<(), BefungeError> {
        let zero = self.context.i64_type().const_zero();

        let x = self.build_pop_stack()?;

        self.build_return_data(&[x, zero, zero])?;
        Ok(())
    }

    fn build_return_zero(&self) -> Result<(), BefungeError> {
        let zero = self.context.i64_type().const_zero();
        self.build_return_data(&[zero, zero, zero])?;
        Ok(())
    }

    fn build_return_stack_pointer(&self) -> Result<(), BefungeError> {
        let i64_type = self.context.i64_type();
        let zero = i64_type.const_zero();

        let ptr = self.stack_ptr();
        let start_ptr = self
            .builder
            .build_ptr_to_int(ptr, i64_type, "stack_pointer")?;

        let ptr = self.build_peek_stack_ptr()?;
        let end_ptr = self
            .builder
            .build_ptr_to_int(ptr, i64_type, "stack_counter_pointer")?;

        self.build_return_data(&[start_ptr, end_ptr, zero])?;
        Ok(())
    }
}

#[derive(Copy, Clone)]
pub struct JitOptions {
    pub opt_level: OptimizationLevel,
    pub print_llvm_ir: bool,
    pub silent: bool,
}

impl Default for JitOptions {
    fn default() -> Self {
        Self {
            opt_level: OptimizationLevel::Default,
            print_llvm_ir: false,
            silent: false,
        }
    }
}

pub struct JitCompiler<'ctx> {
    codegen: CodeGen<'ctx>,
    pub position: BefungePosition,
    function_cache: FunctionCache,
    visited: HashMap<Location, HashSet<BefungePosition>>,
    pub program: Program,
    put_int_func: PutIntFunc,
    get_stack_func: BefungeFunc,
    config: JitOptions,
}

/// JIT TIME
impl<'ctx> JitCompiler<'ctx> {
    fn step_position(&mut self) {
        self.position.location = step_with_wrap(
            self.program.width,
            self.program.height,
            self.position.direction,
            self.position.location,
        );
    }

    pub fn new(
        context: &'ctx Context,
        program: Program,
        opts: JitOptions,
    ) -> Result<Self, BefungeError> {
        let codegen = CodeGen::new(context, &opts)?;
        let put_int_func = codegen.get_fn_ptr_put_int();
        let get_stack_func = codegen.get_fn_ptr_return_stack();

        Ok(Self {
            codegen,
            visited: HashMap::new(),
            position: BefungePosition::default(),
            function_cache: FunctionCache::new(program.width, program.height),
            program,
            put_int_func,
            get_stack_func,
            config: opts,
        })
    }

    pub fn jit_to_completion(&mut self) -> Result<(), BefungeError> {
        loop {
            let finished = self.execute_some()?;
            if finished {
                return Ok(());
            }
        }
    }

    /// Run through some amount of befunge code (until the next branch)
    /// Returns true if execution has stopped (reached an @)
    fn execute_some(&mut self) -> Result<bool, BefungeError> {
        let func;
        let last_char;
        if let Some(cached_side_effects) = self.function_cache.get(&self.position) {
            func = cached_side_effects.func;
            last_char = cached_side_effects.last_char;
            self.position = cached_side_effects.pos_after;
        } else {
            let start_pos = self.position;
            (func, last_char) = self.jit_expression()?;
            self.function_cache.set(
                start_pos,
                CachedFunction {
                    last_char,
                    func,
                    pos_after: self.position,
                },
            );
        }

        //println!("function run: {:?}", self.position);
        //println!("{:?}", unsafe {
        //    let x = *(self.codegen.get_fn_ptr_return_stack())();
        //    read_stack_from_ptr(x.0 as *const u64, x.1 as *const u64)
        //});
        let status = unsafe { *func() };

        match last_char {
            b'@' => {
                /*
                let stack_start = status.0 as *const u64;
                let stack_end = status.1 as *const u64;

                let stack = read_stack_from_ptr(stack_start, stack_end);
                */

                return Ok(true);
            }
            b'q' => {
                let stack_start = status.0 as *const u64;
                let stack_end = status.1 as *const u64;

                let stack = read_stack_from_ptr(stack_start, stack_end);

                println!("stack: {stack:?}");
            }
            b'?' => {
                self.position.direction = rand::random();
            }
            b'_' => {
                let status = status.0;
                if status == 0 {
                    self.position.direction = Direction::East;
                } else {
                    self.position.direction = Direction::West;
                }
            }
            b'|' => {
                let status = status.0;
                if status == 0 {
                    self.position.direction = Direction::South;
                } else {
                    self.position.direction = Direction::North;
                }
            }
            b'p' => {
                let BefungeReturn(y, x, value) = status;

                let loc = Location(x as usize, y as usize);
                let success = self.program.set_if_valid(&loc, value);
                if success {
                    if let Some(visitors) = self.visited.get(&loc) {
                        for visitor in visitors {
                            self.function_cache.delete(visitor);
                        }
                    };
                };
            }
            b'g' => {
                let BefungeReturn(y, x, _) = status;

                let val = self
                    .program
                    .get(&Location(x as usize, y as usize))
                    .unwrap_or_else(|| b' '.into());
                unsafe { (self.put_int_func)(val) };
            }
            b'&' => {
                let mut input_line = String::new();
                io::stdin()
                    .read_line(&mut input_line)
                    .expect("Failed to read line");
                let x: u64 = input_line.trim().parse().expect("Input not an integer");
                unsafe { (self.put_int_func)(x) };
            }
            b'~' => {
                let input = io::stdin()
                    .bytes()
                    .next()
                    .and_then(std::result::Result::ok)
                    .map(u64::from)
                    .expect("Input not a character");
                unsafe { (self.put_int_func)(input) };
            }
            _ => unreachable!(),
        }
        self.step_position();
        Ok(false)
    }

    fn jit_expression(&mut self) -> Result<(BefungeFunc, u8), BefungeError> {
        let module = self.codegen.context.create_module("befunger");
        self.codegen.execution_engine
            .add_module(&module)
            .expect("Adding a module to the execution engine should not fail as the module was just instanciated and so cannot already be in any execution engine");
        let ptr_type = self.codegen.context.ptr_type(AddressSpace::default());

        // see BefungeFunc
        let fn_type = ptr_type.fn_type(&[], true);

        // FIXME: safety last, chance of name collision is lowTM ;)
        let func_name = Alphanumeric.sample_string(&mut rand::thread_rng(), 16);
        let function = module.add_function(&func_name, fn_type, None);
        let basic_block = self.codegen.context.append_basic_block(function, "entry");

        self.codegen.builder.position_at_end(basic_block);

        let mut char: u8;

        loop {
            let maybe_char = self.program.get_unchecked(&self.position.location);
            // attempt to convert the u64 into a u8 char
            char = maybe_char
                .try_into()
                .map_err(|_| BefungeError::InvalidInstruction(maybe_char))?;

            //println!("op: {}, loc: {:?}", char as char, pos.location);
            match self.visited.get_mut(&self.position.location) {
                None => {
                    let mut visitors = HashSet::default();
                    visitors.insert(self.position);
                    self.visited.insert(self.position.location, visitors);
                }
                Some(visitors) => {
                    visitors.insert(self.position);
                }
            };

            match char {
                // string mode
                b'"' => {
                    // read all characters directly onto stack until next "
                    loop {
                        self.step_position();
                        let char = self.program.get_unchecked(&self.position.location);
                        if char == b'"'.into() {
                            break;
                        }
                        self.codegen.build_push_static_number(char)?;
                    }
                }

                b'0'..=b'9' => self
                    .codegen
                    .build_push_static_number((char - b'0').into())?,

                // -- normal operations
                b'+' => self.codegen.build_addition()?,
                b'-' => self.codegen.build_subtraction()?,
                b'*' => self.codegen.build_multiplication()?,
                b'/' => self.codegen.build_division()?,
                b'%' => self.codegen.build_modulo()?,
                b'!' => self.codegen.build_not(function)?,
                b'`' => self.codegen.build_greater_than(function)?,
                b':' => self.codegen.build_duplicate()?,
                b'\\' => self.codegen.build_swap()?,
                b'$' => self.codegen.build_pop_and_discard()?,

                // -- static direction changes
                // (compilation can continue fine)
                b'>' => self.position.direction = Direction::East,
                b'<' => self.position.direction = Direction::West,
                b'^' => self.position.direction = Direction::North,
                b'v' => self.position.direction = Direction::South,
                b'#' => self.step_position(), // skip forwards one

                // -- dynamic direction changes
                // (compilation pauses here, the outcome of the branch is not known until runtime)
                b'?' | b'_' | b'|' => {
                    self.codegen.build_return_pop_one()?;
                    break;
                }

                // put (this is the big one!)
                b'p' => {
                    self.codegen.build_return_pop_three()?;
                    break;
                }

                // get
                b'g' => {
                    self.codegen.build_return_pop_two()?;
                    break;
                }

                // input
                b'&' | b'~' => {
                    self.codegen.build_return_zero()?;
                    break;
                }

                // halt and debug operator
                b'@' | b'q' => {
                    self.codegen.build_return_stack_pointer()?;
                    break;
                }

                // -- IO output
                b'.' => {
                    if !self.config.silent {
                        self.codegen
                            .build_printf_int(self.codegen.build_pop_stack()?)?
                    }
                }
                b',' => {
                    if !self.config.silent {
                        self.codegen
                            .build_printf_char(self.codegen.build_pop_stack()?)?
                    }
                }

                // noop
                b' ' => (),

                char => return Err(BefungeError::InvalidInstruction(char.into())),
            }
            self.step_position();
        }

        if self.config.print_llvm_ir {
            println!(
                "-- LLVM IR begin: \n{}-- LLVM IR end:\n",
                module.print_to_string().to_string()
            );
        }

        // inkwell provides no get_function by FunctionValue
        // so we will just pass around this FunctionValue
        // and call it ourselves

        let func = unsafe {
            self.codegen
                .execution_engine
                .get_function(&func_name)
                .expect("function name exists")
                .into_raw()
        };

        Ok((func, char))
    }
}

fn read_stack_from_ptr(start: *const u64, end: *const u64) -> Vec<u64> {
    let length = unsafe { end.offset_from(start) };
    if length < 0 {
        // stack must have underflowed...
        // not good but also not our problem anymore
        Vec::new()
    } else {
        let length = length as usize;
        let slice = unsafe { slice::from_raw_parts(start, length) };
        slice.to_vec()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn example() {
        assert_eq!(5, 5);
    }
}

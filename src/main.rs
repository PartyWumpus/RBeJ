#![allow(clippy::cast_possible_truncation, clippy::needless_raw_string_hashes)]
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction};
use inkwell::module::Module;
use inkwell::values::{AsValueRef, FunctionValue, IntValue, PointerValue};
use inkwell::{AddressSpace, OptimizationLevel};
use rand::distributions::{Alphanumeric, DistString};

mod program;

use crate::program::{BefungeProgram, Direction, Location};
use std::collections::HashMap;
use std::error::Error;

// TODO:
// impl last operators
// read from file
// figure out a good debug info system

const STACK_SIZE: usize = 100;

#[repr(C)]
#[derive(Debug, Clone, Copy)]
struct BefungeReturn(u64, u64, u64);

type BefungeFunc = unsafe extern "C" fn() -> *const BefungeReturn;

struct FunctionEffects {
    last_char: u8,
    func: BefungeFunc,
    state_after: BefungeState,
}

#[derive(Copy, Clone)]
struct BefungeState {
    location: Location,
    direction: Direction,
}

impl BefungeState {
    const fn new() -> Self {
        Self {
            location: Location(0, 0),
            direction: Direction::East,
        }
    }

    fn step(&mut self, program: &BefungeProgram) {
        self.location = program.step_with_wrap(self.direction, self.location);
    }
}

struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    execution_engine: ExecutionEngine<'ctx>,
}

/// GENERAL UTILITY
impl<'ctx> CodeGen<'ctx> {
    fn prelude(&self) {
        let i64_type = self.context.i64_type();
        let stack_type = i64_type.vec_type(STACK_SIZE as u32);
        let i64_type = self.context.i64_type();
        let status_type = self
            .context
            .struct_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);

        let zero = i64_type.const_int(0, false);
        let stack_zero = stack_type.const_zero();
        let status_zero = status_type.const_zero();

        let ptr = self.module.add_global(i64_type, None, "stack_counter");
        ptr.set_initializer(&zero);

        let stack = self.module.add_global(stack_type, None, "stack");
        stack.set_initializer(&stack_zero);

        let stack = self.module.add_global(status_type, None, "status");
        stack.set_initializer(&status_zero);

        let ptr = self.context.ptr_type(AddressSpace::default());

        let printf_type = self.context.i32_type().fn_type(&[ptr.into()], true);
        self.module.add_function("printf", printf_type, None);
    }

    fn printf_int(&self, int: IntValue) {
        let str = unsafe {
            self.builder
                .build_global_string("%d ", "int_str")
                .unwrap()
                .as_pointer_value()
        };

        let printf = self.module.get_function("printf").unwrap();

        self.builder
            .build_call(printf, &[str.into(), int.into()], "printy")
            .unwrap();
    }

    fn printf_char(&self, int: IntValue) {
        let str = unsafe {
            self.builder
                .build_global_string("%c ", "char_str")
                .unwrap()
                .as_pointer_value()
        };

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

    fn get_status_ptr(&self) -> PointerValue<'_> {
        self.module.get_global("status").unwrap().as_pointer_value()
    }

    fn increment_stack_counter(&self) {
        let i64_type = self.context.i64_type();
        let one = i64_type.const_int(1, false);

        let ptr = self.get_stack_counter_ptr();

        let stack_counter = self
            .builder
            .build_load(i64_type, ptr, "count")
            .unwrap()
            .into_int_value();

        let stack_counter = self
            .builder
            .build_int_add(stack_counter, one, "count")
            .unwrap();

        self.builder.build_store(ptr, stack_counter).unwrap();
    }

    fn decrement_stack_counter(&self) {
        let i64_type = self.context.i64_type();
        let minus_one = i64_type.const_int(u64::MAX, false); // ;)

        let ptr = self.get_stack_counter_ptr();

        let stack_counter = self
            .builder
            .build_load(i64_type, ptr, "count")
            .unwrap()
            .into_int_value();

        let stack_counter = self
            .builder
            .build_int_add(stack_counter, minus_one, "count")
            .unwrap();

        self.builder.build_store(ptr, stack_counter).unwrap();
    }

    fn peek_ptr(&self) -> PointerValue<'_> {
        let i64_type = self.context.i64_type();
        let stack_type = i64_type.vec_type(STACK_SIZE as u32);
        let zero = i64_type.const_zero();

        let stack_ptr = self.get_stack_ptr();
        let counter_ptr = self.get_stack_counter_ptr();
        let counter = self
            .builder
            .build_load(i64_type, counter_ptr, "count")
            .unwrap()
            .into_int_value();

        unsafe {
            self.builder
                .build_in_bounds_gep(stack_type, stack_ptr, &[zero, counter], "val")
                .unwrap()
        }
    }

    fn peek_stack(&self) -> IntValue<'_> {
        let i64_type = self.context.i64_type();
        let ptr = self.peek_ptr();

        let res = self
            .builder
            .build_load(i64_type, ptr, "stack_val")
            .unwrap()
            .into_int_value();

        res
    }

    fn pop_stack(&self) -> IntValue<'_> {
        let res = self.peek_stack();
        self.decrement_stack_counter();

        res
    }

    fn push_stack(&self, val: IntValue<'_>) {
        self.increment_stack_counter();
        let ptr = self.peek_ptr();

        self.builder.build_store(ptr, val).unwrap();
    }
}

/// OPERATIONS
impl<'ctx> CodeGen<'ctx> {
    // numbers

    fn push_static_number(&self, int: u64) {
        let i64_type = self.context.i64_type();
        let int = i64_type.const_int(u64::from(int), false);

        self.push_stack(int);
    }

    // normal operations

    fn addition(&self) {
        let a = self.pop_stack();
        let b = self.pop_stack();

        let res = self.builder.build_int_add(a, b, "add").unwrap();
        self.push_stack(res);
    }

    fn subtraction(&self) {
        let a = self.pop_stack();
        let b = self.pop_stack();

        let res = self.builder.build_int_sub(b, a, "sub").unwrap();
        self.push_stack(res);
    }

    fn multiplication(&self) {
        let a = self.pop_stack();
        let b = self.pop_stack();
        let res = self.builder.build_int_mul(b, a, "mult").unwrap();
        self.push_stack(res);
    }

    fn division(&self) {
        let a = self.pop_stack();
        let b = self.pop_stack();
        let res = self.builder.build_int_signed_div(b, a, "div").unwrap();
        self.push_stack(res);
    }

    fn modulo(&self) {
        let a = self.pop_stack();
        let b = self.pop_stack();
        // FIXME: check what to do on negative/zero b!!
        let res = self.builder.build_int_signed_rem(b, a, "modulo").unwrap();
        self.push_stack(res);
    }

    // if zero, set to 1, else set to zero
    fn not(&self, func: FunctionValue) {
        let a = self.pop_stack();
        let zero = self.context.i64_type().const_zero();

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
        self.push_static_number(1);
        self.builder.build_unconditional_branch(cont_block).unwrap();

        self.builder.position_at_end(not_zero_block);
        self.push_static_number(0);
        self.builder.build_unconditional_branch(cont_block).unwrap();

        self.builder.position_at_end(cont_block);
    }

    fn greater_than(&self, func: FunctionValue) {
        let a = self.pop_stack();
        let b = self.pop_stack();

        let cond = self
            .builder
            .build_int_compare(inkwell::IntPredicate::SGE, b, a, "isgreater")
            .unwrap();

        let greater_block = self.context.append_basic_block(func, "a_greater");
        let not_greater_block = self.context.append_basic_block(func, "a_not_greater");
        let cont_block = self.context.append_basic_block(func, "cont");

        self.builder
            .build_conditional_branch(cond, greater_block, not_greater_block)
            .unwrap();

        self.builder.position_at_end(greater_block);
        self.push_static_number(1);
        self.builder.build_unconditional_branch(cont_block).unwrap();

        self.builder.position_at_end(not_greater_block);
        self.push_static_number(0);
        self.builder.build_unconditional_branch(cont_block).unwrap();

        self.builder.position_at_end(cont_block);
    }

    fn duplicate(&self) {
        let a = self.peek_stack();
        self.push_stack(a);
    }

    fn swap(&self) {
        let a = self.pop_stack();
        let b = self.pop_stack();
        self.push_stack(a);
        self.push_stack(b);
    }

    fn pop_and_discard(&self) {
        self.pop_stack();
    }

    // return

    fn return_data(&self, vals: &[IntValue; 3]) {
        let ptr = self.get_status_ptr();
        let i64_type = self.context.i64_type();
        let status_type = self
            .context
            .struct_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);

        let status = status_type.const_zero();
        let status = self
            .builder
            .build_insert_value(status, vals[0], 0, "out")
            .unwrap();
        let status = self
            .builder
            .build_insert_value(status, vals[1], 1, "out")
            .unwrap();
        let status = self
            .builder
            .build_insert_value(status, vals[2], 2, "out")
            .unwrap();

        self.builder.build_store(ptr, status).unwrap();

        self.builder.build_return(Some(&ptr)).unwrap();
    }

    fn return_pop_three(&self) {
        let i64_type = self.context.i64_type();

        let y = self.pop_stack();
        let x = self.pop_stack();
        let v = self.pop_stack();

        let y = self.builder.build_int_z_extend(y, i64_type, "y").unwrap();
        let x = self.builder.build_int_z_extend(x, i64_type, "x").unwrap();
        let value = self.builder.build_int_z_extend(v, i64_type, "v").unwrap();

        self.return_data(&[x, y, value]);
    }

    fn return_pop_two(&self) {
        let i64_type = self.context.i64_type();
        let zero = i64_type.const_zero();

        let y = self.pop_stack();
        let x = self.pop_stack();

        let x = self.builder.build_int_z_extend(x, i64_type, "x").unwrap();
        let y = self.builder.build_int_z_extend(y, i64_type, "y").unwrap();

        self.return_data(&[x, y, zero]);
    }

    fn return_pop_one(&self) {
        let i64_type = self.context.i64_type();
        let zero = i64_type.const_zero();

        let x = self.pop_stack();

        let x = self.builder.build_int_z_extend(x, i64_type, "x").unwrap();

        self.return_data(&[x, zero, zero]);
    }

    fn return_zero(&self) {
        let zero = self.context.i64_type().const_zero();
        self.return_data(&[zero, zero, zero]);
    }
}

/// JIT TIME
impl<'ctx> CodeGen<'ctx> {
    fn jit_befunge(&self, mut program: BefungeProgram, init_state: Option<BefungeState>) {
        let mut cache_count = (0, 0);
        let mut state = init_state.map_or_else(BefungeState::new, |state| state);
        let mut cache: HashMap<(Location, Direction), FunctionEffects> = HashMap::new();
        loop {
            let func;
            let last_char;
            if let Some(cached_state) = cache.get(&(state.location, state.direction)) {
                func = cached_state.func.clone();
                last_char = cached_state.last_char;
                state = cached_state.state_after;
                cache_count.0 += 1;
            } else {
                println!("NO CACHEY");
                let pos = (state.location, state.direction);
                (func, last_char) = self.jit_one_expression(&program, &mut state);
                cache.insert(
                    pos,
                    FunctionEffects {
                        last_char,
                        func: func.clone(),
                        state_after: state,
                    },
                );
                cache_count.1 += 1;
            }
            //println!("{} cached vs {} uncached", cache_count.0, cache_count.1);
            let status = unsafe { *func() };
            //println!("status: {status:?}, char: '{}'", last_char as char);
            match last_char {
                b'@' => {
                    return;
                }
                b'?' => {
                    state.direction = rand::random();
                }
                b'_' => {
                    let status = status.0 as u64;
                    if status == 0 {
                        state.direction = Direction::East;
                    } else {
                        state.direction = Direction::West;
                    }
                    state.step(&program);
                }
                b'|' => {
                    let status = status.0 as u64;
                    if status == 0 {
                        state.direction = Direction::South;
                    } else {
                        state.direction = Direction::North;
                    }
                    state.step(&program);
                }
                b'p' => {
                    let y = status.0 as u64;
                    let x = status.1 as u64;
                    let value = status.2 as u64;

                    // TODO: invalidate cache here
                    //cache = HashMap::new();
                    program.set_if_valid(&Location(x as usize, y as usize), value);
                    state.step(&program);
                }
                b'g' => {
                    let y = status.0 as u64;
                    let x = status.1 as u64;

                    let val = program
                        .get(&Location(x as usize, y as usize))
                        .unwrap_or(b' '.into());
                    state.step(&program);

                    // TODO: figure out a less horrifying way to put the data back into the JIT's state
                    // use func args probably
                    let module = self.context.create_module("befunger");
                    self.execution_engine.add_module(&module).unwrap();
                    let fn_type = self.context.void_type().fn_type(&[], false);

                    // FIXME: safety last, chance of name collision is lowTM ;)
                    let func_name = Alphanumeric.sample_string(&mut rand::thread_rng(), 16);
                    let function = module.add_function(&func_name, fn_type, None);
                    let basic_block = self.context.append_basic_block(function, "entry");
                    self.builder.position_at_end(basic_block);

                    self.push_static_number(val);
                    self.builder.build_return(None).unwrap();
                    unsafe { self.execution_engine.run_function(function, &[]) };
                }
                _ => (),
            }
        }
    }

    fn jit_one_expression(
        &self,
        program: &BefungeProgram,
        state: &mut BefungeState,
    ) -> (BefungeFunc, u8) {
        let module = self.context.create_module("befunger");
        self.execution_engine.add_module(&module).unwrap();
        let ptr_type = self.context.ptr_type(AddressSpace::default());
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
                        self.push_static_number(char);
                    }
                }

                b'0'..=b'9' => self.push_static_number((char - b'0').into()),

                // normal operations
                b'+' => self.addition(),
                b'-' => self.subtraction(),
                b'*' => self.multiplication(),
                b'/' => self.division(),
                b'%' => self.modulo(),
                b'!' => self.not(function),
                b'`' => self.greater_than(function),
                b':' => self.duplicate(),
                b'\\' => self.swap(),
                b'$' => self.pop_and_discard(),

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
                    self.return_pop_one();
                    break;
                }

                // put (this is the big one!)
                b'p' => {
                    self.return_pop_three();
                    break;
                }

                // get
                b'g' => {
                    self.return_pop_two();
                    break;
                }

                // input
                b'&' => panic!("unimplemented &"),
                b'~' => panic!("unimplemented ~"),

                // output
                b'.' => self.printf_int(self.pop_stack()),
                b',' => self.printf_char(self.pop_stack()),

                // halt
                b'@' => {
                    self.return_zero();
                    break;
                }

                // noop
                b' ' => (),

                char => panic!("UNKNOWN FUNC :( {:?}", char as char),
            }
            state.step(program);
            // TODO: put a debug info here
            //self.printf_int(self.peek_stack());
        }

        //println!(
        //    "-- LLVM IR begin: \n{}-- LLVM IR end:\n",
        //    module.print_to_string().to_string()
        //);
        //panic!();

        //println!("{:?}", program);

        // inkwell provides no get_function by FunctionValue
        // so we will just pass around this FunctionValue
        // and call it ourselves
        //let x = function.as_value_ref();
        //unsafe { println!("{:?}", *x) };

        // this is slow as balls
        let func = unsafe {
            self.execution_engine
                .get_function(&func_name)
                .unwrap()
                .into_raw()
        };

        (func, char)
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
    codegen.prelude();
    println!(
        "-- LLVM IR PRELUDE begin: \n{}-- LLVM IR PRELUDE end:\n",
        codegen.module.print_to_string().to_string()
    );
    // https://github.com/Mikescher/BefungePrograms?tab=readme-ov-file
    let x = r##"
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
    let x = r##"
v     v.: <
>993**>1-:|
          @
      "##
    .chars()
    .skip(1)
    .collect::<String>();
    let x = r##"
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
    let program = BefungeProgram::new(&x);

    codegen.jit_befunge(program, None);

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

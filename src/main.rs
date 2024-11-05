use clap::Parser;
use inkwell::{context::Context, OptimizationLevel};
use rbej::{BefungeError, JitCompiler, JitConfig, Program};

fn to_opt_level(s: &str) -> Result<OptimizationLevel, String> {
    let opt_level: usize = s.parse().map_err(|_| format!("`{s}` isn't a number"))?;
    Ok(match opt_level {
        0 => OptimizationLevel::None,
        1 => OptimizationLevel::Less,
        2 => OptimizationLevel::Default,
        3 => OptimizationLevel::Aggressive,
        4.. => return Err("Opt level not in range 0-3".to_owned()),
    })
}

#[derive(Parser, Debug)]
#[command(about="RBeJ is an LLVM-based befunge JIT compiler", long_about = None)]
struct Args {
    /// File to compile
    filename: String,

    /// Optimization level, from 0-3
    #[arg(value_enum, long, short='O',short_alias='o', default_value = "2", value_parser=to_opt_level)]
    opt_level: OptimizationLevel,

    /// Print random debug information that is likely not useful
    #[arg(short, long, action = clap::ArgAction::Count)]
    verbose: u8,

    /// Outputs LLVM IR after each function is generated
    #[arg(short, long)]
    print_llvm_ir: bool,

    /// Disables the , and . operators
    #[arg(short, long)]
    silent: bool,
}

fn main() -> Result<(), BefungeError> {
    let args = Args::parse();
    if args.verbose >= 1 {
        println!("ARGS: {args:?}");
    }

    let str = std::fs::read_to_string(&args.filename).expect("Filename should exist");
    let program = Program::new(&str);

    let opts = JitConfig {
        opt_level: args.opt_level,
        print_llvm_ir: args.print_llvm_ir,
        silent: args.silent,
        verbose: args.verbose,
    };

    let context = Context::create();
    let mut jitter = JitCompiler::new(&context, program, opts)?;
    jitter.jit_to_completion()?;

    Ok(())
}

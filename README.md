# RBeJ (Rust-Befunge-Jit)
RBeJ is an LLVM-based JIT compiler for [befunge](https://esolangs.org/wiki/Befunge), a 2D programming language (designed with the goal of "being as difficult to compile as possible").

Aside from being 2D, the language has a 'put' operation that can edit the grid of instructions. This makes it difficult to write a traditional optimizing compiler, as you need to have some sort of interpreter around at runtime to understand what to do with any new instructions.

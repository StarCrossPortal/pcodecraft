# Pcode Craft

Pcode craft is tend to be the API abstraction over the ghidra decompiler in the Rust world.

## Explain

[BinCraft](https://github.com/StarCrossPortal/bincraft) is dedicated to provide binary analysis infrastructure with the help of [Ghidra](https://github.com/NationalSecurityAgency/ghidra).

However, this is not the actual usecase for original ghidra decompiler.

Thus, this API is what we need to make everything universal.

The design of the API is:

- Provide anything that ghidra decompiler objects could do in the traits.
- But, do not enforce the backend implementation.

This is our first step towards "LLVM-like decompiler implementation".
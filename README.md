# macros2
A runtime macro system for Nim with FFI support for exporting and importing macros across dynamic libraries.
This project is a fork of [`elcritch/cdecl`](https://github.com/elcritch/cdecl/tree/main/src/cdecl/compiler) — all credit for the original design and implementation goes to @elcritch.
## What is macros2?
`macros2` provides a `NimNode` type that can be used at **runtime** instead of just at compile-time. This enables runtime macro evaluation, macro FFI across shared library boundaries, and runtime macro caching.

## Limitations
> [!WARNING]  
> `macros2.NimNode` cannot be used in compile-time macros.

* For compile-time macros, you **must** use system.NimNode
* While `macros2` includes utilities to convert between `macros2.NimNode` and `system.NimNode`, these conversions use `cast` and **cannot be used at compile-time** as `cast` is disabled in Nim's VM
* *You cannot mix compile-time and runtime NimNode types- choose one or the other for your use case*

# Key Features
## Core Runtime Macro System
`macros2` provides a complete runtime macro system with utility functions and runtime macro caching support. The original `cdecl` implementation has been fixed to support the latest Nim compiler and optimized for faster compilation by removing unused imports.
## Macro FFI
Export and import macros across dynamic library boundaries using `exportMacro` and `importMacro`:
### Exporting a macro:
```nim
import macros2/ffi

proc myProtectedMacro(b: NimNode, n: NimNode): NimNode =
  result = nnkStmtList.newTree(b, n)

exportMacro myProtectedMacro
```
The `exportMacro` macro generates an FFI wrapper that:

1. Creates a new proc `myProtectedMacroFFI` with `{.exportc, dynlib.}` pragmas
2. Accepts `cstring` parameters for each original `NimNode` parameter
3. Converts each `cstring` parameter back to `NimNode` using `parseStmt`
4. Calls the original proc with the converted nodes
5. Returns the result as a `cstring` via `.repr`

### Importing a macro:
```nim
import macros2/ffi

importMacro myProtectedMacro, (b, n)

# Use it like a normal macro!
myProtectedMacro:
  echo "Hello"
  echo "World"
```
The `importMacro` macro generates:

1. A proc declaration with `{.importc, dynlib.}` to link to the exported FFI wrapper
2. A macro wrapper that takes `untyped` parameters
3. Converts each parameter to `cstring` via `.repr`
4. Calls the imported proc with these string representations
5. Parses the returned `cstring` back into a `NimNode` using `parseStmt`

This creates a seamless bridge where AST nodes are serialized to strings at the boundary, transmitted across the dynamic library interface, and reconstructed on the other side.

# Motivation
The macro FFI system addresses two key use cases:
## A. Source Code Protection
Distribute macro implementations as compiled libraries without exposing the source code. This allows proprietary macro logic to be shipped while maintaining the same API surface as source-distributed macros.
## B. Macro Bootstrapping
Build self-extensible macro systems where macros can generate, transform, and compose other macros across compilation boundaries. This enables incremental development of sophisticated metaprogramming frameworks — foundational macros in one library can be used to construct higher-level abstractions in dependent libraries, with each layer building upon the runtime capabilities of the previous. The result is a composable macro ecosystem where complex transformations emerge from simpler, reusable primitives.
# Release 3.15, 2024-12-13

C language support:
- Minimal syntactic support for `_Float16` type (half-precision FP numbers).  Function declarations using `_Float16` are correctly parsed, but any actual use of `_Float16` is rejected later during compilation. (#525)
- Support C99 array declarator syntax involving `static` and `*`. These annotations are correctly parsed, but ignored during typing and compilation. (#539)

Code generation and optimization:
- Better support for `_Bool` type in the back-end and in the memory model.
  This avoids redundant normalizations to `_Bool`.
- Take types of function parameters into account during value analysis.
  This avoids redundant normalizations on parameters of small integer types.
- More conservative static analysis of pointer comparisons. (#516)
- Refined heuristic for if-conversion. Turn if-conversion off in some cases where it would prevent later optimization of conditional branches in the continuation of the `if`.
- CSE: remember pointer alias information in `Load` equations, making it possible to remove more redundant memory loads. (#518)
- More precise value analysis of integer multiplication, division, modulus.
- Constant propagation: optimize "known integer or undefined" results.  For example, `&x == &x`, which is either 1 or undefined, is now replaced by 1.
- Optimize `(x ^ cst) != 0` into `x != cst`.
- Avoid quadratic compile-time behavior on deeply-nested `if` statements. (#519)

Bug fixes:
- More robust determination of symbols that may be defined in a shared object. (#538)
- Escape `$NNN` identifiers in generated x86 and ARM assembly code (#541).
- Wrong parameter scoping in function definitions such as `int (*f(int y))(int x) { ... }` (a function returning a pointer to a prototyped function).

Usability:
- Mark stack as non-executable in binaries produced by `ccomp`.
- Check that preprocessed sources (`.i` files) do not contain backslash-newline sequences.
- `./configure arm-linux` now selects the hard-FP ABI, since Linux distributions no longer use the soft-FP ABI.

Supporting libraries:
- ARM library for 64-bit integer arithmetic: faster division, cleaned-up code.

Coq development:
- Support Coq 8.20.
- Build: support TIMING and PROFILING like `coq_makefile`. (#512)
- Make dependency on `Extraction` explicit. (#515)
- Install `.glob` and `.v` files along `.vo` files. (#527)


# Release 3.14, 2024-05-02

ISO C conformance:
- `free` has well-defined semantics on blocks of size 0 (#509).

Code generation and optimization:
- More simplifications of comparison operations and selection operations during the CSE pass.
- Replace selection operations with moves if both branches are equal.
- ARM 32 bits: several minor improvements to the generated code (#503 and more).

Bug fixes:
- x86 under Windows: the wrong `sub` instruction was generated for `Pallocframe`.
- ARM: fix PC displacement overflow involving floating-point constants.
- ARM: fix error on printing of "s17" register.
- RISC-V: do not use 64-bit FP registers for `memcpy` if option `-fno-fpu` is given.

Usability:
- Added generation of CFI debugging directives for AArch64 and RISC-V.
- Removed the command-line option `-fstruct-return`, deprecated since release 2.6.

Formal semantics:
- The big-step semantics for Clight now supports the two models for function arguments (either as stack-allocated variables or as register-like temporaries).

Coq development:
- Support Coq 8.17, 8.18, and 8.19.
- Revised most uses of the `intuition` tactic (#496 and more).
- Address most other deprecation warnings from Coq 8.18 and 8.19.
- Updated local copy of MenhirLib to version 20231231.
- Updated local copy of Flocq to version 4.1.4.

Distribution:
- The small test suite was moved to a separate Git repository.
  Use `git submodule init && git submodule update` to download it.


# Release 3.13, 2023-07-04

Code generation and optimization:
- Slightly more precise value analysis, with a better distinction
  between "any integer value" and "any integer or pointer value". (#490)
- Recognize a few more nested conditional expressions that can be
  if-converted into a conditional move.
- Register allocation: better support for "preferred" registers,
  e.g. registers R0-R3 on ARM Thumb, which enable more compact
  instruction encodings.
- ARM Thumb: use more instructions that can be encoded in 16 bits, producing
  more compact code.
- x86: use a shorter instruction encoding for loading unsigned 32-bit
  constants. (#487)

Bug fixes:
- `_Noreturn` on function definitions (but not declarations) was
  ignored sometimes.
- The argument of `__builtin_va_end` was discarded, is now evaluated
  for its side effects.
- Tail call optimization must be disabled in variadic functions,
  otherwise a `va_list` structure can get out of scope.
- Nested compound initializers were elaborated in the wrong order,
  causing compile-time failures later in the compilation pipeline.
- The signedness of a bit field was determined differently when its
  type was an enum type and when it was a typedef to an enum type.

ABI conformance:
- Define `wchar_t` exactly like the ABI says.  On most platforms,
  CompCert was defining `wchar_t` as `signed int`, but it must be
  `unsigned int` for AArch64-ELF and `unsigned long` for PowerPC-EABI.

Supported platforms:
- Removed support for Cygwin 32 bits, which has reached end of life.
  Cygwin 64 bits remains supported.

Coq development:
- Support Coq 8.16.0 and 8.16.1, addressing most of the new warnings in 8.16.
- When installing the Coq development, also install coq-native generated files.
- Tweak some proof scripts for compatibility with future Coq versions.
  (#465, #470, #491, #492)
- Updated the vendored copy of Flocq to version 4.1.1.


# Release 3.12, 2022-11-25

New features:
- Support unstructured `switch` statements such as Duff's device.
  This is achieved via an optional, unverified code rewrite,
  activated by option `-funstructured-switch`. (#459)
- Support C11 Unicode string literals and character constants,
  such as `u8"été"` or `u32'❎'`.

Usability:
- Support the `-std=c99`, `-std=c11` and `-std=c18` option.
  These options are passed to the preprocessor, helping it select the
  correct version of the standard header files.  It also controls
  CompCert's warning for uses of C11 features. (#456)
- The source character set of CompCert is now officially Unicode
  with UTF-8 encoding,  A new warning `invalid-utf8` is triggered if byte
  sequences that are not valid UTF-8 are found outside of comments.
  Other source character sets and stricter validation can be supported
  via the `-finput-charset` option, see next.
- If the GNU preprocessor is used, the source character set can be
  selected with the `-finput-charset=` option.  In particular,
  `-finput-charset=utf8` checks that the source file is correctly
  UTF-8 encoded, and `-finput-charset=ascii` that it contains no
  Unicode characters at all.
- Support mergeable sections for string literals and for numerical constants.
- AArch64, ARM, RISC-V and x86 ELF targets: use `.data.rel.ro` section
  for `const` data whose initializers contain relocatable addresses.
  This is required by the LLVM linker and simplifies the work of the GNU linker.
- `configure` script: add option `-sharedir` to specify where to put
  the `compcert.ini` configuration file (#450, #460)
- ARM 32 bits: emit appropriate `Tag_ABI_VFP` attribute (#461)

Optimizations:
- Recognize more `if`-`else` statements that can be if-converted into
  a conditional move.  In particular, debug statements generated in
  `-g` mode no longer prevent this conversion.

Bug fixes:
- Revised simplification of nested conditional, `||`, `&&` expressions
  to make sure the generated Clight code is well typed and is not rejected
  later by `ccomp` (#458).
- In `-g` mode, when running under Windows, the `ccomp` executable could
  fail on an uncaught exception while inserting lines of the source C file
  as comments in the generated assembly file.
- Reintroduced DWARF debug information for bit fields in structs
  (it was missing since 3.10).

Coq development:
- RTLgen: use the state and error monad for reserving `goto` labels (#371)
  (by Pierre Nigron)
- Add `Declare Scope` statements where appropriate, and re-enable the
  `undeclared-scope` warning.


# Release 3.11, 2022-06-27

New features:
- Support `_Generic` expressions from ISO C11.

ISO C conformance:
- Enumeration types are compatible only with `int` but not with
  other integer types.
- Fixed confusion between unprototyped function pointer types `T (*)()` and
  prototyped, zero-argument function pointer types `T (*)(void)`
  in type casts (#431).

Usability:
- Improved control-flow analysis of calls to "noreturn" functions,
  resulting in more accurate warnings.
- More detailed warning for unprototyped function definitions, now shows
  the prototyped type that is given to the function.
- Extended the warning above to definitions of the form `T f() { ... }`,
  i.e. unprototyped but with no parameters.  (Before, the warning would
  trigger only if parameters were declared.)
- Check (and warn if requested) for arguments of struct/union types passed
  to a variable-argument function.

Bug fixes:
- RISC-V: fixed an error in the modeling of float32 <-> float64 conversions
  when the argument is a NaN (#428).
- x86: changed the compilation of `__builtin_fmin` and `__builtin_fmax`
  so that their NaN behavior is the one documented in the manual.
- Improved reproducibility of register allocation.
  (Before, compiling CompCert with two different OCaml versions could
   have resulted in correct but different allocations.)
- Hardened the configure script against Cygwin installations that produce
  `\r\n` for end-of-lines (#434).
- RISC-V: tail calls to far-away functions were causing link-time errors
  (#436, #437).

Coq development:
- Updated the Flocq library to version 4.1.
- Support for Coq 8.14.1, 8.15.0, 8.15.1, 8.15.2.
- Minimal Coq version supported is now 8.12.0.


# Release 3.10, 2021-11-19

Major improvement:
- Bit fields in structs and unions are now handled in the
  formally-verified part of CompCert. (Before, they were being
  implemented through an unverified source-to-source translation.)
  The CompCert C and Clight languages provide abstract syntax for
  bit-field declarations and formal semantics for bit-field accesses.
  The translation of bit-field accesses to bit manipulations is
  performed in the Cshmgen pass and proved correct.

Usability:
- The layout of bit-fields in memory now follows the ELF ABI
  algorithm, improving ABI compatibility for the CompCert target
  platforms that use ELF.
- Handle the `# 0` line directive generated by some C preprocessors (#398).
- Un-define the `__SIZEOF_INT128__` macro that is predefined by some C
  preprocessors (#419).
- macOS assembler: use `##` instead of `#` to delimit comments (#399).

ISO C conformance:
- Stricter checking of multi-character constants `'abc'`.
  Multi-wide-character constants `L'ab'` are now rejected,
  like GCC and Clang do.
- Ignore (but still warn about) unnamed plain members of structs
  and unions (#411).
- Ignore unnamed bit fields when initializing unions.

Bug fixing:
- x86 64 bits: overflow in offset of `leaq` instructions (#407).
- AArch64, ARM, PowerPC, RISC-V: wrong expansion of `__builtin_memcpy_aligned`
  in cases involving arguments that are stack addresses (#410, #412)
- PowerPC 64 bits: wrong selection of 64-bit rotate-and-mask
  instructions (`rldic`, `rldicl`, `rldicr`), resulting in assertion
  failures later in the compiler.
- RISC-V: update the Asm semantics to reflect the fact that
  register X1 is destroyed by some builtins.

Compiler internals:
- The "PTree" data structure (binary tries) was reimplemented, using
  a canonical representation that guarantees extensionality and
  improves performance.
- Add the ability to give formal semantics to numerical builtins
  with small integer return types.
- PowerPC: share code for memory accesses between Asmgen and Asmexpand
- Declare `__compcert_i64*` helper runtime functions during the C2C
  pass, so that they are not visible during source elaboration.

The clightgen tool:
- Add support for producing Csyntax abstract syntax instead of Clight
  abstract syntax (option `-csyntax` to `clightgen`)
  (contributed by Bart Jacobs; #404, #413).

Coq development:
- Added support for Coq 8.14 (#415).
- Added support for OCaml 4.13.
- Updated the Flocq library to version 3.4.2.
- Replaced `Global Set Asymmetric Patterns` by more local settings (#408).


# Release 3.9, 2021-05-10

New features:
- New port: AArch64 (ARM 64 bits, "Apple silicon") under macOS.
- Support bitfields of types other than `int`, provided they are no larger
  than 32 bits (#387)
- Support `__builtin_unreachable` and `__builtin_expect` (#394)
  (but these builtins are not used for optimization yet)

Optimizations:
- Improved branch tunneling: optimized conditional branches can
  introduce further opportunities for tunneling, which are now taken
  into account.

Usability:
- Pragmas within functions are now ignored (with a warning) instead of
  being lifted just before the function like in earlier versions.
- configure script: add `-mandir` option (#382)

Compiler internals:
- Finer control of variable initialization in sections.  Now we can
  put variables initialized with symbol addresses that need relocation
  in specific sections (e.g. `const_data` on macOS).
- Support re-normalization of function parameters at function entry,
  as required by the AArch64/ELF ABI.
- PowerPC 64 bits: remove `Pfcfi`, `Pfcfiu`, `Pfctiu` pseudo-instructions,
  expanding the corresponding int<->FP conversions during the
  selection pass instead.

Bug fixing:
- PowerPC 64 bits: incorrect `ld` and `std` instructions were generated
  and rejected by the assembler.
- PowerPC: some variadic functions had the wrong position for their
  first variadic parameter.
- RISC-V: fix calling convention in the case of floating-point
  arguments that are passed in integer registers.
- AArch64: the default function alignment was incorrect, causing a
  warning from the LLVM assembler.
- Pick the correct archiver to build `.a` library archives (#380).
- x86 32 bits: make sure functions returning structs and unions
  return the correct pointer in register EAX (#377).
- PowerPC, ARM, AArch64: updated the registers destroyed by asm
  pseudo-instructions and built-in functions.
- Remove spurious error on initialization of a local struct
  containing a flexible array member.
- Fixed bug in emulation of assignment to a volatile bit-field (#395).

The clightgen tool:
- Move the `$` notation for Clight identifiers to scope `clight_scope`
  and submodule `ClightNotations`, to avoid clashes with Ltac2's use of `$`
  (#392).

Coq development:
- Compatibility with Coq 8.12.2, 8.13.0, 8.13.1, 8.13.2.
- Compatibility with Menhir 20210419 and up.
- Oldest Coq version supported is now 8.9.0.
- Use the `lia` tactic instead of `omega`.
- Updated the Flocq library to version 3.4.0.

Licensing and distribution:
- Dual-licensed source files are now distributed under the LGPL version 2.1
  (plus the Inria non-commercial license) instead of the GPL version 2
  (plus the Inria non-commercial license).


# Release 3.8, 2020-11-16

New features:
- Support `_Static_assert` from ISO C11.
- Support `__builtin_constant_p` from GCC and Clang.
- New port: x86 64 bits Windows with the Cygwin 64 environment.
  (configure with target `x86_64-cygwin`).
- The following built-in functions are now available for all ports:
  `__builtin_sqrt`, `__builtin_fabsf`, and all variants of
  `__builtin_clz` and `__builtin_ctz`.
- Added `__builtin_fmin` and `__builtin_fmax` for AArch64.

Removed features:
- The x86 32 bits port is no longer supported under macOS.

Compiler internals:
- Simpler translation of CompCert C casts used for their effects but
  not for their values.
- Known builtins whose results are unused are eliminated earlier.
- Improved error reporting for `++` and `--` applied to pointers to
  incomplete types.
- Improved error reporting for redefinitions and implicit definitions
  of built-in functions.
- Added formal semantics for some PowerPC built-ins.

The clightgen tool:
- New `-canonical-idents` mode, selected by default, to change the way
  C identifiers are encoded as CompCert idents (positive numbers).
  In `-canonical-idents` mode, a fixed one-to-one encoding is used
  so that the same identifier occurring in different compilation units
  encodes to the same number.
- The `-short-idents` flag restores the previous encoding where
  C identifiers are consecutively numbered in order of appearance,
  causing the same identifier to have different numbers in different
  compilation units.
- Removed the automatic translation of annotation builtins to Coq
  logical assertions, which was never used and possibly confusing.

Coq and OCaml development:
- Compatibility with Coq 8.12.1, 8.12.0, 8.11.2, 8.11.1.
- Can use already-installed Flocq and MenhirLib libraries instead of their
  local copies (options `-use-external-Flocq` and `-use-external-MenhirLib`
  to the `configure` script).
- Automatically build to OCaml bytecode on platforms where OCaml
  native-code compilation is not available.
- Install the `compcert.config` summary of configuration choices
  in the same directory as the Coq development.
- Updated the list of dual-licensed source files.


# Release 3.7, 2020-03-31

ISO C conformance:
- Functions declared `extern` then implemented `inline` remain `extern`
- The type of a wide char constant is `wchar_t`, not `int`
- Support vertical tabs and treat them as whitespace
- Define the semantics of `free(NULL)`

Bug fixing:
- Take sign into account for conversions from 32-bit integers to 64-bit pointers
- PowerPC: more precise determination of small data accesses
- AArch64: when addressing global variables, check for correct alignment
- PowerPC, ARM: double rounding error in int64->float32 conversions

ABI conformance:
- x86, AArch64: re-normalize values of small integer types returned by
  function calls
- PowerPC: `float` arguments passed on stack are passed in 64-bit format
- RISC-V: use the new ELF psABI instead of the old ABI from ISA 2.1

Usability and diagnostics:
- Unknown builtin functions trigger a specific error message
- Improved error messages

Coq formalization:
- Revised modeling of the PowerPC/EREF `isel` instruction
- Weaker `ec_readonly` condition over external calls
  (permissions can be dropped on read-only locations)

Coq and OCaml development:
- Compatibility with Coq version 8.10.1, 8.10.2, 8.11.0
- Compatibility with OCaml 4.10 and up
- Compatibility with Menhir 20200123 and up
- Coq versions prior to 8.8.0 are no longer supported
- OCaml versions prior to 4.05.0 are no longer supported


# Release 3.6, 2019-09-17

New features and optimizations:
- New port targeting the AArch64 architecture: ARMv8 in 64-bit mode.
- New optimization: if-conversion.  Some `if`/`else` statements
  and `a ? b : c` conditional expressions are compiled to branchless
  conditional move instructions, when supported by the target processor
- New optimization flag: `-Obranchless`, to favor the generation of
  branchless instruction sequences, even if probably slower than branches.
- Built-in functions can now be given a formal semantics within
  CompCert, instead of being treated as I/O interactions.
  Currently, `__builtin_fsqrt` and `__builtin_bswap*` have semantics.
- Extend constant propagation and CSE optimizations to built-in
  functions that have known semantics.
- New "polymorphic" built-in function: `__builtin_sel(a,b,c)`.
  Similar to `a ? b : c` but `b` and `c` are always evaluated,
  and a branchless conditional move instruction is produced if possible.
- x86 64 bits: faster, branchless instruction sequences are produced
  for conversions between `double` and `unsigned int`.
- `__builtin_bswap64` is now available for all platforms.

Usability and diagnostics:
- Improved the DWARF debug information generated in `-g` mode.
- Added options `-fcommon` and `-fno-common` to control the generation
  of "common" declarations for uninitialized global.
- Check for reserved keywords `_Complex` and `_Imaginary`.
- Reject function declarations with multiple `void` parameters.
- Define macros `__COMPCERT_MAJOR__`, `__COMPCERT_MINOR__`, and
  `__COMPCERT_VERSION__` with CompCert's version number. (#284)
- Prepend `$(DESTDIR)` to the installation target. (#169)
- Extended inline asm: print register names according to the
  types of the corresponding arguments (e.g. for x86_64,
  `%eax` if int and `%rax` if long).

Bug fixing:
- Introduce distinct scopes for iteration and selection statements,
  as required by ISO C99.
- Handle dependencies in sequences of declarations
  (e.g. `int * x, sz = sizeof(x);`).  (#267)
- Corrected the check for overflow in integer literals.
- On x86, `__builtin_fma` was producing wrong code in some cases.
- `float` arguments to `__builtin_annot` and `__builtin_ais_annot`
  were uselessly promoted to type `double`.

Coq formalization and development:
- Improved C parser based on Menhir version 20190626:
  fewer run-time checks, faster validation, no axioms. (#276)
- Compatibility with Coq versions 8.9.1 and 8.10.0.
- Compatibility with OCaml versions 4.08.0 and 4.08.1.
- Updated to Flocq version 3.1.
- Revised the construction of NaN payloads in processor descriptions
  so as to accommodate FMA.
- Removed some definitions and lemmas from lib/Coqlib.v, using Coq's
  standard library instead.

The clightgen tool:
- Fix normalization of Clight `switch` statements. (#285)
- Add more tracing options: `-dprepro`, `-dall`. (#298)
- Fix the output of `-dclight`. (#314)


# Release 3.5, 2019-02-27

Bug fixing:
- Modeling error in PowerPC ISA: how register 0 is interpreted when
  used as base register for indexed load/stores.  The code generated
  by CompCert was correct, but was proved correct against the wrong
  specification.
- Modeling error in x86 ISA: how flag ZF is set by floating-point
  comparisons.  Here as well, the code generated by CompCert was
  correct, but was proved correct against the wrong specification.
- Revised handling of attributes so that they behave more like in
  GCC and Clang.  CompCert now distinguishes between attributes that
  attach to names (variables, fields, typedefs, structs and unions)
  and attributes that attach to objects (variables).  In particular,
  the `aligned(N)` attribute now attaches to names, while the `_Alignas(N)`
   modifier still attaches to objects.  This fixes issue 256.
- Issue with NULL as argument to a variadic function on 64-bit platforms
  (issue 265)
- Macro `__bool_true_false_are_defined` was missing from `<stdbool.h>`
  (issue 266)

Coq development:
- Can now be entirely rechecked using coqchk
  (contributed by Vincent Laporte)
- Support Coq version 8.9.0
- Avoid using "refine mode" when defining Instance
  (contributed by Maxime Dénès)
- Do not support Menhir versions more recent than 20181113, because
  they will introduce an incompatibility with this CompCert release.

New feature:
- PowerPC port: add `__builtin_isel` (conditional move) at types
  `int64`, `uint64`, and `_Bool`.


# Release 3.4, 2018-09-17

Bug fixing:
- Redefinition of a typedef in a different scope was wrongly rejected.
- Attach `_Alignas(N)` and `__attribute((aligned(N)))` to names
  instead of types, so that `_Alignas(16) int * p` means
  "16-aligned pointer to int", not "pointer to 16-aligned int".
- For packed structs, fix a discrepancy between the size and alignment
  computed during elaboration and those computed by the verified front-end
  after expansion.
- Honor qualified array types in function parameters: if a parameter is
  declared as e.g. `int t[const 4]`, it is now treated as `int * const t`
  in the function body, not `int * t` like before.
- Reject `__builtin_offsetof(struct s, f)` if `f` is a bit-field.
- Wrong parsing of attributes having multiple arguments such as
  `__attribute((packed(A,B,C)))`.
- If `__builtin_ais_annot` is followed immediately by a label (e.g. a
  loop head), add a nop instruction to separate the annotation from
  the label.
- Wrong parsing of the command-line options `-u <symbol>` and `-iquote`.
- PowerPC in hybrid 32/64 bit mode: reject %Q and %R register specifications
  in inline assembly code, since 64-bit integer arguments are not split
  in two registers.
- x86 64-bit mode: wrong expansion of `__builtin_clzl` and `builtin_ctzl`
  (issue #127).

New checks for ISO C conformance:
- Removed support for `_Alignof(expr)`, which is not C11;
  only `_Alignof(ty)` is part of C11.
- Reject occurrences of `_Alignas` in places that are not allowed by C11,
  e.g. in `typedef`.  `__attribute((aligned(N)))` can be used instead.
- Reject occurrences of `restrict` in places that are not allowed by
  C99 and C11.
- Reject structs composed of a single flexible array `struct { ty []; }`.
- Check that qualified array types such as `int t[const 4]` occur only
  as function parameters, but nowhere else.
- In function definitions, reject function parameters that have no names.

New warnings:
- Warn for flexible array types `ty[]` in places where they do not make sense.
- Warn for inline (not static inline) functions that declare
  non-constant static variables.
- Optionally warn if the alignment of an object is reduced below its
  natural alignment because of a _Alignas qualifier or an aligned attribute,
  or a packed attribute.
- Warn for tentative static definitions with an incomplete type, e.g.
  `static int x[];`.
- The warning about uses of C11 features is now off by default.

Semantic preservation proof:
- Model the fact that external functions can destroy caller-save registers
  and Outgoing stack slots; adapt the proofs accordingly.

Coq and OCaml development:
- Support Coq versions 8.8.1 and 8.8.2.
- Support OCaml versions 4.7.0 and up.
- Support Menhir versions 20180530 and up.

Others:
- Improved error handling in "configure" script (issue #244)
- clightgen adds configuration information to the generated .v file (issue #226)


# Release 3.3, 2018-05-30

New features:
- Introduced the `__builtin_ais_annot` built-in function to communicate
  source-level annotations to AbsInt's a3 tool suite via a special
  section in object and executable files.
- Improved C11 support: define the C11 conditional feature macros;
  define the `max_align_t` type in stddef.h.
- PowerPC 64-bit port: new built-in functions for 64-bit load-store with
  byte reversal and for 64-bit integer multiply high.
- x86 64 bits: add support for BSD.

Bug fixing:
- Wrong code generated for unions containing several bit fields.
- Internal compiler errors for some initializers for structs and
  unions containing bit-fields, and for anonymous members of unions.
- Missing error reporting for `<integer> - <ptr>` subtraction,
  causing an internal retyping error later during compilation.
- String literals are l-values.
- String literals have array types, not pointer types.
- Array sizes >= 2^32 were handled incorrectly on 64-bit platforms.
- Wrong code generated for global variables of size 2^31 bytes or more.
- struct and union arguments to annotation builtins must be passed by
  reference, regardless of the ABI calling conventions.
- `e1, e2` has pointer type if `e2` has array type.
- x86 64 bits: in "symbol + ofs" addressing modes, the offset "ofs"
  must be limited to [-2^24, 2^24) otherwise linking can fail.

New or improved diagnostics (errors and warnings):
- Warn for comparison of a pointer to a complete type and a pointer to
  an incomplete type.
- More checks on variables declared in `for` loops: not static, not
  extern, not function types.
- Reject empty declarations in K&R functions.
- Reject arrays of incomplete types.
- Reject duplicate `case` or `default` statements within a `switch`.
- Reject `case` and `default` statements outside a `switch`.
- Check that `typedef` declares a name and doesn't contain `_Noreturn`.
- Function parameters are in the same scope as function local variables.
- More comprehensive constant-ness checks for initializers of global
  or static local variables.
- Make sure an enum cannot have the same tag as a struct or an union.
- More checks on where the `auto` storage class can be used.
- Accept empty enum declaration after nonempty enum definition.
- Reject pointers to incomplete types in ptr - ptr subtraction.
- When defining a function, take attributes (_Noreturn, etc) from
  earlier declarations of the function into account.
- Better check for multiple definitions of functions or global variables.
- Reject illegal initializations of aggregates such as `char c[4] = 42;`.
- Reject designated initializers where a member of a composite type is
  re-initialized after the composite has been initialized as a whole.
- Reject casts to struct/union types.
- Reject sizeof(e) where e designates a bit-field member of a struct or union.
- `e1, e2` is not a compile-time constant expression even if `e1` and `e2` are.
- `main` function must not be `inline`
- Warn for functions declared extern after having been defined.
- Warn for function declarations after function definitions when the
  declaration has more attributes than the definition.
- Warn for assignment of a volatile struct to a non-volatile struct.
- Warn for `main` function if declared `_Noreturn`.

Coq development:
- Added support for Coq versions 8.7.2 and 8.8.0.
- Rewrote `Implicit Arguments` and `Require` inside sections,
  these are obsolete in 8.8.0.
- Upgraded Flocq to version 2.6.1.
- Optionally install the .vo files for reuse by other projects
  (options `-install-coqdev` and `-coqdevdir` to configure script;
   automatically selected if option `-clightgen` is given).


# Release 3.2, 2018-01-15

Code generation and optimization:
- Inline static functions that are called only once.
  Can be turned off by setting the `noinline` attribute on the function.
- More consistent detection and elimination of divisions by 1.
- ARM in Thumb mode: simpler instruction sequence for branch through jump table.
- ARM: support and use the `cmn` instruction.
- Issue #208: make value analysis of comparisons more conservative for
  dubious comparisons such as `(uintptr_t) &global == 0x1234` which are
  undefined behavior in CompCert.

Usability:
- Resurrected support for the Cygwin x86-32 port, which got lost at release 3.0.
- Support the `noinline` attribute on C function definitions.
- PowerPC port with Diab toolchain: support `-t <target processor>` option
  and pass it to the Diab tools.
- Clightgen tool: add `-o` option to specify output file.
- Pull request #192: improve the printing of Clight intermediate code
  so that it looks more like valid C source.  (Frédéric Besson)

Bug fixing:
- Issue #P25: make sure `sizeof(long double) = sizeof(double)` in all contexts.
- Issue #211: wrong scoping for C99 declarations within a `for` statement.

Coq and Caml development:
- Pull request `#191`: Support Coq version 8.7.0 and 8.7.1 in addition
  to Coq 8.6.1.  Coq 8.6 (.0) is no longer supported owing to an
  incompatibility with 8.7.0.
  (Sigurd Schneider)
- ARM code generator: refactoring of constant expansions and EABI fixups.
- Resynchronized the list of dual-licensed files given in file LICENSE
  and the copyright headers of the dual-licensed files.


# Release 3.1, 2017-08-18

Major improvements:

- New port targeting the RISC-V architecture, in 32- and 64-bit modes.

- Improved support for PowerPC 64 processors: use 64-bit registers and
  instructions for 64-bit integer arithmetic.  Pointers remain 32 bits
  and the 32-bit ABI is still used.

Code generation and optimization:

- Optimize leaf functions in the PowerPC back-end.
  (Avoid reloading the return address from the stack.)
- Avoid generating useless conditional branches for empty if/else statements.
- Earlier elimination of redundant `&*expr` and `*&expr` addressings.
- Improve utilization of addressing modes for volatile loads and stores.

Usability:

- Add options `-finline` / `-fno-inline` to control function inlining.
- Removed the compilation of `.cm` files written in Cminor concrete syntax.
- More precise warnings about missing function returns.
- clightgen: add option `-normalize` to avoid memory loads deep inside
  expressions.

Bug fixing:

- Issue #179: clightgen produces wrong output for `switch` statements.
- Issue #196: excessive proof times in .v files produced by clightgen.
- Do not generate code for functions with `inline` specifier that are
  neither static nor extern, as per ISO C99.
- Some line number information was missing for some goto labels and
  switch cases.
- Issue #P16: illegal PowerPC asm generated for unsigned division after
  constant propagation.
- Issue #P18: ARM addressing overflows caused by 1- underestimation of
  code size, causing mismanagement of constant pool, and 2- large stack
  frames where return address and back link are at offsets >= 4Kb.
- Pass `-no-pie` flag to the x86 linker when `-pie` is the default.

Coq and Caml development:

- Support Coq 8.6.1.
- Improve compatibility with Coq working version.
- Always generate `.merlin` and `_CoqProject` files.


# Release 3.0.1, 2017-02-14

- Ported to Coq 8.6.


# Release 3.0, 2017-02-10

Major improvements:

- Added support for 64-bit target platforms, including pointers that
  are 64-bit wide, and the ability to use 64-bit integer registers and
  arithmetic operations.  This support does not replace but comes in
  addition to CompCert's original support for 32-bit target platforms,
  with 32-bit pointers and emulation of 64-bit integer arithmetic
  using pairs of 32-bit integers.  In terms of C data models, CompCert
  used to be restricted to the ILP32LL64 model; now it also supports
  I32LP64 and IL32LLP64.

- The x86 port of CompCert was extended to produce x86-64 bit code in
  addition to the original x86-32 bit (IA32) code.  (This is the first
  instantiation of the new support for 64-bit targets described
  above.) Support for x86-64 is currently available for Linux and MacOS X.
  (Run the configure script with `x86_64-linux` or `x86_64-macosx`.)
  This is an early port: several ABI incompatibilities remain.

Language features:

- Support for anonymous structures and unions as members of
  structures or unions.  (ISO C11, section 6.7.2.1, para 13 and 19.)
- New built-in functions for ARM and PowerPC:
  `__builtin_ctz`, `__builtin_ctzl`, `__builtin_ctzll`
  (count trailing zeros, 32 and 64 bits).

Usability:

- Added options `-Wxxx` and `-Wno-xxx` (for various values of `xxx`)
  to control which warnings are emitted.
- Added options `-Werror=xxx` and `-Wno-error=xxx` (for various values of `xxx`)
  to control which warnings are treated as errors.
- Support response files where additional command-line arguments can
  be passed (syntax: `@file`).
- Improved wording of warning and error messages.
- Improved handling of attributes, distinguishing attributes that apply
  to types from attributes that apply to names.  For example, in
    `__attribute((aligned(8),section("foo"))) int * p;`
  the `aligned` attribute is attached to type `int`, while
  the `section` attribute is attached to name `p`.

Code generation:

- Support for ARM target processors in big-endian mode.
- Optimize 64-bit integer division by constants.

Bug fixing:

- Issue #155: on ARM, assembly errors caused by large jump tables for
  `switch` statements and overflow in accessing constant pools.
- Issue #151: large inductive definition causes a fatal error in
  32-bit versions of Coq.
- Issue #143: handle `%lf` `printf()` format in the reference interpreter
- Issue #138: struct declarations in K&R function parameters were ignored.
- Issues #110, #111, #113, #114, #115, #119, #120, #121, #122, #123, #124,
  #125, #126, #127, #128, #129, #130, #133, #138, #144: various cases
  of internal errors and failed assertions that should have been
  proper errors instead.
- For `__builtin_memcpy_aligned`, size and alignment arguments of 64-bit
  integer type were causing a fatal error on a 32-bit target.
- ARM and x86 ports: wrong register allocation for some calls to
  function pointers. 


# Release 2.7.1, 2016-07-18

- Ported to Coq 8.5pl2.

Bug fixing:
- Fixed a compile-time assertion failure involving builtins
  taking a 64-bit integer parameter and given an unsigned 32-bit integer
  argument.
- Updates to the Cminor parser.


# Release 2.7, 2016-06-29

Major improvement:
- The proof of semantic preservation now accounts for separate compilation
  and linking, following the approach of Kang, Kim, Hur, Dreyer and
  Vafeiadis, "Lightweight verification of separate compilation", POPL 2016.
  Namely, the proof considers a set of C compilation units, separately
  compiled to assembly then linked, and shows that the resulting
  assembly program preserves the semantics of the C program that would
  be obtained by syntactic linking of the source C compilation units.

Language features:
- Parse the `_Noreturn` function attribute from ISO C11.
- New standard includes files: `<iso646.h>` and `<stdnoreturn.h>` from ISO C11.
- New built-in functions: `__builtin_clzl`, `__builtin_clzll`
  (count leading zeros, 32 and 64 bits) for ARM, IA32 and PowerPC;
  `__builtin_ctz`, `__builtin_ctzl`, `__builtin_ctzll`
  (count trailing zeros, 32 and 64 bits) for IA32.

Formal C semantics:
- The semantics of conversions from pointer types to `_Bool`
  is fully defined (again).

Usability:
- The generation of DWARF debugging information in `-g` mode is now
  supported for ARM and IA32 (in addition to PowerPC).

Coq development:
- Revised the Stacking pass and its proof to make it more extensible
  later to e.g. 64-bit integer registers.
- Use register pairs in function calling conventions to control more
  precisely the splitting of 64-bit integer arguments and results
  into pairs of 32-bit quantities
- Revised the way register conventions are described in Machregs
  and Conventions.
- Simulation diagrams now live in Prop instead of Type.

OCaml development:
- Code cleanup to remove warnings, support "safe strings" mode,
  and be fully compatible with OCaml 4.02 and 4.03.
- Cminor parser: support for single-precision FP numbers and operators.

Bug fixing:
- Some declarations within C expressions were incorrectly ignored
  (e.g. `sizeof(enum e {A})`).
- ARM in Thumb mode: incorrect `movs` instructions involving the stack
  pointer register were generated.


# Release 2.6, 2015-12-21

Usability:
- Generation of full DWARF v2 debugging information in `-g` mode,
  including function-local variables.  This is fully supported
  for the PowerPC target with GNU tools or Diab tools.  Support
  for IA32 and ARM is nearly there.
- Production of detailed explanations for syntax errors during parsing.
  (Exploiting recent work by F. Pottier on the Menhir parser generator.)
- PowerPC port: added many new builtin functions.

Code generation and optimization:
- Support for PowerPC 64-bits (pointers are still 32-bit wide)
  and Freescale's E5500 variant.
- More prudent alias analysis for operations over pointers that are
  formally undefined, such as bit masking.
- New pass: Debugvar, to associate debug information to local variables.

Coq development:
- Richer representation of arguments and results to builtin operations.
- As a consequence, annotation builtins no longer need special handling.
- Added EF_debug builtins to transport debugging information throughout
  the compiler back-end.
- Upgraded the Flocq library to version 2.5.0.

Bug fixing:
- Issue #71: incorrect initialization of an array of `wchar_t`
- Corrected the handling of bit-fields of type `_Bool` and width > 1
- Removed copy optimization when returning a struct from a function.
- Full parsing of unprototyped (K&R-style) function definitions.
  (Before, the parsing was incomplete and would reject some definitions.)

Miscellaneous:
- The cchecklink tool (for a posteriori validation of assembly
  and linking) was removed.  It is replaced by the Valex tool,
  available from AbsInt.
- Added a command-line option `-conf <config file>` to select
  a different `compcert.ini` configuration file.
- Removed the command-line options `-fstruct-passing=<convention>`
  and `-fstruct-return=<convention>`, more confusing than useful.
- Added a command-line option `-fstruct-passing` that activates
  ABI-conformant by-value passing of structs and unions as
  function arguments or results.  If this option is not set,
  passing a struct/union as function argument is now rejected.
- The `-fstruct-return` command-line option is deprecated and
  becomes a synonymous for `-fstruct-passing`.
- The return type of `__builtin_clz` is `int`, as documented,
  and not `unsigned int`, as previously implemented.


# Release 2.5, 2015-06-12

Language features:
- Extended inline assembly in the style of GCC.  (See section 6.5
  of the user's manual.)  The implementation is not as complete
  as that of GCC or Clang.  In particular, the only constraints
  supported over operands are `r` (register), `m` (memory), and
  `i` (integer immediate).

Code generation and optimization:
- Revised translation of `||` and `&&` to Clight so as to
  produce well-typed Clight code.
- More prudent value analysis of uninitialized declarations of
  `const` global variables.
- Revised handling of "common" global declarations, fixes an issue
  with uninitialized declarations of `const` global variables.

Improvements in confidence:
- Formalized the typing rules for CompCert C in Coq and verified
  a type-checker, which is used to produce the type annotations
  in CompCert C ASTs, rather than trusting the types produced by
  the Elab pass.
- Coq proof of correctness for the Unusedglob pass (elimination
  of unreferenced static global definitions).  The Coq AST for
  compilation units now records which globals are static.
- More careful semantics of comparisons between a non-null pointer
  and the null pointer.  The comparison is undefined if the non-null
  pointer is out of bounds.

Usability:
- Generation of DWARF v2 debugging information in `-g` mode.
  The information describes C types, global variables, functions,
  but not yet function-local variables.  This is currently available
  only for the PowerPC/Diab target.
- Added command-line options to turn individual optimizations on or off,
  and a `-O0` option to turn them all off.
- Revised handling of arguments to `__builtin_annot` so that no code
  is generated for an argument that is a global variable or a local
  variable whose address is taken.
- In string and character literals, treat illegal escape sequences
  (e.g. `\%` or `\0`) as an error instead of a warning.
- Warn if floating-point literals overflow or underflow when converted
  to FP numbers.
- In `-g -S` mode, annotate the generated `.s` file with comments
  containing the C source code.
- Recognize and accept more of GCC's alternate keywords, e.g. `__signed`,
  `__volatile__`, etc.
- cchecklink: added option `-files-from` to read `.sdump` file names
    from a file or from standard input.

ABI conformance:
- Improved ABI conformance for passing values of struct or union types
  as function arguments or results.  Full conformance is achieved on
  IA32/ELF, IA32/MacOSX, PowerPC/EABI, PowerPC/Linux, and ARM/EABI.
- Support the `va_arg` macro from `<stdarg.h>` in the case of arguments
  of struct or union types.

Coq development:
- In the CompCert C and Clight ASTs, struct and union types are now
  represented by name instead of by structure.  A separate environment
  maps these names to struct/union definitions.  This avoids
  bad algorithmic complexity of operations over structural types.
- Introduce symbol environments (type `Senv.t`) as a restricted view on
  global environments (type `Genv.t`).
- Upgraded the Flocq library to version 2.4.0.

Bug fixing:
- Issue #4: exponential behaviors with deeply-nested struct types.
- Issue #6: mismatch on the definition of `wchar_t`
- Issue #10: definition of composite type missing from the environment.
- Issue #13: improved handling of wide string literals
- Issue #15: variable-argument functions are not eligible for inlining.
- Issue #19: support empty `switch` statements
- Issue #20: ABI incompatibility wrt struct passing on IA32.
- Issue #28: missing type decay in `__builtin_memcpy_aligned` applied to arrays.
- Issue #42: emit error if `static` definition follows non-`static` declaration.
- Issue #44: OSX assembler does not recognize `.global` directive.
- Protect against redefinition of the `__i64_xxx` helper library functions.
- Revised handling of nonstandard attributes in C type compatibility check.
- Emit an error on "preprocessing numbers" that are invalid numerical literals.
- Added missing check for static redefinition following a non-static
  declaration.
- Added missing check for redefinition of a typedef as an ordinary
  identifier within the same scope.

Miscellaneous:
- When preprocessing with gcc or clang, use `-std=c99` mode to force
  C99 conformance.
- Use a Makefile instead of ocamlbuild to compile the OCaml code.


# Release 2.4, 2014-09-17

Language features:
- Support C99 compound literals  (ISO C99 section 6.5.2.5).
- Support `switch` statements over an argument of type `long long`.

Code generation and optimization:
- Revised and improved support for single-precision floating-point
  arithmetic.  Earlier, all FP arithmetic was performed at double
  precision, with conversions to/from single precision as needed,
  in particular when loading/storing a single-precision FP number
  from/to memory.  Now, FP operations whose arguments are of type
  `float` are performed in single-precision, using the processor's
  single FP instructions.  Fewer conversions between double and
  single precision are generated.
- Value analysis and constant propagation: more precise treatment of
  comparisons against an integer constant.

Improvements in confidence:
- Full correctness proofs for the algorithms used in the runtime
  support library for conversions between 64-bit integers and
  floating-point numbers.

ARM port:
- Added support for Thumb2 instruction encoding (option `-mthumb`).
  Thumb2 is supported on ARMv7 and up, and produces more compact
  machine code.
- Exploit some VFPv3 instructions when available.
- Built-in function `__builtin_cntlz` (count leading zeros)
  renamed `__builtin_clz` for GCC / Clang compatibility.

PowerPC port:
- Refactored the expansion of built-in functions and
  pseudo-instructions so that it does not need to be re-done in
  cchecklink.
- Updated the cchecklink validator accordingly.
- More efficient code generated for volatile accesses to small data areas.
- Built-in function `__builtin_cntlz` (count leading zeros)
  renamed `__builtin_clz` for GCC / Clang compatibility.

IA32 port:
- Added built-in functions `__builtin_clz` and `__builtin_ctz`
  (count leading / trailing zeros).

Coq development:
- The memory model was extended with two new "chunks", Many32 and Many64,
  that enable storing any 32-bit value or 64-bit value using
  an abstract, not bit-based encoding, and reloading these values exactly.
  These new chunks are used to implement saving and restoring callee-save
  registers that can contain data of unknown types (e.g. float32 or float64)
  but known sizes.
- Refactored the library of FP arithmetic (lib/Floats.v) to support
  both 64- and 32-bit floats.


# Release 2.3pl2, 2014-05-15

Usability:
- Re-added support for `__func__` identifier as per ISO C99.
- Re-added some popular GCC extensions to ISO C99:
     * alternate keywords `__restrict`, `__inline__`, etc, 
     * support for empty structs and unions
     * support `\e` escape in char and string literals, meaning ESC
- Do not assume that the preprocessor removed all comments.

Bug fixing:
- Fixed regression on initializers of the form  `T x[N] = "literal";`
  where `T` is a typedef for a character type.
- `asm` statements were causing syntax errors.
- Better handling of `extern` and `extern inline` function definitions.
- Internal error on some octal escape sequences in string literals.
- Parsing of `#pragma section` directives made more robust and
  with better error reporting.


# Release 2.3, 2014-05-05
	
Language features:
- Support for C99 designated initializers. (ISO C99 section 6.7.8.)

Improvements in confidence:
- The parser is now formally verified against the ISO C99 grammar plus
  CompCert's extensions.  The verification proves that the parser
  recognizes exactly the language specified by the grammar, and that
  the grammar has no ambiguities.  For more details, see the paper
  "Validating LR(1) parsers" by Jacques-Henri Jourdan, François Pottier,
  and Xavier Leroy, ESOP 2012, http://dx.doi.org/10.1007/978-3-642-28869-2_20
- More theorems proved about float<->integer conversions.

Optimizations:
- Optimize `x != 0`, `x == 0`, `x != 1`, and `x == 1` when x is known
  to be a boolean already, ranging over {0, 1, undef}.
- More systematic constant propagation in pass Selection, lightens
  the work of later RTL optimisations.
- IA32: recognize and use the `not` instruction.

Usability:
- Option `-timings` to print compilation times for various passes.
- Various tweaks in IRC graph coloring to reduce compilation time.
- IA32: add built-in functions for fused multiply-add
  (require a recent processor with FMA3 extensions).

Improvements in ABI conformance:
- New target platform: ARM with EABI "hard float" calling conventions
  (armhf in Debian's classification).
- IA32 and ARM: revised handling of "common" variables to conform with ABI.

Bug fixing:
- In -fbitfields emulation: `a->f` was not properly rewritten if `a`
  had "array of structs" type instead of "pointer to struct".
- Moved analysis of single-precision floats from RTLtyping to Machtyping.
  (RTLtyping was incorrectly rejecting some functions involving
  single-precision floats.)  Simplified LTL semantics and Allocation
  pass accordingly.
- Assignment to a l-value of `volatile float` type could cause
  an internal error in RTLtyping/Machtyping.
- The case __builtin_fabs applied to integers was missing in the
  C semantics and in C#minor generation.
- Fixed some type annotations on CompCert C expressions.  These
  annotations were incorrect but not in a way that impacted code
  generation.


# Release 2.2, 2014-02-24

Major improvements:

- Two new static analyses are performed on the RTL intermediate form:
    . Value analysis, tracking constants, some integer range information,
      and pointer aliasing information.
    . Neededness analysis, generalizing liveness analysis to individual
      bits of integer values and to stack memory locations.

- Improved RTL optimizations, exploiting the results of these analyses:
    . Constant propagation can track constants across memory stores and loads.
    . Common subexpression elimination exploits nonaliasing information.
    . Dead code elimination can eliminate useless memory writes and 
      block copies, as well as integer operations that do not change
      the needed bits.
    . Redundant cast elimination is now performed globally (at
      function level) rather than locally on individual expressions.

- Experimental support for defining and calling variable-argument functions,
  including support for the <stdarg.h> interface.
  (Option -fvararg-calls, "on" by default.)

Language features:
- In `switch` statements, `default` cases can now appear anywhere, not
  just as the last case.
- Support for incomplete array as last field of a struct,
  as specified in ISO C 99.
- Support for declarations within `for` loops, as specified in ISO C 99.
  (E.g. `for (int i = 0; i < 4; i++) ...`)
- Revised semantics and implementation of _Alignas(N) attribute
  to better match those of GCC and Clang.
- Better tolerance for functions declared without prototypes
  (option -funprototyped, "on" by default).
- On PowerPC, support "far-data" sections
  (register-relative addressing with 32-bit offsets).

Improvements in ABI conformance:
- For x86/IA32, align struct fields of types `double` or `long long` to 4
  instead of 8, as prescribed by the x86 ELF ABI.
- For PowerPC and ARM, structs and unions returned as function results
  are now passed in integer registers if their sizes are small enough
  (<= 8 bytes for PowerPC, <= 4 bytes for ARM).

Usability:
- Revised parsing of command-line arguments to be closer to GCC and Clang.
  In particular, `ccomp -c foo.c -o obj/foo.o` now works as expected,
  instead of ignoring the `-o` option as in earlier CompCert versions.
- Recognize input files ending in .i and .p as C source files that
  must not be preprocessed.
- Warn for uses of the following GCC extensions to ISO C:
  zero-sized arrays, empty structs/unions, empty initializer braces.
- Option `-fno-fpu` to prevent the use of FP registers for some
  integer operations such as block copies.  (Replaces the previous
  `-fno-sse` option which was x86/IA32-specific, and extends it to
  PowerPC and ARM.)
- Option `-drtl` to record the RTL intermediate representation
  at every stage of optimization.  (Replaces `-dtailcall`, `-dinlining`,
  `-dconstprop`, and `-dcse`.)
- Add CompCert version number and command-line arguments as comments
  in the generated assembly files.

Other performance improvements:
- Recognize __builtin_fabs as a primitive unary operator instead of
  a built-in function, enabling more optimizations.
- PowerPC: shorter code generated for `&global_variable + expr`.

Improvements in compilation times:
- More efficient implementation of Kildall's dataflow equation solver,
  reduces size of worklist and nomber of times a node is visited.
- Better OCaml GC settings significantly reduce compilation times
  for very large source functions.

Bug fixing:
- Fixed incorrect hypothesis on __builtin_write{16,32}_reversed.
- Fixed syntax error in __attribute__((__packed__)).
- Emit clean compile-time error for `switch` over a value of 64-bit
  integer type (currently not supported).
- Recognize source files with .i or .p extension as C sources that
  should not be preprocessed.

Coq development:
- Removed propositional extensionality axiom (prop_ext).
- Suppressed the Mfloat64al32 memory_chunk, no longer needed.


# Release 2.1, 2013-10-28

Language semantics:
- More precise modeling of not-a-numbers (NaNs) in floating-point
  arithmetic.
- The CompCert C language is now defined with reference to ISO C99
  instead of ISO C90 ("ANSI C") as before.  This affects mostly the
  wording of the reference manual.  However, the parsing of integer
  constants and character constants was revised to follow the ISO C99
  standard.

Language features:
- Support for _Alignas(N) attribute from ISO C 2011.
- Revised implementation of packed structs, taking advantage of _Alignas.
- Suppressed the pragma `packed`, replaced by a struct-level attribute
  `__packed__(params)` or `__attribute__(packed(params))`.
- Fixed typing rules for `__builtin_annot()` to avoid casting arguments
  of small integer or FP types.

Performance improvements:
- Optimize integer divisions by positive constants, turning them into
  multiply-high and shifts.
- Optimize floating-point divisions by powers of 2, turning them
  into multiplications.
- Optimize `x * 2.0` and `2.0 * x` into `x + x`.
- PowerPC: more efficient implementation of division on 64-bit integers.

Bug fixing:
- Fixed compile-time error when assigning a long long RHS to a bitfield.
- Avoid double rounding issues in conversion from 64-bit integers
  to single-precision floats.

Miscellaneous:
- Minor simplifications in the generic solvers for dataflow analysis.
- Small improvements in compilation times for the register allocation pass.
- MacOS X port updated to the latest XCode (version 5.0).


# Release 2.0, 2013-06-21

Major improvements:

- Support for C types `long long` and `unsigned long long`, that is,
  64-bit integers.  Regarding arithmetic operations on 64-bit integers,
  . simple operations are expanded in-line and proved correct;
  . more complex operations (division, modulus, conversions to/from floats)
    call into library functions written in assembly, heavily tested
    but not yet proved correct.

- The register allocator was completely rewritten to use an "end-to-end"
  translation validation approach, using a validation algorithm
  described in the paper "Validating register allocation and spilling"
  by Silvain Rideau and Xavier Leroy, Compiler Construction 2010,
  http://dx.doi.org/10.1007/978-3-642-11970-5_13
  This validation-based approach enables better register allocation, esp:
  . live-range splitting is implemented
  . two-address operations are treated more efficiently
  . no need to reserve processor registers for spilling and reloading.
  The improvements in quality of generated code is significant for
  IA32 (because of its paucity of registers) but less so for ARM and PowerPC.

- Preliminary support for debugging information.  The `-g` flag
  causes DWARF debugging information to be generated for line numbers
  and stack structure (Call Frame Information).  With a debugger like
  GDB, this makes it possible to step through the code, put breakpoints
  by line number, and print stack backtraces.  However, no information
  is generated yet for C type definitions nor for variables; therefore,
  it is not possible to print the values of variables.

Improvements in ABI conformance:
- For IA32 and ARM, function arguments of type `float`
  (single-precision FP) were incorrectly passed as `double`.
- For PowerPC, fixed alignment of `double` and `long long` arguments
  passed on stack.

Improvements in code generation:
- More aggressive common subexpression elimination across some builtin
  function calls, esp. annotations.

Improvements in compiler usability:
- Option -fno-taillcalls to turn off tail-call elimination.
  (Some static analysis tools are confused by this optimization.)
- Reduced stack usage of the compiler by rewriting some key functions
  in tail-recursive style.
- Reduced memory requirements of constant propagation pass by forgetting
  compile-time approximations of dead variables.
- More careful elaboration of C struct and union types into CompCert C
  types, avoiding behaviors exponential in the nesting of structs.

Bug fixing:
- Fixed parsing of labeled statements inside `switch` constructs,
  which were causing syntax errors.
- The `->` operator applied to an array type was causing a type error.
- Nested conditional expressions `a ? (b ? c : d) : e` were causing
  a compile-time error if `c`, `d` and `e` had different types.

Coq development:
- Adapted the memory model to the needs of the VST project at Princeton:
  . Memory block identifiers are now of type `positive` instead of `Z`
  . Strengthened invariants in the definition of memory injections
    and the specification of external calls.
- The LTL intermediate language is now a CFG of basic blocks.
- Suppressed the LTLin intermediate language, no longer used.


# Release 1.13, 2013-03-12

Language semantics:
- Comparisons involving pointers "one past" the end of a block are
  now defined.  (They used to be undefined behavior.)
  (Contributed by Robbert Krebbers).

Language features:
- Arguments to `__builtin_annot()` that are compile-time constants
  are now replaced by their (integer or float) value in the annotation
  generated in the assembly file.

Improvements in performance:
- ARM and PowerPC ports: more efficient access to function parameters
  that are passed on the call stack.
- ARM port; slightly better code generated for some indirect memory
  accesses.

Bug fixing:
- Fixed a bug in the reference interpreter in -all mode causing some
  reductions to be incorrectly merged.
- Wrong parsing of hexadecimal floating-point literals 0xMMMMpEEE.

Improvements in usability:
- Better error and warning messages for declarations of variables
  of size >= 2^32 bits.
- Reference interpreter: more efficient exploration of states in -all mode.

Coq development:
- More efficient implementation of machine integers (module Integers)
  taking advantage of bitwise operations defined in ZArith in Coq 8.4.
- Revised handling of return addresses in the Mach language
  and the Stacking and Asmgen passes.
- A number of definitions that were opaque for no good reason are now
  properly transparent.


# Release 1.12.1, 2013-01-29

Ported to Coq 8.4pl1.  Otherwise functionally identical to release 1.12.


# Release 1.12, 2013-01-11

Improvements in confidence:
- Floating-point literals are now parsed and converted to IEEE-754 binary
  FP numbers using a provably-correct conversion function implemented on
  top of the Flocq library.

Language semantics:
- Comparison between function pointers is now correctly defined
  in the semantics of CompCert C (it was previously undefined behavior,
  by mistake).
- Bit-fields of `enum` type are now treated as either unsigned or signed,
  whichever is able to represent all values of the enum.
  (Previously: always signed.)
- The `&&` and `||` operators are now primitive in CompCert C and are
  given explicit semantic rules, instead of being expressed in terms
  of `_ ? _ : _` as in previous CompCert releases.
- Added a `Ebuiltin` expression form (invocation of built-in function)
  to CompCert C, and a `Sbuiltin` statement form to Clight.
  Used it to simplify the encoding of annotations, memcpy, and volatile
  memory accesses.

Performance improvements:
- Better code generated for `&&` and `||` operators.
- More aggressive elimination of conditional branches during constant
  propagation, taking better advantage of inferred constants.

Language features:
- By popular demand, `asm` statements for inline assembly are now supported
  if the flag -finline-asm is set.  Use with extreme caution, as the
  semantic preservation proof assumes these statements have no effect
  on the processor state.

Internal simplifications and reorganization:
- Clight, Csharpminor, Cminor: suppressed the `Econdition` conditional
  expressions, no longer useful.
- Clight: a single loop form, the three C loops are derived forms.
- Clight: volatile memory accesses are materialized as builtin operations.
- Clight: removed dependencies on CompCert C syntax and semantics.
- New pass SimplLocals over Clight that replaces local scalar variables
  whose address is never taken by temporary, nonadressable variables.
  (This used to be done in Cminorgen.)
- Csharpminor: simplified semantics.
- Cminor: suppressed the `Oboolval` and `Onotbool` operators,
  which can be expressed in terms of `Ocmpu` at no performance costs.
- All languages: programs are now presented as a list of global definitions
  (of functions or variables) instead of two lists, one for functions
  and the other for variables.

Other changes:
- For compatibility with other C compilers, output files are now generated
  in the current directory, by default; output file name can be controlled
  with the -o option, somewhat like with GCC.
- Reference interpreter: better handling of volatile memory accesses.
- IA32/MacOS X: now supports referencing global variables defined in shared
  libraries; old hack for stdio is no longer needed.
- PowerPC/MacOS X: this port was removed, as recent version of MacOS X
  no longer support PowerPC.


# Release 1.11, 2012-07-13

Improvements in confidence:
- Floating-point numbers and arithmetic operations, previously axiomatized,
  are now implemented and proved correct in Coq, using the Flocq library
  of S. Boldo and G. Melquiond.

Language semantics:
- In accordance with ISO C standards, the signed division `min_int / -1`
  and the signed remainder `min_int % -1` (where `min_int` is the smallest
  representable signed integer) now have undefined semantics and are
  treated as "going wrong" behaviors.
  (Previously, they were defined with results `min_int` and 0 respectively,
  but this behavior requires unnatural code to be generated on IA32 and
  PowerPC.)

Performance improvements:
- Function inlining is now implemented.  The functions that are inlined
  are those declared `inline` in the C source, provided they are not
  recursive.
- Constant propagation is now able to propagate the initial values of
  `const` global variables.
- Added option -ffloat-const-prop to control the propagation of
  floating-point constants; see user's manual for documentation.
- Common subexpression elimination can now eliminate memory loads
  following a memory store at the same location.
- ARM: make use of the `fcmpzd` and `fmdrr` instructions.

New tool:
- The "cchecklink" tool performs a posteriori validation of the
  assembling and linking phases.  It is available for PowerPC-EABI
  only.  It takes as inputs an ELF-PowerPC executable as produced
  by the linker, as well as .sdump files (abstract assembly) as
  produced by `ccomp -sdump`, and checks that the executable contains
  properly-assembled and linked code and data corresponding to those
  produced by CompCert.

Other changes:
- Elimination of `static` functions and `static` global variables that
  are not referenced in the generated code.
- The memory model was enriched with "max" permissions in addition to
  "current" permissions, to better reason over "const" blocks and
  already-deallocated blocks.
- More efficient implementation of the memory model, resulting
  in faster interpretation of source files by `ccomp -interp`.
- Added option `-falign-functions` to control alignment of function code.


# Release 1.10, 2012-03-13

Improvements in confidence:
- CompCert C now natively supports volatile types.  Its semantics fully
  specifies the meaning of volatile memory accesses.  The translation
  of volatile accesses to built-in function invocations is now proved correct.
- CompCert C now natively supports assignment between composite types
  (structs or unions), passing composite types by value as function
  parameters, and other instances of using composites as r-values, with
  the exception of returning composites by value from a function.
  (The latter remains emulated, using the -fstruct-return option.)
- PowerPC: removed the -fmadd option, not semantically-preserving
  in the strict sense.

Language features:
- Support for `_Bool` type from ISO C99.
- Support for `_Alignof(ty)` operator from ISO C 2011
  and `__alignof__(ty)`, `__alignof__(expr)` from GCC.

Performance improvements:
- Improvements in instruction selection, especially for integer casts
  and their combinations with bitwise operations.
- Shorter, more efficient code generated for accessing volatile global
  variables.
- Better code generated for the && and || operators.
- More aggressive common subexpression elimination (CSE) of memory loads.
- Improved register allocation for invocations of built-ins,
  especially for annotations.
- In Cminor and down, make safe operators non-strict: they return Vundef
  instead of getting stuck.  This enables more optimizations.
- Cast optimization is no longer performed by a separate pass over
  RTL, but equivalent optimization is done during Cminor generation
  and during instruction selection.

Other improvements:
- PowerPC/EABI: uninitialized global variables now go in common (bss) section.
- PowerPC: work around limited excursion of conditional branch instructions.
- PowerPC: added `__builtin_fnmadd()` and `__builtin_fnmsub()`.
- Reference interpreter: better printing of pointer values and locations.
- Added command-line options -Wp,<opt> -Wa,<opt> -Wl,<opt> to pass
  specific options to the preprocessor, assembler, or linker, respectively.
- More complete Cminor parser and printer (contributed by Andrew Tolmach).


# Release 1.9.1, 2011-11-28

Bug fixes:
- Initialization of a char array by a short string literal was wrongly rejected
- Incorrect handling of volatile arrays.
- IA32 code generator: make sure that min_int / -1 does not cause a
  machine trap.

Improvements:
- Added language option -flongdouble to treat `long double` like `double`.
- The reference interpreter (ccomp -interp) now supports 2-argument main
  functions (int main(int, char **)).
- Improved but still very experimental emulation of packed structs
  (-fpacked-structs)
- Coq->Caml extraction: extract Coq pairs to Caml pairs and Coq
  characters to Caml `char` type.


# Release 1.9, 2011-08-22

- The reduction semantics of CompCert C was made executable and turned
  into a reference interpreter for CompCert C, enabling animation of
  the semantics.  (Thanks to Brian Campbell for suggesting this approach.)
  Usage is:  `ccomp -interp [options] source.c`
  Options include:
    `-trace`      to print a detailed trace of reduction steps
    `-random`     to randomize execution order
    `-all`        to explore all possible execution orders in parallel

- Revised and strengthened the top-level statements of semantic preservation.
  In particular, we now show:
  * backward simulation for the whole compiler without assuming
    a deterministic external world;
  * if the source program goes wrong after performing some I/O,
    the compiled code performs at least these I/O before continuing
    with an arbitrary behavior.

- Fixed two omissions in the semantics of CompCert C
  (reported by Brian Campbell):
  * Functions calls through a function pointer had undefined semantics.
  * Conditional expressions `e1 ? e2 : e3` where `e2` and `e3` have different
    types were missing a cast to their common type.

- Support for "read-modify-write" operations over volatiles
  (such as `e++` or `--e` or `e |= 1` where `e` has volatile type)
  through a new presimplification (flag `-fvolatile-rmw`, "on" by default).

- New optimization pass: Redundant Reload Elimination, which fixes up
  inefficiencies introduced during the Reload pass.  On x86, it increases
  performance by up to 10%.  On PowerPC and ARM, the effect is negligible.

- Revised handling of annotation statements.  Now they come in two forms:
    1. `__builtin_annot("format", x1, ..., xN)`
       (arbitrarily many arguments; no code generated, even if some
        of the xi's were spilled; no return value)
    2. `__builtin_annot_intval("format", x1)`
       (one integer argument, reloaded in a register if needed,
        returned as result).

- Related clean-ups in the handling of external functions and
  compiler built-ins.  In particular, `__builtin_memcpy` is now
  fully specified.

- ARM code generator was ported to the new ABI (EABI in ARM parlance,
  armel in Debian parlance), using VFD instructions for floating-point.
  (Successfully tested on a Trimslice platform running Ubuntu 11.04.)

- IA32 code generator:
    . Added -fno-sse option to prevent generation of SSE instructions
      for memory copy operations.
    . More realistic modeling of the ST0 (top-of-FP-stack) register
      and of floating-point compare and branch.

- PowerPC code generator: more efficient instruction sequences generated
  for insertion in a bit field and for some comparisons against 0.


# Release 1.8.2, 2011-05-24

- Support for `aligned` and `section` attributes on global variables, e.g.
    `__attribute__((aligned(16))) int x;`

- Experimental emulation of packed structs (flag -fpacked-structs).

- Pointer comparisons now treated as unsigned comparisons (previously: signed).
  This fixes an issue with arrays straddling the 0x8000_0000 boundary.
  Consequently, the `ofs` part of pointer values `Vptr b ofs` is
  now treated as unsigned (previously: signed).

- Elimination of unreferenced labels now performed by a separate pass
  (backend/CleanupLabels.v) and proved correct.

- Stacking pass revised: supports more flexible layout of the stack
  frame; two-step proof (Stackingproof + Machabstr2concr) merged
  into one single proof (Stackingproof).

- The requirement that pointers be valid in pointer comparisons
  was pushed through all intermediate languages of the back-end
  (previously: requirement present only up to Csharpminor).

- Emulation of assignment between structs and between unions was
  simplified and made more efficient, thanks to a better implementation
  of `__builtin_memcpy`.

- Improvements to the compiler driver:
    .  -E option now prints preprocessed result to standard output
       instead of saving it in a .i file
    .  support for .s (assembly) and .S (assembly to be preprocessed)
       input files


# Release 1.8.1, 2011-03-14

- Adapted to Coq 8.3pl1.

- Reduced compilation times through several algorithmic improvements
  (contributed by A. Pilkiewicz).

- In the various semantics, allow float-to-int conversions to fail
  (if the float argument is outside the range of representable ints).

- Initialization of global C variables made more robust and proved correct.

- ABI conformance improved:
     * the `char` type is now signed for x86, remains unsigned for PowerPC and ARM
     * placement of bit-fields now follows SVR4 conventions (affects PowerPC)

- Bug fixes in the C pre-simplifier:
     * nontermination with some recursive struct types
     * issues with zero-width bit fields
     * elimination of struct assignments duplicating some volatile accesses


# Release 1.8, 2010-09-21

- The input language to the proved part of the compiler is no longer
  Clight but CompCert C: a larger subset of the C language supporting
  in particular side-effects within expressions.  The transformations
  that pull side effects out of expressions and materialize implicit
  casts, formerly performed by untrusted Caml code, are now fully
  proved in Coq.

- New port targeting Intel/AMD x86 processors.  Generates 32-bit x86 code
  using SSE2 extensions for floating-point arithmetic.  Works under
  Linux, MacOS X, and the Cygwin environment for Windows.
  CompCert's compilation strategy is not a very good match for the
  x86 architecture, therefore the performance of the generated code
  is not as good as for the PowerPC port, but still usable.
  (About 75% of the performance of `gcc -O1` for x86, compared with
   more than 90% for PowerPC.)

- More faithful semantics for volatile accesses:
  . volatile reads and writes from a volatile global variable are treated
    like input and output system calls (respectively), bypassing
    the memory model entirely;
  . volatile reads and writes from other locations are treated like
    regular loads and stores.

- Introduced `__builtin_memcpy()` and `__builtin_memcpy_words()`, use them
  instead of `memcpy()` to compile struct and union assignments.

- Introduced `__builtin_annotation()` to transmit assertions from
  the source program all the way to the generated assembly code.

- Elimination of some useless casts around `&`, `|` and `^` bitwise operators.

- Produce fewer "moves" during RTL generation.  This speeds up the
  rest of compilation and slightly improves the result of register
  allocation when register pressure is high.

- Improvements in register allocation:
  . Implemented a spilling heuristic during register allocation.
    This heuristic reduces significantly the amount of spill code
    generated when register pressure is high.
  . More coalescing between low-pressure and high-pressure variables.
  . Aggressive coalescing between pairs of spilled variables.

- Fixed some bugs in the emulation of bit fields.


# Release 1.7.1, 2010-04-13

Bug fixes in the new C pre-simplifier:
- Missing cast on return value for some functions
- Incorrect simplification of some uses of || and &&
- Nontermination in the presence of a bit field of size exactly 32 bits.
- Global initializers for structs containing bit fields.
- Wrong type in volatile reads from variables of type `unsigned int`.

Small improvements to the PowerPC port:
- Added `__builtin_trap()` built-in function.
- Support for `#pragma reserve_register` (EABI)
- Less aggressive alignment of global variables.
- Generate `.type` and `.size` directives (EABI).


# Release 1.7, 2010-03-31

- New implementation of the C type-checker, simplifier, and translation to
  Clight.  Compared with the previous CIL-based solution, the new
  implementation is more modular and supports more optional simplifications.

- More features of the C language are handled by expansion during
  translation to Clight:
    . assignment between structs and unions (option -fstruct-assign)
    . passing structs and union by value (option -fstruct-passing)
    . bit-fields in structs (option -fbitfields)

- The `volatile` modifier is now honored.  Volatile accesses are represented
  in Clight by calls to built-in functions, which are preserved throughout
  the compilation chain, then turned into processor loads and stores
  at the end.

- Generic support for C built-in functions.  These predefined external
  functions give access to special instructions of the processor.  See
  powerpc/CBuiltins.ml for the list of PowerPC built-in functions.

- The memory model now exposes the bit-level in-memory representation
  of integers and floats.  This strengthens the semantic preservation
  theorem: we now prove that C code that directly manipulates these
  bit-level representations (e.g. via a union between floats and integers)
  is correctly compiled.

- The memory model now supports fine-grained access control to individual
  bytes of a memory block.  This feature is currently unused in the
  compiler proofs, but will facilitate connections with separation logics
  later.

- External functions are now allowed to read and modify memory.
  The semantic preservation proofs were strengthened accordingly.
  In particular, this enables the malloc() and free() C library functions
  to be modeled as external functions in a provably correct manner.

- Minor improvements in the handling of global environments and the
  construction of the initial memory state.

- Bug fixes in the handling of `#pragma section` and `#pragma set_section`.

- The C test suite was enriched and restructured.


# Release 1.6, 2010-01-13

- Support Clight initializers of the form `int * x = &y;`.

- Fixed spurious compile-time error on Clight initializers of the form
  `const enum E x[2] = { E_1, E_2 };`.

- Produce informative error message if a `return` without argument
  occurs in a non-void function, or if a `return` with an argument
  occurs in a void function.

- Preliminary support for `#pragma section` and `#pragma set_section`.

- Preliminary support for small data areas in PowerPC code generator.

- Back-end: added support for jump tables; used them to compile
  dense `switch` statements.

- PowerPC code generator: force conversion to single precision before
  doing a "store single float" instruction.


# Release 1.5, 2009-08-28

- Support for `goto` in the source language Clight.

- Added small-step semantics for Clight.

- Traces for diverging executions are now uniquely defined;
  tightened semantic preservation results accordingly.

- Emulated assignments between structures
  (during the C to Clight initial translation).

- Fixed spurious compile-time error on Clight statements of the form
  `x = f(...);` where x is a global variable.

- Fixed spurious compile-time error on Clight initializers where
  the initial value is the result of a floating-point computation
  (e.g. `double x = 3.14159 / 2;`).

- Simplified the interface of the generic dataflow solver.

- Reduced running time and memory requirements for the constant propagation
  pass.

- Improved the implementation of George and Appel's graph coloring heuristic:
  runs faster, produces better results.

- Revised the implementation of branch tunneling.

- Improved modularization between processor-dependent and
  processor-independent parts.


# Release 1.4.1, 2009-06-05

- Adapted to Coq 8.2-1.  No changes in functionality.

# Release 1.4, 2009-04-20

- Modularized the processor dependencies in the back-end.

- Three target architectures are now supported:
       PowerPC / MacOS X       (most mature)
       PowerPC / EABI & Linux  (getting stable)
       ARM / Linux EABI        (still experimental)

- Added alignment constraints to the memory model.

- Clight: added support for conditional expressions (a ? b : c);
  removed support for array accesses a[i], now a derived form.

- C front-end: honor `static` modifiers on globals.

- New optimization over RTL: turning calls into tail calls when possible.

- Instruction selection pass: elimination of redundant casts following
  a memory load of a `small` memory quantity.

- Linearization pass: improved the linearization heuristic.

- Reloading pass: more economical use of temporaries.

- Back-end: removed "alloc heap" instruction; removed pointer validity
  checks in pointer comparisons.


# Release 1.3, 2008-08-11

- Added `goto` and labeled statements to Cminor.  Extended RTLgen and
    its proof accordingly.

- Introduced small-step transition semantics for Cminor; used it in
    proof of RTLgen pass; proved consistency of Cminor big-step semantics
    w.r.t. transition semantics.

- Revised division of labor between the Allocation pass and the Reload pass.
    The semantics of LTL and LTLin no longer need to anticipate the passing
    of arguments through the conventional locations.

- Cleaned up Stacking pass: the positions of the back link and of
    the return address in the stack frame are no longer hard-wired
    in the Mach semantics.

- Added operator to convert from float to unsigned int; used it in C front-end

- Added flag -fmadd to control recognition of fused multiply-add and -sub

- Semantics of pointer-pointer comparison in Clight was incomplete:
    pointers within different blocks can now be compared using == or !=

- Addition integer + pointer is now supported in Clight.

- Improved instruction selection for complex conditions involving || and &&.

- Improved translation of Cminor `switch` statements to RTL decision trees.

- Fixed error in C parser and simplifier related to `for` loops with
    complex expressions as condition.

- More benchmark programs in test/


# Release 1.2, 2008-04-03

- First public release

/-! # C identifiers the C backend makes from a module name (findings J2–J4)

The C backend used to print, for a module `m`,

* the struct tag `struct m`,
* the functions `sparkle_m_reset`, `sparkle_m_eval`, `sparkle_m_tick`,
  `sparkle_m_eval_tick`.

Three collisions followed (`docs/parallel/J-tagged-names.md`, measured):

* J2 — the role is a SUFFIX, and `_eval` is a prefix of `_eval_tick`:
  modules `X` and `X_eval` both define `sparkle_X_eval_tick`;
* J3 — the tag is the bare module name: a module named `volatile` gives
  `struct volatile`;
* J4 — the fixed trampolines of the JIT wrapper are `sparkle_jit_reset`, …:
  a module named `jit` defines them a second time.

Here ONE function makes every such identifier:

    cIdent role m  =  "sparkle_"  ++  code role  ++  "_"  ++  m

The role comes FIRST, as a code of exactly two letters followed by `_`:

    ms  struct tag      mr  reset      me  eval      mt  tick      mx  eval_tick

What that gives (`Tools/ShippingCIdent.lean` proves 1–3; the grids are
`#guard`s in `Tests/Compiler/CIdentTest.lean`):

1. INJECTIVE in the pair: `cIdent r m = cIdent r' m'` only if `r = r'` and
   `m = m'` — for ALL strings `m`, `m'`. (The codes have one length, so the
   text after the fixed prefix splits in one way.) No module name can make
   two identifiers equal; in particular the struct tag is never a function
   name, which matters for the CUDA emitters, where the text is C++ and a
   struct tag is an ordinary identifier.
2. Every identifier starts with `sparkle_m`. So it is not a C or C++
   keyword, not `main`, not a name of the C library (`memcpy`, `calloc`, …),
   and it does not start with `_` (the reserved `_X…` / `__…` forms).
3. No FIXED name of the backend starts with `sparkle_m` (`fixedNames` below:
   the trampolines `sparkle_jit_*`, `sparkle_wide_shr64`, `jit_vtable`, …),
   so a module-derived identifier never equals one, whatever the module is
   called — `jit`, `main`, `memcpy`, or a name that itself starts with
   `sparkle_`.
4. The characters of `cIdent r m` are those of `m` plus lower-case letters
   and `_`: when `m` has only letters, digits, `_`, `$` (every compiler-made
   module name: `Sparkle.IR.ModuleName`), `CSim.sanitizeName` leaves the
   identifier unchanged.

NOT claimed: that `m` itself is free of `__` (a tagged module name such as
`Sp$D$always__ff` has it; C reserves only a LEADING `__`, C++ reserves it
anywhere — the CUDA text is C++ and stays UNVERIFIED); that member names
(ports, wires, instances) avoid C keywords; that a wire of a parsed design is
not itself named like one of these identifiers.

Structural recursion on lists only (the pattern of `Sparkle.IR.ModuleName`),
so everything evaluates and the proofs are by cases. -/
namespace Sparkle.Backend.CIdent

/-- What a module-derived C identifier is FOR. -/
inductive Role where
  /-- the tag of the module's `struct` -/
  | structTag
  /-- the reset function -/
  | reset
  /-- the combinational evaluation -/
  | eval
  /-- the clock edge -/
  | tick
  /-- the fused evaluation and clock edge -/
  | evalTick
  deriving DecidableEq, Repr

/-- The two-letter code of a role. -/
def Role.code : Role → List Char
  | .structTag => ['m', 's']
  | .reset => ['m', 'r']
  | .eval => ['m', 'e']
  | .tick => ['m', 't']
  | .evalTick => ['m', 'x']

/-- Every role, for the grids. -/
def Role.all : List Role := [.structTag, .reset, .eval, .tick, .evalTick]

/-- `sparkle_`, the project prefix of every generated global identifier. -/
def prefixL : List Char := ['s', 'p', 'a', 'r', 'k', 'l', 'e', '_']

/-- The identifier as characters: prefix, code, `_`, module name. -/
def cIdentL (r : Role) (m : List Char) : List Char :=
  prefixL ++ (r.code ++ ('_' :: m))

/-- **The C identifier of a role of a module.** `m` is the module name as the
emitter prints it (`CSim.sanitizeName m.name`). -/
def cIdent (r : Role) (m : String) : String := String.ofList (cIdentL r m.toList)

/-- The head every module-derived identifier has: `sparkle_m`. -/
def moduleHead : String := "sparkle_m"

/-- The FIXED global names in the C text of the backend (file scope: the JIT
trampolines and vtable, the wide-shift helper and its guard macro) and the
names the text takes from the C library or the language. None starts with
`sparkle_m` (`Tests/Compiler/CIdentTest.lean`). -/
def fixedNames : List String :=
  [ "sparkle_jit_create", "sparkle_jit_destroy", "sparkle_jit_reset", "sparkle_jit_eval",
    "sparkle_jit_tick", "sparkle_jit_eval_tick", "sparkle_jit_set_input",
    "sparkle_jit_get_output", "sparkle_jit_get_wire", "sparkle_jit_set_mem",
    "sparkle_jit_get_mem", "sparkle_jit_memset_word", "sparkle_jit_wire_name",
    "sparkle_jit_num_wires", "sparkle_jit_set_reg", "sparkle_jit_get_reg",
    "sparkle_jit_reg_name", "sparkle_jit_num_regs", "sparkle_jit_snapshot",
    "sparkle_jit_restore", "sparkle_jit_free_snapshot", "sparkle_jit_load",
    "sparkle_jit_run_cdc", "g_sparkle_jit_vtable", "jit_vtable", "JitVTable",
    "sparkle_wide_shr64", "SPARKLE_WIDE_SHR", "sparkle_evalTick_placeholder",
    "main", "memcpy", "memset", "memcmp", "calloc", "malloc", "free", "printf",
    "__builtin_memcmp", "self", "uint8_t", "uint16_t", "uint32_t", "uint64_t",
    "volatile", "double", "float", "char", "long", "short", "auto", "goto", "switch",
    "sizeof", "inline", "restrict", "register", "struct", "static", "void", "int",
    "unsigned", "signed", "const", "return", "if", "else", "for", "while", "do",
    "break", "continue", "case", "default", "typedef", "union", "enum", "extern",
    "_Bool", "_Static_assert", "_Atomic", "class", "namespace", "template", "new",
    "delete", "this", "operator", "public", "private", "virtual", "bool", "true", "false" ]

end Sparkle.Backend.CIdent

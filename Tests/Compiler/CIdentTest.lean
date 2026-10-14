import Sparkle
import Tools.ShippingCIdent

/-! # C identifiers of the C backend (findings J2–J4) — ASSERTING, no external tool

`Sparkle.Backend.CIdent.cIdent role m` makes every module-derived global
identifier of the C text (`Sparkle/Backend/CIdent.lean`); the general
statements are the theorems of `Tools/ShippingCIdent.lean`.

1. `#guard` grids (evaluated by the compiler, not the kernel): the five
   forms; pairwise distinct identifiers over a grid of module names chosen
   against the old scheme (`fk` / `fk_eval`, `jit`, `main`, `memcpy`,
   `volatile`, names that start with the project prefix, the empty name,
   tagged names); every identifier starts with `sparkle_m`; no FIXED name of
   the backend (`CIdent.fixedNames`) starts with `sparkle_m`, so none is an
   identifier of the grid or of any module; `CSim.sanitizeName` leaves every
   identifier of the grid unchanged.
2. The REAL C text (`CSim.toCJIT`) of a real declaration (a parent with two
   hardware-module children, compiled by the real entry), with its three
   modules RENAMED row by row to the names of the findings. In each text:
   every struct and every function is defined exactly once; each fixed
   trampoline is defined exactly once; the parent calls each child's eval
   once (in its eval), its eval_tick once (in its eval_tick) and its tick
   once (in its tick only: the fused function does not tick a child twice).
   Renaming is done on the IR (module names and instance targets), because a
   declaration named `main`, `jit` or `volatile` cannot be put in a file the
   suite imports; the driver `scripts/shipping-coverage/tagged_names_sim.sh`
   has the real declarations and the C compiler (rows `cfn`, `ckw`, `cjit`,
   `cmain`, `clibc`, `cpre`).
3. Axiom audit of the injectivity theorems.

A failure throws. Nothing here starts a C compiler: that the text COMPILES is
the driver's `csim-cc` rows, not this file. WRITTEN, NOT BUILT/RUN. -/

open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

namespace Tests.Compiler.CIdentTest
open Sparkle.Backend.CIdent

/-! ### 1. Grids -/

#guard cIdent .structTag "foo" == "sparkle_ms_foo"
#guard cIdent .reset "foo" == "sparkle_mr_foo"
#guard cIdent .eval "foo" == "sparkle_me_foo"
#guard cIdent .tick "foo" == "sparkle_mt_foo"
#guard cIdent .evalTick "foo" == "sparkle_mx_foo"
#guard cIdent .eval "Sp$D$always__ff" == "sparkle_me_Sp$D$always__ff"

-- J2: the old scheme gave `sparkle_fk_eval_tick` to both
#guard cIdent .evalTick "fk" != cIdent .tick "fk_eval"
-- J3: the tag is not the bare module name
#guard cIdent .structTag "volatile" == "sparkle_ms_volatile"
-- J4: a module named `jit` does not define a trampoline
#guard cIdent .reset "jit" == "sparkle_mr_jit"
#guard !fixedNames.contains (cIdent .reset "jit")

/-- Module names chosen against the old scheme and against this one. -/
def gridNames : List String :=
  [ "fk", "fk_eval", "fk_eval_tick", "fk_tick", "fk_reset", "eval", "tick", "eval_tick",
    "reset", "jit", "jit_eval", "jit_vtable", "main", "memcpy", "calloc", "free",
    "volatile", "double", "struct", "sparkle_", "sparkle_m", "sparkle_me_fk", "sparkle_ms_fk",
    "sparkle_jit", "sparkle_jit_eval", "ms", "me", "me_fk", "s_fk", "m", "", "_", "x_", "_x",
    "Sp$D$module", "Sp$D$always__ff", "Sp$D$1bad", "SparkleMem_combo_4_8",
    "Tests_Compiler_CIdentTest_fk", "Tests_Compiler_CIdentTest_fk_eval" ]

/-- Every identifier of the grid: all roles of all names. -/
def gridIds : List String :=
  Role.all.flatMap fun r => gridNames.map fun m => cIdent r m

#guard Role.all.length == 5
#guard gridNames.eraseDups.length == gridNames.length
#guard gridIds.length == 5 * gridNames.length
-- pairwise distinct: no two (role, module) pairs share an identifier
#guard gridIds.eraseDups.length == gridIds.length
-- every identifier starts with `sparkle_m`
#guard gridIds.all fun i => i.startsWith moduleHead
-- no fixed name of the backend, keyword or library name starts with it …
#guard fixedNames.all fun f => !f.startsWith moduleHead
-- … so none is an identifier of the grid
#guard gridIds.all fun i => !fixedNames.contains i
-- the emitter's sanitiser leaves every identifier unchanged
#guard gridIds.all fun i => Sparkle.Backend.CSim.sanitizeName i == i
-- and nothing starts with an underscore
#guard gridIds.all fun i => !i.startsWith "_"

/-! ### 2. The real C text, modules renamed -/

@[hardware_module]
def cidKidA (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 17#8 : Signal defaultDomain (BitVec 8))

@[hardware_module]
def cidKidB (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 19#8 : Signal defaultDomain (BitVec 8))

def cidTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  cidKidA x + cidKidB x

/-- Rename the target of an instance by `f`. -/
def renameStmt (f : String → String) : Sparkle.IR.AST.Stmt → Sparkle.IR.AST.Stmt
  | .inst target iname conns => .inst (f target) iname conns
  | other => other

def renameModule (f : String → String) (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with name := f m.name, body := m.body.map (renameStmt f) }

/-- Rename modules (names and instance targets) by `f`. -/
def renameDesign (f : String → String) (d : Sparkle.IR.AST.Design) : Sparkle.IR.AST.Design :=
  { topModule := f d.topModule, modules := d.modules.map (renameModule f) }

/-- The number of occurrences of `pat` in `s`. -/
def occurrences (s pat : String) : Nat := (s.splitOn pat).length - 1

structure Row where
  tag : String
  kidA : String
  kidB : String
  top : String

/-- The rows: the names the three modules get. -/
def rows : List Row :=
  [ { tag := "cfn", kidA := "X_fk", kidB := "X_fk_eval", top := "X_cfnTop" },
    { tag := "ckw", kidA := "volatile", kidB := "double", top := "X_ckwTop" },
    { tag := "cjit", kidA := "jit", kidB := "jit_eval", top := "X_cjitTop" },
    { tag := "cmain", kidA := "main", kidB := "X_k", top := "X_cmainTop" },
    { tag := "clibc", kidA := "memcpy", kidB := "calloc", top := "X_clibcTop" },
    { tag := "cpre", kidA := "sparkle_me_fk", kidB := "fk", top := "sparkle_jit" },
    { tag := "ctop", kidA := "X_a", kidB := "X_b", top := "main" },
    { tag := "ctag", kidA := "Sp$D$a", kidB := "Sp$D$a__b", top := "Sp$D$t" } ]

/-- The fixed trampolines that take the top's functions. -/
def trampolineHeads : List String :=
  [ "static void* sparkle_jit_create(void) {",
    "static void sparkle_jit_reset(void* ctx) {",
    "static void sparkle_jit_eval(void* ctx) {",
    "static void sparkle_jit_tick(void* ctx) {",
    "static void sparkle_jit_eval_tick(void* ctx) {" ]

/-- The failed checks of one C text whose modules are `names` (children
`kidA`, `kidB`). -/
def checkText (c : String) (names : List String) (kidA kidB : String) : List String :=
  let defs : List String := names.flatMap fun n =>
    let tag := cIdent .structTag n
    [ "struct " ++ tag ++ " {\n",
      "static void " ++ cIdent .reset n ++ "(struct " ++ tag ++ "* self) {",
      "static void " ++ cIdent .eval n ++ "(struct " ++ tag ++ "* self) {",
      "static void " ++ cIdent .tick n ++ "(struct " ++ tag ++ "* self) {",
      "static void " ++ cIdent .evalTick n ++ "(struct " ++ tag ++ "* self) {" ]
  let once : List String := defs ++ trampolineHeads ++
    [kidA, kidB].flatMap fun k =>
      -- a call line starts with the body indentation, so the identifier is
      -- matched WHOLE (`sparkle_me_fk(` is a part of `sparkle_me_sparkle_me_fk(`)
      [ "        " ++ cIdent .eval k ++ "(&self->", "        " ++ cIdent .evalTick k ++ "(&self->",
        "        " ++ cIdent .tick k ++ "(&self->", "        " ++ cIdent .reset k ++ "(&self->" ]
  (once.filter fun pat => occurrences c pat != 1).map fun pat =>
    "expected exactly once, found " ++ toString (occurrences c pat) ++ ": " ++ pat

open Lean Elab Command in
run_cmd liftTermElabM do
  logInfo m!"CIDENT: START synthesizeHierarchical cidTop"
  let design ← Sparkle.Compiler.Elab.synthesizeHierarchical ``cidTop
  let opt := Sparkle.IR.Optimize.optimizeDesign design
  let nameA := Sparkle.IR.ModuleName.ofDecl ``cidKidA
  let nameB := Sparkle.IR.ModuleName.ofDecl ``cidKidB
  let nameT := Sparkle.IR.ModuleName.ofDecl ``cidTop
  let have3 := [nameA, nameB, nameT].all fun n => opt.modules.any fun m => m.name == n
  unless have3 do
    throwError "CIDENT FAILED: the design does not hold the three expected modules: {opt.modules.map (·.name)}"
  let mut errs : Array String := #[]
  -- the text as the compiler names the modules
  logInfo m!"CIDENT: START the unrenamed text"
  let c0 := Sparkle.Backend.CSim.toCJIT opt
  for e in checkText c0 [nameA, nameB, nameT] nameA nameB do
    errs := errs.push ("asis: " ++ e)
  for r in rows do
    logInfo m!"CIDENT: START row {r.tag}"
    let f (n : String) : String :=
      if n == nameA then r.kidA else if n == nameB then r.kidB else if n == nameT then r.top else n
    let c := Sparkle.Backend.CSim.toCJIT (renameDesign f opt)
    let bad := checkText c [r.kidA, r.kidB, r.top] r.kidA r.kidB
    for e in bad do
      errs := errs.push (r.tag ++ ": " ++ e)
    logInfo m!"CIDENT {r.tag}: modules [{r.kidA}, {r.kidB}, {r.top}], C text {c.length} characters, failed checks {bad.length}"
  unless errs.isEmpty do throwError "CIDENT FAILED: {errs}"
  -- 3. axioms
  for n in [``Tools.ShippingCIdent.cIdent_injective, ``Tools.ShippingCIdent.cIdentL_injective,
      ``Tools.ShippingCIdent.cIdent_role_ne, ``Tools.ShippingCIdent.cIdent_module_ne,
      ``Tools.ShippingCIdent.cIdentL_hasHead, ``Tools.ShippingCIdent.cIdent_ne_of_no_head] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"CIDENT: {rows.length} renamed rows and the unrenamed text: every struct, function and trampoline defined once, every child called once per role; cIdent_injective and its companions on standard axioms"

end Tests.Compiler.CIdentTest

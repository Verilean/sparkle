import Tools.ShippingGen5Cover5
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in g5cv-r11 at 00b29bcb (Pod `kjob lake build Tests.Gen5.Cover5Check`, exit 0; TYPE 6, MUTANT 8, AXIOMS 6 standard, CLOSURE OK 5040 constants with 3 negative / 2 clean controls, UNKNOWN 3 negative / 1 clean; 3 intended sorry negatives print 3 "declaration uses `sorry`" warnings). Clean build is the coder's. No sorry / axiom / native_decide in source.
/-! # DG-COVER rev6 U-E2 (Tools/ShippingGen5Cover5.lean) checks

TYPE: each theorem is compared by the SAME comparer (`checkExpected`: binder names / binder info / `==` then `isDefEq` fallback, logged) with an `Exp…` statement
written here from the freeze text `scripts/gen5/DG_COVER_FREEZE_REV6.md` §2 (own spelling; the Tools file's statements are not copied).
Counting rule: one compared declaration = 1. TYPE = 6 theorems (T1–T6); MUTANT = 8 (T1 1, T2 2, T3 2, T4 2, T6 1); AXIOMS = 6 theorems.
MUTANT: one-place changes (or, for the conclusion mutants, dropping a conjunct), each well-typed, rejected by the same comparer — a signature / defeq rejection, NOT a semantic counterexample.
CLOSURE: value-closure walk over `getUsedConstants`; unknown names throw; negative controls built in memory inside `withoutModifyingEnv`
(3 intended `sorry`-based negatives, so the build prints 3 "declaration uses `sorry`" warnings). -/

namespace Tests.Gen5.Cover5Check
open Lean Meta Elab
open Tools.ShippingGen5Cover5 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingMachineAuto Tools.ShippingGen5Cover3 Tools.ShippingReaderFuel

section Expected

def ExpT1 : Prop := ∀ {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead}
    {v : Lean.Expr} {sp : MachineShape} (h : shapePost ai p m st v = some sp),
    sp.layout.lets = st.lets.size ∧ sp.layout.slots.length = min st.kinds.size st.inits.size

def ExpT2 : Prop := ∀ {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead}
    {v : Lean.Expr} {sp : MachineShape} (h : shapePost ai p m st v = some sp) (hL : st.LenOk),
    sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
    sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size

def ExpT3 : Prop := ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some (some sp)),
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size

def ExpT4 : Prop := ∀ {d : MachineData} {st : MachRead} {sp : MachineShape}
    (hs : sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
          sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size)
    (hsp : d.shape = sp) (hss : d.ss.length = sp.layout.slots.length)
    (hls : d.ls.length = sp.layout.lets) (hn : sp.insts.length ≤ d.nIn),
    ShapeAgree d st

def ExpT5 : Prop := ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some (some sp)) {d : MachineData}
    (hsp : d.shape = sp) (hss : d.ss.length = sp.layout.slots.length)
    (hls : d.ls.length = sp.layout.lets) (hn : sp.insts.length ≤ d.nIn),
    ∃ st : MachRead, st.LenOk ∧ ShapeAgree d st

def ExpT6 : Prop := ∀ {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (hbr : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, machineShapeF n false [] E senv true = some (some sp))
    (h : machineShape? false [] E senv = some sp) {d : MachineData}
    (hsp : d.shape = sp) (hss : d.ss.length = sp.layout.slots.length)
    (hls : d.ls.length = sp.layout.lets) (hn : sp.insts.length ≤ d.nIn),
    ∃ st : MachRead, st.LenOk ∧ ShapeAgree d st

/-- Mutant T1: `max` for `min`. -/
def MutT1Max : Prop := ∀ {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead}
    {v : Lean.Expr} {sp : MachineShape} (h : shapePost ai p m st v = some sp),
    sp.layout.lets = st.lets.size ∧ sp.layout.slots.length = max st.kinds.size st.inits.size

/-- Mutant T2: the `instOrigins` conjunct dropped. -/
def MutT2NoOrigins : Prop := ∀ {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead}
    {v : Lean.Expr} {sp : MachineShape} (h : shapePost ai p m st v = some sp) (hL : st.LenOk),
    sp.insts = st.insts.toList ∧
    sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size

/-- Mutant T2: no `hL`. -/
def MutT2NoLenOk : Prop := ∀ {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead}
    {v : Lean.Expr} {sp : MachineShape} (h : shapePost ai p m st v = some sp),
    sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
    sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size

/-- Mutant T3: last conjunct reads `st1.lets.size` (single-variable change). -/
def MutT3St1Lets : Prop := ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some (some sp)),
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st1.lets.size

/-- Mutant T3: the `shapePost … = some sp` clause removed (decouples `st` from `sp`). -/
def MutT3NoPost : Prop := ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some (some sp)),
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size

/-- Mutant T4: no `hsp` (the identification premise). -/
def MutT4NoHsp : Prop := ∀ {d : MachineData} {st : MachRead} {sp : MachineShape}
    (hs : sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
          sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size)
    (hss : d.ss.length = sp.layout.slots.length)
    (hls : d.ls.length = sp.layout.lets) (hn : sp.insts.length ≤ d.nIn),
    ShapeAgree d st

/-- Mutant T4: no `hn`. -/
def MutT4NoHn : Prop := ∀ {d : MachineData} {st : MachRead} {sp : MachineShape}
    (hs : sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
          sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size)
    (hsp : d.shape = sp) (hss : d.ss.length = sp.layout.slots.length)
    (hls : d.ls.length = sp.layout.lets),
    ShapeAgree d st

/-- Mutant T6: no `hbr`. -/
def MutT6NoHbr : Prop := ∀ {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp) {d : MachineData}
    (hsp : d.shape = sp) (hss : d.ss.length = sp.layout.slots.length)
    (hls : d.ls.length = sp.layout.lets) (hn : sp.insts.length ≤ d.nIn),
    ∃ st : MachRead, st.LenOk ∧ ShapeAgree d st

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``shapePost_layout_sizes ``ExpT1
  checkExpected ``shapePost_state_side ``ExpT2
  checkExpected ``machineShapeF_state_side ``ExpT3
  checkExpected ``shapeAgree_of_sides ``ExpT4
  checkExpected ``shapeAgree_of_fuel_run ``ExpT5
  checkExpected ``shapeAgree_of_production ``ExpT6
  -- mutants (same comparer; signature / defeq rejection, not semantic counterexamples)
  checkMutant ``shapePost_layout_sizes ``MutT1Max
  checkMutant ``shapePost_state_side ``MutT2NoOrigins
  checkMutant ``shapePost_state_side ``MutT2NoLenOk
  checkMutant ``machineShapeF_state_side ``MutT3St1Lets
  checkMutant ``machineShapeF_state_side ``MutT3NoPost
  checkMutant ``shapeAgree_of_sides ``MutT4NoHsp
  checkMutant ``shapeAgree_of_sides ``MutT4NoHn
  checkMutant ``shapeAgree_of_production ``MutT6NoHbr
  logInfo m!"GEN5 COVER5 TYPE 6 / MUTANT 8 (declarations compared, one each)"

def allThms : List Name := [``shapePost_layout_sizes, ``shapePost_state_side, ``machineShapeF_state_side, ``shapeAgree_of_sides, ``shapeAgree_of_fuel_run, ``shapeAgree_of_production]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in allThms do checkAxioms n

/-! ## Closure audit -/

def valueOfCI : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

partial def closureOf (env : Environment) (root : Name) : StateT (NameSet × NameSet) MetaM Unit := do
  if (← get).1.contains root then return
  modify fun (s, u) => (s.insert root, u)
  match env.find? root with
  | none => modify fun (s, u) => (s, u.insert root)
  | some ci =>
    for c in ci.type.getUsedConstants do closureOf env c
    match valueOfCI ci with
    | some v => for c in v.getUsedConstants do closureOf env c
    | none => pure ()
    match ci with
    | .inductInfo v => for c in v.ctors do closureOf env c
    | _ => pure ()

def forbiddenConsts : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler]

def closureHits (env : Environment) (roots : List Name) : MetaM (NameSet × NameSet × List Name) := do
  let (_, (seen, unk)) ← (roots.forM (closureOf env)).run ({}, {})
  pure (seen, unk, forbiddenConsts.filter seen.contains)

-- Negative controls (built in memory, no `sorry` token in this file): each must be detected; clean controls must not be.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let bad := mkApp2 (mkConst ``sorryAx [Level.zero]) tru (mkConst ``Bool.false)
    let ok := mkConst ``True.intro
    addDecl (.thmDecl { name := `Cover5Ctl.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `Cover5Ctl.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `Cover5Ctl.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `Cover5Ctl.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`Cover5Ctl.direct, `Cover5Ctl.viaHelper, `Cover5Ctl.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 COVER5 CLOSURE CONTROL FAILED: {n} not detected"
    for n in [`Cover5Ctl.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 COVER5 CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 COVER5 CLOSURE CONTROLS OK: 3 negative controls detected, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `Cover5Ctl.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `Cover5Ctl.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `Cover5Ctl.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `Cover5Ctl.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`Cover5Ctl.Missing.nowhere]
    unless unkRoot.contains `Cover5Ctl.Missing.nowhere do throwError "GEN5 COVER5 UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`Cover5Ctl.viaHelperU, `Cover5Ctl.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `Cover5Ctl.Missing.nowhere do throwError "GEN5 COVER5 UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`Cover5Ctl.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 COVER5 UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 COVER5 UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env allThms
  unless hits.isEmpty do throwError "GEN5 COVER5 CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "dataOf").length > 1 || (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 COVER5 CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 COVER5 CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 COVER5 CLOSURE OK: {seen.toList.length} constants, no forbidden constant"

#print axioms shapeAgree_of_production

end Tests.Gen5.Cover5Check

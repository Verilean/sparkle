import Tools.ShippingGen5ReaderTraceShape
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in Pod (kjob lake build Tests.Gen5.ReaderTraceShapeCheck, exit 0, 773 jobs; TYPE 7, MUTANT 5 signature/defeq rejections not semantic counterexamples, AXIOMS 7 standard only, CLOSURE OK 5214 constants from 7 roots, no sorryAx; 3 intended in-memory sorry negatives print warnings) on the tree of 8ba8bf09 (Lean content identical; this header is comment-only). Clean build is the coder's. (checks the part of rev14 U-R12a that is implemented: MidInputs / ShapeInputs / ShapeCarry, shapeCarry_empty, shapeRootLet_trace, rootLets_trace, shapeBody_trace). No sorry / axiom / native_decide in source.
/-! # DG-READERTRACE U-R12a (part) checks (Tools/ShippingGen5ReaderTraceShape.lean)

TYPE: the three `def`s (compared by VALUE) and the four theorems are compared by `checkExpected` against `Exp…` statements written here (own spelling).
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples). `ShapeInputs`, `hT` and the named hypotheses behind `hT` are not claimed true.
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceShapeCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv
open Tools.ShippingLetsAliasInv

section Expected

def ExpMid : Nat → StructEnv → ShapePre → Lean.Expr → Prop := fun nDecl senv p en =>
  p.bs.length ≤ nDecl ∧
  (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), (shapeMid senv p en).rootLets[k]? = some x →
      NoPh x.2.2 = true ∧ BvarLt (k + nDecl) x.2.2 = true) ∧
  (∀ (dom αs ie b : Lean.Expr), (shapeMid senv p en).run? = some (dom, αs, ie, b) →
      NoPh dom = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + nDecl) dom = true ∧
      ((∃ j, dom = .bvar j) ∨ (∃ c ls, dom = .const c ls)) ∧
      NoPh b = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + 1 + nDecl) b = true) ∧
  ((shapeMid senv p en).run? = none →
      NoPh (shapeMid senv p en).root = true ∧
      BvarLt ((shapeMid senv p en).rootLets.length + nDecl) (shapeMid senv p en).root = true)
def ExpShapeInputs : Nat → StructEnv → Bool → List (String × Nat) → ConstantInfo → Nat → Prop :=
  fun nDecl senv sm ps ci n => ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p →
    machNormF n senv p.e = some en → MidInputs nDecl senv p en
def ExpCarry : StructEnv → Nat → List MachVal → MachRead → Prop := fun senv nDecl env st =>
  RdOk st ∧ EnvOk st.lets.size env ∧ TrInv senv nDecl st ∧ EnvPh nDecl st env
def ExpEmpty : Prop := ∀ (senv : StructEnv) (nDecl : Nat), ShapeCarry senv nDecl [] ({} : MachRead)
def ExpDomAtomic : Lean.Expr → Prop := fun e => (∃ j, e = .bvar j) ∨ (∃ c ls, e = .const c ls)
def ExpStart : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (m : ShapeMid)
    (hdom : ∀ dom αs ie b, m.run? = some (dom, αs, ie, b) →
        NoPh dom = true ∧ BvarLt (m.rootLets.length + nDecl) dom = true ∧ ((∃ j, dom = .bvar j) ∨ (∃ c ls, dom = .const c ls)))
    {st0 : MachRead} (hr : (shapeStart senv m).run (wtab senv n) = some (some st0)),
    FReachC nDecl ({} : MachRead) st0 ∧ ShapeCarry senv nDecl [] st0
def ExpRootLet : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr)
    (hs : ShapeCarry senv nDecl s.1 s.2)
    (hn : NoPh a.2.2 = true) (hb : BvarLt (s.1.length + nDecl) a.2.2 = true)
    {s' : List MachVal × MachRead} (hr : (shapeRootLet senv s a).run (wtab senv n) = some (some s')),
    FReachC nDecl s.2 s'.2 ∧ ShapeCarry senv nDecl s'.1 s'.2 ∧ s'.1.length = s.1.length + 1
def ExpRootLets : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (l : List (Name × Lean.Expr × Lean.Expr)) (env : List MachVal) (st : MachRead),
    ShapeCarry senv nDecl env st →
    (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), l[k]? = some x →
        NoPh x.2.2 = true ∧ BvarLt (env.length + k + nDecl) x.2.2 = true) →
    ∀ {env' : List MachVal} {st' : MachRead},
    (foldO (shapeRootLet senv) (env, st) l).run (wtab senv n) = some (some (env', st')) →
    FReachC nDecl st st' ∧ ShapeCarry senv nDecl env' st' ∧ env'.length = env.length + l.length
def ExpBody : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (m : ShapeMid) (env : List MachVal) (st1 : MachRead)
    (hs : ShapeCarry senv nDecl env st1) (hlen : env.length = m.rootLets.length)
    (hrun : ∀ dom αs ie b, m.run? = some (dom, αs, ie, b) →
        NoPh b = true ∧ BvarLt (m.rootLets.length + 1 + nDecl) b = true)
    (hroot : m.run? = none → NoPh m.root = true ∧ BvarLt (m.rootLets.length + nDecl) m.root = true)
    {st : MachRead} {v : Lean.Expr} (hr : (shapeBody m env st1).run (wtab senv n) = some (some (st, v))),
    FReachC nDecl st1 st ∧ TrInv senv nDecl st ∧
    (m.wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v)

def MutStart : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (m : ShapeMid)
    (hdom : ∀ dom αs ie b, m.run? = some (dom, αs, ie, b) →
        NoPh dom = true ∧ BvarLt (m.rootLets.length + nDecl) dom = true ∧ ((∃ j, dom = .bvar j) ∨ (∃ c ls, dom = .const c ls)))
    {st0 : MachRead} (hr : (shapeStart senv m).run (wtab senv n) = some (some st0)),
    ShapeCarry senv nDecl [] st0
def MutMid : Nat → StructEnv → ShapePre → Lean.Expr → Prop := fun nDecl senv p en =>
  p.bs.length ≤ nDecl ∧
  (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), (shapeMid senv p en).rootLets[k]? = some x →
      NoPh x.2.2 = true ∧ BvarLt (k + nDecl) x.2.2 = true) ∧
  (∀ (dom αs ie b : Lean.Expr), (shapeMid senv p en).run? = some (dom, αs, ie, b) →
      NoPh dom = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + nDecl) dom = true ∧
      ((∃ j, dom = .bvar j) ∨ (∃ c ls, dom = .const c ls)) ∧
      NoPh b = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + nDecl) b = true) ∧
  ((shapeMid senv p en).run? = none →
      NoPh (shapeMid senv p en).root = true ∧
      BvarLt ((shapeMid senv p en).rootLets.length + nDecl) (shapeMid senv p en).root = true)
def MutCarry : StructEnv → Nat → List MachVal → MachRead → Prop := fun senv nDecl env st =>
  RdOk st ∧ EnvOk st.lets.size env ∧ TrInv senv nDecl st
def MutRootLet : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr)
    (hs : ShapeCarry senv nDecl s.1 s.2)
    (hn : NoPh a.2.2 = true) (hb : BvarLt (s.1.length + nDecl) a.2.2 = true)
    {s' : List MachVal × MachRead} (hr : (shapeRootLet senv s a).run (wtab senv n) = some (some s')),
    FReachC nDecl s.2 s'.2 ∧ ShapeCarry senv nDecl s'.1 s'.2
def MutRootLets : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (l : List (Name × Lean.Expr × Lean.Expr)) (env : List MachVal) (st : MachRead),
    ShapeCarry senv nDecl env st →
    (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), l[k]? = some x →
        NoPh x.2.2 = true ∧ BvarLt (k + nDecl) x.2.2 = true) →
    ∀ {env' : List MachVal} {st' : MachRead},
    (foldO (shapeRootLet senv) (env, st) l).run (wtab senv n) = some (some (env', st')) →
    FReachC nDecl st st' ∧ ShapeCarry senv nDecl env' st' ∧ env'.length = env.length + l.length
def MutBody : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (m : ShapeMid) (env : List MachVal) (st1 : MachRead)
    (hs : ShapeCarry senv nDecl env st1) (hlen : env.length = m.rootLets.length)
    (hrun : ∀ dom αs ie b, m.run? = some (dom, αs, ie, b) →
        NoPh b = true ∧ BvarLt (m.rootLets.length + 1 + nDecl) b = true)
    (hroot : m.run? = none → NoPh m.root = true ∧ BvarLt (m.rootLets.length + nDecl) m.root = true)
    {st : MachRead} {v : Lean.Expr} (hr : (shapeBody m env st1).run (wtab senv n) = some (some (st, v))),
    TrInv senv nDecl st ∧
    (m.wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v)

def ExpReach : Prop := ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape} {nDecl : Nat}
    (hT : TraceGood senv nDecl (readF senv n))
    (h : machineShapeF n sm ps ci senv ai = some (some sp))
    (hIn : ShapeInputs nDecl senv sm ps ci n),
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size ∧
      FReachC nDecl ({} : MachRead) st0 ∧ FReachC nDecl st0 st1 ∧ FReachC nDecl st1 st ∧
      TrInv senv nDecl st ∧
      ((shapeMid senv p en).wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v)
def ExpPrem : Prop := ∀ (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hi1 : Inst1Agrees) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env)) {n : Nat} {sm : Bool}
    {ps : List (String × Nat)} {ci : ConstantInfo} {ai : Bool} {sp : MachineShape} {nDecl : Nat}
    (h : machineShapeF n sm ps ci (structEnv env) ai = some (some sp))
    (hIn : ShapeInputs nDecl (structEnv env) sm ps ci n),
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (envs : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci (structEnv env) = some p ∧
      machNormF n (structEnv env) p.e = some en ∧
      (shapeStart (structEnv env) (shapeMid (structEnv env) p en)).run (wtab (structEnv env) n) = some (some st0) ∧
      (foldO (shapeRootLet (structEnv env)) (([] : List MachVal), st0) (shapeMid (structEnv env) p en).rootLets).run
        (wtab (structEnv env) n) = some (some (envs, st1)) ∧
      (shapeBody (shapeMid (structEnv env) p en) envs st1).run (wtab (structEnv env) n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid (structEnv env) p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size ∧
      FReachC nDecl ({} : MachRead) st0 ∧ FReachC nDecl st0 st1 ∧ FReachC nDecl st1 st ∧
      TrInv (structEnv env) nDecl st ∧
      ((shapeMid (structEnv env) p en).wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v)
def ExpRanges : Prop := ∀ {nDecl : Nat} {senv : StructEnv} {st : MachRead} (hTr : TrInv senv nDecl st),
    (∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) →
        InRange nDecl st j v ∧ NoLoose 0 v) ∧
    (∀ w ∈ st.ws, w.1 < st.kinds.size ∧ InRange nDecl st st.lets.size w.2) ∧
    (∀ d, st.dom = some d → InRange nDecl st st.lets.size d ∧ NoLoose 0 d)
def MutReach : Prop := ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape} {nDecl : Nat}
    (hT : TraceGood senv nDecl (readF senv n))
    (h : machineShapeF n sm ps ci senv ai = some (some sp))
    (hIn : ShapeInputs nDecl senv sm ps ci n),
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size ∧
      FReachC nDecl st0 st1 ∧ FReachC nDecl st1 st ∧
      TrInv senv nDecl st ∧
      ((shapeMid senv p en).wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v)
def MutReach2 : Prop := ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape} {nDecl : Nat}
    (hT : TraceGood senv nDecl (readF senv n))
    (h : machineShapeF n sm ps ci senv ai = some (some sp))
    (hIn : ShapeInputs nDecl senv sm ps ci n),
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size ∧
      FReachC nDecl ({} : MachRead) st0 ∧ FReachC nDecl st0 st1 ∧ FReachC nDecl st1 st ∧
      FullInv nDecl st ∧
      ((shapeMid senv p en).wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v)

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``MidInputs ``ExpMid
  checkExpected ``ShapeInputs ``ExpShapeInputs
  checkExpected ``ShapeCarry ``ExpCarry
  checkExpected ``shapeCarry_empty ``ExpEmpty
  checkExpected ``DomAtomic ``ExpDomAtomic
  checkExpected ``shapeStart_trace ``ExpStart
  checkExpected ``machineShapeF_reach ``ExpReach
  checkExpected ``machineShapeF_reach_of_premises ``ExpPrem
  checkExpected ``machineShapeF_ranges ``ExpRanges
  checkExpected ``shapeRootLet_trace ``ExpRootLet
  checkExpected ``rootLets_trace ``ExpRootLets
  checkExpected ``shapeBody_trace ``ExpBody
  logInfo m!"GEN5 SHAPECHECK TYPE 12 declarations compared"
  checkMutant ``MidInputs ``MutMid
  checkMutant ``ShapeCarry ``MutCarry
  checkMutant ``shapeStart_trace ``MutStart
  checkMutant ``machineShapeF_reach ``MutReach
  checkMutant ``machineShapeF_reach ``MutReach2
  checkMutant ``shapeRootLet_trace ``MutRootLet
  checkMutant ``rootLets_trace ``MutRootLets
  checkMutant ``shapeBody_trace ``MutBody
  logInfo m!"GEN5 SHAPECHECK MUTANT 8 statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``DomAtomic, ``shapeStart_trace, ``machineShapeF_reach, ``machineShapeF_reach_of_premises, ``machineShapeF_ranges, ``MidInputs, ``ShapeInputs, ``ShapeCarry, ``shapeCarry_empty, ``shapeRootLet_trace,
  ``rootLets_trace, ``shapeBody_trace]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 SHAPECHECK AXIOMS {newThms.length} declarations checked (standard axioms only)"

def closureRoots : List Name := newThms

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
    addDecl (.thmDecl { name := `ReaderTraceShapeCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceShapeCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceShapeCheck.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceShapeCheck.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceShapeCheck.direct, `ReaderTraceShapeCheck.viaHelper, `ReaderTraceShapeCheck.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 SHAPECHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 SHAPECHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceShapeCheck.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 SHAPECHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 SHAPECHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceShapeCheck.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceShapeCheck.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceShapeCheck.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceShapeCheck.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceShapeCheck.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceShapeCheck.Missing.nowhere do throwError "GEN5 SHAPECHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceShapeCheck.viaHelperU, `ReaderTraceShapeCheck.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceShapeCheck.Missing.nowhere do throwError "GEN5 SHAPECHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceShapeCheck.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 SHAPECHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 SHAPECHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 12 do throwError "GEN5 SHAPECHECK CLOSURE FAILED: expected 12 declarations"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 SHAPECHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 SHAPECHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 SHAPECHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 SHAPECHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 SHAPECHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (12 declarations); all 12 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceShapeCheck

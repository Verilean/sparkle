import Tools.ShippingGen5ReaderTraceDirect
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT: first draft.

/-! # DG-READERTRACE `shapeInputs_of_direct` checks (Tools/ShippingGen5ReaderTraceDirect.lean)

TYPE: the five condition `def`s (by VALUE) and the five theorems are compared by `checkExpected` against `Exp…` statements written here
(own spelling, conditions expanded inline where cheap), independently of the rev19 `#check` text.
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples). Positive controls: `lamDepth` on concrete terms by `rfl`.
The hypotheses (`DeclValuePh`, `PackTupleInputsBridge`, `RawNodePh`, `NormNodePh`, `CiDirect`, `DomAtomic`, `p.bs.length ≤ nDecl`, `ZeroLitAgrees0`,
`LiftAgrees`, `Inst1Agrees`) are not claimed true; none is registered in Tools/Assume. -/

namespace Tests.Gen5.ReaderTraceDirectCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5ReaderTracePack Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.ShippingReaderFuelShapeR5

section Expected

def ExpDeclValuePh : Lean.Environment → Prop := fun env =>
  ∀ (n : Lean.Name) (d : Lean.DefinitionVal), env.find? n = some (.defnInfo d) → NoPh d.value = true ∧ BvarLt 0 d.value = true
def ExpBridge : Prop := ∀ e : Lean.Expr, NoPh e = true → BvarLt 0 e = true →
  Sparkle.Compiler.MachTupleIn.packTupleInputs e = packTupleInputsF (lamDepth e) e
def ExpRawNodePh : StructEnv → Prop := fun senv =>
  ∀ (L : Nat) (f a e' : Lean.Expr), NoPh f = true → NoPh a = true → BvarLt L f = true → BvarLt L a = true →
    Sparkle.Compiler.MachRawSurface.rawNode senv.prodMatch (.app f a) = some e' → NoPh e' = true ∧ BvarLt L e' = true
def ExpNormNodePh : StructEnv → Prop := fun senv =>
  ∀ (L : Nat) (f a : Lean.Expr), NoPh f = true → NoPh a = true → BvarLt L f = true → BvarLt L a = true →
    NoPh (machNormNode senv (.app f a)) = true ∧ BvarLt L (machNormNode senv (.app f a)) = true
def ExpCiDirect : Lean.Environment → Lean.ConstantInfo → Prop := fun env ci => ∃ c : Lean.Name, env.find? c = some ci

def ExpUnpack : Prop := ∀ {L : Nat} (dom x : Lean.Expr) (ws : List Nat),
  (hdn : NoPh dom = true) → (hdb : BvarLt L dom = true) → (hxn : NoPh x = true) → (hxb : BvarLt L x = true) →
  NoPh (Sparkle.Compiler.MachTupleIn.unpackE dom ws x) = true ∧ BvarLt L (Sparkle.Compiler.MachTupleIn.unpackE dom ws x) = true
def ExpPackF : Prop := ∀ (hla : LiftAgrees) (hi1 : Inst1Agrees) (k L : Nat) (e : Lean.Expr),
  NoPh e = true → BvarLt L e = true → NoPh (packTupleInputsF k e) = true ∧ BvarLt L (packTupleInputsF k e) = true
def ExpAshr : Prop := ∀ {L : Nat} (dom x y : Lean.Expr) (n : Nat),
  (hdn : NoPh dom = true) → (hdb : BvarLt L dom = true) → (hxn : NoPh x = true) → (hxb : BvarLt L x = true) →
  (hyn : NoPh y = true) → (hyb : BvarLt L y = true) →
  NoPh (Sparkle.Compiler.MachSignOps.ashrE inlNatLit
      (fun m a b => machSigBin m ((machSigInst m).getD .anonymous) dom n a b) dom n x y) = true ∧
  BvarLt L (Sparkle.Compiler.MachSignOps.ashrE inlNatLit
      (fun m a b => machSigBin m ((machSigInst m).getD .anonymous) dom n a b) dom n x y) = true
def ExpNorm : Prop := ∀ (hi1 : Inst1Agrees) (senv : StructEnv)
  (hraw : ExpRawNodePh senv) (hnode : ExpNormNodePh senv) (n L : Nat) (e en : Lean.Expr),
  NoPh e = true → BvarLt L e = true → machNormF n senv e = some en → NoPh en = true ∧ BvarLt L en = true
def ExpDirect : Prop := ∀ (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : ExpDeclValuePh env) {ci : Lean.ConstantInfo} (hci : ExpCiDirect env ci)
    (hbr : ExpBridge) (hraw : ExpRawNodePh (structEnv env)) (hnode : ExpNormNodePh (structEnv env))
    {nDecl : Nat} {sm : Bool} {ps : List (String × Nat)} {n : Nat}
    (hdom : ∀ (p : ShapePre) (en : Lean.Expr),
      shapePre sm ps ci (structEnv env) = some p → machNormF n (structEnv env) p.e = some en →
      ∀ (dom αs ie b : Lean.Expr), (shapeMid (structEnv env) p en).run? = some (dom, αs, ie, b) →
        ((∃ j, dom = .bvar j) ∨ (∃ c ls, dom = .const c ls)))
    (hbs : ∀ p : ShapePre, shapePre sm ps ci (structEnv env) = some p → p.bs.length ≤ nDecl),
    ShapeInputs nDecl (structEnv env) sm ps ci n

-- mutants (single changes)
def MutDeclValuePh : Lean.Environment → Prop := fun env =>
  ∀ (n : Lean.Name) (d : Lean.DefinitionVal), env.find? n = some (.defnInfo d) → NoPh d.value = true ∧ BvarLt 1 d.value = true
def MutNormNodePh : StructEnv → Prop := fun senv =>
  ∀ (L : Nat) (f a : Lean.Expr), NoPh f = true → NoPh a = true → BvarLt L f = true → BvarLt L a = true →
    NoPh (machNormNode senv (.app f a)) = true
def MutCiDirect : Lean.Environment → Lean.ConstantInfo → Prop := fun env ci => ∃ c : Lean.Name, env.find? c = none
def MutPackF : Prop := ∀ (hla : LiftAgrees) (hi1 : Inst1Agrees) (k L : Nat) (e : Lean.Expr),
  NoPh e = true → BvarLt L e = true → NoPh (packTupleInputsF k e) = true ∧ BvarLt (L + 1) (packTupleInputsF k e) = true
def MutNorm : Prop := ∀ (hi1 : Inst1Agrees) (senv : StructEnv)
  (hraw : ExpRawNodePh senv) (hnode : ExpNormNodePh senv) (n L : Nat) (e en : Lean.Expr),
  NoPh e = true → BvarLt L e = true → machNormF n senv e = some en → NoPh en = true ∧ BvarLt 0 en = true
def MutDirectNoHla : Prop := ∀ (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : ExpDeclValuePh env) {ci : Lean.ConstantInfo} (hci : ExpCiDirect env ci)
    (hbr : ExpBridge) (hraw : ExpRawNodePh (structEnv env)) (hnode : ExpNormNodePh (structEnv env))
    {nDecl : Nat} {sm : Bool} {ps : List (String × Nat)} {n : Nat}
    (hdom : ∀ (p : ShapePre) (en : Lean.Expr),
      shapePre sm ps ci (structEnv env) = some p → machNormF n (structEnv env) p.e = some en →
      ∀ (dom αs ie b : Lean.Expr), (shapeMid (structEnv env) p en).run? = some (dom, αs, ie, b) →
        ((∃ j, dom = .bvar j) ∨ (∃ c ls, dom = .const c ls)))
    (hbs : ∀ p : ShapePre, shapePre sm ps ci (structEnv env) = some p → p.bs.length ≤ nDecl),
    ShapeInputs nDecl (structEnv env) sm ps ci n
def MutDirectNoHbs : Prop := ∀ (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : ExpDeclValuePh env) {ci : Lean.ConstantInfo} (hci : ExpCiDirect env ci)
    (hbr : ExpBridge) (hraw : ExpRawNodePh (structEnv env)) (hnode : ExpNormNodePh (structEnv env))
    {nDecl : Nat} {sm : Bool} {ps : List (String × Nat)} {n : Nat}
    (hdom : ∀ (p : ShapePre) (en : Lean.Expr),
      shapePre sm ps ci (structEnv env) = some p → machNormF n (structEnv env) p.e = some en →
      ∀ (dom αs ie b : Lean.Expr), (shapeMid (structEnv env) p en).run? = some (dom, αs, ie, b) →
        ((∃ j, dom = .bvar j) ∨ (∃ c ls, dom = .const c ls))),
    ShapeInputs nDecl (structEnv env) sm ps ci n

end Expected

-- positive controls (kernel evaluation of the twin's depth)
example : lamDepth (.lam `a (.bvar 0) (.lam `b (.bvar 1) (.bvar 0) .default) .default) = 2 := rfl
example : lamDepth (.bvar 0) = 0 := rfl

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``Tools.Assume.EnvDeclValue.DeclValuePh ``ExpDeclValuePh
  checkExpected ``Tools.Assume.PackTupleBridge.PackTupleInputsBridge ``ExpBridge
  checkExpected ``Tools.Assume.NormNodePh.RawNodePh ``ExpRawNodePh
  checkExpected ``Tools.Assume.NormNodePh.NormNodePh ``ExpNormNodePh
  checkExpected ``CiDirect ``ExpCiDirect
  checkExpected ``unpackE_ph ``ExpUnpack
  checkExpected ``packTupleInputsF_ph ``ExpPackF
  checkExpected ``ashrE_ph ``ExpAshr
  checkExpected ``machNormF_ph ``ExpNorm
  checkExpected ``shapeInputs_of_direct ``ExpDirect
  logInfo m!"GEN5 DIRECTCHECK TYPE 10 declarations compared"
  checkMutant ``Tools.Assume.EnvDeclValue.DeclValuePh ``MutDeclValuePh
  checkMutant ``Tools.Assume.NormNodePh.NormNodePh ``MutNormNodePh
  checkMutant ``CiDirect ``MutCiDirect
  checkMutant ``packTupleInputsF_ph ``MutPackF
  checkMutant ``machNormF_ph ``MutNorm
  checkMutant ``shapeInputs_of_direct ``MutDirectNoHla
  checkMutant ``shapeInputs_of_direct ``MutDirectNoHbs
  logInfo m!"GEN5 DIRECTCHECK MUTANT 7 statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"
  logInfo m!"GEN5 DIRECTCHECK COUNTS: TYPE 10 / MUTANT 7 / AXIOMS 10 / POSITIVE 2"

def newThms : List Name := [``unpackE_ph, ``packTupleInputsF_ph, ``ashrE_ph, ``machNormF_ph, ``shapeInputs_of_direct,
  ``Tools.Assume.EnvDeclValue.DeclValuePh, ``Tools.Assume.PackTupleBridge.PackTupleInputsBridge,
  ``Tools.Assume.NormNodePh.RawNodePh, ``Tools.Assume.NormNodePh.NormNodePh, ``CiDirect]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 DIRECTCHECK AXIOMS {newThms.length} declarations checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceDirectCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceDirectCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceDirectCheck.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceDirectCheck.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceDirectCheck.direct, `ReaderTraceDirectCheck.viaHelper, `ReaderTraceDirectCheck.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 DIRECTCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 DIRECTCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceDirectCheck.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 DIRECTCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 DIRECTCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceDirectCheck.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceDirectCheck.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceDirectCheck.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceDirectCheck.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceDirectCheck.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceDirectCheck.Missing.nowhere do throwError "GEN5 DIRECTCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceDirectCheck.viaHelperU, `ReaderTraceDirectCheck.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceDirectCheck.Missing.nowhere do throwError "GEN5 DIRECTCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceDirectCheck.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 DIRECTCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 DIRECTCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 10 do throwError "GEN5 DIRECTCHECK CLOSURE FAILED: expected 10 declarations"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 DIRECTCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 DIRECTCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 DIRECTCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 DIRECTCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 DIRECTCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (10 declarations); all 10 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceDirectCheck

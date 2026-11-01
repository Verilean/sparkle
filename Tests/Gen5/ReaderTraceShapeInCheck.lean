import Tools.ShippingGen5ReaderTraceShapeIn
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in Pod (kjob lake build Tests.Gen5.ReaderTraceShapeInCheck, exit 0; TYPE 9, MUTANT 5 signature/defeq rejections not semantic counterexamples, AXIOMS 9 standard only, CLOSURE OK 4845 constants from 9 roots, no sorryAx; 3 intended in-memory sorry negatives print warnings) on the tree of 179cbe7a16a15cb9610c070cbede717c7dcffc50 (Lean content identical; this header is comment-only). Clean build is the coder's. Checks for rev14 §2.3 U-R12c (structural NoPh/BvarLt lemmas through the preprocessing of shapeMid, MidPh, shapeInputs_of). No sorry / axiom / native_decide in source.
/-! # DG-READERTRACE U-R12c checks (Tools/ShippingGen5ReaderTraceShapeIn.lean)

TYPE: the two `def`s (by VALUE) and the seven theorems are compared by `checkExpected` against `Exp…` statements written here (own spelling).
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples). The hypotheses of `shapeInputs_of` (declaration value, `packTupleInputs`, `machNormF`, `DomAtomic`, `p.bs.length ≤ nDecl`, `ZeroLitAgrees0`, `RootFloatAgrees`) are not claimed true.
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceShapeInCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv
open Tools.ShippingLetsAliasInv

section Expected

def ExpLetsPh : Nat → List (Name × Lean.Expr × Lean.Expr) → Prop := fun L l =>
  ∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), l[k]? = some x → NoPh x.2.2 = true ∧ BvarLt (k + L) x.2.2 = true
def ExpMidPh : Nat → ShapeMid → Prop := fun L m =>
  (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), m.rootLets[k]? = some x → NoPh x.2.2 = true ∧ BvarLt (k + L) x.2.2 = true) ∧
  (∀ (dom αs ie b : Lean.Expr), m.run? = some (dom, αs, ie, b) →
      NoPh dom = true ∧ BvarLt (m.rootLets.length + L) dom = true ∧
      NoPh b = true ∧ BvarLt (m.rootLets.length + 1 + L) b = true) ∧
  (m.run? = none → NoPh m.root = true ∧ BvarLt (m.rootLets.length + L) m.root = true)
def ExpFold : Prop := ∀ {L : Nat} (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
    NoPh (inlFoldNat e) = true ∧ BvarLt L (inlFoldNat e) = true
def ExpLoop : Prop := ∀ {L : Nat} (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
    NoPh (machLoopAsLet e) = true ∧ BvarLt L (machLoopAsLet e) = true
def ExpPeel : Prop := ∀ {L : Nat} (e : Lean.Expr) (bs : List (Name × MixedGateBinder)) (b : Lean.Expr),
    mixedGatePeel e = some (bs, b) → NoPh e = true → BvarLt L e = true →
    NoPh b = true ∧ BvarLt (L + bs.length) b = true
def ExpZero : Prop := ∀ (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) {L : Nat} {e : Lean.Expr}
    (hn : NoPh e = true) (hb : BvarLt L e = true),
    NoPh (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? e) = true ∧
    BvarLt L (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? e) = true
def ExpRoot : Prop := ∀ {L : Nat} (projs : Name → Option (Name × Nat × Nat)) (e : Lean.Expr)
    (acc : List (Name × Lean.Expr × Lean.Expr)),
    NoPh e = true → BvarLt (L + acc.length) e = true →
    (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), acc.reverse[k]? = some x → NoPh x.2.2 = true ∧ BvarLt (k + L) x.2.2 = true) →
    (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), (machRoot projs e acc).1[k]? = some x →
        NoPh x.2.2 = true ∧ BvarLt (k + L) x.2.2 = true) ∧
    (∀ (dom αs ie b : Lean.Expr), (machRoot projs e acc).2.2.1.bind machRunApp? = some (dom, αs, ie, b) →
        NoPh dom = true ∧ BvarLt ((machRoot projs e acc).1.length + L) dom = true ∧
        NoPh b = true ∧ BvarLt ((machRoot projs e acc).1.length + 1 + L) b = true) ∧
    NoPh (machRoot projs e acc).2.2.2 = true ∧ BvarLt ((machRoot projs e acc).1.length + L) (machRoot projs e acc).2.2.2 = true
def ExpMid : Prop := ∀ (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hrf : RootFloatAgrees) (senv : StructEnv) (p : ShapePre)
    {en : Lean.Expr} {L : Nat} (hn : NoPh en = true) (hb : BvarLt L en = true), ExpMidPh L (shapeMid senv p en)
def ExpInputs : Prop := ∀ (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hrf : RootFloatAgrees)
    {nDecl : Nat} {senv : StructEnv} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {n : Nat}
    (hdecl : ∀ d, ci = ConstantInfo.defnInfo d → NoPh d.value = true ∧ BvarLt 0 d.value = true)
    (hpack : ∀ (L : Nat) (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
      NoPh (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true ∧
        BvarLt L (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true)
    (hnorm : ∀ (L : Nat) (e en : Lean.Expr), NoPh e = true → BvarLt L e = true → machNormF n senv e = some en →
      NoPh en = true ∧ BvarLt L en = true)
    (hdom : ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p → machNormF n senv p.e = some en →
      ∀ (dom αs ie b : Lean.Expr), (shapeMid senv p en).run? = some (dom, αs, ie, b) →
        ((∃ j, dom = .bvar j) ∨ (∃ c ls, dom = .const c ls)))
    (hbs : ∀ p : ShapePre, shapePre sm ps ci senv = some p → p.bs.length ≤ nDecl),
    ShapeInputs nDecl senv sm ps ci n

def MutFold : Prop := ∀ {L : Nat} (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
    NoPh (inlFoldNat e) = true ∧ BvarLt (L + 1) (inlFoldNat e) = true
def MutPeel : Prop := ∀ {L : Nat} (e : Lean.Expr) (bs : List (Name × MixedGateBinder)) (b : Lean.Expr),
    mixedGatePeel e = some (bs, b) → NoPh e = true → BvarLt L e = true →
    NoPh b = true ∧ BvarLt L b = true
def MutRoot : Prop := ∀ {L : Nat} (projs : Name → Option (Name × Nat × Nat)) (e : Lean.Expr)
    (acc : List (Name × Lean.Expr × Lean.Expr)),
    NoPh e = true → BvarLt (L + acc.length) e = true →
    (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), acc.reverse[k]? = some x → NoPh x.2.2 = true ∧ BvarLt (k + L) x.2.2 = true) →
    (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), (machRoot projs e acc).1[k]? = some x →
        NoPh x.2.2 = true ∧ BvarLt L x.2.2 = true) ∧
    (∀ (dom αs ie b : Lean.Expr), (machRoot projs e acc).2.2.1.bind machRunApp? = some (dom, αs, ie, b) →
        NoPh dom = true ∧ BvarLt ((machRoot projs e acc).1.length + L) dom = true ∧
        NoPh b = true ∧ BvarLt ((machRoot projs e acc).1.length + 1 + L) b = true) ∧
    NoPh (machRoot projs e acc).2.2.2 = true ∧ BvarLt ((machRoot projs e acc).1.length + L) (machRoot projs e acc).2.2.2 = true
def MutMidPh : Nat → ShapeMid → Prop := fun L m =>
  (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), m.rootLets[k]? = some x → NoPh x.2.2 = true ∧ BvarLt (k + L) x.2.2 = true) ∧
  (∀ (dom αs ie b : Lean.Expr), m.run? = some (dom, αs, ie, b) →
      NoPh dom = true ∧ BvarLt (m.rootLets.length + L) dom = true ∧
      NoPh b = true ∧ BvarLt (m.rootLets.length + L) b = true) ∧
  (m.run? = none → NoPh m.root = true ∧ BvarLt (m.rootLets.length + L) m.root = true)
def MutInputs : Prop := ∀ (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hrf : RootFloatAgrees)
    {nDecl : Nat} {senv : StructEnv} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {n : Nat}
    (hdecl : ∀ d, ci = ConstantInfo.defnInfo d → NoPh d.value = true ∧ BvarLt 0 d.value = true)
    (hpack : ∀ (L : Nat) (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
      NoPh (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true ∧
        BvarLt L (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true)
    (hnorm : ∀ (L : Nat) (e en : Lean.Expr), NoPh e = true → BvarLt L e = true → machNormF n senv e = some en →
      NoPh en = true ∧ BvarLt L en = true)
    (hbs : ∀ p : ShapePre, shapePre sm ps ci senv = some p → p.bs.length ≤ nDecl),
    ShapeInputs nDecl senv sm ps ci n

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``LetsPh ``ExpLetsPh
  checkExpected ``MidPh ``ExpMidPh
  checkExpected ``inlFoldNat_ph ``ExpFold
  checkExpected ``machLoopAsLet_ph ``ExpLoop
  checkExpected ``mixedGatePeel_ph ``ExpPeel
  checkExpected ``zeroLit_ph ``ExpZero
  checkExpected ``machRoot_ph ``ExpRoot
  checkExpected ``shapeMid_ph ``ExpMid
  checkExpected ``shapeInputs_of ``ExpInputs
  logInfo m!"GEN5 SHAPEINCHECK TYPE 9 declarations compared"
  checkMutant ``inlFoldNat_ph ``MutFold
  checkMutant ``mixedGatePeel_ph ``MutPeel
  checkMutant ``machRoot_ph ``MutRoot
  checkMutant ``MidPh ``MutMidPh
  checkMutant ``shapeInputs_of ``MutInputs
  logInfo m!"GEN5 SHAPEINCHECK MUTANT 5 statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``LetsPh, ``MidPh, ``inlFoldNat_ph, ``machLoopAsLet_ph, ``mixedGatePeel_ph, ``zeroLit_ph, ``machRoot_ph,
  ``shapeMid_ph, ``shapeInputs_of]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 SHAPEINCHECK AXIOMS {newThms.length} declarations checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceShapeInCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceShapeInCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceShapeInCheck.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceShapeInCheck.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceShapeInCheck.direct, `ReaderTraceShapeInCheck.viaHelper, `ReaderTraceShapeInCheck.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 SHAPEINCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 SHAPEINCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceShapeInCheck.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 SHAPEINCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 SHAPEINCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceShapeInCheck.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceShapeInCheck.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceShapeInCheck.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceShapeInCheck.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceShapeInCheck.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceShapeInCheck.Missing.nowhere do throwError "GEN5 SHAPEINCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceShapeInCheck.viaHelperU, `ReaderTraceShapeInCheck.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceShapeInCheck.Missing.nowhere do throwError "GEN5 SHAPEINCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceShapeInCheck.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 SHAPEINCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 SHAPEINCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 9 do throwError "GEN5 SHAPEINCHECK CLOSURE FAILED: expected 9 declarations"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 SHAPEINCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 SHAPEINCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 SHAPEINCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 SHAPEINCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 SHAPEINCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (9 declarations); all 9 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceShapeInCheck

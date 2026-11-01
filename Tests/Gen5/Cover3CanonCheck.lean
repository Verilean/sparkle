import Tools.ShippingGen5Cover3Canon
import Tests.Gen3.ExpectedType
set_option autoImplicit false
set_option linter.unusedVariables false
-- NOT BUILT (draft at 7f45fb24 + working tree; see the build line below once a build succeeds). No sorry / axiom / native_decide in source.
/-! # C.CV-1 canon units (Tools/ShippingGen5Cover3Canon.lean) checks, `scripts/gen5/CV1_CANON_FREEZE.md` §1 / §3 / §4

TYPE: each theorem is compared by `checkExpected` / `checkExpectedUnf` with an `Exp…` statement written here from the freeze text, spelled out without the new
definitions (`LetQuoteEqC` and `ReadsOfQuoteStmtC` are re-spelled; only `machCanonAp`, `machClose`, `machField`, `machPack`, `LooseOcc`, `quote`, and the Cover3
interface defs `ShapeAgree`/`FullInv`/`LetsNoLoose` are shared).
MUTANT: one-place changes, well-typed, rejected by the same comparer: a signature / defeq rejection, NOT a semantic counterexample.
POSITIVE / NEGATIVE: `LetQuoteEqC` is `Iff.rfl` to its re-spelling; the OLD `rowC_of_reader` type (with `LetQuoteEq`) is rejected as the type of `rowC_of_reader_canon`
(signature rejection only: it does not say `LetQuoteEq` is false anywhere).
AXIOMS: standard only. CLOSURE: value-closure walk with in-memory controls (no `sorry` token in this file). -/

namespace Tests.Gen5.Cover3CanonCheck
open Lean Meta Elab
open Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover3Canon Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingMixedSourceBridge Tools.ShippingUnifiedSource Tools.ShippingMachineAuto
open Sparkle.Compiler.MachInstOrigin
open Tools.ShippingGen5Cover2 (MentionsPh PhInRange)
open Tools.ShippingGen5Sem (kDOf callArgs callKind originOf cleanLets posOk)

section Expected

def ExpLetQuoteEqC (d : MachineData) (st : MachRead) : Prop :=
  ∀ (j : Nat) (hj : j < d.ls.length) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) →
    quote d.dom (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.bpos i))
                (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.vpos i)) (d.ls[j]'hj).2
      = machCanonAp (machClose st.insts.size st.kinds.size st.lets.size 0 v)

def ExpLetQuoteEqOld (d : MachineData) (st : MachRead) : Prop :=
  ∀ (j : Nat) (hj : j < d.ls.length) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) →
    quote d.dom (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.bpos i))
                (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.vpos i)) (d.ls[j]'hj).2
      = machClose st.insts.size st.kinds.size st.lets.size 0 v

def ExpLetsNoLoose (st : MachRead) : Prop :=
  ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ b, ¬ LooseOcc 0 v b

def ExpCanonClose : Prop := ∀ (kI n k d : Nat) (e : Lean.Expr),
    machCanonAp (machClose kI n k d e) = machClose kI n k d (machCanonAp e)

def MutCanonCloseDepth : Prop := ∀ (kI n k d : Nat) (e : Lean.Expr),
    machCanonAp (machClose kI n k d e) = machClose kI n k (d + 1) (machCanonAp e)

def ExpCanonField : Prop := ∀ (dom : Lean.Expr) (hdom : machCanonAp dom = dom)
    (kd : MixedGateBinder) (e : Lean.Expr),
    (machField dom kd e).map (fun p => (p.1, machCanonAp p.2)) = machField dom kd (machCanonAp e)

def MutCanonFieldNoDom : Prop := ∀ (dom : Lean.Expr)
    (kd : MixedGateBinder) (e : Lean.Expr),
    (machField dom kd e).map (fun p => (p.1, machCanonAp p.2)) = machField dom kd (machCanonAp e)

def ExpCanonPack : Prop := ∀ (dom : Lean.Expr) (hdom : machCanonAp dom = dom)
    (fs : List (Nat × Lean.Expr)),
    (machPack dom fs).map (fun p => (p.1, machCanonAp p.2)) = machPack dom (fs.map fun p => (p.1, machCanonAp p.2))

def ExpLooseCanon : Prop := ∀ (d : Nat) (e : Lean.Expr) (b : Nat), LooseOcc d (machCanonAp e) b ↔ LooseOcc d e b

def MutLooseCanonShift : Prop := ∀ (d : Nat) (e : Lean.Expr) (b : Nat), LooseOcc (d + 1) (machCanonAp e) b ↔ LooseOcc d e b

def ExpReadsOfQuoteStmtC : Prop :=
  ∀ (dom : Lean.Expr) (nDecl kI n k : Nat) (bpos vpos : Nat → Nat) (okP : Nat → Bool)
    {s : SType} (t : Term s) (v : Lean.Expr),
    PhInRange nDecl kI n k v →
    (∀ j, bpos j < nDecl + kI + n + k) → (∀ j, vpos j < nDecl + kI + n + k) →
    (∀ b, ¬ LooseOcc 0 v b) →
    quote dom (fun j => inputExpr (nDecl + kI + n + k) (bpos j))
      (fun j => inputExpr (nDecl + kI + n + k) (vpos j)) t = machCanonAp (machClose kI n k 0 v) →
    (∀ p, MentionPos nDecl kI n k v p → okP p = true) →
    Tools.ShippingMachineRef.reads (fun j => okP (bpos j)) (fun j => okP (vpos j)) t = true

/-- Mutant: the premise without `machCanonAp` (the OLD `readsOfQuoteStmt` statement). -/
def MutReadsOfQuoteStmtNoCanon : Prop :=
  ∀ (dom : Lean.Expr) (nDecl kI n k : Nat) (bpos vpos : Nat → Nat) (okP : Nat → Bool)
    {s : SType} (t : Term s) (v : Lean.Expr),
    PhInRange nDecl kI n k v →
    (∀ j, bpos j < nDecl + kI + n + k) → (∀ j, vpos j < nDecl + kI + n + k) →
    (∀ b, ¬ LooseOcc 0 v b) →
    quote dom (fun j => inputExpr (nDecl + kI + n + k) (bpos j))
      (fun j => inputExpr (nDecl + kI + n + k) (vpos j)) t = machClose kI n k 0 v →
    (∀ p, MentionPos nDecl kI n k v p → okP p = true) →
    Tools.ShippingMachineRef.reads (fun j => okP (bpos j)) (fun j => okP (vpos j)) t = true

def ExpFullInv (nDecl : Nat) (st : MachRead) : Prop := FullInv nDecl st

def ExpRowCCanon : Prop := ∀ {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv (kDOf d) st)
    (hqC : ExpLetQuoteEqC d st) (hnl : ExpLetsNoLoose st)
    (hb : ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length) (hv : ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length),
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true

/-- Mutant (negative control): the OLD premise `LetQuoteEq` (no `machCanonAp`). -/
def MutRowCOldPremise : Prop := ∀ {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv (kDOf d) st)
    (hqC : ExpLetQuoteEqOld d st) (hnl : ExpLetsNoLoose st)
    (hb : ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length) (hv : ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length),
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true

/-- Mutant: the conclusion drops `LetsNoLoose`. -/
def MutRowCNoNLCanon : Prop := ∀ {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv (kDOf d) st)
    (hqC : ExpLetQuoteEqC d st)
    (hb : ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length) (hv : ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length),
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true

end Expected

theorem letQuoteEqC_iff (d : MachineData) (st : MachRead) : LetQuoteEqC d st ↔ ExpLetQuoteEqC d st := Iff.rfl
theorem letsNoLoose_iff (st : MachRead) : LetsNoLoose st ↔ ExpLetsNoLoose st := Iff.rfl

def checkExpectedUnf (thm exp : Name) : MetaM Unit := do
  let ci ← getConstInfo thm
  let a ← whnfD ci.type
  let e ← stmtOf exp
  cmpTele s!"{thm}" a e
  logInfo m!"GEN3 TYPE OK (unfolded) {thm} against {exp}"

def checkMutantUnf (thm mt : Name) : MetaM Unit := do
  let ci ← getConstInfo thm
  let a ← whnfD ci.type
  let e ← stmtOf mt
  let accepted ← withoutModifyingState do
    try
      cmpTele s!"{thm} vs mutant {mt}" a e
      pure true
    catch _ => pure false
  if accepted then throwError "GEN3 MUTANT ACCEPTED: {mt} matches {thm}"
  logInfo m!"GEN3 MUTANT REJECTED {mt} (against {thm})"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``machCanonAp_machClose ``ExpCanonClose
  checkExpected ``machCanonAp_machField ``ExpCanonField
  checkExpected ``machCanonAp_machPack ``ExpCanonPack
  checkExpected ``looseOcc_machCanonAp ``ExpLooseCanon
  checkExpectedUnf ``readsOfQuoteStmtC ``ExpReadsOfQuoteStmtC
  checkExpected ``rowC_of_reader_canon ``ExpRowCCanon
  -- mutants (same comparer; signature / defeq rejection, not semantic counterexamples)
  checkMutant ``machCanonAp_machClose ``MutCanonCloseDepth
  checkMutant ``machCanonAp_machField ``MutCanonFieldNoDom
  checkMutant ``looseOcc_machCanonAp ``MutLooseCanonShift
  checkMutantUnf ``readsOfQuoteStmtC ``MutReadsOfQuoteStmtNoCanon
  checkMutant ``rowC_of_reader_canon ``MutRowCOldPremise
  checkMutant ``rowC_of_reader_canon ``MutRowCNoNLCanon
  logInfo m!"GEN5 COVER3CANON COUNTS: TYPE 6, MUTANT 6 (signature/defeq rejections, not semantic counterexamples), AXIOMS 9, CLOSURE controls 3 negative / 2 clean, UNKNOWN controls 3 negative / 1 clean"

def allThms : List Name :=
  [``machCanonAp_machClose, ``machCanonAp_machField, ``machCanonAp_machPack, ``looseOcc_machCanonAp, ``readsOfQuoteStmtC,
   ``rowC_of_reader_canon, ``letQuoteEqC_iff, ``letsNoLoose_iff, ``machCanonApNode_machClose]

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
    addDecl (.thmDecl { name := `Cover3CanonCtl.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `Cover3CanonCtl.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `Cover3CanonCtl.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `Cover3CanonCtl.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`Cover3CanonCtl.direct, `Cover3CanonCtl.viaHelper, `Cover3CanonCtl.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 COVER3CANON CLOSURE CONTROL FAILED: {n} not detected"
    for n in [`Cover3CanonCtl.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 COVER3CANON CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 COVER3CANON CLOSURE CONTROLS OK: 3 negative controls detected, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `Cover3CanonCtl.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `Cover3CanonCtl.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `Cover3CanonCtl.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `Cover3CanonCtl.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`Cover3CanonCtl.Missing.nowhere]
    unless unkRoot.contains `Cover3CanonCtl.Missing.nowhere do throwError "GEN5 COVER3CANON UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`Cover3CanonCtl.viaHelperU, `Cover3CanonCtl.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `Cover3CanonCtl.Missing.nowhere do throwError "GEN5 COVER3CANON UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`Cover3CanonCtl.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 COVER3CANON UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 COVER3CANON UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env allThms
  unless hits.isEmpty do throwError "GEN5 COVER3CANON CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "dataOf").length > 1 || (s.splitOn "native").length > 1 then
      throwError "GEN5 COVER3CANON CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 COVER3CANON CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 COVER3CANON CLOSURE OK: {seen.toList.length} constants, no forbidden constant"

#print axioms machCanonAp_machClose
#print axioms readsOfQuoteStmtC
#print axioms rowC_of_reader_canon

end Tests.Gen5.Cover3CanonCheck

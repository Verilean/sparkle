import Tools.ShippingGen5Cover2
import Tests.Gen3.ExpectedType
-- Built in g5cv-r4 at f921375b (Pod `kjob lake build`, exit 0; Cover2Check: TYPE 10, MUTANT 5, AXIOMS standard, CLOSURE OK with 3 negative / 2 clean controls). Clean build is the coder's. No sorry / axiom / native_decide in source.

/-! # DG-COVER rev2 preservation lemmas (Tools/ShippingGen5Cover2.lean) checks

TYPE: every theorem is compared (`checkExpected`) with an independently written `Expected…` statement, spelled out without the invariant definitions of
`Tools.ShippingGen5Cover2` (only the scanner primitives `MentionsPh` / `LetReach` are shared). MUTANT: one-place changes, well-typed, rejected by `checkMutant`
— a signature / defeq rejection, NOT a semantic counterexample. AXIOMS: standard axioms only. CLOSURE: a walk over the constants the unit mentions (types and
explicit values), rejecting `sorryAx` and the native-reduction axioms; exercised on negative controls built in memory (direct use, use through a helper in another
namespace, an opaque with an explicit value) and on unrelated clean controls. -/

namespace Tests.Gen5.Cover2Check
open Lean Meta Elab
open Tools.ShippingGen5Cover2 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingMixedSourceBridge

section Expected

/-- The four-clause invariant, spelled out. -/
def ExpInv (st : MachRead) : Prop :=
  (∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ i, MentionsPh "_machLet" i v → i < j) ∧
  (∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ m, MentionsPh "_machInst" m v → m < st.insts.size) ∧
  (∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) → ∀ a ∈ js, a < st.lets.size) ∧
  (∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) → ∀ a ∈ js, ∀ i, LetReach st.lets a i →
    ∀ (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[i]? = some (nm, kd, v) → ∀ m, MentionsPh "_machInst" m v → m < k)

def ExpEmpty : Prop := ∀ (st : MachRead) (hl : st.lets = #[]) (hi : st.insts = #[]), ExpInv st

def ExpPushInst : Prop := ∀ (st st' : MachRead) (c : Name) (js : List Nat) (r : MixedGateBinder),
  ExpInv st → (∀ a ∈ js, a < st.lets.size) → st' = { st with insts := st.insts.push (c, js, r) } → ExpInv st'

def ExpPushLet : Prop := ∀ (st st' : MachRead) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr),
  ExpInv st → (∀ i, MentionsPh "_machLet" i v → i < st.lets.size) → (∀ m, MentionsPh "_machInst" m v → m < st.insts.size) →
  st' = { st with lets := st.lets.push (nm, kd, v) } → ExpInv st'

def ExpReachPush : Prop := ∀ (lets : MachLets) (x : Name × MixedGateBinder × Lean.Expr)
    (hE : ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), lets[j]? = some (nm, kd, v) → ∀ i, MentionsPh "_machLet" i v → i < j)
    {a i : Nat} (h : LetReach (lets.push x) a i), a < lets.size → LetReach lets a i

def ExpReachLt : Prop := ∀ (lets : MachLets)
    (hE : ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), lets[j]? = some (nm, kd, v) → ∀ i, MentionsPh "_machLet" i v → i < j)
    {a i : Nat} (h : LetReach lets a i), a < lets.size → i < lets.size

def ExpLetPh : Prop := ∀ (st : MachRead) (h : ExpInv st) {j : Nat} {nm : Name} {kd : MixedGateBinder} {v : Lean.Expr}
  (hj : st.lets[j]? = some (nm, kd, v)) {k : Nat} (hk : j ≤ k), ∀ i, MentionsPh "_machLet" i v → i < k

def ExpInstPh : Prop := ∀ (st : MachRead) (h : ExpInv st) {j : Nat} {nm : Name} {kd : MixedGateBinder} {v : Lean.Expr}
  (hj : st.lets[j]? = some (nm, kd, v)) {kI : Nat} (hk : st.insts.size ≤ kI), ∀ m, MentionsPh "_machInst" m v → m < kI

def ExpPhRange : Prop := ∀ (st : MachRead) (h : ExpInv st) {j : Nat} {nm : Name} {kd : MixedGateBinder} {v : Lean.Expr}
  (hj : st.lets[j]? = some (nm, kd, v)) {nDecl kI n k : Nat} (hk : j ≤ k) (hkI : st.insts.size ≤ kI)
  (hin : ∀ i, MentionsPh "_machIn" i v → i < nDecl) (hsl : ∀ i, MentionsPh "_machSlot" i v → i < n),
  ((∀ i, MentionsPh "_machIn" i v → i < nDecl) ∧ (∀ j, MentionsPh "_machInst" j v → j < kI) ∧
   (∀ i, MentionsPh "_machSlot" i v → i < n) ∧ (∀ j, MentionsPh "_machLet" j v → j < k))

def ExpPhMono : Prop := ∀ {nDecl kI n k nDecl' kI' n' k' : Nat} {v : Lean.Expr}
  (h : (∀ i, MentionsPh "_machIn" i v → i < nDecl) ∧ (∀ j, MentionsPh "_machInst" j v → j < kI) ∧
   (∀ i, MentionsPh "_machSlot" i v → i < n) ∧ (∀ j, MentionsPh "_machLet" j v → j < k))
  (h1 : nDecl ≤ nDecl') (h2 : kI ≤ kI') (h3 : n ≤ n') (h4 : k ≤ k'),
  ((∀ i, MentionsPh "_machIn" i v → i < nDecl') ∧ (∀ j, MentionsPh "_machInst" j v → j < kI') ∧
   (∀ i, MentionsPh "_machSlot" i v → i < n') ∧ (∀ j, MentionsPh "_machLet" j v → j < k'))

def ExpSteps : Prop := ∀ {st0 st : MachRead} (h0 : ExpInv st0) (h : PushReach st0 st), ExpInv st

/-- Mutant: the invariant without the `ArgsExist` clause (the rev1 shape) as the premise of `PushLetPreserves`. -/
def MutPushLetNoArgsExist : Prop := ∀ (st st' : MachRead) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr),
  ((∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ i, MentionsPh "_machLet" i v → i < j) ∧
   (∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ m, MentionsPh "_machInst" m v → m < st.insts.size) ∧
   (∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) → ∀ a ∈ js, ∀ i, LetReach st.lets a i →
    ∀ (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[i]? = some (nm, kd, v) → ∀ m, MentionsPh "_machInst" m v → m < k)) →
  (∀ i, MentionsPh "_machLet" i v → i < st.lets.size) → (∀ m, MentionsPh "_machInst" m v → m < st.insts.size) →
  st' = { st with lets := st.lets.push (nm, kd, v) } → ExpInv st'

/-- Mutant: `PushInst` with the argument premise weakened to `a ≤ lets.size`. -/
def MutPushInstLe : Prop := ∀ (st st' : MachRead) (c : Name) (js : List Nat) (r : MixedGateBinder),
  ExpInv st → (∀ a ∈ js, a ≤ st.lets.size) → st' = { st with insts := st.insts.push (c, js, r) } → ExpInv st'

/-- Mutant: the let-range supplier with `k ≤ j`. -/
def MutLetPhRev : Prop := ∀ (st : MachRead) (h : ExpInv st) {j : Nat} {nm : Name} {kd : MixedGateBinder} {v : Lean.Expr}
  (hj : st.lets[j]? = some (nm, kd, v)) {k : Nat} (hk : k ≤ j), ∀ i, MentionsPh "_machLet" i v → i < k

/-- Mutant: the instance-range supplier with the bound `kI ≤ insts.size`. -/
def MutInstPhRev : Prop := ∀ (st : MachRead) (h : ExpInv st) {j : Nat} {nm : Name} {kd : MixedGateBinder} {v : Lean.Expr}
  (hj : st.lets[j]? = some (nm, kd, v)) {kI : Nat} (hk : kI ≤ st.insts.size), ∀ m, MentionsPh "_machInst" m v → m < kI

/-- Mutant: `PhInRange` monotonicity with the last bound reversed. -/
def MutPhMonoRev : Prop := ∀ {nDecl kI n k nDecl' kI' n' k' : Nat} {v : Lean.Expr}
  (h : (∀ i, MentionsPh "_machIn" i v → i < nDecl) ∧ (∀ j, MentionsPh "_machInst" j v → j < kI) ∧
   (∀ i, MentionsPh "_machSlot" i v → i < n) ∧ (∀ j, MentionsPh "_machLet" j v → j < k))
  (h1 : nDecl ≤ nDecl') (h2 : kI ≤ kI') (h3 : n ≤ n') (h4 : k' ≤ k),
  ((∀ i, MentionsPh "_machIn" i v → i < nDecl') ∧ (∀ j, MentionsPh "_machInst" j v → j < kI') ∧
   (∀ i, MentionsPh "_machSlot" i v → i < n') ∧ (∀ j, MentionsPh "_machLet" j v → j < k'))

end Expected

/-- `thm`'s type is a definition (a `Prop` statement such as `PushInstPreserves`): unfold the head constant, then compare binder by binder. -/
def checkExpectedUnf (thm exp : Name) : MetaM Unit := do
  let ci ← getConstInfo thm
  let a ← whnfD ci.type
  let e ← stmtOf exp
  cmpTele s!"{thm}" a e
  logInfo m!"GEN3 TYPE OK (unfolded) {thm} against {exp}"

/-- Mutant version of `checkExpectedUnf`: must be rejected. -/
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
  checkExpected ``callOrderInv_of_empty ``ExpEmpty
  checkExpectedUnf ``pushInst_preserves ``ExpPushInst
  checkExpectedUnf ``pushLet_preserves ``ExpPushLet
  checkExpected ``letReach_push ``ExpReachPush
  checkExpected ``letReach_lt ``ExpReachLt
  checkExpected ``letPh_lt_of_inv ``ExpLetPh
  checkExpected ``instPh_lt_of_inv ``ExpInstPh
  checkExpected ``phInRange_of_inv ``ExpPhRange
  checkExpected ``phInRange_mono ``ExpPhMono
  checkExpected ``callOrderInv_of_steps ``ExpSteps
  checkMutantUnf ``pushLet_preserves ``MutPushLetNoArgsExist
  checkMutantUnf ``pushInst_preserves ``MutPushInstLe
  checkMutant ``letPh_lt_of_inv ``MutLetPhRev
  checkMutant ``instPh_lt_of_inv ``MutInstPhRev
  checkMutant ``phInRange_mono ``MutPhMonoRev

-- Axiom audit (standard axioms only).
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``callOrderInv_of_empty, ``pushInst_preserves, ``pushLet_preserves, ``letReach_push, ``letReach_lt, ``letPh_lt_of_inv, ``instPh_lt_of_inv,
      ``phInRange_of_inv, ``phInRange_mono, ``callOrderInv_of_steps] do
    checkAxioms n

/-! ## Closure audit -/

/-- The value of a constant, for theorem / definition / opaque constants alike (`ConstantInfo.value?` skips opaques). -/
def valueOfCI : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- Walk the constants mentioned by `root`'s type and explicit value; unknown constants are recorded in the second component, not failed. -/
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
    addDecl (.thmDecl { name := `Cover2Ctl.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `Cover2Ctl.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `Cover2Ctl.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `Cover2Ctl.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`Cover2Ctl.direct, `Cover2Ctl.viaHelper, `Cover2Ctl.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 COVER2 CLOSURE CONTROL FAILED: {n} not detected"
    for n in [`Cover2Ctl.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 COVER2 CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 COVER2 CLOSURE CONTROLS OK: 3 negative controls detected, 2 unrelated clean controls clean"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let roots := [``callOrderInv_of_empty, ``pushInst_preserves, ``pushLet_preserves, ``letReach_push, ``letReach_lt, ``letPh_lt_of_inv, ``instPh_lt_of_inv,
      ``phInRange_of_inv, ``phInRange_mono, ``callOrderInv_of_steps]
  let (seen, unk, hits) ← closureHits env roots
  unless hits.isEmpty do throwError "GEN5 COVER2 CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "dataOf").length > 1 || (s.splitOn "native").length > 1 then
      throwError "GEN5 COVER2 CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do logInfo m!"GEN5 COVER2 CLOSURE: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 COVER2 CLOSURE OK: {seen.toList.length} constants, no forbidden constant"

#print axioms pushInst_preserves
#print axioms pushLet_preserves
#print axioms callOrderInv_of_steps

end Tests.Gen5.Cover2Check

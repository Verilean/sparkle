import Tools.ShippingGen5DataOfPure
import Tools.ShippingGen5T1ND
import Tests.Gen3.ExpectedType
set_option autoImplicit false
set_option linter.unusedVariables false
-- NOT BUILT (DG-DATAOF checks for Tools/ShippingGen5DataOfPure.lean; scripts/gen5/DG_DATAOF_FREEZE.md rev1).
-- No sorry / axiom / native_decide.

/-! # DG-DATAOF checks for the pure units (U-A, U-B, U-C)

1. TYPE: the statements of the pure lemmas against independently written, fully bound `Exp…` statements
   (binder names / binder info / types, `isDefEq` fallback logged), and the types of the four definitions.
2. MUTANT: changed statements are rejected by the same comparison. These are rejections by signature / defeq of a
   changed statement, NOT semantic counterexamples.
3. Concrete controls (kernel `decide`): `anyBeq`/`bitsBeq` accept equal terms and reject terms that differ only in the
   index (the width, or the split of a `concat` with the same total width).
4. Closure audit (reachable constants over explicit bodies): no `T1Hyp` / `T1HypND` field or recursor, no
   `Lean.Expr.equal` / `Lean.Expr.eqv`, no `Lean.ofReduceBool`. Opaque / body-less constants (including `partial`
   definitions, whose body is not explored) are COUNTED and reported, not claimed absent.
5. Axioms. -/

namespace Tests.Gen5.DataOfFixture
theorem badDec : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.dec
theorem badNDCases : True := (fun _ => trivial) @Tools.ShippingGen2.T1HypND.casesOn.{0}
theorem badEqual : True := (fun _ => trivial) @Lean.Expr.equal
theorem unrelated : True := trivial
end Tests.Gen5.DataOfFixture

namespace Tests.Gen5.DataOfCheck
open Lean Meta
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingGen5DataOfPure
open Tests.Gen3.ExpectedType

/-! ## 1. Expected types -/

def ExpTermsOfAnyFields : Prop :=
  ∀ (l : List (Σ s : SType, Term s)), (termsOfAny l).fields = l.map (fun t => toField t.1 t.2)

def ExpTermBeqSound : Prop :=
  ∀ {s : SType} (a : Term s) {s' : SType} (b : Term s'), termBeq a b = true → s = s' ∧ HEq a b

def ExpTermBeqRefl : Prop := ∀ {s : SType} (a : Term s), termBeq a a = true

def ExpAnyBeqEq : Prop :=
  ∀ {a b : Σ s : SType, Term s} (h : anyBeq a b = true), a = b

def ExpAnyBeqRefl : Prop := ∀ (a : Σ s : SType, Term s), anyBeq a a = true

def ExpBitsBeqEq : Prop :=
  ∀ {a b : Σ w : Nat, Term (.bits w)} (h : bitsBeq a b = true), a = b

def ExpBitsBeqRefl : Prop := ∀ (a : Σ w : Nat, Term (.bits w)), bitsBeq a a = true

def ExpBitsBeqWidth : Prop :=
  ∀ {a b : Σ w : Nat, Term (.bits w)} (h : bitsBeq a b = true), a.1 = b.1

def ExpInitOkOfOk : Prop :=
  ∀ (d : MachineData) (h : d.ok = true), d.initOk (initsOf d) = true

/-! ## 2. Mutants (signature / defeq rejections) -/

def MutAnyBeqIff : Prop :=
  ∀ {a b : Σ s : SType, Term s}, anyBeq a b = true ↔ a = b

def MutBitsBeqWidthOnly : Prop :=
  ∀ {a b : Σ w : Nat, Term (.bits w)} (h : bitsBeq a b = true), a.1 = b.1 ∧ True

def MutBitsBeqEqHEq : Prop :=
  ∀ {a b : Σ w : Nat, Term (.bits w)} (h : bitsBeq a b = true), HEq a b

def MutInitOkNoHyp : Prop :=
  ∀ (d : MachineData), d.initOk (initsOf d) = true

def MutInitOkConverse : Prop :=
  ∀ (d : MachineData) (h : d.initOk (initsOf d) = true), d.ok = true

def MutTermsReverse : Prop :=
  ∀ (l : List (Σ s : SType, Term s)), (termsOfAny l).fields = (l.map (fun t => toField t.1 t.2)).reverse

def MutTermBeqNoSort : Prop :=
  ∀ {s : SType} (a : Term s) {s' : SType} (b : Term s'), termBeq a b = true → HEq a b

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``termsOfAny_fields ``ExpTermsOfAnyFields
  checkExpected ``termBeq_sound ``ExpTermBeqSound
  checkExpected ``termBeq_refl ``ExpTermBeqRefl
  checkExpected ``anyBeq_eq ``ExpAnyBeqEq
  checkExpected ``anyBeq_refl ``ExpAnyBeqRefl
  checkExpected ``bitsBeq_eq ``ExpBitsBeqEq
  checkExpected ``bitsBeq_refl ``ExpBitsBeqRefl
  checkExpected ``bitsBeq_width ``ExpBitsBeqWidth
  checkExpected ``initOk_of_ok ``ExpInitOkOfOk
  checkMutant ``anyBeq_eq ``MutAnyBeqIff
  checkMutant ``bitsBeq_width ``MutBitsBeqWidthOnly
  checkMutant ``bitsBeq_eq ``MutBitsBeqEqHEq
  checkMutant ``initOk_of_ok ``MutInitOkNoHyp
  checkMutant ``initOk_of_ok ``MutInitOkConverse
  checkMutant ``termsOfAny_fields ``MutTermsReverse
  checkMutant ``termBeq_sound ``MutTermBeqNoSort

/-- Elaborate a type written as syntax. -/
def elabT (stx : Lean.Syntax) : MetaM Expr := Lean.Elab.Term.TermElabM.run' do
  let e ← Lean.Elab.Term.elabTerm stx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

-- The types of the definitions, by `isDefEq` against independently written types.
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let chk (n : Name) (e : Expr) : MetaM Unit := do
    let t := (← getConstInfo n).type
    unless ← isDefEq t e do throwError "DATAOF TYPE FAILED {n}"
    logInfo m!"DATAOF DEF TYPE OK {n}"
  chk ``anyBeq (← elabT (← `(term| (Σ s : SType, Term s) → (Σ s : SType, Term s) → Bool)))
  chk ``bitsBeq (← elabT (← `(term| (Σ w : Nat, Term (.bits w)) → (Σ w : Nat, Term (.bits w)) → Bool)))
  chk ``initsOf (← elabT (← `(term| (d : MachineData) → Sparkle.Core.HList (tys d.ss))))
  chk ``termsOfAny (← elabT (← `(term| (l : List (Σ s : SType, Term s)) → Terms (l.map (·.1)))))

/-! ## 3. Concrete controls -/

example : anyBeq ⟨.bool, .boolLit true⟩ ⟨.bool, .boolLit true⟩ = true := by decide
example : anyBeq ⟨.bool, .boolLit true⟩ ⟨.bool, .boolLit false⟩ = false := by decide
example : anyBeq ⟨.bool, .boolLit true⟩ ⟨.bits 1, .bitsLit 1 1⟩ = false := by decide
example : bitsBeq ⟨2, .bitsLit 2 1⟩ ⟨3, .bitsLit 3 1⟩ = false := by decide
example : bitsBeq ⟨1, .bitsInput 1 0⟩ ⟨2, .bitsInput 2 0⟩ = false := by decide
/-- Same total width 4, different split. -/
example : bitsBeq ⟨4, .concat (.bitsLit 1 0) (.bitsLit 3 0)⟩ ⟨4, .concat (.bitsLit 2 0) (.bitsLit 2 0)⟩ = false := by
  decide
example : bitsBeq ⟨4, .concat (.bitsLit 2 0) (.bitsLit 2 0)⟩ ⟨4, .concat (.bitsLit 2 0) (.bitsLit 2 0)⟩ = true := by
  decide
/-- A Bool `mux` is not the bit literal it packs from. -/
example : bitsBeq ⟨1, .mux (.boolLit true) (.bitsLit 1 1) (.bitsLit 1 0)⟩ ⟨1, .bitsLit 1 1⟩ = false := by decide

/-! ## 4. Closure audit -/

def forbidConsts : List Name :=
  [`Tools.ShippingGen2.T1Hyp.rec, `Tools.ShippingGen2.T1Hyp.casesOn, `Tools.ShippingGen2.T1Hyp.recOn,
   `Tools.ShippingGen2.T1HypND.rec, `Tools.ShippingGen2.T1HypND.casesOn, `Tools.ShippingGen2.T1HypND.recOn,
   `Lean.Expr.equal, `Lean.Expr.eqv, `Lean.ofReduceBool] ++
  (["pkg", "defines", "closes", "dec", "closed"].map fun f => (`Tools.ShippingGen2.T1Hyp).str f) ++
  (["pkg", "defines", "closes", "closed"].map fun f => (`Tools.ShippingGen2.T1HypND).str f)

def badProj (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .proj s _ _ => s == `Tools.ShippingGen2.T1Hyp || s == `Tools.ShippingGen2.T1HypND
    | _ => false).isSome

def body? : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

structure AReach where
  hit : Option (List Name) := none
  seen : NameSet := {}
  visited : Nat := 0
  noBody : Nat := 0
  opaques : Nat := 0
  opaqueNames : List Name := []

def reach (root : Name) (cap : Nat := 3000000) : MetaM AReach := do
  let env ← getEnv
  let mut out : AReach := { seen := ({} : NameSet).insert root }
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then throwError "DATAOF AUDIT INCOMPLETE at {root}"
    let some ci := env.find? c | continue
    let body := body? ci
    if body.isNone then out := { out with noBody := out.noBody + 1 }
    if ci matches .opaqueInfo _ then out := { out with opaques := out.opaques + 1, opaqueNames := c :: out.opaqueNames }
    if badProj ci.type || (body.map badProj).getD false then
      return { out with hit := some (path ++ [`rawProj]) }
    for u in ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[] do
      if forbidConsts.contains u then return { out with hit := some (path ++ [u]) }
      unless out.seen.contains u do
        out := { out with seen := out.seen.insert u }
        queue := queue.push (u, path ++ [u])
  return out

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  unless badProj (.proj `Tools.ShippingGen2.T1Hyp 3 (.bvar 0)) do throwError "DATAOF AUDIT FAILED: raw T1Hyp proj missed"
  if badProj (.proj ``Prod 0 (.bvar 0)) then throwError "DATAOF AUDIT FAILED: unrelated raw proj flagged"
  let F := `Tests.Gen5.DataOfFixture
  for (c, bad) in [(F ++ `badDec, true), (F ++ `badNDCases, true), (F ++ `badEqual, true), (F ++ `unrelated, false)] do
    let r ← reach c
    if bad && r.hit.isNone then throwError "DATAOF AUDIT FAILED: detector misses {c}"
    if !bad && r.hit.isSome then throwError "DATAOF AUDIT FAILED: detector flags {c}"
    logInfo m!"DATAOF CONTROL {c}: {toString r.hit}"
  for c in [``termsOfAny_fields, ``termBeq_sound, ``termBeq_refl, ``anyBeq_eq, ``anyBeq_refl, ``bitsBeq_eq,
      ``bitsBeq_refl, ``bitsBeq_width, ``initOk_of_ok] do
    let r ← reach c
    if let some p := r.hit then throwError "DATAOF AUDIT FAILED {c}: forbidden use via {p}"
    logInfo m!"DATAOF REACH {c}: no T1Hyp / T1HypND / Expr.equal / Expr.eqv / ofReduceBool; visited {r.visited}, body-less {r.noBody}, opaque {r.opaques} {r.opaqueNames} (an opaque or `partial` constant's body is NOT explored)"

/-! ## 5. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``termsOfAny_fields, ``termBeq_sound, ``termBeq_refl, ``anyBeq_eq, ``anyBeq_refl, ``bitsBeq_eq,
      ``bitsBeq_refl, ``bitsBeq_width, ``initOk_of_ok] do
    checkAxioms n

end Tests.Gen5.DataOfCheck

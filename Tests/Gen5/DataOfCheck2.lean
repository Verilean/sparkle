import Tools.ShippingGen5DataOfPure2
import Tests.Gen5.DataOfCheck
import Tests.Gen3.ExpectedType
set_option autoImplicit false
set_option linter.unusedVariables false
-- BUILT: clean issue-linked build do3v-62ea2479 exit 0 (758 jobs), scoped approved at 62ea2479 (no claim beyond U-D/U-E); re-verified after the shared DataOfCheck.reach unknown-name fail in the clean issue-linked build do5v-945fbe9a (exit 0, 762 jobs), scoped approved at 945fbe9a (DG-DATAOF checks for Tools/ShippingGen5DataOfPure2.lean; scripts/gen5/DG_DATAOF_FREEZE.md rev2).
-- No sorry / axiom / native_decide.

/-! # DG-DATAOF checks for U-D and U-E

1. TYPE against independently written fully bound statements.
2. MUTANT: changed statements rejected by the same comparison (signature / defeq rejections, NOT semantic counterexamples).
   Among them the old `toField_unField` (rev1) and the variant of `unField_sortOf` without the width hypothesis.
3. Kernel controls: the counterexample of the review (`k = .bits 8`, `f = ⟨16, bitsLit 16 0⟩`): `unField` returns
   a result and the re-pack equals `f`, but `sortOf k ≠ some t.1`; this is the reason `toField_unField` was withdrawn.
4. Closure audit (explicit walk, reuses `Tests.Gen5.DataOfCheck.reach`); opaque / body-less constants counted, not claimed absent.
5. Axioms. -/

namespace Tests.Gen5.DataOfCheck2
open Lean Meta
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineCommand
open Tools.ShippingMachineEntry Tools.ShippingReaderInputs Tools.ShippingGen5DataOfPure2
open Sparkle.IR.Machine Sparkle.Compiler.Elab
open Tests.Gen3.ExpectedType

/-! ## 1. Expected types -/

def ExpBposLEq : Prop := ∀ (ks : List MixedGateBinder),
    (((List.range ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) =>
      if pk.2 == .bool then some pk.1 else none) = posB 0 ks

def ExpVposLEq : Prop := ∀ (ks : List MixedGateBinder),
    (((List.range ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) =>
      match pk.2 with | .bits _ => some pk.1 | _ => none) = posV 0 ks

def ExpVwLEq : Prop := ∀ (ks : List MixedGateBinder),
    (((List.range ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) =>
      match pk.2 with | .bits w => some w | _ => none) = widV ks

def ExpSplitLetsSome : Prop :=
  ∀ {n : Nat} {t : Σ w : Nat, Term (.bits w)} {fs : List (Σ w : Nat, Term (.bits w))}
    {core : Σ w : Nat, Term (.bits w)},
    splitLets n t = some (fs, core) → fs.length = n ∧ t = packLets fs core.2

def ExpSplitFieldsSome : Prop :=
  ∀ {n : Nat} {t : Σ w : Nat, Term (.bits w)} {fs : List (Σ w : Nat, Term (.bits w))}
    (h : splitFields n t = some fs), 0 < n ∧ fs.length = n ∧ t = packAll fs

def ExpUnFieldBool : Prop :=
  ∀ {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s} (h : unField .bool f = some t),
    ∃ (w : Nat) (c : Term .bool) (a b : Term (.bits w)), f = ⟨w, .mux c a b⟩ ∧ t = ⟨.bool, c⟩

def ExpUnFieldBits : Prop :=
  ∀ {n w : Nat} {u : Term (.bits w)} {t : Σ s : SType, Term s} (h : unField (.bits n) ⟨w, u⟩ = some t),
    t = ⟨.bits w, u⟩

def ExpUnFieldDomain : Prop := ∀ {f : Σ w : Nat, Term (.bits w)}, unField .domain f = none

def ExpUnFieldBitsToField : Prop :=
  ∀ {n : Nat} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s} (h : unField (.bits n) f = some t),
    toField t.1 t.2 = f

def ExpUnFieldBitsSortOfIff : Prop :=
  ∀ {n : Nat} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s} (h : unField (.bits n) f = some t),
    (sortOf (.bits n) = some t.1 ↔ f.1 = n)

def ExpUnFieldSortOf : Prop :=
  ∀ {k : MixedGateBinder} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}
    (h : unField k f = some t) (hw : ∀ n, k = .bits n → f.1 = n), sortOf k = some t.1

def ExpUnFieldWidthOfSortOf : Prop :=
  ∀ {n : Nat} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}
    (h : unField (.bits n) f = some t) (hs : sortOf (.bits n) = some t.1), f.1 = n

def ExpUnFieldOutKindSort : Prop :=
  ∀ {o : OutField} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}
    (h : unField (outKind o) f = some t) (hw : o.width = (toField t.1 t.2).1), sortOf (outKind o) = some t.1

def ExpOkKNexts : Prop :=
  ∀ {d : MachineData} (h : d.ok = true), ∀ i, i < d.ss.length → d.K (d.nIn + i) = d.ss[i]?

def ExpOkLetsTyped : Prop :=
  ∀ {d : MachineData} (h : d.ok = true),
    LetsTyped d.bpos d.vpos d.kb d.kv d.vw d.K (d.nIn + d.ss.length) d.ls

def ExpOkOutsFit : Prop :=
  ∀ {d : MachineData} (h : d.ok = true),
    outsFitB d.kb d.kv d.vw d.fields d.shape.layout.outs d.outs = true

/-! ## 2. Mutants (signature / defeq rejections) -/

/-- The statement of rev1 (WITHDRAWN: false for `.bits n` binders, see §3). -/
def MutToFieldUnField : Prop :=
  ∀ {k : MixedGateBinder} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s},
    unField k f = some t → toField t.1 t.2 = f → sortOf k = some t.1

def MutUnFieldSortOfNoWidth : Prop :=
  ∀ {k : MixedGateBinder} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s},
    unField k f = some t → sortOf k = some t.1

def MutBitsSortOfIffOneWay : Prop :=
  ∀ {n : Nat} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s},
    unField (.bits n) f = some t → f.1 = n → sortOf (.bits n) = some t.1

def MutUnFieldBoolBranches : Prop :=
  ∀ {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}, unField .bool f = some t →
    ∃ (c : Term .bool), f = ⟨1, .mux c (.bitsLit 1 1) (.bitsLit 1 0)⟩ ∧ t = ⟨.bool, c⟩

def MutSplitLetsNoLength : Prop :=
  ∀ {n : Nat} {t : Σ w : Nat, Term (.bits w)} {fs : List (Σ w : Nat, Term (.bits w))}
    {core : Σ w : Nat, Term (.bits w)},
    splitLets n t = some (fs, core) → t = packLets fs core.2

def MutSplitFieldsZero : Prop :=
  ∀ {n : Nat} {t : Σ w : Nat, Term (.bits w)} {fs : List (Σ w : Nat, Term (.bits w))},
    splitFields n t = some fs → fs.length = n ∧ t = packAll fs

def MutBposLEqVpos : Prop := ∀ (ks : List MixedGateBinder),
    (((List.range ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) =>
      if pk.2 == .bool then some pk.1 else none) = posV 0 ks

def MutOkKNextsNoHyp : Prop :=
  ∀ (d : MachineData) (i : Nat), i < d.ss.length → d.K (d.nIn + i) = d.ss[i]?

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``bposL_eq ``ExpBposLEq
  checkExpected ``vposL_eq ``ExpVposLEq
  checkExpected ``vwL_eq ``ExpVwLEq
  checkExpected ``splitLets_some ``ExpSplitLetsSome
  checkExpected ``splitFields_some ``ExpSplitFieldsSome
  checkExpected ``unField_bool ``ExpUnFieldBool
  checkExpected ``unField_bits ``ExpUnFieldBits
  checkExpected ``unField_domain ``ExpUnFieldDomain
  checkExpected ``unField_bits_toField ``ExpUnFieldBitsToField
  checkExpected ``unField_bits_sortOf_iff ``ExpUnFieldBitsSortOfIff
  checkExpected ``unField_sortOf ``ExpUnFieldSortOf
  checkExpected ``unField_width_of_sortOf ``ExpUnFieldWidthOfSortOf
  checkExpected ``unField_outKind_sort ``ExpUnFieldOutKindSort
  checkExpected ``ok_K_nexts ``ExpOkKNexts
  checkExpected ``ok_letsTyped ``ExpOkLetsTyped
  checkExpected ``ok_outsFit ``ExpOkOutsFit
  checkMutant ``unField_sortOf ``MutToFieldUnField
  checkMutant ``unField_sortOf ``MutUnFieldSortOfNoWidth
  checkMutant ``unField_bits_sortOf_iff ``MutBitsSortOfIffOneWay
  checkMutant ``unField_bool ``MutUnFieldBoolBranches
  checkMutant ``splitLets_some ``MutSplitLetsNoLength
  checkMutant ``splitFields_some ``MutSplitFieldsZero
  checkMutant ``bposL_eq ``MutBposLEqVpos
  checkMutant ``ok_K_nexts ``MutOkKNextsNoHyp

/-! ## 3. Kernel controls: the counterexample to the withdrawn `toField_unField` -/

/-- `unField (.bits 8)` ignores the declared width 8 and returns the field at width 16. -/
example : unField (.bits 8) ⟨16, .bitsLit 16 0⟩ = some ⟨.bits 16, .bitsLit 16 0⟩ := rfl
/-- The re-pack reproduces the field (`hre` holds). -/
example : toField (SType.bits 16) (Term.bitsLit 16 0) = ⟨16, .bitsLit 16 0⟩ := rfl
/-- Yet the binder's sort is not the result's sort: the premise of `toField_unField` holds and its conclusion fails. -/
example : sortOf (.bits 8) ≠ some (SType.bits 16) := by decide
/-- With the matching width the iff's right side holds. -/
example : sortOf (.bits 16) = some (SType.bits 16) := rfl
/-- `unField .bool` accepts a mux with any width and any branches. -/
example : unField .bool ⟨4, .mux (.boolLit true) (.bitsLit 4 7) (.bitsLit 4 9)⟩ = some ⟨.bool, .boolLit true⟩ := rfl
/-- `unField .bool` refuses a non-mux field; `.domain` always refuses. -/
example : unField .bool ⟨1, .bitsLit 1 1⟩ = none := rfl
example : unField .domain ⟨1, .bitsLit 1 1⟩ = none := rfl
/-- `splitFields 0` is refused; `splitLets 0` is the identity split. -/
example : splitFields 0 ⟨1, .bitsLit 1 0⟩ = none := rfl
example : splitLets 0 ⟨1, .bitsLit 1 0⟩ = some ([], ⟨1, .bitsLit 1 0⟩) := rfl
/-- The position lists on a small kind list `[bool, bits 3, domain, bool]`. -/
example : posB 0 [.bool, .bits 3, .domain, .bool] = [0, 3] := rfl
example : posV 0 [.bool, .bits 3, .domain, .bool] = [1] := rfl
example : widV [.bool, .bits 3, .domain, .bool] = [3] := rfl

/-! ## 4. Closure audit -/

open Tests.Gen5.DataOfCheck in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for c in [``bposL_eq, ``vposL_eq, ``vwL_eq, ``splitLets_some, ``splitFields_some, ``unField_bool, ``unField_bits,
      ``unField_domain, ``unField_bits_toField, ``unField_bits_sortOf_iff, ``unField_sortOf,
      ``unField_width_of_sortOf, ``unField_outKind_sort, ``ok_K_nexts, ``ok_letsTyped, ``ok_outsFit] do
    let r ← reach c
    if let some p := r.hit then throwError "DATAOF2 AUDIT FAILED {c}: forbidden use via {p}"
    logInfo m!"DATAOF2 REACH {c}: no T1Hyp / T1HypND / Expr.equal / Expr.eqv / ofReduceBool; visited {r.visited}, body-less {r.noBody}, opaque {r.opaques} {r.opaqueNames} (an opaque or `partial` constant's body is NOT explored)"

/-! ## 5. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``bposL_eq, ``vposL_eq, ``vwL_eq, ``splitLets_some, ``splitFields_some, ``unField_bool, ``unField_bits,
      ``unField_domain, ``unField_bits_toField, ``unField_bits_sortOf_iff, ``unField_sortOf,
      ``unField_width_of_sortOf, ``unField_outKind_sort, ``ok_K_nexts, ``ok_letsTyped, ``ok_outsFit] do
    checkAxioms n

end Tests.Gen5.DataOfCheck2

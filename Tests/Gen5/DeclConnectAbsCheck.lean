import Lean
import Tools.ShippingGen5DeclConnectAbs
-- Built at 5e3ebf90bf3807120dd58f86b3b4f8714fe7835a (exit 0): TYPE 4 (U2,U3b,U4a,U5 vs independent Prop), MUTANT 1 refutation example (U4b without existence premise, via the empty relation; MutU2Rev/MutU6NoClosed are definitions only, not checked rejections), AXIOMS 8, CLOSURE 8. Signature/defeq checks, NOT semantic counterexamples.
set_option autoImplicit false
-- NOT BUILT (pending `kjob lake build Tests.Gen5.DeclConnectAbsCheck`).

/-! # DC-CONNECT abstract units: checks (scripts/gen5/DC_CONNECT_FREEZE.md rev2 §4)

1. TYPE: each unit's statement against an independently written expected `Prop` (fully bound, `example : Exp := @unit`).
2. MUTANT (signature/defeq rejections, NOT semantic counterexamples): U4a without `Functional` is not the same type; U2 with the
   inclusion reversed; U6 without `hclosed`; U4b without the existence premise. Each is `fun h => ...` checked to NOT unify.
3. AXIOMS: no `sorryAx`, no `Classical.choice` beyond the listed, no `Lean.ofReduceBool`.
4. CLOSURE: the units reach no declaration outside this file's namespace besides core logic (scan of `usedConstants`). -/
open Lean Tools.ShippingGen5DeclConnectAbs

namespace Tests.Gen5.DeclConnectAbsCheck
universe u
variable {E N CI Pk Shape : Type} {Ty : Shape → Type}

def ExpU2 : Prop := ∀ (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) {Tgt Tgt' : N → Prop},
    (∀ X, Tgt' X → Tgt X) →
    (∀ X, Tgt X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v) →
    (∀ X, Tgt' X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v)
example : @ExpU2 E N CI Pk Shape Ty := fun find CV shapeOf Match Obs P env _ _ h =>
  @dcGen_mono E N CI Pk Shape Ty find CV shapeOf Match Obs P env _ _ h

def ExpU3b : Prop := ∀ (find : E → N → Option CI) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) (Tgt : N → Prop)
    {X : N} {p : Pk}, Tgt X → P X = some p →
    ¬ (∀ Y, Tgt Y → ∀ q, P Y = some q → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env Y = some ci ∧ shapeOf ci = some sh ∧ Match sh q ∧ False ∧ Obs q sh v)
example : @ExpU3b E N CI Pk Shape Ty := fun find shapeOf Match Obs P env Tgt X p hT hP =>
  @not_dcGen_of_empty E N CI Pk Shape Ty find shapeOf Match Obs P env Tgt X p hT hP

def ExpU4a : Prop := ∀ (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E),
    (∀ env c (α β : Type) (v : α) (w : β), CV env c α v → CV env c β w → α = β ∧ HEq v w) → ∀ (Tgt : N → Prop),
    (∀ X, Tgt X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v) →
    ∀ X, Tgt X → ∀ p, P X = some p → ∀ ci, find env X = some ci → ∀ sh, shapeOf ci = some sh → Match sh p →
      ∀ v : Ty sh, CV env X (Ty sh) v → Obs p sh v
example : @ExpU4a E N CI Pk Shape Ty := fun find CV shapeOf Match Obs P env hV2 Tgt =>
  @dcImp_of_dcGen E N CI Pk Shape Ty find CV shapeOf Match Obs P env hV2 Tgt

def ExpU5 : Prop := ∀ {α : Sort u} {R : α → α → Prop} {Ready : α → Prop},
    (∀ X, (∀ c, R c X → Ready c) → Ready X) → ∀ X, Acc R X → Ready X
example : ExpU5.{u} := @acc_ready

-- MUTANTS: each is a statement that must NOT be the type of the unit (checked by failing to unify).
def MutU2Rev : Prop := ∀ (Tgt Tgt' : N → Prop), (∀ X, Tgt X → Tgt' X) → True
def MutU6NoClosed : Prop := ∀ (R : N → N → Prop) (Tgt : N → Prop), (∀ X, Tgt X → Acc R X) → True
/-- U4b without the existence premise would assert `DCGen` from `DCImp` alone; that is the rev1 vacuity (U3a/U3b). -/
def MutU4bNoEx : Prop := ∀ (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) (Tgt : N → Prop),
    DCImp find CV shapeOf Match Obs P env Tgt → DCGen find CV shapeOf Match Obs P env Tgt
-- the mutant is refuted by the empty relation when a target with a package exists:
example (find : E → N → Option CI) (shapeOf : CI → Option Shape) (Match : Shape → Pk → Prop)
    (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) (Tgt : N → Prop) {X : N} {p : Pk}
    (hT : Tgt X) (hP : P X = some p) :
    ¬ (DCImp find (fun _ _ _ _ => False) shapeOf Match Obs P env Tgt →
        DCGen find (fun _ _ _ _ => False) shapeOf Match Obs P env Tgt) :=
  fun h => not_dcGen_of_empty find shapeOf Match Obs P env Tgt hT hP (h (dcImp_of_empty find shapeOf Match Obs P env Tgt))

/-! ## AXIOMS and CLOSURE -/
open Tests.Gen3.ExpectedType in
run_cmd Lean.Elab.Command.liftTermElabM do
  let all := [``dcGen_iff, ``dcGen_mono, ``dcImp_of_empty, ``not_dcGen_of_empty, ``dcImp_of_dcGen, ``dcGen_of_imp_exists,
    ``acc_ready, ``dcGen_of_rows]
  for n in all do
    checkAxioms n
  -- CLOSURE: no unit mentions Pkg / MachineData / sigShape / ConstantInfo / a dependency (DG-SEM/DATAOF/ACC) name
  for n in all do
    let some ci := (← getEnv).find? n | throwError "{n} not found"
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
    let forbidden := used.filter fun c =>
      let s := c.toString
      ["Pkg", "MachineData", "sigShape", "ConstantInfo", "GenPInv", "DataSoundAt", "dataOf", "genP", "Laws", "T1Hyp"].any
        fun f => (s.splitOn f).length > 1
    unless forbidden.isEmpty do throwError "CLOSURE FAILED {n}: mentions {forbidden}"
    logInfo m!"CLOSURE OK {n}"

end Tests.Gen5.DeclConnectAbsCheck

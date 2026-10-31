import Lean
import Tools.ShippingGen5DeclConnectAbs
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- U-UNIV (Pk : Type u) re-built at cef857c6 (agent build exit 0; TYPE 8/MUTANT 8/U-UNIV/AXIOMS 8/CLOSURE 8 + controls). Previous: Built at b7e3ffcfd51128188d90f788b563aae4d5cbde02 (kjob lake build Tests.Gen5.DeclConnectAbsCheck, exit 0, agent build; clean issue-linked build is the coder's). rev3 audit: TYPE 8 + MUTANT 8 (one-change well-typed, each executed and rejected by defeq), AXIOMS 8, CLOSURE 8 (transitive ConstantInfo walk) + 4 controls. Previous 5e3ebf90 ran only 4 TYPE examples + 1 refutation; MutU2Rev/MutU6NoClosed there were never run (removed). Signature/defeq checks, NOT semantic counterexamples.
-- rev3 runs: TYPE (8 independent Expected, defeq), MUTANT (8 one-change well-typed mutants, each must NOT be defeq), AXIOMS 8, CLOSURE (transitive ConstantInfo walk + 4 negative controls). Signature/defeq checks, NOT semantic counterexamples.

/-! # DC-CONNECT abstract units: checks (scripts/gen5/DC_CONNECT_FREEZE.md rev3 §4.1)

1. TYPE: each theorem's type is compared (`isDefEq`) with an independently written, fully unfolded `Prop` (`ExpU*`). Positive control of the MUTANT step.
2. MUTANT (signature/defeq rejections, NOT semantic counterexamples): per theorem one well-typed `MutU*` differing from `ExpU*` in one place; the same comparison must fail.
   U6's `_hclosed` is unused in the proof; nothing here claims its removal is unprovable.
3. AXIOMS: `checkAxioms` on each theorem.
4. CLOSURE: transitive walk over the `ConstantInfo` bodies (thm/defn value + types; opaque/axiom are untracked boundaries) with negative controls. -/
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

/-- one change: the inclusion is reversed (`Tgt X → Tgt' X`). -/
def MutU2 : Prop := ∀ (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) {Tgt Tgt' : N → Prop},
    (∀ X, Tgt X → Tgt' X) →
    (∀ X, Tgt X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v) →
    (∀ X, Tgt' X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v)

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

/-! ## Independent Expected statements (TYPE) and one-change mutants (MUTANT)
Each mentions all six section variables `E N CI Pk Shape Ty`, so `ExpU* ` takes them as its leading binders. -/

def ExpU1 : Prop := ∀ (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) (Tgt : N → Prop),
    (∀ X, Tgt X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v) ↔ (∀ X, Tgt X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v)
/-- one change: `∀ X` on the right becomes `∃ X, … ∧`. -/
def MutU1 : Prop := ∀ (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) (Tgt : N → Prop),
    (∀ X, Tgt X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v) ↔ (∃ X, Tgt X ∧ (∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v))

def ExpU3a : Prop := ∀ (find : E → N → Option CI) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) (Tgt : N → Prop),
    ∀ X, Tgt X → ∀ p, P X = some p → ∀ ci, find env X = some ci → ∀ sh, shapeOf ci = some sh → Match sh p →
      ∀ v : Ty sh, False → Obs p sh v
/-- one change: the conclusion is the existence (`DCGen`) shape instead of the implication shape. -/
def MutU3a : Prop := ∀ (find : E → N → Option CI) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) (Tgt : N → Prop),
    ∀ X, Tgt X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ False ∧ Obs p sh v

/-- one change: `¬` dropped. -/
def MutU3b : Prop := ∀ (find : E → N → Option CI) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) (Tgt : N → Prop)
    {X : N} {p : Pk}, Tgt X → P X = some p →
    (∀ Y, Tgt Y → ∀ q, P Y = some q → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env Y = some ci ∧ shapeOf ci = some sh ∧ Match sh q ∧ False ∧ Obs q sh v)

/-- one change: the `Functional` premise dropped. -/
def MutU4a : Prop := ∀ (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) (Tgt : N → Prop),
    (∀ X, Tgt X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v) →
    ∀ X, Tgt X → ∀ p, P X = some p → ∀ ci, find env X = some ci → ∀ sh, shapeOf ci = some sh → Match sh p →
      ∀ v : Ty sh, CV env X (Ty sh) v → Obs p sh v

def ExpU4b : Prop := ∀ (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) (Tgt : N → Prop),
    (∀ X, Tgt X → ∀ p, P X = some p → ∀ ci, find env X = some ci → ∀ sh, shapeOf ci = some sh → Match sh p →
      ∀ v : Ty sh, CV env X (Ty sh) v → Obs p sh v) →
    (∀ X, Tgt X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v) →
    (∀ X, Tgt X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v)
/-- one change: the existence premise dropped. -/
def MutU4b : Prop := ∀ (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) (Tgt : N → Prop),
    (∀ X, Tgt X → ∀ p, P X = some p → ∀ ci, find env X = some ci → ∀ sh, shapeOf ci = some sh → Match sh p →
      ∀ v : Ty sh, CV env X (Ty sh) v → Obs p sh v) →
    (∀ X, Tgt X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v)

/-- one change: `R c X` reversed to `R X c` in the step premise. -/
def MutU5 : Prop := ∀ {α : Sort u} {R : α → α → Prop} {Ready : α → Prop},
    (∀ X, (∀ c, R X c → Ready c) → Ready X) → ∀ X, Acc R X → Ready X

def ExpU6 : Prop := ∀ (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) (Tgt : N → Prop) {R : N → N → Prop},
    (∀ X, Tgt X → Acc R X) → (∀ X c, Tgt X → R c X → Tgt c) →
    (∀ X, Tgt X → (∀ c, R c X → Tgt c → (∀ p, P c = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env c = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env c (Ty sh) v ∧ Obs p sh v)) → (∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v)) →
    (∀ X, Tgt X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v)
/-- one change: `hAcc` dropped. -/
def MutU6 : Prop := ∀ (find : E → N → Option CI) (CV : E → N → (α : Type) → α → Prop) (shapeOf : CI → Option Shape)
    (Match : Shape → Pk → Prop) (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) (Tgt : N → Prop) {R : N → N → Prop},
    (∀ X c, Tgt X → R c X → Tgt c) →
    (∀ X, Tgt X → (∀ c, R c X → Tgt c → (∀ p, P c = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env c = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env c (Ty sh) v ∧ Obs p sh v)) → (∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v)) →
    (∀ X, Tgt X → ∀ p, P X = some p → ∃ (ci : CI) (sh : Shape) (v : Ty sh),
      find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v)

/-- U4b without the existence premise would assert `DCGen` from `DCImp` alone (the rev1 vacuity); refuted by the empty relation: -/
example (find : E → N → Option CI) (shapeOf : CI → Option Shape) (Match : Shape → Pk → Prop)
    (Obs : Pk → (sh : Shape) → Ty sh → Prop) (P : N → Option Pk) (env : E) (Tgt : N → Prop) {X : N} {p : Pk}
    (hT : Tgt X) (hP : P X = some p) :
    ¬ (DCImp find (fun _ _ _ _ => False) shapeOf Match Obs P env Tgt →
        DCGen find (fun _ _ _ _ => False) shapeOf Match Obs P env Tgt) :=
  fun h => not_dcGen_of_empty find shapeOf Match Obs P env Tgt hT hP (h (dcImp_of_empty find shapeOf Match Obs P env Tgt))

/-- U-UNIV: `Pk` may live in `Type 1` (`Pkg ι dom : Type 1`); instantiating it with `Type` must elaborate. -/
def univProbe := @dcGen_mono Unit Unit Unit Type Unit (fun _ => Unit)

/-! ## Meta-level checks -/
open Meta in
/-- the theorem's type after its first `n` (implicit type) binders, versus `exp` applied to those binders. -/
def sameType (thm exp : Name) (n : Nat) : MetaM Bool := do
  let T ← inferType (← mkConstWithFreshMVarLevels thm)
  forallBoundedTelescope T (some n) fun xs body => do
    isDefEq body (mkAppN (← mkConstWithFreshMVarLevels exp) xs)

/-- reachability over ConstantInfo bodies. `opaqueInfo`/`axiomInfo` bodies are NOT followed (untracked boundary). -/
structure Reach where
  seen : NameSet := {}
  opaques : Array Name := #[]
  axioms : Array Name := #[]

partial def walk (env : Environment) (n : Name) : StateM Reach Unit := do
  if (← get).seen.contains n then return
  modify fun s => { s with seen := s.seen.insert n }
  let some ci := env.find? n | return
  let refs : Array Name := match ci with
    | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .opaqueInfo v => v.type.getUsedConstants
    | .axiomInfo v => v.type.getUsedConstants
    | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray
    | .ctorInfo v => v.type.getUsedConstants
    | .recInfo v => v.type.getUsedConstants
    | .quotInfo v => v.type.getUsedConstants
  match ci with
  | .opaqueInfo _ => modify fun s => { s with opaques := s.opaques.push n }
  | .axiomInfo _ => modify fun s => { s with axioms := s.axioms.push n }
  | _ => pure ()
  for r in refs do walk env r

def reach (env : Environment) (n : Name) : Reach := ((walk env n).run {}).2

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

def isCoreMod (m : Name) : Bool := [`Init, `Std, `Lean].any (·.isPrefixOf m)

def forbiddenFragments : List String :=
  ["Pkg", "MachineData", "sigShape", "ConstantInfo", "GenPInv", "DataSoundAt", "dataOf", "genP", "Laws", "T1Hyp"]

/-- Reached constants outside the allowed set. `allowCurrent` lets the Check file's own helpers pass the module test
(used only for the negative controls, so that the name test must find them through the walk). -/
def violations (env : Environment) (r : Reach) (allowCurrent : Bool) : Array Name :=
  r.seen.toList.foldl (init := #[]) fun acc n =>
    let nonCore := match moduleOf env n with
      | some m => !isCoreMod m
      | none => true
    let badMod := match moduleOf env n with
      | some m => !isCoreMod m && m != `Tools.ShippingGen5DeclConnectAbs
      | none => !allowCurrent
    let s := n.toString
    let badName := nonCore && forbiddenFragments.any fun f => (s.splitOn f).length > 1
    if badMod || badName then acc.push n else acc

-- Negative-control declarations (they live in this file, hence "current module").
def Foreign.PkgInner : Prop := True
def Foreign.wrapA : Prop := Foreign.PkgInner
theorem Foreign.lemmaA : Foreign.PkgInner := trivial
opaque Foreign.opq : Nat
theorem negDirect : Foreign.PkgInner := trivial
theorem negViaDef : Foreign.wrapA := trivial
theorem negViaThm : True := by
  have _h := Foreign.lemmaA
  trivial
theorem negOpaque : Foreign.opq = Foreign.opq := rfl

/-! ## Run -/
open Tests.Gen3.ExpectedType in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  -- TYPE and MUTANT: (theorem, Exp, Mut, number of leading implicit type binders)
  let table : List (Name × Name × Name × Nat) :=
    [(``dcGen_iff, ``ExpU1, ``MutU1, 6), (``dcGen_mono, ``ExpU2, ``MutU2, 6), (``dcImp_of_empty, ``ExpU3a, ``MutU3a, 6),
     (``not_dcGen_of_empty, ``ExpU3b, ``MutU3b, 6), (``dcImp_of_dcGen, ``ExpU4a, ``MutU4a, 6),
     (``dcGen_of_imp_exists, ``ExpU4b, ``MutU4b, 6), (``acc_ready, ``ExpU5, ``MutU5, 0), (``dcGen_of_rows, ``ExpU6, ``MutU6, 6)]
  for (thm, e, m, k) in table do
    unless ← sameType thm e k do throwError "TYPE FAILED {thm} vs {e}"
    logInfo m!"TYPE OK {thm}"
    if ← sameType thm m k then throwError "MUTANT NOT REJECTED {m} (same type as {thm})"
    logInfo m!"MUTANT REJECTED {m} (signature/defeq, not a semantic counterexample)"
  -- U-UNIV: the six unit statements carrying `Pk` are universe-polymorphic in it
  for n in [``dcGen_iff, ``dcGen_mono, ``dcImp_of_empty, ``not_dcGen_of_empty, ``dcImp_of_dcGen, ``dcGen_of_imp_exists, ``dcGen_of_rows] do
    unless (← getConstInfo n).levelParams.length == 1 do throwError "U-UNIV: {n} is not universe-polymorphic in Pk"
  logInfo m!"U-UNIV OK (7 statements with Pk : Type u; univProbe instantiates Pk := Type)"
  -- AXIOMS
  let all := table.map (·.1)
  for n in all do
    checkAxioms n
  -- CLOSURE, positive
  for n in all do
    let r := reach env n
    let v := violations env r false
    unless v.isEmpty do throwError "CLOSURE FAILED {n}: {v}"
    logInfo m!"CLOSURE OK {n}: reached {r.seen.size} constants, untracked opaque {r.opaques}, axioms {r.axioms}"
  -- the walk descends into definition bodies (DCAt is reached from dcGen_mono only through DCGen's body)
  unless (reach env ``dcGen_mono).seen.contains ``DCAt do throwError "WALK does not enter defn bodies"
  logInfo m!"CLOSURE WALK-DEPTH OK (DCAt reached from dcGen_mono through DCGen)"
  -- CLOSURE, negative controls: direct; through a helper definition body; through a helper theorem body
  for (c, why) in [(``negDirect, "direct"), (``negViaDef, "through a helper definition's body"),
                   (``negViaThm, "through a helper theorem's body")] do
    let v := violations env (reach env c) true
    if v.isEmpty then throwError "CLOSURE CONTROL NOT DETECTED {c} ({why})"
    logInfo m!"CLOSURE CONTROL DETECTED {c} ({why}): {v}"
  -- `Foreign.wrapA` has no forbidden fragment in its name: it is found only because the walk follows its body
  unless (violations env (reach env ``negViaDef) true).contains ``Foreign.PkgInner do throwError "negViaDef not found via PkgInner"
  let ro := reach env ``negOpaque
  unless ro.opaques.contains ``Foreign.opq do throwError "CLOSURE opaque boundary not reported"
  logInfo m!"CLOSURE CONTROL DETECTED negOpaque as untracked boundary: {ro.opaques}"

end Tests.Gen5.DeclConnectAbsCheck

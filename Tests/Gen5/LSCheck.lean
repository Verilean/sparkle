import Tools.ShippingGen5ConstValueELS
import Tools.ShippingGen5FG
set_option autoImplicit false
-- D.D-4 LS: structural check that `CVLS PT` is a `ConstValueRel` with no extra hypothesis, negative controls, `#print axioms`.

namespace Tests.Gen5.LSCheck
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG

/-! ## Structural match: `CVLS PT` has the type `ConstValueRel`, for every `PT`; the functionality needs no hypothesis -/
example (PT : PrimTable) : ConstValueRel := CVLS PT
example (PT : PrimTable) : ConstValueRel := fun env X α v => ConstValueEAt PT env X (LS env X) α v
example : ∀ PT : PrimTable, ConstValueFunctional (CVLS PT) := fun PT env X _ _ _ _ h h' => cvls_functional PT env X h h'
example : ∀ (PT : PrimTable) (env : Environment) (X : Name) {α β : Type} {v : α} {w : β},
    CVLS PT env X α v → CVLS PT env X β w → α = β ∧ HEq v w := cvls_functional

/-! ## Negative controls -/
/-- `ConstValueFunctional` is not trivial: the full relation is not functional (same type, different values). -/
example (env : Environment) : ¬ ConstValueFunctional (fun _ _ _ _ => True) := fun h =>
  absurd (eq_of_heq (h env `x Nat Nat 0 1 trivial trivial).2) (by decide)

-- `LS` follows the declaration's `levelParams` (not `[]` always): checked on real constants. -/
run_meta do
  let env ← getEnv
  unless (LS env ``List).length == 1 && (LS env ``Nat).isEmpty && (LS env `no.such.constant).isEmpty do
    throwError "LS: unexpected length"
  unless (LS env ``PProd).length == 2 && LS env ``List == [Level.zero] do throwError "LS: unexpected value"
  logInfo m!"LS controls ok: List {LS env ``List}, PProd {LS env ``PProd}, Nat {LS env ``Nat}"

-- The length lemma is not vacuous: it gives a nonempty list for a polymorphic constant. -/
run_meta do
  let env ← getEnv
  let some ci := env.find? ``List | throwError "List absent"
  unless ci.levelParams.length == 1 do throwError "List levelParams"

end Tests.Gen5.LSCheck

#print axioms Tools.ShippingGen5ConstValueE.cvls_functional
#print axioms Tools.ShippingGen5ConstValueE.LS_length
#print axioms Tools.ShippingGen5ConstValueE.LS_none
#print axioms Tools.ShippingGen5ConstValueE.CVLS

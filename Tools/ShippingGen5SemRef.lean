import Tools.ShippingMachineSource
set_option autoImplicit false
-- Built in g5sm-r2 at d5492921 (Pod `kjob lake build`, exit 0; SemUnitsCheck: TYPE 6, MUTANT 5, AXIOMS standard). No sorry / axiom / native_decide.
-- No sorry / axiom / native_decide.

/-! # DG-SEM P1 / P2: the pending-write and live-state packing, for ANY slot list `αs`

Pure statements about the Signal library (`Tools.ShippingMachineSource.valsAt`, `Circuit.SigList`, `mkHolds`); no
`MachineData`, no `dataOf`, no `GenIn`. Class **I** of `scripts/gen5/DG_SEM_FREEZE_REV2.md` §6.

* `sigListOfFn αs f` packs a function of time with values in `HList αs` into one pending-write Signal per slot.
* **P1** `valsAt_sigListOfFn`: `valsAt αs (sigListOfFn αs f) t = f t`.
* `reconState αs holds` is the state Signal whose value at `t` is `valsAt αs holds t`.
* **P2** `reconState_mkHolds`: `reconState αs (mkHolds αs S) = S` (and the pointwise form `valsAt_mkHolds`).
-/
namespace Tools.ShippingGen5Sem
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineSource (valsAt)

variable {dom : DomainConfig}

/-- One pending-write Signal per slot, read off a function of time into the tuple. -/
def sigListOfFn : (αs : List Type) → (Nat → HList αs) → Circuit.SigList dom αs
  | [], _ => ()
  | _ :: αs, f => (⟨fun t => (f t).1⟩, sigListOfFn αs (fun t => (f t).2))

/-- **P1.** The values of the packed Signals are the function. -/
theorem valsAt_sigListOfFn : ∀ (αs : List Type) (f : Nat → HList αs) (t : Nat),
    valsAt αs (sigListOfFn (dom := dom) αs f) t = f t
  | [], f, t => rfl
  | _ :: αs, f, t => by
    show ((f t).1, valsAt αs (sigListOfFn (dom := dom) αs (fun t => (f t).2)) t) = f t
    rw [valsAt_sigListOfFn αs (fun t => (f t).2) t]

/-- The state Signal rebuilt from a tuple of per-slot Signals (its value at `t` is the tuple of their values). -/
def reconState (αs : List Type) (ws : Circuit.SigList dom αs) : Signal dom (HList αs) :=
  ⟨fun t => valsAt αs ws t⟩

/-- Pointwise form of **P2**: the values of the "everything holds" seed are the live state. -/
theorem valsAt_mkHolds : ∀ (αs : List Type) (S : Signal dom (HList αs)) (t : Nat),
    valsAt αs (mkHolds αs S) t = S.val t
  | [], S, t => rfl
  | _ :: αs, S, t => by
    show ((S.val t).1, valsAt αs (mkHolds αs (Signal.map Prod.snd S)) t) = S.val t
    rw [valsAt_mkHolds αs (Signal.map Prod.snd S) t]
    rfl

/-- **P2.** Rebuilding the state from the seed gives the state back. -/
theorem reconState_mkHolds (αs : List Type) (S : Signal dom (HList αs)) :
    reconState αs (mkHolds αs S) = S := by
  show (⟨fun t => valsAt αs (mkHolds αs S) t⟩ : Signal dom (HList αs)) = S
  have : (fun t => valsAt αs (mkHolds αs S) t) = S.val := funext (valsAt_mkHolds αs S)
  rw [this]

/-- The seed built from a rebuilt state agrees with the packed Signals pointwise (`reconState` then `mkHolds`). -/
theorem valsAt_mkHolds_reconState (αs : List Type) (ws : Circuit.SigList dom αs) (t : Nat) :
    valsAt αs (mkHolds αs (reconState αs ws)) t = valsAt αs ws t :=
  valsAt_mkHolds αs (reconState αs ws) t

end Tools.ShippingGen5Sem

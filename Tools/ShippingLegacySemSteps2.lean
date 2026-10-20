import Tools.ShippingLegacySemSteps

/-! # More inversion steps (for the body's prefix)

Same discipline as `Tools/ShippingLegacySemSteps.lean`: one construct at the
head of the program, reduced by the unifier; the program is never normalised.

* `returns_throw` — a lifted `throwError` has no successful run.
* `returns_ite_lift_then` — `if c then (a lifted oracle; P) else P`: a run of
  `P` from the same builder state (an `if` without `else` whose body is one
  oracle, followed by the rest — the join point occurs in both branches).
* `returns_optCases` — a `match` on an `Option` at the head, in the form every
  such matcher unfolds to (`Option.casesOn`): the discriminant's value and
  the taken arm's run. EXPECTED, not observed: that the unifier unfolds the
  auxiliary matcher of `match d with | some x => … | _ => …` against
  `Option.casesOn d n s`.
* `guard_not` — the Boolean fact behind the `whnf` test of the body. -/
namespace Tools.ShippingLegacySem
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- A lifted `throwError` does not return. -/
theorem returns_throw {α : Type} {m : MessageData} {ctx : CompilerState} {s t : CircuitState}
    {r : α} (h : Returns (CompilerM.liftMetaM (Lean.throwError m : MetaM α)) ctx s r t) :
    False := by
  obtain ⟨hm, _⟩ := returns_liftMetaM h
  obtain ⟨mctx, mref, cctx, cref, w0, w1, hrun⟩ := hm
  exact Tools.ShippingChildInv.throwError_not_runs (mctx := mctx) (mref := mref)
    (cctx := cctx) (cref := cref) m hrun

/-- `if c then (oracle; P) else P`: `P` runs from the same builder state. -/
theorem returns_ite_lift_then {α β : Type} {c : Prop} [Decidable c] {x : MetaM β}
    {P : CompilerM α} {ctx : CompilerState} {s t : CircuitState} {r : α}
    (h : Returns (if c then (CompilerM.liftMetaM x >>= fun _ => P) else P) ctx s r t) :
    Returns P ctx s r t := by
  rcases returns_ite h with ⟨_, k⟩ | ⟨_, k⟩
  · obtain ⟨u, s1, hx, k1⟩ := Returns.bind k
    have hs1 : s1 = s := Returns.liftMetaM hx
    rw [hs1] at k1
    exact k1
  · exact k

/-- A `match` on an `Option` at the head. -/
theorem returns_optCases {α β : Type} {d : Option β} {n : CompilerM α} {sm : β → CompilerM α}
    {ctx : CompilerState} {s t : CircuitState} {r : α}
    (h : Returns (Option.casesOn (motive := fun _ => CompilerM α) d n sm) ctx s r t) :
    (d = none ∧ Returns n ctx s r t) ∨ (∃ b, d = some b ∧ Returns (sm b) ctx s r t) := by
  cases d with
  | none => exact Or.inl ⟨rfl, h⟩
  | some b => exact Or.inr ⟨b, rfl, h⟩

/-- `!x || y` is false when `x` holds and `y` does not. -/
theorem guard_not {x y : Bool} (hx : x = true) (hy : y = false) : ¬ ((!x || y) = true) := by
  rw [hx, hy]
  decide

end Tools.ShippingLegacySem

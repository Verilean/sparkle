import Tools.ShippingRefineSoundness

/-! # The width adapter of an instance connection (findings A, A'; alternative (b))

Nothing in the compiler uses this file. It states the EXPRESSION a closing
could put between a parent wire and a child port so that the two sides of
an instance connection have the same width by construction
(`docs/parallel/B-callwidths.md` §4), and its value in the IR semantics.

`castRef x wFrom wTo`: the value of the wire `x`, declared `wFrom` bits
wide, as a `wTo`-bit value:

* `wFrom = wTo` — the reference itself. The closing's output is then the
  one it produces today, statement for statement (`castRef_same`);
* otherwise the slice `x[wTo-1:0]`, whose IR value is `env x` masked to
  `wTo` bits (`eval_castRef`): the low bits of a wider wire, and a narrower
  wire's value unchanged when it is in range (`eval_castRef_inRange` — the
  printer emits the size cast `wTo'(x)` for an over-wide slice of a known
  wire, `Sparkle/Backend/Verilog.lean` 186–196). This is what the emitted
  Verilog does TODAY at a port whose widths differ (it truncates or
  zero-extends silently), and what the linked IR semantics does NOT do
  (`connEnvS` / `bindOuts` copy the natural number unmasked): with the
  adapter the two agree, without it `PortsMatch` is the premise that rules
  the difference out.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingCallCast
open Sparkle.IR.AST Sparkle.IR.Semantics

/-- The wire `x` (declared `wFrom` bits) as a `wTo`-bit value. -/
def castRef (x : String) (wFrom wTo : Nat) : Expr :=
  if wFrom = wTo then .ref x else .slice (.ref x) (wTo - 1) 0

/-- Equal widths: the reference itself — the connection is unchanged. -/
theorem castRef_same (x : String) (w : Nat) : castRef x w w = .ref x := by
  unfold castRef
  rw [if_pos rfl]

theorem castRef_ne (x : String) {a b : Nat} (h : a ≠ b) :
    castRef x a b = .slice (.ref x) (b - 1) 0 := by
  unfold castRef
  rw [if_neg h]

theorem eval_ref (we : WEnv) (env : Env) (x : String) :
    evalExpr we env (.ref x) = some (env x) := rfl

/-- The adapter's value: the wire's when the widths agree, its low `wTo`
bits otherwise. -/
theorem eval_castRef (we : WEnv) (env : Env) (x : String) (wFrom wTo : Nat) (hpos : 0 < wTo) :
    evalExpr we env (castRef x wFrom wTo) =
      some (if wFrom = wTo then env x else mask wTo (env x)) := by
  by_cases h : wFrom = wTo
  · subst h
    rw [if_pos rfl, castRef_same, eval_ref]
  · have e1 : wTo - 1 - 0 + 1 = wTo := by omega
    rw [if_neg h, castRef_ne x h,
      Tools.ShippingRefineSoundness.eval_slice we env (eval_ref we env x) (wTo - 1) 0, e1,
      Nat.shiftRight_zero]

/-- A value in the port's range passes unchanged, whatever the declared
width of the wire (a narrower wire into a wider port: zero extension). -/
theorem eval_castRef_inRange (we : WEnv) (env : Env) (x : String) (wFrom wTo : Nat)
    (hpos : 0 < wTo) (hv : env x < 2 ^ wTo) :
    evalExpr we env (castRef x wFrom wTo) = some (env x) := by
  rw [eval_castRef we env x wFrom wTo hpos]
  by_cases h : wFrom = wTo
  · rw [if_pos h]
  · rw [if_neg h]
    unfold mask
    rw [Nat.mod_eq_of_lt hv]

/-- The adapted value always fits the port. -/
theorem eval_castRef_lt (we : WEnv) (env : Env) (x : String) (wFrom wTo : Nat)
    (hpos : 0 < wTo) (hx : wFrom = wTo → env x < 2 ^ wTo) :
    ∃ v, evalExpr we env (castRef x wFrom wTo) = some v ∧ v < 2 ^ wTo := by
  by_cases h : wFrom = wTo
  · refine ⟨env x, ?_, hx h⟩
    rw [eval_castRef we env x wFrom wTo hpos, if_pos h]
  · refine ⟨mask wTo (env x), ?_, Nat.mod_lt _ (Nat.two_pow_pos wTo)⟩
    rw [eval_castRef we env x wFrom wTo hpos, if_neg h]

end Tools.ShippingCallCast

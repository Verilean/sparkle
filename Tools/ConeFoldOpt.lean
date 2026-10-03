import Tools.ConeFoldSlices

/-!
  The optimizer as translation validation — formally.

  `optimizeModule` (Sparkle/IR/Optimize.lean, ~1.1 kloc, ten partial
  defs) is not proven; instead the certified chain is CARRIED ACROSS
  it per instance.  Measured on every certified circuit, the optimizer
  changes an elaborator module's fully-inlined, slice-resolved cones in
  exactly ONE way: `inlineSingleUseWires` re-inserts a width mask
  `and [e, const (2^w - 1) w]` where an inlined wire of declared width
  `w` used to be a masking point.  `stripMask` removes those (when the
  masked expression is in the bounded fragment, so the mask is provably
  the identity) and the result is SYNTACTICALLY the original cone —
  checked by `native_decide` per instance.  With `stripMask_eval`, the
  optimized body's register-input and output cones evaluate to the
  original's, and the ConeFold bridge replays over the optimized body:
  Signal ≡ runModule of `optimizeModule m` ≡ (M4) the Verilog-subset
  semantics of the emission of THE MODULE THAT IS ACTUALLY PRINTED.

  Formalizes the argument `#verify_emit`'s header states informally
  ("stepwise cone equality gives full sequential equivalence").
-/

open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.SVParser.RoundtripProof (sfragCheck sfragCheck_sound
  sfrag_eval_bounded eval_const_ofNat)

namespace Tools.ConeFold

/-- `v &&& (2^w - 1) = v % 2^w` (bitwise ext). -/
theorem and_pow_two_sub_one (v w : Nat) : v &&& (2 ^ w - 1) = v % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow]
  exact Bool.and_comm _ _

/-- The width environment `wof` induces (the M2/M4 checkers' convention). -/
abbrev weW (wof : String → Option Nat) : WEnv := fun n => (wof n).getD 0

/-- Peephole: drop an identity width mask `and [e, const (2^w-1) w]`
    when `e` has width `w` and lies in the bounded fragment (so its
    value fits `w` bits and the mask is the identity). -/
def maskOf (wof : String → Option Nat) : Expr → Expr
  | .op .and [e, .const c w] =>
    if c == Int.ofNat (2 ^ w - 1) && widthOf (weW wof) e == w
        && sfragCheck wof e then e
    else .op .and [e, .const c w]
  | e => e

mutual
-- Remove the optimizer's re-inserted identity masks, bottom-up.
def stripMask (wof : String → Option Nat) : Expr → Expr
  | .op o args => maskOf wof (.op o (stripMaskL wof args))
  | .concat args => .concat (stripMaskL wof args)
  | .slice e hi lo => .slice (stripMask wof e) hi lo
  | e => e
def stripMaskL (wof : String → Option Nat) : List Expr → List Expr
  | [] => []
  | a :: rest => stripMask wof a :: stripMaskL wof rest
end

theorem maskOf_width (wof : String → Option Nat) (x : Expr) :
    widthOf (weW wof) (maskOf wof x) = widthOf (weW wof) x := by
  cases x with
  | op o args =>
    cases o <;> simp only [maskOf]
    case and =>
      match args with
      | [e, .const c w] =>
        simp only
        split
        · rename_i h
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          simp [widthOf, h.1.2]
        · rfl
      | [] => simp [maskOf]
      | [_] => simp [maskOf]
      | [_, .ref _] => simp [maskOf]
      | [_, .op _ _] => simp [maskOf]
      | [_, .concat _] => simp [maskOf]
      | [_, .slice _ _ _] => simp [maskOf]
      | [_, .sliceDim _ _ _] => simp [maskOf]
      | [_, .index _ _] => simp [maskOf]
      | _ :: _ :: _ :: _ => simp [maskOf]
  | _ => simp [maskOf]

/-- The identity mask evaluates to its operand on bounded environments. -/
theorem maskOf_eval (wof : String → Option Nat) (env : Env)
    (hb : Bounded (weW wof) env) (x : Expr) :
    evalExpr (weW wof) env (maskOf wof x) = evalExpr (weW wof) env x := by
  cases x with
  | op o args =>
    cases o <;> simp only [maskOf]
    case and =>
      match args with
      | [e, .const c w] =>
        simp only
        split
        · rename_i h
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨hc, hw⟩, hsf⟩ := h
          subst hc
          -- both sides: evaluate e first
          cases he : evalExpr (weW wof) env e with
          | none =>
            simp [evalExpr, evalList, he]
          | some v =>
            have hlt : v < 2 ^ w := by
              rw [← hw]
              exact sfrag_eval_bounded (sfragCheck_sound wof e hsf env hb) hb v he
            have hconst : evalExpr (weW wof) env (.const (Int.ofNat (2 ^ w - 1)) w)
                = some (2 ^ w - 1) :=
              eval_const_ofNat _ _ _ _ (by have := Nat.two_pow_pos w; omega)
            have hW : widthOf (weW wof)
                (.op .and [e, .const (Int.ofNat (2 ^ w - 1)) w]) = w := by
              simp [widthOf, hw]
            -- unfold ONE layer with the operand evaluations kept opaque,
            -- so `he`/`hconst` rewrite instead of the const being
            -- expanded into its Int encode
            rw [show evalExpr (weW wof) env
                  (.op .and [e, .const (Int.ofNat (2 ^ w - 1)) w])
                = ((evalList (weW wof) env [e, .const (Int.ofNat (2 ^ w - 1)) w]).bind
                    fun vals => evalOp (weW wof) .and
                      [e, .const (Int.ofNat (2 ^ w - 1)) w] vals
                      (widthOf (weW wof)
                        (.op .and [e, .const (Int.ofNat (2 ^ w - 1)) w])))
                from rfl]
            rw [show evalList (weW wof) env [e, .const (Int.ofNat (2 ^ w - 1)) w]
                = (evalExpr (weW wof) env e).bind fun v0 =>
                    (evalExpr (weW wof) env (.const (Int.ofNat (2 ^ w - 1)) w)).bind
                      fun vc => some [v0, vc]
                from rfl]
            rw [he, hconst, hW]
            simp only [Option.bind_some, evalOp, mask, and_pow_two_sub_one,
              Nat.mod_eq_of_lt hlt]
        · rfl
      | [] => simp [maskOf]
      | [_] => simp [maskOf]
      | [_, .ref _] => simp [maskOf]
      | [_, .op _ _] => simp [maskOf]
      | [_, .concat _] => simp [maskOf]
      | [_, .slice _ _ _] => simp [maskOf]
      | [_, .sliceDim _ _ _] => simp [maskOf]
      | [_, .index _ _] => simp [maskOf]
      | _ :: _ :: _ :: _ => simp [maskOf]
  | _ => simp [maskOf]

mutual
theorem stripMask_width (wof : String → Option Nat) :
    ∀ e, widthOf (weW wof) (stripMask wof e) = widthOf (weW wof) e
  | .op o args => by
    simp only [stripMask]
    rw [maskOf_width]
    exact widthOf_op_shape _ o (stripMaskL_widthMatch wof args)
  | .concat args => by
    simp only [stripMask, widthOf]
    exact widthOfGo_congr _ (stripMaskL_widthMatch wof args)
  | .slice e hi lo => by simp [stripMask, widthOf]
  | .const .. => by simp [stripMask]
  | .ref .. => by simp [stripMask]
  | .sliceDim .. => by simp [stripMask]
  | .index .. => by simp [stripMask]

theorem stripMaskL_widthMatch (wof : String → Option Nat) :
    ∀ args, WidthMatch (weW wof) args (stripMaskL wof args)
  | [] => by simp only [stripMaskL]; exact .nil
  | a :: rest => by
    simp only [stripMaskL]
    exact .cons (stripMask_width wof a) (stripMaskL_widthMatch wof rest)
end

mutual
/-- Stripping identity masks preserves evaluation on bounded envs. -/
theorem stripMask_eval (wof : String → Option Nat) (env : Env)
    (hb : Bounded (weW wof) env) :
    ∀ e, evalExpr (weW wof) env (stripMask wof e) = evalExpr (weW wof) env e
  | .op o args => by
    simp only [stripMask]
    rw [maskOf_eval wof env hb]
    have hwm := stripMaskL_widthMatch wof args
    simp only [evalExpr, stripMaskL_eval wof env hb args,
      widthOf_op_shape _ o hwm]
    cases evalList (weW wof) env args with
    | none => rfl
    | some vals =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [evalOp_congr _ hwm o vals _]
  | .concat args => by
    simp only [stripMask, evalExpr, stripMaskL_eval wof env hb args]
    cases evalList (weW wof) env args with
    | none => rfl
    | some vals =>
      simp only [Option.bind_eq_bind, Option.bind_some,
        evalGo_congr _ (stripMaskL_widthMatch wof args) vals]
  | .slice e hi lo => by
    simp only [stripMask, evalExpr, stripMask_eval wof env hb e]
  | .const .. => by simp [stripMask]
  | .ref .. => by simp [stripMask]
  | .sliceDim .. => by simp [stripMask]
  | .index .. => by simp [stripMask]

theorem stripMaskL_eval (wof : String → Option Nat) (env : Env)
    (hb : Bounded (weW wof) env) :
    ∀ args, evalList (weW wof) env (stripMaskL wof args)
      = evalList (weW wof) env args
  | [] => by simp [stripMaskL]
  | a :: rest => by
    simp only [stripMaskL, evalList, stripMask_eval wof env hb a,
      stripMaskL_eval wof env hb rest]
end

end Tools.ConeFold

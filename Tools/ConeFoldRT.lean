import Tools.ConeFoldOpt
import Tools.ConeFoldMem

/-!
  The printed text as translation validation — the 1-bit normal forms.

  The `#verify_elab_deep` shared route replays its chain over two more
  bodies (Tools/DeepElab.lean, `sharedBridge`): the OPTIMIZED body
  (`optimizeModule m`, the module `toVerilog` prints) and the body the
  shipping parser+lowerer reads back from that text.  As on the
  `#verify_elab` route, the bridge is a per-instance SYNTACTIC equality
  of cones after a normaliser with an evaluation-preservation proof.
  `stripMask` (Tools/ConeFoldOpt.lean) handles the optimizer's one
  rewrite.  The printed text introduces two more, MEASURED on
  `crc16CcittHW` (2026-09-14): the printer emits a 1-bit `not x` as
  `1'(x ^ 1'd1)` and the lowerer reads the size cast back as a
  zero-extend-and-slice, so `not [x]` comes back as
  `slice (concat [const 0 1, xor [x, const 1 1]]) 0 0`.  `rtNorm` maps
  both forms to `not [x]`; `rtNorm_eval` proves the value unchanged.

  The slice rule needs the sliced operand's value to fit one bit, which
  `evalExpr_bounded` gives on a bounded environment under the mux
  arm-width side condition (`widthOk`).  The side condition is stated on
  the NORMALISED term, which is what the bridge compares syntactically
  to the original cone — so per instance it is one closed Boolean.
-/

open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.SVParser.RoundtripProof (eval_const_ofNat)

namespace Tools.ConeFold

/-- Peephole at an operator node: a 1-bit `x ^ 1` is `not x`. -/
def rtOp (we : WEnv) (o : Operator) (args : List Expr) : Expr :=
  match o, args with
  | .xor, [x, .const (.ofNat 1) 1] =>
    if widthOf we x == 1 then .op .not [x] else .op .xor [x, .const (.ofNat 1) 1]
  | o, args => .op o args

/-- Peephole at a slice node: the lowered 1-bit size cast
    `{1'b0, x}[0:0]` of a 1-bit `x` is `x`. -/
def rtSlice (we : WEnv) (e : Expr) (hi lo : Nat) : Expr :=
  match e, hi, lo with
  | .concat [.const (.ofNat 0) 1, x], 0, 0 =>
    if widthOf we x == 1 then x else .slice (.concat [.const (.ofNat 0) 1, x]) 0 0
  | e, hi, lo => .slice e hi lo

mutual
/-- Bottom-up normalisation of the printed-text 1-bit forms. -/
def rtNorm (we : WEnv) : Expr → Expr
  | .op o args => rtOp we o (rtNormL we args)
  | .concat args => .concat (rtNormL we args)
  | .slice e hi lo => rtSlice we (rtNorm we e) hi lo
  | e => e
def rtNormL (we : WEnv) : List Expr → List Expr
  | [] => []
  | a :: rest => rtNorm we a :: rtNormL we rest
end

/- ---- width preservation ---- -/

theorem rtOp_width (we : WEnv) (o : Operator) (args : List Expr) :
    widthOf we (rtOp we o args) = widthOf we (.op o args) := by
  unfold rtOp
  split
  · split
    · rename_i h
      simp only [beq_iff_eq] at h
      simp [widthOf, h]
    · rfl
  · rfl

theorem rtSlice_width (we : WEnv) (e : Expr) (hi lo : Nat) :
    widthOf we (rtSlice we e hi lo) = widthOf we (.slice e hi lo) := by
  unfold rtSlice
  split
  · split
    · rename_i h
      simp only [beq_iff_eq] at h
      simp [widthOf, h]
    · rfl
  · rfl

mutual
theorem rtNorm_width (we : WEnv) :
    ∀ e, widthOf we (rtNorm we e) = widthOf we e
  | .op o args => by
    simp only [rtNorm]
    rw [rtOp_width]
    exact widthOf_op_shape _ o (rtNormL_widthMatch we args)
  | .concat args => by
    simp only [rtNorm, widthOf]
    exact widthOfGo_congr _ (rtNormL_widthMatch we args)
  | .slice e hi lo => by
    simp only [rtNorm]
    rw [rtSlice_width]
    simp [widthOf]
  | .const .. => by simp [rtNorm]
  | .ref .. => by simp [rtNorm]
  | .sliceDim .. => by simp [rtNorm]
  | .index .. => by simp [rtNorm]

theorem rtNormL_widthMatch (we : WEnv) :
    ∀ args, WidthMatch we args (rtNormL we args)
  | [] => by simp only [rtNormL]; exact .nil
  | a :: rest => by
    simp only [rtNormL]
    exact .cons (rtNorm_width we a) (rtNormL_widthMatch we rest)
end

/- ---- the side condition flows down through the peepholes ---- -/

theorem rtOp_widthOkL (we : WEnv) (o : Operator) (args : List Expr)
    (h : widthOk we (rtOp we o args) = true) : widthOkL we args = true := by
  unfold rtOp at h
  split at h
  · split at h
    · simp only [widthOk, widthOkL, Bool.and_eq_true] at h ⊢
      exact ⟨h.2.1, trivial, trivial⟩
    · simp only [widthOk, Bool.and_eq_true] at h
      exact h.2
  · simp only [widthOk, Bool.and_eq_true] at h
    exact h.2

theorem rtSlice_widthOk (we : WEnv) (e : Expr) (hi lo : Nat)
    (h : widthOk we (rtSlice we e hi lo) = true) : widthOk we e = true := by
  unfold rtSlice at h
  split at h
  · split at h
    · simp only [widthOk, widthOkL, Bool.and_eq_true]
      exact ⟨trivial, h, trivial⟩
    · simpa [widthOk] using h
  · simpa [widthOk] using h

/- ---- evaluation ---- -/

theorem rtOp_eval (we : WEnv) (env : Env) (o : Operator) (args : List Expr) :
    evalExpr we env (rtOp we o args) = evalExpr we env (.op o args) := by
  unfold rtOp
  split
  · split
    · rename_i x h
      simp only [beq_iff_eq] at h
      cases hx : evalExpr we env x with
      | none => simp [evalExpr, evalList, hx]
      | some a =>
        have hc : evalExpr we env (.const (.ofNat 1) 1) = some 1 :=
          eval_const_ofNat we env 1 1 (by decide)
        rw [show evalExpr we env (.op .not [x])
              = (evalList we env [x]).bind
                  (fun vals => evalOp we .not [x] vals (widthOf we (.op .not [x])))
            from rfl]
        rw [show evalExpr we env (.op .xor [x, .const (.ofNat 1) 1])
              = (evalList we env [x, .const (.ofNat 1) 1]).bind
                  (fun vals => evalOp we .xor [x, .const (.ofNat 1) 1] vals
                    (widthOf we (.op .xor [x, .const (.ofNat 1) 1])))
            from rfl]
        rw [show evalList we env [x] = (evalExpr we env x).bind (fun v => some [v]) from rfl]
        rw [show evalList we env [x, .const (.ofNat 1) 1]
              = (evalExpr we env x).bind (fun v0 =>
                  (evalExpr we env (.const (.ofNat 1) 1)).bind fun v1 => some [v0, v1])
            from rfl]
        rw [hx, hc]
        simp [evalOp, widthOf, h]
    · rfl
  · rfl

theorem rtSlice_eval (we : WEnv) (env : Env) (hb : ∀ n, env n < 2 ^ we n)
    (e : Expr) (hi lo : Nat) (hok : widthOk we (rtSlice we e hi lo) = true) :
    evalExpr we env (rtSlice we e hi lo) = evalExpr we env (.slice e hi lo) := by
  unfold rtSlice at hok ⊢
  split
  · split
    · rename_i x h
      simp only [beq_iff_eq] at h
      simp only [h, BEq.rfl, ite_true] at hok
      cases hx : evalExpr we env x with
      | none => simp [evalExpr, evalList, hx]
      | some v =>
        have hv : v < 2 ^ 1 := h ▸ evalExpr_bounded we env hb x v hok hx
        have hc : evalExpr we env (.const (.ofNat 0) 1) = some 0 :=
          eval_const_ofNat we env 0 1 (by decide)
        have e1 : evalExpr we env (.concat [.const (.ofNat 0) 1, x])
            = some (evalExpr.go we [.const (.ofNat 0) 1, x] [0, v]) := by
          rw [show evalExpr we env (.concat [.const (.ofNat 0) 1, x])
                = (evalList we env [.const (.ofNat 0) 1, x]).bind
                    (fun vals => some (evalExpr.go we [.const (.ofNat 0) 1, x] vals))
              from rfl]
          rw [show evalList we env [.const (.ofNat 0) 1, x]
                = (evalExpr we env (.const (.ofNat 0) 1)).bind (fun v0 =>
                    (evalList we env [x]).bind fun vs => some (v0 :: vs))
              from rfl]
          rw [show evalList we env [x] = (evalExpr we env x).bind (fun v1 => some [v1]) from rfl]
          rw [hc, hx]
          rfl
        rw [show evalExpr we env (.slice (.concat [.const (.ofNat 0) 1, x]) 0 0)
              = (evalExpr we env (.concat [.const (.ofNat 0) 1, x])).bind
                  (fun c => some (mask (0 - 0 + 1) (c >>> 0)))
            from rfl]
        rw [e1]
        simp only [Option.bind_some, Option.some.injEq]
        simp only [evalExpr.go, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons,
          List.foldl_nil, widthOf, h, mask, Nat.shiftRight_zero, Nat.shiftLeft_zero]
        have h0 : (0 : Nat) % 2 ^ 1 = 0 := by decide
        simp only [h0, Nat.zero_shiftLeft, Nat.zero_or, Nat.or_zero, Nat.zero_add]
        rw [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hv]
    · rfl
  · rfl

mutual
/-- **Normalisation preserves evaluation** on bounded environments,
    under the mux arm-width side condition on the normalised term. -/
theorem rtNorm_eval (we : WEnv) (env : Env) (hb : ∀ n, env n < 2 ^ we n) :
    ∀ e, widthOk we (rtNorm we e) = true →
      evalExpr we env (rtNorm we e) = evalExpr we env e
  | .op o args, hok => by
    simp only [rtNorm] at hok ⊢
    rw [rtOp_eval]
    have hwm := rtNormL_widthMatch we args
    have hokL : widthOkL we (rtNormL we args) = true := rtOp_widthOkL we o _ hok
    simp only [evalExpr, rtNormL_eval we env hb args hokL, widthOf_op_shape _ o hwm]
    cases evalList we env args with
    | none => rfl
    | some vals =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [evalOp_congr _ hwm o vals _]
  | .concat args, hok => by
    simp only [rtNorm, widthOk] at hok ⊢
    simp only [evalExpr, rtNormL_eval we env hb args hok]
    cases evalList we env args with
    | none => rfl
    | some vals =>
      simp only [Option.bind_eq_bind, Option.bind_some,
        evalGo_congr _ (rtNormL_widthMatch we args) vals]
  | .slice e hi lo, hok => by
    simp only [rtNorm] at hok ⊢
    rw [rtSlice_eval we env hb _ hi lo hok]
    have hok' : widthOk we (rtNorm we e) = true := rtSlice_widthOk we _ hi lo hok
    simp only [evalExpr, rtNorm_eval we env hb e hok']
  | .const .., _ => by simp [rtNorm]
  | .ref .., _ => by simp [rtNorm]
  | .sliceDim .., _ => by simp [rtNorm]
  | .index .., _ => by simp [rtNorm]

theorem rtNormL_eval (we : WEnv) (env : Env) (hb : ∀ n, env n < 2 ^ we n) :
    ∀ args, widthOkL we (rtNormL we args) = true →
      evalList we env (rtNormL we args) = evalList we env args
  | [], _ => by simp [rtNormL]
  | a :: rest, hok => by
    simp only [rtNormL, widthOkL, Bool.and_eq_true] at hok ⊢
    simp only [evalList, rtNorm_eval we env hb a hok.1, rtNormL_eval we env hb rest hok.2]
end

/-- The composed per-instance bridge fact: when the normalised,
    mask-stripped cone of the replayed body IS the normalised original
    cone (one `native_decide` per cone), the two cones evaluate alike on
    a bounded environment. -/
theorem rtBridge_eval (wof : String → Option Nat) (env : Env)
    (hb : ∀ n, env n < 2 ^ weW wof n) (cX cO : Expr)
    (heq : rtNorm (weW wof) (stripMask wof cX) = rtNorm (weW wof) cO)
    (hokX : widthOk (weW wof) (rtNorm (weW wof) (stripMask wof cX)) = true)
    (hokO : widthOk (weW wof) (rtNorm (weW wof) cO) = true) :
    evalExpr (weW wof) env cO = evalExpr (weW wof) env cX := by
  rw [← rtNorm_eval _ env hb cO hokO, ← heq, rtNorm_eval _ env hb _ hokX,
    stripMask_eval wof env hb]

-- the crc16 shapes, pinned
#guard rtNorm (fun _ => 1)
  (.slice (.concat [.const (.ofNat 0) 1, .op .xor [.ref "c", .const (.ofNat 1) 1]]) 0 0)
  == .op .not [.ref "c"]
#guard rtNorm (fun _ => 8) (.op .xor [.ref "c", .const (.ofNat 1) 1])
  == .op .xor [.ref "c", .const (.ofNat 1) 1]
#guard rtNorm (fun _ => 1) (.op .xor [.ref "c", .const (.ofNat 1) 1]) == .op .not [.ref "c"]

end Tools.ConeFold

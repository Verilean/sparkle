/-
  M4, first fragment: DIRECT forward correctness of the emitter.

      evalSV wof env (widthOf we e) (emitAstExpr wof e) = evalExpr we env e

  — the IR value of a fragment expression equals the VERILOG value of
  its emission, evaluated by the SystemVerilog-subset semantics at the
  assignment context width (which the module fragment's width-agreement
  conditions pin to `widthOf we e`).  This is the statement that removes
  the PARSER from the trusted base for the emit direction.

  The v0 fragment deliberately requires WIDTH-UNIFORM operands on
  arithmetic (`widthOf a = widthOf b`) and mux arms: Verilog evaluates
  context-determined operands at the CONTEXT width, so a bare
  mixed-width nested addition keeps its inner carry where the IR
  semantics masks per node — the emitter does not (yet) pin binop
  operands, so mixed widths sit outside this fragment (recorded as the
  M4 opening investigation).
-/
import Tools.SVParser.EmitAst
import Tools.SVParser.SVSemantics

namespace Tools.SVParser.EmitSem

open Tools.SVParser.AST
open Tools.SVParser.SVSemantics
open Sparkle.IR.AST
open Sparkle.IR.Semantics

/-- v0 forward fragment: refs, fitting constants, width-uniform
    unsigned arithmetic/bitwise, width-uniform mux, and the pinned
    NOT. -/
inductive SF4 (wof : String → Option Nat) (we : WEnv) : Expr → Prop
  | ref (n : String)
      (hs : Sparkle.Backend.Verilog.sanitizeName n = n)
      (hw : wof n = some (we n)) : SF4 wof we (.ref n)
  | const (v : Int) (w : Nat)
      (h0 : 0 ≤ v) (hlt : v < ((2 ^ w : Nat) : Int)) (hw : 0 < w) :
      SF4 wof we (.const v w)
  | binop (op : Operator)
      (hop : op = .and ∨ op = .or ∨ op = .xor ∨ op = .add
        ∨ op = .sub ∨ op = .mul)
      {a b : Expr}
      (hww : Sparkle.IR.Semantics.widthOf we a
        = Sparkle.IR.Semantics.widthOf we b)
      (ha : SF4 wof we a) (hb : SF4 wof we b) :
      SF4 wof we (.op op [a, b])
  | mux {c t f : Expr}
      (hwf : Sparkle.IR.Semantics.widthOf we f
        = Sparkle.IR.Semantics.widthOf we t)
      (hc : SF4 wof we c) (ht : SF4 wof we t) (hf : SF4 wof we f) :
      SF4 wof we (.op .mux [c, t, f])
  | not {x : Expr} (w : Nat)
      (hwT : Tools.SVParser.EmitAst.exprWidthT wof x = some w)
      (hwS : Sparkle.IR.Semantics.widthOf we x = w)
      (hw0 : 0 < w)
      (hx : SF4 wof we x) : SF4 wof we (.op .not [x])

/-- v0 fragment expressions always evaluate (their shapes are total in
    `evalExpr`). -/
theorem sf4_eval_isSome {wof : String → Option Nat} {we : WEnv}
    {e : Expr} (h : SF4 wof we e) :
    ∀ env, (evalExpr we env e).isSome := by
  induction h with
  | ref n hs hw => intro env; simp [evalExpr]
  | const v w h0 hlt hw => intro env; simp [evalExpr]
  | binop op hop hww ha hb iha ihb =>
    rename_i a b
    intro env
    obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp (iha env)
    obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp (ihb env)
    rcases hop with h | h | h | h | h | h <;> subst h <;>
      simp [evalExpr, evalList, hva, hvb, evalOp]
  | mux hwf hc ht hf ihc iht ihf =>
    rename_i c t f
    intro env
    obtain ⟨vc, hvc⟩ := Option.isSome_iff_exists.mp (ihc env)
    obtain ⟨vt, hvt⟩ := Option.isSome_iff_exists.mp (iht env)
    obtain ⟨vf, hvf⟩ := Option.isSome_iff_exists.mp (ihf env)
    simp [evalExpr, evalList, hvc, hvt, hvf, evalOp]
  | not w hwT hwS hw0 hx ihx =>
    rename_i x
    intro env
    obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp (ihx env)
    simp [evalExpr, evalList, hvx, evalOp]

/-- **Forward correctness, v0**: the emitted form has the same
    self-determined width AND, evaluated at the IR width as context,
    the same value as the IR expression. -/
theorem emit_sem {wof : String → Option Nat} {we : WEnv} {env : Env}
    {e : Expr} (h : SF4 wof we e) (hbe : Bounded we env) :
    ∀ sv, Tools.SVParser.EmitAst.emitAstExpr wof e = some sv →
      widthSV wof sv = some (Sparkle.IR.Semantics.widthOf we e)
      ∧ evalAt wof env (Sparkle.IR.Semantics.widthOf we e) sv
          = evalExpr we env e := by
  induction h with
  | ref n hs hw =>
    intro sv hsv
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hs,
      Option.some_inj] at hsv
    subst hsv
    refine ⟨by simp [widthSV, hw, Sparkle.IR.Semantics.widthOf], ?_⟩
    simp only [evalAt, hw, Option.bind_eq_bind, Option.bind_some,
      evalExpr, Sparkle.IR.Semantics.widthOf]
    have := hbe n
    simp [mask, Nat.mod_eq_of_lt this]
  | const v w h0 hlt hw =>
    intro sv hsv
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hne,
      if_neg (by omega : ¬v < 0), Option.some_inj] at hsv
    subst hsv
    refine ⟨by simp [widthSV, hne, Sparkle.IR.Semantics.widthOf], ?_⟩
    simp only [evalAt, litVal, evalExpr, Sparkle.IR.Semantics.widthOf]
    -- both sides encode a fitting nonnegative constant
    congr 1
    have hmod : v % ((2 ^ w : Nat) : Int) = v :=
      Int.emod_eq_of_lt h0 hlt
    rw [hmod, Int.add_emod_right, hmod]
  | binop op hop hww ha hb iha ihb =>
    rename_i a b
    intro sv hsv
    rcases hop with h | h | h | h | h | h <;> subst h <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr,
        Option.bind_eq_bind] at hsv
      obtain ⟨sva, hsa, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, hsb, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Tools.SVParser.EmitAst.binOpOf, Option.bind_some,
        Option.some_inj] at hsv
      subst hsv
      obtain ⟨hwa, hva⟩ := iha sva hsa
      obtain ⟨hwb, hvb⟩ := ihb svb hsb
      constructor
      · simp only [widthSV, hwa, hwb, Option.bind_eq_bind,
          Option.bind_some, Sparkle.IR.Semantics.widthOf, hww,
          Nat.max_self]
      · simp only [Sparkle.IR.Semantics.widthOf] at hva hvb ⊢
        rw [show max (Sparkle.IR.Semantics.widthOf we a)
            (Sparkle.IR.Semantics.widthOf we b)
          = Sparkle.IR.Semantics.widthOf we a by omega] at *
        simp only [evalAt, Option.bind_eq_bind, hva,
          hww ▸ hvb]
        rw [show evalExpr we env (.op _ [a, b])
              = ((evalList we env [a, b]).bind fun vals =>
                  evalOp we _ [a, b] vals
                    (Sparkle.IR.Semantics.widthOf we (.op _ [a, b])))
            from rfl]
        cases hA : evalExpr we env a with
        | none => simp [evalList, hA, hva, hww ▸ hvb]
        | some va =>
        cases hB : evalExpr we env b with
        | none => simp [evalList, hA, hB, hva, hww ▸ hvb]
        | some vb =>
        simp [evalList, hA, hB, hva, hww ▸ hvb, evalOp,
          Sparkle.IR.Semantics.widthOf, hww, Nat.max_self]
  | mux hwf hc ht hf ihc iht ihf =>
    rename_i c t f
    intro sv hsv
    simp only [Tools.SVParser.EmitAst.emitAstExpr,
      Option.bind_eq_bind] at hsv
    obtain ⟨svc, hsc, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    obtain ⟨svt, hst, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    obtain ⟨svf, hsf, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv
    obtain ⟨hwc, hvc⟩ := ihc svc hsc
    obtain ⟨hwt, hvt⟩ := iht svt hst
    obtain ⟨hwff, hvf⟩ := ihf svf hsf
    constructor
    · simp [widthSV, hwt, hwff, Sparkle.IR.Semantics.widthOf, hwf,
        Nat.max_self]
    · -- condition is self-determined; arms inherit the context width
      have hW : Sparkle.IR.Semantics.widthOf we (.op .mux [c, t, f])
          = Sparkle.IR.Semantics.widthOf we t := by
        simp [Sparkle.IR.Semantics.widthOf]
      rw [hW]
      simp only [evalAt, evalSV, Option.bind_eq_bind, hwc,
        Option.bind_some, Nat.max_eq_right (Nat.zero_le _), hvc]
      rw [show evalExpr we env (.op .mux [c, t, f])
            = ((evalList we env [c, t, f]).bind fun vals =>
                evalOp we .mux [c, t, f] vals
                  (Sparkle.IR.Semantics.widthOf we (.op .mux [c, t, f])))
          from rfl]
      cases hC : evalExpr we env c with
      | none => simp [evalList, hC]
      | some vc =>
      cases hT : evalExpr we env t with
      | none =>
        exact absurd hT (Option.isSome_iff_ne_none.mp
          (sf4_eval_isSome ht env))
      | some vt =>
      cases hF : evalExpr we env f with
      | none =>
        exact absurd hF (Option.isSome_iff_ne_none.mp
          (sf4_eval_isSome hf env))
      | some vf =>
      simp only [evalList, hC, hT, hF, Option.bind_some,
        Option.bind_eq_bind, evalOp, Option.some_inj]
      have hvf' : evalAt wof env (Sparkle.IR.Semantics.widthOf we t) svf
          = evalExpr we env f := hwf ▸ hvf
      by_cases hvc0 : vc ≠ 0
      · rw [if_pos hvc0, if_pos hvc0, hvt, hT]
      · rw [if_neg hvc0, if_neg hvc0, hvf', hF]
  | not w hwT hwS hw0 hx ihx =>
    rename_i x
    intro sv hsv
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hwT, hne,
      Option.bind_eq_bind] at hsv
    obtain ⟨svx, hsx, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [hne, Bool.false_eq_true, if_false,
      Option.some_inj] at hsv
    subst hsv
    obtain ⟨hwx, hvx⟩ := ihx svx hsx
    have hW : Sparkle.IR.Semantics.widthOf we (.op .not [x]) = w := by
      simp [Sparkle.IR.Semantics.widthOf, hwS]
    constructor
    · simp [widthSV, hW]
    · rw [hW]
      -- the emitted `w'(x ^ w'dM)`: cast boundary puts the xor in a
      -- w-bit context, and everything is width w
      simp only [evalAt, evalSV, Option.bind_eq_bind, widthSV, hwx,
        hwS, Option.bind_some, Nat.max_self,
        Nat.max_eq_right (Nat.le_refl w)]
      rw [show evalExpr we env (.op .not [x])
            = ((evalList we env [x]).bind fun vals =>
                evalOp we .not [x] vals
                  (Sparkle.IR.Semantics.widthOf we (.op .not [x])))
          from rfl]
      cases hX : evalExpr we env x with
      | none => simp [evalList, hX, hvx, hwS ▸ hvx]
      | some vx =>
      simp only [evalList, hX, Option.bind_some, Option.bind_eq_bind,
        evalOp, Option.some_inj, litVal]
      rw [hwS] at hvx
      simp only [hvx, hX, Option.bind_some]
      -- mask w (mask w (vx ^^^ mask w (2^w-1))) = mask w (vx ^^^ (2^w-1))
      have hm : mask w ((2 : Nat) ^ w - 1) = 2 ^ w - 1 := by
        have := Nat.two_pow_pos w
        simp [mask, Nat.mod_eq_of_lt (by omega)]
      simp [mask, hm, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _), hwS]

/-- The headline form: at the assignment context width (which the
    module fragment's width-agreement conditions supply), the emitted
    Verilog computes the IR value. -/
theorem emit_sem_evalSV {wof : String → Option Nat} {we : WEnv}
    {env : Env} {e : Expr} (h : SF4 wof we e) (hbe : Bounded we env)
    {sv : SVExpr}
    (hsv : Tools.SVParser.EmitAst.emitAstExpr wof e = some sv) :
    evalSV wof env (Sparkle.IR.Semantics.widthOf we e) sv
      = evalExpr we env e := by
  obtain ⟨hw, hv⟩ := emit_sem h hbe sv hsv
  unfold evalSV
  simp [hw, Nat.max_self, hv]

end Tools.SVParser.EmitSem

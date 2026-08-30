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
  | const (v : Int) (w : Nat) (hw : 0 < w) :
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
  | cmpU (op : Operator)
      (hop : op = .eq ∨ op = .lt_u ∨ op = .le_u ∨ op = .gt_u
        ∨ op = .ge_u)
      {a b : Expr}
      -- Verilog sizes comparison operands to their own max, the IR
      -- masks each per node; width agreement makes both read the same
      -- self-determined values.
      (hww : Sparkle.IR.Semantics.widthOf we a
        = Sparkle.IR.Semantics.widthOf we b)
      (ha : SF4 wof we a) (hb : SF4 wof we b) :
      SF4 wof we (.op op [a, b])
  | sliceRef (n : String) (hi lo : Nat)
      (hs : Sparkle.Backend.Verilog.sanitizeName n = n)
      (hw : wof n = some (we n))
      (hlo : lo ≤ hi) (hhi : hi < we n)
      -- the exact full-width slice is the ELIDED emission — see
      -- `sliceRefFull`
      (hne : ¬(lo = 0 ∧ hi + 1 = we n)) :
      SF4 wof we (.slice (.ref n) hi lo)
  | sliceRefFull (n : String) (hi : Nat)
      (hs : Sparkle.Backend.Verilog.sanitizeName n = n)
      (hw : wof n = some (we n))
      (hfull : hi + 1 = we n) :
      SF4 wof we (.slice (.ref n) hi 0)
  | concat {args : List Expr}
      (hall : ∀ e, e ∈ args → SF4 wof we e)
      -- op-typed elements get the emitter's width-pinning size cast;
      -- the pin is faithful when the emitter's width matches the IR's
      (hpin : ∀ e, e ∈ args → ∀ op as, e = .op op as →
        Tools.SVParser.EmitAst.exprWidthT wof e
          = some (Sparkle.IR.Semantics.widthOf we e)
        ∧ 0 < Sparkle.IR.Semantics.widthOf we e) :
      SF4 wof we (.concat args)

/-- v0 fragment expressions always evaluate (their shapes are total in
    `evalExpr`). -/
theorem sf4_eval_isSome {wof : String → Option Nat} {we : WEnv}
    {e : Expr} (h : SF4 wof we e) :
    ∀ env, (evalExpr we env e).isSome := by
  induction h with
  | ref n hs hw => intro env; simp [evalExpr]
  | const v w hw => intro env; simp [evalExpr]
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
  | cmpU op hop hww ha hb iha ihb =>
    rename_i a b
    intro env
    obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp (iha env)
    obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp (ihb env)
    rcases hop with h | h | h | h | h <;> subst h <;>
      simp [evalExpr, evalList, hva, hvb, evalOp]
  | sliceRef n hi lo hs hw hlo hhi hne =>
    intro env; simp [evalExpr]
  | sliceRefFull n hi hs hw hfull =>
    intro env; simp [evalExpr]
  | concat hall hpin ihall =>
    rename_i args
    intro env
    have : ∀ (as : List Expr), (∀ e, e ∈ as → (evalExpr we env e).isSome)
        → (evalList we env as).isSome := by
      intro as
      induction as with
      | nil => intro _; simp [evalList]
      | cons a rest ih =>
        intro hmem
        obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp
          (hmem a (List.mem_cons_self ..))
        obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp
          (ih fun e he => hmem e (List.mem_cons_of_mem _ he))
        simp [evalList, hva, hvs]
    obtain ⟨vals, hvals⟩ := Option.isSome_iff_exists.mp
      (this args fun e he => ihall e he env)
    simp [evalExpr, hvals]

private theorem evalList_length {we : WEnv} {env : Env} :
    ∀ (as : List Expr) (vs : List Nat),
      evalList we env as = some vs → vs.length = as.length := by
  intro as
  induction as with
  | nil => intro vs h; simp [evalList] at h; simp [← h]
  | cons a rest ih =>
    intro vs h
    simp only [evalList, Option.bind_eq_bind] at h
    obtain ⟨va, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vr, hvr, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some_inj] at h
    subst h
    simp [ih vr hvr]

private theorem zip_foldl_width {we : WEnv} :
    ∀ (as : List Expr) (vs : List Nat) (acc : Nat),
      as.length = vs.length →
      (as.zip vs).foldl (fun acc (p : Expr × Nat) =>
        acc + Sparkle.IR.Semantics.widthOf we p.1) acc
      = acc + Sparkle.IR.Semantics.widthOf.go we as := by
  intro as
  induction as with
  | nil =>
    intro vs acc _
    simp [Sparkle.IR.Semantics.widthOf.go]
  | cons a rest ih =>
    intro vs acc hlen
    cases vs with
    | nil => simp at hlen
    | cons v vrest =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [ih vrest _ (by simpa using hlen),
        Sparkle.IR.Semantics.widthOf.go]
      omega

/-- Element-wise alignment of the emitter's concat with the IR's:
    same total width, same MSB-first assembly, and the assembled value
    fits its total width (so the context mask at the top is inert). -/
private theorem concat_elems_sem {wof : String → Option Nat} {we : WEnv}
    {env : Env} :
    ∀ (args : List Expr) (svs : List SVExpr),
      (∀ e, e ∈ args → (evalExpr we env e).isSome) →
      (∀ e, e ∈ args → ∀ sv,
        Tools.SVParser.EmitAst.emitAstExpr wof e = some sv →
          widthSV wof sv = some (Sparkle.IR.Semantics.widthOf we e)
          ∧ evalAt wof env (Sparkle.IR.Semantics.widthOf we e) sv
              = evalExpr we env e) →
      (∀ e, e ∈ args → ∀ op as, e = .op op as →
        Tools.SVParser.EmitAst.exprWidthT wof e
          = some (Sparkle.IR.Semantics.widthOf we e)
        ∧ 0 < Sparkle.IR.Semantics.widthOf we e) →
      Tools.SVParser.EmitAst.emitConcatElems wof args = some svs →
      widthSV.go wof svs
          = some (Sparkle.IR.Semantics.widthOf.go we args)
      ∧ ∃ vals, evalList we env args = some vals
        ∧ goConcat wof env svs
            = some (Sparkle.IR.Semantics.evalExpr.go we args vals)
        ∧ Sparkle.IR.Semantics.evalExpr.go we args vals
            < 2 ^ Sparkle.IR.Semantics.widthOf.go we args := by
  intro args
  induction args with
  | nil =>
    intro svs _ _ _ hemit
    simp only [Tools.SVParser.EmitAst.emitConcatElems,
      Option.some_inj] at hemit
    subst hemit
    exact ⟨by simp [widthSV.go, Sparkle.IR.Semantics.widthOf.go],
      [], by simp [evalList],
      by simp [goConcat, Sparkle.IR.Semantics.evalExpr.go],
      by simp [Sparkle.IR.Semantics.evalExpr.go,
        Sparkle.IR.Semantics.widthOf.go, Nat.zero_lt_one]⟩
  | cons a rest ih =>
    intro svs hsome hsem hpin hemit
    obtain ⟨vA, hvA⟩ := Option.isSome_iff_exists.mp
      (hsome a (List.mem_cons_self ..))
    -- the assembly, abstracted over the (possibly cast-pinned) head:
    -- any head emission with the right width whose value agrees with
    -- the IR element up to its own mask assembles correctly
    have finish : ∀ (ca : SVExpr) (es : List SVExpr),
        Tools.SVParser.EmitAst.emitConcatElems wof rest = some es →
        widthSV wof ca = some (Sparkle.IR.Semantics.widthOf we a) →
        (∃ va, evalSV wof env 0 ca = some va
          ∧ mask (Sparkle.IR.Semantics.widthOf we a) va
            = mask (Sparkle.IR.Semantics.widthOf we a) vA) →
        widthSV.go wof (ca :: es)
            = some (Sparkle.IR.Semantics.widthOf.go we (a :: rest))
        ∧ ∃ vals, evalList we env (a :: rest) = some vals
          ∧ goConcat wof env (ca :: es)
              = some (Sparkle.IR.Semantics.evalExpr.go we (a :: rest) vals)
          ∧ Sparkle.IR.Semantics.evalExpr.go we (a :: rest) vals
              < 2 ^ Sparkle.IR.Semantics.widthOf.go we (a :: rest) := by
      rintro ca es hes htw ⟨va, hva, hmva⟩
      obtain ⟨hwgo, vals, hvals, hgo, hbnd⟩ := ih es
        (fun e he => hsome e (List.mem_cons_of_mem _ he))
        (fun e he => hsem e (List.mem_cons_of_mem _ he))
        (fun e he => hpin e (List.mem_cons_of_mem _ he))
        hes
      have hlen := evalList_length rest vals hvals
      refine ⟨?_, vA :: vals, ?_, ?_, ?_⟩
      · simp only [widthSV.go, htw, hwgo, Option.bind_eq_bind,
          Option.bind_some, Sparkle.IR.Semantics.widthOf.go]
      · simp [evalList, hvA, hvals]
      · simp only [goConcat, htw, hva, hwgo, hgo, Option.bind_eq_bind,
          Option.bind_some, Option.some_inj,
          Sparkle.IR.Semantics.evalExpr.go]
        rw [zip_foldl_width rest vals 0 hlen.symm, hmva]
        simp
      · simp only [Sparkle.IR.Semantics.evalExpr.go,
          Sparkle.IR.Semantics.widthOf.go]
        rw [zip_foldl_width rest vals 0 hlen.symm]
        simp only [Nat.zero_add]
        have h1 : mask (Sparkle.IR.Semantics.widthOf we a) vA
            < 2 ^ Sparkle.IR.Semantics.widthOf we a :=
          Nat.mod_lt _ (Nat.two_pow_pos _)
        have h2 : mask (Sparkle.IR.Semantics.widthOf we a) vA
              <<< Sparkle.IR.Semantics.widthOf.go we rest
            < 2 ^ (Sparkle.IR.Semantics.widthOf we a
                + Sparkle.IR.Semantics.widthOf.go we rest) := by
          rw [Nat.shiftLeft_eq, Nat.pow_add]
          exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h1
        have h3 : Sparkle.IR.Semantics.evalExpr.go we rest vals
            < 2 ^ (Sparkle.IR.Semantics.widthOf we a
                + Sparkle.IR.Semantics.widthOf.go we rest) :=
          Nat.lt_of_lt_of_le hbnd
            (Nat.pow_le_pow_right (by omega) (by omega))
        exact Nat.or_lt_two_pow h2 h3
    cases a
    case op op' as' =>
      obtain ⟨hpT, hp0⟩ := hpin _ (List.mem_cons_self ..) op' as' rfl
      simp only [Tools.SVParser.EmitAst.emitConcatElems, hpT,
        Option.bind_eq_bind] at hemit
      obtain ⟨ea, hea, hemit⟩ := Option.bind_eq_some_iff.mp hemit
      obtain ⟨es, hes, hemit⟩ := Option.bind_eq_some_iff.mp hemit
      simp only [Option.some_inj] at hemit
      rw [if_pos hp0] at hemit
      subst hemit
      obtain ⟨hwea, hvea⟩ := hsem _ (List.mem_cons_self ..) ea hea
      refine finish _ es hes (by simp [widthSV]) ?_
      refine ⟨mask (Sparkle.IR.Semantics.widthOf we (.op op' as'))
        (mask (Sparkle.IR.Semantics.widthOf we (.op op' as')) vA),
        ?_, by simp [mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]⟩
      unfold evalSV
      simp only [widthSV, Option.bind_eq_bind, Option.bind_some,
        Nat.max_eq_right (Nat.zero_le _), evalAt]
      unfold evalSV
      simp [hwea, hvea, hvA]
    all_goals
      (simp only [Tools.SVParser.EmitAst.emitConcatElems,
         Option.bind_eq_bind] at hemit;
       obtain ⟨ea, hea, hemit⟩ := Option.bind_eq_some_iff.mp hemit;
       obtain ⟨es, hes, hemit⟩ := Option.bind_eq_some_iff.mp hemit;
       simp only [Option.some_inj] at hemit;
       subst hemit;
       obtain ⟨hwea, hvea⟩ := hsem _ (List.mem_cons_self ..) ea hea;
       refine finish ea es hes hwea ⟨vA, ?_, rfl⟩;
       unfold evalSV;
       simp [hwea, hvea, hvA])

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
  | const v w hw =>
    intro sv hsv
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    by_cases hneg : v < 0
    · -- negative: sized-hex two's complement — the emission carries the
      -- IR encode LITERALLY (`encodeConst` is the same formula), so the
      -- two masked values coincide definitionally.
      simp only [Tools.SVParser.EmitAst.emitAstExpr, hne,
        if_pos hneg, Option.some_inj] at hsv
      subst hsv
      refine ⟨by simp [widthSV, Sparkle.IR.Semantics.widthOf], ?_⟩
      simp [evalAt, litVal, evalExpr, Sparkle.IR.Semantics.widthOf,
        Tools.SVParser.EmitAst.encodeConst]
    · -- nonnegative (fitting or not): both sides reduce `v` mod 2^w —
      -- the SV side by the context mask on the raw decimal, the IR side
      -- inside its two's-complement encode.
      simp only [Tools.SVParser.EmitAst.emitAstExpr, hne,
        if_neg hneg, Option.some_inj] at hsv
      subst hsv
      refine ⟨by simp [widthSV, hne, Sparkle.IR.Semantics.widthOf], ?_⟩
      simp only [evalAt, litVal, evalExpr, Sparkle.IR.Semantics.widthOf]
      congr 1
      rcases Int.eq_ofNat_of_zero_le (Int.not_lt.mp hneg) with ⟨n, rfl⟩
      have h2 : (0 : Int) < ((2 ^ w : Nat) : Int) :=
        Int.natCast_pos.mpr (Nat.two_pow_pos w)
      rw [Int.add_emod_right]
      have hmm : ∀ m : Nat, (m : Int) % ((2 ^ w : Nat) : Int)
          = ((m % 2 ^ w : Nat) : Int) := fun m => by omega
      rw [hmm n, hmm (n % 2 ^ w), Int.toNat_natCast, Int.toNat_natCast]
      simp [mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]
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
  | cmpU op hop hww ha hb iha ihb =>
    rename_i a b
    intro sv hsv
    rcases hop with h | h | h | h | h <;> subst h <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr,
        Option.bind_eq_bind] at hsv
      obtain ⟨sva, hsa, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, hsb, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Tools.SVParser.EmitAst.binOpOf, Option.bind_some,
        Option.some_inj] at hsv
      subst hsv
      obtain ⟨hwa, hva⟩ := iha sva hsa
      obtain ⟨hwb, hvb⟩ := ihb svb hsb
      have hvb' : evalAt wof env (Sparkle.IR.Semantics.widthOf we a) svb
          = evalExpr we env b := hww ▸ hvb
      constructor
      · simp [widthSV, Sparkle.IR.Semantics.widthOf]
      · -- comparison operands are SELF-determined: they size to their
        -- own max, which width agreement pins to `widthOf we a` — the
        -- exact width the IH evaluated them at.
        rw [show evalExpr we env (.op _ [a, b])
              = ((evalList we env [a, b]).bind fun vals =>
                  evalOp we _ [a, b] vals
                    (Sparkle.IR.Semantics.widthOf we (.op _ [a, b])))
            from rfl]
        cases hA : evalExpr we env a with
        | none =>
          exact absurd hA (Option.isSome_iff_ne_none.mp
            (sf4_eval_isSome ha env))
        | some va =>
        cases hB : evalExpr we env b with
        | none =>
          exact absurd hB (Option.isSome_iff_ne_none.mp
            (sf4_eval_isSome hb env))
        | some vb =>
        simp only [evalAt, hwa, hwb, Option.bind_eq_bind,
          Option.bind_some, ← hww, Nat.max_self, hva, hvb', hA, hB,
          evalList, evalOp, Option.some_inj]
  | sliceRef n hi lo hs hw hlo hhi hne =>
    intro sv hsv
    -- unfold the emitter on the non-castEnc, non-elided, in-range slice
    have helide : (lo == 0 && hi + 1 == we n) = false := by
      rcases Nat.eq_zero_or_pos lo with h0 | h0
      · subst h0
        have : hi + 1 ≠ we n := fun hc => hne ⟨rfl, hc⟩
        simp [this]
      · simp [Nat.pos_iff_ne_zero.mp h0]
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hs, hw, helide,
      Bool.false_eq_true, if_false, if_pos hhi,
      Option.some_inj] at hsv
    subst hsv
    constructor
    · simp [widthSV, Sparkle.IR.Semantics.widthOf]
    · simp only [Sparkle.IR.Semantics.widthOf, evalAt, hw,
        Option.bind_eq_bind, Option.bind_some, evalExpr,
        if_pos (And.intro hlo hhi)]
      simp [mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]
  | concat hall hpin ihall =>
    rename_i args
    intro sv hsv
    simp only [Tools.SVParser.EmitAst.emitAstExpr,
      Option.bind_eq_bind] at hsv
    obtain ⟨svs, hsvs, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv
    have hsome : ∀ e, e ∈ args → (evalExpr we env e).isSome :=
      fun e he => sf4_eval_isSome (hall e he) env
    obtain ⟨hwgo, vals, hvals, hgo, hbnd⟩ :=
      concat_elems_sem args svs hsome (fun e he => ihall e he) hpin hsvs
    constructor
    · simpa [widthSV, Sparkle.IR.Semantics.widthOf] using hwgo
    · simp only [evalAt, Option.bind_eq_bind, hgo, Option.bind_some,
        evalExpr, hvals, Sparkle.IR.Semantics.widthOf,
        Option.some_inj]
      simp [mask, Nat.mod_eq_of_lt hbnd]
  | sliceRefFull n hi hs hw hfull =>
    intro sv hsv
    have helide : (0 == 0 && hi + 1 == we n) = true := by simp [hfull]
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hs, hw, helide,
      if_true, Option.some_inj] at hsv
    subst hsv
    constructor
    · simp [widthSV, hw, Sparkle.IR.Semantics.widthOf, hfull]
    · simp only [Sparkle.IR.Semantics.widthOf, evalAt, hw,
        Option.bind_eq_bind, Option.bind_some, evalExpr,
        Nat.sub_zero, Option.some_inj]
      simp [Nat.shiftRight_zero]

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

import Tools.ShippingSyntaxSoundness

/-! Width-indexed backend correctness for unsigned comparisons and mux.
This extends the printable/semantic IR domain, not the quoted Signal source
fragment. In particular it adds no unchecked optimizer acceptance path. -/
namespace Tools.ShippingTypedExprSoundness
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingScalarSoundness Tools.ShippingTranslateSoundness
open Tools.ShippingPrintSoundness Tools.ShippingNameBinding Tools.ShippingSyntaxSoundness
open Tools.SVParser.EmitAst Tools.SVParser.EmitSem

/-- Positive-width expressions, with one-bit comparison results and mux
conditions. Branches and comparison operands agree in width; the whole tree
need not have one uniform width. -/
inductive TypedExpr (we : WEnv) : Expr → Nat → Prop
  | ref (x : String) : 0 < we x → TypedExpr we (.ref x) (we x)
  | const (v : Int) (n : Nat) : 0 < n → TypedExpr we (.const v n) n
  | bin (op : Binary) {a b : Expr} {n : Nat} :
      TypedExpr we a n → TypedExpr we b n →
      Sparkle.IR.PrintCheck.shiftShape op.operator b = true →
      TypedExpr we (.op op.operator [a, b]) n
  | compare {op : Operator} {a b : Expr} {n : Nat} :
      isCompareOp op = true → TypedExpr we a n → TypedExpr we b n →
      TypedExpr we (.op op [a, b]) 1
  | mux {c t f : Expr} {n : Nat} :
      TypedExpr we c 1 → TypedExpr we t n → TypedExpr we f n →
      TypedExpr we (.op .mux [c, t, f]) n

theorem TypedExpr.width {we e n} (h : TypedExpr we e n) : widthOf we e = n := by
  induction h with
  | ref => rfl
  | const => rfl
  | bin op _ _ _ ha hb => cases op <;> simp [Binary.operator, widthOf, ha, hb]
  | compare hop _ _ ha hb => cases ‹Operator› <;> simp_all [isCompareOp, Sparkle.IR.OptCheck.isControlBinOp, widthOf]
  | mux _ _ _ _ ht _ => simp [widthOf, ht]

theorem TypedExpr.positive {we e n} (h : TypedExpr we e n) : 0 < n := by
  induction h with
  | ref _ hn | const _ _ hn => exact hn
  | bin _ _ _ _ ha _ => exact ha
  | compare => decide
  | mux _ _ _ _ ht _ => exact ht

theorem TypedExpr.ofSized {we e n} (h : SizedExpr we e n) (hn : 0 < n) :
    TypedExpr we e n := by
  induction h with
  | ref x => exact .ref x hn
  | const v n => exact .const v n hn
  | bin op _ _ hs ha hb => exact .bin op (ha hn) (hb hn) hs

theorem TypedExpr.printShape {we e n} (h : TypedExpr we e n) : PrintShape e := by
  induction h with
  | ref x => exact .ref x
  | const v n => exact .const v n
  | bin op _ _ _ ha hb =>
    exact .bin (by cases op <;> decide) ha hb
  | compare ho _ _ ha hb => exact .compare ho ha hb
  | mux _ _ _ hc ht hf => exact .mux hc ht hf

theorem TypedExpr.notShl {we e n} (h : TypedExpr we e n) :
    isShlLit e = false ∧ shlOperand e = e := by
  have hn : isShlLit e = false := by
    cases h with
    | ref | const | mux => rfl
    | @bin op a b n ha hb hs =>
      cases op <;> cases b <;>
        simp_all [Binary.operator, Sparkle.IR.PrintCheck.shiftShape, isShlLit]
    | compare ho => cases ‹Operator› <;> simp_all [isCompareOp, Sparkle.IR.OptCheck.isControlBinOp, isShlLit]
  exact ⟨hn, shlOperand_id hn⟩

theorem TypedExpr.forward {we e n} (h : TypedExpr we e n)
    (wof : String → Option Nat)
    (hname : ∀ x ∈ Sparkle.IR.Reorder.refsOf e,
      Sparkle.Backend.Verilog.sanitizeName x = x ∧ wof x = some (we x)) :
    sf4Check wof we e = true := by
  induction h with
  | ref x _ =>
    obtain ⟨hs, hw⟩ := hname x (by simp [Sparkle.IR.Reorder.refsOf])
    simp [sf4Check, hs, hw]
  | const v n hn => simpa [sf4Check] using hn
  | bin op ha hb hs ia ib =>
    have ia := ia (fun x hx => hname x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    have ib := ib (fun x hx => hname x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    cases op <;> simp [Binary.operator, sf4Check, ha.width, hb.width,
      ha.notShl.1, ha.notShl.2, ia, ib]
  | compare ho ha hb ia ib =>
    have ia := ia (fun x hx => hname x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    have ib := ib (fun x hx => hname x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    cases ‹Operator› <;> simp_all [isCompareOp, Sparkle.IR.OptCheck.isControlBinOp]
    all_goals simp [sf4Check, ha.width, hb.width, ha.notShl.1, ha.notShl.2, ia, ib]
  | mux hc ht hf ic it iff =>
    have ic := ic (fun x hx => hname x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    have it := it (fun x hx => hname x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    have iff := iff (fun x hx => hname x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    simp [sf4Check, ht.width, hf.width, ic, it, iff]

/-- The actual shipping expression text represents an identifier-safe AST
with the same value as the IR. The forward-check premise is derived from
`TypedExpr`, including comparison/mux widths, rather than assumed. -/
theorem typedExpr_printed {we e n} (h : TypedExpr we e n)
    {wof : String → Option Nat}
    (hnames : ∀ x ∈ Sparkle.IR.Reorder.refsOf e,
      Sparkle.Backend.Verilog.sanitizeName x = x ∧ wof x = some (we x) ∧
      Tools.SVParser.ConcreteSyntax.Identifier x) :
    ∃ sv, emitAstExpr wof e = some sv ∧
      Tools.SVParser.ConcreteSyntax.Expression sv (Sparkle.Backend.Verilog.emitExpr wof e) ∧
      ∀ env, Bounded we env → (∀ x w, wof x = some w → env x < 2 ^ w) →
        Tools.SVParser.SVSemantics.evalSV wof env n sv = evalExpr we env e := by
  obtain ⟨sv, he, hr⟩ := emitExpr_render_all h.printShape wof
  have hb : ExprBound Tools.SVParser.ConcreteSyntax.Identifier sv :=
    emitExpr_bound h.printShape (fun x hx => by
      rw [(hnames x hx).1]; exact (hnames x hx).2.2) he
  refine ⟨sv, he, renderExpr_syntax hr hb, ?_⟩
  intro env henv hwof
  have hc := h.forward wof (fun x hx => ⟨(hnames x hx).1, (hnames x hx).2.1⟩)
  simpa only [h.width] using emit_sem_evalSV (sf4Check_sound hc) henv hwof he

/-- Width-indexed assignment bodies discharge the existing execution check.
Together with assignment ordering, this is the premise used by the general
module-settling and delta-convergence theorems. -/
theorem typedBody_assignsCheck {we : WEnv} {wof : String → Option Nat}
    {body : List Stmt}
    (hbody : ∀ st ∈ body, ∃ l r, st = .assign l r ∧ TypedExpr we r (we l))
    (hnames : ∀ st ∈ body, ∀ l r, st = .assign l r →
      (Sparkle.Backend.Verilog.sanitizeName l = l ∧ wof l = some (we l)) ∧
      ∀ x ∈ Sparkle.IR.Reorder.refsOf r,
        Sparkle.Backend.Verilog.sanitizeName x = x ∧ wof x = some (we x)) :
    assignsCheck wof we body = true := by
  induction body with
  | nil => rfl
  | cons st rest ih =>
    obtain ⟨l, r, rfl, hr⟩ := hbody st (by simp)
    obtain ⟨⟨hl, hw⟩, hn⟩ := hnames _ (by simp) l r rfl
    have ht := ih (fun s hs => hbody s (by simp [hs]))
      (fun s hs => hnames s (by simp [hs]))
    simp [assignsCheck, hl, hw, hr.width, hr.forward wof hn, ht]

end Tools.ShippingTypedExprSoundness

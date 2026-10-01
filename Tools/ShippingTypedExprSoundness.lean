import Tools.ShippingSyntaxSoundness

/-! Width-indexed backend correctness for comparisons and mux.
This extends the printable/semantic IR domain, not the quoted Signal source
fragment. In particular it adds no unchecked optimizer acceptance path. -/
namespace Tools.ShippingTypedExprSoundness
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingScalarSoundness Tools.ShippingTranslateSoundness
open Tools.ShippingPrintSoundness Tools.ShippingNameBinding Tools.ShippingSyntaxSoundness
open Tools.SVParser.EmitAst Tools.SVParser.EmitSem

def isUnsignedCompare : Operator → Bool
  | .eq | .lt_u | .le_u | .gt_u | .ge_u => true
  | _ => false

def isSignedCompare : Operator → Bool
  | .lt_s | .le_s | .gt_s | .ge_s => true
  | _ => false

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
      isUnsignedCompare op = true → TypedExpr we a n → TypedExpr we b n →
      TypedExpr we (.op op [a, b]) 1
  /-- Actual signed lowering compares wires, whose declaration widths are known.
  Arbitrary compound signed operands require a separate width-visibility proof. -/
  | signedCompare {op : Operator} (a b : String) :
      isSignedCompare op = true → 0 < we a → we a = we b →
      TypedExpr we (.op op [.ref a, .ref b]) 1
  | mux {c t f : Expr} {n : Nat} :
      TypedExpr we c 1 → TypedExpr we t n → TypedExpr we f n →
      TypedExpr we (.op .mux [c, t, f]) n
  /-- Zero-extension of a wire by a positive zero prefix, `{k'd0, x}`. -/
  | zext (x : String) (k : Nat) : 0 < k → 0 < we x →
      TypedExpr we (.concat [.const 0 k, .ref x]) (k + we x)
  /-- Truncation (or same-width cast) via the canonical size-cast encode
  `w'(x)`, i.e. `slice (concat [0_w, x]) (w-1) 0`. -/
  | trunc (x : String) (w : Nat) : 0 < w → w ≤ we x →
      TypedExpr we (.slice (.concat [.const 0 w, .ref x]) (w - 1) 0) w
  /-- A part-select of a wire inside its declared width, `x[hi:lo]`. -/
  | slice (x : String) (hi lo : Nat) : lo ≤ hi → hi < we x →
      TypedExpr we (.slice (.ref x) hi lo) (hi - lo + 1)

/-- Flat same-width comparisons cover both unsigned and signed operators. -/
theorem TypedExpr.compareRefs {we : WEnv} {op : Operator} {a b : String} {n : Nat}
    (ho : isCompareOp op = true) (hn : 0 < n) (wa : we a = n) (wb : we b = n) :
    TypedExpr we (.op op [.ref a, .ref b]) 1 := by
  cases op <;> simp_all only [isCompareOp, Sparkle.IR.OptCheck.isControlBinOp, Bool.false_eq_true]
  all_goals first
    | exact .compare (n := n) rfl
        (wa ▸ TypedExpr.ref (we := we) a (by omega))
        (wb ▸ TypedExpr.ref (we := we) b (by omega))
    | exact .signedCompare a b rfl (by omega) (wa.trans wb.symm)

theorem TypedExpr.width {we e n} (h : TypedExpr we e n) : widthOf we e = n := by
  induction h with
  | ref => rfl
  | const => rfl
  | bin op _ _ _ ha hb => cases op <;> simp [Binary.operator, widthOf, ha, hb]
  | compare hop _ _ ha hb => cases ‹Operator› <;> simp_all [isUnsignedCompare, Sparkle.IR.OptCheck.isControlBinOp, widthOf]
  | signedCompare _ _ ho _ _ => cases ‹Operator› <;> simp_all [isSignedCompare, widthOf]
  | mux _ _ _ _ ht _ => simp [widthOf, ht]
  | zext x k hk hx => simp [widthOf, widthOf.go]
  | trunc x w hw hwx => simp [widthOf]; omega
  | slice x hi lo hle hhi => simp [widthOf]

theorem TypedExpr.positive {we e n} (h : TypedExpr we e n) : 0 < n := by
  induction h with
  | ref _ hn | const _ _ hn => exact hn
  | bin _ _ _ _ ha _ => exact ha
  | compare | signedCompare => decide
  | mux _ _ _ _ ht _ => exact ht
  | zext _ _ hk _ => omega
  | trunc _ _ hw _ => exact hw
  | slice => omega

/-- Every typed reference has a positive internal declaration width. -/
theorem TypedExpr.refs_positive {we e n} (h : TypedExpr we e n) :
    ∀ x ∈ Sparkle.IR.Reorder.refsOf e, 0 < we x := by
  induction h with
  | ref x hn => simpa [Sparkle.IR.Reorder.refsOf] using hn
  | const => simp [Sparkle.IR.Reorder.refsOf]
  | bin op _ _ _ ha hb | compare _ _ _ ha hb =>
    intro x hx
    simp only [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList,
      List.append_nil, List.mem_append] at hx
    exact hx.elim (ha x) (hb x)
  | signedCompare a b ho hn hw =>
    intro x hx
    simp only [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList,
      List.append_nil, List.mem_append, List.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hn
    · simpa only [← hw] using hn
  | mux _ _ _ hc ht hf =>
    intro x hx
    simp only [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList,
      List.append_nil, List.mem_append] at hx
    rcases hx with hx | hx | hx
    · exact hc x hx
    · exact ht x hx
    · exact hf x hx
  | zext y k hk hy =>
    intro x hx
    simp only [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList,
      List.append_nil, List.nil_append, List.mem_singleton] at hx
    subst hx
    exact hy
  | trunc y w hw hwy =>
    intro x hx
    simp only [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList,
      List.append_nil, List.nil_append, List.mem_singleton] at hx
    subst hx
    omega
  | slice y hi lo hle hhi =>
    intro x hx
    simp only [Sparkle.IR.Reorder.refsOf, List.mem_singleton] at hx
    subst hx
    omega

/-- Typing only depends on widths at the expression's actual references. -/
theorem TypedExpr.we_congr {we we' e n} (h : TypedExpr we e n)
    (hw : ∀ x ∈ Sparkle.IR.Reorder.refsOf e, we' x = we x) : TypedExpr we' e n := by
  induction h with
  | ref x hn =>
    have eq := hw x (by simp [Sparkle.IR.Reorder.refsOf])
    simpa only [eq] using TypedExpr.ref (we := we') x (by rw [eq]; exact hn)
  | const v n hn => exact .const v n hn
  | bin op _ _ hs ha hb =>
    exact .bin op (ha (fun x hx => hw x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx])))
      (hb (fun x hx => hw x (by
        simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))) hs
  | compare ho _ _ ha hb =>
    exact .compare ho (ha (fun x hx => hw x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx])))
      (hb (fun x hx => hw x (by
        simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx])))
  | signedCompare a b ho hn he =>
    have ha := hw a (by simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList])
    have hb := hw b (by simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList])
    exact .signedCompare a b ho (by simpa only [ha] using hn) (by simpa only [ha, hb] using he)
  | mux _ _ _ hc ht hf =>
    apply TypedExpr.mux
    · exact hc (fun x hx => hw x (by simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    · exact ht (fun x hx => hw x (by simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    · exact hf (fun x hx => hw x (by simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
  | zext y k hk hy =>
    have ey := hw y (by simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList])
    have step := TypedExpr.zext (we := we') y k hk (by rw [ey]; exact hy)
    rwa [ey] at step
  | trunc y w hwid hwy =>
    have ey := hw y (by simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList])
    exact TypedExpr.trunc (we := we') y w hwid (by rw [ey]; exact hwy)
  | slice y hi lo hle hhi =>
    have ey := hw y (by simp [Sparkle.IR.Reorder.refsOf])
    exact TypedExpr.slice (we := we') y hi lo hle (by rw [ey]; exact hhi)

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
  | compare ho _ _ ha hb =>
    exact .compare (by cases ‹Operator› <;> simp_all [isUnsignedCompare, isCompareOp, Sparkle.IR.OptCheck.isControlBinOp]) ha hb
  | signedCompare a b ho _ _ =>
    exact .compare (by cases ‹Operator› <;> simp_all [isSignedCompare, isCompareOp, Sparkle.IR.OptCheck.isControlBinOp]) (.ref a) (.ref b)
  | mux _ _ _ hc ht hf => exact .mux hc ht hf
  | zext y k hk hy => exact .zext 0 k y
  | trunc y w hwid hwy => exact .castRef y w hwid
  | slice y hi lo hle hhi => exact .sliceRef y hi lo hle

theorem TypedExpr.notShl {we e n} (h : TypedExpr we e n) :
    isShlLit e = false ∧ shlOperand e = e := by
  have hn : isShlLit e = false := by
    cases h with
    | ref | const | mux | zext | trunc | slice => rfl
    | @bin op a b n ha hb hs =>
      cases op <;> cases b <;>
        simp_all [Binary.operator, Sparkle.IR.PrintCheck.shiftShape, isShlLit]
    | signedCompare _ _ ho _ _ => cases ‹Operator› <;> simp_all [isSignedCompare, isShlLit]
    | compare ho => cases ‹Operator› <;> simp_all [isUnsignedCompare, Sparkle.IR.OptCheck.isControlBinOp, isShlLit]
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
    cases ‹Operator› <;> simp_all [isUnsignedCompare, Sparkle.IR.OptCheck.isControlBinOp]
    all_goals simp [sf4Check, ha.width, hb.width, ha.notShl.1, ha.notShl.2, ia, ib]
  | signedCompare a b ho hn hw =>
    obtain ⟨sa, wa⟩ := hname a (by simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList])
    obtain ⟨sb, wb⟩ := hname b (by simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList])
    cases ‹Operator› <;> simp_all [isSignedCompare, sf4Check, widthOf, exprWidthT, isShlLit, shlOperand]
  | mux hc ht hf ic it iff =>
    have ic := ic (fun x hx => hname x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    have it := it (fun x hx => hname x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    have iff := iff (fun x hx => hname x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    simp [sf4Check, ht.width, hf.width, ic, it, iff]
  | zext y k hk hy =>
    obtain ⟨hs, hwof⟩ := hname y (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList])
    simp [sf4Check, List.attach_cons, hs, hwof, hk]
  | trunc y w hwid hwy =>
    obtain ⟨hs, hwof⟩ := hname y (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList])
    have harm : ((w - 1 : Nat) + 1 == w) = true := by
      simp only [beq_iff_eq]; omega
    simp [sf4Check, hs, hwof, hwid, harm, widthOf, hwy]
  | slice y hi lo hle hhi =>
    obtain ⟨hs, hwof⟩ := hname y (by simp [Sparkle.IR.Reorder.refsOf])
    by_cases hfull : lo = 0 ∧ hi + 1 = we y
    · simp [sf4Check, hs, hwof, hfull.1, hfull.2]
    · simp only [sf4Check, hs, hwof, beq_self_eq_true, Bool.true_and, decide_eq_true hle,
        decide_eq_true hhi, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        beq_iff_eq, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      left
      by_cases h0 : lo = 0
      · exact Or.inr (fun h => hfull ⟨h0, h⟩)
      · exact Or.inl h0

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

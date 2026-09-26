import Tools.ShippingDeclWidths

/-! Declaration binding for the actual emitted combinational AST. This is a
syntactic check on every expression, including dead assignments; it does not
infer declaration coverage merely from successful numerical evaluation. -/
namespace Tools.ShippingNameBinding
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.OptCheck
open Tools.SVParser.AST Tools.SVParser.EmitAst Tools.SVParser.EmitSem
open Tools.ShippingPrintSoundness Tools.ShippingModulePrintSoundness
open Tools.ShippingPrintEntrySoundness Tools.ShippingEntrySoundness
open Tools.ShippingTranslateSoundness Tools.ShippingOptSoundness
open Tools.ShippingSVBridge Tools.ShippingDeclWidths

/-- Every identifier leaf in the supported expression grammar is declared.
Unsupported forms are rejected rather than treated as having no references. -/
def ExprBound (declared : String → Prop) : SVExpr → Prop
  | .lit _ => True
  | .ident x => declared x
  | .binary _ a b => ExprBound declared a ∧ ExprBound declared b
  | .ternary c t f => ExprBound declared c ∧ ExprBound declared t ∧ ExprBound declared f
  | _ => False

def Declared (sv : SVModule) (x : String) : Prop :=
  ∃ entry ∈ declarationTable sv, entry.1 = x

def AssignmentsBound (sv : SVModule) (pairs : List CombStep) : Prop :=
  ∀ step ∈ pairs, match step with
    | .assign l rhs => Declared sv l ∧ ExprBound (Declared sv) rhs
    | .reads .. => False

/-- Name uniqueness is about occurrences, not just consistency of widths. -/
theorem table_name_unique {table : List (String × Option Nat)}
    (hn : (table.map Prod.fst).Nodup) {a b : String × Option Nat}
    (ha : a ∈ table) (hb : b ∈ table) (he : a.1 = b.1) : a = b := by
  induction table with
  | nil => cases ha
  | cons p rest ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ha with hpa | harest
    · subst a
      rcases List.mem_cons.mp hb with hpb | hbrest
      · exact hpb.symm
      · exact False.elim (hnot (he ▸ List.mem_map_of_mem hbrest))
    · rcases List.mem_cons.mp hb with hpb | hbrest
      · subst b
        exact False.elim (hnot (he ▸ List.mem_map_of_mem harest))
      · exact ih htail harest hbrest

theorem declared_unique {sv : SVModule} {x : String}
    (hn : ((declarationTable sv).map Prod.fst).Nodup) (hd : Declared sv x) :
    ∃ entry, (entry ∈ declarationTable sv ∧ entry.1 = x) ∧
      ∀ other, other ∈ declarationTable sv → other.1 = x → other = entry := by
  obtain ⟨entry, hm, he⟩ := hd
  exact ⟨entry, ⟨hm, he⟩, fun other ho hx => table_name_unique hn ho hm (hx.trans he.symm)⟩

theorem declared_of_width {sv : SVModule} {x : String} {n : Nat}
    (h : astWidths sv x = some n) : Declared sv x := by
  unfold astWidths lookupTable at h
  obtain ⟨entry, hf, _⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨entry, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

theorem emitExpr_bound {e : Sparkle.IR.AST.Expr} {sv : SVExpr}
    {wof : String → Option Nat} {declared : String → Prop}
    (hs : PrintShape e)
    (hr : ∀ x ∈ Sparkle.IR.Reorder.refsOf e,
      declared (Sparkle.Backend.Verilog.sanitizeName x))
    (he : emitAstExpr wof e = some sv) : ExprBound declared sv := by
  induction hs generalizing sv with
  | const v w =>
    simp only [emitAstExpr] at he
    split at he <;> cases he <;> trivial
  | ref x =>
    cases he
    exact hr x (by simp [Sparkle.IR.Reorder.refsOf])
  | @bin op a b hop ha hb ia ib =>
    obtain ⟨sa, hsa, _⟩ := emitExpr_render_all ha wof
    obtain ⟨sb, hsb, _⟩ := emitExpr_render_all hb wof
    have ba := ia (fun x hx => hr x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx])) hsa
    have bb := ib (fun x hx => hr x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx])) hsb
    cases op <;> simp_all [isPrintBinOp_eq_true, isBinOp, emitAstExpr, binOpOf]
    all_goals subst sv; exact ⟨ba, bb⟩

  | @compare op a b hop ha hb ia ib =>
    obtain ⟨sa, hsa, _⟩ := emitExpr_render_all ha wof
    obtain ⟨sb, hsb, _⟩ := emitExpr_render_all hb wof
    have ba := ia (fun x hx => hr x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx])) hsa
    have bb := ib (fun x hx => hr x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx])) hsb
    cases op <;> simp_all [isCompareOp, Sparkle.IR.OptCheck.isControlBinOp, emitAstExpr, binOpOf]
    all_goals subst sv; exact ⟨ba, bb⟩
  | mux hc ht hf ic it iff =>
    obtain ⟨sc, hsc, _⟩ := emitExpr_render_all hc wof
    obtain ⟨st, hst, _⟩ := emitExpr_render_all ht wof
    obtain ⟨sf, hsf, _⟩ := emitExpr_render_all hf wof
    simp only [emitAstExpr, hsc, hst, hsf, bind, Option.bind_some] at he
    cases he
    refine ⟨ic ?_ hsc, it ?_ hst, iff ?_ hsf⟩
    all_goals intro x hx; exact hr x (by
      simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx])

/-- The checked expression facts supply widths for every read, not merely
for wires that contribute to the final output. -/
theorem emitAssigns_bound {m : Sparkle.IR.AST.Module} {sv : SVModule}
    (hw : astWidths sv = printWidths (m.wires ++ m.inputs ++ m.outputs))
    {body : List Stmt} {pairs : List CombStep}
    (hs : ∀ st ∈ body, ∃ l r, st = .assign l r ∧ PrintShape r)
    (hc : ∀ st ∈ body, (match st with
      | .assign l r => match Sparkle.IR.PrintCheck.widths m l with
        | some n => Sparkle.Backend.Verilog.sanitizeName l == l &&
            (0 < n) && Sparkle.IR.PrintCheck.exprCheck m n r
        | none => false
      | _ => false) = true)
    (he : emitAssigns (astWidths sv) body = some pairs) : AssignmentsBound sv pairs := by
  induction body generalizing pairs with
  | nil => simp [emitAssigns] at he; subst pairs; simp [AssignmentsBound]
  | cons st rest ih =>
    obtain ⟨l, r, rfl, hshape⟩ := hs st (by simp)
    have check := hc (.assign l r) (by simp)
    cases hn : Sparkle.IR.PrintCheck.widths m l with
    | none => simp only [hn] at check; cases check
    | some n =>
      change (match Sparkle.IR.PrintCheck.widths m l with
        | some n => Sparkle.Backend.Verilog.sanitizeName l == l &&
            (0 < n) && Sparkle.IR.PrintCheck.exprCheck m n r
        | none => false) = true at check
      rw [hn] at check
      obtain ⟨_, hr⟩ := printExpr_sound m n r (Bool.and_eq_true_iff.mp check).2
      simp only [emitAssigns, bind, Option.bind_eq_some_iff] at he
      obtain ⟨rhs, hright, tail, htail, heq⟩ := he
      cases heq
      have left : Declared sv l := declared_of_width (by rw [hw]; exact hn)
      have right : ExprBound (Declared sv) rhs := emitExpr_bound hshape (by
        intro x hx
        obtain ⟨hname, hwidth⟩ := hr x hx
        rw [hname]
        exact declared_of_width (by rw [hw]; exact hwidth)) hright
      intro step hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨left, right⟩
      · exact ih (fun st hm => hs st (by simp [hm]))
          (fun st hm => hc st (by simp [hm])) htail step hm

/-- All assignment targets and all RHS identifiers in the real emitted tree
are bound to that same tree's declarations. No caller-supplied name premise. -/
theorem compiled_astBindings {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr} {sv : SVModule} {pairs : List CombStep}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (ht : emitAstModule (checkedOptimize m) = some sv)
    (hi : combItems sv.items = some pairs) : AssignmentsBound sv pairs := by
  have hg := (synthesized_printFacts h henv hwf hn).2
  have hp := checkedOptimize_printCheck hg
    (synthesized_printCheck h henv hwf hn (synthesized_names h henv hwf hn))
  have hc := (forwardCheck_sound (printCheck_forward hp)).2
  obtain ⟨sv', pairs', ht', he, hi'⟩ := module_combItems _
    (printed_printDecls h henv hwf hn) (checkedOptimize_printShape hg) hc
  rw [ht] at ht'; cases ht'
  rw [hi] at hi'; cases hi'
  have hw := compiled_astWidths h henv hwf hn ht
  rw [← hw] at he
  apply emitAssigns_bound hw (checkedOptimize_printShape hg) ?_ he
  intro st hm
  exact List.all_eq_true.mp hp st hm

end Tools.ShippingNameBinding

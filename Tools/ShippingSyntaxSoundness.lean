import Tools.SVParser.ConcreteSyntax
import Tools.ShippingNameBinding
import Tools.ShippingModuleNames

/-! Direct concrete-syntax correctness of the emitted combinational fragment.
There is no new runtime checker, parser assumption, or change to emitted RTL.
The auxiliary renderer rejects zero-sized literal ASTs, and its existing
shipping-emitter equality theorem proves that real output never needs them.
-/
namespace Tools.ShippingSyntaxSoundness
open Tools.SVParser.AST Tools.SVParser.ConcreteSyntax
open Tools.ShippingPrintSoundness Tools.ShippingModulePrintSoundness
open Tools.ShippingNameBinding Tools.ShippingDeclWidths Tools.ShippingSVBridge

set_option maxRecDepth 4096

/-- Allocated data names cannot be reserved words. -/
theorem dataName_identifier {s : String} (h : Sparkle.IR.NameHints.DataName s) :
    Identifier s := by
  rcases h with ⟨hclean, hhead⟩ | rfl
  · have hk : ∀ k ∈ Sparkle.IR.ModuleNames.keywords, k.toList.head? ≠ some '_' := by decide
    have hnot : s ∉ Sparkle.IR.ModuleNames.keywords := fun hm => hk s hm hhead
    have hstart : (match s.toList with | [] => false | c :: _ => c.isAlpha || c == '_') = true := by
      cases he : s.toList with
      | nil => simp [he] at hhead
      | cons c cs => simp [he] at hhead; simp [hhead]
    have hall : s.all Sparkle.IR.NameHints.charOk = true := by
      simpa [Sparkle.IR.NameHints.Clean, String.all_bool_eq] using hclean
    change Sparkle.IR.ModuleNames.legal s = true
    unfold Sparkle.IR.ModuleNames.legal
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨hstart, hall⟩, ?_⟩
    simpa using hnot
  · simp [Identifier, Sparkle.IR.ModuleNames.legal, Sparkle.IR.NameHints.charOk,
      Sparkle.IR.ModuleNames.keywords]

theorem renderBin_syntax {op tok} (h : renderBin op = some tok) : BinaryToken op tok := by
  cases op <;> simp [renderBin] at h <;> subst tok
  all_goals constructor

theorem renderExpr_syntax {e text} (hr : renderExpr e = some text)
    (hn : ExprBound Identifier e) : Expression e text := by
  cases e with
  | lit l =>
    cases l with
    | binary w v =>
      cases w with
      | none => simp [renderExpr] at hr
      | some w =>
        by_cases hw : w = 1
        · subst w
          by_cases hv : v = 0
          · subst v; cases hr; exact .binaryZero
          · simp [renderExpr, hv] at hr
        · simp [renderExpr, hw] at hr
    | decimal w v | hex w v =>
      cases w <;> simp only [renderExpr] at hr
      all_goals try { cases hr }
      all_goals rename_i w; split at hr
      all_goals try { cases hr }
      all_goals
        cases hr
        first
        | exact Expression.decimal (by omega) (numeral_decimal _) (numeral_decimal _)
        | exact Expression.hex (by omega) (numeral_decimal _) (numeral_toDigits (by decide) _)
    | _ => simp [renderExpr] at hr
  | unary op a =>
    cases op <;> simp only [renderExpr] at hr
    all_goals try { cases hr }
    simp only [bind, Option.bind_eq_some_iff] at hr
    obtain ⟨sa, ha, he⟩ := hr
    cases he
    exact .signed (renderExpr_syntax ha hn)
  | ident name => cases hr; exact .ident hn
  | binary op a b =>
    simp only [renderExpr, bind, Option.bind_eq_some_iff] at hr
    obtain ⟨tok, ht, sa, ha, sb, hb, he⟩ := hr
    cases he
    exact .binary (renderBin_syntax ht) (renderExpr_syntax ha hn.1) (renderExpr_syntax hb hn.2)
  | ternary c t f =>
    simp only [renderExpr, bind, Option.bind_eq_some_iff] at hr
    obtain ⟨sc, hc, st, ht, sf, hf, he⟩ := hr
    cases he
    exact .ternary (renderExpr_syntax hc hn.1) (renderExpr_syntax ht hn.2.1)
      (renderExpr_syntax hf hn.2.2)
  | _ => simp [renderExpr] at hr

termination_by sizeOf e

theorem renderType_syntax (w) : LogicType w (renderType w) := by
  cases w with
  | none => exact .scalar
  | some w => exact .packed (numeral_decimal w.1) (numeral_decimal w.2)

theorem renderPort_syntax {p text} (hr : renderPort p = some text)
    (hn : Identifier p.name) : Port p text := by
  rcases p with ⟨dir, reg, width, name, widthExpr, signed⟩
  cases reg <;> cases signed <;> cases widthExpr <;> cases dir <;>
    simp [renderPort] at hr
  all_goals subst text; constructor <;> first | exact hn | exact renderType_syntax _

theorem whitespace_empty : Whitespace "" := by simp [Whitespace]

theorem whitespace_append {a b} (ha : Whitespace a) (hb : Whitespace b) :
    Whitespace (a ++ b) := by
  intro c hc
  simp only [String.toList_append, List.mem_append] at hc
  exact hc.elim (ha c) (hb c)

theorem padded_self {α} {P : α → String → Prop} {x s} (h : P x s) : Padded P x s := by
  simpa using (Padded.mk (left := "") (right := "") whitespace_empty h whitespace_empty)

theorem padded_left {α} {P : α → String → Prop} {x s l}
    (h : Padded P x s) (hw : Whitespace l) : Padded P x (l ++ s) := by
  cases h with
  | mk hl hs hr =>
    simpa only [String.append_assoc] using (Padded.mk (whitespace_append hw hl) hs hr)

theorem items_append {xs ys a b} (ha : Items xs a) (hb : Items ys b) :
    Items (xs ++ ys) (a ++ b) := by
  induction ha generalizing ys b with
  | nil => simpa using hb
  | cons h _ ih => simpa only [List.cons_append, String.append_assoc] using Items.cons h (ih hb)
  | @pad xs s left right hl h hr ih =>
    have hbr : Items ys (right ++ b) := by
      simpa using Items.pad (right := "") hr hb whitespace_empty
    simpa only [List.append_assoc, String.append_assoc, String.append_empty] using
      Items.pad (right := "") hl (ih hbr) whitespace_empty


inductive Each {α β : Type} (P : α → β → Prop) : List α → List β → Prop
  | nil : Each P [] []
  | cons {x y xs ys} : P x y → Each P xs ys → Each P (x :: xs) (y :: ys)

private theorem mapM_phrases {α β} {f : α → Option β} {P : α → β → Prop}
    {xs : List α} {ys : List β} (h : xs.mapM f = some ys)
    (hp : ∀ x ∈ xs, ∀ y, f x = some y → P x y) : Each P xs ys := by
  induction xs generalizing ys with
  | nil => simp at h; subst ys; exact .nil
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨y, hy, tail, ht, he⟩ := h
    cases he
    exact .cons (hp x (by simp) y hy) (ih ht (fun a ha => hp a (by simp [ha])))

private theorem ports_intercalate {ps texts} (h : Each Port ps texts) :
    Ports ps (String.intercalate ",\n    " texts) := by
  induction h with
  | nil => exact .nil
  | @cons p t ps ts hp hrest ih =>
    cases hrest with
    | nil => simpa using Ports.one (padded_self hp)
    | cons hp' ht =>
      have hi := Ports.pad (left := "\n    ") (right := "") (by decide) ih whitespace_empty
      simpa [String.intercalate_cons_cons, String.append_assoc, ToString.toString,
        ← String.append_assoc (s₁ := ",") (s₂ := "\n    ")] using
        Ports.cons (padded_self hp) hi (by simp)

private theorem items_intercalate {items texts sep} (hw : Whitespace sep)
    (h : Each (Padded Item) items texts) :
    Items items (String.intercalate sep texts) := by
  induction h with
  | nil => exact .nil
  | @cons p t ps ts hp hrest ih =>
    cases hrest with
    | nil => simpa using Items.cons hp Items.nil
    | cons hp' ht =>
      have hi := Items.pad (right := "") hw ih whitespace_empty
      simpa [String.intercalate_cons_cons, String.append_assoc, ToString.toString] using Items.cons hp hi

private theorem exprBound_mono {P Q : String → Prop} {e : SVExpr}
    (h : ExprBound P e) (hi : ∀ x, P x → Q x) : ExprBound Q e := by
  cases e with
  | lit => trivial
  | ident x => exact hi x h
  | unary op a =>
    cases op <;> try exact False.elim h
    exact exprBound_mono (e := a) h hi
  | binary op a b => exact ⟨exprBound_mono h.1 hi, exprBound_mono h.2 hi⟩
  | ternary c t f => exact ⟨exprBound_mono h.1 hi, exprBound_mono h.2.1 hi,
      exprBound_mono h.2.2 hi⟩
  | _ => exact False.elim h

termination_by sizeOf e

private theorem combItems_assignment {items pairs l rhs}
    (h : combItems items = some pairs) (hm : .contAssign (.ident l) rhs ∈ items) :
    Tools.SVParser.EmitSem.CombStep.assign l rhs ∈ pairs := by
  induction items generalizing pairs with
  | nil => cases hm
  | cons item rest ih =>
    cases item with
    | wireDecl name width init =>
      cases init <;> simp only [combItems] at h
      · exact ih h (by simpa using hm)
      · cases h
    | contAssign lhs r =>
      cases lhs <;> simp only [combItems] at h
      all_goals try { cases h }
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨tail, ht, he⟩ := h
      cases he
      rcases List.mem_cons.mp hm with he | hm
      · cases he; simp
      · exact List.mem_cons_of_mem _ (ih ht hm)
    | _ => simp [combItems] at h

private theorem port_declared {sv : SVModule} {p : SVPort} (hm : p ∈ sv.ports) :
    Declared sv p.name := by
  exact ⟨(p.name, declaredPortWidth p), List.mem_append_left _ (List.mem_map_of_mem hm), rfl⟩

private theorem wire_declared {sv : SVModule} {name width}
    (hm : .wireDecl name width none ∈ sv.items) : Declared sv name := by
  refine ⟨(name, some (match width with | none => 1 | some (hi, lo) => max hi lo - min hi lo + 1)),
    List.mem_append_right _ ?_, rfl⟩
  exact List.mem_filterMap.mpr ⟨_, hm, by cases width <;> rfl⟩

private theorem renderWire_syntax {sv : SVModule} {item text}
    (hr : renderWire item = some text) (hm : item ∈ sv.items)
    (hd : ∀ x, Declared sv x → Identifier x) : Padded Item item text := by
  cases item <;> simp only [renderWire] at hr
  all_goals try { cases hr }
  rename_i name width init
  cases init
  · cases hr
    simpa [String.append_assoc, ToString.toString] using Padded.mk (left := "    ") (right := "")
      (by decide) (Item.wire (hd _ (wire_declared hm)) (renderType_syntax width)) whitespace_empty
  · cases hr

private theorem renderItem_syntax {sv : SVModule} {pairs item text}
    (hr : renderItem "    " item = some text) (hm : item ∈ sv.items)
    (hi : combItems sv.items = some pairs) (hb : AssignmentsBound sv pairs)
    (hd : ∀ x, Declared sv x → Identifier x) : Padded Item item text := by
  cases item <;> simp only [renderItem] at hr
  all_goals try { cases hr }
  rename_i lhs rhs
  cases lhs
  all_goals try { cases hr }
  rename_i name
  simp only [bind, Option.bind_eq_some_iff] at hr
  obtain ⟨s, hs, he⟩ := hr
  cases he
  obtain ⟨hl, he⟩ := hb _ (combItems_assignment hi hm)
  simpa [← String.append_assoc, ToString.toString] using Padded.mk (left := "    ") (right := "") (by decide)
    (Item.assign (hd _ hl) (renderExpr_syntax hs (exprBound_mono he hd))) whitespace_empty

private theorem moduleComment_syntax (name : String) :
    Comments (Sparkle.Backend.Verilog.moduleComment name) := by
  have h : ∀ c ∈ (" Module: " ++ Sparkle.Backend.Verilog.commentLabel name).toList,
      c ≠ '\n' ∧ c ≠ '\r' := by
    intro c hc
    simp only [String.toList_append, List.mem_append] at hc
    rcases hc with hc | hc
    · revert hc; decide +revert
    · exact commentLabel_lineText name c hc
  have hh := Comments.line (label := " Generated by Sparkle HDL") (by decide)
    (Comments.line h (Comments.pad (left := "\n") (right := "") (by decide) Comments.nil whitespace_empty))
  simpa [Sparkle.Backend.Verilog.moduleComment, String.append_assoc,
    ← String.append_assoc (s₁ := "//") (s₂ := " Module: "),
    ← String.append_assoc (s₁ := "// Generated by Sparkle HDL\n") (s₂ := "// Module: ")] using hh

/-- Byte equality plus lexical and binding invariants entails a derivation
of the entire text as the SAME AST. No parse-success premise is supplied. -/
theorem renderModule_syntax {sv : SVModule} {name count text pairs}
    (hr : renderModule name count sv = some text)
    (hn : Identifier sv.name)
    (hd : ∀ entry ∈ declarationTable sv, Identifier entry.1)
    (hi : combItems sv.items = some pairs) (hb : AssignmentsBound sv pairs) :
    Tools.SVParser.ConcreteSyntax.Module sv text := by
  have hdecl : ∀ x, Declared sv x → Identifier x := by
    intro x ⟨entry, hm, he⟩; subst x; exact hd entry hm
  unfold renderModule at hr
  split at hr
  · cases hr
  · rename_i hparams
    have hp : sv.params = [] := by simpa using hparams
    simp only [bind, Option.bind_eq_some_iff] at hr
    obtain ⟨ps, hps, ws, hws, bs, hbs, he⟩ := hr
    cases he
    have ports := ports_intercalate (mapM_phrases hps (fun p hm _ he =>
      renderPort_syntax he (hdecl _ (port_declared hm))))
    have wires := items_intercalate (sep := "\n") (by decide)
      (mapM_phrases hws (fun item hm _ he =>
        renderWire_syntax he (List.mem_of_mem_take hm) hdecl))
    have body := items_intercalate (sep := "\n\n") (by decide)
      (mapM_phrases hbs (fun item hm _ he =>
        renderItem_syntax he (List.mem_of_mem_drop hm) hi hb hdecl))
    let wireText := if ws.isEmpty then "" else "\n" ++ String.intercalate "\n" ws ++ "\n" ++ "\n"
    let bodyText := if bs.isEmpty then "" else "\n" ++ String.intercalate "\n\n" bs ++ "\n"
    have hw : Items (sv.items.take count) wireText := by
      dsimp [wireText]; split
      · rename_i hnil; have he : ws = [] := by simpa using hnil
        rw [he] at wires; exact wires
      · simpa [String.append_assoc] using
          Items.pad (left := "\n") (right := "\n\n") (by decide) wires (by decide)
    have hbody : Items (sv.items.drop count) bodyText := by
      dsimp [bodyText]; split
      · rename_i hnil; have he : bs = [] := by simpa using hnil
        rw [he] at body; exact body
      · exact Items.pad (by decide) body (by decide)
    have hitems : Items sv.items (wireText ++ bodyText ++ "\n") := by
      have hh := items_append hw hbody
      rw [List.take_append_drop] at hh
      simpa using Items.pad (left := "") (right := "\n") whitespace_empty hh (by decide)
    have hports : Ports sv.ports
        (if ps.isEmpty then "" else "\n    " ++ String.intercalate ",\n    " ps ++ "\n") := by
      split
      · rename_i hnil; have he : ps = [] := by simpa using hnil
        rw [he] at ports; exact ports
      · exact Ports.pad (by decide) ports (by decide)
    have hmod := Tools.SVParser.ConcreteSyntax.Module.module hn (moduleComment_syntax name)
      hports hitems (beforePorts := "") (afterPorts := "") (afterHeader := "\n")
      (afterEnd := "\n") whitespace_empty whitespace_empty (by decide) (by decide)
    rcases sv with ⟨name', params, ports', items⟩
    dsimp at hp
    subst params
    simpa [wireText, bodyText, String.append_assoc, ToString.toString,
      ← String.append_assoc (s₁ := " ") (s₂ := "(")] using hmod

end Tools.ShippingSyntaxSoundness

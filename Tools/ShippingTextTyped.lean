import Tools.ShippingSeqCheckTyped
import Tools.ShippingMachineCleanup

/-! # From statements typed in the WIRE table to the emitter's text check (G1, pure)

`Tools.ShippingSeqCheckTyped.core_text_same` reduces conjuncts 2 and 3 of
`textCheckI` to four hypotheses stated in the EMITTER's width tables
(`wofOf m`, `weS m`: wires ++ inputs ++ outputs by sanitized name). What a
compiler run gives is typedness in the WIRE table
`Tools.ShippingEntrySoundness.weOf m` (the declared wires by raw name; `0`
elsewhere). This file is the bridge, with no run:

* `pos_wire`: a name of positive wire-table width in a module with
  sanitize-stable wire names is a wire, the two tables agree on it, and it
  is declared in the emitter's map.
* `moduleWof_output`: an OUTPUT PORT whose name is no wire's and no input's
  sanitized name, among sanitize-stable distinct output names, of a scalar
  type, has its own entry in the emitter's map: `some ty.bitWidth`.
* `mem_seqNames`: a name of `seqNames body` is read by an assignment, or is
  a register's output or read by its input.
* `TypedIn m`: the module's statements are assignments, registers and
  instances; every assignment `l := r` is `TypedExpr (weOf m) r n` with
  `weOf m l = n`, or `l` an output port of width `n`; every register input
  is typed at its output's width; the wire names are sanitize-stable; the
  output ports are apart from the wires and inputs, stable, distinct, scalar.
* `TypedIn.text`: `hread`, `hA`, `hR` of `core_text_same` (its `hwn` is the
  field `wn`).
* `TypedIn.seqCheck`: conjuncts 2 and 3 of `textCheckI` for `m` ITSELF.
* `designCheck_same_of_typedIn`: `designCheck` of the shipped module in the
  case `checkedOptimize b = b`, from `RunFacts` and `TypedIn b`
  (`portsMatchB` and the children's check as hypotheses).

`scalarTy`: the decidable form of "one bit or a bit vector".

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingTextTyped
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.OptCheck (checkedOptimize)
open Tools.ShippingTypedExprSoundness (TypedExpr)
open Tools.ShippingSeqCheckTyped (Decl)

/-- One bit or a bit vector (the types the emitter's width map knows). -/
def scalarTy : Sparkle.IR.Type.HWType → Bool
  | .bit => true
  | .bitVector _ => true
  | _ => false

theorem scalarTy_spec {ty : Sparkle.IR.Type.HWType} (h : scalarTy ty = true) :
    ty = .bit ∨ ∃ n, ty = .bitVector n := by
  cases ty with
  | bit => exact Or.inl rfl
  | bitVector n => exact Or.inr ⟨n, rfl⟩
  | _ => simp [scalarTy] at h

/-- **A name of positive wire-table width**: it is a wire, the emitter's
width of it is the wire table's, and it is declared and sanitize-stable. -/
theorem pos_wire {m : Sparkle.IR.AST.Module}
    (hwn : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) {x : String}
    (hx : 0 < Tools.ShippingEntrySoundness.weOf m x) :
    x ∈ m.wires.map (·.name) ∧
      Tools.ShippingDesignSV.weS m x = Tools.ShippingEntrySoundness.weOf m x ∧
      Decl (Tools.ShippingDesignSV.wofOf m) x := by
  have hmem : x ∈ m.wires.map (·.name) := by
    have hx' := hx
    unfold Tools.ShippingEntrySoundness.weOf at hx'
    cases hf : m.wires.find? (fun p => p.name == x) with
    | none => rw [hf] at hx'; simp at hx'
    | some p =>
      have hn : p.name = x := by simpa using List.find?_some hf
      exact List.mem_map.mpr ⟨p, List.mem_of_find?_eq_some hf, hn⟩
  have hw : Tools.ShippingDesignSV.weS m x = Tools.ShippingEntrySoundness.weOf m x :=
    (Tools.ShippingWidthTables.declWidth_eq_weS hwn hmem).symm.trans
      (congrFun (show Sparkle.IR.RegDedup.declWidth m = Tools.ShippingEntrySoundness.weOf m
        from rfl) x)
  obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hmem
  have hpn' : p.name = x := hpn
  refine ⟨hmem, hw, ⟨by rw [← hpn']; exact hwn p hp, ?_⟩⟩
  cases hk : Tools.SVParser.RoundtripProof.moduleWof m x with
  | some k =>
    first
      | exact ⟨k, hk⟩
      | exact ⟨k, rfl⟩
  | none =>
    have h0 : Tools.ShippingDesignSV.weS m x = 0 := by
      show (Tools.SVParser.RoundtripProof.moduleWof m x).getD 0 = 0
      simp [hk]
    rw [h0] at hw
    exfalso
    omega

/-- A list whose elements all fail `p` is skipped by `find?`. -/
theorem find?_append_none {α : Type} (p : α → Bool) :
    ∀ (l₁ l₂ : List α), (∀ a ∈ l₁, p a = false) → (l₁ ++ l₂).find? p = l₂.find? p
  | [], _, _ => rfl
  | a :: l₁, l₂, h => by
    have ha : p a = false := h a (List.Mem.head _)
    have ih := find?_append_none p l₁ l₂ (fun b hb => h b (List.Mem.tail _ hb))
    simp only [List.cons_append, List.find?_cons, ha]
    exact ih

/-- **An output port's entry in the emitter's width map is its own**, when
no wire and no input has its name as sanitized name. -/
theorem moduleWof_output {m : Sparkle.IR.AST.Module} {q : Port}
    (hw : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name ≠ q.name)
    (hi : ∀ p ∈ m.inputs, Sparkle.Backend.Verilog.sanitizeName p.name ≠ q.name)
    (hs : ∀ p ∈ m.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (nd : (m.outputs.map (·.name)).Nodup) (hq : q ∈ m.outputs)
    (hty : q.ty = .bit ∨ ∃ n, q.ty = .bitVector n) :
    Tools.SVParser.RoundtripProof.moduleWof m q.name = some q.ty.bitWidth := by
  have h3 : m.outputs.find? (fun p => Sparkle.Backend.Verilog.sanitizeName p.name == q.name) =
      some q :=
    (Tools.ShippingSVBridge.find_sanitized m.outputs q.name hs).trans
      (Tools.ShippingEntrySoundness.find?_of_nodup nd hq)
  have hfind : (m.wires ++ m.inputs ++ m.outputs).find?
      (fun p => Sparkle.Backend.Verilog.sanitizeName p.name == q.name) = some q :=
    (find?_append_none (fun p : Port => Sparkle.Backend.Verilog.sanitizeName p.name == q.name)
      (m.wires ++ m.inputs) m.outputs (fun p hp => by
        rcases List.mem_append.mp hp with h | h
        · exact Bool.eq_false_iff.mpr (fun hb => hw p h (beq_iff_eq.mp hb))
        · exact Bool.eq_false_iff.mpr (fun hb => hi p h (beq_iff_eq.mp hb)))).trans h3
  simp only [Tools.SVParser.RoundtripProof.moduleWof]
  rw [hfind]
  rcases hty with h | ⟨n, h⟩
  · have hb : q.ty.bitWidth = 1 := congrArg Sparkle.IR.Type.HWType.bitWidth h
    rw [hb]
    simp [h]
  · have hb : q.ty.bitWidth = n := congrArg Sparkle.IR.Type.HWType.bitWidth h
    rw [hb]
    simp [h]

/-- A name of `seqNames body` is read by an assignment, or is a register's
output or read by its input. -/
theorem mem_seqNames : ∀ (body : List Stmt) (x : String),
    x ∈ Tools.ShippingSeqSVSoundness.seqNames body →
    (∃ l r, Stmt.assign l r ∈ body ∧ x ∈ Sparkle.IR.Reorder.refsOf r) ∨
      (∃ o c rk i iv, Stmt.register o c rk i iv ∈ body ∧
        (x = o ∨ x ∈ Sparkle.IR.Reorder.refsOf i))
  | [], x, h => by
    have h' : x ∈ ([] : List String) := h
    cases h'
  | st :: rest, x, h => by
    have tl : x ∈ Tools.ShippingSeqSVSoundness.seqNames rest →
        (∃ l r, Stmt.assign l r ∈ st :: rest ∧ x ∈ Sparkle.IR.Reorder.refsOf r) ∨
          (∃ o c rk i iv, Stmt.register o c rk i iv ∈ st :: rest ∧
            (x = o ∨ x ∈ Sparkle.IR.Reorder.refsOf i)) := by
      intro h'
      rcases mem_seqNames rest x h' with ⟨l, r, hm, hx⟩ | ⟨o, c, rk, i, iv, hm, hx⟩
      · exact Or.inl ⟨l, r, List.Mem.tail _ hm, hx⟩
      · exact Or.inr ⟨o, c, rk, i, iv, List.Mem.tail _ hm, hx⟩
    cases st with
    | assign l r =>
      have h' : x ∈ Sparkle.IR.Reorder.refsOf r ++ Tools.ShippingSeqSVSoundness.seqNames rest := h
      rcases List.mem_append.mp h' with h1 | h1
      · exact Or.inl ⟨l, r, List.Mem.head _, h1⟩
      · exact tl h1
    | register o c rk i iv =>
      have h' : x ∈ o :: (Sparkle.IR.Reorder.refsOf i ++
          Tools.ShippingSeqSVSoundness.seqNames rest) := h
      rcases List.mem_cons.mp h' with h1 | h1
      · exact Or.inr ⟨o, c, rk, i, iv, List.Mem.head _, Or.inl h1⟩
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact Or.inr ⟨o, c, rk, i, iv, List.Mem.head _, Or.inr h2⟩
        · exact tl h2
    | _ =>
      first
        | exact tl h
        | exact tl (by simpa [Tools.ShippingSeqSVSoundness.seqNames] using h)

/-- **A module typed and declared in its own wire table**, with output ports
the emitter's map resolves to themselves. -/
structure TypedIn (m : Sparkle.IR.AST.Module) : Prop where
  /-- (hwn) the wire names are sanitize-stable -/
  wn : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name
  /-- no wire has an output port's name -/
  ow : ∀ q ∈ m.outputs, ∀ p ∈ m.wires, p.name ≠ q.name
  /-- no input's sanitized name is an output port's name -/
  oi : ∀ q ∈ m.outputs, ∀ p ∈ m.inputs, Sparkle.Backend.Verilog.sanitizeName p.name ≠ q.name
  /-- the output port names are sanitize-stable -/
  ostable : ∀ q ∈ m.outputs, Sparkle.Backend.Verilog.sanitizeName q.name = q.name
  ond : (m.outputs.map (·.name)).Nodup
  /-- the output ports are one bit or bit vectors -/
  oty : ∀ q ∈ m.outputs, q.ty = .bit ∨ ∃ n, q.ty = .bitVector n
  /-- assignments, registers and instances only -/
  kinds : ∀ st ∈ m.body, Tools.ShippingHierSVSoundness.seqStmtOkI st = true
  /-- an assignment is typed at its target's width: a wire's declared width,
  or an output port's -/
  asg : ∀ l r, Stmt.assign l r ∈ m.body →
    ∃ n, TypedExpr (Tools.ShippingEntrySoundness.weOf m) r n ∧
      (Tools.ShippingEntrySoundness.weOf m l = n ∨
        ∃ q ∈ m.outputs, q.name = l ∧ q.ty.bitWidth = n)
  /-- a register's input is typed at its output's declared width -/
  reg : ∀ o c rk i iv, Stmt.register o c rk i iv ∈ m.body →
    TypedExpr (Tools.ShippingEntrySoundness.weOf m) i (Tools.ShippingEntrySoundness.weOf m o)

/-- **`hread`, `hA`, `hR` of `core_text_same`**, for a module typed in its
own wire table. -/
theorem TypedIn.text {m : Sparkle.IR.AST.Module} (h : TypedIn m) :
    (∀ x ∈ Tools.ShippingSeqSVSoundness.seqNames m.body, x ∈ m.wires.map (·.name)) ∧
    (∀ l r, Stmt.assign l r ∈ m.body →
      Decl (Tools.ShippingDesignSV.wofOf m) l ∧
        TypedExpr (Tools.ShippingDesignSV.weS m) r (Tools.ShippingDesignSV.weS m l) ∧
        ∀ x ∈ Sparkle.IR.Reorder.refsOf r, Decl (Tools.ShippingDesignSV.wofOf m) x) ∧
    (∀ o c rk i iv, Stmt.register o c rk i iv ∈ m.body →
      (∃ k, Tools.ShippingDesignSV.wofOf m o = some k) ∧
        TypedExpr (Tools.ShippingDesignSV.weS m) i (Tools.ShippingDesignSV.weS m o) ∧
        ∀ x ∈ Sparkle.IR.Reorder.refsOf i, Decl (Tools.ShippingDesignSV.wofOf m) x) := by
  have pw : ∀ x : String, 0 < Tools.ShippingEntrySoundness.weOf m x →
      (x ∈ m.wires.map (·.name) ∧
        Tools.ShippingDesignSV.weS m x = Tools.ShippingEntrySoundness.weOf m x ∧
        Decl (Tools.ShippingDesignSV.wofOf m) x) := fun x hx => pos_wire h.wn hx
  have cv : ∀ {e : Sparkle.IR.AST.Expr} {n : Nat},
      TypedExpr (Tools.ShippingEntrySoundness.weOf m) e n →
      TypedExpr (Tools.ShippingDesignSV.weS m) e n ∧
        ∀ x ∈ Sparkle.IR.Reorder.refsOf e, Decl (Tools.ShippingDesignSV.wofOf m) x := by
    intro e n ht
    exact ⟨ht.we_congr (fun x hx => (pw x (ht.refs_positive x hx)).2.1),
      fun x hx => (pw x (ht.refs_positive x hx)).2.2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases mem_seqNames m.body x hx with ⟨l, r, hm, hxr⟩ | ⟨o, c, rk, i, iv, hm, hxo⟩
    · obtain ⟨n, ht, -⟩ := h.asg l r hm
      exact (pw x (ht.refs_positive x hxr)).1
    · have ht := h.reg o c rk i iv hm
      rcases hxo with hxo | hxo
      · rw [hxo]
        exact (pw o ht.positive).1
      · exact (pw x (ht.refs_positive x hxo)).1
  · intro l r hm
    obtain ⟨n, ht, hl⟩ := h.asg l r hm
    obtain ⟨ht', hrefs⟩ := cv ht
    rcases hl with hl | ⟨q, hq, hqn, hqw⟩
    · have hpos : 0 < Tools.ShippingEntrySoundness.weOf m l := by
        rw [hl]
        exact ht.positive
      obtain ⟨-, hwl, hdl⟩ := pw l hpos
      refine ⟨hdl, ?_, hrefs⟩
      rw [hwl, hl]
      exact ht'
    · have hwof := moduleWof_output (m := m) (q := q)
        (fun p hp => by
          rw [h.wn p hp]
          exact h.ow q hq p hp)
        (h.oi q hq) h.ostable h.ond hq (h.oty q hq)
      rw [hqn] at hwof
      have hwl : Tools.ShippingDesignSV.weS m l = n := by
        show (Tools.SVParser.RoundtripProof.moduleWof m l).getD 0 = n
        rw [hwof]
        exact hqw
      have hst : Sparkle.Backend.Verilog.sanitizeName l = l := by
        rw [← hqn]
        exact h.ostable q hq
      refine ⟨⟨hst, _, hwof⟩, ?_, hrefs⟩
      rw [hwl]
      exact ht'
  · intro o c rk i iv hm
    have ht := h.reg o c rk i iv hm
    obtain ⟨ht', hrefs⟩ := cv ht
    obtain ⟨-, hwo, hdo⟩ := pw o ht.positive
    refine ⟨hdo.2, ?_, hrefs⟩
    rw [hwo]
    exact ht'

/-- **Conjuncts 2 and 3 of `textCheckI` of the module itself** (no
optimizer in the statement). -/
theorem TypedIn.seqCheck {m : Sparkle.IR.AST.Module} (h : TypedIn m) :
    Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf m)
        (Tools.ShippingDesignSV.weS m) m.body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames m.body).all
        (fun x => Sparkle.IR.RegDedup.declWidth m x == Tools.ShippingDesignSV.weS m x) = true := by
  obtain ⟨hread, hA, hR⟩ := h.text
  exact ⟨Tools.ShippingSeqCheckTyped.seqCheck_of_typed m.body h.kinds hA hR,
    Tools.ShippingWidthTables.seqNames_widths h.wn hread⟩

/-- **`designCheck` of the shipped module when it is shipped as it is**, with
the four text hypotheses of `core_designCheck_same` discharged by `TypedIn`. -/
theorem designCheck_same_of_typedIn
    {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {b : Sparkle.IR.AST.Module}
    (h : Tools.ShippingGuardsSound.RunFacts C b) (ht : TypedIn b)
    (hsame : checkedOptimize b = b) (n : Nat)
    (hports : Tools.ShippingDesignSV.portsMatchB C b = true)
    (hkids : Tools.ShippingDesignSV.kidsPass C (Tools.ShippingChecksDesign.kidCheck C n)
      b.body = true) :
    Tools.ShippingDesignSV.designCheck C n (checkedOptimize b) = true := by
  obtain ⟨hread, hA, hR⟩ := ht.text
  exact Tools.ShippingSeqCheckTyped.core_designCheck_same h hsame n ht.wn hread hA hR hports hkids

end Tools.ShippingTextTyped

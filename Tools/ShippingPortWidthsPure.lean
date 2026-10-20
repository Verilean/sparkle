import Tools.ShippingLeafTyped

/-! # Emitted widths of INPUT ports: the pure part (G1, port matching)

`portsMatchB` compares, per connection, the emitter's width `weS` of a
parent wire with the emitter's width of the child's PORT. For an input port
of a machine's module this file has the facts that need no run:

* `nonDom`, `declN`, `declTys`, `declWidths`: the declared (non-domain)
  binders of a machine before its slots and `let`s, their port types and
  widths — DATA of a `MachineData` (`declWidths d` is what `callArgsOk`'s
  `kidIns` must be for a leaf child with data `d`).
* `inputPorts_zip_tys`, `machPorts_tys`: the binder walk declares one port
  per non-domain binder, of the binder's type (`kindTy`), in order — the
  variant of `Tools.ShippingMachineEntry.inputPorts_types` WITH domain
  binders in the list.
* `kindTy_pos`: positive binders have ports of positive width.
* `inPort_weS`: an argument port (a non-clock input) whose name has, in the
  WIRE table, its type's width (the leaf clause of `MachineWired`) has that
  width in the emitter's map — it is a wire of positive width (`pos_wire`).
* `find?_cons_pos`, `find?_cons_neg`, `weS_of_input_find`: the emitter's map
  reads wires, then inputs, then outputs, by sanitized name; an input found
  first among the inputs, no wire having that sanitized name, of type `.bit`
  has width `1`.
* `wire_ne_clk`: an allocated name or the `next…` name of one is
  sanitize-stable and is neither `clk` nor `rst`.
* `weS_clk_rst`: inputs `A ++ clk :: rst :: X` with `A` allocated names, over
  allocated / `next…` wires: `weS m "clk" = 1 ∧ weS m "rst" = 1`.
* `inputs_clk_shape`, `weS_clk_rst_filtered`: the same for the input list of
  a machine WITH calls (`MachineWired`'s input clause: a filtered list).
* `seq_of_alloc_inputs`: allocated input names only ⇒ not a sequential child.
* `closeMachine_inputs`: the inputs of `closeMachine lay t`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingPortWidthsPure
open Lean
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineEntry (inputPorts kindTy machPorts)
open Tools.ShippingMixedEntrySoundness (Setup extend PositiveBinders)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingInstStmtG (inPortsOf isSeqChild)

/-! ## The declared binders' ports -/

/-- A binder that gets a port (a domain binder has none). -/
def nonDom (b : Name × MixedGateBinder) : Bool := b.2 != MixedGateBinder.domain

theorem nonDom_domain (name : Name) : nonDom (name, MixedGateBinder.domain) = false := by
  first
    | rfl
    | decide
    | simp [nonDom]

theorem nonDom_bool (name : Name) : nonDom (name, MixedGateBinder.bool) = true := by
  first
    | rfl
    | decide
    | simp [nonDom]

theorem nonDom_bits (name : Name) (n : Nat) : nonDom (name, MixedGateBinder.bits n) = true := by
  first
    | rfl
    | simp [nonDom]

/-- The number of binders before the slots and the `let`s (for a machine
without calls: the declaration's own binders). -/
def declN (d : MachineData) : Nat :=
  d.shape.binders.length - d.shape.layout.slots.length - d.shape.layout.lets

/-- The port types of the declared non-domain binders, in order. -/
def declTys (d : MachineData) : List Sparkle.IR.Type.HWType :=
  ((d.shape.binders.take (declN d)).filter nonDom).map fun b => kindTy b.2

/-- **The widths of a leaf machine's argument ports**, as data. -/
def declWidths (d : MachineData) : List Nat :=
  (declTys d).map fun ty => ty.bitWidth

/-- **The binder walk's port types, with domain binders in the list**: one
port per non-domain binder, of the binder's type, in order. -/
theorem inputPorts_zip_tys {bools : FVarId → Bool}
    {bits : (id : FVarId) → (n : Nat) → BitVec n} :
    ∀ (bs : List (Name × MixedGateBinder)) (ids : List FVarId) (a : Setup),
      bs.length ≤ ids.length →
      (inputPorts bools bits (bs.zip ids) a).map (fun p => p.ty) =
        (bs.filter nonDom).map (fun b => kindTy b.2)
  | [], ids, a, _ => by
    first
      | rfl
      | (rw [List.zip_nil_left]; rfl)
      | simp [inputPorts]
  | b :: bs, [], a, h => by
    first
      | exact absurd h (Nat.not_succ_le_zero _)
      | (simp at h)
  | (name, .domain) :: bs, id :: ids, a, h => by
    have h' : bs.length ≤ ids.length := by
      first
        | exact Nat.le_of_succ_le_succ h
        | simpa using h
    have ih := inputPorts_zip_tys (bools := bools) (bits := bits) bs ids
      (extend a ((name, .domain), id) bools bits) h'
    have hneg : ¬ (nonDom (name, MixedGateBinder.domain) = true) := by
      rw [nonDom_domain name]
      exact Bool.false_ne_true
    rw [List.zip_cons_cons,
      List.filter_cons_of_neg (p := nonDom) (a := (name, MixedGateBinder.domain)) (l := bs) hneg]
    first
      | exact ih
      | (simp only [inputPorts]; exact ih)
  | (name, .bool) :: bs, id :: ids, a, h => by
    have h' : bs.length ≤ ids.length := by
      first
        | exact Nat.le_of_succ_le_succ h
        | simpa using h
    have ih := inputPorts_zip_tys (bools := bools) (bits := bits) bs ids
      (extend a ((name, .bool), id) bools bits) h'
    rw [List.zip_cons_cons,
      List.filter_cons_of_pos (p := nonDom) (a := (name, MixedGateBinder.bool)) (l := bs)
        (nonDom_bool name)]
    simp only [inputPorts, List.map_cons]
    first
      | exact congrArg (List.cons _) ih
      | (rw [ih]; rfl)
      | rw [ih]
  | (name, .bits n) :: bs, id :: ids, a, h => by
    have h' : bs.length ≤ ids.length := by
      first
        | exact Nat.le_of_succ_le_succ h
        | simpa using h
    have ih := inputPorts_zip_tys (bools := bools) (bits := bits) bs ids
      (extend a ((name, .bits n), id) bools bits) h'
    rw [List.zip_cons_cons,
      List.filter_cons_of_pos (p := nonDom) (a := (name, MixedGateBinder.bits n)) (l := bs)
        (nonDom_bits name n)]
    simp only [inputPorts, List.map_cons]
    first
      | exact congrArg (List.cons _) ih
      | (rw [ih]; rfl)
      | rw [ih]

/-- The same for the ports a machine's binders get. -/
theorem machPorts_tys (c : Name) (ids : List FVarId) (cache : IO.Ref (ExprStructMap String))
    (bs : List (Name × MixedGateBinder)) (h : bs.length ≤ ids.length) :
    (machPorts c ids cache bs).map (fun p => p.ty) =
      (bs.filter nonDom).map (fun b => kindTy b.2) := by
  unfold Tools.ShippingMachineEntry.machPorts
  exact inputPorts_zip_tys bs ids _ h

/-- A positive binder's port has positive width. -/
theorem kindTy_pos {bs : List (Name × MixedGateBinder)} (h : PositiveBinders bs)
    {bn : Name × MixedGateBinder} (hb : bn ∈ bs) : 0 < (kindTy bn.2).bitWidth := by
  obtain ⟨name, k⟩ := bn
  cases k with
  | domain =>
    first
      | exact Nat.zero_lt_succ 0
      | decide
  | bool =>
    first
      | exact Nat.zero_lt_succ 0
      | decide
  | bits n => exact h name n hb

theorem getElem?_map_some {α β : Type} (f : α → β) {l : List α} {j : Nat} {a : α}
    (h : l[j]? = some a) : (l.map f)[j]? = some (f a) := by
  simp [h]

/-! ## An argument port's emitted width -/

/-- **The emitted width of an argument port**: at position `j` of the
non-clock inputs, the width of the type of the `j`-th non-domain binder. -/
theorem inPort_weS {m : Sparkle.IR.AST.Module} {bs : List (Name × MixedGateBinder)}
    (hwn : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (hty : (inPortsOf m).map (fun p => p.ty) = (bs.filter nonDom).map (fun b => kindTy b.2))
    (hpos : ∀ bn ∈ bs, 0 < (kindTy bn.2).bitWidth)
    (hW : ∀ p ∈ inPortsOf m,
      (p.ty = Sparkle.IR.Type.HWType.bit → Tools.ShippingEntrySoundness.weOf m p.name = 1) ∧
      ∀ k, p.ty = Sparkle.IR.Type.HWType.bitVector k →
        Tools.ShippingEntrySoundness.weOf m p.name = k)
    {j : Nat} {q : Port} (hq : (inPortsOf m)[j]? = some q) :
    ∃ wd, ((((bs.filter nonDom).map (fun b => kindTy b.2)).map
        (fun ty : Sparkle.IR.Type.HWType => ty.bitWidth))[j]? = some wd) ∧
      Tools.ShippingDesignSV.weS m q.name = wd := by
  have hqm : q ∈ inPortsOf m := List.mem_of_getElem? hq
  have h1 : ((inPortsOf m).map (fun p => p.ty))[j]? = some q.ty :=
    getElem?_map_some (fun p : Port => p.ty) hq
  rw [hty] at h1
  have h2 := h1
  rw [List.getElem?_map] at h2
  cases hb : (bs.filter nonDom)[j]? with
  | none =>
    rw [hb] at h2
    cases h2
  | some bn =>
    rw [hb] at h2
    have hqt : kindTy bn.2 = q.ty := by
      simpa only [Option.map_some, Option.some.injEq] using h2
    have hbm : bn ∈ bs := (List.mem_filter.mp (List.mem_of_getElem? hb)).1
    have hp0 : 0 < (kindTy bn.2).bitWidth := hpos bn hbm
    obtain ⟨hbit, hvec⟩ := hW q hqm
    have hwq : Tools.ShippingEntrySoundness.weOf m q.name = q.ty.bitWidth := by
      rcases Tools.ShippingTransitionPortTys.kindTy_shape bn.2 with hk | ⟨n, hk⟩
      · have hq1 : q.ty = Sparkle.IR.Type.HWType.bit := hqt.symm.trans hk
        exact (hbit hq1).trans (congrArg Sparkle.IR.Type.HWType.bitWidth hq1).symm
      · have hq1 : q.ty = Sparkle.IR.Type.HWType.bitVector n := hqt.symm.trans hk
        exact (hvec n hq1).trans (congrArg Sparkle.IR.Type.HWType.bitWidth hq1).symm
    have hpq : 0 < Tools.ShippingEntrySoundness.weOf m q.name := by
      rw [hwq, ← hqt]
      exact hp0
    obtain ⟨-, hws, -⟩ := Tools.ShippingTextTyped.pos_wire hwn hpq
    exact ⟨q.ty.bitWidth,
      getElem?_map_some (fun ty : Sparkle.IR.Type.HWType => ty.bitWidth) h1, hws.trans hwq⟩

/-! ## The clock and the reset -/

theorem find?_cons_pos {α : Type} (p : α → Bool) (a : α) (l : List α) (h : p a = true) :
    (a :: l).find? p = some a := by
  simp only [List.find?_cons, h]

theorem find?_cons_neg {α : Type} (p : α → Bool) (a : α) (l : List α) (h : p a = false) :
    (a :: l).find? p = l.find? p := by
  simp only [List.find?_cons, h]

theorem clk_ne_rst : ("clk" : String) ≠ "rst" := by
  intro h
  have h2 : ("clk" : String).toList.head? = ("rst" : String).toList.head? :=
    congrArg (fun s : String => s.toList.head?) h
  revert h2
  decide

/-- **An input found first among the inputs, of type `.bit`, under no wire
of that sanitized name, has emitted width 1.** -/
theorem weS_of_input_find {m : Sparkle.IR.AST.Module} {x : String} {q : Port}
    (hw : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name ≠ x)
    (hf : m.inputs.find? (fun p => Sparkle.Backend.Verilog.sanitizeName p.name == x) = some q)
    (hty : q.ty = Sparkle.IR.Type.HWType.bit) : Tools.ShippingDesignSV.weS m x = 1 := by
  have hfi : (m.inputs ++ m.outputs).find?
      (fun p => Sparkle.Backend.Verilog.sanitizeName p.name == x) = some q := by
    first
      | (rw [List.find?_append, hf]; rfl)
      | simp [List.find?_append, hf]
  have hfind : (m.wires ++ m.inputs ++ m.outputs).find?
      (fun p => Sparkle.Backend.Verilog.sanitizeName p.name == x) = some q := by
    rw [List.append_assoc]
    exact (Tools.ShippingTextTyped.find?_append_none
      (fun p : Port => Sparkle.Backend.Verilog.sanitizeName p.name == x)
      m.wires (m.inputs ++ m.outputs)
      (fun p hp => Bool.eq_false_iff.mpr (fun hb => hw p hp (beq_iff_eq.mp hb)))).trans hfi
  have h1 : Tools.SVParser.RoundtripProof.moduleWof m x = some 1 := by
    simp only [Tools.SVParser.RoundtripProof.moduleWof]
    rw [hfind]
    simp [hty]
  show (Tools.SVParser.RoundtripProof.moduleWof m x).getD 0 = 1
  exact congrArg (fun o : Option Nat => o.getD 0) h1

/-- An allocated name, or the `next…` name of one: sanitize-stable, and
neither the clock nor the reset. -/
theorem wire_ne_clk {x : String}
    (h : Sparkle.IR.NameHints.Allocated x ∨
      ∃ y, Sparkle.IR.NameHints.Allocated y ∧ x = nextName y) :
    Sparkle.Backend.Verilog.sanitizeName x = x ∧ x ≠ "clk" ∧ x ≠ "rst" := by
  rcases h with ha | ⟨y, hy, e⟩
  · exact ⟨Tools.ShippingNamesStable.sanitizeName_of_allocated ha,
      fun e => Tools.ShippingMachineCleanup.not_allocated_clk (e ▸ ha),
      fun e => Tools.ShippingRegisterSoundness.not_allocated_rst (e ▸ ha)⟩
  · rw [e]
    exact ⟨Tools.ShippingNamesNext.sanitizeName_nextName hy,
      (Tools.ShippingCallsAssemblyG.nextName_ne_clk y).1,
      (Tools.ShippingCallsAssemblyG.nextName_ne_clk y).2⟩

/-- **The clock and the reset are one bit in the emitter's width map** of a
module whose wires are allocated / `next…` names and whose inputs are
allocated names, then `clk`, then `rst`. -/
theorem weS_clk_rst {m : Sparkle.IR.AST.Module} {A X : List Port}
    (hw : ∀ p ∈ m.wires, Sparkle.IR.NameHints.Allocated p.name ∨
      ∃ y, Sparkle.IR.NameHints.Allocated y ∧ p.name = nextName y)
    (hA : ∀ p ∈ A, Sparkle.IR.NameHints.Allocated p.name)
    (hi : m.inputs = A ++ (({ name := "clk", ty := .bit } : Port) ::
      ({ name := "rst", ty := .bit } : Port) :: X)) :
    Tools.ShippingDesignSV.weS m "clk" = 1 ∧ Tools.ShippingDesignSV.weS m "rst" = 1 := by
  have hwc : ∀ x : String, x = "clk" ∨ x = "rst" → ∀ p ∈ m.wires,
      Sparkle.Backend.Verilog.sanitizeName p.name ≠ x := by
    intro x hx p hp
    obtain ⟨hs, h1, h2⟩ := wire_ne_clk (hw p hp)
    rw [hs]
    rcases hx with e | e
    · rw [e]
      exact h1
    · rw [e]
      exact h2
  have hAc : ∀ x : String, x = "clk" ∨ x = "rst" → ∀ p ∈ A,
      (Sparkle.Backend.Verilog.sanitizeName p.name == x) = false := by
    intro x hx p hp
    obtain ⟨hs, h1, h2⟩ := wire_ne_clk (Or.inl (hA p hp))
    rw [hs]
    rcases hx with e | e
    · rw [e]
      exact Bool.eq_false_iff.mpr (fun hb => h1 (beq_iff_eq.mp hb))
    · rw [e]
      exact Bool.eq_false_iff.mpr (fun hb => h2 (beq_iff_eq.mp hb))
  have hcc : (Sparkle.Backend.Verilog.sanitizeName
      ({ name := "clk", ty := .bit } : Port).name == "clk") = true :=
    beq_iff_eq.mpr Tools.ShippingNamesClk.sanitizeName_clk
  have hrr : (Sparkle.Backend.Verilog.sanitizeName
      ({ name := "rst", ty := .bit } : Port).name == "rst") = true :=
    beq_iff_eq.mpr Tools.ShippingNamesClk.sanitizeName_rst
  have hcr : (Sparkle.Backend.Verilog.sanitizeName
      ({ name := "clk", ty := .bit } : Port).name == "rst") = false :=
    Bool.eq_false_iff.mpr (fun hb =>
      clk_ne_rst (Tools.ShippingNamesClk.sanitizeName_clk.symm.trans (beq_iff_eq.mp hb)))
  constructor
  · refine weS_of_input_find (q := ({ name := "clk", ty := .bit } : Port))
      (hwc "clk" (Or.inl rfl)) ?_ rfl
    rw [hi]
    exact (Tools.ShippingTextTyped.find?_append_none
      (fun p : Port => Sparkle.Backend.Verilog.sanitizeName p.name == "clk") A
      (({ name := "clk", ty := .bit } : Port) :: ({ name := "rst", ty := .bit } : Port) :: X)
      (hAc "clk" (Or.inl rfl))).trans
      (find?_cons_pos (fun p : Port => Sparkle.Backend.Verilog.sanitizeName p.name == "clk")
        ({ name := "clk", ty := .bit } : Port) (({ name := "rst", ty := .bit } : Port) :: X) hcc)
  · refine weS_of_input_find (q := ({ name := "rst", ty := .bit } : Port))
      (hwc "rst" (Or.inr rfl)) ?_ rfl
    rw [hi]
    exact ((Tools.ShippingTextTyped.find?_append_none
      (fun p : Port => Sparkle.Backend.Verilog.sanitizeName p.name == "rst") A
      (({ name := "clk", ty := .bit } : Port) :: ({ name := "rst", ty := .bit } : Port) :: X)
      (hAc "rst" (Or.inr rfl))).trans
      (find?_cons_neg (fun p : Port => Sparkle.Backend.Verilog.sanitizeName p.name == "rst")
        ({ name := "clk", ty := .bit } : Port) (({ name := "rst", ty := .bit } : Port) :: X)
        hcr)).trans
      (find?_cons_pos (fun p : Port => Sparkle.Backend.Verilog.sanitizeName p.name == "rst")
        ({ name := "rst", ty := .bit } : Port) X hrr)

/-- The input list of a machine with calls and slots (`MachineWired`'s input
clause), with the clock and the reset exposed. -/
theorem inputs_clk_shape {P E extra I : List Port} {f : Port → Bool}
    (hI : I = (P ++ E ++ extra).filter f)
    (hE : E = [({ name := "clk", ty := .bit } : Port), ({ name := "rst", ty := .bit } : Port)])
    (hc : f ({ name := "clk", ty := .bit } : Port) = true)
    (hr : f ({ name := "rst", ty := .bit } : Port) = true) :
    I = P.filter f ++ (({ name := "clk", ty := .bit } : Port) ::
      ({ name := "rst", ty := .bit } : Port) :: extra.filter f) := by
  have e1 : ([({ name := "clk", ty := .bit } : Port),
      ({ name := "rst", ty := .bit } : Port)]).filter f =
      [({ name := "clk", ty := .bit } : Port), ({ name := "rst", ty := .bit } : Port)] := by
    rw [List.filter_cons_of_pos (p := f) (a := ({ name := "clk", ty := .bit } : Port))
        (l := [({ name := "rst", ty := .bit } : Port)]) hc,
      List.filter_cons_of_pos (p := f) (a := ({ name := "rst", ty := .bit } : Port))
        (l := []) hr] <;> rfl
  have e2 : (P ++ E ++ extra).filter f = P.filter f ++ E.filter f ++ extra.filter f := by
    rw [List.filter_append, List.filter_append]
  rw [hI, e2, hE, e1, List.append_assoc] <;> rfl

/-- `weS_clk_rst` over the filtered input list of a machine with calls. -/
theorem weS_clk_rst_filtered {m : Sparkle.IR.AST.Module} {P0 E extra : List Port} {K : Nat}
    {f : Port → Bool}
    (hI : m.inputs = (P0.take K ++ E ++ extra).filter f)
    (hE : E = [({ name := "clk", ty := .bit } : Port), ({ name := "rst", ty := .bit } : Port)])
    (hc : f ({ name := "clk", ty := .bit } : Port) = true)
    (hr : f ({ name := "rst", ty := .bit } : Port) = true)
    (hw : ∀ p ∈ m.wires, Sparkle.IR.NameHints.Allocated p.name ∨
      ∃ y, Sparkle.IR.NameHints.Allocated y ∧ p.name = nextName y)
    (hP : ∀ p ∈ P0, Sparkle.IR.NameHints.Allocated p.name) :
    Tools.ShippingDesignSV.weS m "clk" = 1 ∧ Tools.ShippingDesignSV.weS m "rst" = 1 :=
  weS_clk_rst (A := (P0.take K).filter f) (X := extra.filter f) hw
    (fun p hp => hP p (List.mem_of_mem_take (List.mem_filter.mp hp).1))
    (inputs_clk_shape hI hE hc hr)

/-- A module whose inputs are allocated names has no clock and no reset. -/
theorem seq_of_alloc_inputs {m : Sparkle.IR.AST.Module}
    (hA : ∀ p ∈ m.inputs, Sparkle.IR.NameHints.Allocated p.name) : isSeqChild m = false := by
  cases hs : isSeqChild m with
  | false => rfl
  | true =>
    have hs' : (m.inputs.any fun p => p.name == "clk" || p.name == "rst") = true := hs
    obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp hs'
    have hpe' : (p.name == "clk" || p.name == "rst") = true := hpe
    obtain ⟨-, h1, h2⟩ := wire_ne_clk (Or.inl (hA p hp))
    rw [Bool.or_eq_true] at hpe'
    rcases hpe' with e | e
    · exact absurd (beq_iff_eq.mp e) h1
    · exact absurd (beq_iff_eq.mp e) h2

/-- **The inputs of the closed machine**: the transition's ports before the
slots, then `clk` and `rst` when there are slots. -/
theorem closeMachine_inputs {t : Sparkle.IR.AST.Module} {lay : Layout} {B : List Stmt}
    {w : String} (hbody : t.body = B ++ [.assign "out" (.ref w)]) :
    (lay.slots.isEmpty = true → (closeMachine lay t).inputs =
      t.inputs.take (t.inputs.length - lay.slots.length)) ∧
    (lay.slots.isEmpty = false → (closeMachine lay t).inputs =
      t.inputs.take (t.inputs.length - lay.slots.length) ++
        [({ name := "clk", ty := .bit } : Port), ({ name := "rst", ty := .bit } : Port)]) := by
  have hpw : packedWire? t.body = some w := by simp [packedWire?, hbody]
  have hMi : (closeMachine lay t).inputs =
      t.inputs.take (t.inputs.length - lay.slots.length) ++
        (if lay.slots.isEmpty then []
         else [({ name := "clk", ty := .bit } : Port), ({ name := "rst", ty := .bit } : Port)]) := by
    simp [closeMachine, hpw]
  constructor
  · intro hs
    rw [hMi, if_pos hs, List.append_nil]
  · intro hs
    have hn : ¬ (lay.slots.isEmpty = true) := by
      rw [hs]
      exact Bool.false_ne_true
    rw [hMi, if_neg hn]

end Tools.ShippingPortWidthsPure

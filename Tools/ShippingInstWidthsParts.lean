import Tools.ShippingOutsExtractedParts

/-! # `instOutWidthsOk` and `hierGate` from their parts (G1, conjuncts 8 and 1)

Nothing here mentions a run.

* `instOutWidthsOk_of`: the check from, for every instance statement, its
  child in the map and the width equation of every connected output port.
* `declWidth_of_unique`: the declared width of a name whose only wire is a
  one-bit or a bit-vector port is that port's width.
* `dropZW_wires_sub`: the zero-width cleanup adds no wire.
* `callStmtG_outWireF`: `callStmtG_outWire` with the FIELD — an output
  connection of a call group's instance connects the transition input of an
  entry `e` of the group, and its port is the entry's field `e.2`.
* `hierGate_of`, `hierBinds_of`: the statement-kind gate from an instance
  statement and "every statement is an instance, an assignment or a
  register"; `hierBinds` from the gate and `refineCheck flat flat`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingInstWidthsParts
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingHierOpen

/-- **`instOutWidthsOk` from its statements.** -/
theorem instOutWidthsOk_of {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {W : WEnv} :
    ∀ (body : List Stmt),
      (∀ mn i conns, Stmt.inst mn i conns ∈ body → ∃ child cwe, C mn = some (child, cwe) ∧
        ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (Expr.ref w) →
          W w = p.ty.bitWidth) →
      instOutWidthsOk C W body = true
  | [], _ => rfl
  | st :: rest, h => by
    have ih := instOutWidthsOk_of (C := C) (W := W) rest
      (fun mn i conns hm => h mn i conns (List.Mem.tail _ hm))
    cases st with
    | inst mn i conns =>
      obtain ⟨child, cwe, hc, hp⟩ := h mn i conns (List.Mem.head _)
      simp only [Tools.ShippingHierOpen.instOutWidthsOk, hc, ih, Bool.and_true]
      rw [List.all_eq_true]
      intro p hpm
      cases hl : conns.lookup p.name with
      | none => first | rfl | simp only [hl]
      | some e =>
        cases e with
        | ref w =>
          first
            | exact beq_iff_eq.mpr (hp p hpm w hl)
            | (simp only [hl]; exact beq_iff_eq.mpr (hp p hpm w hl))
        | _ => first | rfl | simp only [hl]
    | _ => exact ih

/-- The declared width of a name whose only wire is a one-bit or bit-vector
port. -/
theorem declWidth_of_unique {m : Sparkle.IR.AST.Module} {nm : String}
    {ty : Sparkle.IR.Type.HWType}
    (hq : ({ name := nm, ty := ty } : Port) ∈ m.wires)
    (hu : ∀ r ∈ m.wires, r.name = nm → r = ({ name := nm, ty := ty } : Port))
    (hty : ty = .bit ∨ ∃ n, ty = .bitVector n) :
    Sparkle.IR.RegDedup.declWidth m nm = ty.bitWidth := by
  have hf : m.wires.find? (fun p => p.name == nm) = some ({ name := nm, ty := ty } : Port) := by
    cases h : m.wires.find? (fun p => p.name == nm) with
    | none =>
      have h0 := List.find?_eq_none.mp h _ hq
      exact absurd (beq_self_eq_true nm) h0
    | some r =>
      have hr := List.mem_of_find?_eq_some h
      have hn : (fun p : Port => p.name == nm) r = true :=
        List.find?_some (p := fun p : Port => p.name == nm) (l := m.wires) h
      exact congrArg some (hu r hr (beq_iff_eq.mp hn))
  unfold Sparkle.IR.RegDedup.declWidth
  rw [hf]
  rcases hty with h | ⟨n, h⟩
  · subst h
    rfl
  · subst h
    rfl

/-- The zero-width cleanup adds no wire. -/
theorem dropZW_wires_sub (m : Sparkle.IR.AST.Module) :
    ∀ p ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).wires, p ∈ m.wires := by
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
  split
  · intro p hp
    exact hp
  · intro p hp
    have hp' : p ∈ m.wires.filter (fun p => p.ty.bitWidth != 0) := hp
    exact (List.mem_filter.mp hp').1

/-- **An output connection of a call group's instance, with its field.** A
connection whose port name is no argument port of the child, not `clk` and
not `rst`, connects the transition input of an entry `e` of the group, and
the port is the entry's field. -/
theorem callStmtG_outWireF {nIn kI n : Nat} {names : List String} {args : List Nat}
    {outs : List (Nat × String)} {mc : Sparkle.IR.AST.Module} {mn iname : String}
    {conns : List (String × Expr)}
    (h : Tools.ShippingMachineInstG.CallStmtG nIn kI n names args outs mc
      (Stmt.inst mn iname conns))
    {p : Port} (hpin : ∀ q ∈ Tools.ShippingInstStmtG.inPortsOf mc, q.name ≠ p.name)
    (hclk : p.name ≠ "clk") (hrst : p.name ≠ "rst")
    {w : String} (hm : (p.name, Expr.ref w) ∈ conns) :
    ∃ e ∈ outs, names[nIn + e.1]? = some w ∧ e.2 = p.name := by
  obtain ⟨outWs, argWs, iname', hout, -, -, -, -, -, -, -, -, -, -, he⟩ := h
  injection he with h1 h2 h3
  rw [h3] at hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · -- an argument connection: its port is an argument port
      obtain ⟨⟨q, aw⟩, hq, heq⟩ := List.mem_map.mp hm
      have hqn : q.name = p.name := congrArg Prod.fst heq
      exact absurd hqn (hpin q (List.of_mem_zip hq).1)
    · -- the clock and the reset
      by_cases hs : (mc.inputs.any fun p => p.name == "clk" || p.name == "rst") = true
      · rw [if_pos hs] at hm
        rcases List.mem_cons.mp hm with h0 | h0
        · have h' : p.name = "clk" := congrArg Prod.fst h0
          exact absurd h' hclk
        · rcases List.mem_cons.mp h0 with h0 | h0
          · have h' : p.name = "rst" := congrArg Prod.fst h0
            exact absurd h' hrst
          · cases h0
      · rw [if_neg hs] at hm
        cases hm
  · -- an output connection: position `j` of the group
    obtain ⟨⟨f, w'⟩, hfw, heq⟩ := List.mem_map.mp hm
    have hfp : f = p.name := congrArg Prod.fst heq
    have h2' : Expr.ref w' = Expr.ref w := congrArg Prod.snd heq
    have hw' : w' = w := by
      cases h2'
      rfl
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hfw
    obtain ⟨hj1, hj2⟩ := List.getElem?_zip_eq_some.mp hj
    have hj1' : (outs.map (·.2))[j]? = some f := hj1
    have hj2' : outWs[j]? = some w' := hj2
    rw [List.getElem?_map] at hj1'
    cases he : outs[j]? with
    | none =>
      rw [he] at hj1'
      cases hj1'
    | some e =>
      rw [he] at hj1'
      have hef : e.2 = f := by
        simpa only [Option.map_some, Option.some.injEq] using hj1'
      have hjl : j < outs.length := (List.getElem?_eq_some_iff.mp he).1
      have hej : outs[j] = e := by
        rw [List.getElem?_eq_getElem hjl] at he
        exact Option.some.inj he
      obtain ⟨-, hget⟩ := Tools.ShippingMachineInst.mapM_some _ _ _ hout
      obtain ⟨z, hz, hzj⟩ := hget j hjl
      rw [hej] at hz
      rw [hj2'] at hzj
      have hzw : z = w' := (Option.some.inj hzj).symm
      have hz' : names[nIn + e.1]? = some z := by
        obtain ⟨k, f'⟩ := e
        exact hz
      exact ⟨e, List.mem_of_getElem? he, by rw [hz', hzw, hw'], hef.trans hfp⟩

/-- **The statement-kind gate** of the hierarchical check: an instance
statement, and every statement an instance or an assignment / register. -/
theorem hierGate_of {m : Sparkle.IR.AST.Module}
    (hany : ∃ mn i conns, Stmt.inst mn i conns ∈ m.body)
    (hall : ∀ st ∈ m.body, Sparkle.IR.Machine.isInst st = true ∨
      Sparkle.IR.OptCheck.seqStmtOk st = true) :
    Sparkle.IR.RefineCheck.hierGate m = true := by
  unfold Sparkle.IR.RefineCheck.hierGate
  simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true, Bool.or_eq_true]
  refine ⟨?_, ?_⟩
  · obtain ⟨mn, i, conns, h⟩ := hany
    exact ⟨_, h, rfl⟩
  · intro st hst
    rcases hall st hst with h | h
    · cases st with
      | inst mn i conns => exact Or.inl rfl
      | _ => exact Tools.ShippingChecksDerived.ff_absurd h
    · exact Or.inr h

/-- `hierBinds` is the gate and the self-check of the extracted interface. -/
theorem hierBinds_of {m : Sparkle.IR.AST.Module}
    (hg : Sparkle.IR.RefineCheck.hierGate m = true)
    (hr : Sparkle.IR.RefineCheck.refineCheck
      (Sparkle.IR.HierCheck.openFlat m (Sparkle.IR.HierCheck.openIns m)
        (Sparkle.IR.HierCheck.openOuts m))
      (Sparkle.IR.HierCheck.openFlat m (Sparkle.IR.HierCheck.openIns m)
        (Sparkle.IR.HierCheck.openOuts m)) = true) :
    Sparkle.IR.RefineCheck.hierBinds m = true := by
  unfold Sparkle.IR.RefineCheck.hierBinds
  rw [hg, Bool.true_and]
  exact hr

end Tools.ShippingInstWidthsParts

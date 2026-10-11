import Tools.ShippingCloseChecks

/-! # The instance statement of a one-output call

`instStmt` returns the instance of the child's module — its input ports
connected to the argument wires in order, its one output to the call's wire —
when the child's interface fits the call. Here: that statement, explicitly,
from the fitting facts; and what the order (`combReads` / `combWrites`), the
linked view (`instOuts`) and `kidsCombB`'s fifth condition (every input
connected by a wire) see of it. Pure. -/
namespace Tools.ShippingInstStmt
open Sparkle.IR.AST Sparkle.IR.Machine

/-- The connections of a call's instance. -/
def callConns (ins : List Port) (argWs : List String) (outP : Port) (outW : String) :
    List (String × Expr) :=
  (ins.zip argWs).map (fun (x : Port × String) => (x.1.name, Expr.ref x.2)) ++ [(outP.name, Expr.ref outW)]

/-- **`instStmt` on a fitting child.** -/
theorem instStmt_some {nIn kI n k : Nat} {portNames : List String} {args : List Nat}
    {mc m : Module} {outW : String} {argWs : List String} {outP : Port}
    (hout : portNames[nIn + k]? = some outW)
    (hargs : args.mapM (fun j => portNames[nIn + kI + n + j]?) = some argWs)
    (hclk : ∀ p ∈ mc.inputs, p.name ≠ "clk" ∧ p.name ≠ "rst")
    (hlen : mc.inputs.length = argWs.length)
    (hnd : (mc.inputs.map (·.name)).Nodup)
    (hne : outW ∉ argWs)
    (hop : mc.outputs = [outP])
    (hoin : ∀ p ∈ mc.inputs, p.name ≠ outP.name) (horst : outP.name ≠ "rst")
    (hwire : ∃ p ∈ m.wires, p.name = outW)
    (hfresh : s!"inst{k}_{mc.name}" ∉
      m.inputs.map (·.name) ++ m.outputs.map (·.name) ++ m.wires.map (·.name)) :
    instStmt nIn kI n portNames k args mc m =
      some (.inst mc.name s!"inst{k}_{mc.name}" (callConns mc.inputs argWs outP outW)) := by
  have hfilter : mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst") = mc.inputs := by
    rw [List.filter_eq_self]
    intro p hp
    simp [(hclk p hp).1, (hclk p hp).2]
  have hany : mc.inputs.any (fun p => p.name == "clk" || p.name == "rst") = false := by
    rw [List.any_eq_false]
    intro p hp
    simp [(hclk p hp).1, (hclk p hp).2]
  have hany2 : mc.inputs.any (fun p => p.name == outP.name) = false := by
    rw [List.any_eq_false]
    intro p hp
    simpa using hoin p hp
  have hw : m.wires.any (fun p => p.name == outW) = true := by
    obtain ⟨p, hp, he⟩ := hwire
    exact List.any_eq_true.mpr ⟨p, hp, by simpa using he⟩
  unfold instStmt
  simp only [hout, hargs, Option.bind_eq_bind, Option.bind_some, hfilter, hlen, bne_self_eq_false,
    Bool.false_eq_true, if_false, hany, hnd, decide_true, Bool.not_true, Bool.false_or, hop,
    hany2, Bool.or_false]
  simp [hne, horst, hw, callConns]
  have key : ∀ x : Port, x.name = s!"inst{k}_{mc.name}" →
      (x ∈ m.inputs ∨ x ∈ m.outputs ∨ x ∈ m.wires) → False := by
    intro x hx hm
    apply hfresh
    simp only [List.mem_append, List.mem_map]
    rcases hm with h | h | h
    · exact Or.inl (Or.inl ⟨x, h, hx⟩)
    · exact Or.inl (Or.inr ⟨x, h, hx⟩)
    · exact Or.inr ⟨x, h, hx⟩
  exact ⟨fun x hx h => key x h (Or.inl hx), fun x hx h => key x h (Or.inr (Or.inl hx)),
    fun x hx h => key x h (Or.inr (Or.inr hx))⟩

/-! ## What is seen of the instance -/

theorem lookup_zip_ins : ∀ (ins : List Port) (argWs : List String) (rest : List (String × Expr))
    (p : Port), ins.length = argWs.length → p ∈ ins →
    ∃ w, (((ins.zip argWs).map (fun (x : Port × String) => (x.1.name, Expr.ref x.2))) ++ rest).lookup p.name =
      some (Expr.ref w)
  | q :: ins, a :: argWs, rest, p, hl, hp => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons_append, List.lookup_cons]
    by_cases he : p.name == q.name
    · simp only [he]
      exact ⟨a, rfl⟩
    · simp only [he]
      rcases List.mem_cons.mp hp with rfl | hp
      · simp at he
      · exact lookup_zip_ins ins argWs rest p (by simpa using hl) hp
  | [], _, _, _, _, hp => by cases hp
  | _ :: _, [], _, _, hl, _ => by simp at hl

/-- `kidsCombB`'s fifth condition: every input port is connected by a wire. -/
theorem conns_inputs {ins : List Port} {argWs : List String} {outP : Port} {outW : String}
    (hl : ins.length = argWs.length) :
    ins.all (fun p => match (callConns ins argWs outP outW).lookup p.name with
      | some (.ref _) => true
      | _ => false) = true := by
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨w, hw⟩ := lookup_zip_ins ins argWs [(outP.name, Expr.ref outW)] p hl hp
  unfold callConns
  rw [hw]

theorem lookup_zip_none : ∀ (ins : List Port) (argWs : List String) (x : String),
    (∀ p ∈ ins, p.name ≠ x) →
    ((ins.zip argWs).map (fun (x : Port × String) => (x.1.name, Expr.ref x.2))).lookup x = none
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | q :: ins, a :: argWs, x, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.lookup_cons]
    have : (x == q.name) = false := by
      simpa using fun e => h q (List.mem_cons_self ..) e.symm
    simp only [this]
    exact lookup_zip_none ins argWs x (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- The linked view: the instance drives the call's wire. -/
theorem conns_instOuts {ins : List Port} {argWs : List String} {outP : Port} {outW : String}
    (hoin : ∀ p ∈ ins, p.name ≠ outP.name) :
    instOuts [outP] (callConns ins argWs outP outW) = [outW] := by
  unfold instOuts callConns
  simp only [List.filterMap_cons, List.filterMap_nil, List.lookup_append,
    lookup_zip_none ins argWs outP.name hoin, Option.none_or, List.lookup_cons, beq_self_eq_true,
    Option.or]

theorem zip_refs : ∀ (ins : List Port) (argWs : List String) (c : String × Expr),
    c ∈ (ins.zip argWs).map (fun (x : Port × String) => (x.1.name, Expr.ref x.2)) → ∃ w ∈ argWs, c.2 = Expr.ref w
  | q :: ins, a :: argWs, c, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, List.mem_cons_self .., rfl⟩
    · obtain ⟨w, hw, he⟩ := zip_refs ins argWs c h
      exact ⟨w, List.mem_cons_of_mem _ hw, he⟩
  | [], _, _, h => by cases h
  | _ :: _, [], _, h => by cases h

/-- Every connection is a wire: an argument wire or the call's wire. -/
theorem conns_refs {ins : List Port} {argWs : List String} {outP : Port} {outW : String} :
    ∀ c ∈ callConns ins argWs outP outW, ∃ w, c.2 = Expr.ref w ∧ (w ∈ argWs ∨ w = outW) := by
  intro c hc
  unfold callConns at hc
  rcases List.mem_append.mp hc with h | h
  · obtain ⟨w, hw, he⟩ := zip_refs ins argWs c h
    exact ⟨w, he, Or.inl hw⟩
  · have : c = (outP.name, Expr.ref outW) := by simpa using h
    exact ⟨outW, by rw [this], Or.inr rfl⟩

theorem combWrites_refs {A : List String} {mn iname : String} {o outW : String}
    (hout : outW ∉ A) :
    ∀ (L : List (String × Expr)), (∀ c ∈ L, ∃ w, w ∈ A ∧ c.2 = Expr.ref w) →
      combWrites A (.inst mn iname (L ++ [(o, Expr.ref outW)])) = [outW]
  | [], _ => by simp [combWrites, hout]
  | c :: L, h => by
    obtain ⟨w, hw, he⟩ := h c (List.mem_cons_self ..)
    have ih := combWrites_refs (mn := mn) (iname := iname) (o := o) hout L
      (fun c hc => h c (List.mem_cons_of_mem _ hc))
    obtain ⟨p, e⟩ := c
    simp only [] at he
    subst he
    simp only [combWrites, List.cons_append, List.filterMap_cons] at ih ⊢
    simpa [hw] using ih

/-- The order's view: with the argument wires assign-driven and the call's
wire not, the instance drives exactly the call's wire and reads argument
wires. -/
theorem conns_comb {A : List String} {mn iname : String} {ins : List Port} {argWs : List String}
    {outP : Port} {outW : String} (hargs : ∀ w ∈ argWs, w ∈ A) (hout : outW ∉ A) :
    combWrites A (.inst mn iname (callConns ins argWs outP outW)) = [outW] ∧
    ∀ x ∈ combReads A (.inst mn iname (callConns ins argWs outP outW)), x ∈ argWs := by
  refine ⟨?_, ?_⟩
  · unfold callConns
    refine combWrites_refs hout _ (fun c hc => ?_)
    obtain ⟨w, hw, he⟩ := zip_refs ins argWs c hc
    exact ⟨w, hargs w hw, he⟩
  · intro x hx
    simp only [combReads, List.mem_flatMap] at hx
    obtain ⟨c, hc, hxc⟩ := hx
    obtain ⟨w, he, hw⟩ := conns_refs c hc
    obtain ⟨p, e⟩ := c
    simp only [] at he
    subst he
    simp only [Sparkle.IR.Reorder.refsOf, List.mem_filter, List.mem_singleton] at hxc
    obtain ⟨rfl, hA⟩ := hxc
    rcases hw with hw | hw
    · exact hw
    · exact absurd (by simpa using hA) (hw ▸ hout)

end Tools.ShippingInstStmt

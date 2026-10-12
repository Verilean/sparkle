import Tools.ShippingChecksExtract

/-! # `outsExtracted` from its four parts, and the pure pieces (G1, conjunct 6)

Nothing here mentions a run.

* `outsExtracted_of_parts`: `outsExtracted C b` from, for every
  instance-driven wire: (a) it is the name of a declared wire of `b`,
  (c) it is not in `drivesOf b.body`, (d) it is not an input name — (b), a
  connected wire, is `bodyInstOuts_connRefs`.
* `mem_drivesOf`: a driven name is written (`writesOf`) or a register's
  output.
* `mem_bodyInstOuts`, `instOutWires_port`, `stmtInstOuts_inst`: an
  instance-driven wire is connected, in an instance statement of the body,
  to an OUTPUT port of the module the instance's name resolves to.
* `callStmtG_name`, `callStmtG_outWire`: in the instance statement of a call
  group (`CallStmtG`), a connection whose port name is no argument port of
  the child, not `clk` and not `rst` is an output connection: its wire is
  the transition input `names[nIn + k]` of an entry `k` of the group.
* `dropZW_inputs`, `dropZW_wires`: the zero-width cleanup keeps the inputs,
  and every wire of non-zero width.
* `getElem?_nodup_inj`, `mapM_some_mem`: lists.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingOutsExtractedParts
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingHierOpen

/-- In a duplicate-free list an element has one position. (As
`Tools.ShippingChildServe.nodup_getElem?_inj`.) -/
theorem getElem?_nodup_inj {α : Type} {l : List α} (h : l.Nodup) {i j : Nat} {a : α}
    (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  have hi' := (List.getElem?_eq_some_iff.mp hi).1
  exact (List.getElem?_inj hi' h).mp (by rw [hi, hj])

/-- An element of a successful `mapM` is the image of an element. -/
theorem mapM_some_mem {α β : Type} (f : α → Option β) (l : List α) (r : List β)
    (h : l.mapM f = some r) {y : β} (hy : y ∈ r) : ∃ x ∈ l, f x = some y := by
  obtain ⟨hlen, hget⟩ := Tools.ShippingMachineInst.mapM_some f l r h
  obtain ⟨i, hi, hiy⟩ := List.getElem_of_mem hy
  have hil : i < l.length := by
    rw [← hlen]
    exact hi
  obtain ⟨z, hz, hrz⟩ := hget i hil
  rw [List.getElem?_eq_getElem hi, hiy] at hrz
  have hzy : z = y := (Option.some.inj hrz).symm
  exact ⟨l[i], List.getElem_mem hil, by rw [hz, hzy]⟩

/-- A driven name is an assignment target (or a combinational read's data)
or a register statement's output. -/
theorem mem_drivesOf {body : List Stmt} {w : String}
    (h : w ∈ Sparkle.IR.HierCheck.drivesOf body) :
    w ∈ Sparkle.IR.Reorder.writesOf body ∨
      ∃ (c : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Expr) (init : Int),
        Stmt.register w c rs inp init ∈ body := by
  unfold Sparkle.IR.HierCheck.drivesOf at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · obtain ⟨st, hst, he⟩ := List.mem_filterMap.mp h
    cases st with
    | register r c rs inp init =>
      have he' : some r = some w := he
      cases he'
      exact Or.inr ⟨c, rs, inp, init, hst⟩
    | _ =>
      have he' : (none : Option String) = some w := he
      cases he'

/-- An instance-driven wire of the body is driven by one of its statements. -/
theorem mem_bodyInstOuts {C : String → Option (Sparkle.IR.AST.Module × WEnv)} :
    ∀ (body : List Stmt) (w : String), w ∈ bodyInstOuts C body →
      ∃ st ∈ body, w ∈ stmtInstOuts C st
  | [], w, h => by
    have h' : w ∈ ([] : List String) := h
    cases h'
  | st :: rest, w, h => by
    have h' : w ∈ stmtInstOuts C st ++ bodyInstOuts C rest := h
    rcases List.mem_append.mp h' with h1 | h1
    · exact ⟨st, List.Mem.head _, h1⟩
    · obtain ⟨st', hst', hw'⟩ := mem_bodyInstOuts (C := C) rest w h1
      exact ⟨st', List.Mem.tail _ hst', hw'⟩

/-- An instance-output wire is the reference of a connection of an OUTPUT
port. (`Tools.ShippingChecksExtract.instOutWires_conn`, keeping the port.) -/
theorem instOutWires_port {outs : List Port} {conns : List (String × Expr)} {w : String}
    (h : w ∈ instOutWires outs conns) : ∃ p ∈ outs, (p.name, Expr.ref w) ∈ conns := by
  unfold Tools.ShippingHierOpen.instOutWires at h
  obtain ⟨p, hpm, hp⟩ := List.mem_filterMap.mp h
  cases hl : conns.lookup p.name with
  | none =>
    rw [hl] at hp
    have hp' : (none : Option String) = some w := hp
    cases hp'
  | some e =>
    rw [hl] at hp
    cases e with
    | ref v =>
      have hv : some v = some w := hp
      cases hv
      obtain ⟨l₁, l₂, e, -⟩ := List.lookup_eq_some_iff.mp hl
      exact ⟨p, hpm, by rw [e]; exact List.mem_append_right _ (List.Mem.head _)⟩
    | _ =>
      have hp' : (none : Option String) = some w := hp
      cases hp'

/-- A wire an instance statement drives is connected to an output port of the
module its name resolves to. -/
theorem stmtInstOuts_inst {ms : List Sparkle.IR.AST.Module} {mn iname : String}
    {conns : List (String × Expr)} {mc : Sparkle.IR.AST.Module} {w : String}
    (hfind : Sparkle.IR.Machine.moduleByName ms mn = some mc)
    (h : w ∈ stmtInstOuts (Tools.ShippingMachineLinked.childMap ms) (Stmt.inst mn iname conns)) :
    ∃ p ∈ mc.outputs, (p.name, Expr.ref w) ∈ conns := by
  have hc : Tools.ShippingMachineLinked.childMap ms mn =
      some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
    congrArg (Option.map fun c => (c, Sparkle.IR.RegDedup.declWidth c)) hfind
  unfold Tools.ShippingHierOpen.stmtInstOuts at h
  simp only [hc] at h
  exact instOutWires_port h

/-- The module name of a call group's instance statement. -/
theorem callStmtG_name {nIn kI n : Nat} {names : List String} {args : List Nat}
    {outs : List (Nat × String)} {mc : Sparkle.IR.AST.Module} {mn iname : String}
    {conns : List (String × Expr)}
    (h : Tools.ShippingMachineInstG.CallStmtG nIn kI n names args outs mc
      (Stmt.inst mn iname conns)) : mn = mc.name := by
  obtain ⟨_, _, _, -, -, -, -, -, -, -, -, -, -, -, he⟩ := h
  injection he with h1 h2 h3
  all_goals exact h1

/-- **An output connection of a call group's instance is a call port.** A
connection whose port name is no argument port of the child, not `clk` and
not `rst`, connects the transition input of an entry of the group. -/
theorem callStmtG_outWire {nIn kI n : Nat} {names : List String} {args : List Nat}
    {outs : List (Nat × String)} {mc : Sparkle.IR.AST.Module} {mn iname : String}
    {conns : List (String × Expr)}
    (h : Tools.ShippingMachineInstG.CallStmtG nIn kI n names args outs mc
      (Stmt.inst mn iname conns))
    {p : Port} (hpin : ∀ q ∈ Tools.ShippingInstStmtG.inPortsOf mc, q.name ≠ p.name)
    (hclk : p.name ≠ "clk") (hrst : p.name ≠ "rst")
    {w : String} (hm : (p.name, Expr.ref w) ∈ conns) :
    ∃ e ∈ outs, names[nIn + e.1]? = some w := by
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
  · -- an output connection
    obtain ⟨⟨f, w'⟩, hfw, heq⟩ := List.mem_map.mp hm
    have h2' : Expr.ref w' = Expr.ref w := congrArg Prod.snd heq
    have hw' : w' = w := by
      cases h2'
      rfl
    have hmemW : w ∈ outWs := by
      rw [← hw']
      exact (List.of_mem_zip hfw).2
    obtain ⟨⟨k, f'⟩, hk, hfk⟩ := mapM_some_mem _ _ _ hout hmemW
    exact ⟨(k, f'), hk, hfk⟩

/-- The zero-width cleanup keeps the inputs. -/
theorem dropZW_inputs (m : Sparkle.IR.AST.Module) :
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).inputs = m.inputs := by
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
  split <;> rfl

/-- The zero-width cleanup keeps every wire of non-zero width. -/
theorem dropZW_wires {m : Sparkle.IR.AST.Module} {p : Port} (hp : p ∈ m.wires)
    (hw : p.ty.bitWidth ≠ 0) : p ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).wires := by
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
  split
  · exact hp
  · exact List.mem_filter.mpr ⟨hp, bne_iff_ne.mpr hw⟩

/-- **`outsExtracted` from its parts**: every instance-driven wire is a
declared wire (a), not driven by the body (c), not an input (d); it is a
connected wire by `bodyInstOuts_connRefs` (b). -/
theorem outsExtracted_of_parts {C : String → Option (Sparkle.IR.AST.Module × WEnv)}
    {b : Sparkle.IR.AST.Module}
    (ha : ∀ w ∈ bodyInstOuts C b.body, ∃ q ∈ b.wires, q.name = w)
    (hc : ∀ w ∈ bodyInstOuts C b.body, w ∉ Sparkle.IR.HierCheck.drivesOf b.body)
    (hd : ∀ w ∈ bodyInstOuts C b.body, w ∉ b.inputs.map (·.name)) :
    Tools.ShippingHierPremisesBase.outsExtracted C b = true := by
  unfold Tools.ShippingHierPremisesBase.outsExtracted
  rw [List.all_eq_true]
  intro w hw
  obtain ⟨q, hq, hqn⟩ := ha w hw
  have hwq : q.name ∈ bodyInstOuts C b.body := by
    rw [hqn]
    exact hw
  have h1 : (Sparkle.IR.HierCheck.connRefs b.body).contains q.name = true := by
    simpa [List.contains_eq_mem] using
      Tools.ShippingChecksExtract.bodyInstOuts_connRefs b.body q.name hwq
  have h2 : (!(Sparkle.IR.HierCheck.drivesOf b.body).contains q.name) = true := by
    simpa [List.contains_eq_mem] using hc q.name hwq
  have h3 : (!(b.inputs.map (·.name)).contains q.name) = true := by
    simpa [List.contains_eq_mem] using hd q.name hwq
  have hopen : q ∈ Sparkle.IR.HierCheck.openIns b := by
    unfold Sparkle.IR.HierCheck.openIns
    refine List.mem_filter.mpr ⟨hq, ?_⟩
    show ((Sparkle.IR.HierCheck.connRefs b.body).contains q.name &&
      !(Sparkle.IR.HierCheck.drivesOf b.body).contains q.name &&
      !(b.inputs.map (·.name)).contains q.name) = true
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨h1, h2⟩, h3⟩
  have hmem : w ∈ (Sparkle.IR.HierCheck.openIns b).map (·.name) :=
    List.mem_map.mpr ⟨q, hopen, hqn⟩
  simpa [List.contains_eq_mem] using hmem

end Tools.ShippingOutsExtractedParts

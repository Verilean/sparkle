import Tools.ShippingCallsKidsD
import Tools.ShippingClosedKinds
import Tools.ShippingMachineDepthChild

/-! # A machine child WITH calls of its own, from its own run

A run of the FULL entry on a machine-route declaration with registers and
calls (closed by either closing: one-output or general) returns a module and a design with what
a parent's closing asks (`ChildIfaceD`), the design described by the printed
names of its children and of their descendants:

* ports: the non-clock inputs are the declaration's hardware arguments
  (`calls_ports` on the raw module's wiring), the outputs the layout's;
* the body is the closed machine's assignments and registers and the
  instance statements (no memory);
* the design is the join of its children's modules and designs: distinct
  names, each a child's or a descendant's printed name; every instance names
  a module of it (the wiring's instance clause);
* the post-passes: the zero-width cleanup keeps the module (the wiring's
  cleanup clause), the checked merge keeps a module with an instance, and
  the design is unchanged when no module of it is named as the declaration.

From ONE run witness; the children by the `RealChild` witnesses the run's
closing returns. Premise about names (N1): the declaration prints differently
from its children and their descendants. Data conditions per declaration:
the endpoint's `ok`, S3, the slots, output types, the argument split `kD`.
Not here: slotless children with calls, memory children. -/
namespace Tools.ShippingKidsChildIface
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds
open Sparkle.IR.RefineCheck (mergeChecked)
open Sparkle.IR.OptCheck (seqStmtOk)

theorem map_other (N : String) (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) :
    ∀ (l : List Sparkle.IR.AST.Module), (∀ x ∈ l, x.name ≠ N) →
      (l.map fun x => if x.name == N then f x else x) = l
  | [], _ => rfl
  | x :: l, h => by
    have hx : (x.name == N) = false := by simpa using h x (List.mem_cons_self ..)
    simp only [List.map_cons, hx, Bool.false_eq_true, if_false]
    exact congrArg _ (map_other N f l (fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-- **The full entry's design is the core run's**, when no module of it is
named as the top module. -/
theorem synthesizeCombinational_designL {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        M' = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      ((∀ x ∈ D.modules, x.name ≠ M.name) → D'.modules = D.modules) := by
  unfold synthesizeCombinational synthesizeCombinationalWith at h
  obtain ⟨⟨M, D⟩, w1, hcore, h⟩ := RunsTo.bind h
  refine ⟨M, D, w1, hcore, ?_⟩
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := RunsTo.bind h
  rcases RunsTo.ite h with h | h
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    subst h1 h2
    exact ⟨Or.inl rfl, fun hx => map_other M.name _ D.modules hx⟩
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    subst h1 h2
    refine ⟨Or.inr rfl, fun hx => ?_⟩
    show (D.modules.map _).map _ = _
    rw [map_other M.name _ D.modules hx, map_other M.name _ D.modules hx]

/-- **What a child with calls asks of ITS children**: the name, and the
design described by printed names (no port fact). -/
structure KidNames (c : Name) (names : List String) (b : Sparkle.IR.AST.Module)
    (design : Design) : Prop where
  name : b.name = c.toString
  desNames : ∀ g ∈ design.modules, g.name ∈ names
  closed : ∀ g ∈ b :: design.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body → mn ∈ names

theorem _root_.Tools.ShippingCallsKidsD.ChildIfaceD.kid {c : Name} {n : Nat}
    {outs names : List String} {b : Sparkle.IR.AST.Module} {design : Design}
    (h : ChildIfaceD c n outs names b design) : KidNames c names b design :=
  ⟨h.name, h.desNames, h.closed⟩

/-- A gate child or a slotless machine child (`ChildIface`): no descendant. -/
theorem kid_of_iface {c : Name} {n : Nat} {b : Sparkle.IR.AST.Module} {design : Design}
    (h : Tools.ShippingCallsGate.ChildIface c n b design) : KidNames c [] b design := by
  obtain ⟨hcomb, -, hname, hdes⟩ := h
  refine ⟨hname, (by rw [hdes]; intro g hg; cases hg), ?_⟩
  rw [hdes]
  intro g hg mn i conns hm
  have hgb : g = b := by simpa using hg
  subst hgb
  have := List.all_eq_true.mp hcomb.assigns _ hm
  simp [Sparkle.IR.RegDedup.isAssign] at this

/-- The printed names of a machine's children and of their descendants. -/
def namesOf (d : MachineData) (namesK : Nat → List String) : List String :=
  d.shape.insts.map (·.1.toString) ++ (List.range d.shape.insts.length).flatMap namesK

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **The interface of a machine child with calls, at its full entry.** -/
theorem kidsChild_iface {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (namesK : Nat → List String)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      KidNames (d.shape.insts[k]).1 (namesK k) y.1 y.2)
    (hself : c.toString ∉ namesOf d namesK)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ChildIfaceD c ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length
      (d.shape.layout.outs.map (·.name)) (namesOf d namesK) b design := by
  obtain ⟨M, D, w1, hcore, hpost, hdesL⟩ := synthesizeCombinational_designL hr
  obtain ⟨bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
    machine_run_of_core hcore entry (ChildBnd.of_invW mctx cctx hw)
  have hne := closes bb _ _ _ hw9 hd9 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
  obtain ⟨-, -, hMname, L, hLinst, hperm, -, -, -, -, -, hDeq, -⟩ := hcc.some
  obtain ⟨hseq0, hname0, hd0⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  -- the raw module's wiring
  have ok' := ok
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok'
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, _, _, _, _, _, _, _, _⟩ := ok'
  have hposv : PositiveBinders d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have layW : Tools.ShippingMachineClose.Zip₂
      (fun (f : SlotField) (b : Name × MixedGateBinder) =>
        f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeMachineCertified_sound hrun9.mreturns d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨hinNd, -, -, houtIn, hargP, -⟩ :=
    Tools.ShippingMachineDepthChild.calls_ports wired hlenIds hsl (fun o ho => (outsOk o ho).2)
      kD hkD hIlen hSL hSlen hLlen hNIn
  obtain ⟨-, -, -, -, hcall1, hinst1, -, houtsM, -, -, -, hGinst, hGcall, -, -, hcleanAny, -⟩ :=
    wired
  obtain ⟨hzb, -, hzi, hzo⟩ := hcleanAny outTy
  -- an instance statement of the module names a module of its design
  have hinstD : ∀ mn i conns, Stmt.inst mn i conns ∈ M.body → ∃ mc ∈ D.modules, mc.name = mn := by
    intro mn i conns hm
    by_cases hf : d.shape.instFields = []
    · obtain ⟨k, args, mc, -, hfind, -⟩ := hinst1 hf mn i conns hm
      unfold moduleByName at hfind
      exact ⟨mc, List.mem_of_find?_eq_some hfind, by simpa using List.find?_some hfind⟩
    · obtain ⟨args, outs, mc, hcs, hfind, -⟩ := hGinst hf _ hm rfl
      obtain ⟨_, _, _, -, -, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      cases he
      exact ⟨mc, List.mem_of_find?_eq_some hfind, rfl⟩
  have hhas : Tools.ShippingMachineShipsHier.hasInst M := by
    have hk0 : 0 < d.shape.insts.length := List.length_pos_iff.mpr hins
    by_cases hf : d.shape.instFields = []
    · obtain ⟨args, mc, st, -, hst, -, hcs⟩ := hcall1 hf 0 hk0
      obtain ⟨_, _, _, iname, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      exact ⟨mc.name, iname, _, he ▸ hst⟩
    · obtain ⟨st, hst, args, outs, mc, hcs, -⟩ := hGcall hf 0 hk0
      obtain ⟨_, _, iname, -, -, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      exact ⟨mc.name, iname, _, he ▸ hst⟩
  have hbeq : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M := by
    rcases hpost with h | h
    · exact h
    · rw [h]
      refine Tools.ShippingMachineDepthRun.mergeChecked_of_hasInst ?_
      obtain ⟨mn, i, conns, hm⟩ := hhas
      exact ⟨mn, i, conns, by rw [hzb]; exact hm⟩
  have hbname : b.name = c.toString := by
    rw [hbeq, Tools.ShippingMachineDepthRun.dropZW_name, hMname, hname0]
  have hbody' : b.body = M.body := by rw [hbeq, hzb]
  -- the children, by their witnesses
  obtain ⟨hlenC, hall⟩ := hreal
  have hfull : ∀ (k : Nat) (y : Res), children[k]? = some y → ∃ hk : k < d.shape.insts.length,
      KidNames (d.shape.insts[k]).1 (namesK k) y.1 y.2 := by
    intro k y hc
    have hk : k < d.shape.insts.length := by
      rw [← hlenC]
      exact (List.getElem?_eq_some_iff.mp hc).1
    obtain ⟨y', hy, hor⟩ := hall k hk
    rw [hc] at hy
    cases hy
    rcases hor with hmem | hre
    · rw [hnomem _ (List.getElem_mem hk)] at hmem
      cases hmem
    · exact ⟨hk, hkid k hk y hre⟩
  have hnameK : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      (d.shape.insts[k]).1.toString ∈ namesOf d namesK ∧
      ∀ x ∈ namesK k, x ∈ namesOf d namesK := by
    intro k hk
    refine ⟨List.mem_append_left _ (List.mem_map.mpr ⟨_, List.getElem_mem hk, rfl⟩), fun x hx => ?_⟩
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, hx⟩)
  -- the design: the join of the children
  rw [hDeq] at hinstD hdesL
  obtain ⟨hdNd, hdVis⟩ := designWith_modules (children := children) hd0
  have hvisN : ∀ g ∈ (designWith children d₀).modules, g.name ∈ namesOf d namesK ∧
      ∀ mn i conns, Stmt.inst mn i conns ∈ g.body → mn ∈ namesOf d namesK := by
    intro g hg
    obtain ⟨y, hy, hor⟩ := mem_visited.mp (hdVis g hg)
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hy
    obtain ⟨hk', full⟩ := hfull k y hk
    obtain ⟨hn1, hn2⟩ := hnameK k hk'
    rcases hor with rfl | hin
    · exact ⟨by rw [full.name]; exact hn1,
        fun mn i conns hm => hn2 _ (full.closed _ (List.mem_cons_self ..) mn i conns hm)⟩
    · exact ⟨hn2 _ (full.desNames g hin),
        fun mn i conns hm => hn2 _ (full.closed g (List.mem_cons_of_mem _ hin) mn i conns hm)⟩
  have hdesEq : design.modules = (designWith children d₀).modules := by
    refine hdesL (fun x hx e => hself ?_)
    rw [← hname0, ← hMname, ← e]
    exact (hvisN x hx).1
  -- the ports
  have hbin : b.inputs = M.inputs := by rw [hbeq, hzi]
  have hbout : b.outputs = M.outputs := by rw [hbeq, hzo]
  have houtNames : b.outputs.map (·.name) = d.shape.layout.outs.map (·.name) := by
    rw [hbout, houtsM, List.map_map]
    rfl
  have hinP : inPortsOf b = machPorts c ids cache (d.bsIn.take kD) := by
    unfold inPortsOf
    rw [hbin]
    exact hargP
  refine ⟨hbname, ?_, ?_, houtNames, ?_, by rw [houtNames]; exact outsNodup, ?_,
    by rw [hdesEq]; exact hdNd, by rw [hdesEq]; exact fun g hg => (hvisN g hg).1, ?_⟩
  · rw [hinP]
    exact Tools.ShippingMachineCompose.machPorts_length _ (by
      have : d.bsIn.length ≤ d.shape.binders.length := by
        simp only [MachineData.bsIn, List.length_take]
        omega
      rw [List.length_take, hlenIds]
      omega)
  · unfold inPortsOf
    rw [hbin]
    exact hinNd.sublist ((List.filter_sublist).map _)
  · intro p hp
    have hpo : p.name ∈ M.outputs.map (·.name) := by
      rw [← hbout]
      exact List.mem_map_of_mem hp
    have hnotIn := houtIn p.name hpo
    have hpn : p.name ∈ d.shape.layout.outs.map (·.name) := by
      rw [← houtNames]
      exact List.mem_map_of_mem hp
    obtain ⟨o, ho, hoe⟩ := List.mem_map.mp hpn
    refine ⟨fun q hq e => hnotIn ?_, ?_⟩
    · unfold inPortsOf at hq
      rw [hbin] at hq
      rw [← e]
      exact List.mem_map_of_mem (List.mem_filter.mp hq).1
    · rw [← hoe]
      exact outName_ne_clk (outsOk o ho).2
  · -- no memory statement in the body
    have hkinds : ∀ st ∈ M.body, seqStmtOk st = true ∨ isInst st = true := by
      intro st hs
      rcases List.mem_append.mp (hperm.symm.subset hs) with h | h
      · exact Or.inl (List.all_eq_true.mp hseq0 st h)
      · exact Or.inr (List.all_eq_true.mp hLinst st h)
    unfold Sparkle.Compiler.MachMemory.memParams?
    split
    · rename_i heq
      rw [hbody'] at heq
      have := hkinds _ (by rw [heq]; exact List.mem_cons_self ..)
      simp [seqStmtOk, isInst] at this
    · rfl
  · intro g hg mn i conns hm
    rcases List.mem_cons.mp hg with rfl | hg
    · rw [hbody'] at hm
      obtain ⟨mc, hmc, rfl⟩ := hinstD mn i conns hm
      exact (hvisN mc hmc).1
    · rw [hdesEq] at hg
      exact (hvisN g hg).2 mn i conns hm

/-- **A real child of a machine declaration with calls has the interface** —
from its OWN run (the `RealChild` witness), its reflection and its closing in
that run's contexts. -/
theorem kidsChild_of_real {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (namesK : Nat → List String)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      KidNames (d.shape.insts[k]).1 (namesK k) y.1 y.2)
    (hself : c.toString ∉ namesOf d namesK)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineDefines mctx' mref cctx' cref c d.shape →
      MachineClosesAt mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChild mref cref c y) :
    ChildIfaceD c ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length
      (d.shape.layout.outs.map (·.name)) (namesOf d namesK) y.1 y.2 := by
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := h.inv
  exact kidsChild_iface d ok hbody hC hslots hdomB hins hsl outTy kD hkD hIlen hSL hSlen
    hLlen hNIn namesK hnomem hkid hself hw hr
    (Tools.ShippingReflectCtx.MachineDefines.ctx entry)
    (closes mctx' cctx' (Tools.ShippingReflectCtx.MachineDefines.ctx entry))

end Tools.ShippingKidsChildIface

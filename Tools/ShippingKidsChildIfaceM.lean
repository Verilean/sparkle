import Tools.ShippingKidsChildIface
import Tools.ShippingMemClosesKids

/-! # A machine child whose calls may be MEMORY reads, from its own run (round par/c-2)

WRITTEN, NOT BUILT.

`kidsChild_iface` / `kidsChild_of_real` (`Tools/ShippingKidsChildIface.lean`)
give a parent's closing the interface `ChildIfaceD` of a child that has calls
of its own — with the premise `hnomem` (no call of the child is a memory
placeholder) and the children described by `KidNames`, whose field `name`
says the child module is named `ModuleName.ofDecl` of the callee. A memory
entry's child is the built module `memModule cb aw dw`, named
`ModuleName.ofMem …` (`Sparkle/Compiler/MachMemory.lean` 47–61): `KidNames`
is FALSE of it. So `memCounterH` (one memory read) has no `iface_deep`, and a
parent of it (`memParent`) no closing.

`hnomem` is used ONCE in `kidsChild_iface`'s proof: to turn a child's witness
(`memChild? c = some y ∨ RealChild …`, `ChildrenReal`) into a `RealChild`.
Here the children are taken as the general closing takes them (`Kid`, by
`kid_of` and the closing's own `MemChildren` — available under
`instFields ≠ []`, the new premise `hfne`), and described by `KidNamesP`:
`KidNames` with the child module's NAME a parameter (`nameK k`), as
`ChildIfaceP` does for the closing. The conclusion is the SAME `ChildIfaceD`
(its fields are about the child's own module and design; `noMem` holds: the
memory is an instance of a submodule, not a statement of the body), over the
names `namesOfP d nameK namesK`.

* `KidNamesP`, `namesOfP`; `KidNames.toP` (a real child), `memKidNamesP`
  (a memory placeholder's kid).
* `kidsChild_ifaceM`, `kidsChild_of_realM`: the proofs of `kidsChild_iface` /
  `kidsChild_of_real` (copied from the built file, lines 127–352 and
  354–390), changed in three places: `hMC` taken from the closing, the
  children's facts by `kid_of`, the membership of `nameK k` in the names. -/
namespace Tools.ShippingKidsChildIfaceM
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
open Tools.ShippingKidsChildIface

/-- **What a child with calls asks of its children, the child module's name a
parameter** (`KidNames` for a real child, at `ModuleName.ofDecl c`). -/
structure KidNamesP (nm : String) (names : List String) (b : Sparkle.IR.AST.Module)
    (design : Design) : Prop where
  name : b.name = nm
  desNames : ∀ g ∈ design.modules, g.name ∈ names
  closed : ∀ g ∈ b :: design.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body → mn ∈ names

theorem _root_.Tools.ShippingKidsChildIface.KidNames.toP {c : Name} {names : List String}
    {b : Sparkle.IR.AST.Module} {design : Design} (h : KidNames c names b design) :
    KidNamesP (Sparkle.IR.ModuleName.ofDecl c) names b design :=
  ⟨h.name, h.desNames, h.closed⟩

/-- The names of a machine's children (`nameK`) and of their descendants. -/
def namesOfP (d : MachineData) (nameK : Nat → String) (namesK : Nat → List String) : List String :=
  (List.range d.shape.insts.length).map nameK ++ (List.range d.shape.insts.length).flatMap namesK

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A memory placeholder's kid**: the built memory module, its design the
module itself, no instance. -/
theorem memKidNamesP {c : Name} {cb : Bool} {aw dw : Nat}
    (hc : Sparkle.Compiler.MachMemory.memChild? c =
      some (Sparkle.Compiler.MachMemory.memModule cb aw dw))
    {y : Res} (hy : Tools.ShippingMemKid.Kid mref cref c y) :
    KidNamesP (Sparkle.Compiler.MachMemory.memModule cb aw dw).1.name
      [(Sparkle.Compiler.MachMemory.memModule cb aw dw).1.name] y.1 y.2 := by
  have e := hy.mem hc
  subst e
  exact ⟨rfl, (Tools.ShippingMemCloses.memIface cb aw dw).desNames,
    (Tools.ShippingMemCloses.memIface cb aw dw).closed⟩

set_option maxHeartbeats 4000000 in
/-- **The interface of a machine child whose calls may be memory reads, at its
full entry** (`kidsChild_iface` over `Kid`, the children named by `nameK`). -/
theorem kidsChild_ifaceM {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hfne : d.shape.instFields ≠ [])
    (nameK : Nat → String) (namesK : Nat → List String)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingMemKid.Kid mref cref (d.shape.insts[k]).1 y →
      KidNamesP (nameK k) (namesK k) y.1 y.2)
    (hself : (Sparkle.IR.ModuleName.ofDecl c) ∉ namesOfP d nameK namesK)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ChildIfaceD c ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length
      (d.shape.layout.outs.map (·.name)) (namesOfP d nameK namesK) b design := by
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
  -- the general closing's own statement about its memory entries
  have hMC : MemChildren d.shape children := by
    rcases hcc with ⟨hf0, -⟩ | ⟨-, -, h⟩
    · exact absurd hf0 hfne
    · exact h
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
  have hinstD : ∀ mn i conns, Stmt.inst mn i conns ∈ M.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧ mc ∈ D.modules ∧ mc.name = mn := by
    intro mn i conns hm
    by_cases hf : d.shape.instFields = []
    · obtain ⟨k, args, mc, -, hfind, -⟩ := hinst1 hf mn i conns hm
      have hfind' := hfind
      unfold moduleByName at hfind'
      exact ⟨mc, hfind, List.mem_of_find?_eq_some hfind', by simpa using List.find?_some hfind'⟩
    · obtain ⟨args, outs, mc, hcs, hfind, -⟩ := hGinst hf _ hm rfl
      obtain ⟨_, _, _, -, -, -, -, -, -, -, -, -, -, -, he⟩ := hcs
      cases he
      exact ⟨mc, hfind, List.mem_of_find?_eq_some hfind, rfl⟩
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
  have hbname : b.name = (Sparkle.IR.ModuleName.ofDecl c) := by
    rw [hbeq, Tools.ShippingMachineDepthRun.dropZW_name, hMname, hname0]
  have hbody' : b.body = M.body := by rw [hbeq, hzb]
  -- the children, by their witnesses
  obtain ⟨hlenC, hall⟩ := hreal
  have hfull : ∀ (k : Nat) (y : Res), children[k]? = some y → ∃ hk : k < d.shape.insts.length,
      KidNamesP (nameK k) (namesK k) y.1 y.2 := by
    intro k y hc
    have hk : k < d.shape.insts.length := by
      rw [← hlenC]
      exact (List.getElem?_eq_some_iff.mp hc).1
    obtain ⟨y', hy, hor⟩ := hall k hk
    rw [hc] at hy
    cases hy
    exact ⟨hk, hkid k hk y (Tools.ShippingMemKid.kid_of hk hMC hc hor)⟩
  have hnameK : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nameK k ∈ namesOfP d nameK namesK ∧
      ∀ x ∈ namesK k, x ∈ namesOfP d nameK namesK := by
    intro k hk
    refine ⟨List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩), fun x hx => ?_⟩
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, hx⟩)
  -- the design: the join of the children
  rw [hDeq] at hinstD hdesL
  obtain ⟨hdNd, hdVis⟩ := designWith_modules (children := children) hd0
  have hvisN : ∀ g ∈ (designWith children d₀).modules, g.name ∈ namesOfP d nameK namesK ∧
      ∀ mn i conns, Stmt.inst mn i conns ∈ g.body → mn ∈ namesOfP d nameK namesK := by
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
    by rw [hdesEq]; exact hdNd, by rw [hdesEq]; exact fun g hg => (hvisN g hg).1, ?_, ?_⟩
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
      obtain ⟨mc, -, hmc, rfl⟩ := hinstD mn i conns hm
      exact (hvisN mc hmc).1
    · rw [hdesEq] at hg
      exact (hvisN g hg).2 mn i conns hm
  · intro mn i conns hm
    rw [hbody'] at hm
    obtain ⟨mc, hfind, -, -⟩ := hinstD mn i conns hm
    exact ⟨mc, by rw [hdesEq]; exact hfind⟩

/-- **A real child of a machine declaration whose calls may be memory reads
has the interface** (`kidsChild_of_real` over `Kid`) —
from its OWN run (the `RealChild` witness), its reflection and its closing in
that run's contexts. -/
theorem kidsChild_of_realM {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hfne : d.shape.instFields ≠ [])
    (nameK : Nat → String) (namesK : Nat → List String)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingMemKid.Kid mref cref (d.shape.insts[k]).1 y →
      KidNamesP (nameK k) (namesK k) y.1 y.2)
    (hself : (Sparkle.IR.ModuleName.ofDecl c) ∉ namesOfP d nameK namesK)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineDefines mctx' mref cctx' cref c d.shape →
      MachineClosesAt mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChild mref cref c y) :
    ChildIfaceD c ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length
      (d.shape.layout.outs.map (·.name)) (namesOfP d nameK namesK) y.1 y.2 := by
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := h.inv
  exact kidsChild_ifaceM d ok hbody hC hslots hdomB hins hsl outTy kD hkD hIlen hSL hSlen
    hLlen hNIn hfne nameK namesK hkid hself hw hr
    (Tools.ShippingReflectCtx.MachineDefines.ctx entry)
    (closes mctx' cctx' (Tools.ShippingReflectCtx.MachineDefines.ctx entry))

end Tools.ShippingKidsChildIfaceM

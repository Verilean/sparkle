import Tools.ShippingChecksRun2
import Tools.ShippingChecksDepth

/-! # `outsCheck` of a machine with calls, at the CORE run's design, every depth (G1)

The shipping heads (`machine_ships_hierC`, `ships_design_svN_all`) state
their checks on `childMap D.modules` where `(raw, D)` is the result of the
CORE run inside the full entry (`synthesizeCombinational_checked`), NOT the
design the full entry returns. This file states the derived checks on that
`D`, literally in the heads' shape:

* `core_kids_facts`: for a core run on a machine with calls and a register,
  at the machine boundary, with `b` the cleaned module or its checked merge —
  the module's name; `b`'s body and output ports are the core module's;
  every instance statement of the core module resolves in `D`; every module
  of `D` is a real child's module or a module of its design, and `D` has a
  module of the name of every module of that child's design and of the
  child; `b` assigns every output.
* `core_outsCheck_all`: `outsCheck (childMap D.modules) n (checkedOptimize b)
  = true` for EVERY depth `n`, at a run starting in a world of the child
  boundary (`ChildBnd`: what the generated endpoints assume — NOT the
  stronger `InvW`, which an outermost run's start world need not satisfy;
  round 13), under the gate `hierBinds b` and two facts
  per real child: its modules assign their outputs (`hkidA`) and its
  instance statements name modules of its own design (`hkidR`).
* `kids_run_kid` / `kids_real_kid`: `hkidA` and `hkidR` for a child WITH
  calls, from its own run / `RealChild` witness and the same two facts of
  ITS children — the step that iterates (grandparent → parent → leaf).
* `leaf_real_kidR`: `hkidR` for a child without calls (no instance).

What is NOT proved here
* The heads do not expose that their `(raw, D)` is a core run's result (the
  witnesses are existential); to USE `core_outsCheck_all` in a head, the
  head must be proved with it inside (after its own
  `synthesizeCombinational_checked hr`) or return the core run. Stated in
  docs/parallel/G1-checks.md §9.
* The gate `hierBinds b`; slotless and memory children; `designCheck`. -/
namespace Tools.ShippingChecksCore
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

/-- The output ports of the closed machine are the layout's. -/
theorem closeMachine_outputs {lay : Layout} {t : Sparkle.IR.AST.Module} {w : String}
    (h : packedWire? t.body = some w) :
    (closeMachine lay t).outputs =
      lay.outs.map (fun o => ({ name := o.name, ty := o.ty } : Port)) := by
  unfold closeMachine
  split
  · rename_i heq
    rw [h] at heq
    cases heq
  · rfl

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **A core run on a machine with calls: the module, its instances in the
design, and the design's modules.** -/
theorem core_kids_facts {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    M.name = c.toString ∧ b.body = M.body ∧ b.outputs = M.outputs ∧
    (∀ mn i conns, Stmt.inst mn i conns ∈ M.body → ∃ mc, moduleByName D.modules mn = some mc) ∧
    (∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
      ∀ g2 ∈ y.1 :: y.2.modules, ∃ g' ∈ D.modules, g'.name = g2.name) ∧
    Tools.ShippingDesignSVBack.outsAssigned b = true := by
  obtain ⟨bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
    machine_run_of_core hcore entry hB
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
  have hbody' : b.body = M.body := by rw [hbeq, hzb]
  have hbout : b.outputs = M.outputs := by rw [hbeq, hzo]
  -- the children, by their witnesses
  obtain ⟨hlenC, hall⟩ := hreal
  -- the design: the join of the children
  obtain ⟨hdNd, hdVis⟩ := designWith_modules (children := children) hd0
  have hnames := Tools.ShippingChecksDepth.visited_name (children := children) hd0
  -- the closed machine assigns its outputs, and so does the module
  obtain ⟨ids', cache', returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  obtain ⟨wP, hpw⟩ := Tools.ShippingChecksPacked.transition_packed nd len hrun hm d.packed hwf
    hb' hv' hbody
  obtain ⟨wP', hpw'⟩ := Option.isSome_iff_exists.mp
    (Tools.ShippingChecksPacked.closeLets_packed hcl hpw)
  have hMA : Tools.ShippingDesignSVBack.outsAssigned M = true := by
    refine Tools.ShippingChecksDerived2.outsAssigned_of_assigned fun p hp => ?_
    have hp2 : p ∈ (closeMachine d.shape.layout t').outputs := by
      rw [closeMachine_outputs hpw']
      rw [houtsM] at hp
      exact hp
    obtain ⟨r, hr⟩ := Tools.ShippingChecksDerived3.closeMachine_outs_assigned hpw' p hp2
    exact ⟨r, hperm.subset (List.mem_append_left _ hr)⟩
  refine ⟨hMname.trans hname0, hbody', hbout,
    fun mn i conns hm => (hinstD mn i conns hm).imp fun _ h => h.1, ?_,
    Tools.ShippingChecksDerived3.outsAssigned_congr hbody' hbout hMA⟩
  intro g hg
  rw [hDeq] at hg
  obtain ⟨y, hy, hor⟩ := mem_visited.mp (hdVis g hg)
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hy
  have hk' : k < d.shape.insts.length := by
    rw [← hlenC]
    exact (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨y', hy', hor'⟩ := hall k hk'
  rw [hk] at hy'
  cases hy'
  rcases hor' with hmem | hre
  · rw [hnomem _ (List.getElem_mem hk')] at hmem
    cases hmem
  · refine ⟨k, hk', y, hre, hor, fun g2 hg2 => ?_⟩
    rw [hDeq]
    refine hnames g2 (mem_visited.mpr ⟨y, hy, ?_⟩)
    rcases List.mem_cons.mp hg2 with h | h
    · exact Or.inl h
    · exact Or.inr h

set_option maxHeartbeats 4000000 in
/-- **`outsCheck` of the printed module of a machine with calls, on the core
run's design, at every depth** — the heads' literal form. `hkidA`: each real
child's module and the modules of its design assign their outputs; `hkidR`:
every instance statement of those modules names a module of the child's
design. -/
theorem core_outsCheck_all {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkidA : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
        ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true)
    (hkidR : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
        ∃ g2 ∈ y.2.modules, g2.name = mn)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hb : hierBinds b = true) (n : Nat) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true := by
  obtain ⟨-, hbody', -, hresM, hrealD, -⟩ :=
    core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB hcore hpost entry closes
  refine Tools.ShippingChecksDepth.outsCheck_opt_all hb ?_ ?_ ?_ n
  · intro mn iname conns hm
    rw [hbody'] at hm
    exact hresM mn iname conns hm
  · intro g hg
    obtain ⟨k, hk, y, hre, hor, -⟩ := hrealD g hg
    rcases hor with heq | hin
    · rw [heq]
      exact (hkidA k hk y hre).1
    · exact (hkidA k hk y hre).2 g hin
  · intro g hg mn iname conns hm
    obtain ⟨k, hk, y, hre, hor, hnm⟩ := hrealD g hg
    have hg' : g ∈ y.1 :: y.2.modules := by
      rcases hor with heq | hin
      · rw [heq]
        exact List.Mem.head _
      · exact List.Mem.tail _ hin
    obtain ⟨g2, hg2, hn2⟩ := hkidR k hk y hre g hg' mn iname conns hm
    obtain ⟨g', hg'D, hn'⟩ := hnm g2 (List.Mem.tail _ hg2)
    exact Tools.ShippingChecksDepth.resolves_by_name ⟨g', hg'D, hn'.trans hn2⟩

set_option maxHeartbeats 4000000 in
/-- **`hkidA` and `hkidR` of a machine with calls, at its full entry**, from
the same two facts of ITS children: its module and every module of its
design assign their outputs; every instance statement of those modules names
a module of its design. -/
theorem kids_run_kid {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (namesK : Nat → List String)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      KidNames (d.shape.insts[k]).1 (namesK k) y.1 y.2)
    (hkidA : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
        ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true)
    (hkidR : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
        ∃ g2 ∈ y.2.modules, g2.name = mn)
    (hself : c.toString ∉ namesOf d namesK)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    (Tools.ShippingDesignSVBack.outsAssigned b = true ∧
      ∀ g ∈ design.modules, Tools.ShippingDesignSVBack.outsAssigned g = true) ∧
    (∀ g ∈ b :: design.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ design.modules, g2.name = mn) := by
  obtain ⟨M, D, w1, hcore, hpost, hdesL⟩ := synthesizeCombinational_designL hr
  obtain ⟨hMn, hbody', -, hresM, hrealD, hbA⟩ :=
    core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem (ChildBnd.of_invW mctx cctx hw) hcore hpost entry closes
  -- the full entry's design is the core run's: no module of it has the top's name
  have hdes : design.modules = D.modules := by
    refine hdesL (fun x hx e => hself ?_)
    obtain ⟨k, hk, y, hre, hor, -⟩ := hrealD x hx
    have full := hkid k hk y hre
    have hxn : x.name ∈ namesOf d namesK := by
      rcases hor with heq | hin
      · rw [heq, full.name]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨_, List.getElem_mem hk, rfl⟩)
      · exact List.mem_append_right _
          (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, full.desNames x hin⟩)
    rw [← hMn, ← e]
    exact hxn
  refine ⟨⟨hbA, fun g hg => ?_⟩, fun g hg mn i conns hm => ?_⟩
  · rw [hdes] at hg
    obtain ⟨k, hk, y, hre, hor, -⟩ := hrealD g hg
    rcases hor with heq | hin
    · rw [heq]
      exact (hkidA k hk y hre).1
    · exact (hkidA k hk y hre).2 g hin
  · rcases List.mem_cons.mp hg with heq | hgD
    · rw [heq, hbody'] at hm
      obtain ⟨mc, hmc⟩ := hresM mn i conns hm
      obtain ⟨hmem, hname⟩ := Tools.ShippingHierPremisesBase.moduleByName_mem hmc
      exact ⟨mc, by rw [hdes]; exact hmem, hname⟩
    · rw [hdes] at hgD
      obtain ⟨k, hk, y, hre, hor, hnm⟩ := hrealD g hgD
      have hg' : g ∈ y.1 :: y.2.modules := by
        rcases hor with heq | hin
        · rw [heq]
          exact List.Mem.head _
        · exact List.Mem.tail _ hin
      obtain ⟨g2, hg2, hn2⟩ := hkidR k hk y hre g hg' mn i conns hm
      obtain ⟨g', hg'D, hn'⟩ := hnm g2 (List.Mem.tail _ hg2)
      exact ⟨g', by rw [hdes]; exact hg'D, hn'.trans hn2⟩

/-- **`hkidA` and `hkidR` of a real child WITH calls**, from its `RealChild`
witness and the same facts of its own children. -/
theorem kids_real_kid {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (namesK : Nat → List String)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      KidNames (d.shape.insts[k]).1 (namesK k) y.1 y.2)
    (hkidA : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
        ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true)
    (hkidR : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
        ∃ g2 ∈ y.2.modules, g2.name = mn)
    (hself : c.toString ∉ namesOf d namesK)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineClosesAt mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChild mref cref c y) :
    (Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true) ∧
    (∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ y.2.modules, g2.name = mn) := by
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := h.inv
  exact kids_run_kid d ok hbody hC hslots hdomB hins outTy namesK hnomem hkid hkidA hkidR hself
    hw hr (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx')

/-- **`hkidR` of a real child without calls**: its module has no instance
statement and its design no module. -/
theorem leaf_real_kidR {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChild mref cref c y) :
    ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ y.2.modules, g2.name = mn := by
  have hI := seqChild_of_real d ok hbody hno outTy entry closes h
  intro g hg mn i conns hm
  rw [hI.design] at hg
  have hgy : g = y.1 := List.mem_singleton.mp hg
  rw [hgy] at hm
  have hs := List.all_eq_true.mp hI.seqOk _ hm
  exact Tools.ShippingChecksDerived.ff_absurd hs

end Tools.ShippingChecksCore

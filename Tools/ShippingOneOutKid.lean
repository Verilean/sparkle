import Tools.ShippingKidFacts
import Tools.ShippingCallsChildPorts
import Tools.ShippingOneOutFacts
import Tools.ShippingLinkedFresh
import Tools.ShippingReflectCtx
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # A callee WITH a register and one-output calls of its own, as a child (G1, unit U2, round par/a-13)

`Tools.ShippingPortsMatchRawLeaf.LeafKid` has the field
`leaf : dk.shape.insts = []`. `OneOutKid` is the interface for a callee `c`
whose data `dk` has calls (`insts ≠ []`), all tied by the ONE-OUTPUT closing
(`instFields = []`), and a register (`slots ≠ []`) — `midH` (child `rcH`),
the stand-in of `wKeccakF` (child `keccakRcHW`). Its fields are the callee's
data conditions (decidable), its reflection and closing in every context,
and the facts of ITS callees (the grandchildren) that the callee's own
check-free one-output chain uses (`#machine_oneout`: `KidNames`, `kidA`,
`kidR`, the leaf form of the children's check, and `portsMatchB` of its raw
module over every core run — `c.machine_portsRawH`). No field mentions
`RealChild mref cref c`.

From it, for every `y` with `RealChild mref cref c y`:

* `OneOutKid.core` — THE BRIDGE: the served module is the post-processing of
  a core run of `c` from a world where the child boundary holds, in some
  contexts, and the served design IS that run's design:

      ∃ mctx' cctx' w w1 M D, ChildBnd mref cref w ∧
        RunsTo (synthesizeCombinationalCore c [] false) mctx' mref cctx' cref w (M, D) w1 ∧
        (y.1 = dropZeroWidthModule M ∨ y.1 = mergeChecked (dropZeroWidthModule M)) ∧
        y.2.modules = D.modules

  (`RealChild.inv`, `synthesizeCombinational_designL`, the name separation
  `self` as in `kids_run_kid`). The reflections are moved to those contexts
  by `MachineDefines.ctx` / `EntryDefines.ctx` (BUILT): the "reflection
  context transfer" is not an open obligation.
* the child-side facts, each the callee's OWN core-run theorem at that run:
  `outsIn` (`kidsChild_of_real`), `outTys`, `masked`, `inW`
  (`core_calls_ports₁`), `kidAR` (`kids_real_kid`), `portsIn`
  (`core_closed_typedIn`), `clk` (`core_clk`), and
* `OneOutKid.check`: `designCheck (childMap ms) 0 y.1 = true` for EVERY
  module list `ms` that resolves the modules of `y.2` to themselves — the
  child's `textCheckI` conjuncts are those of its own run
  (`core_runFactsH`, `core_linkedWF`, `TypedIn`, `portsRaw`), moved from
  the child's map to `childMap ms` by `Tools/ShippingChildMapCongr.lean`
  (the two maps agree on the child's instances); the UNOPTIMISED module is
  checked (the parent's design holds the child as its entry returned it:
  `checkedOptimize` is applied to the top module only), so nothing of
  `c.machine_designFullH` (about `checkedOptimize b`) is used.
* `OneOutKid.facts : KidFacts mref cref c dk.shape.layout.outs (argWidths dk nDecl) 1`.

SCOPE: depth exactly 1 below the parent (`KidFacts … 1`: the grandchildren
are LEAVES for the check, `kidK` in the leaf form — gate children by
`gate_real_kidK`); a callee with a register; the one-output closing in the
callee. NOT a callee under the general closing (`mid → cnt`: unit U3), NOT
a slotless callee, NOT a memory callee.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingOneOutKid
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
open Tools.ShippingChildMapCongr (AgreeOn)
open Tools.ShippingCallsChildPorts (CallsPorts argWidths)

/-- `kidCheck` one level up is `designCheck`. -/
theorem kidCheck_succ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
    (k : Nat) (o : Sparkle.IR.AST.Module) :
    Tools.ShippingChecksDesign.kidCheck C (k + 1) o = Tools.ShippingDesignSV.designCheck C k o :=
  rfl

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 0 of the UNOPTIMISED full-entry module of a
machine with a register and one-output calls, against ANY module list that
resolves the modules of the run's design to themselves.** `hkidK`: the leaf
form of the children's check (the hypothesis of `core_designCheckH`);
`hports`: the connection widths of the raw module in its own design
(`core_portsMatch_raw₁`). -/
theorem core_designCheck_in₁ {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hsl : d.shape.layout.slots ≠ [])
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (hkidK : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
        ∀ g ∈ y.2.modules,
          ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
            Tools.ShippingChecksDesign.kidCheck C n g = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hports : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true)
    (ms : List Sparkle.IR.AST.Module)
    (hms : ∀ g ∈ D.modules, moduleByName ms g.name = some g) :
    Tools.ShippingDesignSV.designCheck (childMap ms) 0 b = true := by
  have hF := Tools.ShippingOneOutFacts.core_runFactsH d ok hbody hC hslots hdomB hins hf outTy
    hnomem hB hcore hpost entry closes hsl
  have hwf := Tools.ShippingLinkedFresh.core_linkedWF d ok hbody hC hslots hdomB hins outTy
    hnomem hB hcore hpost entry closes
  have hT := Tools.ShippingClosedTyped.core_closed_typedIn d ok hbody hC hslots hdomB hins outTy
    hnomem hB hcore hpost entry closes hon hoty
  obtain ⟨-, hbody', -, hresM, hrealD, -⟩ :=
    Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes
  -- an instance of `b` resolves, in both module lists, to the same module
  have hres : ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧ moduleByName ms mn = some mc := by
    intro mn iname conns hm
    rw [hbody'] at hm
    obtain ⟨mc, hmc⟩ := hresM mn iname conns hm
    obtain ⟨hmem, hname⟩ := Tools.ShippingHierPremisesBase.moduleByName_mem hmc
    refine ⟨mc, hmc, ?_⟩
    rw [← hname]
    exact hms mc hmem
  have hag : AgreeOn (childMap ms) (childMap D.modules) b.body := by
    intro mn iname conns hm
    obtain ⟨mc, h1, h2⟩ := hres mn iname conns hm
    simp only [Tools.ShippingMachineLinked.childMap, h1, h2]
  have hCm : ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, mc ∈ D.modules ∧
        childMap ms mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) := by
    intro mn iname conns hm
    obtain ⟨mc, h1, h2⟩ := hres mn iname conns hm
    exact ⟨mc, (Tools.ShippingHierPremisesBase.moduleByName_mem h1).1,
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) h2⟩
  have hlinked : Tools.ShippingHierOpen.linkedWF (childMap ms) b.body = true := by
    rw [Tools.ShippingChildMapCongr.linkedWF_congr b.body hag]
    exact hwf
  have hself : Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) b.body = true := by
    rw [Tools.ShippingChildMapCongr.noSelfRead_congr hag]
    exact hF.self
  have hportsM : Tools.ShippingDesignSV.portsMatchB (childMap ms) b = true := by
    rw [Tools.ShippingChildMapCongr.portsMatchB_congr hag]
    exact hports
  have hkids : Tools.ShippingDesignSV.kidsPass (childMap ms)
      (Tools.ShippingChecksDesign.kidCheck (childMap ms) 0) b.body = true := by
    unfold Tools.ShippingDesignSV.kidsPass
    rw [List.all_eq_true]
    intro st hst
    cases st with
    | inst mn iname conns =>
      obtain ⟨mc, hmem, hc⟩ := hCm mn iname conns hst
      obtain ⟨k, hk, y, hre, hor, -⟩ := hrealD mc hmem
      simp only [hc]
      rcases hor with heq | hin
      · rw [heq]
        exact (hkidK k hk y hre).1 _ 0
      · exact (hkidK k hk y hre).2 mc hin _ 0
    | _ => rfl
  rw [Tools.ShippingChecksDesign.designCheck_eq]
  exact Tools.ShippingChecksDepth.and_true_intro
    (Tools.ShippingChecksDesign.textCheckI_of
      (List.all_eq_true.mpr hT.kinds) hT.seqCheck.1 hT.seqCheck.2 hlinked hF.ndB hself hportsM
      (fun mn iname conns hm => by
        obtain ⟨mc, -, hc⟩ := hCm mn iname conns hm
        simp [hc]))
    hkids

/-- **A callee with a register and one-output calls of its own**: its data
conditions, its reflection and closing in every context, and the facts of
its own callees its check-free one-output chain uses. No field `leaf`. -/
structure OneOutKid (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) (c : Name) (dk : MachineData) (nDecl : Nat)
    (namesK : Nat → List String) : Prop where
  ok : dk.ok = true
  body : dk.shape.body = quote dk.dom
    (fun j => inputExpr dk.shape.binders.length (dk.bpos j))
    (fun j => inputExpr dk.shape.binders.length (dk.vpos j)) dk.packed
  calls : dk.callsOk nDecl = true
  ss : dk.ss.length = dk.shape.layout.slots.length
  dom : ∀ b ∈ dk.shape.binders.drop nDecl, b.2 ≠ .domain
  insts : dk.shape.insts ≠ []
  oneOut : dk.shape.instFields = []
  slots : dk.shape.layout.slots ≠ []
  outTy : ∀ o ∈ dk.shape.layout.outs, o.ty.bitWidth = o.width
  outName : ∀ o ∈ dk.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name
  outScalar : ∀ o ∈ dk.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true
  nomem : ∀ x ∈ dk.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true
  -- the argument split at `nDecl` (the data conditions of `kidsChild_iface`)
  hkD : nDecl ≤ dk.bsIn.length
  hIlen : (dk.bsIn.drop nDecl).length = dk.shape.insts.length
  hSL : ∀ b ∈ dk.slotBs ++ dk.letBs, b.2 ≠ .domain
  hSlen : dk.slotBs.length = dk.shape.layout.slots.length
  hLlen : dk.letBs.length = dk.shape.layout.lets
  hNIn : machNIn dk.shape = ((dk.bsIn.take nDecl).filter (fun b => b.2 != .domain)).length
  -- its own callees (the grandchildren)
  kid : ∀ (k : Nat) (hk : k < dk.shape.insts.length) (y : Res),
    RealChild mref cref (dk.shape.insts[k]).1 y →
    KidNames (dk.shape.insts[k]).1 (namesK k) y.1 y.2
  self : (Sparkle.IR.ModuleName.ofDecl c) ∉ namesOf dk namesK
  kidA : ∀ (k : Nat) (hk : k < dk.shape.insts.length) (y : Res),
    RealChild mref cref (dk.shape.insts[k]).1 y →
    Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true
  kidR : ∀ (k : Nat) (hk : k < dk.shape.insts.length) (y : Res),
    RealChild mref cref (dk.shape.insts[k]).1 y →
    ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ y.2.modules, g2.name = mn
  kidK : ∀ (k : Nat) (hk : k < dk.shape.insts.length) (y : Res),
    RealChild mref cref (dk.shape.insts[k]).1 y →
    (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
        Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n g = true
  -- the connection widths of its raw module in its own design, over every
  -- core run (`c.machine_portsRawH`)
  portsRaw : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (w w1 : Void IO.RealWorld)
    (M b : Sparkle.IR.AST.Module) (D : Design),
    ChildBnd mref cref w →
    RunsTo (synthesizeCombinationalCore c [] false) mctx' mref cctx' cref w (M, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) →
    Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true
  -- its reflection and its closing, in every context
  entry : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
    MachineDefines mctx' mref cctx' cref c dk.shape
  closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
    MachineClosesAt mctx' mref cctx' cref c dk.shape

variable {c : Name} {dk : MachineData} {nDecl : Nat} {namesK : Nat → List String}

set_option maxHeartbeats 4000000 in
/-- **THE BRIDGE: a real child of such a callee is the post-processing of a
core run of the callee, and its design is that run's.** -/
theorem OneOutKid.core (K : OneOutKid mref cref c dk nDecl namesK) {y : Res}
    (hy : RealChild mref cref c y) :
    ∃ (mctx' : Meta.Context) (cctx' : Core.Context) (w w1 : Void IO.RealWorld)
      (M : Sparkle.IR.AST.Module) (D : Design),
      ChildBnd mref cref w ∧
      RunsTo (synthesizeCombinationalCore c [] false) mctx' mref cctx' cref w (M, D) w1 ∧
      (y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        y.1 = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      y.2.modules = D.modules := by
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := hy.inv
  obtain ⟨M, D, w1, hcore, hpost, hdesL⟩ :=
    synthesizeCombinational_designL (M' := y.1) (D' := y.2) hr
  have hB : ChildBnd mref cref w := ChildBnd.of_invW mctx' cctx' hw
  obtain ⟨hMn, -, -, -, hrealD, -⟩ :=
    Tools.ShippingChecksCore.core_kids_facts dk K.ok K.body K.calls K.ss K.dom K.insts K.outTy
      K.nomem hB hcore hpost (K.entry mctx' cctx') (K.closes mctx' cctx')
  refine ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, hdesL (fun x hx e => K.self ?_)⟩
  obtain ⟨k, hk, y', hre, hor, -⟩ := hrealD x hx
  have full := K.kid k hk y' hre
  have hxn : x.name ∈ namesOf dk namesK := by
    rcases hor with heq | hin
    · rw [heq, full.name]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨_, List.getElem_mem hk, rfl⟩)
    · exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, full.desNames x hin⟩)
  rw [← hMn, ← e]
  exact hxn

/-- `hkidP`: no output port of the served module is an argument port, the
clock or the reset (`kidsChild_of_real`). -/
theorem OneOutKid.outsIn (K : OneOutKid mref cref c dk nDecl namesK) {y : Res}
    (hy : RealChild mref cref c y) :
    ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
      p.name ≠ "rst" := by
  obtain ⟨mctx', cctx', _, _, _, _⟩ := hy.inv
  exact (Tools.ShippingKidsChildIface.kidsChild_of_real dk K.ok K.body K.calls K.ss K.dom
    K.insts K.slots K.outTy nDecl K.hkD K.hIlen K.hSL K.hSlen K.hLlen K.hNIn namesK K.nomem
    K.kid K.self (K.entry mctx' cctx') (fun mc cc _ => K.closes mc cc) hy).outsIn

/-- `hkidA` and `hkidR` (`kids_real_kid`). -/
theorem OneOutKid.kidAR (K : OneOutKid mref cref c dk nDecl namesK) {y : Res}
    (hy : RealChild mref cref c y) :
    (Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true) ∧
    (∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ y.2.modules, g2.name = mn) := by
  obtain ⟨mctx', cctx', _, _, _, _⟩ := hy.inv
  exact Tools.ShippingChecksCore.kids_real_kid dk K.ok K.body K.calls K.ss K.dom K.insts
    K.outTy namesK K.nomem K.kid K.kidA K.kidR K.self (K.entry mctx' cctx') K.closes hy

/-- The ports of the served module (`core_calls_ports₁` at the callee's run). -/
theorem OneOutKid.ports (K : OneOutKid mref cref c dk nDecl namesK) {y : Res}
    (hy : RealChild mref cref c y) : CallsPorts c dk nDecl y.1 := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, -⟩ := K.core hy
  exact Tools.ShippingCallsChildPorts.core_calls_ports₁ dk K.ok K.body K.calls K.ss K.dom
    K.insts K.oneOut K.outTy K.nomem K.slots nDecl K.hkD K.hIlen K.hSL K.hSlen K.hLlen K.hNIn
    hB hcore hpost (K.entry mctx' cctx') (K.closes mctx' cctx')

/-- The served module is typed in its own wire table (`core_closed_typedIn`). -/
theorem OneOutKid.typedIn (K : OneOutKid mref cref c dk nDecl namesK) {y : Res}
    (hy : RealChild mref cref c y) : Tools.ShippingTextTyped.TypedIn y.1 := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, -⟩ := K.core hy
  exact Tools.ShippingClosedTyped.core_closed_typedIn dk K.ok K.body K.calls K.ss K.dom K.insts
    K.outTy K.nomem hB hcore hpost (K.entry mctx' cctx') (K.closes mctx' cctx') K.outName
    K.outScalar

/-- `hkidM` (the child's own module): its outputs are masked and no instance
connection names one. -/
theorem OneOutKid.masked (K : OneOutKid mref cref c dk nDecl namesK) {y : Res}
    (hy : RealChild mref cref c y) :
    Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, -⟩ := K.core hy
  exact Tools.ShippingCallsChildPorts.outsMaskedN_of_calls (K.ports hy) (K.typedIn hy)
    (Tools.ShippingCallsChildPorts.core_conn_wires₁ dk K.ok K.body K.calls K.ss K.dom K.insts
      K.oneOut K.outTy K.nomem hB hcore hpost (K.entry mctx' cctx') (K.closes mctx' cctx'))

/-- `hkidClk`: the clock and the reset are one bit in the emitted width map
(`core_clk` at the callee's run: it has a register of its own). -/
theorem OneOutKid.clk (K : OneOutKid mref cref c dk nDecl namesK) {y : Res}
    (hy : RealChild mref cref c y) :
    Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1 := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, -⟩ := K.core hy
  exact Tools.ShippingCoreClk.core_clk dk K.ok K.body K.calls K.ss K.dom K.insts K.outTy K.nomem
    K.slots hB hcore hpost (K.entry mctx' cctx') (K.closes mctx' cctx')

set_option maxHeartbeats 4000000 in
/-- **The children's check of the served module, one level below a parent**:
against every module list that resolves the modules of the served design to
themselves. -/
theorem OneOutKid.check (K : OneOutKid mref cref c dk nDecl namesK) {y : Res}
    (hy : RealChild mref cref c y) (ms : List Sparkle.IR.AST.Module)
    (hms : ∀ g ∈ y.2.modules, moduleByName ms g.name = some g) :
    Tools.ShippingDesignSV.designCheck (childMap ms) 0 y.1 = true ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n g = true := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, hdes⟩ := K.core hy
  have entry := K.entry mctx' cctx'
  have closes : MachineClosesAt mctx' mref cctx' cref c dk.shape := K.closes mctx' cctx'
  refine ⟨?_, ?_⟩
  · exact core_designCheck_in₁ dk K.ok K.body K.calls K.ss K.dom K.insts K.oneOut K.outTy
      K.nomem K.slots K.outName K.outScalar K.kidK hB hcore hpost entry closes
      (K.portsRaw mctx' cctx' w w1 M y.1 D hB hcore hpost) ms
      (fun g hg => hms g (by rw [hdes]; exact hg))
  · -- a module of the served design is a real grandchild's, or of its design
    intro g hg
    rw [hdes] at hg
    obtain ⟨-, -, -, -, hrealD, -⟩ :=
      Tools.ShippingChecksCore.core_kids_facts dk K.ok K.body K.calls K.ss K.dom K.insts K.outTy
        K.nomem hB hcore hpost entry closes
    obtain ⟨k, hk, y', hre, hor, -⟩ := hrealD g hg
    rcases hor with heq | hin
    · rw [heq]
      exact (K.kidK k hk y' hre).1
    · exact (K.kidK k hk y' hre).2 g hin

/-- **`KidFacts` of a callee with a register and one-output calls of its
own, one level below the parent.** -/
theorem OneOutKid.facts (K : OneOutKid mref cref c dk nDecl namesK) :
    Tools.ShippingKidFacts.KidFacts mref cref c dk.shape.layout.outs (argWidths dk nDecl) 1 :=
  { outsIn := fun _ hy => K.outsIn hy
    outTys := fun _ hy => ⟨(K.ports hy).outs⟩
    kidA := fun _ hy => (K.kidAR hy).1
    kidR := fun _ hy => (K.kidAR hy).2
    masked := fun _ hy => K.masked hy
    portsIn := fun _ hy => Tools.ShippingLeafTyped.PortsIn.of_typedIn (K.typedIn hy)
    inW := fun _ hy _ _ hq => (K.ports hy).inWidths (K.typedIn hy).wn hq
    clk := fun _ hy _ => K.clk hy
    check := fun y hy ms _ h2 => by
      obtain ⟨h0, hg⟩ := K.check hy ms h2
      exact ⟨(kidCheck_succ (childMap ms) 0 y.1).trans h0, fun g hgm => hg g hgm _ 1⟩ }

end Tools.ShippingOneOutKid

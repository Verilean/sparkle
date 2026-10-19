import Tools.ShippingKidFacts
import Tools.ShippingCallsPortsG
import Tools.ShippingLinkedFresh
import Tools.ShippingReflectCtx
import Tools.ShippingChildMapCongr
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # A callee WITH a register whose own calls are tied by the GENERAL closing, as a child (G1, unit U3, round par/a-15)

`Tools.ShippingOneOutKid.OneOutKid` is the interface for a callee whose own
calls are tied by the ONE-OUTPUT closing (`instFields = []`: `midH → rcH`)
and gives `KidFacts … 1`. `GenKid` is the interface for a callee `c` whose
own calls are tied by the GENERAL closing (`instFields ≠ []`: `mid → cnt`,
`mid2 → midH`) — the callee the generator `#machine_no_ports_kids` refuses
("KidFacts of such a child is not derived (unit U3)").

Its fields: the callee's data conditions (decidable), its reflection and
closing in every context, `KidNames` of ITS callees (the grandchildren; for
the bridge and `kidsChild_of_real`, as in `OneOutKid`), and — instead of the
grandchildren's leaf-form facts and `portsRaw` — `KidFacts` of every one of
its call entries' callees, i.e. the SAME interface one level down, at TWO
depths:

    kidsLo : ∀ k hk, KidFacts mref cref (dk.shape.insts[k]).1 (kidOuts k) (kidIns k) n
    kidsHi : ∀ k hk, KidFacts mref cref (dk.shape.insts[k]).1 (kidOuts k) (kidIns k) (n + 1)

with the callee's two width conditions against those tables (`callW`,
`callA`). No field mentions `RealChild mref cref c`.

From it, for every `y` with `RealChild mref cref c y`:

* `GenKid.core` — THE BRIDGE (`OneOutKid.core`'s statement and proof; it does
  not read the closing): the served module is the post-processing of a core
  run of `c` from a world where the child boundary holds, in some contexts,
  and the served design is that run's.
* the child-side facts, each the `kids_*` / `core_*` theorem of the
  callee's OWN core run at that run (the no-ports chain's lemmas, used as a
  child's facts): `outsIn` (`kidsChild_of_real`), `kidAR` (`kids_real_kid`),
  `ports` (`core_calls_portsG`), `typedIn` (`core_closed_typedIn`), `masked`
  (`outsMaskedN_of_callsG`), `clk` (`core_clk`), and
* `GenKid.check`: against every module list `ms` that resolves the modules
  of the served design to themselves,

      designCheck (childMap ms) n y.1 = true ∧
        ∀ g ∈ y.2.modules, kidCheck (childMap ms) (n + 1) g = true

  The first conjunct is `kids_designCheck_in` (below) with `kidsLo`; the
  second is `kidsHi`'s `check` at the grandchild that
  `Tools.ShippingKidsSelf.core_kids_self` finds for `g`.
* `GenKid.facts : KidFacts mref cref c dk.shape.layout.outs (argWidths dk nDecl) (n + 1)`.

WHY TWO DEPTHS. `KidFacts.check` at depth `m` asks `kidCheck C m` of the
child's module AND of every module of its design (the form
`core_kidsPass_deep` consumes: an instance of the parent resolves to SOME
module of the design). For the callee `c` at depth `n + 1`: its own module
needs `designCheck C n`, whose instances' children are checked at
`kidCheck C n` (`kidsLo`); the modules of its design are the grandchildren's
modules and are asked at `kidCheck C (n + 1)` (`kidsHi`). A leaf register
machine has `KidFacts` at every depth (`leafKid_facts`), so both are
available for `mid → cnt`. For `mid2 → midH` the built
`OneOutKid.facts` gives depth 1 only; `kidsHi` at `n + 1 = 2` is
`Tools.ShippingOneOutKidDepth.factsN` (this round, not built).

`kids_designCheck_in`: `designCheck (childMap ms) n b = true` of the
UNOPTIMISED full-entry module `b` of a machine tied by the general closing,
against ANY module list `ms` that resolves the modules of the run's design
to themselves — the general-closing, depth-`n` form of
`Tools.ShippingOneOutKid.core_designCheck_in₁` (the parent's design holds
the child as its entry returned it; `checkedOptimize` is applied to the top
module only, so `kids_designCheck` — about `checkedOptimize b` and
`childMap D.modules` — is not what a parent asks of a child).

SCOPE: a callee WITH a register (`slots`), with calls, the general closing
in the callee, no memory callee of the callee. Not a slotless callee.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingGenKid
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
open Tools.ShippingKidFacts (KidFacts)

/-- `kidCheck` one level up is `designCheck`. -/
theorem kidCheck_succ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
    (k : Nat) (o : Sparkle.IR.AST.Module) :
    Tools.ShippingChecksDesign.kidCheck C (k + 1) o = Tools.ShippingDesignSV.designCheck C k o :=
  rfl

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth `n` of the UNOPTIMISED full-entry module of a
machine with a register tied by the general closing, against ANY module list
that resolves the modules of the run's design to themselves**, from
`KidFacts` at depth `n` of every call entry's callee and the two width
conditions. No check premise. -/
theorem kids_designCheck_in {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (ms : List Sparkle.IR.AST.Module)
    (hms : ∀ g ∈ D.modules, moduleByName ms g.name = some g) :
    Tools.ShippingDesignSV.designCheck (childMap ms) n b = true := by
  have hkidW := Tools.ShippingCallWidths.hkidW_of_data hcw
    (fun k hk y hy => (hkid k hk).outTys y hy)
  have hF : Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
    Tools.ShippingKidFacts.kids_runFacts d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem
      kidOuts kidIns n hkid hcw hB hcore hpost entry closes
  have hwf := Tools.ShippingLinkedFresh.core_linkedWF d ok hbody hC hslots hdomB hins outTy
    hnomem hB hcore hpost entry closes
  have hT := Tools.ShippingClosedTyped.core_closed_typedIn d ok hbody hC hslots hdomB hins outTy
    hnomem hB hcore hpost entry closes hon hoty
  -- the connection widths of the raw module in its own design
  have hports : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true :=
    Tools.ShippingPortsMatchRaw.core_portsMatch_raw d ok hbody hC hslots hdomB hins hfne outTy
      hnomem hkidW
      (fun k hk y hy => (hkid k hk).portsIn y hy)
      (kidIns := kidIns) hargs
      (fun k hk y hy j q hq => (hkid k hk).inW y hy j q hq)
      (fun k hk y hy hs => (hkid k hk).clk y hy hs)
      hB hcore hpost entry closes hon hoty
      (Tools.ShippingCoreClk.core_clk d ok hbody hC hslots hdomB hins outTy hnomem hsl hB hcore
        hpost entry closes)
  obtain ⟨-, hbody', -, hresM, -, -⟩ :=
    Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes
  have hselfD := Tools.ShippingKidsSelf.core_kids_self d ok hbody hC hslots hdomB hins hnomem
    hB hcore entry closes
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
  -- the children's check: each instance's module is a real child's module or
  -- a module of a real child's design, and `ms` resolves that child's module
  -- and the modules of its design to themselves
  have hkids : Tools.ShippingDesignSV.kidsPass (childMap ms)
      (Tools.ShippingChecksDesign.kidCheck (childMap ms) n) b.body = true := by
    unfold Tools.ShippingDesignSV.kidsPass
    rw [List.all_eq_true]
    intro st hst
    cases st with
    | inst mn iname conns =>
      obtain ⟨mc, hmem, hc⟩ := hCm mn iname conns hst
      obtain ⟨k, hk, y, hre, hor, hs1, hs2⟩ := hselfD mc hmem
      have hy1 : moduleByName ms y.1.name = some y.1 :=
        hms y.1 (Tools.ShippingHierPremisesBase.moduleByName_mem hs1).1
      have hy2 : ∀ g ∈ y.2.modules, moduleByName ms g.name = some g := fun g hg =>
        hms g (Tools.ShippingHierPremisesBase.moduleByName_mem (hs2 g hg)).1
      have hchk := (hkid k hk).check y hre ms hy1 hy2
      simp only [hc]
      rcases hor with heq | hin
      · rw [heq]
        exact hchk.1
      · exact hchk.2 mc hin
    | _ => rfl
  rw [Tools.ShippingChecksDesign.designCheck_eq]
  exact Tools.ShippingChecksDepth.and_true_intro
    (Tools.ShippingChecksDesign.textCheckI_of
      (List.all_eq_true.mpr hT.kinds) hT.seqCheck.1 hT.seqCheck.2 hlinked hF.ndB hself hportsM
      (fun mn iname conns hm => by
        obtain ⟨mc, -, hc⟩ := hCm mn iname conns hm
        simp [hc]))
    hkids

/-- **A callee with a register whose own calls are tied by the general
closing**: its data conditions, its reflection and closing in every context,
`KidNames` of its callees, and `KidFacts` of its callees at the depths `n`
and `n + 1`. No field `leaf`, no field about `RealChild mref cref c`. -/
structure GenKid (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) (c : Name) (dk : MachineData) (nDecl : Nat)
    (namesK : Nat → List String) (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat)
    (n : Nat) : Prop where
  ok : dk.ok = true
  body : dk.shape.body = quote dk.dom
    (fun j => inputExpr dk.shape.binders.length (dk.bpos j))
    (fun j => inputExpr dk.shape.binders.length (dk.vpos j)) dk.packed
  calls : dk.callsOk nDecl = true
  ss : dk.ss.length = dk.shape.layout.slots.length
  dom : ∀ b ∈ dk.shape.binders.drop nDecl, b.2 ≠ .domain
  insts : dk.shape.insts ≠ []
  general : dk.shape.instFields ≠ []
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
  -- its own callees (the grandchildren): names, for the bridge
  kid : ∀ (k : Nat) (hk : k < dk.shape.insts.length) (y : Res),
    RealChild mref cref (dk.shape.insts[k]).1 y →
    KidNames (dk.shape.insts[k]).1 (namesK k) y.1 y.2
  self : (Sparkle.IR.ModuleName.ofDecl c) ∉ namesOf dk namesK
  -- its own callees: the same interface one level down, at the two depths
  kidsLo : ∀ (k : Nat) (hk : k < dk.shape.insts.length),
    KidFacts mref cref (dk.shape.insts[k]).1 (kidOuts k) (kidIns k) n
  kidsHi : ∀ (k : Nat) (hk : k < dk.shape.insts.length),
    KidFacts mref cref (dk.shape.insts[k]).1 (kidOuts k) (kidIns k) (n + 1)
  -- its two width conditions against its callees' tables
  callW : Tools.ShippingCallWidths.callWidthsOk dk nDecl kidOuts = true
  callA : Tools.ShippingPortsMatchRaw.callArgsOk dk nDecl kidIns = true
  -- its reflection and its closing, in every context
  entry : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
    MachineDefines mctx' mref cctx' cref c dk.shape
  closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
    MachineClosesAt mctx' mref cctx' cref c dk.shape

variable {c : Name} {dk : MachineData} {nDecl : Nat} {namesK : Nat → List String}
  {kidOuts : Nat → List OutField} {kidIns : Nat → List Nat} {n : Nat}

set_option maxHeartbeats 4000000 in
/-- **THE BRIDGE: a real child of such a callee is the post-processing of a
core run of the callee, and its design is that run's.** -/
theorem GenKid.core (K : GenKid mref cref c dk nDecl namesK kidOuts kidIns n) {y : Res}
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
theorem GenKid.outsIn (K : GenKid mref cref c dk nDecl namesK kidOuts kidIns n) {y : Res}
    (hy : RealChild mref cref c y) :
    ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
      p.name ≠ "rst" := by
  obtain ⟨mctx', cctx', _, _, _, _⟩ := hy.inv
  exact (Tools.ShippingKidsChildIface.kidsChild_of_real dk K.ok K.body K.calls K.ss K.dom
    K.insts K.slots K.outTy nDecl K.hkD K.hIlen K.hSL K.hSlen K.hLlen K.hNIn namesK K.nomem
    K.kid K.self (K.entry mctx' cctx') (fun mc cc _ => K.closes mc cc) hy).outsIn

/-- `hkidA` and `hkidR` (`kids_real_kid`, with the grandchildren's from
`kidsLo`). -/
theorem GenKid.kidAR (K : GenKid mref cref c dk nDecl namesK kidOuts kidIns n) {y : Res}
    (hy : RealChild mref cref c y) :
    (Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true) ∧
    (∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ y.2.modules, g2.name = mn) := by
  obtain ⟨mctx', cctx', _, _, _, _⟩ := hy.inv
  exact Tools.ShippingChecksCore.kids_real_kid dk K.ok K.body K.calls K.ss K.dom K.insts
    K.outTy namesK K.nomem K.kid
    (fun k hk y' hy' => (K.kidsLo k hk).kidA y' hy')
    (fun k hk y' hy' => (K.kidsLo k hk).kidR y' hy')
    K.self (K.entry mctx' cctx') K.closes hy

/-- The ports of the served module (`core_calls_portsG` at the callee's run). -/
theorem GenKid.ports (K : GenKid mref cref c dk nDecl namesK kidOuts kidIns n) {y : Res}
    (hy : RealChild mref cref c y) : CallsPorts c dk nDecl y.1 := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, -⟩ := K.core hy
  exact Tools.ShippingCallsPortsG.core_calls_portsG dk K.ok K.body K.calls K.ss K.dom
    K.insts K.general K.outTy K.nomem K.slots nDecl K.hkD K.hIlen K.hSL K.hSlen K.hLlen K.hNIn
    hB hcore hpost (K.entry mctx' cctx') (K.closes mctx' cctx')

/-- The served module is typed in its own wire table (`core_closed_typedIn`). -/
theorem GenKid.typedIn (K : GenKid mref cref c dk nDecl namesK kidOuts kidIns n) {y : Res}
    (hy : RealChild mref cref c y) : Tools.ShippingTextTyped.TypedIn y.1 := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, -⟩ := K.core hy
  exact Tools.ShippingClosedTyped.core_closed_typedIn dk K.ok K.body K.calls K.ss K.dom K.insts
    K.outTy K.nomem hB hcore hpost (K.entry mctx' cctx') (K.closes mctx' cctx') K.outName
    K.outScalar

/-- `hkidM` (the child's own module): its outputs are masked and no instance
connection names one. -/
theorem GenKid.masked (K : GenKid mref cref c dk nDecl namesK kidOuts kidIns n) {y : Res}
    (hy : RealChild mref cref c y) :
    Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, -⟩ := K.core hy
  exact Tools.ShippingCallsPortsG.outsMaskedN_of_callsG (K.ports hy) (K.typedIn hy)
    (fun p hp => (K.outsIn hy p hp).2)
    (Tools.ShippingCallsPortsG.core_conn_refsG dk K.ok K.body K.calls K.ss K.dom K.insts
      K.general K.outTy K.nomem hB hcore hpost (K.entry mctx' cctx') (K.closes mctx' cctx'))

/-- `hkidClk`: the clock and the reset are one bit in the emitted width map
(`core_clk` at the callee's run: it has a register of its own). -/
theorem GenKid.clk (K : GenKid mref cref c dk nDecl namesK kidOuts kidIns n) {y : Res}
    (hy : RealChild mref cref c y) :
    Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1 := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, -⟩ := K.core hy
  exact Tools.ShippingCoreClk.core_clk dk K.ok K.body K.calls K.ss K.dom K.insts K.outTy K.nomem
    K.slots hB hcore hpost (K.entry mctx' cctx') (K.closes mctx' cctx')

set_option maxHeartbeats 4000000 in
/-- **The check of the served module at depth `n`, and of the modules of the
served design at `kidCheck … (n + 1)`**, against every module list that
resolves the modules of the served design to themselves. -/
theorem GenKid.check (K : GenKid mref cref c dk nDecl namesK kidOuts kidIns n) {y : Res}
    (hy : RealChild mref cref c y) (ms : List Sparkle.IR.AST.Module)
    (hms : ∀ g ∈ y.2.modules, moduleByName ms g.name = some g) :
    Tools.ShippingDesignSV.designCheck (childMap ms) n y.1 = true ∧
      ∀ g ∈ y.2.modules,
        Tools.ShippingChecksDesign.kidCheck (childMap ms) (n + 1) g = true := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, hdes⟩ := K.core hy
  have entry := K.entry mctx' cctx'
  have closes : MachineClosesAt mctx' mref cctx' cref c dk.shape := K.closes mctx' cctx'
  have hmsD : ∀ g ∈ D.modules, moduleByName ms g.name = some g := fun g hg =>
    hms g (by rw [hdes]; exact hg)
  refine ⟨?_, ?_⟩
  · exact kids_designCheck_in dk K.ok K.body K.calls K.ss K.dom K.insts K.slots K.general
      K.outTy K.nomem kidOuts kidIns n K.kidsLo K.callW K.callA hB hcore hpost entry closes
      K.outName K.outScalar ms hmsD
  · -- a module of the served design is a real grandchild's, or of its design
    intro g hg
    rw [hdes] at hg
    obtain ⟨k, hk, y', hre, hor, hs1, hs2⟩ :=
      Tools.ShippingKidsSelf.core_kids_self dk K.ok K.body K.calls K.ss K.dom K.insts K.nomem
        hB hcore entry closes g hg
    have hy1 : moduleByName ms y'.1.name = some y'.1 :=
      hmsD y'.1 (Tools.ShippingHierPremisesBase.moduleByName_mem hs1).1
    have hy2 : ∀ g2 ∈ y'.2.modules, moduleByName ms g2.name = some g2 := fun g2 hg2 =>
      hmsD g2 (Tools.ShippingHierPremisesBase.moduleByName_mem (hs2 g2 hg2)).1
    have hchk := (K.kidsHi k hk).check y' hre ms hy1 hy2
    rcases hor with heq | hin
    · rw [heq]
      exact hchk.1
    · exact hchk.2 g hin

/-- **`KidFacts` of a callee with a register whose own calls are tied by the
general closing, at depth `n + 1`**, from `KidFacts` of its callees at the
depths `n` and `n + 1`. -/
theorem GenKid.facts (K : GenKid mref cref c dk nDecl namesK kidOuts kidIns n) :
    KidFacts mref cref c dk.shape.layout.outs (argWidths dk nDecl) (n + 1) :=
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
      exact ⟨(kidCheck_succ (childMap ms) n y.1).trans h0, hg⟩ }

end Tools.ShippingGenKid

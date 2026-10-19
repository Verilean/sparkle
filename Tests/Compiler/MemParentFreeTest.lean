import Tests.Compiler.MemParentClosesTest
import Tools.ShippingGenKidM
import Tools.ShippingKidFactsT
import Tools.ShippingLeafKidFacts
import Tools.ShippingSVBridge
import Tools.ShippingBndOnly
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # The check-free design-level endpoint of `memParent`, by hand (round par/d-1)

WRITTEN, NOT BUILT. TARGET-ONLY; not in `Tests.AllTests`. ASSERTING: every
theorem below and the two commands at the end are errors of the file when
they fail. It imports `Tests/Compiler/MemParentClosesTest.lean` (and through
it the probe `Tests/Compiler/MemDepthProbeTest.lean`) for the declarations
and for what their successful steps leave in the environment:

* of the probe: `machineData`, `machine_ok`, `machine_body` of `memCounterH`
  and `memParent`; `memCounterH.noPortsMem_data`, `memCounterH.noPortsMem_closes`
  (step C5); `memParent.machine_ships_hierNR1` (steps S2.a, S2.b);
* of the closing test: `memParent_closes`, `memCounterH_iface`, `memNames`,
  the tables `nkT`, `outsT`, `namesT` and `namesT_allMem`.

## What is proved

`memParent` is a register parent under the general closing with the call
entries `[cnt, cnt, memCounterH]`; `memCounterH` is a register machine whose
one call is a memory read. The generators refuse it
(`#machine_no_ports_kids`: "calls of its own under the GENERAL closing";
`#machine_no_ports_deep`: no `closes_deep`, then "a memory child").

    memCounterH_factsT : (∀ mctx' cctx', MachineDefines mctx' mref cctx' cref memCounterH …) →
        KidFactsT mref cref memCounterH memCounterH.machineData.shape.layout.outs
          (argWidths memCounterH.machineData 3) 1

by `Tools.ShippingGenKidM.GenKidM.factsT` (the kid's kids: the built memory
module, `memKid_facts` at depth 0), and

    memParent_design_noPorts1_closed :
      RunsTo (synthesizeCombinational memParent) mctx mref cctx cref w (b, design) w' →
      MachineDefines … memParent … → MachineDefines … cnt … → MachineDefines … memCounterH … →
      ∃ raw D, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
        (ChildBnd mref cref w → ∃ ids, … DesignSV (childMap D.modules) 1 (checkedOptimize b) … )

— no checker antecedent, no closing premise.

## How (and why not from `memParent.machine_design_svNR1`)

`memParent.machine_design_svNR1` states its check antecedents UNDER
`∃ raw D`, and nothing in its statement says that `(raw, D)` is the core
run's result; the antecedents cannot be discharged from outside. As every
built check-free generator, the endpoint is the head
`Tools.ShippingNoPorts.machine_design_noPorts` at the arguments of
`memParent.machine_ships_hierNR1`'s proof term, with its four run hypotheses
by `Tools.ShippingKidFactsT.kidsT_runFacts` / `kidsT_outsCheck` /
`kidsT_maskedN` / `kidsT_designCheck` at `memParent`'s data
(`memParent_runFacts1` … `memParent_designP1` below; `KidFactsT` of the three
entries: `cnt` by the built leaf facts `.toT`, `memCounterH` by
`memCounterH_factsT`). The application itself is the BUILT function
`Tools.ShippingNoPortsDeepCommand.endpointTermX` (`#noports_open_as`,
`Tools/ShippingBndOnly.lean`): `memParent_design_noPorts1`, with the closing
of `memParent` a binder and the boundary of the depth endpoint,

    ChildBnd mref cref w ∧ MachineDefines … cnt … ∧
      (MachineDefines … memCounterH … ∧
        ∀ mctx' cctx', ChildRanIn mref cref memCounterH mctx' cctx' →
          MachineClosesAt mctx' mref cctx' cref memCounterH … ∧
            ∀ wc raw D, ChildBnd mref cref wc → ChildBnd mref cref wc)

(read off `generateCoreNR`, `Tools/ShippingMachineDepthCommandR.lean`
641-692, 916-918; NOT printed — if it has another shape the last theorem
fails at its `refine`). The last theorem gives that boundary its components:
the kid's closing by `memCounterH.noPortsMem_closes`, `memParent`'s by
`memParent_closes`.

ASSUMED BY READING, as in the closing test: the call entries of `memParent`
are `[cnt, cnt, memCounterH]` (`memParent_calls` there), `nDecl` is 4 for
`memParent` and 3 for `memCounterH`. -/
namespace Tests.Compiler.MemParentFreeTest
open Sparkle.Tests.Compiler.MemDepthProbeTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.Compiler.MachMemory (memChild? memModule memChildName)
open Sparkle.IR.ModuleName (ofDecl ofMem)
open Tools.ShippingKidsChildIfaceM Tools.ShippingMemNamesP
open Tools.ShippingKidFactsT (KidFactsT)
open Tools.ShippingMemKid (memOuts memIns memKid_facts)
open Tools.ShippingGenKidM (GenKidM)
open Tests.Compiler.MemParentClosesTest

/-! ## `cnt` as a kid: the leaf interface (the generators' `cnt.machine_leafKid`, by hand) -/

/-- The leaf interface of `cnt` (`Tools.ShippingNoPortsCommand.leafKidTheorem`'s
term, under a name of this test). -/
theorem cnt_leafKid {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (entryC : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape) :
    Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref ``cnt cnt.machineData :=
  { ok := cnt.machine_ok
    body := cnt.machine_body
    calls := by decide
    dom := by decide
    leaf := rfl
    slots := fun h0 => absurd (congrArg List.length h0) (by decide)
    ss := by decide
    outTy := by decide
    outName := fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
      ((show ∀ o ∈ cnt.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
          Sparkle.IR.NameHints.charOk c = true from by
        first | decide | decide +kernel) o ho)
    outScalar := by decide
    entry := entryC
    closes := fun mc cc => cnt.machine_closes mc _ cc _ }

/-! ## `memCounterH` as a kid: `GenKidM` at depth 0, then `KidFactsT … 1` -/

set_option maxHeartbeats 4000000 in
/-- **`memCounterH` as a general-closing callee whose callees are memory
placeholders.** The data conditions: the fields of the built
`memCounterH.noPortsMem_data` (`MemOnlyData`, step C5 of the probe) where it
has them, the kernel's `decide` otherwise (and as a fallback). The kids: the
built memory module (`memKidNamesP`, `memKid_facts`). The closing: the built
`memCounterH.noPortsMem_closes`. -/
theorem memCounterH_genKidM {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR : ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context),
      Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref ``memCounterH
        memCounterH.machineData.shape) :
    GenKidM mref cref ``memCounterH memCounterH.machineData 3
      (fun _ => ofMem true 4 8) (fun _ => [ofMem true 4 8])
      (fun _ => memOuts 8) (fun _ => memIns 4 8) 0 :=
  { ok := memCounterH.machine_ok
    body := memCounterH.machine_body
    calls := by first | exact memCounterH.noPortsMem_data.calls | decide
    ss := by first | exact memCounterH.noPortsMem_data.slots | decide
    dom := by first | exact memCounterH.noPortsMem_data.domB | decide
    insts := fun h0 => absurd (congrArg List.length h0) (by decide)
    general := fun h0 => absurd (congrArg List.length h0) (by decide)
    slots := fun h0 => absurd (congrArg List.length h0) (by decide)
    outTy := by first | exact memCounterH.noPortsMem_data.outTy | decide
    outName := by
      first
        | exact memCounterH.noPortsMem_data.outNames
        | exact fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
            ((show ∀ o ∈ memCounterH.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
                Sparkle.IR.NameHints.charOk c = true from by
              first | decide | decide +kernel) o ho)
    outScalar := by first | exact memCounterH.noPortsMem_data.outScalar | decide
    hkD := by decide
    hIlen := by decide
    hSL := by decide
    hSlen := by decide
    hLlen := by decide
    hNIn := by decide
    kid := fun k hk _ hy =>
      memKidNamesP ((congrArg memChild? (memCounterH_entry k hk)).trans mem_isMem) hy
    self := ofDecl_not_mem_allMem ``memCounterH memNames_allMem
    kidsLo := fun k hk =>
      memKid_facts ((congrArg memChild? (memCounterH_entry k hk)).trans mem_isMem)
    callW := by
      first
        | exact memCounterH.noPortsMem_data.cw
        | decide
        | decide +kernel
    callA := by
      first
        | exact memCounterH.noPortsMem_data.args
        | decide
        | decide +kernel
    entry := hR
    closes := fun _ _ => memCounterH.noPortsMem_closes
    agree := by first | decide | decide +kernel }

/-- **`KidFactsT` of `memCounterH` at depth 1**: what a parent's check-free
depth chain takes of it — the check of its OWN module (`designCheck … 0`,
its instance's child the memory module at `leafCheck`). `KidFacts … 1` is
false of it (`Tests/Compiler/MemKidCheckProbe.lean`). -/
theorem memCounterH_factsT {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR : ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context),
      Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref ``memCounterH
        memCounterH.machineData.shape) :
    KidFactsT mref cref ``memCounterH memCounterH.machineData.shape.layout.outs
      (Tools.ShippingCallsChildPorts.argWidths memCounterH.machineData 3) 1 :=
  (memCounterH_genKidM hR).factsT

/-! ## The tables of `memParent`'s three entries, and `KidFactsT` of each -/

/-- The entries' callees' layout outputs, in the reader's order. -/
noncomputable def kidOutsP : Nat → List Sparkle.IR.Machine.OutField :=
  fun k => List.getD [cnt.machineData.shape.layout.outs, cnt.machineData.shape.layout.outs,
    memCounterH.machineData.shape.layout.outs] k []

/-- The entries' callees' argument widths, in the reader's order. -/
noncomputable def kidInsP : Nat → List Nat :=
  fun k => List.getD [Tools.ShippingPortWidthsPure.declWidths cnt.machineData,
    Tools.ShippingPortWidthsPure.declWidths cnt.machineData,
    Tools.ShippingCallsChildPorts.argWidths memCounterH.machineData 3] k []

/-- **`KidFactsT` of every call entry of `memParent`, at depth 1.** -/
theorem memParent_kidsT {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memCounterH
      memCounterH.machineData.shape) :
    ∀ (k : Nat) (hk : k < memParent.machineData.shape.insts.length),
      KidFactsT mref cref (memParent.machineData.shape.insts[k]).1 (kidOutsP k) (kidInsP k) 1 := by
  intro k hk
  have hk' : k < 3 := hk
  cases k with
  | zero =>
    exact (Tools.ShippingLeafKidFacts.leafKid_facts (cnt_leafKid hRc) 1).toT
  | succ k =>
    cases k with
    | zero =>
      exact (Tools.ShippingLeafKidFacts.leafKid_facts (cnt_leafKid hRc) 1).toT
    | succ k =>
      cases k with
      | zero =>
        exact memCounterH_factsT (fun _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx hRm)
      | succ k => exact absurd hk' (by omega)

/-- **The interfaces of `memParent`'s three kids** (the term of
`memParent_closes`' premise `hkid`, `Tests/Compiler/MemParentClosesTest.lean`
156-173: `cnt` by the built leaf route, `memCounterH` by `memCounterH_iface`).
Its fields `name` and `desNames` are the names `kidsT_designCheck` asks. -/
theorem memParent_kidIface {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memCounterH
      memCounterH.machineData.shape) :
    ∀ (k : Nat) (hk : k < memParent.machineData.shape.insts.length)
      (y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design),
      Tools.ShippingChildInv.RealChild mref cref (memParent.machineData.shape.insts[k]).1 y →
      Tools.ShippingCallsKidsD.ChildIfaceD (memParent.machineData.shape.insts[k]).1
        (nkT k) (outsT k) (namesT k) y.1 y.2 := by
  intro k hk y hy
  have hk' : k < 3 := hk
  cases k with
  | zero =>
    exact Tools.ShippingCallsKidsD.ChildIfaceG.toD
      (Tools.ShippingSeqChildIface.seqChild_of_real cnt.machineData cnt.machine_ok
        cnt.machine_body rfl (by decide) hRc (fun mc cc => cnt.machine_closes mc _ cc _) hy)
  | succ k =>
    cases k with
    | zero =>
      exact Tools.ShippingCallsKidsD.ChildIfaceG.toD
        (Tools.ShippingSeqChildIface.seqChild_of_real cnt.machineData cnt.machine_ok
          cnt.machine_body rfl (by decide) hRc (fun mc cc => cnt.machine_closes mc _ cc _) hy)
    | succ k =>
      cases k with
      | zero => exact memCounterH_iface hRm y hy
      | succ k => exact absurd hk' (by omega)

/-! ## The four run hypotheses of the head, at `memParent`'s data

The terms of `Tools.ShippingNoPortsKidsCommand.runTheorems` (the data
conditions decided in the same positions), with `kidsT_*` for `kids_*` and
the names for `kidsT_designCheck`. Binders: `hcore hpost entry closes`
(`hg`), then what `endpointTermX` finds in the endpoint's boundary. -/

set_option maxHeartbeats 4000000 in
theorem memParent_runFacts1 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``memParent [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memParent
      memParent.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``memParent
      memParent.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memCounterH
      memCounterH.machineData.shape) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingKidFactsT.kidsT_runFacts (nDecl := 4) memParent.machineData
    memParent.machine_ok memParent.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    kidOutsP kidInsP 1 (memParent_kidsT hRc hRm)
    (show Tools.ShippingCallWidths.callWidthsOk memParent.machineData 4 kidOutsP = true from by
      first | decide | decide +kernel)
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
theorem memParent_outsG1 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``memParent [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memParent
      memParent.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``memParent
      memParent.machineData.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memCounterH
      memCounterH.machineData.shape) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules)
      1 (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFactsT.kidsT_outsCheck (nDecl := 4) memParent.machineData
    memParent.machine_ok memParent.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    kidOutsP kidInsP 1 (memParent_kidsT hRc hRm)
    hB hcore hpost entry closes hg

set_option maxHeartbeats 4000000 in
theorem memParent_maskedG1 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``memParent [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memParent
      memParent.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``memParent
      memParent.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memCounterH
      memCounterH.machineData.shape) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingKidFactsT.kidsT_maskedN (nDecl := 4) memParent.machineData
    memParent.machine_ok memParent.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    kidOutsP kidInsP 1 (memParent_kidsT hRc hRm)
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
theorem memParent_designP1 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``memParent [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memParent
      memParent.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``memParent
      memParent.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memCounterH
      memCounterH.machineData.shape) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules)
      1 (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFactsT.kidsT_designCheck (nDecl := 4) memParent.machineData
    memParent.machine_ok memParent.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    kidOutsP kidInsP 1 (memParent_kidsT hRc hRm)
    (show Tools.ShippingCallWidths.callWidthsOk memParent.machineData 4 kidOutsP = true from by
      first | decide | decide +kernel)
    (show Tools.ShippingPortsMatchRaw.callArgsOk memParent.machineData 4 kidInsP = true from by
      first | decide | decide +kernel)
    namesT
    (fun k hk y hy =>
      ⟨(memParent_kidIface hRc hRm k hk y hy).name,
       (memParent_kidIface hRc hRm k hk y hy).desNames⟩)
    (fun k _ k' _ => ofDecl_not_mem_allMem _ (namesT_allMem k'))
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
      ((show ∀ o ∈ memParent.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
          Sparkle.IR.NameHints.charOk c = true from by
        first | decide | decide +kernel) o ho))
    (by decide)

/-! ## The endpoint -/

-- the head `machine_design_noPorts` at the arguments of
-- `memParent.machine_ships_hierNR1`, by the BUILT `endpointTermX`: the closing
-- of `memParent` is still a binder, the boundary still the depth endpoint's
#noports_open_as memParent_design_noPorts1 := memParent 1 memParent_runFacts1 memParent_outsG1
  memParent_maskedG1 memParent_designP1 [ ]

set_option maxHeartbeats 4000000 in
/-- **The check-free design-level endpoint of `memParent`, closed.** Premises:
the run of the full entry, the reflections of `memParent`, `cnt` and
`memCounterH` at the run's contexts; under `∃ raw D`, the runtime laws at the
start world (`ChildBnd`) only. No checker antecedent, no closing premise. -/
theorem memParent_design_noPorts1_closed :
    bnd_only% memParent_design_noPorts1 [cnt, memCounterH] := by
  intro mctx mref cctx cref w w' b design hr hP hRc hRm
  obtain ⟨raw, D, hpost, h⟩ := memParent_design_noPorts1 hr hP (memParent_closes hRc hRm)
  -- the depth endpoint's boundary, component by component: the runtime laws,
  -- `cnt`'s premise, `memCounterH`'s reflection, and its closing and own
  -- boundary in every context it is synthesised in
  refine ⟨raw, D, hpost, fun hB => h ⟨hB, ?_, hRm, fun _ _ _ =>
    ⟨memCounterH.noPortsMem_closes, fun _ _ _ hb => hb⟩⟩⟩
  -- `cnt` is a leaf: its reflection alone when its closing is a theorem
  -- (`cnt.machine_closes`), with the closing otherwise
  first
    | exact hRc
    | exact ⟨hRc, fun mc cc _ => cnt.machine_closes mc _ cc _⟩

/-! ## The statement check and the axioms -/

-- the census's own re-check on the stored statement: every proposition
-- binder and the antecedent under the existentials ALLOWED, no checker /
-- closing constant, `DesignSV` mentioned. An error unless it passes.
#assert_check_free memParent_design_noPorts1_closed

#print axioms memCounterH_factsT
#print axioms memParent_design_noPorts1_closed

end Tests.Compiler.MemParentFreeTest

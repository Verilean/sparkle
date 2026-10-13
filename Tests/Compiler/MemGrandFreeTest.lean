import Tests.Compiler.MemParentFreeTest
import Tools.ShippingGenKidT
import Tools.ShippingCallSelf

/-! # `memGrand` (depth 2): the check antecedents discharged by hand; the closing stays a premise (round par/d-1)

WRITTEN, NOT BUILT. TARGET-ONLY; not in `Tests.AllTests`. ASSERTING for its
theorems (an error here is an error of the file); the last command only
LOGS, because the last statement is known NOT to be check-free.

`memGrand` is a register parent under the general closing with the call
entries `[cnt, cnt, memParent]` (ASSUMED BY READING; `memGrand_calls` checks
it), and `memParent` itself calls `cnt` and `memCounterH`.

## What is proved

* `memParent_genKidT`: `memParent` as a general-closing callee
  (`Tools.ShippingGenKidT.GenKidT … 1`: its callees' `KidFactsT … 1` are
  `memParent_kidsT`), hence `KidFactsT … memParent … 2`.
* `memGrand_runFacts2`, `memGrand_outsG2`, `memGrand_maskedG2`,
  `memGrand_designP2`: the four run hypotheses of the head at `memGrand`'s
  data and depth 2 — the last by `Tools.ShippingCallSelf.kidsT_designCheckO`,
  WITHOUT a name premise.
* `memGrand_design_noPorts2`: the head `machine_design_noPorts` at the
  arguments of `memGrand.machine_ships_hierNR2` (the BUILT `endpointTermX`),
  with the extra binder `MachineDefines … memCounterH …` (a descendant that
  is not a direct callee). No checker antecedent.
* `memGrand_design_noPorts2_bnd`: the same with the boundary reduced to
  `ChildBnd mref cref w` — the closings of the descendants (`memParent`,
  `memCounterH`) are theorems; the closing of `memGrand` ITSELF is still a
  binder.

## Why the name-free `kidsT_designCheckO`

`cnt` is a callee of `memGrand` AND a callee of its callee `memParent`. The
built `kidsT_designCheck` asks `hsep`: no callee's printed name is a name
below a callee — FALSE here (`ofDecl cnt` is a name below `memParent`).
`core_callSelf` needs no names.

## THE OBSTACLE: the closing of `memGrand`

`MachineClosesAt … memGrand …` is NOT derived. The built theorem for a
parent of children with designs, `Tools.ShippingCallsKidsD.machineClosesAt_of_kidsD`,
asks `hdisjD`: for two entries with different callees, the first callee's
printed name is not a name below the second — for the entries `cnt` and
`memParent` that is `ofDecl cnt ∉ (names below memParent)`, which is false:
`memParent` calls `cnt`. This is the shape of `mixDeep` (a callee that is
also a descendant of another callee; "Finding H"), not a fact about
memories. So the last statement has ONE premise the final goal does not
allow, and `#log_check_free` is expected to say DOES NOT PASS with the
closing constant `MachineClosesAt`. -/
namespace Tests.Compiler.MemGrandFreeTest
open Sparkle.Tests.Compiler.MemDepthProbeTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.IR.ModuleName (ofDecl ofMem)
open Tools.ShippingMemNamesP
open Tools.ShippingKidFactsT (KidFactsT)
open Tools.ShippingGenKidT (GenKidT)
open Tests.Compiler.MemParentClosesTest
open Tests.Compiler.MemParentFreeTest

/-- The call entries of `memGrand`, in the reader's order. -/
theorem memGrand_calls :
    memGrand.machineData.shape.insts.map (·.1) = [``cnt, ``cnt, ``memParent] := by decide

/-! ## `memParent` as a kid: `GenKidT` at depth 1, then `KidFactsT … 2` -/

/-- `memParent`'s module name is not the name of one of its callees' modules
nor a name below one (a memory-module name). -/
theorem memParent_self :
    ofDecl ``memParent ∉ Tools.ShippingKidsChildIface.namesOf memParent.machineData namesT := by
  intro h
  unfold Tools.ShippingKidsChildIface.namesOf at h
  rcases List.mem_append.mp h with h1 | h2
  · obtain ⟨x, hx, e⟩ := List.mem_map.mp h1
    exact Tools.ShippingNameDischarge.parent_ne memParent.machineData.shape.insts ``memParent
      (by decide) x hx e
  · obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp h2
    exact ofDecl_not_mem_allMem ``memParent (namesT_allMem k) hk

set_option maxHeartbeats 4000000 in
/-- **`memParent` as a general-closing callee** (the generators'
`k.machine_genKid{d}`, by hand, over `KidFactsT`): the data conditions
decided in the generator's positions, the kids' names from
`memParent_kidIface`, the kids' facts `memParent_kidsT`, the closing
`memParent_closes`. -/
theorem memParent_genKidT {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memParent
      memParent.machineData.shape)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memCounterH
      memCounterH.machineData.shape) :
    GenKidT mref cref ``memParent memParent.machineData 4 namesT kidOutsP kidInsP 1 :=
  { ok := memParent.machine_ok
    body := memParent.machine_body
    calls := by decide
    ss := by decide
    dom := by decide
    insts := fun h0 => absurd (congrArg List.length h0) (by decide)
    general := fun h0 => absurd (congrArg List.length h0) (by decide)
    slots := fun h0 => absurd (congrArg List.length h0) (by decide)
    outTy := by decide
    outName := fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
      ((show ∀ o ∈ memParent.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
          Sparkle.IR.NameHints.charOk c = true from by
        first | decide | decide +kernel) o ho)
    outScalar := by decide
    nomem := by decide
    hkD := by decide
    hIlen := by decide
    hSL := by decide
    hSlen := by decide
    hLlen := by decide
    hNIn := by decide
    kid := fun k hk y hy =>
      Tools.ShippingCallsKidsD.ChildIfaceD.kid (memParent_kidIface hRc hRm k hk y hy)
    self := memParent_self
    kidsLo := memParent_kidsT hRc hRm
    callW := by first | decide | decide +kernel
    callA := by first | decide | decide +kernel
    entry := fun _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx hRp
    closes := fun _ _ =>
      memParent_closes (Tools.ShippingReflectCtx.MachineDefines.ctx hRc)
        (Tools.ShippingReflectCtx.MachineDefines.ctx hRm) }

/-! ## The tables of `memGrand`'s three entries, and `KidFactsT` of each -/

noncomputable def kidOutsGr : Nat → List Sparkle.IR.Machine.OutField :=
  fun k => List.getD [cnt.machineData.shape.layout.outs, cnt.machineData.shape.layout.outs,
    memParent.machineData.shape.layout.outs] k []

noncomputable def kidInsGr : Nat → List Nat :=
  fun k => List.getD [Tools.ShippingPortWidthsPure.declWidths cnt.machineData,
    Tools.ShippingPortWidthsPure.declWidths cnt.machineData,
    Tools.ShippingCallsChildPorts.argWidths memParent.machineData 4] k []

/-- **`KidFactsT` of every call entry of `memGrand`, at depth 2.** -/
theorem memGrand_kidsT {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memParent
      memParent.machineData.shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memCounterH
      memCounterH.machineData.shape) :
    ∀ (k : Nat) (hk : k < memGrand.machineData.shape.insts.length),
      KidFactsT mref cref (memGrand.machineData.shape.insts[k]).1 (kidOutsGr k) (kidInsGr k) 2 := by
  intro k hk
  have hk' : k < 3 := hk
  cases k with
  | zero =>
    exact (Tools.ShippingLeafKidFacts.leafKid_facts (cnt_leafKid hRc) 2).toT
  | succ k =>
    cases k with
    | zero =>
      exact (Tools.ShippingLeafKidFacts.leafKid_facts (cnt_leafKid hRc) 2).toT
    | succ k =>
      cases k with
      | zero => exact (memParent_genKidT hRp hRc hRm).factsT
      | succ k => exact absurd hk' (by omega)

/-! ## The four run hypotheses of the head, at `memGrand`'s data, depth 2 -/

set_option maxHeartbeats 4000000 in
theorem memGrand_runFacts2 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``memGrand [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memGrand
      memGrand.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``memGrand
      memGrand.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memParent
      memParent.machineData.shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memCounterH
      memCounterH.machineData.shape) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingKidFactsT.kidsT_runFacts (nDecl := 4) memGrand.machineData
    memGrand.machine_ok memGrand.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    kidOutsGr kidInsGr 2 (memGrand_kidsT hRc hRp hRm)
    (show Tools.ShippingCallWidths.callWidthsOk memGrand.machineData 4 kidOutsGr = true from by
      first | decide | decide +kernel)
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
theorem memGrand_outsG2 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``memGrand [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memGrand
      memGrand.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``memGrand
      memGrand.machineData.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memParent
      memParent.machineData.shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memCounterH
      memCounterH.machineData.shape) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules)
      2 (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFactsT.kidsT_outsCheck (nDecl := 4) memGrand.machineData
    memGrand.machine_ok memGrand.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    kidOutsGr kidInsGr 2 (memGrand_kidsT hRc hRp hRm)
    hB hcore hpost entry closes hg

set_option maxHeartbeats 4000000 in
theorem memGrand_maskedG2 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``memGrand [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memGrand
      memGrand.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``memGrand
      memGrand.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memParent
      memParent.machineData.shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memCounterH
      memCounterH.machineData.shape) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingKidFactsT.kidsT_maskedN (nDecl := 4) memGrand.machineData
    memGrand.machine_ok memGrand.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    kidOutsGr kidInsGr 2 (memGrand_kidsT hRc hRp hRm)
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
theorem memGrand_designP2 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``memGrand [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memGrand
      memGrand.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``memGrand
      memGrand.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memParent
      memParent.machineData.shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memCounterH
      memCounterH.machineData.shape) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules)
      2 (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingCallSelf.kidsT_designCheckO (nDecl := 4) memGrand.machineData
    memGrand.machine_ok memGrand.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    kidOutsGr kidInsGr 2 (memGrand_kidsT hRc hRp hRm)
    (show Tools.ShippingCallWidths.callWidthsOk memGrand.machineData 4 kidOutsGr = true from by
      first | decide | decide +kernel)
    (show Tools.ShippingPortsMatchRaw.callArgsOk memGrand.machineData 4 kidInsGr = true from by
      first | decide | decide +kernel)
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
      ((show ∀ o ∈ memGrand.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
          Sparkle.IR.NameHints.charOk c = true from by
        first | decide | decide +kernel) o ho))
    (by decide)

/-! ## The endpoint, its closing a premise -/

-- the head at the arguments of `memGrand.machine_ships_hierNR2`; after its
-- binders: `MachineDefines … memCounterH …` (not a direct callee: its
-- reflection at the run's contexts is not a conjunct of the boundary)
#noports_open_as memGrand_design_noPorts2 := memGrand 2 memGrand_runFacts2 memGrand_outsG2
  memGrand_maskedG2 memGrand_designP2 [memCounterH]

set_option maxHeartbeats 4000000 in
/-- **The depth-2 endpoint of `memGrand` without a checker antecedent, its
boundary reduced to the runtime laws at the start world.** The closings of
`memParent` and `memCounterH` are discharged; the closing of `memGrand`
ITSELF is still a premise (the header: the obstacle). -/
theorem memGrand_design_noPorts2_bnd :
    bnd_only_closing% memGrand_design_noPorts2 [cnt, memParent, memCounterH] := by
  intro mctx mref cctx cref w w' b design hr hP hcl hRc hRp hRm
  obtain ⟨raw, D, hpost, h⟩ := memGrand_design_noPorts2 hr hP hcl hRm
  -- the boundary: the runtime laws, `cnt`'s premise, `memParent`'s reflection,
  -- and in every context `memParent` is synthesised in: its closing and its
  -- own boundary (the runtime laws there, `cnt`'s premise, `memCounterH`'s
  -- reflection, closing and boundary)
  refine ⟨raw, D, hpost, fun hB => h ⟨hB, ?_, hRp, fun _ _ _ =>
    ⟨memParent_closes (Tools.ShippingReflectCtx.MachineDefines.ctx hRc)
        (Tools.ShippingReflectCtx.MachineDefines.ctx hRm),
      fun _ _ _ hb => ⟨hb, ?_, Tools.ShippingReflectCtx.MachineDefines.ctx hRm, fun _ _ _ =>
        ⟨memCounterH.noPortsMem_closes, fun _ _ _ hb' => hb'⟩⟩⟩⟩⟩
  all_goals
    first
      | exact hRc
      | exact Tools.ShippingReflectCtx.MachineDefines.ctx hRc
      | exact ⟨hRc, fun mc cc _ => cnt.machine_closes mc _ cc _⟩
      | exact ⟨Tools.ShippingReflectCtx.MachineDefines.ctx hRc,
          fun mc cc _ => cnt.machine_closes mc _ cc _⟩

/-! ## The statement check (LOG only) and the axioms -/

-- expected: DOES NOT PASS, with the one closing constant `MachineClosesAt`
-- (the closing of `memGrand`); no checker constant
#log_check_free memGrand_design_noPorts2_bnd

#print axioms memParent_genKidT
#print axioms memGrand_design_noPorts2_bnd

end Tests.Compiler.MemGrandFreeTest

import Tests.Compiler.NoPortsTopD2Test
import Tools.ShippingLeafKidFacts

/-! # `mixDeep` by hand: the OPEN depth-2 endpoint without the four check premises, over THREE kinds of children; NO closed form (G1, unit U3, round par/a-16, repaired after the first build)

`mixDeep → {mid2 → midH → rcH, midH → rcH, cnt}`
(`Tests/Compiler/ShippingChildBoundaryTest.lean` 278–286, READ):

    def mixDeep (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
      circuit do
        let r ← Signal.reg 0#8
        let rs := (r : Signal defaultDomain (BitVec 8))
        let a := mid2 en
        let b := midH en
        let c := cnt en
        r <~ Signal.mux a.hit (rs + b.n + c.n) rs
        return rs

## Why there is NO closed form (the first build of this file, and the reading)

MEASURED (integrator's build of 3b70e5eb): `#machine_closes_deep mixDeep`
succeeded, but `mixDeep.closes_deep` has 7 premises: the four reflections
and THREE name premises, and the audit of the closed endpoint threw on them.

READ (`Tools/ShippingChildIfaceGen.lean` 181–232): the generator discharges
the three name hypotheses of `machineClosesAt_of_kidsD` (`hparentD`,
`hselfD`, `hdD`) by a kernel `decide` only when its Boolean `namesSep`
holds; otherwise it turns ALL THREE into premises (`hN_…_parentD`,
`…_selfD`, `…_disjD`) — a branch, not a silently caught failure. `namesSep`
asks, for different callees `k`, `k'`, that `k` be separated (`sepB`) from
every descendant declaration of `k'`. For `mixDeep`, `k = midH` and
`k' = mid2`: the descendants of `mid2` are `midH`, `rcH`, and `sepB midH
midH` is false (a name is not separated from itself). `grandH`, `topD2`
(one callee) and `mixD1` (`midH`, `cnt`: no shared descendant) do not meet
this.

READ (`Tools/ShippingCallsKidsD.lean` 131–133), the hypothesis behind the
third premise:

    (hdD : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 ≠ (d.shape.insts[k']).1 →
      Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1 ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k')

For `mixDeep` this is not an undecided condition: it is FALSE BY READING.
With `k` an entry of `midH` and `k'` an entry of `mid2`, `namesK k'` is the
printed list of `mid2`'s descendants, which contains `midH`'s printed name
(and `rcH`'s is in both `namesK k` and `namesK k'`). So
`mixDeep.closes_deep` as generated has an unsatisfiable premise, and an
endpoint closed with it would be vacuous. This file therefore does NOT run
`#machine_closes_deep mixDeep` and adds NO `_closed` endpoint. The first
`run_cmd` asserts the measured fact the reading rests on (`midH` is a call
entry of `mixDeep` AND of `mid2`).

MISSING (exact): a closing theorem for a general-closing parent whose
different callees SHARE a descendant declaration — `machineClosesAt_of_kidsD`
with `hdD` weakened from disjointness of the descendants' printed names to
"a printed name met under two callees is of the same declaration" (the
merged design holds one module per declaration), and, for the first
conjunct, "a callee's printed name among another callee's descendants is
that callee itself". Not attempted here: it is a statement about the
closing's design merge (`Tools/ShippingCallsKidsD.lean`), not about this
declaration.

## What IS proved: `mixD1`'s pattern with three kinds of entries

    mid2   GenKid.facts (mid2_kid …)                  KidFacts … (1 + 1)    NoPortsTopD2Test (BUILT)
    midH   Tools.ShippingOneOutKidDepth.factsN (midH_kid …) 1               KidFacts … (1 + 1)
    cnt    Tools.ShippingLeafKidFacts.leafKid_facts (cnt.machine_leafKid …) 2

The per-entry tables are indexed by the callee's NAME (`calleeOf k`,
`outsOf`, `insOf`), with two decided ∀-statements (`mixDeep_callee`,
`mixDeep_three`); they do not depend on the entry count or order. (These
theorems elaborated in the first build: it reached the audit.)

## EXPECTED (the audit THROWS otherwise)

| endpoint | premise of `mixDeep.machine_design_svNR2` | state |
|---|---|---|
| `mixDeep.machine_design_noPortsNR2` (OPEN form only) | `shipsHierCheck (childMap D.modules) b` | predicted absent (the generation step ran in the first build; this revision is NOT BUILT) |
| | `kidsMaskedN D.modules b.body` | predicted absent |
| | `designCheck (childMap D.modules) 2 (checkedOptimize b)` (incl. `kidsPass`, `portsMatchB`) | predicted absent |
| | `outsCheck (childMap D.modules) 2 (checkedOptimize b)` | predicted absent |
| | `MachineClosesAt mixDeep` | STAYS — NOT ALLOWED, not removed, no closed form |
| | the boundary | STAYS, unchanged, not reduced (no `closedB`, no gap theorem) |
| | `hr`, `MachineDefines mixDeep` | stay |
| | — | ADDED: `EntryDefines rcH` at the run's contexts |

So `mixDeep` is NOT a check-free, gap-free endpoint: four check premises
are predicted gone, the closing and the boundary remain.

## SCOPE (binding for any report)

ONE declaration, `mixDeep`, at depth 2, OPEN form. Data conditions decided
per declaration by the kernel are conditions, not reductions. The result
depends on the compiler's guards with fallback. The conclusion is about
`DesignSV (childMap D.modules) 2 (checkedOptimize b)` — the module list
(children UNOPTIMISED), not the SV string, not `#sim`.

UNVERIFIED at the time of writing: this revision was not built. -/

/-! ## The shapes this file relies on: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
  let m2 := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
  let m := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let rg ← Tools.ShippingMachineCommand.readMachine g
  let r2 ← Tools.ShippingMachineCommand.readMachine m2
  let rm ← Tools.ShippingMachineCommand.readMachine m
  let rcn ← Tools.ShippingMachineCommand.readMachine c
  let env ← Lean.getEnv
  let ge := rg.shape.insts.map (·.1)
  let need := [g ++ `machine_ships_hierNR2, g ++ `machine_design_svNR2, m2 ++ `closes_deep,
    m ++ `closes_deep, c ++ `machine_leafKid,
    c ++ `machine_closes, rc ++ `gate_full, rc ++ `gate_peel,
    ``Tests.Compiler.NoPortsGrandHTest.midH_kid, ``Tests.Compiler.NoPortsTopD2Test.mid2_kid]
  let present := need.filter fun n => env.contains n
  let absent := need.filter fun n => !env.contains n
  let gatey := [m2, m, c].filter fun k => env.contains (k ++ `gate_peel)
  let hasCl := env.contains (g ++ `closes_deep)
  Lean.logInfo m!"NOPORTS MIXDEEP DATA {g}: nDecl={rg.nDecl}, call entries {ge}, instFields={rg.shape.instFields}, slots={rg.shape.layout.slots.length}, outputs {rg.shape.layout.outs.map (·.name)}; {m2}: nDecl={r2.nDecl}, call entries {r2.shape.insts.map (·.1)}; {m}: nDecl={rm.nDecl}, call entries {rm.shape.insts.map (·.1)}; {c}: nDecl={rcn.nDecl}, call entries {rcn.shape.insts.map (·.1)}; callees with gate_peel (gate children for the generators): {gatey}; closes_deep of {g} present already: {hasCl}; in the imports: {present}; NOT in the imports: {absent}"
  unless absent.isEmpty do throwError "not in the imports (this file builds on them): {absent}"
  unless rg.nDecl == 1 do throwError "{g}: nDecl = {rg.nDecl}, the hand theorems are written for 1"
  unless r2.nDecl == 2 do throwError "{m2}: nDecl = {r2.nDecl}, mid2_kid is written for 2"
  unless rm.nDecl == 2 do throwError "{m}: nDecl = {rm.nDecl}, midH_kid is written for 2"
  let kids := ge.eraseDups
  unless kids.length == 3 && kids.contains m2 && kids.contains m && kids.contains c do
    throwError "{g}: the distinct callees are {kids}, expected {m2}, {m} and {c}"
  if rg.shape.instFields.isEmpty then throwError "{g}: instFields = [] — not the general closing"
  if rg.shape.layout.slots.isEmpty then throwError "{g}: no register"
  unless rcn.shape.insts.isEmpty do throwError "{c}: has calls — not a leaf"
  unless gatey.isEmpty do throwError "{gatey}: a callee with gate_peel (a gate child for the generators)"
  -- the measured fact behind "no closed form": a direct callee of the parent is
  -- also a callee of another direct callee (a SHARED descendant)
  let e2 := r2.shape.insts.map (·.1)
  unless ge.contains m && e2.contains m do
    throwError "{g}: {m} is not both a call entry of {g} ({ge}) and of {m2} ({e2}) — the reading in the header is wrong"
  Lean.logInfo m!"NOPORTS MIXDEEP SHARED {g}: {m} is a call entry of {g} and of its callee {m2} ({e2}): the disjointness hypothesis hdD of machineClosesAt_of_kidsD cannot hold for the entries of {m} against those of {m2} (READ, not proved here); no closed form is generated"
  for n in [g ++ `machine_design_noPortsNR2, g ++ `machine_design_noPortsNR2_closed] do
    if env.contains n then throwError "{n}: exists already"

namespace Tests.Compiler.NoPortsMixDeepTest
open Tools.ShippingKidFacts (KidFacts)
open Tools.ShippingCallsChildPorts (argWidths)
open Tests.Compiler.NoPortsGrandHTest (midH_kid)
open Tests.Compiler.NoPortsTopD2Test (mid2_kid)

/-- The callee of the call entry `k` of `mixDeep`, read off the reflected
data (anonymous out of range). -/
noncomputable def calleeOf (k : Nat) : Lean.Name :=
  (((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.insts).map (fun c => c.1)).getD k Lean.Name.anonymous

/-- The layout outputs of a callee, by its NAME. -/
noncomputable def outsOf (c : Lean.Name) : List Sparkle.IR.Machine.OutField :=
  if c = ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 then (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.layout.outs
  else if c = ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH then (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape.layout.outs
  else (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.layout.outs

/-- The argument widths of a callee, by its NAME. -/
noncomputable def insOf (c : Lean.Name) : List Nat :=
  if c = ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 then argWidths Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData 2
  else if c = ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH then argWidths Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData 2
  else Tools.ShippingPortWidthsPure.declWidths Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData

/-- The per-entry tables. -/
noncomputable def outsT (k : Nat) : List Sparkle.IR.Machine.OutField := outsOf (calleeOf k)

noncomputable def insT (k : Nat) : List Nat := insOf (calleeOf k)

theorem midH_ne_mid2 : ¬ (``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH = ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2) := by decide

theorem cnt_ne_mid2 : ¬ (``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt = ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2) := by decide

theorem cnt_ne_midH : ¬ (``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt = ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH) := by decide

theorem outsOf_mid2 : outsOf ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 = (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.layout.outs :=
  if_pos rfl

theorem outsOf_midH : outsOf ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH = (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape.layout.outs :=
  (if_neg midH_ne_mid2).trans (if_pos rfl)

theorem outsOf_cnt : outsOf ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt = (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.layout.outs :=
  (if_neg cnt_ne_mid2).trans (if_neg cnt_ne_midH)

theorem insOf_mid2 : insOf ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 = argWidths Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData 2 :=
  if_pos rfl

theorem insOf_midH : insOf ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH = argWidths Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData 2 :=
  (if_neg midH_ne_mid2).trans (if_pos rfl)

theorem insOf_cnt : insOf ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt =
    Tools.ShippingPortWidthsPure.declWidths Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData :=
  (if_neg cnt_ne_mid2).trans (if_neg cnt_ne_midH)

/-- Entry `k`'s callee is `calleeOf k` (ONE statement, decided on the
reflected data; independent of the entry count). -/
theorem mixDeep_callee : ∀ (k : Nat) (hk : k < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.insts[k]).1 = calleeOf k := by
  first | decide | decide +kernel

/-- Every entry's callee is `mid2`, `midH` or `cnt` (ONE decided statement). -/
theorem mixDeep_three : ∀ (k : Nat), k < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.insts.length →
    calleeOf k = ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 ∨ calleeOf k = ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH ∨ calleeOf k = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **`KidFacts` at depth 2 of each of the three callees**, against the
tables at its name. -/
theorem mixDeep_kidOf {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) (c : Lean.Name)
    (h : c = ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 ∨ c = ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH ∨ c = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt) :
    KidFacts mref cref c (outsOf c) (insOf c) 2 := by
  rcases h with h | h | h
  · rw [h, outsOf_mid2, insOf_mid2]
    exact (mid2_kid hRm2 hRm hRr).facts
  · rw [h, outsOf_midH, insOf_midH]
    exact Tools.ShippingOneOutKidDepth.factsN (midH_kid hRm hRr) 1
  · rw [h, outsOf_cnt, insOf_cnt]
    exact Tools.ShippingLeafKidFacts.leafKid_facts (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_leafKid hRc) 2

/-- **`KidFacts` of every call entry's callee of `mixDeep`**, at depth 2. -/
theorem mixDeep_kids {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    ∀ (k : Nat) (hk : k < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.insts.length),
      KidFacts mref cref ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.insts[k]).1 (outsT k) (insT k) 2 := by
  intro k hk
  rw [mixDeep_callee k hk]
  exact mixDeep_kidOf hRm2 hRm hRr hRc (calleeOf k) (mixDeep_three k hk)

/-- The two width conditions of `mixDeep` against the tables. -/
theorem mixDeep_callWidths :
    Tools.ShippingCallWidths.callWidthsOk Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData 1 outsT = true := by
  first | decide | decide +kernel

theorem mixDeep_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData 1 insT = true := by
  first | decide | decide +kernel

theorem mixDeep_outChars : ∀ o ∈ (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape.layout.outs,
    ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The run's facts of `mixDeep`'s full-entry module** (`kids_runFacts`). -/
theorem mixDeep_runFacts {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingKidFacts.kids_runFacts (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_ok
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    outsT insT 2 (mixDeep_kids hRm2 hRm hRr hRc) mixDeep_callWidths
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **The output check at depth 2 under the statement-kind gate**
(`kids_outsCheck`). -/
theorem mixDeep_outsG2 {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFacts.kids_outsCheck (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_ok
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    outsT insT 2 (mixDeep_kids hRm2 hRm hRr hRc)
    hB hcore hpost entry closes hg

set_option maxHeartbeats 4000000 in
/-- **The children's masked outputs** (`kids_maskedN`). -/
theorem mixDeep_maskedG {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingKidFacts.kids_maskedN (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_ok
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    outsT insT 2 (mixDeep_kids hRm2 hRm hRr hRc)
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 2 of the shipped module, with no check premise**
(`kids_designCheck`). -/
theorem mixDeep_designP2 {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFacts.kids_designCheck (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_ok
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    outsT insT 2 (mixDeep_kids hRm2 hRm hRr hRc) mixDeep_callWidths mixDeep_callArgs
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (mixDeep_outChars o ho))
    (by decide)

end Tests.Compiler.NoPortsMixDeepTest

/-! ## The OPEN endpoint (no closed form: see the header) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let extras (ctx : Array Lean.Expr) : Lean.Meta.MetaM (Array (Lean.Name × Lean.Expr)) := do
    let tR ← Lean.Meta.mkAppM ``Tools.ShippingInlineSoundness.EntryDefines
      (ctx ++ #[Lean.toExpr rc, Lean.mkConst (rc ++ `gateValue)])
    return #[(`hRr, tR)]
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsTopD2Test.generateX g 2 extras
      ``Tests.Compiler.NoPortsMixDeepTest.mixDeep_runFacts
      ``Tests.Compiler.NoPortsMixDeepTest.mixDeep_outsG2
      ``Tests.Compiler.NoPortsMixDeepTest.mixDeep_maskedG
      ``Tests.Compiler.NoPortsMixDeepTest.mixDeep_designP2
  Lean.logInfo m!"NOPORTS MIXDEEP OPEN [{name}]: the depth-2 endpoint of a parent with a child under the general closing (mid2), a child with a one-output call of a gate (midH) and a leaf register machine child (cnt), without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents — by hand (mixDeep_kidOf: GenKid.facts of mid2, factsN of midH at 1, leafKid_facts of cnt at 2; mixDeep_kids over the name-indexed tables; mixDeep_runFacts, mixDeep_outsG2, mixDeep_maskedG, mixDeep_designP2: Tools.ShippingKidFacts.kids_* at depth 2). OPEN form: it ASKS MachineClosesAt of {g}; NO closed form (the closing's disjointness hypothesis does not hold for a shared descendant). One binder ADDED against the open base endpoint: the reflection of {rc} at the run's contexts"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let old := g ++ `machine_design_svNR2
  let openN := g ++ `machine_design_noPortsNR2
  let closed := g ++ `machine_design_noPortsNR2_closed
  -- (a) standard axioms
  for n in [``Tools.ShippingGenKid.GenKid.facts, ``Tools.ShippingOneOutKidDepth.factsN,
      ``Tools.ShippingLeafKidFacts.leafKid_facts,
      ``Tests.Compiler.NoPortsMixDeepTest.mixDeep_callee,
      ``Tests.Compiler.NoPortsMixDeepTest.mixDeep_three,
      ``Tests.Compiler.NoPortsMixDeepTest.mixDeep_kidOf,
      ``Tests.Compiler.NoPortsMixDeepTest.mixDeep_kids,
      ``Tests.Compiler.NoPortsMixDeepTest.mixDeep_runFacts,
      ``Tests.Compiler.NoPortsMixDeepTest.mixDeep_outsG2,
      ``Tests.Compiler.NoPortsMixDeepTest.mixDeep_maskedG,
      ``Tests.Compiler.NoPortsMixDeepTest.mixDeep_designP2, openN] do
    unless (← Lean.getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (b) the statement mentions no checker constant
  let openT := (← Lean.getConstInfo openN).type
  for k in Tests.Compiler.NoPortsTest.checkers do
    if (openT.find? (·.isConstOf k)).isSome then
      throwError "{openN}: the statement mentions {k}"
  -- (c) the inventory: the base endpoint of this build asks the four check premises
  let oldT := (← Lean.getConstInfo old).type
  for k in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
      ``Tools.ShippingMachineShipsDepth.kidsMaskedN, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck] do
    unless (oldT.find? (·.isConstOf k)).isSome do
      throwError "{old}: does not mention {k} (the inventory is wrong)"
  -- (d) the closing STAYS a premise, and no closed form was added by this file
  unless (openT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome do
    throwError "{openN}: does not ask MachineClosesAt (it is the OPEN form)"
  if (← Lean.getEnv).contains closed then
    throwError "{closed}: exists — this file adds no closed form (see the header)"
  -- (e) the binder counts (LOGGED, not asserted: the base endpoint's count is not measured),
  -- and the last binder IS the reflection of the gate grandchild
  let nOld ← Lean.Meta.forallTelescope oldT fun xs _ => pure xs.size
  let nNew ← Lean.Meta.forallTelescope openT fun xs _ => pure xs.size
  let lastOk ← Lean.Meta.forallTelescope openT fun xs _ => do
    let t ← Lean.instantiateMVars (← Lean.Meta.inferType xs[xs.size - 1]!)
    pure (t.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines &&
      (t.find? fun e => e == Lean.toExpr rc).isSome)
  unless lastOk do
    throwError "{openN}: its last binder is not the reflection of {rc}"
  -- (f) the antecedents under the existentials: exactly one (the boundary)
  let inner ← Lean.Meta.forallTelescope openT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  let innerOld ← Lean.Meta.forallTelescope oldT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  unless inner.size == 1 do
    throwError "{openN}: {inner.size} antecedents under the existentials, expected 1 (the boundary)"
  let same := innerOld.any fun a => a.1 == inner[0]!.1
  -- (g) the complete premise list, with the goal-gap classifier's verdicts (LOGGED, not bounded:
  -- the closing and the boundary are expected among the NOT ALLOWED ones)
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines openN
  Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
  if bad.isEmpty then
    throwError "{openN}: the classifier allows every premise — the header says the closing and the boundary remain (the inventory is wrong)"
  Lean.logInfo m!"NOPORTS MIXDEEP AUDIT {g}: {openN} (OPEN form ONLY) on standard axioms, with GenKid.facts, Tools.ShippingOneOutKidDepth.factsN, Tools.ShippingLeafKidFacts.leafKid_facts, the kids_* theorems and the hand lemmas mixDeep_callee, mixDeep_three, mixDeep_kidOf, mixDeep_kids, mixDeep_runFacts, mixDeep_outsG2, mixDeep_maskedG, mixDeep_designP2. The statement mentions none of portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN, hierCheck, while {old} mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck. {nNew} binders against {nOld}: ADDED the reflection of {rc}. It ASKS MachineClosesAt of {g}: NOT removed, NO closed form, NO reduced boundary, NO gap theorem — {bad.size} premise(s) NOT ALLOWED by the goal-gap classifier (listed above). Under the existentials: 1 antecedent, the boundary; printed the same as an antecedent of {old}: {same}. This is NOT a check-free gap-free endpoint. SCOPE: one declaration at depth 2, OPEN form; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list with the children UNOPTIMISED — not the SV string, not #sim."

import Tests.Compiler.NoPortsGrandHTest
import Tools.ShippingLeafKidFacts
import Tools.ShippingGenKid

/-! # `grand` by hand: the depth-2 endpoint without the four check premises, over a child under the GENERAL closing (G1, unit U3, round par/a-15)

`grand → mid → cnt` (`Tests/Compiler/ShippingMachineSeqTest.lean` 20–69, READ):

    @[hardware_module] def cnt {dom} (en : Signal dom Bool) : CntOut dom := …      -- a register, no call
    @[hardware_module] def mid {dom : DomainConfig} (en : Signal dom Bool) : CntOut dom :=
      circuit do
        let r ← Signal.reg 0#8
        let rs := (r : Signal dom (BitVec 8))
        let k := cnt en          -- CntOut: n : BitVec 8, hit : Bool
        r <~ k.n
        return ({ n := rs, hit := k.hit } : CntOut dom)
    def grand (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
      circuit do
        let r ← Signal.reg 0#8
        let rs := (r : Signal defaultDomain (BitVec 8))
        let m := mid en
        let nz := ((fun c => !(c == 0#8)) <$> m.n : Signal defaultDomain Bool)
        r <~ Signal.mux (m.hit &&& nz) (rs + m.n) rs
        return rs

`#machine_no_ports_kids grand 2` REFUSES (BUILT log, `verification-a14b.md`
104: "the callee …mid has calls of its own under the GENERAL closing
(instFields ≠ []): KidFacts of such a child is not derived (unit U3)").
This file reaches the endpoint BY HAND over the new general theorems

    Tools/ShippingCallsPortsG.lean   core_calls_portsG, core_conn_refsG, outsMaskedN_of_callsG
    Tools/ShippingGenKid.lean        kids_designCheck_in, GenKid, GenKid.core (the bridge), .check, .facts

and the BUILT `leafKid_facts`, `kids_runFacts / _outsCheck / _maskedN /
_designCheck`, `closeDeep`, `dischargeWith`.

## READ vs INFERRED about the data (nothing was run)

READ (sources): the callees; the projected fields (`m.hit`, `m.n` in
`grand`; `k.n`, `k.hit` in `mid`); one register each.
MEASURED (BUILT logs): `mid`: `nDecl = 2`, call entries `[cnt, cnt]`,
`instFields ≠ []`, a slot, outputs `[n, hit]` (`verification-a13.md` 86,
8424); `grand.machine_design_svNR2` exists, mentions the four check
constants, and `grand.closes_deep` has exactly 2 premises, both reflections
(`ShippingCallsCloseDeepTest`: "DEEP CLOSINGS … (2, 2, 3, 3)");
`grand.machine_design_svNR2_closed`'s boundary reduces to `ChildBnd` under
its binders (`verification-a14.md` 146–150: only the four check premises
are KEPT).
INFERRED, and ASSERTED on the reader's data by the first `run_cmd` (which
LOGS the data before it checks): `grand`: `nDecl = 1`, every call entry is
`mid` (the count is NOT assumed: `grand_entry` is one decided ∀-statement),
`instFields ≠ []`, a slot. INFERRED from the generator
(`Tools/ShippingChildIfaceGen.lean` 77–260, READ): `mid.closes_deep` exists
with ONE premise, the reflection of `cnt` (the two premises of
`grand.closes_deep` are then the reflections of `mid` and `cnt`);
`grand.machine_ships_hierNR2` exists and is built from
`machine_ships_hierC` with 25 arguments and 11 binders (as `grandH`'s at
depth 1: the same generator).

## What is proved here (one declaration)

* `mid_kid`: `GenKid mref cref mid mid.machineData 2 midNames (cnt's outs)
  (declWidths cnt) 1` from the reflections of `mid` and `cnt` — the data
  conditions of `mid` decided; `KidNames` of `cnt` by
  `seqChild_of_real … .toD.kid`; `KidFacts` of `cnt` at the depths 1 and 2
  by `leafKid_facts (cnt.machine_leafKid hRc)`; `mid`'s closing in every
  context by `mid.closes_deep`.
* `grand_kids`: `KidFacts mref cref (grand's k-th callee) (mid's outs)
  (argWidths mid.machineData 2) 2` = `(mid_kid …).facts`.
* `grand_runFacts`, `grand_outsG2`, `grand_maskedG`, `grand_designP2`: the
  four run hypotheses of the head at depth 2 (`kids_*`).
* `grand.machine_design_noPortsNR2` (`generateM`: `generateH` with the
  extra binder a MACHINE grandchild's reflection) and
  `grand.machine_design_noPortsNR2_closed` (`closeDeep` over the BUILT
  `grand.closes_deep`).

## EXPECTED (stated before the build; the audit THROWS otherwise)

| endpoint | premise of `grand.machine_design_svNR2` | predicted state |
|---|---|---|
| `grand.machine_design_noPortsNR2` (+ `_closed`) | `shipsHierCheck (childMap D.modules) b` | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `kidsMaskedN D.modules b.body` | predicted absent, pending build |
| | `designCheck (childMap D.modules) 2 (checkedOptimize b)` (incl. `kidsPass`, `portsMatchB`) | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 2 (checkedOptimize b)` | predicted absent, pending build |
| | `MachineClosesAt grand` (open form) | predicted absent in `_closed` (`grand.closes_deep`, BUILT), pending build |
| | the boundary (`ChildBnd`, `MachineDefines mid`, `mid`'s own boundary in the contexts it is synthesised in) | STAYS in this file, unchanged (reduced in `NoPortsGrandBTest`) |
| | `hr`, `MachineDefines grand` | stay |
| | — | ADDED to the open form: `MachineDefines cnt` at the run's contexts (a binder of the base CLOSED endpoint already: a premise of `grand.closes_deep`) |

## SCOPE (binding for any report)

ONE declaration, `grand`: a parent WITH a register, the general closing, one
callee `mid` — a machine with a register whose own calls (of the leaf
register machine `cnt`) are tied by the GENERAL closing — depth 2. Data
conditions decided per declaration by the kernel (for `grand`: `callsOk 1`,
slot lengths, no late domain binder, `insts ≠ []`, `slots ≠ []`,
`instFields ≠ []`, output width / name / scalar, no memory callee,
`callWidthsOk` against `mid`'s layout, `callArgsOk` against `argWidths
mid.machineData 2`; for `mid`: the same at `nDecl = 2` against `cnt`'s
layout and `declWidths cnt.machineData`, the argument split, the name
separation of `mid` from `cnt`; for `cnt`: `cnt.machine_leafKid`) are
conditions, not reductions. The result depends on the compiler's guards
with fallback, including the closings' own check that the merged design
resolves every child module by name to itself. The conclusion is about
`DesignSV (childMap D.modules) 2 (checkedOptimize b)` — the module list
(the children as their entries returned them, UNOPTIMISED), not the SV
string, not `#sim`. The run, the reflections and the boundary stay premises
(no runtime model). NOT covered: `topD2`, `mixDeep`, a generator, "all
successful inputs".

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The shapes this file relies on: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
  let m := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let rg ← Tools.ShippingMachineCommand.readMachine g
  let rm ← Tools.ShippingMachineCommand.readMachine m
  let rc ← Tools.ShippingMachineCommand.readMachine c
  let ge := rg.shape.insts.map (·.1)
  let me := rm.shape.insts.map (·.1)
  Lean.logInfo m!"NOPORTS GRAND DATA {g}: nDecl={rg.nDecl}, call entries {ge}, instFields={rg.shape.instFields}, slots={rg.shape.layout.slots.length}, outputs {rg.shape.layout.outs.map (·.name)}; {m}: nDecl={rm.nDecl}, call entries {me}, instFields={rm.shape.instFields}, slots={rm.shape.layout.slots.length}, outputs {rm.shape.layout.outs.map (·.name)}; {c}: nDecl={rc.nDecl}, call entries {rc.shape.insts.map (·.1)}, slots={rc.shape.layout.slots.length}"
  unless rg.nDecl == 1 do throwError "{g}: nDecl = {rg.nDecl}, the hand theorems are written for 1"
  unless rm.nDecl == 2 do throwError "{m}: nDecl = {rm.nDecl}, the hand theorems are written for 2"
  unless ge.eraseDups == [m] do
    throwError "{g}: the call entries are {ge}, expected every entry to be {m}"
  unless me.eraseDups == [c] do
    throwError "{m}: the call entries are {me}, expected every entry to be {c}"
  if rg.shape.instFields.isEmpty then throwError "{g}: instFields = [] — not the general closing"
  if rm.shape.instFields.isEmpty then throwError "{m}: instFields = [] — not the general closing"
  if rg.shape.layout.slots.isEmpty || rm.shape.layout.slots.isEmpty ||
      rc.shape.layout.slots.isEmpty then
    throwError "{g} / {m} / {c}: no register"
  unless rc.shape.insts.isEmpty do throwError "{c}: has calls — not a leaf"
  for n in [g ++ `closes_deep, m ++ `closes_deep, g ++ `machine_ships_hierNR2,
      g ++ `machine_design_svNR2, c ++ `machine_leafKid, c ++ `machine_closes] do
    unless (← Lean.getEnv).contains n do throwError "{n}: not in the imports (this file builds on it)"
  for n in [g ++ `machine_design_noPortsNR2, g ++ `machine_design_noPortsNR2_closed] do
    if (← Lean.getEnv).contains n then throwError "{n}: exists already"

namespace Tests.Compiler.NoPortsGrandTest
open Tools.ShippingGenKid (GenKid)
open Tools.ShippingKidFacts (KidFacts)
open Tools.ShippingCallsChildPorts (argWidths)

/-- The printed names of the descendants of `mid`'s callees: none (its one
callee is a leaf). -/
def midNames : Nat → List String := fun _ => ([] : List Lean.Name).map fun n => Sparkle.IR.ModuleName.ofDecl n

/-- Every call entry of `mid` is of `cnt` (decided on the reflected data). -/
theorem mid_entry : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData).shape.insts[k]).1 =
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt := by decide

/-- Every call entry of `grand` is of `mid`. -/
theorem grand_entry : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData).shape.insts[k]).1 =
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid := by decide

theorem mid_outChars :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **`mid` as a child**: the interface of a callee under the general
closing, from its reflection and its leaf callee's. -/
theorem mid_kid {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData).shape)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    GenKid mref cref ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid
      Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData 2 midNames
      (fun _ => (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.layout.outs)
      (fun _ => Tools.ShippingPortWidthsPure.declWidths
        Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData) 1 :=
  { ok := Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_ok
    body := Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_body
    calls := by decide
    ss := by decide
    dom := by decide
    insts := fun h0 => absurd (congrArg List.length h0) (by decide)
    general := fun h0 => absurd (congrArg List.length h0) (by decide)
    slots := fun h0 => absurd (congrArg List.length h0) (by decide)
    outTy := by decide
    outName := fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (mid_outChars o ho)
    outScalar := by decide
    nomem := by decide
    hkD := by decide
    hIlen := by decide
    hSL := by decide
    hSlen := by decide
    hLlen := by decide
    hNIn := by decide
    kid := by
      intro k hk y hy
      rw [mid_entry k hk] at hy ⊢
      exact Tools.ShippingCallsKidsD.ChildIfaceD.kid (Tools.ShippingCallsKidsD.ChildIfaceG.toD
        (Tools.ShippingSeqChildIface.seqChild_of_real
          Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData
          Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ok
          Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_body
          rfl (by decide) hRc
          (fun mc cc => Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_closes mc _ cc _)
          hy))
    self := by
      have h : Tools.ShippingKidsChildIface.namesOf
          Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData midNames =
          (Tools.ShippingKidsChildIface.declsOf
            Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData
            (fun _ => ([] : List Lean.Name))).map fun n => Sparkle.IR.ModuleName.ofDecl n :=
        Tools.ShippingKidsChildIface.namesOf_map
          Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData
          (fun _ => ([] : List Lean.Name))
      rw [h]
      exact Tools.ShippingNameSep.Enc.not_mem_map_of _ _ (by decide)
    kidsLo := by
      intro k hk
      rw [mid_entry k hk]
      exact Tools.ShippingLeafKidFacts.leafKid_facts
        (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_leafKid hRc) 1
    kidsHi := by
      intro k hk
      rw [mid_entry k hk]
      exact Tools.ShippingLeafKidFacts.leafKid_facts
        (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_leafKid hRc) 2
    callW := by first | decide | decide +kernel
    callA := by first | decide | decide +kernel
    entry := fun _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx hRm
    closes := fun _ _ => Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.closes_deep
      (Tools.ShippingReflectCtx.MachineDefines.ctx hRc) }

/-- **`KidFacts` of every call entry's callee of `grand`**, two levels of
check below it (`GenKid.facts` at `n = 1`). -/
theorem grand_kids {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData).shape)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    ∀ (k : Nat)
      (hk : k < (Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData).shape.insts.length),
      KidFacts mref cref
        ((Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData).shape.insts[k]).1
        (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData).shape.layout.outs
        (argWidths Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData 2) 2 := by
  intro k hk
  rw [grand_entry k hk]
  exact (mid_kid hRm hRc).facts

/-- The two width conditions of `grand` against `mid`'s data. -/
theorem grand_callWidths : Tools.ShippingCallWidths.callWidthsOk
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData 1
    (fun _ => (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData).shape.layout.outs) =
      true := by
  first | decide | decide +kernel

theorem grand_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData 1
    (fun _ => argWidths Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData 2) =
      true := by
  first | decide | decide +kernel

theorem grand_outChars :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The run's facts of `grand`'s full-entry module** (`kids_runFacts`). -/
theorem grand_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData).shape)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingKidFacts.kids_runFacts (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_ok
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData).shape.layout.outs)
    (fun _ => argWidths Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData 2) 2
    (grand_kids hRm hRc) grand_callWidths
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **The output check at depth 2 under the statement-kind gate**
(`kids_outsCheck`). -/
theorem grand_outsG2 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData).shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData).shape)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFacts.kids_outsCheck (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_ok
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData).shape.layout.outs)
    (fun _ => argWidths Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData 2) 2
    (grand_kids hRm hRc)
    hB hcore hpost entry closes hg

set_option maxHeartbeats 4000000 in
/-- **The children's masked outputs** (`kids_maskedN`). -/
theorem grand_maskedG {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData).shape)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingKidFacts.kids_maskedN (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_ok
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData).shape.layout.outs)
    (fun _ => argWidths Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData 2) 2
    (grand_kids hRm hRc)
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 2 of the shipped module, with no check premise**
(`kids_designCheck`). -/
theorem grand_designP2 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData).shape)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFacts.kids_designCheck (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_ok
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData).shape.layout.outs)
    (fun _ => argWidths Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData 2) 2
    (grand_kids hRm hRc) grand_callWidths grand_callArgs
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (grand_outChars o ho))
    (by decide)

open Lean Meta Elab Command

/-- `Tests.Compiler.NoPortsGrandHTest.generateH`, copied, with ONE change:
the extra binder after those of `f.machine_ships_hierNR{n}` is the
reflection of a MACHINE grandchild `gc` at the run's contexts
(`MachineDefines … gc gc.machineData.shape`) instead of a gate
grandchild's (`EntryDefines … rc rc.gateValue`). -/
def generateM (f gc : Name) (n : Nat) (facts outs masked design : Name) : MetaM Name := do
  let ships := f ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  let name := f ++ Name.mkSimple s!"machine_design_noPortsNR{n}"
  if (← getEnv).contains name then throwError "{name}: exists already"
  let some (.thmInfo ti) := (← getEnv).find? ships
    | throwError "{ships}: not a theorem (run #machine_design_svNR first)"
  let v := ti.value
  unless v.isAppOf ``Tools.ShippingMachineShipsHier.machine_ships_hierC do
    throwError "{ships}: not built from machine_ships_hierC"
  let a := v.getAppArgs
  unless a.size == 25 do throwError "{ships}: {a.size} arguments of machine_ships_hierC, expected 25"
  let value ← forallTelescope (← inferType (mkConst ships)) fun xs _ => do
    unless xs.size == 11 do throwError "{ships}: {xs.size} binders, expected 11"
    let gshape ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[mkConst (gc ++ `machineData)]
    let rT ← mkAppM ``Tools.ShippingMachineEntry.MachineDefines
      #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, toExpr gc, gshape]
    withLocalDeclD `hRc rT fun hRc => do
    let args : Array (Option Lean.Expr) :=
      #[some (mkNatLit n), some a[3]!, some a[4]!, some a[5]!, some a[6]!, some a[7]!,
        some a[8]!, some a[9]!, some a[10]!, some a[11]!,
        some a[12]!, some a[13]!, some a[14]!, some a[15]!, some a[16]!, some a[17]!,
        some a[18]!, some a[19]!, some a[20]!, some a[21]!,
        some a[22]!, some a[23]!, some a[24]!] ++ xs.map some
    let pre ← instantiateMVars
      (← mkAppOptM ``Tools.ShippingNoPorts.machine_design_noPorts args)
    if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
    -- the run's facts: zs = raw D w1 hcore hpost hBnd ; xs[9] = entry, xs[10] = closes
    let .forallE _ TF _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's run-facts hypothesis is not where it is expected"
    let hFacts ← forallTelescope TF fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the run-facts hypothesis has {zs.size} binders"
      let p ← mkAppM facts #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith facts p zs[5]! goal #[hRc])
    let pre := mkApp pre hFacts
    -- the output check under the gate: zs = raw D w1 hcore hpost hg hBnd
    let .forallE _ TO _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallTelescope TO fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      let p ← mkAppM outs #[zs[3]!, zs[4]!, xs[9]!, xs[10]!, zs[5]!]
      mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith outs p zs[6]! goal #[hRc])
    let pre := mkApp pre hOuts
    -- the children's bound: zs = raw D w1 hcore hpost hBnd (cut at 6 binders)
    let .forallE _ TM _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's children-bound hypothesis is not where it is expected"
    let hMasked ← forallBoundedTelescope TM (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the children-bound hypothesis has {zs.size} binders"
      let p ← mkAppM masked #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith masked p zs[5]! goal #[hRc])
    let pre := mkApp pre hMasked
    -- `designCheck` with no check premise: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TD _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's design-check hypothesis is not where it is expected"
    let hDesign ← forallBoundedTelescope TD (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the design-check hypothesis has {zs.size} binders"
      let p ← mkAppM design #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith design p zs[5]! goal #[hRc])
    mkLambdaFVars (xs ++ #[hRc]) (mkApp pre hDesign)
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  for c in Tools.ShippingNoPortsCommand.forbidden do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

end Tests.Compiler.NoPortsGrandTest

/-! ## The endpoint and its closed form -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsGrandTest.generateM g c 2
      ``Tests.Compiler.NoPortsGrandTest.grand_runFacts
      ``Tests.Compiler.NoPortsGrandTest.grand_outsG2
      ``Tests.Compiler.NoPortsGrandTest.grand_maskedG
      ``Tests.Compiler.NoPortsGrandTest.grand_designP2
  let closed := Tools.ShippingMachineClosesGen.closedName name
  Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsGrandHTest.closeDeep g name (g ++ `closes_deep) closed
  Lean.logInfo m!"NOPORTS GRAND [{name}, {closed}]: the depth-2 endpoint of a parent whose child's own calls are tied by the general closing, without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents — by hand (mid_kid: GenKid of the child, KidFacts of its leaf callee at the depths 1 and 2 by leafKid_facts; grand_kids: GenKid.facts; grand_runFacts, grand_outsG2, grand_maskedG, grand_designP2: Tools.ShippingKidFacts.kids_* at depth 2); one binder ADDED against the open base endpoint: the reflection of {c} at the run's contexts"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
  let m := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let old := g ++ `machine_design_svNR2
  let openN := g ++ `machine_design_noPortsNR2
  let closed := g ++ `machine_design_noPortsNR2_closed
  -- (a) standard axioms: the general theorems of this round, the hand lemmas, the endpoints
  for n in [``Tools.ShippingCallsPortsG.core_calls_portsG,
      ``Tools.ShippingCallsPortsG.core_conn_refsG,
      ``Tools.ShippingCallsPortsG.outsMaskedN_of_callsG,
      ``Tools.ShippingGenKid.kids_designCheck_in,
      ``Tools.ShippingGenKid.GenKid.core,
      ``Tools.ShippingGenKid.GenKid.check,
      ``Tools.ShippingGenKid.GenKid.facts,
      ``Tools.ShippingLeafKidFacts.leafKid_facts,
      ``Tools.ShippingKidFacts.kids_runFacts,
      ``Tools.ShippingKidFacts.kids_outsCheck,
      ``Tools.ShippingKidFacts.kids_maskedN,
      ``Tools.ShippingKidFacts.kids_designCheck,
      ``Tests.Compiler.NoPortsGrandTest.mid_kid,
      ``Tests.Compiler.NoPortsGrandTest.grand_kids,
      ``Tests.Compiler.NoPortsGrandTest.grand_runFacts,
      ``Tests.Compiler.NoPortsGrandTest.grand_outsG2,
      ``Tests.Compiler.NoPortsGrandTest.grand_maskedG,
      ``Tests.Compiler.NoPortsGrandTest.grand_designP2, openN, closed] do
    unless (← Lean.getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (b) no endpoint statement mentions a checker constant
  for n in [openN, closed] do
    let ci ← Lean.getConstInfo n
    for k in Tests.Compiler.NoPortsTest.checkers do
      if (ci.type.find? (·.isConstOf k)).isSome then
        throwError "{n}: the statement mentions {k}"
  -- (c) the inventory: the base endpoint of this build asks the four check premises
  let oldT := (← Lean.getConstInfo old).type
  for k in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
      ``Tools.ShippingMachineShipsDepth.kidsMaskedN, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck] do
    unless (oldT.find? (·.isConstOf k)).isSome do
      throwError "{old}: does not mention {k} (the inventory is wrong)"
  -- (d) the closing: asked by the open form, not by the closed one
  let openT := (← Lean.getConstInfo openN).type
  let closedT := (← Lean.getConstInfo closed).type
  unless (openT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome do
    throwError "{openN}: does not ask MachineClosesAt"
  if (closedT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
    throwError "{closed}: still asks MachineClosesAt"
  -- (e) the binders of the closed form: the run, and reflections only — one
  -- each of grand, mid, cnt (MachineDefines)
  let (nProps, refl) ← Lean.Meta.forallTelescope closedT fun xs _ => do
    let mut props : Nat := 0
    let mut refl : List Lean.Name := []
    for x in xs do
      let t ← Lean.instantiateMVars (← Lean.Meta.inferType x)
      if ← Lean.Meta.isProp t then
        props := props + 1
        if t.isAppOf ``Tools.ShippingEntrySoundness.RunsTo then pure ()
        else if t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines ||
            t.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines then
          for k in [g, m, c] do
            if (t.find? fun e => e == Lean.toExpr k).isSome then refl := refl ++ [k]
        else
          throwError "{closed}: a binder that is neither the run nor a reflection:{Lean.indentExpr t}"
    return (props, refl)
  unless nProps == 4 && refl.length == 3 && refl.contains g && refl.contains m &&
      refl.contains c do
    throwError "{closed}: {nProps} proposition binders, reflections of {refl}; expected the run and one reflection each of {g}, {m}, {c}"
  -- (f) the antecedents under the existentials: exactly one (the boundary),
  -- an antecedent of the base endpoint too
  let inner ← Lean.Meta.forallTelescope closedT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  let innerOld ← Lean.Meta.forallTelescope oldT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  unless inner.size == 1 do
    throwError "{closed}: {inner.size} antecedents under the existentials, expected 1 (the boundary)"
  let same := innerOld.any fun a => a.1 == inner[0]!.1
  -- (g) the complete premise list, with the goal-gap classifier's verdicts (LOGGED)
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines closed
  Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
  unless bad.size ≤ 1 do
    throwError "{closed}: {bad.size} premises the classifier does not allow, expected at most the inherited boundary:\n{String.intercalate "\n" bad.toList}"
  Lean.logInfo m!"NOPORTS GRAND AUDIT {g}: {openN} and {closed} on standard axioms, with the general theorems of Tools.ShippingCallsPortsG / ShippingGenKid, Tools.ShippingLeafKidFacts.leafKid_facts, the kids_* theorems and the hand lemmas mid_kid, grand_kids, grand_runFacts, grand_outsG2, grand_maskedG, grand_designP2. No endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while {old} mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck. Closed form: {nProps} proposition binders — the run and the reflections of {refl}; MachineClosesAt asked by the open form only. Under the existentials: 1 antecedent, the boundary; printed the same as an antecedent of {old}: {same}. The goal-gap classifier lists {bad.size} premise(s) NOT ALLOWED in THIS closed form (the inherited boundary; its reduction is NoPortsGrandBTest, not claimed here). ADDED against the open base endpoint: the reflection of {c} at the run's contexts. SCOPE: one declaration, a parent WITH a register under the general closing, one callee with a register whose own calls of a leaf register machine are tied by the general closing, depth 2; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback (including the closings' own design-consistency check); DesignSV of the module list with the children UNOPTIMISED — not the SV string, not #sim. NOT covered: topD2, mixDeep, a generator."

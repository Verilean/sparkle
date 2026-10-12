import Tests.Compiler.NoPortsGrandHTest
import Tools.ShippingGenKid
import Tools.ShippingOneOutKidDepth

/-! # `topD2` by hand: the depth-2 endpoint without the four check premises, over a child under the GENERAL closing whose child has a one-output call (G1, unit U3, round par/a-15)

`topD2 → mid2 → midH → rcH` (`Tests/Compiler/ShippingDesignSVTest.lean` 25–40,
`Tests/Compiler/ShippingMachineDepthHTest.lean` 19–32, READ):

    @[hardware_module] def rcH  {dom} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := …   -- a gate
    @[hardware_module] def midH {dom} (en : Signal dom Bool) : CntOut dom := …   -- a register, y := rcH rs
    @[hardware_module] def mid2 {dom : DomainConfig} (en : Signal dom Bool) : CntOut dom :=
      circuit do
        let r ← Signal.reg 0#8
        let rs := (r : Signal dom (BitVec 8))
        let k := midH en
        r <~ Signal.mux k.hit (rs + k.n) rs
        return ({ n := rs, hit := k.hit } : CntOut dom)
    def topD2 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
      circuit do
        let r ← Signal.reg 0#8
        let rs := (r : Signal defaultDomain (BitVec 8))
        let m := mid2 en
        r <~ Signal.mux m.hit (rs + m.n) rs
        return rs

`#machine_no_ports_kids topD2 2` REFUSES (BUILT log, `verification-a14b.md`
102). This file reaches the endpoint BY HAND:

    Tools/ShippingGenKid.lean           GenKid, GenKid.facts                         (this round)
    Tools/ShippingOneOutKidDepth.lean   factsN : OneOutKid … → KidFacts … (n + 1)    (this round)
    Tests/Compiler/NoPortsGrandHTest    midH_kid, dischargeWith                      (BUILT)

## READ vs INFERRED about the data (nothing was run; NOTHING about `mid2` or `topD2` was measured)

READ (sources): the callees and the projected fields (`m.hit`, `m.n` in
`topD2`; `k.hit`, `k.n` in `mid2`); one register each.
READ (BUILT logs): `topD2.machine_design_svNR2` and `topD2.closes_deep`
exist, the latter with exactly 3 premises, all reflections
(`ShippingCallsCloseDeepTest`); on `topD2.machine_design_svNR2_closed` the
boundary reduces to `ChildBnd` under its binders (`verification-a14.md`
129–133); `midH`: `nDecl = 2`, `midH_kid` built.
INFERRED, ASSERTED on the reader's data by the first `run_cmd` (which LOGS
the data before it checks): `topD2`: `nDecl = 1`, every call entry is
`mid2`; `mid2`: `nDecl = 2` (the signature of `mid`, measured 2), every call
entry is `midH`, `instFields ≠ []`; a slot in each. The entry COUNTS are not
assumed (`topD2_entry`, `mid2_entry`: one decided ∀-statement each).
INFERRED from the generator (`Tools/ShippingChildIfaceGen.lean`, READ):
`mid2.closes_deep` exists with TWO premises, the reflections of `midH` and
`rcH` — the ORDER is not assumed (`first` over both).

## What is proved here (one declaration)

* `mid2_kid`: `GenKid mref cref mid2 mid2.machineData 2 mid2Names (midH's
  outs) (argWidths midH.machineData 2) 1` — `KidNames` of `midH` by
  `kidsChild_of_real` over the fields of `midH_kid`; `KidFacts` of `midH` at
  depth 1 by `OneOutKid.facts` and at depth 2 by
  `Tools.ShippingOneOutKidDepth.factsN`; the closing by `mid2.closes_deep`.
* `topD2_kids`, `topD2_runFacts`, `topD2_outsG2`, `topD2_maskedG`,
  `topD2_designP2` (`kids_*` at depth 2).
* `topD2.machine_design_noPortsNR2` (`generateX`: TWO extra binders, the
  reflections of `midH` and `rcH` at the run's contexts) and its `_closed`
  (`closeDeepX` over the BUILT `topD2.closes_deep`).

## EXPECTED (stated before the build; the audit THROWS otherwise)

| endpoint | premise of `topD2.machine_design_svNR2` | predicted state |
|---|---|---|
| `topD2.machine_design_noPortsNR2` (+ `_closed`) | `shipsHierCheck (childMap D.modules) b` | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `kidsMaskedN D.modules b.body` | predicted absent, pending build |
| | `designCheck (childMap D.modules) 2 (checkedOptimize b)` (incl. `kidsPass`, `portsMatchB`) | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 2 (checkedOptimize b)` | predicted absent, pending build |
| | `MachineClosesAt topD2` (open form) | predicted absent in `_closed` (`topD2.closes_deep`, BUILT), pending build |
| | the boundary | STAYS in this file, unchanged (reduced in `NoPortsTopD2BTest`) |
| | `hr`, `MachineDefines topD2` | stay |
| | — | ADDED to the open form: `MachineDefines midH` and `EntryDefines rcH` at the run's contexts (binders of the base CLOSED endpoint already: premises of `topD2.closes_deep`) |

NOT touched: `topD2.machine_design_svNR3` (the same declaration one depth
higher; it needs `KidFacts mid2 … 3`, i.e. `GenKid` at `n = 2` — the same
theorems, not instantiated here).

## SCOPE (binding for any report)

ONE declaration, `topD2`, at depth 2: a parent WITH a register, the general
closing, one callee `mid2` (a register; its own calls, of `midH`, tied by
the general closing), `midH` a register machine with ONE one-output call of
the GATE `rcH`. Data conditions decided per declaration by the kernel are
conditions, not reductions. The result depends on the compiler's guards with
fallback. The conclusion is about `DesignSV (childMap D.modules) 2
(checkedOptimize b)` — the module list (children UNOPTIMISED), not the SV
string, not `#sim`. The run, the reflections and the boundary stay premises.
NOT covered: `mixDeep`, depth 3, a generator.

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The shapes this file relies on: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
  let m2 := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
  let m := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let rg ← Tools.ShippingMachineCommand.readMachine g
  let r2 ← Tools.ShippingMachineCommand.readMachine m2
  let rm ← Tools.ShippingMachineCommand.readMachine m
  let ge := rg.shape.insts.map (·.1)
  let e2 := r2.shape.insts.map (·.1)
  Lean.logInfo m!"NOPORTS TOPD2 DATA {g}: nDecl={rg.nDecl}, call entries {ge}, instFields={rg.shape.instFields}, slots={rg.shape.layout.slots.length}, outputs {rg.shape.layout.outs.map (·.name)}; {m2}: nDecl={r2.nDecl}, call entries {e2}, instFields={r2.shape.instFields}, slots={r2.shape.layout.slots.length}, outputs {r2.shape.layout.outs.map (·.name)}; {m}: nDecl={rm.nDecl}, call entries {rm.shape.insts.map (·.1)}, instFields={rm.shape.instFields}"
  unless rg.nDecl == 1 do throwError "{g}: nDecl = {rg.nDecl}, the hand theorems are written for 1"
  unless r2.nDecl == 2 do throwError "{m2}: nDecl = {r2.nDecl}, the hand theorems are written for 2"
  unless rm.nDecl == 2 do throwError "{m}: nDecl = {rm.nDecl}, midH_kid is written for 2"
  unless ge.eraseDups == [m2] do
    throwError "{g}: the call entries are {ge}, expected every entry to be {m2}"
  unless e2.eraseDups == [m] do
    throwError "{m2}: the call entries are {e2}, expected every entry to be {m}"
  if rg.shape.instFields.isEmpty then throwError "{g}: instFields = [] — not the general closing"
  if r2.shape.instFields.isEmpty then throwError "{m2}: instFields = [] — not the general closing"
  if rg.shape.layout.slots.isEmpty || r2.shape.layout.slots.isEmpty then
    throwError "{g} / {m2}: no register"
  for n in [g ++ `closes_deep, m2 ++ `closes_deep, g ++ `machine_ships_hierNR2,
      g ++ `machine_design_svNR2, rc ++ `gate_full,
      ``Tests.Compiler.NoPortsGrandHTest.midH_kid] do
    unless (← Lean.getEnv).contains n do throwError "{n}: not in the imports (this file builds on it)"
  for n in [g ++ `machine_design_noPortsNR2, g ++ `machine_design_noPortsNR2_closed] do
    if (← Lean.getEnv).contains n then throwError "{n}: exists already"

namespace Tests.Compiler.NoPortsTopD2Test
open Tools.ShippingGenKid (GenKid)
open Tools.ShippingKidFacts (KidFacts)
open Tools.ShippingCallsChildPorts (argWidths)
open Tests.Compiler.NoPortsGrandHTest (midH_kid midHNames)

/-- The printed names of the descendants of `mid2`'s callees: per entry,
`midH`'s children and their descendants (`declsOf midH …`: `rcH`), printed. -/
noncomputable def mid2Names : Nat → List String := fun _ =>
  (Tools.ShippingKidsChildIface.declsOf
    Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData
    (fun _ => ([] : List Lean.Name))).map fun n => n.toString

/-- Every call entry of `mid2` is of `midH` (decided on the reflected data). -/
theorem mid2_entry : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.insts[k]).1 =
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH := by decide

/-- Every call entry of `topD2` is of `mid2`. -/
theorem topD2_entry : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape.insts[k]).1 =
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 := by decide

theorem mid2_outChars :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

/-- `KidNames` of `midH` as `mid2`'s callee: its interface as a child with
calls (`kidsChild_of_real` over the fields of `midH_kid`), with the printed
names in the form `mid2Names` has. -/
theorem midH_names {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue)
    {y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design}
    (hy : Tools.ShippingChildInv.RealChild mref cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH y) (k : Nat) :
    Tools.ShippingKidsChildIface.KidNames
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH (mid2Names k) y.1 y.2 := by
  have K := midH_kid hRm hRr
  have h0 := Tools.ShippingCallsKidsD.ChildIfaceD.kid
    (Tools.ShippingKidsChildIface.kidsChild_of_real
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData
      K.ok K.body K.calls K.ss K.dom K.insts K.slots K.outTy 2 K.hkD K.hIlen K.hSL K.hSlen
      K.hLlen K.hNIn midHNames K.nomem K.kid K.self (K.entry mctx cctx)
      (fun mc cc _ => K.closes mc cc) hy)
  have h : Tools.ShippingKidsChildIface.namesOf
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData midHNames =
      (Tools.ShippingKidsChildIface.declsOf
        Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData
        (fun _ => ([] : List Lean.Name))).map fun n => n.toString :=
    Tools.ShippingKidsChildIface.namesOf_map
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData
      (fun _ => ([] : List Lean.Name))
  rw [h] at h0
  exact h0

set_option maxHeartbeats 4000000 in
/-- **`mid2` as a child**: the interface of a callee under the general
closing, from its reflection, `midH`'s and `rcH`'s. -/
theorem mid2_kid {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue) :
    GenKid mref cref ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData 2 mid2Names
      (fun _ =>
        (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape.layout.outs)
      (fun _ => argWidths Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData 2)
      1 :=
  { ok := Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machine_ok
    body := Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machine_body
    calls := by decide
    ss := by decide
    dom := by decide
    insts := fun h0 => absurd (congrArg List.length h0) (by decide)
    general := fun h0 => absurd (congrArg List.length h0) (by decide)
    slots := fun h0 => absurd (congrArg List.length h0) (by decide)
    outTy := by decide
    outName := fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (mid2_outChars o ho)
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
      rw [mid2_entry k hk] at hy ⊢
      exact midH_names hRm hRr hy k
    self := by
      have h : Tools.ShippingKidsChildIface.namesOf
          Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData mid2Names =
          (Tools.ShippingKidsChildIface.declsOf
            Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData
            (fun _ => Tools.ShippingKidsChildIface.declsOf
              Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData
              (fun _ => ([] : List Lean.Name)))).map fun n => n.toString :=
        Tools.ShippingKidsChildIface.namesOf_map
          Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData
          (fun _ => Tools.ShippingKidsChildIface.declsOf
            Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData
            (fun _ => ([] : List Lean.Name)))
      rw [h]
      exact Tools.ShippingNameSep.not_mem_map_of _ _ (by first | decide | decide +kernel)
    kidsLo := by
      intro k hk
      rw [mid2_entry k hk]
      exact (midH_kid hRm hRr).facts
    kidsHi := by
      intro k hk
      rw [mid2_entry k hk]
      exact Tools.ShippingOneOutKidDepth.factsN (midH_kid hRm hRr) 1
    callW := by first | decide | decide +kernel
    callA := by first | decide | decide +kernel
    entry := fun _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx hRm2
    closes := fun _ _ => by
      first
        | exact Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.closes_deep
            (Tools.ShippingReflectCtx.MachineDefines.ctx hRm)
            (Tools.ShippingReflectCtx.EntryDefines.ctx hRr)
        | exact Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.closes_deep
            (Tools.ShippingReflectCtx.EntryDefines.ctx hRr)
            (Tools.ShippingReflectCtx.MachineDefines.ctx hRm) }

/-- **`KidFacts` of every call entry's callee of `topD2`**, two levels of
check below it (`GenKid.facts` at `n = 1`). -/
theorem topD2_kids {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue) :
    ∀ (k : Nat)
      (hk : k < (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape.insts.length),
      KidFacts mref cref
        ((Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape.insts[k]).1
        (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.layout.outs
        (argWidths Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData 2) 2 := by
  intro k hk
  rw [topD2_entry k hk]
  exact (mid2_kid hRm2 hRm hRr).facts

/-- The two width conditions of `topD2` against `mid2`'s data. -/
theorem topD2_callWidths : Tools.ShippingCallWidths.callWidthsOk
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData 1
    (fun _ => (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.layout.outs) =
      true := by
  first | decide | decide +kernel

theorem topD2_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData 1
    (fun _ => argWidths Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData 2) =
      true := by
  first | decide | decide +kernel

theorem topD2_outChars :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The run's facts of `topD2`'s full-entry module** (`kids_runFacts`). -/
theorem topD2_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingKidFacts.kids_runFacts (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_ok
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.layout.outs)
    (fun _ => argWidths Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData 2) 2
    (topD2_kids hRm2 hRm hRr) topD2_callWidths
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **The output check at depth 2 under the statement-kind gate**
(`kids_outsCheck`). -/
theorem topD2_outsG2 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFacts.kids_outsCheck (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_ok
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.layout.outs)
    (fun _ => argWidths Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData 2) 2
    (topD2_kids hRm2 hRm hRr)
    hB hcore hpost entry closes hg

set_option maxHeartbeats 4000000 in
/-- **The children's masked outputs** (`kids_maskedN`). -/
theorem topD2_maskedG {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingKidFacts.kids_maskedN (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_ok
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.layout.outs)
    (fun _ => argWidths Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData 2) 2
    (topD2_kids hRm2 hRm hRr)
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 2 of the shipped module, with no check premise**
(`kids_designCheck`). -/
theorem topD2_designP2 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFacts.kids_designCheck (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machineData
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_ok
    Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape.layout.outs)
    (fun _ => argWidths Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData 2) 2
    (topD2_kids hRm2 hRm hRr) topD2_callWidths topD2_callArgs
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (topD2_outChars o ho))
    (by decide)


open Lean Meta Elab Command

/-- `Tests.Compiler.NoPortsGrandHTest.generateH`, copied, with ONE change:
after the binders of `f.machine_ships_hierNR{n}` the endpoint takes SEVERAL
extra binders (`extras`: name and type, the type from the run's four
contexts) — the reflections, at the run's contexts, of the descendants that
are not direct children — which the four run theorems ask besides the
boundary's conjuncts. -/
def generateX (f : Name) (n : Nat)
    (extras : Array Lean.Expr → MetaM (Array (Name × Lean.Expr)))
    (facts outs masked design : Name) : MetaM Name := do
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
    let ex ← extras (xs.extract 0 4)
    let decls : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) :=
      ex.map fun (nm, ty) => (nm, fun _ => pure ty)
    withLocalDeclsD decls fun hEx => do
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
      mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith facts p zs[5]! goal hEx)
    let pre := mkApp pre hFacts
    -- the output check under the gate: zs = raw D w1 hcore hpost hg hBnd
    let .forallE _ TO _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallTelescope TO fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      let p ← mkAppM outs #[zs[3]!, zs[4]!, xs[9]!, xs[10]!, zs[5]!]
      mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith outs p zs[6]! goal hEx)
    let pre := mkApp pre hOuts
    -- the children's bound: zs = raw D w1 hcore hpost hBnd (cut at 6 binders)
    let .forallE _ TM _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's children-bound hypothesis is not where it is expected"
    let hMasked ← forallBoundedTelescope TM (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the children-bound hypothesis has {zs.size} binders"
      let p ← mkAppM masked #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith masked p zs[5]! goal hEx)
    let pre := mkApp pre hMasked
    -- `designCheck` with no check premise: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TD _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's design-check hypothesis is not where it is expected"
    let hDesign ← forallBoundedTelescope TD (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the design-check hypothesis has {zs.size} binders"
      let p ← mkAppM design #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← Tests.Compiler.NoPortsGrandHTest.dischargeWith design p zs[5]! goal hEx)
    mkLambdaFVars (xs ++ hEx) (mkApp pre hDesign)
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  for c in Tools.ShippingNoPortsCommand.forbidden do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

/-- `Tests.Compiler.NoPortsGrandHTest.closeDeep` for an endpoint whose LAST
`k` binders are extra reflections: the endpoint's `MachineClosesAt f` (the
binder before them) is replaced by the premises of `cl` (`f.closes_deep`); a
premise of `cl` that is one of the extra binders is NOT repeated. -/
def closeDeepX (f openN cl closedN : Name) (k : Nat) : MetaM Unit := do
  if (← getEnv).contains closedN then throwError "{closedN}: exists already"
  let info ← getConstInfo openN
  let clT := (← getConstInfo cl).type
  let value ← forallTelescope info.type fun xs _ => do
    let m := xs.size
    unless m ≥ k + 1 do throwError "{openN}: {m} binders"
    let closes := xs[m - 1 - k]!
    let front := xs.extract 0 (m - 1 - k)
    let extras := xs.extract (m - k) m
    let ct ← instantiateMVars (← inferType closes)
    unless ct.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 && ct.getArg! 4 == toExpr f do
      throwError "{openN}: the binder before its last {k} is not MachineClosesAt of {f}:{indentExpr ct}"
    let ctx := ct.getAppArgs.extract 0 4
    forallTelescope (← instantiateForall clT ctx) fun hs goal => do
      unless ← isDefEq goal ct do
        throwError "{cl}: proves{indentExpr goal}\nnot{indentExpr ct}"
      let mut keep : Array Lean.Expr := #[]
      let mut args : Array Lean.Expr := #[]
      for h in hs do
        let ht ← instantiateMVars (← inferType h)
        let mut found : Option Lean.Expr := none
        for e in extras do
          if found.isNone then
            if ← isDefEq ht (← instantiateMVars (← inferType e)) then found := some e
        match found with
        | some e => args := args.push e
        | none =>
          keep := keep.push h
          args := args.push h
      let body := mkAppN (mkConst openN)
        (front ++ #[mkAppN (mkConst cl) (ctx ++ args)] ++ extras)
      mkLambdaFVars (front ++ keep ++ extras) body
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  if (type.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
    throwError "{closedN}: the closed statement still asks MachineClosesAt"
  for c in Tools.ShippingNoPortsCommand.forbidden do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{closedN}: REFUSED, the statement mentions {c}"
  Tools.ShippingMachineLinkedCommand.addTheorem closedN type value

end Tests.Compiler.NoPortsTopD2Test

/-! ## The endpoint and its closed form -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
  let m := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let extras (ctx : Array Lean.Expr) : Lean.Meta.MetaM (Array (Lean.Name × Lean.Expr)) := do
    let mshape ← Lean.Meta.mkAppM ``Tools.ShippingMachineAuto.MachineData.shape
      #[Lean.mkConst (m ++ `machineData)]
    let tM ← Lean.Meta.mkAppM ``Tools.ShippingMachineEntry.MachineDefines
      (ctx ++ #[Lean.toExpr m, mshape])
    let tR ← Lean.Meta.mkAppM ``Tools.ShippingInlineSoundness.EntryDefines
      (ctx ++ #[Lean.toExpr rc, Lean.mkConst (rc ++ `gateValue)])
    return #[(`hRm, tM), (`hRr, tR)]
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsTopD2Test.generateX g 2 extras
      ``Tests.Compiler.NoPortsTopD2Test.topD2_runFacts
      ``Tests.Compiler.NoPortsTopD2Test.topD2_outsG2
      ``Tests.Compiler.NoPortsTopD2Test.topD2_maskedG
      ``Tests.Compiler.NoPortsTopD2Test.topD2_designP2
  let closed := Tools.ShippingMachineClosesGen.closedName name
  Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsTopD2Test.closeDeepX g name (g ++ `closes_deep) closed 2
  Lean.logInfo m!"NOPORTS TOPD2 [{name}, {closed}]: the depth-2 endpoint of a parent whose child (general closing) has a child with a one-output call of a gate, without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents — by hand (mid2_kid: GenKid; KidFacts of midH at depth 1 by OneOutKid.facts and at depth 2 by Tools.ShippingOneOutKidDepth.factsN; topD2_kids: GenKid.facts; topD2_runFacts, topD2_outsG2, topD2_maskedG, topD2_designP2: Tools.ShippingKidFacts.kids_* at depth 2); two binders ADDED against the open base endpoint: the reflections of {m} and {rc} at the run's contexts"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2
  let m2 := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
  let m := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let old := g ++ `machine_design_svNR2
  let openN := g ++ `machine_design_noPortsNR2
  let closed := g ++ `machine_design_noPortsNR2_closed
  -- (a) standard axioms
  for n in [``Tools.ShippingCallsPortsG.core_calls_portsG,
      ``Tools.ShippingCallsPortsG.core_conn_refsG,
      ``Tools.ShippingCallsPortsG.outsMaskedN_of_callsG,
      ``Tools.ShippingGenKid.kids_designCheck_in,
      ``Tools.ShippingGenKid.GenKid.core,
      ``Tools.ShippingGenKid.GenKid.check,
      ``Tools.ShippingGenKid.GenKid.facts,
      ``Tools.ShippingOneOutKidDepth.core_designCheck_inN₁,
      ``Tools.ShippingOneOutKidDepth.checkN,
      ``Tools.ShippingOneOutKidDepth.factsN,
      ``Tools.ShippingOneOutKid.OneOutKid.facts,
      ``Tools.ShippingKidFacts.kids_runFacts,
      ``Tools.ShippingKidFacts.kids_outsCheck,
      ``Tools.ShippingKidFacts.kids_maskedN,
      ``Tools.ShippingKidFacts.kids_designCheck,
      ``Tests.Compiler.NoPortsTopD2Test.midH_names,
      ``Tests.Compiler.NoPortsTopD2Test.mid2_kid,
      ``Tests.Compiler.NoPortsTopD2Test.topD2_kids,
      ``Tests.Compiler.NoPortsTopD2Test.topD2_runFacts,
      ``Tests.Compiler.NoPortsTopD2Test.topD2_outsG2,
      ``Tests.Compiler.NoPortsTopD2Test.topD2_maskedG,
      ``Tests.Compiler.NoPortsTopD2Test.topD2_designP2, openN, closed] do
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
  -- each of topD2, mid2, midH (MachineDefines) and rcH (EntryDefines)
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
          for k in [g, m2, m, rc] do
            if (t.find? fun e => e == Lean.toExpr k).isSome then refl := refl ++ [k]
        else
          throwError "{closed}: a binder that is neither the run nor a reflection:{Lean.indentExpr t}"
    return (props, refl)
  unless nProps == 5 && refl.length == 4 && refl.contains g && refl.contains m2 &&
      refl.contains m && refl.contains rc do
    throwError "{closed}: {nProps} proposition binders, reflections of {refl}; expected the run and one reflection each of {g}, {m2}, {m}, {rc}"
  -- (f) the antecedents under the existentials: exactly one (the boundary)
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
  Lean.logInfo m!"NOPORTS TOPD2 AUDIT {g}: {openN} and {closed} on standard axioms, with the general theorems of Tools.ShippingCallsPortsG / ShippingGenKid / ShippingOneOutKidDepth, OneOutKid.facts, the kids_* theorems and the hand lemmas midH_names, mid2_kid, topD2_kids, topD2_runFacts, topD2_outsG2, topD2_maskedG, topD2_designP2. No endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while {old} mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck. Closed form: {nProps} proposition binders — the run and the reflections of {refl}; MachineClosesAt asked by the open form only. Under the existentials: 1 antecedent, the boundary; printed the same as an antecedent of {old}: {same}. The goal-gap classifier lists {bad.size} premise(s) NOT ALLOWED in THIS closed form (the inherited boundary; its reduction is NoPortsTopD2BTest, not claimed here). ADDED against the open base endpoint: the reflections of {m} and {rc} at the run's contexts. SCOPE: one declaration at depth 2 (NOT its depth-3 endpoint), a parent WITH a register under the general closing, one callee under the general closing whose callee is a register machine with a one-output call of a gate; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list with the children UNOPTIMISED — not the SV string, not #sim. NOT covered: mixDeep, depth 3, a generator."

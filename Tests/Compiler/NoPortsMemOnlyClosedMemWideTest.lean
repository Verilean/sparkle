import Tests.Compiler.NoPortsMemOnlyAtMemWideTest
import Tests.Compiler.NoPortsMemOnlyClosedLib

/-! # `memWide`: the closing of a MEMORY-ONLY parent, and the closed depth-0 endpoint (round par/a-19)

`memWide`: a `Signal.loop` parent with two register slots and ONE combinational-read memory (aw 6, dw 16).
`memWide.machine_design_noPortsR0` (`NoPortsMemOnlyAtMemWideTest`, BUILT at
4bd77170) has `MachineClosesAt memWide` as its last binder (the one premise NOT
ALLOWED). This file derives it with NO premise:

    memWide_closes : MachineClosesAt mctx mref cctx cref `memWide memWide.machineData.shape

by `Tools.ShippingMemOnlyCloses.machineClosesAt_of_memOnlyData` (the general
`machineClosesAt_memOnly` over the BUILT `memWide_data : MemOnlyData …`), a
corollary of `machineClosesAt_of_kidsDM` with the child interface discharged
by `memKid_iface`. A memory child has no reflection.

## The hypotheses on `memWide`'s data — evaluated BY HAND (nothing was run)

MEASURED (`docs/parallel/B-memkids.md` §8.1, run 20261013-055644-b13b-alltests):
nDecl=3, call entries `[SparkleMem.combo.6.16]`, argument lets `[[1,2,3,0]]`,
instFields=`[out]`, slots=2, lets=4. The module's name
`SparkleMem_combo_6_16` is READ (`Sparkle/Compiler/MachMemory.lean` 47).

| hypothesis | evaluation | verdict |
|---|---|---|
| `hmem` (→ `hkid` by `memKid_iface`) | every entry is `SparkleMem.combo.6.16` (`memWide_entry`, BUILT); its child is the built module (`mem_isMem`, BUILT); `memIface` BUILT | TRUE |
| `hargsN` | every argument list has 4 elements | TRUE (measured); DECIDED |
| `hfield` (→ `hfieldOut`) | every field is `out` | TRUE (measured); DECIDED |
| `hargsNd` (→ `hfieldsNd`) | one entry: the antecedents force `k = k'` | TRUE (measured); DECIDED |
| `hsep` | all entries are of ONE placeholder: the conclusion holds whatever the names (`sep_of_one`) | TRUE |
| `hparent` | `memWide` does not print as `SparkleMem_combo_6_16`: every candidate rendering of a five-component name contains `.` | TRUE; DECIDED over `Tools.ShippingNameSep.cands` |
| `hout` (→ `hfresh`) | the output's name was NOT read; LOGGED by the first command, which throws if it starts with `i` | NOT READ; DECIDED (`memWide_outHead`) |
| `hparentD` | derived from `hparent` in the general theorem | TRUE |
| `hdisjD` | derived from `hsep`; no two entries of different callees: vacuous | TRUE |
| `hpair` | not a hypothesis (proved inside `machineClosesAt_of_kidsDM` from `closeInstsGM_run_allM`) | — |
| `halias` | every `let` is a declaration input, a slot projection or a constant: a variable at a position `< nIn + slots` or no variable (`aliasOk`, `Tools/ShippingMachineClosesData.lean` 129–136) | TRUE by reading; DECIDED (`memWide_alias`) — never evaluated before for `memWide` |
| `ok`, `hbody`, `hC`, `hslots`, `hdomB`, `hfne` | fields of the BUILT `memWide_data` | BUILT |

## EXPECTED (stated before the build; the audit THROWS otherwise)

There is NO base closed endpoint for this parent: the closed endpoint is a
NEW statement (`Tests/Compiler/NoPortsMemOnlyClosedLib.lean`).

| endpoint | premise | predicted state |
|---|---|---|
| `memWide.machine_design_noPortsR0_closed` | `MachineClosesAt memWide` (last binder of `…_noPortsR0`, NOT ALLOWED) | WRITTEN, NOT BUILT — predicted ABSENT, pending build |
| | binder added | NONE (`memWide_closes` has no premise) |
| | the run, `MachineDefines memWide` | stay |
| | antecedent `ChildBnd mref cref w` (allowed) | stays |
| | against `memWide.machine_design_sv0`: `shipsHierCheck`, `kidsMem`, `designCheck 0`, `outsCheck 0` | absent (already in the open form, BUILT) |
| | against `memWide.machine_design_sv0`: boundary `True` | `ChildBnd` (ADDED) |
| | against `memWide.machine_design_sv0`: all-worlds `MachineCloses memWide` | none |
| `…_closed_gap` | gap hypotheses | predicted NONE; premise listing 0 NOT ALLOWED |

SCOPE: one declaration, depth 0, data conditions decided per declaration
(conditions, not reductions), compiler guards with fallback, `DesignSV` of
the module list — not the SV string, not `#sim`. The run, the reflection of
`memWide` and `ChildBnd` at the start world remain premises.

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The data this file relies on: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemOnlyClosed.logData
    ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
    [Sparkle.Compiler.MachMemory.memChildName true 6 16]

namespace Tests.Compiler.NoPortsMemOnlyClosedMemWideTest

/-! ## The data conditions of the closing (decided on the reflected data) -/

theorem memWide_alias :
    (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).letsAliasOk = true := by
  first | decide | decide +kernel

theorem memWide_argsN : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.insts[k]).2.1.length = 4 := by
  first | decide | decide +kernel

theorem memWide_field : ∀ (k : Nat),
    k < (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.insts.length →
    (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.instFields.getD k "" = "out" := by
  first | decide | decide +kernel

theorem memWide_argsNd : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.insts.length)
    (k' : Nat)
    (hk' : k' < (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.insts[k]).1 =
      ((Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.insts[k']).1 →
    ((Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.insts[k]).2.1 =
      ((Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.insts[k']).2.1 →
    k = k' := by
  first | decide | decide +kernel

theorem memWide_outHead :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape.layout.outs,
      o.name.toList.head? ≠ some 'i' := by
  first | decide | decide +kernel

/-- **The data conditions of the closing of `memWide`**. -/
theorem memWide_closeData : Tools.ShippingMemOnlyCloses.MemOnlyCloseData
    Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData :=
  Tools.ShippingMemOnlyCloses.MemOnlyCloseData.mk memWide_alias memWide_argsN memWide_field
    memWide_argsNd memWide_outHead

/-! ## Names (decided over the candidate renderings; `Name.toString` is never evaluated) -/

/-- `memWide` does not print as the memory module's name. -/
theorem memWide_notin :
    (``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide : Lean.Name).toString ∉
      [(Sparkle.Compiler.MachMemory.memModule true 6 16).1.name] :=
  Tools.ShippingNameSep.not_mem_of _ _ (by first | decide | decide +kernel)

/-! ## The closing -/

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAt memWide`** — a memory-only parent, from decided reader
data only: NO premise. -/
theorem memWide_closes {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
      (Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machineData).shape :=
  Tools.ShippingMemOnlyCloses.machineClosesAt_of_memOnlyData
    Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_data memWide_closeData
    (Tools.ShippingMemOnlyCloses.sep_of_one Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_entry)
    (Tools.ShippingMemOnlyCloses.parent_of_one Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_entry
      Tests.Compiler.NoPortsMemOnlyAtMemWideTest.mem_isMem memWide_notin)

end Tests.Compiler.NoPortsMemOnlyClosedMemWideTest

/-! ## The closed endpoint -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
  let closed ← Tests.Compiler.NoPortsMemOnlyClosed.closeIt f
    ``Tests.Compiler.NoPortsMemOnlyClosedMemWideTest.memWide_closes
  Lean.logInfo m!"MEMONLY CLOSED [{closed}]: {f}.machine_design_noPortsR0 with its binder MachineClosesAt {f} discharged by memWide_closes (NO premise) — the closing of a memory-only parent, by Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly over Tools.ShippingMemCloses.machineClosesAt_of_kidsDM"

/-! ## The goal gap -/

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide.machine_design_noPortsR0_closed

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemOnlyClosed.auditClosed
    ``Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide
    ``Tests.Compiler.NoPortsMemOnlyClosedMemWideTest.memWide_closes
    [``Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_entry,
     ``Tests.Compiler.NoPortsMemOnlyAtMemWideTest.memWide_data,
     ``Tests.Compiler.NoPortsMemOnlyClosedMemWideTest.memWide_alias,
     ``Tests.Compiler.NoPortsMemOnlyClosedMemWideTest.memWide_argsN,
     ``Tests.Compiler.NoPortsMemOnlyClosedMemWideTest.memWide_field,
     ``Tests.Compiler.NoPortsMemOnlyClosedMemWideTest.memWide_argsNd,
     ``Tests.Compiler.NoPortsMemOnlyClosedMemWideTest.memWide_outHead,
     ``Tests.Compiler.NoPortsMemOnlyClosedMemWideTest.memWide_closeData,
     ``Tests.Compiler.NoPortsMemOnlyClosedMemWideTest.memWide_notin]

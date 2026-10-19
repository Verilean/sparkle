import Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest
import Tests.Compiler.NoPortsMemOnlyClosedLib
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # `mixedMems`: the closing of a MEMORY-ONLY parent with TWO DIFFERENT memory modules, and the closed depth-0 endpoint (round par/a-19)

`mixedMems`: a `Signal.loop` parent with two register slots, a
combinational-read memory and a synchronous-read memory of the SAME widths
(aw 4, dw 8) — two different placeholders, two different modules
(`SparkleMem_combo_4_8`, `SparkleMem_sync_4_8`).
`mixedMems.machine_design_noPortsR0` (`NoPortsMemOnlyAtMixedMemsTest`, BUILT
at 4bd77170) has `MachineClosesAt mixedMems` as its last binder (the one
premise NOT ALLOWED). This file derives it with NO premise:

    mixedMems_closes : MachineClosesAt mctx mref cctx cref `mixedMems mixedMems.machineData.shape

by `Tools.ShippingMemOnlyCloses.machineClosesAt_of_memOnlyData` over the
BUILT `mixedMems_data : MemOnlyData … 3 4 8`.

## The hypotheses on `mixedMems`'s data — evaluated BY HAND (nothing was run)

MEASURED (`docs/parallel/B-memkids.md` §8.1, run 20261013-055644-b13b-alltests):
nDecl=3, call entries `[SparkleMem.combo.4.8, SparkleMem.sync.4.8]`, argument
lets `[[1,2,3,0],[1,4,3,0]]`, instFields=`[out, out]`, slots=2, lets=5. The
modules' names are READ (`Sparkle/Compiler/MachMemory.lean` 47).

| hypothesis | evaluation | verdict |
|---|---|---|
| `hmem` (→ `hkid` by `memKid_iface`) | every entry is one of the two placeholders (`mixedMems_entry`, BUILT); their children are the built modules (`mem_isMemC`, `mem_isMemS`, BUILT) | TRUE |
| `hargsN` | both argument lists have 4 elements | TRUE (measured); DECIDED |
| `hfield` (→ `hfieldOut`) | both fields are `out` | TRUE (measured); DECIDED |
| `hargsNd` (→ `hfieldsNd`) | the two entries have ONE field name `out` but DIFFERENT callees: the antecedent "one callee" is false for `k ≠ k'`. `hfieldsNd` is NOT `Nodup` of the field names (that would be FALSE here) | TRUE (measured); DECIDED |
| `hsep` | `SparkleMem_combo_4_8 ≠ SparkleMem_sync_4_8` (`names_ne`): equal module names only for equal entries' callees | TRUE; DECIDED (a string comparison) |
| `hparent` | `mixedMems` prints as neither module name: every candidate rendering of a five-component name contains `.` | TRUE; DECIDED over `Tools.ShippingNameSep.cands` |
| `hout` (→ `hfresh`) | the output's name was NOT read; LOGGED by the first command, which throws if it starts with `i` | NOT READ; DECIDED (`mixedMems_outHead`) |
| `hparentD` | derived from `hparent` in the general theorem | TRUE |
| `hdisjD` | derived from `hsep`: (combo, sync) `SparkleMem_combo_4_8 ∉ [SparkleMem_sync_4_8]`, and `∀ x ∈ [SparkleMem_combo_4_8], x ∉ [SparkleMem_sync_4_8]`; (sync, combo) the same with the names exchanged — each memory module's design is the module itself, no shared module | TRUE |
| `hpair` | not a hypothesis (proved inside `machineClosesAt_of_kidsDM`); here no two entries have one callee | — |
| `halias` | the `let`s are `addr` (a slot projection), `wa`, `wd`, `we` (declaration inputs) and `Signal.snd st` (a slot projection): a variable at a position `< nIn + slots` or no variable | TRUE by reading; DECIDED (`mixedMems_alias`) — never evaluated before for `mixedMems` |
| `ok`, `hbody`, `hC`, `hslots`, `hdomB`, `hfne` | fields of the BUILT `mixedMems_data` | BUILT |

## EXPECTED (stated before the build; the audit THROWS otherwise)

There is NO base closed endpoint for this parent: the closed endpoint is a
NEW statement (`Tests/Compiler/NoPortsMemOnlyClosedLib.lean`).

| endpoint | premise | predicted state |
|---|---|---|
| `mixedMems.machine_design_noPortsR0_closed` | `MachineClosesAt mixedMems` (last binder of `…_noPortsR0`, NOT ALLOWED) | WRITTEN, NOT BUILT — predicted ABSENT, pending build |
| | binder added | NONE (`mixedMems_closes` has no premise) |
| | the run, `MachineDefines mixedMems` | stay |
| | antecedent `ChildBnd mref cref w` (allowed) | stays |
| | against `mixedMems.machine_design_sv0`: `shipsHierCheck`, `kidsMem`, `designCheck 0`, `outsCheck 0` | absent (already in the open form, BUILT) |
| | against `mixedMems.machine_design_sv0`: boundary `True` | `ChildBnd` (ADDED) |
| | against `mixedMems.machine_design_sv0`: all-worlds `MachineCloses mixedMems` | none |
| `…_closed_gap` | gap hypotheses | predicted NONE; premise listing 0 NOT ALLOWED |

SCOPE: one declaration, depth 0, data conditions decided per declaration
(conditions, not reductions), compiler guards with fallback, `DesignSV` of
the module list — not the SV string, not `#sim`. The run, the reflection of
`mixedMems` and `ChildBnd` at the start world remain premises.

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The data this file relies on: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemOnlyClosed.logData
    ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
    [Sparkle.Compiler.MachMemory.memChildName true 4 8,
     Sparkle.Compiler.MachMemory.memChildName false 4 8]

namespace Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest
open Tools.ShippingMemOnlyCloses (memNameAt memNameAt_eq)
open Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest (mem_isMemC mem_isMemS mixedMems_entry
  mixedMems_data)

/-- The name of the combinational-read module (`SparkleMem_combo_4_8`). -/
abbrev nameC : String := (Sparkle.Compiler.MachMemory.memModule true 4 8).1.name

/-- The name of the synchronous-read module (`SparkleMem_sync_4_8`). -/
abbrev nameS : String := (Sparkle.Compiler.MachMemory.memModule false 4 8).1.name

/-! ## The data conditions of the closing (decided on the reflected data) -/

theorem mixedMems_alias :
    (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).letsAliasOk =
      true := by
  first | decide | decide +kernel

theorem mixedMems_argsN : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts[k]).2.1.length = 4 := by
  first | decide | decide +kernel

theorem mixedMems_field : ∀ (k : Nat),
    k < (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts.length →
    (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.instFields.getD k "" = "out" := by
  first | decide | decide +kernel

theorem mixedMems_argsNd : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts.length)
    (k' : Nat)
    (hk' : k' < (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts[k]).1 =
      ((Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts[k']).1 →
    ((Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts[k]).2.1 =
      ((Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts[k']).2.1 →
    k = k' := by
  first | decide | decide +kernel

theorem mixedMems_outHead :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.layout.outs,
      o.name.toList.head? ≠ some 'i' := by
  first | decide | decide +kernel

/-- **The data conditions of the closing of `mixedMems`**. -/
theorem mixedMems_closeData : Tools.ShippingMemOnlyCloses.MemOnlyCloseData
    Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData :=
  Tools.ShippingMemOnlyCloses.MemOnlyCloseData.mk mixedMems_alias mixedMems_argsN mixedMems_field
    mixedMems_argsNd mixedMems_outHead
    (by first | decide | decide +kernel)

/-! ## Names -/

/-- The two memory modules have different names (a string comparison). -/
theorem names_ne : nameC ≠ nameS := by
  first | decide | decide +kernel

/-- `mixedMems` does not print as the combinational-read module's name. -/
theorem mixedMems_notinC :
    (Sparkle.IR.ModuleName.ofDecl (``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems : Lean.Name)) ∉
      [nameC] :=
  (by name_not_mem)

/-- `mixedMems` does not print as the synchronous-read module's name. -/
theorem mixedMems_notinS :
    (Sparkle.IR.ModuleName.ofDecl (``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems : Lean.Name)) ∉
      [nameS] :=
  (by name_not_mem)

/-- The module name of a combinational entry. -/
theorem mixedMems_atC (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts.length)
    (h : ((Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts[k]).1 =
      Sparkle.Compiler.MachMemory.memChildName true 4 8) :
    memNameAt Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData k =
      nameC :=
  memNameAt_eq Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData hk
    ((congrArg Sparkle.Compiler.MachMemory.memChild? h).trans mem_isMemC)

/-- The module name of a synchronous entry. -/
theorem mixedMems_atS (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts.length)
    (h : ((Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts[k]).1 =
      Sparkle.Compiler.MachMemory.memChildName false 4 8) :
    memNameAt Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData k =
      nameS :=
  memNameAt_eq Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData hk
    ((congrArg Sparkle.Compiler.MachMemory.memChild? h).trans mem_isMemS)

/-- Two entries with one module name have one callee. -/
theorem mixedMems_sep : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts.length)
    (k' : Nat)
    (hk' : k' < (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts.length),
    memNameAt Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData k =
      memNameAt Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData k' →
    ((Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts[k]).1 =
      ((Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts[k']).1 := by
  intro k hk k' hk' he
  rcases mixedMems_entry k hk with h | h
  · rcases mixedMems_entry k' hk' with h' | h'
    · exact h.trans h'.symm
    · exact absurd ((mixedMems_atC k hk h).symm.trans (he.trans (mixedMems_atS k' hk' h')))
        names_ne
  · rcases mixedMems_entry k' hk' with h' | h'
    · exact absurd ((mixedMems_atC k' hk' h').symm.trans (he.symm.trans (mixedMems_atS k hk h)))
        names_ne
    · exact h.trans h'.symm

/-- No memory module is named as the parent. -/
theorem mixedMems_parent : ∀ (k : Nat),
    k < (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape.insts.length →
    memNameAt Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData k ≠
      (Sparkle.IR.ModuleName.ofDecl (``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems : Lean.Name)) := by
  intro k hk e
  rcases mixedMems_entry k hk with h | h
  · exact mixedMems_notinC
      (List.mem_singleton.mpr (((mixedMems_atC k hk h).symm.trans e).symm))
  · exact mixedMems_notinS
      (List.mem_singleton.mpr (((mixedMems_atS k hk h).symm.trans e).symm))

/-! ## The closing -/

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAt mixedMems`** — a memory-only parent with two different
memory modules, from decided reader data only: NO premise. -/
theorem mixedMems_closes {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape :=
  Tools.ShippingMemOnlyCloses.machineClosesAt_of_memOnlyData
    mixedMems_data mixedMems_closeData mixedMems_sep mixedMems_parent

end Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest

/-! ## The closed endpoint -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
  let closed ← Tests.Compiler.NoPortsMemOnlyClosed.closeIt f
    ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_closes
  Lean.logInfo m!"MEMONLY CLOSED [{closed}]: {f}.machine_design_noPortsR0 with its binder MachineClosesAt {f} discharged by mixedMems_closes (NO premise) — the closing of a memory-only parent with two different memory modules, by Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly over Tools.ShippingMemCloses.machineClosesAt_of_kidsDM"

/-! ## The goal gap -/

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machine_design_noPortsR0_closed

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemOnlyClosed.auditClosed
    ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
    ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_closes
    [``Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest.mixedMems_entry,
     ``Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest.mixedMems_data,
     ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_alias,
     ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_argsN,
     ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_field,
     ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_argsNd,
     ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_outHead,
     ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_closeData,
     ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_notinC,
     ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_notinS,
     ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.names_ne,
     ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_sep,
     ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_parent]

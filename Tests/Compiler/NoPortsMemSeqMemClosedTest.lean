import Tests.Compiler.NoPortsMemSeqMemTest
import Tools.ShippingMemClosesKids
import Tools.ShippingBoundaryClose
import Tools.ShippingNameSep
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # `seqMem`: the closing of a parent with a MEMORY child, and the closed check-free endpoint (round par/a-18)

`seqMem.machine_design_noPortsR0` (`NoPortsMemSeqMemTest`, BUILT at 9f279734)
has `MachineClosesAt seqMem` as a binder (classified NOT ALLOWED). This file
derives it:

    seqMem_closes : MachineDefines … cnt cnt.machineData.shape →
                    MachineClosesAt mctx mref cctx cref `seqMem seqMem.machineData.shape

by `Tools.ShippingMemCloses.machineClosesAt_of_kidsDM` (M2) over
`closeInstsGM_run_allM` (M1): the children are `Kid`s — `cnt` a real child
(interface from `cnt.machine_leafKid` through `seqChild_of_real`,
`ChildIfaceG.toD`, `ChildIfaceD.toP`), the memory placeholder the built
module (`memKid_iface`). A memory child has no reflection: the ONLY premise
is the reflection of `cnt`.

## The hypotheses of M2 on `seqMem`'s data — evaluated BY HAND (nothing was run)

Data READ: source (`ShippingChildBoundaryTest` 52–60); the built log
`NOPORTS MEM DATA … nDecl=3, binders=10, call entries [cnt, …`
(`verification-b13.md` 80, cut after the first entry). INFERRED: three call
entries (`k.hit`, `k.n` of `cnt`, `rd` of the memory: one per projected
field), one slot, three `let`s (`en`, `wa`, `wd` — copies are one). The
tables below are keyed by the CALLEE (`calleeAt`), so no entry order or count
is assumed; `seqMem_entry` (BUILT) says every entry is `cnt` or
`memChildName true 4 8`.

| hypothesis | at `cnt` entries | at the memory entry | verdict |
|---|---|---|---|
| `hkid` (`ChildIfaceP`) | `name`: the module is named `cnt.toString` (`ChildIfaceG.name`, BUILT); `memOk`: `memParams? = none` (`memParams_none_of_seqOk`); `self`, `closed`, `desNames`: its design has no module (`ChildIfaceG.design`), `names = []` | `name`: `rfl`; `memOk`: `isMemModule cb aw dw (memModule cb aw dw).1` (`isMemModule_memModule`, WRITTEN: a `simp`); `self`: the design is `[itself]`; `closed`: no instance in the body (`mem_noInst`, BUILT); `names = [SparkleMem_combo_4_8]` | TRUE |
| `hargsN` | `cnt`'s non-domain declaration binders: 1 (`en`); the call `cnt en`: 1 argument `let` | 4 = the four operand `let`s (`Elab.lean` 4042–4069) | TRUE by reading; DECIDED by the kernel |
| `hfieldOut` | `hit`, `n` ∈ `cnt`'s output names | `"out"` ∈ `["out"]` (`Elab.lean` 4069) | TRUE by reading; DECIDED |
| `hfieldsNd` | the two `cnt` entries have fields `hit` ≠ `n` | one entry | TRUE by reading; DECIDED |
| `hsep` (module names) | `cnt.toString` vs `SparkleMem_combo_4_8`: no candidate rendering of `cnt` (five string components, each as itself or `«…»`, joined by `.`) is that string — it has no `.` | — | TRUE; DECIDED over `Tools.ShippingNameSep.cands` |
| `hparent` | `cnt` and `seqMem` print differently (`sep`: last components differ) | `seqMem.toString` is not `SparkleMem_combo_4_8` (candidates contain `.`) | TRUE; DECIDED |
| `hfresh` | the parent's output names do not start with `i` (one scalar result; its name is LOGGED by the first command, which throws if it starts with `i`) | same | NOT READ (the name); DECIDED — a failure is an error of `seqMem_outHead` |
| `hparentD` | `names = []` | `seqMem.toString ∉ [SparkleMem_combo_4_8]` | TRUE; DECIDED |
| `hdisjD` | (`cnt`, memory): `cnt.toString ∉ [SparkleMem_combo_4_8]`; `∀ x ∈ []` | (memory, `cnt`): `… ∉ []`; `∀ x ∈ [SparkleMem_combo_4_8], x ∉ []` | TRUE (no shared descendant: `cnt` is a leaf, the memory's design is itself) |
| `halias` | every `let` (`en`, `wa`, `wd`) is a declaration input: `varPos? < base` | — | TRUE by reading `aliasOk`; DECIDED |
| `hC`, `hslots`, `hdomB`, `hfne` | DECIDED in the BUILT `NoPortsMemSeqMemTest` (`callsOk 3`, slots, late binders, `instFields ≠ []`) | | BUILT |

NOT asked any more (they are FALSE of a memory entry): `hnomem`,
`ChildIfaceD.name` (`SparkleMem_combo_4_8` ≠ `SparkleMem.combo.4.8`),
`ChildIfaceD.noMem`, `hselfD` (the module is in its own design).

## EXPECTED (stated before the build; the audit THROWS otherwise)

| endpoint | premise | predicted state |
|---|---|---|
| `seqMem.machine_design_noPortsR0_closed` | `MachineClosesAt seqMem` (binder of `…_noPortsR0`, NOT ALLOWED) | WRITTEN, NOT BUILT — predicted ABSENT, pending build |
| | binder ADDED: `MachineDefines … cnt cnt.machineData.shape` (allowed) | predicted present |
| | the run, `MachineDefines seqMem` | stay |
| | antecedent `ChildBnd mref cref w ∧ MachineDefines … cnt …` (ALLOWED already in the open form: `verification-b13.md` 87) | stays |
| `…_closedB` | — | predicted NOT GENERATED: `#machine_boundary_close` reduces NOT-ALLOWED antecedents only and throws when nothing changes (`Tools/ShippingBoundaryClose.lean` 140–143, 213–214); the one antecedent is allowed. The `_try` form is used and its line is logged; if it does generate `…_closedB`, the audit is run on that instead |
| `…_closed_gap` | gap hypotheses | predicted NONE; premise listing 0 NOT ALLOWED |

SCOPE: as `NoPortsMemSeqMemTest` — one declaration, a register parent under
the general closing, a leaf register machine child and one
combinational-read memory (aw 4, dw 8), depth 0; data conditions decided per
declaration; compiler guards with fallback; `DesignSV` of the module list,
not the SV string, not `#sim`. The run, the reflections of `seqMem` and `cnt`
and `ChildBnd` at the start world remain premises.

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The data this file relies on: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let mem := Sparkle.Compiler.MachMemory.memChildName true 4 8
  let rf ← Tools.ShippingMachineCommand.readMachine f
  let rc ← Tools.ShippingMachineCommand.readMachine c
  let fe := rf.shape.insts.map (·.1)
  let outs := rf.shape.layout.outs.map (·.name)
  Lean.logInfo m!"MEMCLOSES DATA {f}: nDecl={rf.nDecl}, binders={rf.shape.binders.length}, call entries {fe}, argument lets {rf.shape.insts.map (·.2.1)}, instFields={rf.shape.instFields}, slots={rf.shape.layout.slots.length}, lets={rf.shape.layout.lets}, outputs {outs}; {c}: nDecl={rc.nDecl}, binders={rc.shape.binders.length}, slots={rc.shape.layout.slots.length}, lets={rc.shape.layout.lets}, outputs {rc.shape.layout.outs.map (·.name)}; the memory placeholder {mem}, its module's name {(Sparkle.Compiler.MachMemory.memModule true 4 8).1.name}"
  unless rf.nDecl == 3 do throwError "{f}: nDecl = {rf.nDecl}, the hand theorems are written for 3"
  for e in fe do
    unless e == c || e == mem do
      throwError "{f}: the call entries are {fe}; {e} is neither {c} nor {mem}"
  unless fe.contains c && fe.contains mem do
    throwError "{f}: the call entries are {fe}, expected both {c} and {mem}"
  for o in outs do
    if o.toList.head? == some 'i' then
      throwError "{f}: the output {o} starts with 'i' — hfresh is not decided by the first character (seqMem_outHead will fail)"
  let env ← Lean.getEnv
  for n in [f ++ `machine_design_noPortsR0, f ++ `machineData, f ++ `machine_ok,
      f ++ `machine_body, c ++ `machine_leafKid] do
    unless env.contains n do throwError "{n}: not in the imports (this file builds on it)"
  for n in [f ++ `machine_design_noPortsR0_closed, f ++ `machine_design_noPortsR0_closedB] do
    if env.contains n then throwError "{n}: exists already"

namespace Tests.Compiler.NoPortsMemSeqMemClosedTest
open Tools.ShippingMemKid (Kid calleeAt)
open Tools.ShippingMemCloses (ChildIfaceP)
open Tests.Compiler.NoPortsMemSeqMemTest (seqMem_entry cnt_notMem mem_isMem)

/-- The name of the built memory module (`SparkleMem_combo_4_8`). -/
abbrev memName : String := (Sparkle.Compiler.MachMemory.memModule true 4 8).1.name

/-- The child module's name, keyed by the callee. -/
def nameOf (c : Lean.Name) : String :=
  if c = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt then
    (Sparkle.IR.ModuleName.ofDecl (``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt : Lean.Name))
  else memName

/-- The child's number of argument ports, keyed by the callee. -/
noncomputable def nkOf (c : Lean.Name) : Nat :=
  if c = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt then
    (((Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.binders.take
      ((Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.binders.length -
        (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.layout.slots.length -
        (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.layout.lets)).filter
      fun x => x.2 != .domain).length
  else 4

/-- The child's output names, keyed by the callee. -/
noncomputable def outsNOf (c : Lean.Name) : List String :=
  if c = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt then
    (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.layout.outs.map (·.name)
  else ["out"]

/-- The module names of the child's design, keyed by the callee. -/
def namesOf (c : Lean.Name) : List String :=
  if c = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt then [] else [memName]

theorem nameOf_cnt : nameOf ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt =
    (Sparkle.IR.ModuleName.ofDecl (``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt : Lean.Name)) := by
  unfold nameOf
  exact if_pos rfl

theorem nameOf_mem : nameOf (Sparkle.Compiler.MachMemory.memChildName true 4 8) = memName := by
  unfold nameOf
  exact if_neg (by decide)

theorem nkOf_cnt : nkOf ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt =
    (((Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.binders.take
      ((Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.binders.length -
        (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.layout.slots.length -
        (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.layout.lets)).filter
      fun x => x.2 != .domain).length := by
  unfold nkOf
  exact if_pos rfl

theorem nkOf_mem : nkOf (Sparkle.Compiler.MachMemory.memChildName true 4 8) = 4 := by
  unfold nkOf
  exact if_neg (by decide)

theorem outsNOf_cnt : outsNOf ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt =
    (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.layout.outs.map
      (·.name) := by
  unfold outsNOf
  exact if_pos rfl

theorem outsNOf_mem : outsNOf (Sparkle.Compiler.MachMemory.memChildName true 4 8) = ["out"] := by
  unfold outsNOf
  exact if_neg (by decide)

theorem namesOf_cnt : namesOf ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt = [] := by
  unfold namesOf
  exact if_pos rfl

theorem namesOf_mem : namesOf (Sparkle.Compiler.MachMemory.memChildName true 4 8) = [memName] := by
  unfold namesOf
  exact if_neg (by decide)

/-! ## Names (decided over the candidate renderings; `Name.toString` is never evaluated) -/

/-- `cnt` does not print as the memory module's name. -/
theorem cnt_notin : (Sparkle.IR.ModuleName.ofDecl (``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt : Lean.Name)) ∉
    [memName] :=
  (by name_not_mem)

/-- `seqMem` does not print as the memory module's name. -/
theorem seqMem_notin :
    (Sparkle.IR.ModuleName.ofDecl (``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem : Lean.Name)) ∉
      [memName] :=
  (by name_not_mem)

/-- `cnt` and `seqMem` print differently. -/
theorem cnt_ne_seqMem :
    (Sparkle.IR.ModuleName.ofDecl (``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt : Lean.Name)) ≠
      (Sparkle.IR.ModuleName.ofDecl (``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem : Lean.Name)) :=
  Tools.ShippingNameSep.Enc.sep_ne (by first | decide | decide +kernel)

theorem cnt_ne_mem :
    (Sparkle.IR.ModuleName.ofDecl (``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt : Lean.Name)) ≠ memName := by
  intro e
  apply cnt_notin
  rw [e]
  exact List.mem_cons_self ..

theorem mem_ne_seqMem : memName ≠
    (Sparkle.IR.ModuleName.ofDecl (``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem : Lean.Name)) := by
  intro e
  apply seqMem_notin
  rw [← e]
  exact List.mem_cons_self ..

/-! ## The data conditions of the closing (decided on the reflected data) -/

theorem seqMem_alias :
    (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).letsAliasOk = true := by
  first | decide | decide +kernel

theorem seqMem_argsN : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts.length),
    nkOf (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k) =
      ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts[k]).2.1.length := by
  first | decide | decide +kernel

theorem seqMem_fieldOut : ∀ (k : Nat),
    k < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts.length →
    (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.instFields.getD k "" ∈
      outsNOf (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k) := by
  first | decide | decide +kernel

theorem seqMem_fieldsNd : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts.length)
    (k' : Nat)
    (hk' : k' < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts[k]).1 =
      ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts[k']).1 →
    ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts[k]).2.1 =
      ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts[k']).2.1 →
    (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.instFields.getD k "" =
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.instFields.getD k' "" →
    k = k' := by
  first | decide | decide +kernel

theorem seqMem_outHead :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.layout.outs,
      o.name.toList.head? ≠ some 'i' := by
  first | decide | decide +kernel

/-! ## The premises of M2 on `seqMem` -/

/-- **`cnt`'s full-entry result has the interface**: from its reflection (and
its own closing, inside `cnt.machine_leafKid`). -/
theorem cnt_iface {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl (``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt : Lean.Name))
      (((Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.binders.take
        ((Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.binders.length -
          (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.layout.slots.length -
          (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.layout.lets)).filter
        fun x => x.2 != .domain).length
      ((Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.layout.outs.map
        (·.name))
      [] y.1 y.2 := by
  have lk := Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_leafKid hRc
  have hG := Tools.ShippingSeqChildIface.seqChild_of_real
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData lk.ok lk.body lk.leaf lk.outTy
    lk.entry lk.closes hy
  exact Tools.ShippingCallsKidsD.ChildIfaceD.toP (Tools.ShippingCallsKidsD.ChildIfaceG.toD hG)
    (fun hx => nomatch hx)

/-- **Every kid of `seqMem` has the interface**: `cnt` by `cnt_iface`, the
memory placeholder by `memKid_iface`. -/
theorem seqMem_kidsP {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    ∀ (k : Nat)
      (hk : k < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts.length)
      (y : Tools.ShippingChildInv.Res),
      Kid mref cref
        ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts[k]).1 y →
      ChildIfaceP
        (nameOf (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k))
        (nkOf (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k))
        (outsNOf (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k))
        (namesOf (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k))
        y.1 y.2 := by
  intro k hk y hy
  rw [Tools.ShippingMemKid.calleeAt_eq
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData hk]
  rcases seqMem_entry k hk with h | h
  · rw [h] at hy ⊢
    rw [nameOf_cnt, nkOf_cnt, outsNOf_cnt, namesOf_cnt]
    exact cnt_iface hRc (hy.real cnt_notMem)
  · rw [h] at hy ⊢
    rw [nameOf_mem, nkOf_mem, outsNOf_mem, namesOf_mem]
    exact Tools.ShippingMemCloses.memKid_iface mem_isMem hy

/-- Different callees have different module names. -/
theorem seqMem_sep : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts.length)
    (k' : Nat)
    (hk' : k' < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts.length),
    nameOf (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k) =
      nameOf (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k') →
    ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts[k]).1 =
      ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts[k']).1 := by
  intro k hk k' hk' he
  rw [Tools.ShippingMemKid.calleeAt_eq
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData hk,
    Tools.ShippingMemKid.calleeAt_eq
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData hk'] at he
  rcases seqMem_entry k hk with h | h
  · rcases seqMem_entry k' hk' with h' | h'
    · exact h.trans h'.symm
    · rw [h, h', nameOf_cnt, nameOf_mem] at he
      exact absurd he cnt_ne_mem
  · rcases seqMem_entry k' hk' with h' | h'
    · rw [h, h', nameOf_mem, nameOf_cnt] at he
      exact absurd he.symm cnt_ne_mem
    · exact h.trans h'.symm

/-- No child module is named as the parent. -/
theorem seqMem_parent : ∀ (k : Nat),
    k < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts.length →
    nameOf (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k) ≠
      (Sparkle.IR.ModuleName.ofDecl (``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem : Lean.Name)) := by
  intro k hk
  rw [Tools.ShippingMemKid.calleeAt_eq
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData hk]
  rcases seqMem_entry k hk with h | h
  · rw [h, nameOf_cnt]
    exact cnt_ne_seqMem
  · rw [h, nameOf_mem]
    exact mem_ne_seqMem

/-- No output of the parent is an instance name. -/
theorem seqMem_fresh : ∀ (gi : Nat) (k : Nat),
    k < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts.length →
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.layout.outs,
      o.name ≠ s!"inst{gi}_{nameOf (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k)}" :=
  fun gi _ _ o ho => Tools.ShippingCallsGate.instName_ne_of_head (seqMem_outHead o ho) gi _

/-- The parent's name is not a module name of a child's design. -/
theorem seqMem_parentD : ∀ (k : Nat),
    k < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts.length →
    (Sparkle.IR.ModuleName.ofDecl (``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem : Lean.Name)) ∉
      namesOf (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k) := by
  intro k hk
  rw [Tools.ShippingMemKid.calleeAt_eq
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData hk]
  rcases seqMem_entry k hk with h | h
  · rw [h, namesOf_cnt]
    exact fun hx => nomatch hx
  · rw [h, namesOf_mem]
    exact seqMem_notin

/-- Two different callees share no module name (no shared descendant: `cnt`
is a leaf, the memory module's design is the module itself). -/
theorem seqMem_disj : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts.length)
    (k' : Nat)
    (hk' : k' < (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts[k]).1 ≠
      ((Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape.insts[k']).1 →
    nameOf (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k) ∉
        namesOf (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k') ∧
      ∀ x ∈ namesOf (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k),
        x ∉ namesOf
          (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k') := by
  intro k hk k' hk' hne
  rw [Tools.ShippingMemKid.calleeAt_eq
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData hk,
    Tools.ShippingMemKid.calleeAt_eq
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData hk']
  rcases seqMem_entry k hk with h | h
  · rcases seqMem_entry k' hk' with h' | h'
    · exact absurd (h.trans h'.symm) hne
    · rw [h, h', nameOf_cnt, namesOf_cnt, namesOf_mem]
      exact ⟨cnt_notin, fun x hx => nomatch hx⟩
  · rcases seqMem_entry k' hk' with h' | h'
    · rw [h, h', nameOf_mem, namesOf_mem, namesOf_cnt]
      exact ⟨(fun hx => nomatch hx), (fun x _ hx => nomatch hx)⟩
    · exact absurd (h.trans h'.symm) hne

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAt seqMem`** — a parent with a leaf register machine
child and a memory child, from the reflection of `cnt` only (M2). -/
theorem seqMem_closes {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData).shape :=
  Tools.ShippingMemCloses.machineClosesAt_of_kidsDM (nDecl := 3)
    (hagree := by first | decide | decide +kernel)
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_ok
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_body
    seqMem_alias (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun k => nameOf
      (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k))
    (fun k => nkOf
      (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k))
    (fun k => outsNOf
      (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k))
    (fun k => namesOf
      (calleeAt Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machineData k))
    (seqMem_kidsP hRc) seqMem_argsN seqMem_fieldOut seqMem_fieldsNd seqMem_sep seqMem_parent
    seqMem_fresh seqMem_parentD seqMem_disj

open Lean Meta Elab Command

/-- The closed form of an endpoint whose LAST binder is `MachineClosesAt f`:
that binder replaced by the premises of `cl` (a theorem
`∀ {mctx mref cctx cref}, premises → MachineClosesAt mctx mref cctx cref f …`).
(`Tests.Compiler.NoPortsGrandHTest.closeDeep` takes the last binder BUT ONE;
`seqMem.machine_design_noPortsR0` has no binder after the closing.) -/
def closeLast (f openN cl closedN : Name) : MetaM Unit := do
  if (← getEnv).contains closedN then throwError "{closedN}: exists already"
  let info ← getConstInfo openN
  let clT := (← getConstInfo cl).type
  let value ← forallTelescope info.type fun xs _ => do
    let m := xs.size
    unless m ≥ 1 do throwError "{openN}: no binder"
    let closes := xs[m - 1]!
    let ct ← instantiateMVars (← inferType closes)
    unless ct.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 && ct.getArg! 4 == toExpr f do
      throwError "{openN}: its last binder is not MachineClosesAt of {f}:{indentExpr ct}"
    let ctx := ct.getAppArgs.extract 0 4
    forallTelescope (← instantiateForall clT ctx) fun hs goal => do
      unless ← isDefEq goal ct do
        throwError "{cl}: proves{indentExpr goal}\nnot{indentExpr ct}"
      let body := mkAppN (mkConst openN)
        (xs.extract 0 (m - 1) ++ #[mkAppN (mkConst cl) (ctx ++ hs)])
      mkLambdaFVars (xs.extract 0 (m - 1) ++ hs) body
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  if (type.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
    throwError "{closedN}: the closed statement still asks MachineClosesAt"
  for c in Tests.Compiler.NoPortsMemSeqMemTest.forbiddenMem do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{closedN}: REFUSED, the statement mentions {c}"
  Tools.ShippingMachineLinkedCommand.addTheorem closedN type value

/-- The `gap_…` hypotheses of a goal-gap theorem. -/
def gapsOf (thm : Name) : MetaM (List String) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    let mut out : List String := []
    for x in xs do
      let nm := (← x.fvarId!.getUserName).toString
      if nm.startsWith "gap_" then out := out ++ [nm]
    return out

/-- The proposition binders of a statement, printed. -/
def propBinders (t : Lean.Expr) : MetaM (Array String) :=
  forallTelescope t fun xs _ => do
    let mut out : Array String := #[]
    for x in xs do
      let ty ← instantiateMVars (← inferType x)
      if ← isProp ty then out := out.push (toString (← ppExpr ty))
    return out

end Tests.Compiler.NoPortsMemSeqMemClosedTest

/-! ## The closed endpoint -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem
  let openN := f ++ `machine_design_noPortsR0
  let closed := Tools.ShippingMachineClosesGen.closedName openN
  Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsMemSeqMemClosedTest.closeLast f openN
      ``Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_closes closed
  Lean.logInfo m!"MEMCLOSES [{closed}]: {openN} with its binder MachineClosesAt {f} replaced by the premise of seqMem_closes (the reflection of cnt at the run's contexts) — the closing of a parent with a memory child, by Tools.ShippingMemCloses.machineClosesAt_of_kidsDM over closeInstsGM_run_allM"

/-! ## The boundary and the goal gap

The one antecedent of the closed endpoint is `ChildBnd ∧ MachineDefines cnt`,
ALLOWED as it is; `#machine_boundary_close` reduces NOT-ALLOWED antecedents
only and throws when nothing changes, so its `_try` form is used: a refusal
is LOGGED (`BOUNDARY CLOSE REFUSED`). The gap theorem is generated for the
closed endpoint, and for `…_closedB` if that exists. -/

set_option maxHeartbeats 0 in
#machine_boundary_close_try
  Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of_try
  Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem.machine_design_noPortsR0_closedB

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.seqMem
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let openN := f ++ `machine_design_noPortsR0
  let closed := f ++ `machine_design_noPortsR0_closed
  let closedB := f ++ `machine_design_noPortsR0_closedB
  let hasB := (← Lean.getEnv).contains closedB
  let final := if hasB then closedB else closed
  let gap := if hasB then f ++ `machine_design_noPortsR0_closedB_gap
    else f ++ `machine_design_noPortsR0_closed_gap
  -- (a) standard axioms: the general theorems of this round, the hand lemmas, the endpoints
  for n in [``Tools.ShippingMemCloses.mapM_loop_allM,
      ``Tools.ShippingMemCloses.closeInstsGM_run_allM,
      ``Tools.ShippingMemCloses.closeInstsGM_run_all_again,
      ``Tools.ShippingMemCloses.design_checksM,
      ``Tools.ShippingMemCloses.design_checks_again,
      ``Tools.ShippingMemCloses.isMemModule_memModule,
      ``Tools.ShippingMemCloses.memIface,
      ``Tools.ShippingMemCloses.memKid_iface,
      ``Tools.ShippingCallsKidsD.ChildIfaceD.toP,
      ``Tools.ShippingMemCloses.closeInstsG_of_kidsP,
      ``Tools.ShippingMemCloses.machineClosesAt_of_kidsDM,
      ``Tools.ShippingMemCloses.machineClosesAt_of_kidsD_fromM,
      ``Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_alias,
      ``Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_argsN,
      ``Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_fieldOut,
      ``Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_fieldsNd,
      ``Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_kidsP,
      ``Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_sep,
      ``Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_parent,
      ``Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_fresh,
      ``Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_parentD,
      ``Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_disj,
      ``Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_closes,
      closed, final, gap] do
    unless (← Lean.getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (b) the closing theorem: its ONLY proposition premise is the reflection of cnt
  let clT := (← Lean.getConstInfo ``Tests.Compiler.NoPortsMemSeqMemClosedTest.seqMem_closes).type
  let clB ← Tests.Compiler.NoPortsMemSeqMemClosedTest.propBinders clT
  unless clB.size == 1 do
    throwError "seqMem_closes: {clB.size} proposition premises, expected 1 (MachineDefines {c}): {clB}"
  let clOk ← Lean.Meta.forallTelescope clT fun xs _ => do
    let mut ok := true
    for x in xs do
      let ty ← Lean.instantiateMVars (← Lean.Meta.inferType x)
      if ← Lean.Meta.isProp ty then
        unless ty.isAppOf ``Tools.ShippingMachineEntry.MachineDefines do ok := false
    return ok
  unless clOk do throwError "seqMem_closes: a premise is not a reflection: {clB}"
  -- (c) the statements: no checker constant, no closing premise, no boundary over contexts
  let openT := (← Lean.getConstInfo openN).type
  unless (openT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome do
    throwError "{openN}: does not ask MachineClosesAt (the inventory is wrong)"
  for n in [closed, final, gap] do
    let t := (← Lean.getConstInfo n).type
    for k in Tests.Compiler.NoPortsTest.checkers ++ Tests.Compiler.NoPortsMemSeqMemTest.forbiddenMem do
      if (t.find? (·.isConstOf k)).isSome then throwError "{n}: the statement mentions {k}"
    if (t.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
      throwError "{n}: asks MachineClosesAt"
    if (t.find? (·.isConstOf ``Tools.ShippingChildInv.ChildRanIn)).isSome then
      throwError "{n}: mentions ChildRanIn"
  -- (d) the binders: the open form's without the closing, plus the reflection of cnt
  let closedT := (← Lean.getConstInfo closed).type
  let bOpen ← Tests.Compiler.NoPortsMemSeqMemClosedTest.propBinders openT
  let bClosed ← Tests.Compiler.NoPortsMemSeqMemClosedTest.propBinders closedT
  unless bOpen.size == 3 && bClosed.size == 3 do
    throwError "{closed}: {bClosed.size} proposition binders ({openN}: {bOpen.size}), expected 3 and 3:\n{bClosed}\nvs\n{bOpen}"
  unless bClosed[0]! == bOpen[0]! && bClosed[1]! == bOpen[1]! do
    throwError "{closed}: its first two proposition binders are not those of {openN}:\n{bClosed}\nvs\n{bOpen}"
  let thirdOk ← Lean.Meta.forallTelescope closedT fun xs _ => do
    let mut props : Array Lean.Expr := #[]
    for x in xs do
      let ty ← Lean.instantiateMVars (← Lean.Meta.inferType x)
      if ← Lean.Meta.isProp ty then props := props.push ty
    return props.size == 3 &&
      props[2]!.isAppOf ``Tools.ShippingMachineEntry.MachineDefines &&
      props[2]!.getArg! 4 == Lean.toExpr c
  unless thirdOk do
    throwError "{closed}: its third proposition binder is not the reflection of {c}:\n{bClosed[2]!}"
  -- (e) under the existentials: ONE antecedent, allowed, the open form's
  let finalT := (← Lean.getConstInfo final).type
  let innerOpen ← Lean.Meta.forallTelescope openT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  let inner ← Lean.Meta.forallTelescope finalT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  Lean.logInfo m!"MEMCLOSES ANTECEDENTS {openN}: {innerOpen.size} — {innerOpen.map (·.1)}"
  Lean.logInfo m!"MEMCLOSES ANTECEDENTS {final}: {inner.size} — {inner.map (·.1)}"
  unless inner.size == 1 && inner[0]!.2 do
    throwError "{final}: expected ONE allowed antecedent under the existentials: {inner.map (·.1)}"
  -- (f) the complete premise list: 0 NOT ALLOWED (what is kept is printed, never relaxed)
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines final
  Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
  unless bad.isEmpty do
    throwError "{final}: {bad.size} premise(s) NOT ALLOWED:\n{String.intercalate "\n" bad.toList}"
  let (linesOpen, badOpen) ← Tests.Compiler.NoPortsTest.premiseLines openN
  -- (g) the gap theorem: no gap hypothesis
  let gaps ← Tests.Compiler.NoPortsMemSeqMemClosedTest.gapsOf gap
  unless gaps.isEmpty do throwError "{gap}: the gap hypotheses are {gaps}, expected none"
  let bLine : String := if hasB then "closedB GENERATED (audited above)"
    else "REFUSED (logged above): the antecedent was allowed already, no closedB"
  Lean.logInfo m!"MEMCLOSES AUDIT {f}: {final} and {gap} on standard axioms, with Tools.ShippingMemCloses (mapM_loop_allM, closeInstsGM_run_allM, design_checksM, memIface, closeInstsG_of_kidsP, machineClosesAt_of_kidsDM; the old statements re-derived: closeInstsGM_run_all_again, design_checks_again, machineClosesAt_of_kidsD_fromM) and the hand lemmas of this file. seqMem_closes has ONE proposition premise, the reflection of {c}. Against {openN} ({linesOpen.size} premises listed, {badOpen.size} NOT ALLOWED: MachineClosesAt {f}) the closed endpoint has {lines.size} premises listed, 0 NOT ALLOWED: the run, MachineDefines {f}, MachineDefines {c}, and under the existentials ONE antecedent (the boundary ChildBnd ∧ MachineDefines {c}, allowed). {gap}: NO gap hypothesis. No checker constant, no MachineClosesAt, no ChildRanIn in the statements. Boundary close: {bLine}. SCOPE: one declaration, a register parent under the general closing, a leaf register machine child and one combinational-read memory (aw 4, dw 8), depth 0; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list — not the SV string, not #sim. The run, the reflections and ChildBnd remain premises."

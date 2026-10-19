import Tests.Compiler.MemDepthProbeTest
import Tools.ShippingKidsChildIfaceM
import Tools.ShippingMemNamesP
import Tools.ShippingChildIfaceGen
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # The closing of `memParent`, by hand (round par/c-3)

WRITTEN, NOT BUILT. TARGET-ONLY. Not a measurement: the theorems below are
ASSERTED (an error here is an error of the file). It imports the probe
`Tests/Compiler/MemDepthProbeTest.lean` for the declarations and for what the
probe's successful steps leave in the environment: the endpoints' data of
`memCounterH` and `memParent` (`machineData`, `machine_ok`, `machine_body`),
and `memCounterH.noPortsMem_closes` (step C5, `#machine_no_ports_mem`).

`memParent` is a register parent under the general closing with the callees
`cnt` (a leaf register machine) and `memCounterH` (a hand-written loop whose
one call is a memory read). `#machine_closes_at memParent` refuses it ("the
machine child memCounterH has calls of its own", `ShippingMachineClosesAtGenG`
44); the deep generator would refuse `memCounterH`'s callee ("a memory
child", `ShippingChildIfaceGen` 312). Here the two theorems those generators
would have to produce are written by hand, with the built general theorems:

* `memCounterH_iface`: the interface of `memCounterH` as a kid
  (`ChildIfaceD`), by `kidsChild_of_realM` — its one child is the built
  memory module (`memKidNamesP`), its own closing `memCounterH.noPortsMem_closes`;
* `memParent_closes`: `MachineClosesAt … memParent`, by the BUILT
  `machineClosesAt_of_kidsD` — `memParent` has no memory entry of its OWN
  (`hnomem` is decided), only a kid that has one; the name conditions about
  that kid's descendants are discharged by `ofDecl_not_mem_allMem` (a
  declaration's module name is not a memory-module name).

Premises: the reflections of `cnt` and `memCounterH` at one context, nothing
else. The data conditions are decided by the kernel, as the generators do.

ASSUMED BY READING, checked by the first theorem (`memParent_calls`): the
call entries of `memParent` are `[cnt, cnt, memCounterH]` (a structure call
is one entry per field: `n`, `hit`; then the one-output call). If that
theorem fails, the tables below (indexed 0, 1, 2) are wrong and nothing
after it means anything. -/
namespace Tests.Compiler.MemParentClosesTest
open Sparkle.Tests.Compiler.MemDepthProbeTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.Compiler.MachMemory (memChild? memModule memChildName)
open Sparkle.IR.ModuleName (ofDecl ofMem)
open Tools.ShippingKidsChildIfaceM Tools.ShippingMemNamesP

/-! ## The data read (decided) -/

/-- The call entries of `memParent`, in the reader's order. -/
theorem memParent_calls :
    memParent.machineData.shape.insts.map (·.1) = [``cnt, ``cnt, ``memCounterH] := by decide

/-- The one call entry of `memCounterH` is the combinational placeholder at
address width 4, data width 8. -/
theorem memCounterH_entry : ∀ (k : Nat) (hk : k < memCounterH.machineData.shape.insts.length),
    (memCounterH.machineData.shape.insts[k]).1 = memChildName true 4 8 := by decide

/-- The placeholder's child is the built module (the generators' own `rfl`). -/
theorem mem_isMem : memChild? (memChildName true 4 8) = some (memModule true 4 8) := by
  first | rfl | decide

/-! ## `memCounterH` as a kid -/

/-- The names below `memCounterH`: its memory module, once per entry. -/
noncomputable def memNames : List String :=
  namesOfP memCounterH.machineData (fun _ => ofMem true 4 8) (fun _ => [ofMem true 4 8])

theorem memNames_allMem : AllMem memNames :=
  namesOfP_const_allMem memCounterH.machineData true 4 8

/-- **The interface of `memCounterH` as a kid of a general closing.** -/
theorem memCounterH_iface {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memCounterH
      memCounterH.machineData.shape)
    (y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)
    (hy : Tools.ShippingChildInv.RealChild mref cref ``memCounterH y) :
    Tools.ShippingCallsKidsD.ChildIfaceD ``memCounterH
      (((memCounterH.machineData).bsIn.take 3).filter (fun b => b.2 != .domain)).length
      ((memCounterH.machineData).shape.layout.outs.map (·.name)) memNames y.1 y.2 :=
  kidsChild_of_realM (nDecl := 3) (hagree := by first | decide | decide +kernel)
    memCounterH.machineData
    memCounterH.machine_ok memCounterH.machine_body
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (fun _ => ofMem true 4 8) (fun _ => [ofMem true 4 8])
    (fun k hk y hy =>
      memKidNamesP ((congrArg memChild? (memCounterH_entry k hk)).trans mem_isMem) hy)
    (ofDecl_not_mem_allMem ``memCounterH memNames_allMem)
    hR (fun _ _ _ => memCounterH.noPortsMem_closes) hy

/-! ## The tables of `memParent`'s three entries -/

/-- The hardware arguments of `cnt` (a leaf: the generator's expression). -/
noncomputable def cntArgs : Nat :=
  ((cnt.machineData.shape.binders.take (cnt.machineData.shape.binders.length -
    cnt.machineData.shape.layout.slots.length - cnt.machineData.shape.layout.lets)).filter
      fun x => x.2 != .domain).length

noncomputable def nkT : Nat → Nat
  | 0 => cntArgs
  | 1 => cntArgs
  | 2 => (((memCounterH.machineData).bsIn.take 3).filter (fun b => b.2 != .domain)).length
  | _ => 0

noncomputable def outsT : Nat → List String
  | 0 => cnt.machineData.shape.layout.outs.map (·.name)
  | 1 => cnt.machineData.shape.layout.outs.map (·.name)
  | 2 => (memCounterH.machineData).shape.layout.outs.map (·.name)
  | _ => []

noncomputable def namesT : Nat → List String
  | 2 => memNames
  | _ => []

/-- Only entry 2 has names below it. -/
theorem namesT_two : ∀ (k : Nat) (x : String), x ∈ namesT k → k = 2
  | 0, x, hx => by
    have h : x ∈ ([] : List String) := hx
    cases h
  | 1, x, hx => by
    have h : x ∈ ([] : List String) := hx
    cases h
  | 2, _, _ => rfl
  | k + 3, x, hx => by
    have h : x ∈ ([] : List String) := hx
    cases h

/-- The names below any entry are memory-module names. -/
theorem namesT_allMem : ∀ (k : Nat), AllMem (namesT k)
  | 0 => allMem_nil
  | 1 => allMem_nil
  | 2 => memNames_allMem
  | _ + 3 => allMem_nil

/-! ## The closing -/

set_option maxHeartbeats 4000000 in
/-- **`memParent`'s machine synthesis closes where the real compile runs
it**, from the reflections of its two callees. -/
theorem memParent_closes {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``memCounterH
      memCounterH.machineData.shape) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``memParent
      memParent.machineData.shape :=
  Tools.ShippingCallsKidsD.machineClosesAt_of_kidsD (nDecl := 4) memParent.machineData
    memParent.machine_ok memParent.machine_body
    (by decide) (by decide) (by decide) (by decide) (by decide)
    nkT outsT namesT
    (by decide)
    (by
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
          | succ k => exact absurd hk' (by omega))
    (by decide) (by decide) (by decide)
    (Tools.ShippingNameDischarge.names_inj _)
    (Tools.ShippingNameDischarge.parent_ne _ _ (by decide))
    (fun gi c _ o ho => Tools.ShippingCallsGate.instName_ne_of_head
      ((by decide : ∀ o ∈ memParent.machineData.shape.layout.outs,
        o.name.toList.head? ≠ some 'i') o ho) gi (ofDecl c.1))
    (fun k _ => ofDecl_not_mem_allMem ``memParent (namesT_allMem k))
    (fun k _ => ofDecl_not_mem_allMem _ (namesT_allMem k))
    (fun k hk k' hk' hne =>
      ⟨ofDecl_not_mem_allMem _ (namesT_allMem k'),
       fun x hx hx' => by
        have e1 := namesT_two k x hx
        have e2 := namesT_two k' x hx'
        subst e1
        subst e2
        exact hne rfl⟩)

end Tests.Compiler.MemParentClosesTest

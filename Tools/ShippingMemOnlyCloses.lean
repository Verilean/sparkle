import Tools.ShippingMemClosesKids
import Tools.ShippingMemOnly

/-! # `MachineClosesAt` of a MEMORY-ONLY parent, from decided reader data (round par/a-19)

A corollary of `Tools.ShippingMemCloses.machineClosesAt_of_kidsDM` (M2, BUILT
at 710ed31f) for a shape ALL of whose call entries are memory placeholders
(`memChild? … = some (memModule cb aw dw)`): the child interface `hkid` is
discharged by `memKid_iface` (the built module has `ChildIfaceP`:
`memIface`), so NO reflection premise is left — a memory child has none.

The tables of M2 are fixed here:

    nameK k  := memNameAt d k        -- the name of entry k's memory module
    nk k     := 4                    -- wa, wd, we, ra
    outsK k  := ["out"]
    namesK k := [memNameAt d k]      -- the memory module's design is itself

What is left of M2's hypotheses, all on the reader's data (decided per
declaration; none is a reduction):

| M2 | here |
|---|---|
| `ok`, `hbody`, `halias`, `hC`, `hslots`, `hdomB`, `hfne` | the same |
| `hkid` | `hmem`: every entry is a memory placeholder — then `memKid_iface` |
| `hargsN` | `hargsN`: every entry has 4 argument `let`s |
| `hfieldOut` | `hfield`: every entry's field is `"out"` |
| `hfieldsNd` (callee, arguments AND field equal → one entry) | `hargsNd`: callee and arguments equal → one entry. NOT `Nodup` of field names: with `hfield` the field clause is always true, so two reads of one memory module are told apart by their ARGUMENT `let`s only |
| `hsep` | the same, over `memNameAt` |
| `hparent` | the same, over `memNameAt` |
| `hfresh` | `hout`: no output of the parent starts with `i` (`instName_ne_of_head`) |
| `hparentD` (`declName.toString ∉ [memNameAt d k]`) | DERIVED from `hparent` |
| `hdisjD` (different callees: `memNameAt d k ∉ [memNameAt d k']`, twice) | DERIVED from `hsep` (its contrapositive) |

`hpair` (two entries of one declaration have one child) is not a hypothesis
of M2: it is proved inside it from `closeInstsGM_run_allM`.

NOT proved here: that two different placeholder names give two different
module names (`memNameAt` injective on placeholders — it would need
`Nat.repr` injective); `hsep` and `hparent` stay hypotheses and are decided
on each declaration's concrete names.

Contents: `memNameAt`, `memNameAt_eq`, `machineClosesAt_memOnly` (the
general theorem), `MemOnlyCloseData`, `machineClosesAt_of_memOnlyData` (the
same over the BUILT `MemOnlyData`), `sep_of_one` / `parent_of_one` (`hsep` /
`hparent` of a parent whose entries are all of ONE placeholder).

WRITTEN, NOT BUILT (par/a-19). -/
namespace Tools.ShippingMemOnlyCloses
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingCallsGate Tools.ShippingCallsRunG Tools.ShippingSeqChildIface
open Tools.ShippingInstStmtG Tools.ShippingCallsStmtsG Tools.ShippingDesignWith
open Tools.ShippingDesignWithG Tools.ShippingCallsSeqKids
open Tools.ShippingCallsKidsD
open Tools.ShippingMemKid (Kid calleeAt calleeAt_eq)
open Tools.ShippingMemCloses (ChildIfaceP memKid_iface machineClosesAt_of_kidsDM)
open Sparkle.Compiler.MachMemory (memModule memChild?)

/-- The name of the memory module of call entry `k` (`""` when the entry is
not a memory placeholder, or `k` is out of range). -/
def memNameAt (d : MachineData) (k : Nat) : String :=
  ((memChild? (calleeAt d k)).map fun (md : Res) => md.1.name).getD ""

/-- `memNameAt` at an entry whose placeholder's child is `md`. -/
theorem memNameAt_eq (d : MachineData) {k : Nat} (hk : k < d.shape.insts.length) {md : Res}
    (hc : memChild? (d.shape.insts[k]).1 = some md) : memNameAt d k = md.1.name := by
  have h1 : memChild? (calleeAt d k) = some md :=
    (congrArg memChild? (calleeAt_eq d hk)).trans hc
  exact congrArg (fun (o : Option Res) => (o.map fun (md : Res) => md.1.name).getD "") h1

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000 in
/-- **`MachineClosesAt` of a memory-only parent**: every call entry a memory
placeholder, the rest decided reader data. No reflection premise, no child
interface premise (`memKid_iface`). -/
theorem machineClosesAt_memOnly {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    (hmem : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      ∃ (cb : Bool) (aw dw : Nat), memChild? (d.shape.insts[k]).1 = some (memModule cb aw dw))
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      (d.shape.insts[k]).2.1.length = 4)
    (hfield : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" = "out")
    (hargsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 → k = k')
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), memNameAt d k = memNameAt d k' →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1)
    (hparent : ∀ (k : Nat), k < d.shape.insts.length → memNameAt d k ≠ declName.toString)
    (hout : ∀ o ∈ d.shape.layout.outs, o.name.toList.head? ≠ some 'i') :
    MachineClosesAt mctx mref cctx cref declName d.shape := by
  refine machineClosesAt_of_kidsDM d ok hbody halias hC hslots hdomB hfne
    (memNameAt d) (fun _ => 4) (fun _ => ["out"]) (fun k => [memNameAt d k])
    ?_ ?_ ?_ ?_ hsep hparent ?_ ?_ ?_
  · -- hkid: a kid of a memory placeholder is the built module
    intro k hk y hy
    obtain ⟨cb, aw, dw, hc⟩ := hmem k hk
    show ChildIfaceP (memNameAt d k) 4 ["out"] [memNameAt d k] y.1 y.2
    rw [memNameAt_eq d hk hc]
    exact memKid_iface hc hy
  · -- hargsN
    intro k hk
    exact (hargsN k hk).symm
  · -- hfieldOut
    intro k hk
    show d.shape.instFields.getD k "" ∈ ["out"]
    exact List.mem_singleton.mpr (hfield k hk)
  · -- hfieldsNd: the field clause is not needed
    intro k hk k' hk' hc ha _
    exact hargsNd k hk k' hk' hc ha
  · -- hfresh
    intro gi k _ o ho
    exact Tools.ShippingCallsGate.instName_ne_of_head (hout o ho) gi _
  · -- hparentD
    intro k hk
    show declName.toString ∉ [memNameAt d k]
    intro hx
    exact hparent k hk (List.mem_singleton.mp hx).symm
  · -- hdisjD: two different callees have two different module names
    intro k hk k' hk' hne
    have hn : memNameAt d k ≠ memNameAt d k' := fun e => hne (hsep k hk k' hk' e)
    show memNameAt d k ∉ [memNameAt d k'] ∧ ∀ x ∈ [memNameAt d k], x ∉ [memNameAt d k']
    refine ⟨?_, ?_⟩
    · intro hx
      exact hn (List.mem_singleton.mp hx)
    · intro x hx hx'
      exact hn ((List.mem_singleton.mp hx).symm.trans (List.mem_singleton.mp hx'))

/-- **The data conditions of the closing of one memory-only parent** that
`MemOnlyData` does not have. Every field is decided per declaration by the
kernel; none is a reduction. -/
structure MemOnlyCloseData (d : MachineData) : Prop where
  alias : d.letsAliasOk = true
  argsN : ∀ (k : Nat) (hk : k < d.shape.insts.length), (d.shape.insts[k]).2.1.length = 4
  field : ∀ (k : Nat), k < d.shape.insts.length → d.shape.instFields.getD k "" = "out"
  argsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
    (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
    (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 → k = k'
  outHead : ∀ o ∈ d.shape.layout.outs, o.name.toList.head? ≠ some 'i'

/-- **`MachineClosesAt` of a memory-only parent, over the built
`MemOnlyData`** (`ok`, the body equation, `callsOk`, the slots, the late
binders, `instFields ≠ []` and "every entry is a memory placeholder" are its
fields). -/
theorem machineClosesAt_of_memOnlyData {declName : Name} {d : MachineData} {nDecl aw dw : Nat}
    (D : Tools.ShippingMemOnly.MemOnlyData d nDecl aw dw) (C : MemOnlyCloseData d)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), memNameAt d k = memNameAt d k' →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1)
    (hparent : ∀ (k : Nat), k < d.shape.insts.length → memNameAt d k ≠ declName.toString) :
    MachineClosesAt mctx mref cctx cref declName d.shape :=
  machineClosesAt_memOnly d D.ok D.body C.alias D.calls D.slots D.domB D.fne
    (fun k hk => (D.mem k hk).elim fun cb h => Exists.intro cb (Exists.intro aw (Exists.intro dw h)))
    C.argsN C.field C.argsNd hsep hparent C.outHead

/-- `hsep` of a parent whose entries are all of ONE declaration `c`. -/
theorem sep_of_one {d : MachineData} {c : Name}
    (h : ∀ (k : Nat) (hk : k < d.shape.insts.length), (d.shape.insts[k]).1 = c) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), memNameAt d k = memNameAt d k' →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1 :=
  fun k hk k' hk' _ => (h k hk).trans (h k' hk').symm

/-- `hparent` of a parent whose entries are all of ONE placeholder `c`, with
child `md`: the parent does not print as `md`'s module name. -/
theorem parent_of_one {declName : Name} {d : MachineData} {c : Name} {md : Res}
    (h : ∀ (k : Nat) (hk : k < d.shape.insts.length), (d.shape.insts[k]).1 = c)
    (hc : memChild? c = some md)
    (hnot : declName.toString ∉ [md.1.name]) :
    ∀ (k : Nat), k < d.shape.insts.length → memNameAt d k ≠ declName.toString := by
  intro k hk e
  apply hnot
  have hk' : memChild? (d.shape.insts[k]).1 = some md :=
    (congrArg memChild? (h k hk)).trans hc
  have e' : md.1.name = declName.toString := (memNameAt_eq d hk hk').symm.trans e
  exact List.mem_singleton.mpr e'.symm

end Tools.ShippingMemOnlyCloses

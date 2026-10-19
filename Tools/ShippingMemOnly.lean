import Tools.ShippingMemKidFacts
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # Memory-only parents: the four run hypotheses of the check-free head (G1, unit U4, round par/b-14)

A MEMORY-ONLY parent is a machine all of whose call entries are memory
placeholders (`SparkleMem.combo.aw.dw` / `SparkleMem.sync.aw.dw`):
`memCounter`, `twoMems`, `mixedMems`, `memWide`, `syncNarrow`. Its depth-0
shipping theorem `f.machine_ships_hier` is on the route `.mem`
(`Tools/ShippingMachineShipsHierCommand.lean` 40–43, 86–98): reset `ResetM`,
child bound `Bd = kidsMem`, invariant `memInv`.

This file gives what `Tools.ShippingNoPorts.machine_design_noPorts` at
`n = 0` asks of such a parent's core run — NOTHING here is a copy of a built
proof except the eleven lines of `core_kidsMemM` (the memory branch of the
built `core_kidsMixedM`, which proves `kidsMixed`, a weaker bound than the
route's `kidsMem`):

* `kidsMem_of`: `kidsMem` of a body from one fact per instance statement
  (the all-statements form of the built `kidsMem_one`);
* `core_kidsMemM`: `kidsMem (childMap D.modules) b.body` of a machine tied by
  the general closing whose kids are ALL built memory modules — from the
  built `core_callStmtM`, `kidsMem_one`, `mem_conns_noRdata`;
* `MemOnlyData d nDecl aw dw`: the data conditions of ONE memory-only parent
  whose memories have the same address and data widths (the read kind may
  differ entry by entry: `memOuts` / `memIns` do not depend on it), each
  decided per declaration;
* `memOnly_kids`: `KidFactsM` of every call entry (the built `memKid_facts`);
* `memOnly_runFacts`, `memOnly_outsCheck`, `memOnly_kidsMem`,
  `memOnly_designCheck`: the four run hypotheses, by the built `kidsM_*`
  theorems and `core_kidsMemM` at depth 0.

All four take `ChildBnd mref cref w` and `MachineClosesAt` (as the built
`kidsM_*` do). The closing is NOT proved here.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingMemOnly
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Sparkle.Compiler.MachMemory (memModule memChild?)
open Tools.ShippingMemKid

/-- **`kidsMem` from one fact per instance statement.** -/
theorem kidsMem_of {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {body : List Stmt}
    (h : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
      Tools.ShippingMachineShipsHier.kidsMem C [Stmt.inst mn iname conns] = true) :
    Tools.ShippingMachineShipsHier.kidsMem C body = true := by
  unfold Tools.ShippingMachineShipsHier.kidsMem
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    refine Eq.trans ?_ (h mn iname conns hst)
    first
      | exact (Bool.and_true _).symm
      | simp [Tools.ShippingMachineShipsHier.kidsMem]
  | _ => rfl

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **`kidsMem` of a machine tied by the general closing all of whose kids
are built memory modules, on the core run's design**: every instance of the
full entry's module resolves to a kid's own module, which is the built memory
module; its connections name its ports only (`core_callStmtM`,
`mem_conns_noRdata`). The analogue of `core_kidsMixedM` for the route `.mem`. -/
theorem core_kidsMemM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hagree : Tools.ShippingInstTagged.TagsAgree d.shape)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hkidF : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y → ∃ cb aw dw, y.1 = (memModule cb aw dw).1)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingMachineShipsHier.kidsMem (childMap D.modules) b.body = true := by
  have hst := core_callStmtM (hagree := hagree) d ok hbody hC hslots hdomB hins hfne outTy hB hcore hpost entry
    closes
  refine kidsMem_of fun mn iname conns hm => ?_
  obtain ⟨mc, hmc, ⟨k, hk, y, hre, hmcy⟩, nIn, kI, n, names, args, outs, hcs⟩ :=
    hst mn iname conns hm
  have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
    congrArg (fun o : Option Sparkle.IR.AST.Module =>
      o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
  obtain ⟨cb, aw, dw, hmem⟩ := hkidF k hk y hre
  rw [← hmcy] at hmem
  rw [hmem] at hcs hCm
  exact kidsMem_one hCm (mem_conns_noRdata hcs)

/-- **The data conditions of one memory-only parent** whose memories all have
address width `aw` and data width `dw` (`nDecl`: its declaration binders).
Every field is decided per declaration by the kernel; none is a reduction. -/
structure MemOnlyData (d : MachineData) (nDecl aw dw : Nat) : Prop where
  ok : d.ok = true
  body : d.shape.body = quote d.dom
    (fun j => inputExpr d.shape.binders.length (d.bpos j))
    (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed
  calls : d.callsOk nDecl = true
  slots : d.ss.length = d.shape.layout.slots.length
  domB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain
  ins : d.shape.insts ≠ []
  sl : d.shape.layout.slots ≠ []
  fne : d.shape.instFields ≠ []
  outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width
  mem : ∀ (k : Nat) (hk : k < d.shape.insts.length),
    ∃ cb, memChild? (d.shape.insts[k]).1 = some (memModule cb aw dw)
  cw : Tools.ShippingCallWidths.callWidthsOk d nDecl (fun _ => memOuts dw) = true
  args : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl (fun _ => memIns aw dw) = true
  outNames : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name
  outScalar : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true
  /-- origin dispatch (patched compiler): every entry's placeholder name says
  what its origin builds (decided; a collision shape is then not generated) -/
  agree : Tools.ShippingInstTagged.TagsAgree d.shape

/-- **`KidFactsM` of every call entry of a memory-only parent**, at depth 0
(`memKid_facts`, for either read kind). -/
theorem memOnly_kids {d : MachineData} {aw dw : Nat}
    (hmem : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      ∃ cb, memChild? (d.shape.insts[k]).1 = some (memModule cb aw dw)) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsM mref cref (d.shape.insts[k]).1 (memOuts dw) (memIns aw dw) 0 := by
  intro k hk
  obtain ⟨cb, hc⟩ := hmem k hk
  exact memKid_facts hc

/-- **The run's facts of the full entry's module** (`kidsM_runFacts`). -/
theorem memOnly_runFacts {c : Name} {d : MachineData} {nDecl aw dw : Nat}
    (h : MemOnlyData d nDecl aw dw)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  kidsM_runFacts (hagree := h.agree) d h.ok h.body h.calls h.slots h.domB h.ins h.sl h.fne h.outTy
    (fun _ => memOuts dw) (fun _ => memIns aw dw) 0 (memOnly_kids h.mem) h.cw
    hB hcore hpost entry closes

/-- **The output check at depth 0, under the statement-kind gate**
(`kidsM_outsCheck`). -/
theorem memOnly_outsCheck {c : Name} {d : MachineData} {nDecl aw dw : Nat}
    (h : MemOnlyData d nDecl aw dw)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) 0 (checkedOptimize b) = true :=
  kidsM_outsCheck (hagree := h.agree) d h.ok h.body h.calls h.slots h.domB h.ins h.fne h.outTy
    (fun _ => memOuts dw) (fun _ => memIns aw dw) 0 (memOnly_kids h.mem)
    hB hcore hpost entry closes hg

/-- **The children's bound of the route `.mem`: `kidsMem`** (`core_kidsMemM`;
a kid of a memory placeholder is the built module, `Kid.mem`). -/
theorem memOnly_kidsMem {c : Name} {d : MachineData} {nDecl aw dw : Nat}
    (h : MemOnlyData d nDecl aw dw)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingMachineShipsHier.kidsMem (childMap D.modules) b.body = true :=
  core_kidsMemM (hagree := h.agree) d h.ok h.body h.calls h.slots h.domB h.ins h.fne h.outTy
    (fun k hk y hy => by
      obtain ⟨cb, hc⟩ := h.mem k hk
      exact ⟨cb, aw, dw, congrArg Prod.fst (hy.mem hc)⟩)
    hB hcore hpost entry closes

/-- **`designCheck` at depth 0 of the shipped module, with no check premise**
(`kidsM_designCheck`). -/
theorem memOnly_designCheck {c : Name} {d : MachineData} {nDecl aw dw : Nat}
    (h : MemOnlyData d nDecl aw dw)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) 0 (checkedOptimize b) = true :=
  kidsM_designCheck (hagree := h.agree) d h.ok h.body h.calls h.slots h.domB h.ins h.sl h.fne h.outTy
    (fun _ => memOuts dw) (fun _ => memIns aw dw) 0 (memOnly_kids h.mem) h.cw h.args
    hB hcore hpost entry closes h.outNames h.outScalar

end Tools.ShippingMemOnly

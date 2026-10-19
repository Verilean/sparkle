import Tools.ShippingChecksCore
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # `kidsMaskedN` of a machine with calls, at the core run's design (G1)

The depth endpoints ask `kidsMaskedN D.modules b.body = true`
(`Tools/ShippingMachineShipsDepth.lean`): every instance statement of the
full entry's module names a module of the core design whose outputs are
MASKED, `outsMaskedN child`:

1. `noMem child.body`;
2. for every output port `p`: `outMasked (declWidth child) child.body p` —
   `p.name` is written exactly ONCE in the body
   (`(writesOf child.body).count p.name == 1`), and some statement is
   `assign p.name r` with `r` a constant or a slice (`selfMasked`) and
   `widthOf (declWidth child) r ≤ p.ty.bitWidth`;
3. no instance connection of the child's body is `ref p.name`.

Proved here
* `kidsMaskedN_of`: the check from one fact per instance statement;
* `core_kidsMaskedN`: for a core run on a machine with calls, the check on
  THE CORE RUN'S design and the full entry's module, from one fact per real
  child (`hkidM`: its module and the modules of its design have masked
  outputs) — the same reduction as `core_outsCheck_all`;
* `outsMaskedN_of_seqOk`: on a module of assignments and registers, (1) and
  (3) hold; what is left is (2);
* `leaf_real_outsMaskedN`: `hkidM` for a real child without calls, from (2)
  for its module.

NOT proved — what `kidsMaskedN` still needs, exactly
(2) for a leaf child's entry module `y.1`. By construction the output
assignments are `outAssigns w outs`: `assign o.name (slice (ref w) (lo +
width - 1) lo)` (`Sparkle.IR.Machine.fieldRhs`) — a slice, so `selfMasked`
holds SYNTACTICALLY of what `closeMachine` writes. Three facts are missing
between that and (2), none of them a fact about emitted text, all of them
facts about the run's module:
  a. the slice survives the full entry's post-processing: `y.1` is
     `dropZeroWidthModule M` or its `mergeChecked`; the derived
     `leaf_real_outsAssigned` gives SOME `assign p.name r` in `y.1.body`,
     not that `r` is still the slice (`mergeChecked` rewrites right-hand
     sides when it merges registers; a zero-width field's assignment is
     dropped with its port);
  b. single writer: `p.name` is not written by the transition's wires, by a
     `next` assignment or by a register — the transition's writes and the
     slot names against the output names. `Tools.ShippingCloseMachineFacts`
     has `Acyclic.nodup` for the assignments `X ++ Y` of the closed body and
     `static_checks`; the registers' names against the outputs' and the
     transfer through (a) are not stated anywhere I found;
  c. the width: `widthOf _ (slice e (lo + width - 1) lo) = width` needs
     `0 < width` (else `lo + 0 - 1` underflows), and
     `p.ty.bitWidth = o.width` is the endpoints' `outTy`.
So the answer to "is a slice masked by construction" is yes for the
expression, and the check additionally asks (a)–(c).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingChecksMasked
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
open Tools.ShippingMachineShipsDepth (kidsMaskedN outsMaskedN)
open Tools.ShippingChecksDerived (all_of_seqOk ff_absurd)
open Tools.ShippingChecksDepth (and_true_intro)

/-- `kidsMaskedN` from one fact per instance statement. -/
theorem kidsMaskedN_of {ms : List Sparkle.IR.AST.Module} {body : List Stmt}
    (h : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
      ∃ mc, moduleByName ms mn = some mc ∧ outsMaskedN mc = true) :
    kidsMaskedN ms body = true := by
  unfold Tools.ShippingMachineShipsDepth.kidsMaskedN
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    obtain ⟨mc, hmc, hm⟩ := h mn iname conns hst
    simp only [hmc]
    exact hm
  | _ => rfl

/-- On a module of assignments and registers: no memory, no instance
connection; the outputs are masked when each is assigned once by a
self-masked expression within its width. -/
theorem outsMaskedN_of_seqOk {c : Sparkle.IR.AST.Module} (hs : c.body.all seqStmtOk = true)
    (hm : ∀ p ∈ c.outputs,
      Tools.ShippingMachineShipsHier.outMasked (Sparkle.IR.RegDedup.declWidth c) c.body p = true) :
    outsMaskedN c = true := by
  unfold Tools.ShippingMachineShipsDepth.outsMaskedN Tools.ShippingMachineShipsHier.noMem
  refine and_true_intro
    (all_of_seqOk hs _ fun st hst => by cases st <;> first | rfl | exact ff_absurd hst) ?_
  exact List.all_eq_true.mpr fun p hp => and_true_intro (hm p hp)
    (all_of_seqOk hs _ fun st hst => by cases st <;> first | rfl | exact ff_absurd hst)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **`kidsMaskedN` of a machine with calls, on the core run's design** —
the heads' literal form — from one fact per real child. -/
theorem core_kidsMaskedN {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidM : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      outsMaskedN y.1 = true ∧ ∀ g ∈ y.2.modules, outsMaskedN g = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    kidsMaskedN D.modules b.body = true := by
  obtain ⟨-, hbody', -, hresM, hrealD, -⟩ :=
    Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes
  refine kidsMaskedN_of fun mn iname conns hm => ?_
  rw [hbody'] at hm
  obtain ⟨mc, hmc⟩ := hresM mn iname conns hm
  have hmem : mc ∈ D.modules := (Tools.ShippingHierPremisesBase.moduleByName_mem hmc).1
  obtain ⟨k, hk, y, hre, hor, -⟩ := hrealD mc hmem
  refine ⟨mc, hmc, ?_⟩
  rcases hor with heq | hin
  · rw [heq]
    exact (hkidM k hk y hre).1
  · exact (hkidM k hk y hre).2 mc hin

/-- **`hkidM` for a real child without calls**, from the masked assignment of
each output port of its module (clause (2) of the header — the open part). -/
theorem leaf_real_outsMaskedN {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChild mref cref c y)
    (hm : ∀ p ∈ y.1.outputs,
      Tools.ShippingMachineShipsHier.outMasked (Sparkle.IR.RegDedup.declWidth y.1) y.1.body p =
        true) :
    outsMaskedN y.1 = true ∧ ∀ g ∈ y.2.modules, outsMaskedN g = true := by
  have hI := seqChild_of_real d ok hbody hno outTy entry closes h
  refine ⟨outsMaskedN_of_seqOk hI.seqOk hm, ?_⟩
  intro g hg
  rw [hI.design] at hg
  cases hg

end Tools.ShippingChecksMasked

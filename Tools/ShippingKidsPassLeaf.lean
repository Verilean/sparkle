import Tools.ShippingLeafTyped
import Tools.ShippingChecksWidths
import Tools.ShippingChecksDepthGate

/-! # `hkids` of `core_designCheck_run`: the children's check from per-child facts (G1, round optfb-7)

`core_kidsPass_leaf`:

    kidsPass (childMap D.modules) (kidCheck (childMap D.modules) n) (checkedOptimize b).body = true

for the core run of a machine with calls, at every depth `n`, from ONE fact
per real child (`hkidK`): the child's module — and every module of the
child's own design — passes `kidCheck C n` for every child map and depth.

* The instance statements of the shipped module are the full entry's
  (`checkedOptimize_inst_iff_gate`, under the statement-kind gate
  `core_hierGate`); each resolves in the design to a module of a real child
  (`core_kids_facts`).
* For a LEAF machine child, `hkidK` is
  `Tools.ShippingLeafTyped.leaf_real_kidK` — with its hypothesis
  `hmergePrint` (a merged leaf passes the print guard), which is not derived
  (see that file's header) — or `leaf_real_kidK_id` where the child's merge
  is the identity.

Scope: `hkidK` quantifies over EVERY child map and depth, which a leaf
satisfies (its check does not consult the child map). A child with calls of
its own passes `designCheck C k` only for the child map of a design that
contains ITS children; that case is not covered by this statement.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingKidsPassLeaf
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **The children's check of the shipped module of a machine with calls**,
on the core run's design, at every depth, from one fact per real child. -/
theorem core_kidsPass_leaf {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkidK : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
        ∀ g ∈ y.2.modules,
          ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
            Tools.ShippingChecksDesign.kidCheck C n g = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) (n : Nat) :
    Tools.ShippingDesignSV.kidsPass (childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (childMap D.modules) n)
      (checkedOptimize b).body = true := by
  obtain ⟨-, hbody', -, hresM, hrealD, -⟩ :=
    Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes
  have hgate : Sparkle.IR.RefineCheck.hierGate b = true :=
    Tools.ShippingChecksWidths.core_hierGate d ok hbody hC hslots hdomB hins hfne outTy hnomem
      hB hcore hpost entry closes
  unfold Tools.ShippingDesignSV.kidsPass
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    have hm : Stmt.inst mn iname conns ∈ b.body :=
      (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hgate mn iname conns).mp hst
    rw [hbody'] at hm
    obtain ⟨mc, hmc⟩ := hresM mn iname conns hm
    have hmem : mc ∈ D.modules := (Tools.ShippingHierPremisesBase.moduleByName_mem hmc).1
    obtain ⟨k, hk, y, hre, hor, -⟩ := hrealD mc hmem
    have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
    simp only [hCm]
    rcases hor with heq | hin
    · rw [heq]
      exact (hkidK k hk y hre).1 _ n
    · exact (hkidK k hk y hre).2 mc hin _ n
  | _ => rfl

end Tools.ShippingKidsPassLeaf

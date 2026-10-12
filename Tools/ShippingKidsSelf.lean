import Tools.ShippingKidsPassLeaf
import Tools.ShippingChildServe
import Tools.ShippingPortsMatchRaw
import Tools.ShippingChecksMasked

/-! # The parent's design holds its children's modules AS THEMSELVES; the children's check at depth (G1, unit U2, round par/a-13)

`Tools.ShippingKidsPassLeaf.core_kidsPass_leaf` asks of every real child

    ∀ C n, kidCheck C n y.1 = true        (and the same of the modules of its design)

— true of a LEAF (its check does not read the child map), FALSE of a child
with instances: `kidCheck C (k+1) y.1 = designCheck C k y.1` asks `C` to
resolve the child's instances. This file states the form that is true at
depth and derives the parent's side of it.

* `core_kids_self`: for a core run of a machine with calls (either
  closing), every module `g` of the run's design is a real child's module
  or a module of a real child's design, and the design resolves THAT
  child's module and every module of THAT child's design, by name, to
  itself:

      moduleByName D.modules y.1.name = some y.1 ∧
      ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2

  Both closings CHECK this (`closeInsts` / `closeInstsG`: "every child
  module, and every module of a child's design, is found by its name in the
  merged design as itself"); `Tools.ShippingChecksCore.core_kids_facts`
  keeps only the NAMES (`∃ g' ∈ D.modules, g'.name = g2.name`). Read off
  `closeInsts_names` + `closeInsts_acyclic` / `closeInstsG_names`.
* `core_kidsPass_deep`: `kidsPass (childMap D.modules) (kidCheck (childMap
  D.modules) n) (checkedOptimize b).body = true` from ONE fact per real
  child, in the form that is true at depth:

      ∀ ms, moduleByName ms y.1.name = some y.1 →
        (∀ g ∈ y.2.modules, moduleByName ms g.name = some g) →
        kidCheck (childMap ms) n y.1 = true ∧ ∀ g ∈ y.2.modules, kidCheck (childMap ms) n g = true

  (for a leaf child the two antecedents are not used: `core_kidsPass_leaf`'s
  hypothesis implies this one).
* `core_kidsMaskedN_top`: `kidsMaskedN D.modules b.body = true` from
  `outsMaskedN y.1` of each real child ONLY — not of the modules of its
  design, which `Tools.ShippingChecksMasked.core_kidsMaskedN` asks and
  which is not derived for a gate grandchild. Every instance of the general
  closing's module resolves to a real child's module
  (`Tools.ShippingPortsMatchRaw.core_callConns`).

SCOPE: `core_kidsPass_deep` and `core_kidsMaskedN_top` are for the GENERAL
closing (`instFields ≠ []`: `core_hierGate`, `core_callConns`);
`core_kids_self` is for either closing. No memory child (`hnomem`).

The statement and the first part of `core_kids_self`'s proof are
`core_kids_facts`' (`Tools/ShippingChecksCore.lean`), copied; if that
changes, this copy does not follow.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingKidsSelf
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

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **The design of a core run on a machine with calls resolves its real
children's modules, and the modules of their designs, to themselves.** -/
theorem core_kids_self {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
      moduleByName D.modules y.1.name = some y.1 ∧
      ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2 := by
  obtain ⟨bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
    machine_run_of_core hcore entry hB
  have hne := closes bb _ _ _ hw9 hd9 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
  obtain ⟨-, -, -, L, -, -, -, -, -, -, -, hDeq, -⟩ := hcc.some
  obtain ⟨-, -, hd0⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  -- the closing's own check: every child, and every module of a child's
  -- design, is found by its name in the merged design as itself
  have hself : ∀ y ∈ children, moduleByName D.modules y.1.name = some y.1 ∧
      ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2 := by
    rcases hcc with ⟨-, hI⟩ | ⟨-, hG, -⟩
    · intro y hy
      exact ⟨(Tools.ShippingChildServe.closeInsts_names hI).2 y hy,
        (Tools.ShippingChildServe.closeInsts_acyclic hI).2.2.2 y hy⟩
    · exact (Tools.ShippingMachineInstG.closeInstsG_names hG).2.2.2
  -- the children, by their witnesses
  obtain ⟨hlenC, hall⟩ := hreal
  -- the design: the join of the children
  obtain ⟨-, hdVis⟩ := designWith_modules (children := children) hd0
  intro g hg
  have hg' : g ∈ (designWith children d₀).modules := by
    rw [← hDeq]
    exact hg
  obtain ⟨y, hy, hor⟩ := mem_visited.mp (hdVis g hg')
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hy
  have hk' : k < d.shape.insts.length := by
    rw [← hlenC]
    exact (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨y', hy', hor'⟩ := hall k hk'
  rw [hk] at hy'
  cases hy'
  rcases hor' with hmem | hre
  · rw [hnomem _ (List.getElem_mem hk')] at hmem
    cases hmem
  · exact ⟨k, hk', y, hre, hor, hself y hy⟩

set_option maxHeartbeats 4000000 in
/-- **The children's check of the shipped module of a machine with calls, at
depth `n`**, on the core run's design, from one fact per real child in the
form that holds of a child WITH instances: its check against any module list
that resolves it and the modules of its design to themselves. -/
theorem core_kidsPass_deep {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (n : Nat)
    (hkidK : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ ms : List Sparkle.IR.AST.Module,
        moduleByName ms y.1.name = some y.1 →
        (∀ g ∈ y.2.modules, moduleByName ms g.name = some g) →
        Tools.ShippingChecksDesign.kidCheck (childMap ms) n y.1 = true ∧
          ∀ g ∈ y.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) n g = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingDesignSV.kidsPass (childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (childMap D.modules) n)
      (checkedOptimize b).body = true := by
  obtain ⟨-, hbody', -, hresM, -, -⟩ :=
    Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes
  have hselfD := core_kids_self d ok hbody hC hslots hdomB hins hnomem hB hcore entry closes
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
    obtain ⟨k, hk, y, hre, hor, hs1, hs2⟩ := hselfD mc hmem
    have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
    simp only [hCm]
    rcases hor with heq | hin
    · rw [heq]
      exact (hkidK k hk y hre D.modules hs1 hs2).1
    · exact (hkidK k hk y hre D.modules hs1 hs2).2 mc hin
  | _ => rfl

set_option maxHeartbeats 4000000 in
/-- **`kidsMaskedN` of a machine tied by the general closing, on the core
run's design**, from the masked outputs of each real child's OWN module
(nothing is asked of the modules of the child's design: every instance of
the parent resolves to a real child's module). -/
theorem core_kidsMaskedN_top {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hkidM : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true := by
  have hconn := Tools.ShippingPortsMatchRaw.core_callConns d ok hbody hC hslots hdomB hins hfne
    outTy hnomem hB hcore hpost entry closes
  refine Tools.ShippingChecksMasked.kidsMaskedN_of fun mn iname conns hm => ?_
  obtain ⟨mc, hmc, ⟨k, hk, y, hre, hmcy⟩, -⟩ := hconn mn iname conns hm
  refine ⟨mc, hmc, ?_⟩
  rw [hmcy]
  exact hkidM k hk y hre

end Tools.ShippingKidsSelf

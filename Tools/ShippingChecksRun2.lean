import Tools.ShippingChecksRun

/-! # The modules of a parent's design are its real children's (G1)

`parent_run_outsCheck0` asks `outsA` of every module of the run's design.
Here that is DERIVED from the children's own runs:

* `kidsDesign_real`: for a run of the full entry on a machine with calls and
  a register (the hypotheses of
  `Tools.ShippingKidsChildIface.kidsChild_iface`), every module of the
  returned design is `y.1` or a module of `y.2` for some call `k` and a
  `RealChild` witness `y` of the `k`-th called declaration — the design is
  the join of the closing's children (`designWith_modules`, `mem_visited`),
  each child is real (`ChildrenReal`), and the full entry's design is the
  core run's (`synthesizeCombinational_designL`).
* `parent_run_outsCheck0_kids`: `parent_run_outsCheck0` with `outsA`
  replaced by one fact per real child (`hkidA`): its module assigns its
  outputs, and so does every module of its design.
* `leaf_real_kidA`: that fact for a child that is a machine without calls
  and with a register — from its `RealChild` witness (its module by
  `leaf_real_outsAssigned`, its design is empty by `seqChild_of_real`).

What is NOT proved here
* `hkidA` for a child WITH calls of its own (it would be this file's theorem
  applied at the child, by induction on the depth), for a slotless child and
  for a memory child.
* The gate `hierBinds b` stays a hypothesis. -/
namespace Tools.ShippingChecksRun2
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
/-- **Every module of the full entry's design is a real child's module or a
module of a real child's design.** -/
theorem kidsDesign_real {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (namesK : Nat → List String)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      KidNames (d.shape.insts[k]).1 (namesK k) y.1 y.2)
    (hself : (Sparkle.IR.ModuleName.ofDecl c) ∉ namesOf d namesK)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∀ g ∈ design.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) := by
  obtain ⟨M, D, w1, hcore, hpost, hdesL⟩ := synthesizeCombinational_designL hr
  obtain ⟨_, bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
    machine_run_of_core hcore entry (ChildBnd.of_invW mctx cctx hw)
  have hne := closes bb _ _ _ hw9 hd9 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
  obtain ⟨-, -, hMname, L, hLinst, hperm, -, -, -, -, -, hDeq, -⟩ := hcc.some
  obtain ⟨hseq0, hname0, hd0⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  -- the children, by their witnesses
  obtain ⟨hlenC, hall⟩ := hreal
  have hfull : ∀ (k : Nat) (y : Res), children[k]? = some y → ∃ hk : k < d.shape.insts.length,
      KidNames (d.shape.insts[k]).1 (namesK k) y.1 y.2 := by
    intro k y hc
    have hk : k < d.shape.insts.length := by
      rw [← hlenC]
      exact (List.getElem?_eq_some_iff.mp hc).1
    obtain ⟨y', hy, hor⟩ := hall k hk
    rw [hc] at hy
    cases hy
    rcases hor with hmem | hre
    · rw [hnomem _ (List.getElem_mem hk)] at hmem
      cases hmem
    · exact ⟨hk, hkid k hk y hre⟩
  have hnameK : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      (Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1) ∈ namesOf d namesK ∧
      ∀ x ∈ namesK k, x ∈ namesOf d namesK := by
    intro k hk
    refine ⟨List.mem_append_left _ (List.mem_map.mpr ⟨_, List.getElem_mem hk, rfl⟩), fun x hx => ?_⟩
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, hx⟩)
  -- the design: the join of the children
  rw [hDeq] at hdesL
  obtain ⟨hdNd, hdVis⟩ := designWith_modules (children := children) hd0
  have hvisN : ∀ g ∈ (designWith children d₀).modules, g.name ∈ namesOf d namesK := by
    intro g hg
    obtain ⟨y, hy, hor⟩ := mem_visited.mp (hdVis g hg)
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hy
    obtain ⟨hk', full⟩ := hfull k y hk
    obtain ⟨hn1, hn2⟩ := hnameK k hk'
    rcases hor with heq | hin
    · rw [heq, full.name]
      exact hn1
    · exact hn2 _ (full.desNames g hin)
  have hdesEq : design.modules = (designWith children d₀).modules := by
    refine hdesL (fun x hx e => hself ?_)
    rw [← hname0, ← hMname, ← e]
    exact hvisN x hx
  -- every module of the design is a real child's
  intro g hg
  rw [hdesEq] at hg
  obtain ⟨y, hy, hor⟩ := mem_visited.mp (hdVis g hg)
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
  · exact ⟨k, hk', y, hre, hor⟩

set_option maxHeartbeats 4000000 in
/-- **The depth-0 `outsCheck` of the printed module of a machine with calls,
over every run, from the children's own facts.** `hkidA`: each real child's
module assigns its outputs, and so does every module of its design. -/
theorem parent_run_outsCheck0_kids {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (namesK : Nat → List String)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      KidNames (d.shape.insts[k]).1 (namesK k) y.1 y.2)
    (hkidA : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
        ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true)
    (hself : (Sparkle.IR.ModuleName.ofDecl c) ∉ namesOf d namesK)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hb : hierBinds b = true) :
    Tools.ShippingDesignSVBack.outsCheck (childMap design.modules) 0 (checkedOptimize b) = true ∧
      ∀ mn iname conns, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
        ∃ mc, moduleByName design.modules mn = some mc := by
  have hreal := kidsDesign_real d ok hbody hC hslots hdomB hins namesK hnomem hkid hself hw hr
    entry closes
  refine Tools.ShippingChecksRun.parent_run_outsCheck0 d ok hbody hC hslots hdomB hins hsl outTy
    kD hkD hIlen hSL hSlen hLlen hNIn namesK hnomem hkid hself hw hr entry closes hb ?_
  intro g hg
  obtain ⟨k, hk, y, hre, hor⟩ := hreal g hg
  rcases hor with heq | hin
  · rw [heq]
    exact (hkidA k hk y hre).1
  · exact (hkidA k hk y hre).2 g hin

/-- **`hkidA` for a child that is a machine without calls and with a
register**, from its `RealChild` witness. -/
theorem leaf_real_kidA {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChild mref cref c y) :
    Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true := by
  refine ⟨Tools.ShippingChecksRun.leaf_real_outsAssigned d ok hbody hno hsl hSS outTy entry
    closes h, ?_⟩
  have hI := seqChild_of_real d ok hbody hno outTy entry closes h
  intro g hg
  rw [hI.design] at hg
  cases hg

end Tools.ShippingChecksRun2

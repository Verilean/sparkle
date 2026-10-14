import Tests.Compiler.ShippingHierarchySoundnessTest
import Tools.ShippingGateConeRun

/-! # `gate_cone_runG` instantiated for `parentMix` (worker N, round 3)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeRunTest`;
not in `Tests.AllTests`).

`parentMix a b := childAdd a b + a`: a gate-route parent whose body is a cone
(one canonical `+`) over an instance leaf (`childAdd a b`) and an input leaf.

* `parentMix_coneK` — from the cone guarantee `HierConePreservesK` over a
  child cache `mF`, the compiled module's LINKED evaluation drives `out` with
  `(parentMix aS bS).val t`, given — about THE RUN'S OWN child, `mF`'s entry
  of `childAdd` — that its module is `childModule` and its design has no
  modules, and that `childAdd` is designated in the environment the entry
  read. The child facts of `childModule` are the built ones
  (`childAdd_correct`, decided port facts); no `SubSynthDefinesAll`, no
  `HardwareTagged`.
* `parentMix_gate_cone_runG` — the full entry: binders the run,
  `GateDefines` (NOT ALLOWED until ruled), `ChildBnd`.

The three facts about the run's child and the environment (`tagR`, `hy1`,
`hy2`) are antecedents of the conclusion, not premises: they are facts of
the values the run produced / read (the child's own endpoint would give the
first two; the third is read off the gate's acceptance at `envR`, which the
conclusion exposes — not derived here). -/
namespace Sparkle.Tests.Compiler.GateConeRunTest
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest
open Tools.ShippingHierarchySoundness
open Tools.ShippingUnifiedSource
open Tools.ShippingUnifiedMeaning Tools.ShippingUnifiedRecursion
open Tools.ShippingLinkCtx Tools.ShippingInstanceLeaf Tools.ShippingHierTermSoundness
open Tools.ShippingInstanceEntrySoundness (instEN)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingGateParentRun
open Tools.ShippingGateDefines (GateDefines)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (ChildBnd CacheInv Res)

/-- `parentMix`'s body as the gate reads it (the term of the built
`parentMix_peel`). -/
abbrev parentMixBody : Lean.Expr :=
  quote (inputExpr parentMixBinders.length 0)
    (fun _ => inputExpr parentMixBinders.length 0)
    (parentMixLeaf (inputExpr parentMixBinders.length 0)
      (inputExpr parentMixBinders.length 1) (inputExpr parentMixBinders.length 2))
    parentMixTerm

theorem parentMix_cfrag : cfrag parentMixTerm = true := rfl

/-- What the parent's linked evaluation observes (the conclusion of the built
`parentMix_entry_observes`, at the module `M`). -/
def ParentMixObserves (M : Sparkle.IR.AST.Module) : Prop :=
  ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
  ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) {D : DomainConfig}
    (aS bS : Signal D (BitVec 8)) (t : Nat) (mems : MEnv),
  let a := Tools.ShippingMixedEntrySoundness.start
    (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentMix)
  let p := Tools.ShippingMixedEntrySoundness.prepare bools bits
    (parentMixBinders.zip [i0, i1, i2]) a
  Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
    (parentMixBinders.zip [i0, i1, i2]) a →
  p.bits i1 = some ⟨8, aS.val t⟩ → p.bits i2 = some ⟨8, bS.val t⟩ →
  (∃ result, evalAssignsH (Tools.ShippingMixedEntrySoundness.moduleWidths M)
      (childrenOf childModule.name) mems M.body initial = some result ∧
    result "out" = ((parentMix aS bS).val t).toNat) ∧
  InstsLinked (childrenOf childModule.name) M

/-- **The cone over the run's own child.** -/
theorem parentMix_coneK {envR : Lean.Environment} {mF : Std.HashMap Lean.Name Res}
    {M : Sparkle.IR.AST.Module}
    (P : HierConePreservesK envR mF ``parentMix parentMixBinders parentMixBody M)
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    {y : Res} (hy : mF.get? ``childAdd = some y) (hy1 : y.1 = childModule)
    (hy2 : y.2.modules = []) :
    ParentMixObserves M := by
  obtain ⟨ids, nd, len, cache, P⟩ := P
  have len3 : ids.length = 3 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len3
  rcases ids with _ | ⟨i1, ids⟩
  · cases len3
  rcases ids with _ | ⟨i2, ids⟩
  · cases len3
  rcases ids with _ | ⟨i3, ids⟩
  rotate_left
  · simp at len3
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro bools bits initial D aS bS t mems a p adm ha0 hb0
  obtain ⟨separate, Q⟩ := P (childrenOf childModule.name) addSem bools bits initial mems adm
  have hA : inputValues p.bools p.bits i1 = some (.bits 8 (aS.val t)) :=
    inputValues_bits separate ha0
  have hB : inputValues p.bools p.bits i2 = some (.bits 8 (bS.val t)) :=
    inputValues_bits separate hb0
  letI : HierCtx := hierLink (childrenOf childModule.name)
  letI : ChildSem := addSem
  have hargsM : ∀ k (hk : k < [Lean.Expr.fvar i1, Lean.Expr.fvar i2].length)
      (hk' : k < [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)].length),
      Meaning (inputValues p.bools p.bits)
        ([Lean.Expr.fvar i1, Lean.Expr.fvar i2][k]'hk)
        ([Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)][k]'hk') := by
    intro k hk hk'
    rcases k with _ | k
    · exact .input rfl hA
    · rcases k with _ | k
      · exact .input rfl hB
      · exact absurd hk (by simp)
  have hsem : ChildSem.childSem ``childAdd
      [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)] =
      some (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) := by
    show (if ``childAdd = ``childAdd ∧
        [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)].map Value.kind =
          [.bits 8, .bits 8] then _ else none) = _
    rw [if_pos ⟨rfl, rfl⟩]
    rfl
  have leafM : LeafMeaning addSem (inputValues p.bools p.bits)
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
      (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) :=
    meaning_inst rfl rfl hargsM hsem
  -- the run's own child: `mF`'s entry of `childAdd`
  have kid : KidFacts (childrenOf childModule.name) addSem ``childAdd
      [Lean.Expr.fvar i1, Lean.Expr.fvar i2].length
      (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) y := by
    obtain ⟨y1, y2⟩ := y
    change y1 = childModule at hy1
    change y2.modules = [] at hy2
    subst hy1
    exact ⟨childWe, "out", 8, hy2, (by dsimp only; decide), (by dsimp only; decide), rfl, (by dsimp only; decide), rfl, rfl, rfl,
      childAdd_correct⟩
  -- the instance leaf, read off `mF`
  have leafK0 : LeafK envR (childrenOf childModule.name) addSem mF p.context
      (inputValues p.bools p.bits) mems initial
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
      (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) := by
    refine Or.inr ⟨``childAdd, [], .fvar i0, [.fvar i1, .fvar i2],
      [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)], rfl, rfl, rfl, rfl, tagR, rfl,
      ?_, hsem, ?_⟩
    · intro k hk hk' we fuel
      rcases k with _ | k
      · exact input_contract_fuel hA fuel
      · rcases k with _ | k
        · exact input_contract_fuel hB fuel
        · exact absurd hk (by simp)
    · intro y' hy'
      rw [hy] at hy'
      cases hy'
      exact kid
  have value := Q (.fvar i0) 0 2 (fun _ => 8) (fun _ => .fvar i0)
    (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2)) (fun _ => false)
    (fun j w => if j = 0 then BitVec.ofNat w ((aS.val t).toNat + (bS.val t).toNat)
      else BitVec.ofNat w (aS.val t).toNat)
    parentMixTerm parentMix_wf parentMix_cfrag
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => by
      rcases j with _ | j
      · exact leafM
      · rcases j with _ | j
        · show Meaning (inputValues p.bools p.bits) (.fvar i1)
            (.bits 8 (BitVec.ofNat 8 (aS.val t).toNat))
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
          exact .input rfl hA
        · exact absurd hj (by simp))
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => by
      rcases j with _ | j
      · exact leafK0
      · rcases j with _ | j
        · refine Or.inl ?_
          intro we fuel
          show Contract (translateFuelFix (translateStep envR) fuel) p.context
            (inputValues p.bools p.bits) we mems initial (.fvar i1)
            (.bits 8 (BitVec.ofNat 8 (aS.val t).toNat))
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
          exact input_contract_fuel hA fuel
        · exact absurd hj (by simp))
    rfl
  obtain ⟨⟨result, hev, hout⟩, linked⟩ := value
  refine ⟨⟨result, hev, ?_⟩, linked⟩
  rw [hout]
  show (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat) +
    BitVec.ofNat 8 (aS.val t).toNat).toNat = ((aS.val t + bS.val t) + aS.val t).toNat
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-- **`gate_cone_runG` on `parentMix`.** Binders: the run, `GateDefines`
(NOT ALLOWED until ruled), `ChildBnd`. -/
theorem parentMix_gate_cone_runG {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentMix) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentMix parentMixBinders parentMixBody)
    (bnd : ChildBnd mref cref w) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      (Sparkle.Compiler.isHardwareModule envR ``childAdd = true →
        ∀ y : Res, mF.get? ``childAdd = some y → y.1 = childModule → y.2.modules = [] →
          ParentMixObserves M) := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone⟩ :=
    gate_cone_runG hr gdef bnd
  exact ⟨M, envR, mF, hpost, hcache,
    fun tagR y hy hy1 hy2 => parentMix_coneK hcone tagR hy hy1 hy2⟩

end Sparkle.Tests.Compiler.GateConeRunTest

#print axioms Sparkle.Tests.Compiler.GateConeRunTest.parentMix_gate_cone_runG
#print axioms Tools.ShippingGateParentRun.gate_cone_runG

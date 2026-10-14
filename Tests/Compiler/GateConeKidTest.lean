import Tests.Compiler.GateConeTagTest
import Tools.ShippingFirstGateKid

/-! # `parentMix`: the cone theorem with NO antecedent (worker N, round 5)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeKidTest`;
not in `Tests.AllTests`).

`parentMix_gate_cone_runG'` (round 4) concluded the observation under two
antecedents about `mF`'s entry `y` of `childAdd`: (b) `y.1 = childModule`,
(c) `y.2.modules = []`.

* (b) is REPLACED (not proved): the observation is stated against the run's
  OWN child — the linked context `ownChild y` (`y.1` at its own declared
  widths) instead of the pinned `childrenOf childModule.name` —
  `ParentMixObservesC (ownChild y) M`.
* (c) and the rest of the child's facts are PROVED: every `mF` entry is a
  `RealChild` (`CacheInv`), and `childAdd` is a FIRST-gate declaration;
  `Tools.ShippingFirstGateKid.kidFacts_of_first'` gives the cone's
  `KidFacts (ownChild y) addSem ``childAdd 2 v y` from that witness and ONE
  new binder, `EntryDefines … ``childAdd childAddValue` (ALLOWED).
* `addSem_spec`: what the consumer's child semantics `addSem` answers on
  `childAdd` — by evaluation, no premise.
* `childAddEntry = childAddValue` (`#def_entry_value`, `rfl`): the
  `EntryDefines` value IS the entry constant's value of the real `childAdd`.

`parentMix_gate_cone_runK`: binders the run, `GateDefines` (NOT ALLOWED,
ruling pending, unchanged), `ChildBnd` (ALLOWED), `EntryDefines` of `childAdd`
(ALLOWED). Conclusion: no antecedent besides the cache lookup itself. The
old theorems are kept. -/
namespace Sparkle.Tests.Compiler.GateConeKidTest
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest
open Sparkle.Tests.Compiler.GateConeRunTest
open Sparkle.Tests.Compiler.GateConeTagTest
open Tools.ShippingHierarchySoundness
open Tools.ShippingUnifiedSource
open Tools.ShippingUnifiedMeaning Tools.ShippingUnifiedRecursion
open Tools.ShippingLinkCtx Tools.ShippingInstanceLeaf Tools.ShippingHierTermSoundness
open Tools.ShippingInstanceEntrySoundness (instEN)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingGateParentRun
open Tools.ShippingGateDefines (GateDefines)
open Tools.ShippingEntrySoundness (RunsTo FExpr evalFE quoteDecl)
open Tools.ShippingChildInv (ChildBnd CacheInv Res RealChild)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingFirstGateKid (ownChild kidFacts_of_first')

/-! ## The child: its entry value and its semantics -/

/-- `childAdd`'s value, as the first gate reads it. -/
abbrev childAddValue : Lean.Expr := quoteDecl `dom [`x, `y] 8 (.bin .add (.inp 0) (.inp 1))

#def_entry_value childAddEntry of childAdd

/-- The `EntryDefines` value is the real entry constant's. -/
example : childAddEntry = childAddValue := rfl

theorem childAdd_fe_wf : (FExpr.bin .add (.inp 0) (.inp 1)).WF [`x, `y].length 8 :=
  ⟨(by decide : 0 < 2), (by decide : 1 < 2)⟩

/-- **What `addSem` answers on `childAdd`**: two in-range 8-bit arguments,
and the result is the fragment's value on them. By evaluation. -/
theorem addSem_spec : ∀ (vs : List Value) (u : Value),
    @ChildSem.childSem addSem ``childAdd vs = some u →
    vs.length = [`x, `y].length ∧ (∀ x ∈ vs, x.toNat < 2 ^ 8) ∧
    u.toNat = (evalFE 8 (fun j => BitVec.ofNat 8 ((vs.map Value.toNat).getD j 0))
      (.bin .add (.inp 0) (.inp 1))).toNat := by
  intro vs u hsem
  have hsem' : (if ``childAdd = ``childAdd ∧ vs.map Value.kind = [.bits 8, .bits 8] then
      some (Value.bits 8 (BitVec.ofNat 8 ((vs.map Value.toNat).sum))) else none) = some u := hsem
  split at hsem'
  · rename_i hc
    cases hsem'
    obtain ⟨-, hk⟩ := hc
    have hl : vs.length = 2 := by
      have := congrArg List.length hk
      simpa using this
    rcases vs with _ | ⟨v1, vs⟩
    · cases hl
    rcases vs with _ | ⟨v2, vs⟩
    · cases hl
    rcases vs with _ | ⟨v3, vs⟩
    rotate_left
    · simp at hl
    rcases v1 with b1 | ⟨m1, a⟩
    · simp [Value.kind] at hk
    rcases v2 with b2 | ⟨m2, c⟩
    · simp [Value.kind] at hk
    have hm : m1 = 8 ∧ m2 = 8 := by simpa [Value.kind] using hk
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨rfl, ?_, ?_⟩
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact a.isLt
      · exact c.isLt
    · show (BitVec.ofNat 8 (a.toNat + (c.toNat + 0))).toNat =
        (BitVec.ofNat 8 a.toNat + BitVec.ofNat 8 c.toNat).toNat
      first
        | rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.add_zero, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt c.isLt]
        | simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt a.isLt,
            Nat.mod_eq_of_lt c.isLt]
  · cases hsem'

/-! ## The observation against a linked context -/

/-- `ParentMixObserves` with the linked context a parameter (the pinned one is
`childrenOf childModule.name`: `parentMixObserves_pinned`). -/
def ParentMixObservesC (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (M : Sparkle.IR.AST.Module) : Prop :=
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
      children mems M.body initial = some result ∧
    result "out" = ((parentMix aS bS).val t).toNat) ∧
  InstsLinked children M

theorem parentMixObserves_pinned (M : Sparkle.IR.AST.Module) :
    ParentMixObserves M = ParentMixObservesC (childrenOf childModule.name) M := rfl

/-- **The cone over ANY linked context whose `childAdd` entry has the
cone's child facts** (`parentMix_coneK` with the pinned child replaced by
`KidFacts children …` of `mF`'s entry). -/
theorem parentMix_coneKC {envR : Lean.Environment} {mF : Std.HashMap Lean.Name Res}
    {M : Sparkle.IR.AST.Module} {children : String → Option (Sparkle.IR.AST.Module × WEnv)}
    (P : HierConePreservesK envR mF ``parentMix parentMixBinders parentMixBody M)
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    {y : Res} (hy : mF.get? ``childAdd = some y)
    (hkid : ∀ v : Value, v.kind.width = 8 → KidFacts children addSem ``childAdd 2 v y) :
    ParentMixObservesC children M := by
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
  obtain ⟨separate, Q⟩ := P children addSem bools bits initial mems adm
  have hA : inputValues p.bools p.bits i1 = some (.bits 8 (aS.val t)) :=
    inputValues_bits separate ha0
  have hB : inputValues p.bools p.bits i2 = some (.bits 8 (bS.val t)) :=
    inputValues_bits separate hb0
  letI : HierCtx := hierLink children
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
  -- the run's own child: `mF`'s entry of `childAdd`, with the cone's child facts
  have kid : KidFacts children addSem ``childAdd
      [Lean.Expr.fvar i1, Lean.Expr.fvar i2].length
      (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) y :=
    hkid _ rfl
  -- the instance leaf, read off `mF`
  have leafK0 : LeafK envR children addSem mF p.context
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

/-! ## The full entry, unconditional -/

/-- **`gate_cone_runG` on `parentMix`, with NO antecedent about the run's
child.** Binders: the run, `GateDefines` (NOT ALLOWED, ruling pending —
unchanged), `ChildBnd` (ALLOWED), `EntryDefines` of `childAdd` (ALLOWED; the
ONE new binder). Conclusion: the shipped module is the cleanup (or merge) of
`M`, the final child cache `mF` is `CacheInv`, `childAdd` is tagged at the
run's environment, and for `mF`'s entry `y` of `childAdd`, `M`'s linked
evaluation against THAT child (`ownChild y`) observes `parentMix`. -/
theorem parentMix_gate_cone_runK {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentMix) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentMix parentMixBinders parentMixBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      (∀ y : Res, mF.get? ``childAdd = some y → ParentMixObservesC (ownChild y) M) := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone⟩ :=
    Tools.ShippingGateParentRun.gate_cone_runG hr gdef bnd
  have tagR := parentMix_tag hacc
  refine ⟨M, envR, mF, hpost, hcache, tagR, fun y hy => ?_⟩
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  exact parentMix_coneKC hcone tagR hy (fun v hv =>
    kidFacts_of_first' centry childAdd_fe_wf (by decide) hreal addSem v hv addSem_spec)

end Sparkle.Tests.Compiler.GateConeKidTest

#print axioms Sparkle.Tests.Compiler.GateConeKidTest.addSem_spec
#print axioms Tools.ShippingFirstGateKid.kidFacts_of_first
#print axioms Sparkle.Tests.Compiler.GateConeKidTest.parentMix_gate_cone_runK

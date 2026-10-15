import Tests.Compiler.GateConeEntryTest
import Tests.Compiler.GateParentRunGTest

/-! # `parentUse`: the single-leaf cone at a BOUND domain (worker N, round 9)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeUseTest`;
not in `Tests.AllTests`).

`parentUse a b := childAdd a b`: binders `[dom, a, b]`; the body is the call
itself, `instEN ``childAdd [] (bvar 2) [bvar 1, bvar 0]` (the round-2
`parentUseBody`). As a cone it is the one-leaf term `.bitsInput 8 0` whose
leaf is the whole body — `wrapAdd_gate_cone_runK'` (round 8) with the domain
a BINDER instead of a constant.

* tag: the leaf IS the body, so `GateLeafSel kinds body body` is the round-2
  `MixedGateSel` fact `parentUse_sel` (no new evaluation);
* entry existence: the root is the instance leaf (`inst_entryW`);
* the observation: `ParentUseObservesC (ownChild y) M`, for every domain
  `D` (the domain is a binder).

Premises of `parentUse_gate_cone_runK'`: the run, `GateDefines` (NOT
ALLOWED, ruling pending, unchanged), `ChildBnd` (ALLOWED), `EntryDefines` of
`childAdd` (ALLOWED). -/
namespace Sparkle.Tests.Compiler.GateConeUseTest
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest
open Sparkle.Tests.Compiler.GateConeRunTest
open Sparkle.Tests.Compiler.GateConeKidTest
open Sparkle.Tests.Compiler.GateParentRunGTest (parentUseBody parentUse_sel)
open Tools.ShippingHierarchySoundness
open Tools.ShippingUnifiedSource
open Tools.ShippingUnifiedMeaning Tools.ShippingUnifiedRecursion
open Tools.ShippingLinkCtx Tools.ShippingInstanceLeaf Tools.ShippingHierTermSoundness
open Tools.ShippingInstanceEntrySoundness (instEN)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingGateParentRun
open Tools.ShippingGateDefines (GateDefines)
open Tools.ShippingEntrySoundness (RunsTo FExpr evalFE quoteDecl)
open Tools.ShippingChildInv (ChildBnd CacheInv Res RealChild RefLaws)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingFirstGateKid (ownChild kidFacts_of_first')

/-! ## The tag of the callee, from the gate's acceptance -/

/-- **The callee is tagged at the run's environment**: the leaf is the body,
so the leaf selection fact is the round-2 `parentUse_sel`. -/
theorem parentUse_tag {envR : Lean.Environment}
    (hacc : ∃ dv : Lean.DefinitionVal, mixedCertifiedShape? false [] (.defnInfo dv)
      (Sparkle.Compiler.Elab.instancePredicate envR) = some (parentUseBinders, parentUseBody)) :
    Sparkle.Compiler.isHardwareModule envR ``childAdd = true :=
  Tools.ShippingGateConeTag.gate_leaf_tag' (mn := ``childAdd) (lvls := [])
    (dE := inputExpr parentUseBinders.length 0)
    (n := parentUseBinders.length) (poss := [1, 2]) hacc (List.cons_ne_nil _ _) parentUse_sel

/-! ## The cache entry exists -/

/-- **Every run of the translator on `parentUse`'s instantiated body ends
with `childAdd` in the child cache** (the root IS the instance leaf). -/
theorem parentUse_entryWN {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0)
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (ids : List FVarId) (len : ids.length = parentUseBinders.length) :
    EntryWN L D (translateFuelFix (translateStep envR) translateFuelLimit)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentUseBody) ``childAdd := by
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
  have h1 : 1 ≤ translateFuelLimit := by
    first
      | decide
      | exact Nat.le_of_ble_eq_true rfl
  have hfl : translateFuelLimit = (translateFuelLimit - 1) + 1 := by
    first
      | omega
      | exact (Nat.sub_add_cancel h1).symm
  have hbody : instFVars ([i0, i1, i2].map Lean.Expr.fvar).toArray 0 parentUseBody =
      instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2] := rfl
  rw [hbody, hfl]
  intro mctx cctx hint top named ctx s t wire w0 w1 _ hw hd hr
  exact inst_entryW (tenv := envR) (mn := ``childAdd) (lvls := [])
    (dom := .fvar i0) (argsE := [.fvar i1, .fvar i2])
    L hD (translateFuelLimit - 1) rfl rfl rfl tagR
    mctx cctx hint top named ctx s t wire w0 w1 hw hd hr

/-! ## The observation against a linked context -/

/-- What `M`'s linked evaluation against `children` observes: `parentUse`
(the text of `ParentMixObservesC`, at `parentUse`). -/
def ParentUseObservesC (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (M : Sparkle.IR.AST.Module) : Prop :=
  ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
  ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) {D : DomainConfig}
    (aS bS : Signal D (BitVec 8)) (t : Nat) (mems : MEnv),
  let a := Tools.ShippingMixedEntrySoundness.start
    (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentUse)
  let p := Tools.ShippingMixedEntrySoundness.prepare bools bits
    (parentUseBinders.zip [i0, i1, i2]) a
  Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
    (parentUseBinders.zip [i0, i1, i2]) a →
  p.bits i1 = some ⟨8, aS.val t⟩ → p.bits i2 = some ⟨8, bS.val t⟩ →
  (∃ result, evalAssignsH (Tools.ShippingMixedEntrySoundness.moduleWidths M)
      children mems M.body initial = some result ∧
    result "out" = ((parentUse aS bS).val t).toNat) ∧
  InstsLinked children M

/-- **The single-leaf cone over ANY linked context whose `childAdd` entry has
the cone's child facts.** -/
theorem parentUse_coneKC {envR : Lean.Environment} {mF : Std.HashMap Lean.Name Res}
    {M : Sparkle.IR.AST.Module} {children : String → Option (Sparkle.IR.AST.Module × WEnv)}
    (P : HierConePreservesK envR mF ``parentUse parentUseBinders parentUseBody M)
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    {y : Res} (hy : mF.get? ``childAdd = some y)
    (hkid : ∀ v : Value, v.kind.width = 8 → KidFacts children addSem ``childAdd 2 v y) :
    ParentUseObservesC children M := by
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
    meaning_inst rfl rfl rfl hargsM hsem
  have kid : KidFacts children addSem ``childAdd
      [Lean.Expr.fvar i1, Lean.Expr.fvar i2].length
      (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) y :=
    hkid _ rfl
  have leafK0 : LeafK envR children addSem mF p.context
      (inputValues p.bools p.bits) mems initial
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
      (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) := by
    refine Or.inr ⟨``childAdd, [], [.fvar i0], [.fvar i1, .fvar i2],
      [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)], rfl, (by simp), rfl, rfl, rfl, tagR, rfl,
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
  have value := Q (.fvar i0) 0 1 (fun _ => 8) (fun _ => .fvar i0)
    (fun _ => instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2]) (fun _ => false)
    (fun _ w => BitVec.ofNat w ((aS.val t).toNat + (bS.val t).toNat))
    (.bitsInput 8 0) ⟨by decide, rfl, by decide⟩ rfl
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => by
      rcases j with _ | j
      · exact leafM
      · exact absurd hj (by simp))
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => by
      rcases j with _ | j
      · exact leafK0
      · exact absurd hj (by simp))
    rfl
  obtain ⟨⟨result, hev, hout⟩, linked⟩ := value
  refine ⟨⟨result, hev, ?_⟩, linked⟩
  rw [hout]
  show (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat)).toNat = _
  rfl

/-! ## The full entry -/

/-- **`parentUse`: the cache entry exists and the observation holds against
it.** Binders: the run, `GateDefines` (NOT ALLOWED, ruling pending —
unchanged), `ChildBnd` (ALLOWED), `EntryDefines` of `childAdd` (ALLOWED). -/
theorem parentUse_gate_cone_runK' {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentUse) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentUse parentUseBinders parentUseBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      ∃ y : Res, mF.get? ``childAdd = some y ∧ ParentUseObservesC (ownChild y) M := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone, hentry⟩ :=
    gate_cone_runGE hr gdef bnd
  have tagR := parentUse_tag hacc
  obtain ⟨y, hy⟩ := hentry ``childAdd
    (fun L' _ hD ids len => parentUse_entryWN L' hD tagR ids len)
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  exact ⟨M, envR, mF, hpost, hcache, tagR, y, hy,
    parentUse_coneKC hcone tagR hy (fun v hv =>
      kidFacts_of_first' centry childAdd_fe_wf (by decide) hreal addSem v hv addSem_spec)⟩

end Sparkle.Tests.Compiler.GateConeUseTest

#print axioms Sparkle.Tests.Compiler.GateConeUseTest.parentUse_tag
#print axioms Sparkle.Tests.Compiler.GateConeUseTest.parentUse_entryWN
#print axioms Sparkle.Tests.Compiler.GateConeUseTest.parentUse_gate_cone_runK'

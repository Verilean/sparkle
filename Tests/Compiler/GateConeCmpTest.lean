import Tests.Compiler.GateConeEntryTest
import Tools.ShippingGateConeEntryC

/-! # `parentCmp`: a Bool-valued cone root over an instance leaf (worker N, round 8)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeCmpTest`;
not in `Tests.AllTests`).

`parentCmp a b := Signal.ult (childAdd a b) a`: a canonical comparison whose
first operand is the instance leaf `childAdd a b` (leaf 0) and second the
input `a` (leaf 1) — the leaves of `parentMix` (`parentMixLeaf`), the root a
`compare` (fragment `cfragC`). The shape of `parentMix_gate_cone_runK'`:

* cone: `gate_cone_runGCE` (`Tools/ShippingGateConeEntryC.lean`: round 7's
  `gate_cone_runGC` with the round-6 entry conjunct);
* entry existence: `compare_entryWN` over the first operand (`inst_entryW`)
  — the comparison root goes through the fallback's validated-cache wrapper,
  NOT the core, hence the new lemma;
* tag: the text of `parentMix_leafSel` on this body;
* the observation is Bool: `result "out" = encodeBool ((parentCmp aS bS).val t)`.

Premises of `parentCmp_gate_cone_runK'`: the run, `GateDefines` (NOT
ALLOWED, ruling pending, unchanged), `ChildBnd` (ALLOWED), `EntryDefines` of
`childAdd` (ALLOWED). Peel sanity check at the end, independent. -/
namespace Sparkle.Tests.Compiler.GateConeCmpTest
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest
open Sparkle.Tests.Compiler.GateConeRunTest
open Sparkle.Tests.Compiler.GateConeKidTest
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

/-! ## The body -/

def parentCmpBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`a, .bits 8), (`b, .bits 8)]

/-- `leaf0 <ᵤ leaf1` at width 8. -/
def cmpTerm : Term .bool := .compare .ult (.bitsInput 8 0) (.bitsInput 8 1)

theorem cmp_wf : cmpTerm.WF 0 2 (fun _ => 8) :=
  ⟨⟨by decide, rfl, by decide⟩, ⟨by decide, rfl, by decide⟩⟩

theorem cmp_cfragC : cfragC cmpTerm = true := rfl

/-- `parentCmp`'s body as the gate reads it: the leaves of `parentMix`. -/
abbrev parentCmpBody : Lean.Expr :=
  quote (inputExpr parentCmpBinders.length 0)
    (fun _ => inputExpr parentCmpBinders.length 0)
    (parentMixLeaf (inputExpr parentCmpBinders.length 0)
      (inputExpr parentCmpBinders.length 1) (inputExpr parentCmpBinders.length 2))
    cmpTerm

/-! ## The tag of the callee, from the gate's acceptance -/

theorem cmp_leaf_eq : Tools.ShippingGateConeTag.bvarCallE ``childAdd [0, 1, 2] =
    instEN ``childAdd [] (inputExpr parentCmpBinders.length 0)
      ([1, 2].map (inputExpr parentCmpBinders.length)) := rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- **The gate refuses `parentCmp`'s body under the predicate that refuses
its leaf** (every `isInst` elsewhere). The text of `parentMix_leafSel`. -/
theorem parentCmp_leafSel : ∀ (isInst : Lean.Expr → Bool) (sc : Bool),
    Tools.ShippingGateDefines.mixedGateCond
      (fun e => !Tools.ShippingGateConeTag.bvarCall ``childAdd [0, 1, 2] e && isInst e)
      (parentCmpBinders.map (·.2)).toArray parentCmpBody sc = false := by
  intro isInst sc
  have hs1 : (Sparkle.Compiler.Elab.unifiedInstanceSpine
        (parentCmpBinders.map (·.2)).toArray parentCmpBody ||
      Sparkle.Compiler.Elab.unifiedProjSpine
        (parentCmpBinders.map (·.2)).toArray parentCmpBody) = false := rfl
  have hs2 : Sparkle.Compiler.Elab.hierInstSpine
      (fun e => !Tools.ShippingGateConeTag.bvarCall ``childAdd [0, 1, 2] e && isInst e)
      (parentCmpBinders.map (·.2)).toArray parentCmpBody = false := rfl
  unfold Tools.ShippingGateDefines.mixedGateCond Sparkle.Compiler.Elab.unifiedInstanceRoot
    Sparkle.Compiler.Elab.hierInstRoot
  simp only [hs1, hs2, Bool.and_false, Bool.false_and]
  all_goals rfl

/-- **The callee is tagged at the run's environment.** -/
theorem parentCmp_tag {envR : Lean.Environment}
    (hacc : ∃ dv : Lean.DefinitionVal, mixedCertifiedShape? false [] (.defnInfo dv)
      (Sparkle.Compiler.Elab.instancePredicate envR) = some (parentCmpBinders, parentCmpBody)) :
    Sparkle.Compiler.isHardwareModule envR ``childAdd = true := by
  have h0 := Tools.ShippingGateConeTag.gateLeafSel_of
    (kinds := (parentCmpBinders.map (·.2)).toArray)
    (body := parentCmpBody) parentCmp_leafSel
  rw [cmp_leaf_eq] at h0
  exact Tools.ShippingGateConeTag.gate_leaf_tag' (mn := ``childAdd) (lvls := [])
    (dE := inputExpr parentCmpBinders.length 0)
    (n := parentCmpBinders.length) (poss := [1, 2]) hacc (List.cons_ne_nil _ _) h0

/-! ## The cache entry exists (a COMPARISON root) -/

/-- **Every lookup-free run of the translator on `parentCmp`'s instantiated
body ends with `childAdd` in the child cache** (`compare_entryWN` over the
first operand). -/
theorem parentCmp_entryWN {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0)
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (ids : List FVarId) (len : ids.length = parentCmpBinders.length) :
    EntryWN L D (translateFuelFix (translateStep envR) translateFuelLimit)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentCmpBody) ``childAdd := by
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
  have h2 : 2 ≤ translateFuelLimit := by
    first
      | decide
      | exact Nat.le_of_ble_eq_true rfl
  have hfl : translateFuelLimit = (translateFuelLimit - 2) + 1 + 1 := by
    first
      | omega
      | exact (Nat.sub_add_cancel h2).symm
  have hbody : instFVars ([i0, i1, i2].map Lean.Expr.fvar).toArray 0 parentCmpBody =
      Tools.ShippingBoolSourceSoundness.compareE .ult (.fvar i0) 8
        (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
        (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2) 1) := rfl
  rw [hbody, hfl]
  refine compare_entryWN (tenv := envR) L hD (translateFuelLimit - 2 + 1) (Or.inl ?_)
  show EntryW L D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1))
    (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2]) ``childAdd
  exact inst_entryW (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
    (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR

/-! ## The observation against a linked context (a Bool output) -/

def ParentCmpObservesC (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (M : Sparkle.IR.AST.Module) : Prop :=
  ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
  ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) {D : DomainConfig}
    (aS bS : Signal D (BitVec 8)) (t : Nat) (mems : MEnv),
  let a := Tools.ShippingMixedEntrySoundness.start
    (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentCmp)
  let p := Tools.ShippingMixedEntrySoundness.prepare bools bits
    (parentCmpBinders.zip [i0, i1, i2]) a
  Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
    (parentCmpBinders.zip [i0, i1, i2]) a →
  p.bits i1 = some ⟨8, aS.val t⟩ → p.bits i2 = some ⟨8, bS.val t⟩ →
  (∃ result, evalAssignsH (Tools.ShippingMixedEntrySoundness.moduleWidths M)
      children mems M.body initial = some result ∧
    result "out" = Tools.ShippingMuxLoweringSoundness.encodeBool ((parentCmp aS bS).val t)) ∧
  InstsLinked children M

/-- **The comparison cone over ANY linked context whose `childAdd` entry has
the cone's child facts.** -/
theorem parentCmp_coneKC {envR : Lean.Environment} {mF : Std.HashMap Lean.Name Res}
    {M : Sparkle.IR.AST.Module} {children : String → Option (Sparkle.IR.AST.Module × WEnv)}
    (P : HierConePreservesKC envR mF ``parentCmp parentCmpBinders parentCmpBody M)
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    {y : Res} (hy : mF.get? ``childAdd = some y)
    (hkid : ∀ v : Value, v.kind.width = 8 → KidFacts children addSem ``childAdd 2 v y) :
    ParentCmpObservesC children M := by
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
  have kid : KidFacts children addSem ``childAdd
      [Lean.Expr.fvar i1, Lean.Expr.fvar i2].length
      (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) y :=
    hkid _ rfl
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
    cmpTerm cmp_wf cmp_cfragC
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
  show Tools.ShippingMuxLoweringSoundness.encodeBool
    (BitVec.ult (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))
      (BitVec.ofNat 8 (aS.val t).toNat)) = _
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-! ## The full entry -/

/-- **`parentCmp`: the cache entry exists and the (Bool) observation holds
against it.** Binders: the run, `GateDefines` (NOT ALLOWED, ruling pending —
unchanged), `ChildBnd` (ALLOWED), `EntryDefines` of `childAdd` (ALLOWED). -/
theorem parentCmp_gate_cone_runK' {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentCmp) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentCmp parentCmpBinders parentCmpBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      ∃ y : Res, mF.get? ``childAdd = some y ∧ ParentCmpObservesC (ownChild y) M := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone, hentry⟩ :=
    gate_cone_runGCE hr gdef bnd
  have tagR := parentCmp_tag hacc
  obtain ⟨y, hy⟩ := hentry ``childAdd
    (fun L' _ hD ids len => parentCmp_entryWN L' hD tagR ids len)
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  exact ⟨M, envR, mF, hpost, hcache, tagR, y, hy,
    parentCmp_coneKC hcone tagR hy (fun v hv =>
      kidFacts_of_first' centry childAdd_fe_wf (by decide) hreal addSem v hv addSem_spec)⟩

/-! ## Sanity (independent of the theorems above): the stated body IS the
declaration's peel -/

#def_decl_value parentCmpValue of parentCmp

theorem parentCmp_peel :
    Sparkle.Compiler.Elab.mixedGatePeel parentCmpValue =
      some (parentCmpBinders, parentCmpBody) := rfl

end Sparkle.Tests.Compiler.GateConeCmpTest

#print axioms Sparkle.Tests.Compiler.GateConeCmpTest.parentCmp_tag
#print axioms Sparkle.Tests.Compiler.GateConeCmpTest.parentCmp_entryWN
#print axioms Sparkle.Tests.Compiler.GateConeCmpTest.parentCmp_gate_cone_runK'

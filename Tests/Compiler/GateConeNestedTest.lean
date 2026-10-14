import Tests.Compiler.GateConeEntryTest
import Tools.ShippingGateConeNested

/-! # `parentNested`: an instance leaf whose argument is an instance call (worker N, round 9)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeNestedTest`;
not in `Tests.AllTests`).

`parentNested a b := childAdd (childAdd a b) b`: binders `[dom, a, b]`; the
body is the built `nestedE` (`parentNested_peel`). As a cone it is the
one-leaf term `.bitsInput 8 0` whose leaf is the OUTER call; the outer call's
first argument is the INNER call, which has no world-free contract — so the
leaf is a `LeafKR` (`Tools.ShippingGateConeNested`), and the cone theorem is
`gate_cone_runGER`.

* tag: the inner call is on binders (`bvarCall ``childAdd [0, 1, 2]`); the
  gate refuses the body under any predicate that refuses the inner call
  (`hierInstRoot` asks the predicate of the inner call; every other disjunct
  that consults the predicate on the body is false by its closed spine), so
  `gate_leaf_tag'` gives the tag;
* entry existence: the root is the outer instance leaf (`inst_entryW`);
* the cache: ONE entry `y` of `childAdd` in `mF`; both calls instantiate it.
  The observation needs of `y` exactly the child facts at the two calls'
  values — `KidFacts (ownChild y) addSem ``childAdd 2 v y` at
  `v = .bits 8 (a + b)` (inner) and at `v = .bits 8 ((a + b) + b)` (outer) —
  both instances of the one premise `∀ v, v.kind.width = 8 → KidFacts …`,
  derived once from `RealChild` + `EntryDefines childAdd`.

Premises of `parentNested_gate_cone_runK'`: the run, `GateDefines` (NOT
ALLOWED, ruling pending, unchanged), `ChildBnd` (ALLOWED), `EntryDefines` of
`childAdd` (ALLOWED). -/
namespace Sparkle.Tests.Compiler.GateConeNestedTest
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
open Tools.ShippingGateDefines (GateDefines mixedGateCond)
open Tools.ShippingGateConeTag (bvarCall bvarCallE gateLeafSel_of gate_leaf_tag')
open Tools.ShippingEntrySoundness (RunsTo FExpr evalFE quoteDecl)
open Tools.ShippingChildInv (ChildBnd CacheInv Res RealChild RefLaws)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingFirstGateKid (ownChild kidFacts_of_first')

/-! ## The body -/

/-- `parentNested`'s body as the gate reads it (the built `parentNested_peel`). -/
abbrev parentNestedBody : Lean.Expr :=
  nestedE (inputExpr parentNestedBinders.length 0) (inputExpr parentNestedBinders.length 1)
    (inputExpr parentNestedBinders.length 2)

example : Sparkle.Compiler.Elab.mixedGatePeel parentNestedValue =
    some (parentNestedBinders, parentNestedBody) :=
  parentNested_peel

/-! ## The tag of the callee, from the gate's acceptance -/

/-- The inner call as the recogniser names it. -/
theorem parentNested_leaf_eq : bvarCallE ``childAdd [0, 1, 2] =
    instEN ``childAdd [] (inputExpr parentNestedBinders.length 0)
      ([1, 2].map (inputExpr parentNestedBinders.length)) := rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- **The gate refuses `parentNested`'s body under the predicate that refuses
its inner call** (every `isInst` elsewhere). The two disjuncts that consult
the predicate on the body itself: `unifiedInstanceRoot` is false by its
closed spine (the inner call is not a binder), `hierInstRoot` asks the
predicate of the inner call (false). The rest is evaluation. -/
theorem parentNested_leafSel : ∀ (isInst : Lean.Expr → Bool) (sc : Bool),
    mixedGateCond (fun e => !bvarCall ``childAdd [0, 1, 2] e && isInst e)
      (parentNestedBinders.map (·.2)).toArray parentNestedBody sc = false := by
  intro isInst sc
  have hs1 : (unifiedInstanceSpine (parentNestedBinders.map (·.2)).toArray parentNestedBody ||
      unifiedProjSpine (parentNestedBinders.map (·.2)).toArray parentNestedBody) = false := rfl
  have hs2 : hierInstSpine (fun e => !bvarCall ``childAdd [0, 1, 2] e && isInst e)
      (parentNestedBinders.map (·.2)).toArray parentNestedBody = false := rfl
  unfold mixedGateCond unifiedInstanceRoot hierInstRoot
  simp only [hs1, hs2, Bool.and_false, Bool.false_and]
  all_goals rfl

/-- **The callee is tagged at the run's environment.** -/
theorem parentNested_tag {envR : Lean.Environment}
    (hacc : ∃ dv : Lean.DefinitionVal, mixedCertifiedShape? false [] (.defnInfo dv)
      (Sparkle.Compiler.Elab.instancePredicate envR) =
        some (parentNestedBinders, parentNestedBody)) :
    Sparkle.Compiler.isHardwareModule envR ``childAdd = true := by
  have h0 := gateLeafSel_of (kinds := (parentNestedBinders.map (·.2)).toArray)
    (body := parentNestedBody) parentNested_leafSel
  rw [parentNested_leaf_eq] at h0
  exact gate_leaf_tag' (mn := ``childAdd) (lvls := [])
    (dE := inputExpr parentNestedBinders.length 0)
    (n := parentNestedBinders.length) (poss := [1, 2]) hacc (List.cons_ne_nil _ _) h0

/-! ## The cache entry exists -/

/-- **Every run of the translator on `parentNested`'s instantiated body ends
with `childAdd` in the child cache** (the root IS the outer instance leaf). -/
theorem parentNested_entryWN {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0)
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (ids : List FVarId) (len : ids.length = parentNestedBinders.length) :
    EntryWN L D (translateFuelFix (translateStep envR) translateFuelLimit)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentNestedBody) ``childAdd := by
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
  have hbody : instFVars ([i0, i1, i2].map Lean.Expr.fvar).toArray 0 parentNestedBody =
      instEN ``childAdd [] (.fvar i0)
        [instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2], .fvar i2] := rfl
  rw [hbody, hfl]
  intro mctx cctx hint top named ctx s t wire w0 w1 _ hw hd hr
  exact inst_entryW (tenv := envR) (mn := ``childAdd) (lvls := [])
    (dom := .fvar i0) (argsE := [instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2], .fvar i2])
    L hD (translateFuelLimit - 1) rfl rfl rfl tagR
    mctx cctx hint top named ctx s t wire w0 w1 hw hd hr

/-! ## The observation against a linked context -/

/-- What `M`'s linked evaluation against `children` observes: `parentNested`
(the text of `ParentMixObservesC`, at `parentNested`). -/
def ParentNestedObservesC (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (M : Sparkle.IR.AST.Module) : Prop :=
  ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
  ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) {D : DomainConfig}
    (aS bS : Signal D (BitVec 8)) (t : Nat) (mems : MEnv),
  let a := Tools.ShippingMixedEntrySoundness.start
    (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentNested)
  let p := Tools.ShippingMixedEntrySoundness.prepare bools bits
    (parentNestedBinders.zip [i0, i1, i2]) a
  Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
    (parentNestedBinders.zip [i0, i1, i2]) a →
  p.bits i1 = some ⟨8, aS.val t⟩ → p.bits i2 = some ⟨8, bS.val t⟩ →
  (∃ result, evalAssignsH (Tools.ShippingMixedEntrySoundness.moduleWidths M)
      children mems M.body initial = some result ∧
    result "out" = ((parentNested aS bS).val t).toNat) ∧
  InstsLinked children M

/-- **The pipeline cone over ANY linked context whose `childAdd` entry has the
cone's child facts** — at the inner call's value AND at the outer call's
value (the one entry `y`, two `KidFacts`). -/
theorem parentNested_coneKC {envR : Lean.Environment} {mF : Std.HashMap Lean.Name Res}
    {M : Sparkle.IR.AST.Module} {children : String → Option (Sparkle.IR.AST.Module × WEnv)}
    (P : HierConePreservesKR envR mF ``parentNested parentNestedBinders parentNestedBody M)
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    {y : Res} (hy : mF.get? ``childAdd = some y)
    (hkid : ∀ v : Value, v.kind.width = 8 → KidFacts children addSem ``childAdd 2 v y) :
    ParentNestedObservesC children M := by
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
  -- the inner call
  have innerArgsM : ∀ k (hk : k < [Lean.Expr.fvar i1, Lean.Expr.fvar i2].length)
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
  have innerSem : ChildSem.childSem ``childAdd
      [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)] =
      some (.bits 8 (aS.val t + bS.val t)) := by
    show (if ``childAdd = ``childAdd ∧
        [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)].map Value.kind =
          [.bits 8, .bits 8] then _ else none) = _
    rw [if_pos ⟨rfl, rfl⟩]
    rfl
  have innerM : Meaning (inputValues p.bools p.bits)
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
      (.bits 8 (aS.val t + bS.val t)) :=
    meaning_inst rfl rfl innerArgsM innerSem
  have innerK : LeafKR envR children addSem mF p.context (inputValues p.bools p.bits) mems initial
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
      (.bits 8 (aS.val t + bS.val t)) :=
    LeafKR.inst (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [.fvar i1, .fvar i2])
      (vs := [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)]) rfl rfl rfl tagR rfl
      (fun k hk hk' => by
        rcases k with _ | k
        · exact LeafKR.leaf (by
            intro we fuel
            exact input_contract_fuel hA fuel)
        · rcases k with _ | k
          · exact LeafKR.leaf (by
              intro we fuel
              exact input_contract_fuel hB fuel)
          · exact absurd hk (by simp))
      innerArgsM innerSem
      (fun y' hy' => by
        rw [hy] at hy'
        cases hy'
        exact hkid _ rfl)
  -- the outer call: its first argument is the inner call
  have outerArgsM : ∀ k
      (hk : k < [instEN ``childAdd [] (Lean.Expr.fvar i0)
        [Lean.Expr.fvar i1, Lean.Expr.fvar i2], Lean.Expr.fvar i2].length)
      (hk' : k < [Value.bits 8 (aS.val t + bS.val t), Value.bits 8 (bS.val t)].length),
      Meaning (inputValues p.bools p.bits)
        ([instEN ``childAdd [] (Lean.Expr.fvar i0)
          [Lean.Expr.fvar i1, Lean.Expr.fvar i2], Lean.Expr.fvar i2][k]'hk)
        ([Value.bits 8 (aS.val t + bS.val t), Value.bits 8 (bS.val t)][k]'hk') := by
    intro k hk hk'
    rcases k with _ | k
    · exact innerM
    · rcases k with _ | k
      · exact .input rfl hB
      · exact absurd hk (by simp)
  have outerSem : ChildSem.childSem ``childAdd
      [Value.bits 8 (aS.val t + bS.val t), Value.bits 8 (bS.val t)] =
      some (.bits 8 (BitVec.ofNat 8 ((aS.val t + bS.val t).toNat + (bS.val t).toNat))) := by
    show (if ``childAdd = ``childAdd ∧
        [Value.bits 8 (aS.val t + bS.val t), Value.bits 8 (bS.val t)].map Value.kind =
          [.bits 8, .bits 8] then _ else none) = _
    rw [if_pos ⟨rfl, rfl⟩]
    rfl
  have leafM : LeafMeaning addSem (inputValues p.bools p.bits)
      (instEN ``childAdd [] (.fvar i0)
        [instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2], .fvar i2])
      (.bits 8 (BitVec.ofNat 8 ((aS.val t + bS.val t).toNat + (bS.val t).toNat))) :=
    meaning_inst rfl rfl outerArgsM outerSem
  have outerK : LeafKR envR children addSem mF p.context (inputValues p.bools p.bits) mems initial
      (instEN ``childAdd [] (.fvar i0)
        [instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2], .fvar i2])
      (.bits 8 (BitVec.ofNat 8 ((aS.val t + bS.val t).toNat + (bS.val t).toNat))) :=
    LeafKR.inst (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
      (argsE := [instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2], .fvar i2])
      (vs := [Value.bits 8 (aS.val t + bS.val t), Value.bits 8 (bS.val t)]) rfl rfl rfl tagR rfl
      (fun k hk hk' => by
        rcases k with _ | k
        · exact innerK
        · rcases k with _ | k
          · exact LeafKR.leaf (by
              intro we fuel
              exact input_contract_fuel hB fuel)
          · exact absurd hk (by simp))
      outerArgsM outerSem
      (fun y' hy' => by
        rw [hy] at hy'
        cases hy'
        exact hkid _ rfl)
  have value := Q (.fvar i0) 0 1 (fun _ => 8) (fun _ => .fvar i0)
    (fun _ => instEN ``childAdd [] (.fvar i0)
      [instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2], .fvar i2]) (fun _ => false)
    (fun _ w => BitVec.ofNat w ((aS.val t + bS.val t).toNat + (bS.val t).toNat))
    (.bitsInput 8 0) ⟨by decide, rfl, by decide⟩ rfl
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => by
      rcases j with _ | j
      · exact leafM
      · exact absurd hj (by simp))
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => by
      rcases j with _ | j
      · exact outerK
      · exact absurd hj (by simp))
    rfl
  obtain ⟨⟨result, hev, hout⟩, linked⟩ := value
  refine ⟨⟨result, hev, ?_⟩, linked⟩
  rw [hout]
  show (BitVec.ofNat 8 ((aS.val t + bS.val t).toNat + (bS.val t).toNat)).toNat = _
  rfl

/-! ## The full entry -/

/-- **`parentNested`: the cache entry exists and the observation holds
against it.** Binders: the run, `GateDefines` (NOT ALLOWED, ruling pending —
unchanged), `ChildBnd` (ALLOWED), `EntryDefines` of `childAdd` (ALLOWED). The
two calls of `childAdd` instantiate the ONE entry `y`. -/
theorem parentNested_gate_cone_runK' {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentNested) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentNested parentNestedBinders parentNestedBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      ∃ y : Res, mF.get? ``childAdd = some y ∧ ParentNestedObservesC (ownChild y) M := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone, hentry⟩ :=
    gate_cone_runGER hr gdef bnd
  have tagR := parentNested_tag hacc
  obtain ⟨y, hy⟩ := hentry ``childAdd
    (fun L' _ hD ids len => parentNested_entryWN L' hD tagR ids len)
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  exact ⟨M, envR, mF, hpost, hcache, tagR, y, hy,
    parentNested_coneKC hcone tagR hy (fun v hv =>
      kidFacts_of_first' centry childAdd_fe_wf (by decide) hreal addSem v hv addSem_spec)⟩

end Sparkle.Tests.Compiler.GateConeNestedTest

#print axioms Tools.ShippingGateParentRun.inst_leaf_contractWA
#print axioms Tools.ShippingGateParentRun.leafKR_contractW
#print axioms Tools.ShippingGateParentRun.gate_cone_runGER
#print axioms Sparkle.Tests.Compiler.GateConeNestedTest.parentNested_tag
#print axioms Sparkle.Tests.Compiler.GateConeNestedTest.parentNested_entryWN
#print axioms Sparkle.Tests.Compiler.GateConeNestedTest.parentNested_gate_cone_runK'

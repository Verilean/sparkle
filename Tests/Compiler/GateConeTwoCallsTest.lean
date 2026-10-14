import Tests.Compiler.GateConeEntryTest

/-! # `parentTwoCalls`: two instance leaves, BOTH argument orders (worker N, round 8)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeTwoCallsTest`;
not in `Tests.AllTests`).

`parentTwoCalls a b := childAdd a b + childAdd b a`: a canonical `+` over two
instance leaves of the SAME callee with the arguments in both orders. The
shape of `parentMix_gate_cone_runK'` (round 6):

* both leaves read the SAME `mF` entry `y` of `childAdd` (`InstLeafK` asks
  `KidFacts` of `mF`'s entry, which does not depend on the arguments); the
  argument ORDER lives in the leaf's own value: leaf 1 is `childSem
  ``childAdd [b, a]` (`hsem1`), its arguments `[b, a]` (`hargs1`), so the
  observation is `(childAdd a b + childAdd b a)` — i.e.
  `(parentTwoCalls aS bS).val t` — not `2·(a+b)` by accident of the proof;
* the tag: the gate refuses the body under any predicate refusing the leaf
  `childAdd b a` (`parentTwoCalls_leafSel`). With TWO leaves, the predicate
  is not closed on the other leaf: `gateLeafSel_of2` splits on the value
  `b0` the predicate gives the other leaf (`cond` on a second recogniser),
  and the per-declaration evaluation is `rfl` for both `b0`;
* entry existence: `binary_entryWN` over the FIRST leaf (`inst_entryW`).

Premises of `parentTwoCalls_gate_cone_runK'`: the run, `GateDefines` (NOT
ALLOWED, ruling pending, unchanged), `ChildBnd` (ALLOWED), `EntryDefines` of
`childAdd` (ALLOWED). A peel sanity check (`#def_decl_value` + `rfl`) is at
the END of the file, independent of the theorems (drop it if the reflection
of the value fails). -/
namespace Sparkle.Tests.Compiler.GateConeTwoCallsTest
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

def parentTwoCallsBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`a, .bits 8), (`b, .bits 8)]

/-- The cone's BitVec leaves: leaf 0 is `childAdd a b`, leaf 1 is
`childAdd b a`. -/
def twoCallsLeaf (dom : Lean.Expr) (a b : Lean.Expr) (j : Nat) : Lean.Expr :=
  if j = 0 then instEN ``childAdd [] dom [a, b] else instEN ``childAdd [] dom [b, a]

/-- `parentTwoCalls`'s body as the gate reads it (`parentMixTerm`: leaf 0 +
leaf 1). -/
abbrev parentTwoCallsBody : Lean.Expr :=
  quote (inputExpr parentTwoCallsBinders.length 0)
    (fun _ => inputExpr parentTwoCallsBinders.length 0)
    (twoCallsLeaf (inputExpr parentTwoCallsBinders.length 0)
      (inputExpr parentTwoCallsBinders.length 1) (inputExpr parentTwoCallsBinders.length 2))
    parentMixTerm

/-! ## The tag of the callee, from the gate's acceptance -/

/-- **`GateLeafSel` for a body with TWO recognised calls**: the predicate
refuses the leaf `bvarCallE mn is`; on the other call `bvarCallE mn js` it
answers some `b0`; elsewhere it is `isInst`. If the gate's condition is false
for every `isInst` and every `b0`, the leaf is selected. -/
theorem gateLeafSel_of2 {kinds : Array MixedGateBinder} {body : Lean.Expr} {mn : Name}
    {is js : List Nat}
    (hc : ∀ (isInst : Lean.Expr → Bool) (b0 sc : Bool),
      Tools.ShippingGateDefines.mixedGateCond
        (fun e => cond (Tools.ShippingGateConeTag.bvarCall mn js e) b0
          (!Tools.ShippingGateConeTag.bvarCall mn is e && isInst e))
        kinds body sc = false) :
    Tools.ShippingGateConeTag.GateLeafSel kinds body
      (Tools.ShippingGateConeTag.bvarCallE mn is) := by
  intro isInst sc hI
  have heq : isInst = fun e => cond (Tools.ShippingGateConeTag.bvarCall mn js e)
      (isInst (Tools.ShippingGateConeTag.bvarCallE mn js))
      (!Tools.ShippingGateConeTag.bvarCall mn is e && isInst e) := by
    funext e
    show isInst e = cond (Tools.ShippingGateConeTag.bvarCall mn js e)
      (isInst (Tools.ShippingGateConeTag.bvarCallE mn js))
      (!Tools.ShippingGateConeTag.bvarCall mn is e && isInst e)
    cases hj : Tools.ShippingGateConeTag.bvarCall mn js e with
    | true =>
      have he := Tools.ShippingGateConeTag.bvarCall_sound mn js e hj
      subst he
      rfl
    | false =>
      cases hi : Tools.ShippingGateConeTag.bvarCall mn is e with
      | false => rfl
      | true =>
        have he := Tools.ShippingGateConeTag.bvarCall_sound mn is e hi
        subst he
        rw [hI]
        try rfl
  have h2 : Tools.ShippingGateDefines.mixedGateCond isInst kinds body sc =
      Tools.ShippingGateDefines.mixedGateCond
        (fun e => cond (Tools.ShippingGateConeTag.bvarCall mn js e)
          (isInst (Tools.ShippingGateConeTag.bvarCallE mn js))
          (!Tools.ShippingGateConeTag.bvarCall mn is e && isInst e))
        kinds body sc :=
    congrArg (fun P => Tools.ShippingGateDefines.mixedGateCond P kinds body sc) heq
  rw [h2]
  exact hc isInst (isInst (Tools.ShippingGateConeTag.bvarCallE mn js)) sc

/-- Leaf 1 (`childAdd b a`) as the recogniser names it. -/
theorem twoCalls_leaf1_eq : Tools.ShippingGateConeTag.bvarCallE ``childAdd [1, 0, 2] =
    instEN ``childAdd [] (inputExpr parentTwoCallsBinders.length 0)
      ([2, 1].map (inputExpr parentTwoCallsBinders.length)) := rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- **The gate refuses `parentTwoCalls`'s body under any predicate that
refuses `childAdd b a`**, whatever it answers on `childAdd a b` (`b0`). The
two disjuncts that consult the predicate on the body itself are false by
their (closed) spines (`hierInstSpine` reads leaf 1 first: refused); the rest
is evaluation, per value of `b0`. -/
theorem parentTwoCalls_leafSel : ∀ (isInst : Lean.Expr → Bool) (b0 sc : Bool),
    Tools.ShippingGateDefines.mixedGateCond
      (fun e => cond (Tools.ShippingGateConeTag.bvarCall ``childAdd [0, 1, 2] e) b0
        (!Tools.ShippingGateConeTag.bvarCall ``childAdd [1, 0, 2] e && isInst e))
      (parentTwoCallsBinders.map (·.2)).toArray parentTwoCallsBody sc = false := by
  intro isInst b0 sc
  have hs1 : (Sparkle.Compiler.Elab.unifiedInstanceSpine
        (parentTwoCallsBinders.map (·.2)).toArray parentTwoCallsBody ||
      Sparkle.Compiler.Elab.unifiedProjSpine
        (parentTwoCallsBinders.map (·.2)).toArray parentTwoCallsBody) = false := rfl
  have hs2 : Sparkle.Compiler.Elab.hierInstSpine
      (fun e => cond (Tools.ShippingGateConeTag.bvarCall ``childAdd [0, 1, 2] e) b0
        (!Tools.ShippingGateConeTag.bvarCall ``childAdd [1, 0, 2] e && isInst e))
      (parentTwoCallsBinders.map (·.2)).toArray parentTwoCallsBody = false := rfl
  unfold Tools.ShippingGateDefines.mixedGateCond Sparkle.Compiler.Elab.unifiedInstanceRoot
    Sparkle.Compiler.Elab.hierInstRoot
  simp only [hs1, hs2, Bool.and_false, Bool.false_and]
  all_goals (cases b0 <;> rfl)

/-- **The callee is tagged at the run's environment**, from the gate's
acceptance at that environment. -/
theorem parentTwoCalls_tag {envR : Lean.Environment}
    (hacc : ∃ dv : Lean.DefinitionVal, mixedCertifiedShape? false [] (.defnInfo dv)
      (Sparkle.Compiler.Elab.instancePredicate envR) = some (parentTwoCallsBinders, parentTwoCallsBody)) :
    Sparkle.Compiler.isHardwareModule envR ``childAdd = true := by
  have h0 := gateLeafSel_of2 (kinds := (parentTwoCallsBinders.map (·.2)).toArray)
    (body := parentTwoCallsBody) (mn := ``childAdd) (is := [1, 0, 2]) (js := [0, 1, 2])
    parentTwoCalls_leafSel
  rw [twoCalls_leaf1_eq] at h0
  exact Tools.ShippingGateConeTag.gate_leaf_tag' (mn := ``childAdd) (lvls := [])
    (dE := inputExpr parentTwoCallsBinders.length 0)
    (n := parentTwoCallsBinders.length) (poss := [2, 1]) hacc (List.cons_ne_nil _ _) h0

/-! ## The cache entry exists -/

/-- **Every lookup-free run of the translator on `parentTwoCalls`'s
instantiated body ends with `childAdd` in the child cache** (via the first
leaf). -/
theorem parentTwoCalls_entryWN {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0)
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (ids : List FVarId) (len : ids.length = parentTwoCallsBinders.length) :
    EntryWN L D (translateFuelFix (translateStep envR) translateFuelLimit)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 parentTwoCallsBody) ``childAdd := by
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
  have hbody : instFVars ([i0, i1, i2].map Lean.Expr.fvar).toArray 0 parentTwoCallsBody =
      quote (.fvar i0) (fun _ => .fvar i0) (twoCallsLeaf (.fvar i0) (.fvar i1) (.fvar i2))
        parentMixTerm := rfl
  have ck := Tools.ShippingEntrySoundness.op_checks .add (.fvar i0)
    (twoCallsLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
    (twoCallsLeaf (.fvar i0) (.fvar i1) (.fvar i2) 1) 8
  rw [hbody, hfl]
  show EntryWN L D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1 + 1))
    (Tools.ShippingEntrySoundness.binE (.fvar i0) 8 .add
      (twoCallsLeaf (.fvar i0) (.fvar i1) (.fvar i2) 0)
      (twoCallsLeaf (.fvar i0) (.fvar i1) (.fvar i2) 1)) ``childAdd
  refine binary_entryWN (tenv := envR) L hD (translateFuelLimit - 2 + 1) ck.1 ck.2.1 ck.2.2.1
    ck.2.2.2.1 (Or.inl ?_)
  rw [ck.2.2.2.2.1]
  show EntryW L D (translateFuelFix (translateStep envR) (translateFuelLimit - 2 + 1))
    (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2]) ``childAdd
  exact inst_entryW (tenv := envR) (mn := ``childAdd) (lvls := []) (dom := .fvar i0)
    (argsE := [.fvar i1, .fvar i2]) L hD (translateFuelLimit - 2) rfl rfl rfl tagR

/-! ## The observation against a linked context -/

/-- What `M`'s linked evaluation, against the context `children`, observes of
`parentTwoCalls`. -/
def ParentTwoCallsObservesC (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (M : Sparkle.IR.AST.Module) : Prop :=
  ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
  ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) {D : DomainConfig}
    (aS bS : Signal D (BitVec 8)) (t : Nat) (mems : MEnv),
  let a := Tools.ShippingMixedEntrySoundness.start
    (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``parentTwoCalls)
  let p := Tools.ShippingMixedEntrySoundness.prepare bools bits
    (parentTwoCallsBinders.zip [i0, i1, i2]) a
  Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
    (parentTwoCallsBinders.zip [i0, i1, i2]) a →
  p.bits i1 = some ⟨8, aS.val t⟩ → p.bits i2 = some ⟨8, bS.val t⟩ →
  (∃ result, evalAssignsH (Tools.ShippingMixedEntrySoundness.moduleWidths M)
      children mems M.body initial = some result ∧
    result "out" = ((parentTwoCalls aS bS).val t).toNat) ∧
  InstsLinked children M

/-- **The cone over ANY linked context whose `childAdd` entry has the cone's
child facts** — both leaves read the one entry `y`. -/
theorem parentTwoCalls_coneKC {envR : Lean.Environment} {mF : Std.HashMap Lean.Name Res}
    {M : Sparkle.IR.AST.Module} {children : String → Option (Sparkle.IR.AST.Module × WEnv)}
    (P : HierConePreservesK envR mF ``parentTwoCalls parentTwoCallsBinders parentTwoCallsBody M)
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    {y : Res} (hy : mF.get? ``childAdd = some y)
    (hkid : ∀ v : Value, v.kind.width = 8 → KidFacts children addSem ``childAdd 2 v y) :
    ParentTwoCallsObservesC children M := by
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
  -- leaf 0: `childAdd a b`
  have hargs0 : ∀ k (hk : k < [Lean.Expr.fvar i1, Lean.Expr.fvar i2].length)
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
  -- leaf 1: `childAdd b a` — the arguments in the OTHER order
  have hargs1 : ∀ k (hk : k < [Lean.Expr.fvar i2, Lean.Expr.fvar i1].length)
      (hk' : k < [Value.bits 8 (bS.val t), Value.bits 8 (aS.val t)].length),
      Meaning (inputValues p.bools p.bits)
        ([Lean.Expr.fvar i2, Lean.Expr.fvar i1][k]'hk)
        ([Value.bits 8 (bS.val t), Value.bits 8 (aS.val t)][k]'hk') := by
    intro k hk hk'
    rcases k with _ | k
    · exact .input rfl hB
    · rcases k with _ | k
      · exact .input rfl hA
      · exact absurd hk (by simp)
  have hsem0 : ChildSem.childSem ``childAdd
      [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)] =
      some (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) := by
    show (if ``childAdd = ``childAdd ∧
        [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)].map Value.kind =
          [.bits 8, .bits 8] then _ else none) = _
    rw [if_pos ⟨rfl, rfl⟩]
    rfl
  have hsem1 : ChildSem.childSem ``childAdd
      [Value.bits 8 (bS.val t), Value.bits 8 (aS.val t)] =
      some (.bits 8 (BitVec.ofNat 8 ((bS.val t).toNat + (aS.val t).toNat))) := by
    show (if ``childAdd = ``childAdd ∧
        [Value.bits 8 (bS.val t), Value.bits 8 (aS.val t)].map Value.kind =
          [.bits 8, .bits 8] then _ else none) = _
    rw [if_pos ⟨rfl, rfl⟩]
    rfl
  have leafM0 : LeafMeaning addSem (inputValues p.bools p.bits)
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
      (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) :=
    meaning_inst rfl rfl hargs0 hsem0
  have leafM1 : LeafMeaning addSem (inputValues p.bools p.bits)
      (instEN ``childAdd [] (.fvar i0) [.fvar i2, .fvar i1])
      (.bits 8 (BitVec.ofNat 8 ((bS.val t).toNat + (aS.val t).toNat))) :=
    meaning_inst rfl rfl hargs1 hsem1
  -- the run's own child, ONE entry for both leaves
  have kid0 : KidFacts children addSem ``childAdd
      [Lean.Expr.fvar i1, Lean.Expr.fvar i2].length
      (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) y :=
    hkid _ rfl
  have kid1 : KidFacts children addSem ``childAdd
      [Lean.Expr.fvar i2, Lean.Expr.fvar i1].length
      (.bits 8 (BitVec.ofNat 8 ((bS.val t).toNat + (aS.val t).toNat))) y :=
    hkid _ rfl
  have leafK0 : LeafK envR children addSem mF p.context
      (inputValues p.bools p.bits) mems initial
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
      (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) := by
    refine Or.inr ⟨``childAdd, [], .fvar i0, [.fvar i1, .fvar i2],
      [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)], rfl, rfl, rfl, rfl, tagR, rfl,
      ?_, hsem0, ?_⟩
    · intro k hk hk' we fuel
      rcases k with _ | k
      · exact input_contract_fuel hA fuel
      · rcases k with _ | k
        · exact input_contract_fuel hB fuel
        · exact absurd hk (by simp)
    · intro y' hy'
      rw [hy] at hy'
      cases hy'
      exact kid0
  have leafK1 : LeafK envR children addSem mF p.context
      (inputValues p.bools p.bits) mems initial
      (instEN ``childAdd [] (.fvar i0) [.fvar i2, .fvar i1])
      (.bits 8 (BitVec.ofNat 8 ((bS.val t).toNat + (aS.val t).toNat))) := by
    refine Or.inr ⟨``childAdd, [], .fvar i0, [.fvar i2, .fvar i1],
      [Value.bits 8 (bS.val t), Value.bits 8 (aS.val t)], rfl, rfl, rfl, rfl, tagR, rfl,
      ?_, hsem1, ?_⟩
    · intro k hk hk' we fuel
      rcases k with _ | k
      · exact input_contract_fuel hB fuel
      · rcases k with _ | k
        · exact input_contract_fuel hA fuel
        · exact absurd hk (by simp)
    · intro y' hy'
      rw [hy] at hy'
      cases hy'
      exact kid1
  have value := Q (.fvar i0) 0 2 (fun _ => 8) (fun _ => .fvar i0)
    (twoCallsLeaf (.fvar i0) (.fvar i1) (.fvar i2)) (fun _ => false)
    (fun j w => if j = 0 then BitVec.ofNat w ((aS.val t).toNat + (bS.val t).toNat)
      else BitVec.ofNat w ((bS.val t).toNat + (aS.val t).toNat))
    parentMixTerm parentMix_wf parentMix_cfrag
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => by
      rcases j with _ | j
      · exact leafM0
      · rcases j with _ | j
        · exact leafM1
        · exact absurd hj (by simp))
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => by
      rcases j with _ | j
      · exact leafK0
      · rcases j with _ | j
        · exact leafK1
        · exact absurd hj (by simp))
    rfl
  obtain ⟨⟨result, hev, hout⟩, linked⟩ := value
  refine ⟨⟨result, hev, ?_⟩, linked⟩
  rw [hout]
  show (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat) +
    BitVec.ofNat 8 ((bS.val t).toNat + (aS.val t).toNat)).toNat = _
  rfl

/-! ## The full entry -/

/-- **`parentTwoCalls`: the cache entry exists and the observation holds
against it.** Binders: the run, `GateDefines` (NOT ALLOWED, ruling pending —
unchanged), `ChildBnd` (ALLOWED), `EntryDefines` of `childAdd` (ALLOWED). -/
theorem parentTwoCalls_gate_cone_runK' {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``parentTwoCalls) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``parentTwoCalls parentTwoCallsBinders
      parentTwoCallsBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      ∃ y : Res, mF.get? ``childAdd = some y ∧ ParentTwoCallsObservesC (ownChild y) M := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone, hentry⟩ :=
    gate_cone_runGE hr gdef bnd
  have tagR := parentTwoCalls_tag hacc
  obtain ⟨y, hy⟩ := hentry ``childAdd
    (fun L' _ hD ids len => parentTwoCalls_entryWN L' hD tagR ids len)
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  exact ⟨M, envR, mF, hpost, hcache, tagR, y, hy,
    parentTwoCalls_coneKC hcone tagR hy (fun v hv =>
      kidFacts_of_first' centry childAdd_fe_wf (by decide) hreal addSem v hv addSem_spec)⟩

/-! ## Sanity (independent of the theorems above): the stated body IS the
declaration's peel -/

#def_decl_value parentTwoCallsValue of parentTwoCalls

theorem parentTwoCalls_peel :
    Sparkle.Compiler.Elab.mixedGatePeel parentTwoCallsValue =
      some (parentTwoCallsBinders, parentTwoCallsBody) := rfl

end Sparkle.Tests.Compiler.GateConeTwoCallsTest

#print axioms Sparkle.Tests.Compiler.GateConeTwoCallsTest.gateLeafSel_of2
#print axioms Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCalls_tag
#print axioms Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCalls_entryWN
#print axioms Sparkle.Tests.Compiler.GateConeTwoCallsTest.parentTwoCalls_gate_cone_runK'

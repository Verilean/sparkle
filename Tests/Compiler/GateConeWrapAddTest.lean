import Tests.Compiler.GateConeEntryTest

/-! # `wrapAdd`: a single-leaf cone at a CONSTANT domain (worker N, round 8)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeWrapAddTest`;
not in `Tests.AllTests`).

`wrapAdd a b := childAdd a b` at `defaultDomain`: binders `[a, b]` (NO domain
binder); the body is the call itself, `wrapE (bvar 1) (bvar 0)` (the built
`wrapAdd_peel`). As a cone it is the one-leaf term `.bitsInput 8 0` whose
leaf is the whole body.

How `instEN` reads the constant domain: `instEN mn lvls dom args` is
`args.foldl .app (.app (.const mn lvls) dom)` — the FIRST argument slot is
`dom`, whatever it is. `wrapE a b = instEN ``childAdd []
(.const ``defaultDomain []) [a, b]`: the constant fills the domain slot and
`argsE = [a, b]`, so `argsE.length = 2 = childAdd`'s data inputs (the
`KidFacts` length fact `y.1.inputs.length = argsE.length` holds). Contrast
`wrapPick` (round-7 table): `pick` has no domain binder, so `instEN` would
read its first DATA argument as the domain.

* tag: `GateLeafSel` with the leaf = the body. The recogniser `bvarCall`
  (round 4) only names calls on bound variables (domain a bvar), so a twin
  `domCall` / `domCallE` / `domCall_sound` (head applied to a CONSTANT domain,
  then bound variables) and `gateLeafSel_ofD` are added here; the
  per-declaration evaluation is `rfl` (the predicate refuses the body
  itself, and no disjunct consults it anywhere else first);
* entry existence: the root is the instance leaf (`inst_entryW`; `EntryW`
  implies `EntryWN`).

Premises of `wrapAdd_gate_cone_runK'`: the run, `GateDefines` (NOT ALLOWED,
ruling pending, unchanged), `ChildBnd` (ALLOWED), `EntryDefines` of
`childAdd` (ALLOWED). The body is the built peel (`wrapAdd_peel`). -/
namespace Sparkle.Tests.Compiler.GateConeWrapAddTest
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

/-- `wrapAdd`'s body as the gate reads it (the built `wrapAdd_peel`). -/
abbrev wrapAddBody : Lean.Expr :=
  wrapE (inputExpr wrapAddBinders.length 0) (inputExpr wrapAddBinders.length 1)

example : Sparkle.Compiler.Elab.mixedGatePeel wrapAddValue = some (wrapAddBinders, wrapAddBody) :=
  wrapAdd_peel

/-! ## A recogniser of a call at a constant domain -/

/-- `.const mn []` applied to the constant `.const dn []`, then to the bound
variables `is` (LAST argument first, as `bvarCallE`). -/
def domCallE (mn dn : Name) : List Nat → Lean.Expr
  | [] => .app (.const mn []) (.const dn [])
  | i :: is => .app (domCallE mn dn is) (.bvar i)

/-- A kernel-reducible recogniser of `domCallE mn dn is`. -/
def domCall (mn dn : Name) : List Nat → Lean.Expr → Bool
  | [], .app (.const n us) (.const d ds) =>
    (decide (n = mn) && us.isEmpty) && (decide (d = dn) && ds.isEmpty)
  | i :: is, .app f (.bvar k) => decide (k = i) && domCall mn dn is f
  | _, _ => false

/-- The recogniser is sound for equality (the text of `bvarCall_sound`). -/
theorem domCall_sound (mn dn : Name) :
    ∀ (is : List Nat) (e : Lean.Expr), domCall mn dn is e = true → e = domCallE mn dn is
  | [], e, h => by
    cases e
    case app f a =>
      cases f
      case const n us =>
        cases a
        case const d ds =>
          simp only [domCall, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
          obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
          rw [h1, h2, h3, h4]
          try rfl
        all_goals (first | cases h | (simp [domCall] at h))
      all_goals (first | cases h | (simp [domCall] at h))
    all_goals (first | cases h | (simp [domCall] at h))
  | i :: is, e, h => by
    cases e
    case app f a =>
      cases a
      case bvar k =>
        simp only [domCall, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        subst h1
        rw [domCall_sound mn dn is f h2]
        try rfl
      all_goals (first | cases h | (simp [domCall] at h))
    all_goals (first | cases h | (simp [domCall] at h))

/-- **`GateLeafSel` from a closed evaluation**, for a leaf at a constant
domain (the text of `gateLeafSel_of`). -/
theorem gateLeafSel_ofD {kinds : Array MixedGateBinder} {body : Lean.Expr} {mn dn : Name}
    {is : List Nat}
    (hc : ∀ (isInst : Lean.Expr → Bool) (sc : Bool),
      Tools.ShippingGateDefines.mixedGateCond (fun e => !domCall mn dn is e && isInst e)
        kinds body sc = false) :
    Tools.ShippingGateConeTag.GateLeafSel kinds body (domCallE mn dn is) := by
  intro isInst sc hI
  have heq : (fun e => !domCall mn dn is e && isInst e) = isInst := by
    funext e
    show (!domCall mn dn is e && isInst e) = isInst e
    cases ht : domCall mn dn is e with
    | false => rfl
    | true =>
      have he := domCall_sound mn dn is e ht
      subst he
      rw [hI]
      try rfl
  rw [← heq]
  exact hc isInst sc

/-! ## The tag of the callee, from the gate's acceptance -/

/-- The body as the recogniser names it. -/
theorem wrapAdd_leaf_eq :
    domCallE ``childAdd ``Sparkle.Core.Domain.defaultDomain [0, 1] =
      instEN ``childAdd [] (.const ``Sparkle.Core.Domain.defaultDomain [])
        ([0, 1].map (inputExpr wrapAddBinders.length)) := rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- **The gate refuses `wrapAdd`'s body under any predicate refusing the
body** — by evaluation: every disjunct that consults the predicate consults
it on the body first. -/
theorem wrapAdd_leafSel : ∀ (isInst : Lean.Expr → Bool) (sc : Bool),
    Tools.ShippingGateDefines.mixedGateCond
      (fun e => !domCall ``childAdd ``Sparkle.Core.Domain.defaultDomain [0, 1] e && isInst e)
      (wrapAddBinders.map (·.2)).toArray wrapAddBody sc = false := by
  intro isInst sc
  rfl

/-- **The callee is tagged at the run's environment.** -/
theorem wrapAdd_tag {envR : Lean.Environment}
    (hacc : ∃ dv : Lean.DefinitionVal, mixedCertifiedShape? false [] (.defnInfo dv)
      (Sparkle.Compiler.Elab.instancePredicate envR) = some (wrapAddBinders, wrapAddBody)) :
    Sparkle.Compiler.isHardwareModule envR ``childAdd = true := by
  have h0 := gateLeafSel_ofD (kinds := (wrapAddBinders.map (·.2)).toArray)
    (body := wrapAddBody) wrapAdd_leafSel
  rw [wrapAdd_leaf_eq] at h0
  exact Tools.ShippingGateConeTag.gate_leaf_tag' (mn := ``childAdd) (lvls := [])
    (dE := .const ``Sparkle.Core.Domain.defaultDomain [])
    (n := wrapAddBinders.length) (poss := [0, 1]) hacc (List.cons_ne_nil _ _) h0

/-! ## The cache entry exists -/

/-- **Every run of the translator on `wrapAdd`'s instantiated body ends with
`childAdd` in the child cache** (the root IS the instance leaf). -/
theorem wrapAdd_entryWN {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0)
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    (ids : List FVarId) (len : ids.length = wrapAddBinders.length) :
    EntryWN L D (translateFuelFix (translateStep envR) translateFuelLimit)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapAddBody) ``childAdd := by
  have len2 : ids.length = 2 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len2
  rcases ids with _ | ⟨i1, ids⟩
  · cases len2
  rcases ids with _ | ⟨i2, ids⟩
  rotate_left
  · simp at len2
  have h1 : 1 ≤ translateFuelLimit := by
    first
      | decide
      | exact Nat.le_of_ble_eq_true rfl
  have hfl : translateFuelLimit = (translateFuelLimit - 1) + 1 := by
    first
      | omega
      | exact (Nat.sub_add_cancel h1).symm
  have hbody : instFVars ([i0, i1].map Lean.Expr.fvar).toArray 0 wrapAddBody =
      instEN ``childAdd [] (.const ``Sparkle.Core.Domain.defaultDomain [])
        [.fvar i0, .fvar i1] := rfl
  rw [hbody, hfl]
  intro mctx cctx hint top named ctx s t wire w0 w1 _ hw hd hr
  exact inst_entryW (tenv := envR) (mn := ``childAdd) (lvls := [])
    (dom := .const ``Sparkle.Core.Domain.defaultDomain []) (argsE := [.fvar i0, .fvar i1])
    L hD (translateFuelLimit - 1) rfl rfl rfl tagR
    mctx cctx hint top named ctx s t wire w0 w1 hw hd hr

/-! ## The observation against a linked context -/

def WrapAddObservesC (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (M : Sparkle.IR.AST.Module) : Prop :=
  ∃ (i0 i1 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
  ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) (aS bS : Signal defaultDomain (BitVec 8)) (t : Nat) (mems : MEnv),
  let a := Tools.ShippingMixedEntrySoundness.start
    (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapAdd)
  let p := Tools.ShippingMixedEntrySoundness.prepare bools bits
    (wrapAddBinders.zip [i0, i1]) a
  Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
    (wrapAddBinders.zip [i0, i1]) a →
  p.bits i0 = some ⟨8, aS.val t⟩ → p.bits i1 = some ⟨8, bS.val t⟩ →
  (∃ result, evalAssignsH (Tools.ShippingMixedEntrySoundness.moduleWidths M)
      children mems M.body initial = some result ∧
    result "out" = ((wrapAdd aS bS).val t).toNat) ∧
  InstsLinked children M

/-- **The single-leaf cone over ANY linked context whose `childAdd` entry has
the cone's child facts.** -/
theorem wrapAdd_coneKC {envR : Lean.Environment} {mF : Std.HashMap Lean.Name Res}
    {M : Sparkle.IR.AST.Module} {children : String → Option (Sparkle.IR.AST.Module × WEnv)}
    (P : HierConePreservesK envR mF ``wrapAdd wrapAddBinders wrapAddBody M)
    (tagR : Sparkle.Compiler.isHardwareModule envR ``childAdd = true)
    {y : Res} (hy : mF.get? ``childAdd = some y)
    (hkid : ∀ v : Value, v.kind.width = 8 → KidFacts children addSem ``childAdd 2 v y) :
    WrapAddObservesC children M := by
  obtain ⟨ids, nd, len, cache, P⟩ := P
  have len2 : ids.length = 2 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len2
  rcases ids with _ | ⟨i1, ids⟩
  · cases len2
  rcases ids with _ | ⟨i2, ids⟩
  rotate_left
  · simp at len2
  refine ⟨i0, i1, cache, ?_⟩
  intro bools bits initial aS bS t mems a p adm ha0 hb0
  obtain ⟨separate, Q⟩ := P children addSem bools bits initial mems adm
  have hA : inputValues p.bools p.bits i0 = some (.bits 8 (aS.val t)) :=
    inputValues_bits separate ha0
  have hB : inputValues p.bools p.bits i1 = some (.bits 8 (bS.val t)) :=
    inputValues_bits separate hb0
  letI : HierCtx := hierLink children
  letI : ChildSem := addSem
  have hargsM : ∀ k (hk : k < [Lean.Expr.fvar i0, Lean.Expr.fvar i1].length)
      (hk' : k < [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)].length),
      Meaning (inputValues p.bools p.bits)
        ([Lean.Expr.fvar i0, Lean.Expr.fvar i1][k]'hk)
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
      (instEN ``childAdd [] (.const ``Sparkle.Core.Domain.defaultDomain [])
        [.fvar i0, .fvar i1])
      (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) :=
    meaning_inst rfl rfl hargsM hsem
  have kid : KidFacts children addSem ``childAdd
      [Lean.Expr.fvar i0, Lean.Expr.fvar i1].length
      (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) y :=
    hkid _ rfl
  have leafK0 : LeafK envR children addSem mF p.context
      (inputValues p.bools p.bits) mems initial
      (instEN ``childAdd [] (.const ``Sparkle.Core.Domain.defaultDomain [])
        [.fvar i0, .fvar i1])
      (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) := by
    refine Or.inr ⟨``childAdd, [], .const ``Sparkle.Core.Domain.defaultDomain [],
      [.fvar i0, .fvar i1],
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
  have value := Q (.const ``Sparkle.Core.Domain.defaultDomain []) 0 1 (fun _ => 8)
    (fun _ => .const ``Sparkle.Core.Domain.defaultDomain [])
    (fun _ => instEN ``childAdd [] (.const ``Sparkle.Core.Domain.defaultDomain [])
      [.fvar i0, .fvar i1]) (fun _ => false)
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

/-- **`wrapAdd`: the cache entry exists and the observation holds against
it.** Binders: the run, `GateDefines` (NOT ALLOWED, ruling pending —
unchanged), `ChildBnd` (ALLOWED), `EntryDefines` of `childAdd` (ALLOWED). -/
theorem wrapAdd_gate_cone_runK' {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``wrapAdd) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``wrapAdd wrapAddBinders wrapAddBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``childAdd childAddValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``childAdd = true ∧
      ∃ y : Res, mF.get? ``childAdd = some y ∧ WrapAddObservesC (ownChild y) M := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone, hentry⟩ :=
    gate_cone_runGE hr gdef bnd
  have tagR := wrapAdd_tag hacc
  obtain ⟨y, hy⟩ := hentry ``childAdd
    (fun L' _ hD ids len => wrapAdd_entryWN L' hD tagR ids len)
  have hreal : RealChild mref cref ``childAdd y := hcache ``childAdd y hy
  exact ⟨M, envR, mF, hpost, hcache, tagR, y, hy,
    wrapAdd_coneKC hcone tagR hy (fun v hv =>
      kidFacts_of_first' centry childAdd_fe_wf (by decide) hreal addSem v hv addSem_spec)⟩

end Sparkle.Tests.Compiler.GateConeWrapAddTest

#print axioms Sparkle.Tests.Compiler.GateConeWrapAddTest.domCall_sound
#print axioms Sparkle.Tests.Compiler.GateConeWrapAddTest.wrapAdd_tag
#print axioms Sparkle.Tests.Compiler.GateConeWrapAddTest.wrapAdd_entryWN
#print axioms Sparkle.Tests.Compiler.GateConeWrapAddTest.wrapAdd_gate_cone_runK'

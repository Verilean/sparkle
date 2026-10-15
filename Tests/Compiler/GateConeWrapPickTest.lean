import Tests.Compiler.GateConeEntryTest
import Tests.Compiler.ShippingMachineInstTest
import Tests.Compiler.SlotlessParentProbeTest
import Tools.ShippingInstanceMeaningP
import Tools.ShippingGateKid

/-! # `wrapPick`: a single-leaf cone over a call WITHOUT a domain argument (worker W, round 2)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.GateConeWrapPickTest`;
not in `Tests.AllTests`).

`wrapPick sel x := pick sel x` (`Tests/Compiler/SlotlessParentProbeTest.lean`):
binders `[sel : BitVec 2, x : BitVec 8]`, NO domain binder; `pick`
(`Tests/Compiler/ShippingMachineInstTest.lean`) has no domain binder either,
so the body is `pick (bvar 1) (bvar 0)` — spine `[sel, x]`, BOTH ports, no
prefix. As an expression it is `instEN ``pick [] (bvar 1) [bvar 0]` (the step
lemmas read only the head); the compiler's last-#ports rule reads `[sel, x]`
(`instUncached_shapeE`); the meaning (extended in place) reads the same.

* the body: `wrapPickBody`; the real declaration's peel is checked by
  evaluation (`run_cmd`, the build fails otherwise);
* tag: the leaf is the body (`wrapPick_sel`, the text of `parentUse_sel`);
* entry existence: the root is the instance leaf (`inst_entryW` at
  `dom := sel`, `argsE := [x]` — it does not read the split);
* the child facts of `pick` (a MIXED-gate child, not a first-gate one): the
  new `Tools.ShippingGateKid.kidFacts_of_gate'` from `#gate_child pick`'s
  generated reading (`pick.gate_peel`, `pick.gate_wf`, `pick.gate_old`) and
  `EntryDefines` of `pick` (ALLOWED);
* the child semantics `pickTermSem`: `pick`'s gate term (`pick.gateTerm`, the
  term the gate reads off `pick`'s body and quotes back to it) evaluated on
  the two port values; `ports _ := 2`;
* the cone: the generalized `InstLeafK` leaf with `pre = []`,
  `argsE = [sel, x]` (`wrapPick_coneKT`), and the full entry
  **`wrapPick_gate_cone_runKT`**: the cache entry of `pick` exists and the
  linked evaluation of the compiled module drives `out` with the gate term's
  value of `pick` on the inputs.

The source-level (Signal) form `wrapPick_gate_cone_runK'` — `out` is
`((wrapPick sS xS).val t).toNat` — is
`Tests/Compiler/GateConeWrapPickSourceTest.lean` (it adds one definitional
step, kept apart so this file does not depend on it).

Premises of `wrapPick_gate_cone_runKT`: the run, `GateDefines` (NOT ALLOWED,
ruling pending, unchanged — as for `wrapAdd`), `ChildBnd` (ALLOWED),
`EntryDefines` of `pick` (ALLOWED). -/
namespace Sparkle.Tests.Compiler.GateConeWrapPickTest
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineInstTest (pick)
open Sparkle.Tests.Compiler.SlotlessParentProbeTest (wrapPick)
open Tools.ShippingHierarchySoundness
open Tools.ShippingUnifiedSource
open Tools.ShippingUnifiedMeaning Tools.ShippingUnifiedRecursion
open Tools.ShippingLinkCtx Tools.ShippingInstanceLeaf Tools.ShippingHierTermSoundness
open Tools.ShippingInstanceEntrySoundness (instEN)
open Tools.ShippingInstanceMeaningP (instEP meaning_instP)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingGateParentRun
open Tools.ShippingGateDefines
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (ChildBnd CacheInv Res RealChild RefLaws)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingFirstGateKid (ownChild)
open Tools.ShippingMachineChild (InRange decB decV)

/-! ## The body -/

def wrapPickBinders : List (Name × MixedGateBinder) := [(`sel, .bits 2), (`x, .bits 8)]

/-- `pick sel x`, quoted: no prefix before the two ports. As an expression it
is the domain-carrying shape with `sel` in the first slot. -/
abbrev wrapPickBody : Lean.Expr :=
  instEN ``pick [] (inputExpr wrapPickBinders.length 0)
    ([1].map (inputExpr wrapPickBinders.length))

/-- The same body, read by the compiler's rule: no prefix, two ports. -/
example : wrapPickBody = instEP ``pick [] [] [.bvar 1, .bvar 0] := rfl

-- The real declaration's peel IS `(wrapPickBinders, wrapPickBody)` (checked
-- by evaluation; the build fails otherwise).
run_cmd Lean.Elab.Command.liftTermElabM do
  let some ci := (← getEnv).find? ``Sparkle.Tests.Compiler.SlotlessParentProbeTest.wrapPick
    | throwError "wrapPick is not in the environment"
  let some v := ci.value? | throwError "wrapPick has no value"
  match mixedGatePeel v with
  | some (bs, body) =>
    unless bs == wrapPickBinders do throwError "wrapPick's peeled binders differ"
    unless body == wrapPickBody do throwError "wrapPick's peeled body differs: {body}"
    logInfo m!"WRAPPICK peel = (wrapPickBinders, wrapPickBody)"
  | none => throwError "wrapPick does not peel"

/-! ## The tag of the callee -/

set_option maxRecDepth 8192 in
/-- Only an instance disjunct accepts the body (the text of `parentUse_sel`). -/
theorem wrapPick_sel : MixedGateSel (wrapPickBinders.map (·.2)).toArray wrapPickBody := by
  intro isInst sc hI
  unfold mixedGateCond unifiedInstanceRoot hierInstRoot
  rw [hI]
  rfl

/-- **The callee is tagged at the run's environment.** -/
theorem wrapPick_tag {envR : Lean.Environment}
    (hacc : ∃ dv : Lean.DefinitionVal, mixedCertifiedShape? false [] (.defnInfo dv)
      (Sparkle.Compiler.Elab.instancePredicate envR) = some (wrapPickBinders, wrapPickBody)) :
    Sparkle.Compiler.isHardwareModule envR ``pick = true :=
  Tools.ShippingGateConeTag.gate_leaf_tag' (mn := ``pick) (lvls := [])
    (dE := inputExpr wrapPickBinders.length 0)
    (n := wrapPickBinders.length) (poss := [1]) hacc (List.cons_ne_nil _ _) wrapPick_sel

/-! ## The cache entry exists -/

set_option maxRecDepth 8192 in
/-- **Every run of the translator on `wrapPick`'s instantiated body ends with
`pick` in the child cache** (the root IS the instance leaf; `inst_entryW`
does not read how the spine splits into prefix and ports). -/
theorem wrapPick_entryWN {envR : Lean.Environment}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0)
    (tagR : Sparkle.Compiler.isHardwareModule envR ``pick = true)
    (ids : List FVarId) (len : ids.length = wrapPickBinders.length) :
    EntryWN L D (translateFuelFix (translateStep envR) translateFuelLimit)
      (instFVars (ids.map Lean.Expr.fvar).toArray 0 wrapPickBody) ``pick := by
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
  have hbody : instFVars ([i0, i1].map Lean.Expr.fvar).toArray 0 wrapPickBody =
      instEN ``pick [] (.fvar i0) [.fvar i1] := rfl
  rw [hbody, hfl]
  intro mctx cctx hint top named ctx s t wire w0 w1 _ hw hd hr
  exact inst_entryW (tenv := envR) (mn := ``pick) (lvls := [])
    (dom := .fvar i0) (argsE := [.fvar i1])
    L hD (translateFuelLimit - 1) rfl rfl rfl tagR
    mctx cctx hint top named ctx s t wire w0 w1 hw hd hr

/-! ## `pick`'s child semantics: its gate term -/

/-- `pick`'s gate term evaluated on port values `ns` (decoded as the gate
child theorem decodes them). -/
noncomputable def pickTermV (ns : List Nat) : Value :=
  pack Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateSort
    (eval
      (fun j => decB Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateBinders ns
        (Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateBpos.getD j 0))
      (fun j w => decV Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateBinders ns
        (Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateVpos.getD j 0) w)
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateTerm)

/-- Its packed number. -/
noncomputable def pickF (ns : List Nat) : Nat := (pickTermV ns).toNat

/-- `pick`'s child semantics: the gate term on a 2-bit and an 8-bit value;
`pick` has two ports. -/
noncomputable def pickTermSem : ChildSem where
  childSem mn vs :=
    if mn = ``pick ∧ vs.map Value.kind = [.bits 2, .bits 8] then
      some (pickTermV (vs.map Value.toNat))
    else none
  ports _ := 2

theorem pickTermV_kind (ns : List Nat) : (pickTermV ns).kind = .bits 8 := rfl

/-- A value of kind `bits 8` is the 8-bit vector of its number. -/
theorem value_bits8 : ∀ (v : Value), v.kind = .bits 8 → v = .bits 8 (BitVec.ofNat 8 v.toNat)
  | .bool b, h => by simp [Value.kind] at h
  | .bits n b, h => by
    have hn : n = 8 := by simpa [Value.kind] using h
    subst hn
    show Value.bits 8 b = Value.bits 8 (BitVec.ofNat 8 b.toNat)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- What `pickTermSem` answers on `pick`: two values, in range of the gate's
binders, the result the gate term's packed number (`kidFacts_of_gate`'s
`hC`). -/
theorem pickTermSem_hC : ∀ (vs : List Value) (u : Value),
    @ChildSem.childSem pickTermSem ``pick vs = some u →
    vs.length = 2 ∧
    InRange (vs.map Value.toNat)
      (Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateBinders.filter
        fun x => x.2 != .domain) ∧
    u.toNat = pickF (vs.map Value.toNat) := by
  intro vs u h
  have h' : (if ``pick = ``pick ∧ vs.map Value.kind = [.bits 2, .bits 8] then
      some (pickTermV (vs.map Value.toNat)) else none) = some u := h
  split at h'
  · rename_i hc
    cases h'
    obtain ⟨-, hk⟩ := hc
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vs⟩⟩⟩
    · simp at hk
    · simp at hk
    · cases v1 with
      | bool b1 => simp [Value.kind] at hk
      | bits n1 b1 =>
        cases v2 with
        | bool b2 => simp [Value.kind] at hk
        | bits n2 b2 =>
          obtain ⟨e1, e2⟩ : n1 = 2 ∧ n2 = 8 := by simpa [Value.kind] using hk
          subst e1 e2
          refine ⟨rfl, ?_, rfl⟩
          show Tools.ShippingMachineClose.Zip₂ _ [b1.toNat, b2.toNat] _
          refine Tools.ShippingMachineClose.Zip₂.cons ?_
            (Tools.ShippingMachineClose.Zip₂.cons ?_ Tools.ShippingMachineClose.Zip₂.nil)
          · exact b1.isLt
          · exact b2.isLt
    · simp at hk
  · cases h'

/-! ## The observation against a linked context -/

/-- What `M`'s linked evaluation against `children` observes: `out` is
`pick`'s gate term on the two inputs. -/
def WrapPickObservesT (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (M : Sparkle.IR.AST.Module) : Prop :=
  ∃ (i0 i1 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
  ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) (sS : Signal defaultDomain (BitVec 2)) (xS : Signal defaultDomain (BitVec 8))
    (t : Nat) (mems : MEnv),
  let a := Tools.ShippingMixedEntrySoundness.start
    (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl ``wrapPick)
  let p := Tools.ShippingMixedEntrySoundness.prepare bools bits
    (wrapPickBinders.zip [i0, i1]) a
  Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
    (wrapPickBinders.zip [i0, i1]) a →
  p.bits i0 = some ⟨2, sS.val t⟩ → p.bits i1 = some ⟨8, xS.val t⟩ →
  (∃ result, evalAssignsH (Tools.ShippingMixedEntrySoundness.moduleWidths M)
      children mems M.body initial = some result ∧
    result "out" = (BitVec.ofNat 8 (pickF [(sS.val t).toNat, (xS.val t).toNat])).toNat) ∧
  InstsLinked children M

set_option maxRecDepth 8192 in
/-- **The single-leaf cone over ANY linked context whose `pick` entry has the
cone's child facts** — the leaf is the generalized `InstLeafK` with NO prefix
and the two ports. -/
theorem wrapPick_coneKT {envR : Lean.Environment} {mF : Std.HashMap Lean.Name Res}
    {M : Sparkle.IR.AST.Module} {children : String → Option (Sparkle.IR.AST.Module × WEnv)}
    (P : HierConePreservesK envR mF ``wrapPick wrapPickBinders wrapPickBody M)
    (tagR : Sparkle.Compiler.isHardwareModule envR ``pick = true)
    {y : Res} (hy : mF.get? ``pick = some y)
    (hkid : ∀ v : Value, v.kind.width = 8 → KidFacts children pickTermSem ``pick 2 v y) :
    WrapPickObservesT children M := by
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
  intro bools bits initial sS xS t mems a p adm hs0 hx0
  obtain ⟨separate, Q⟩ := P children pickTermSem bools bits initial mems adm
  have hS : inputValues p.bools p.bits i0 = some (.bits 2 (sS.val t)) :=
    inputValues_bits separate hs0
  have hX : inputValues p.bools p.bits i1 = some (.bits 8 (xS.val t)) :=
    inputValues_bits separate hx0
  letI : HierCtx := hierLink children
  letI : ChildSem := pickTermSem
  have hargsM : ∀ k (hk : k < [Lean.Expr.fvar i0, Lean.Expr.fvar i1].length)
      (hk' : k < [Value.bits 2 (sS.val t), Value.bits 8 (xS.val t)].length),
      Meaning (inputValues p.bools p.bits)
        ([Lean.Expr.fvar i0, Lean.Expr.fvar i1][k]'hk)
        ([Value.bits 2 (sS.val t), Value.bits 8 (xS.val t)][k]'hk') := by
    intro k hk hk'
    rcases k with _ | k
    · exact .input rfl hS
    · rcases k with _ | k
      · exact .input rfl hX
      · exact absurd hk (by simp)
  have hsemT : ChildSem.childSem ``pick [Value.bits 2 (sS.val t), Value.bits 8 (xS.val t)] =
      some (pickTermV [(sS.val t).toNat, (xS.val t).toNat]) := by
    show (if ``pick = ``pick ∧
        [Value.bits 2 (sS.val t), Value.bits 8 (xS.val t)].map Value.kind =
          [.bits 2, .bits 8] then _ else none) = _
    rw [if_pos ⟨rfl, rfl⟩]
    rfl
  have hsem : ChildSem.childSem ``pick [Value.bits 2 (sS.val t), Value.bits 8 (xS.val t)] =
      some (.bits 8 (BitVec.ofNat 8 (pickF [(sS.val t).toNat, (xS.val t).toNat]))) := by
    rw [hsemT]
    exact congrArg some (value_bits8 _ (pickTermV_kind _))
  -- the leaf's meaning, read by the compiler's rule: no prefix, two ports
  have leafM : LeafMeaning pickTermSem (inputValues p.bools p.bits)
      (instEP ``pick [] [] [.fvar i0, .fvar i1])
      (.bits 8 (BitVec.ofNat 8 (pickF [(sS.val t).toNat, (xS.val t).toNat]))) :=
    meaning_instP rfl rfl rfl hargsM hsem
  have kid : KidFacts children pickTermSem ``pick
      [Lean.Expr.fvar i0, Lean.Expr.fvar i1].length
      (.bits 8 (BitVec.ofNat 8 (pickF [(sS.val t).toNat, (xS.val t).toNat]))) y :=
    hkid _ rfl
  have leafK0 : LeafK envR children pickTermSem mF p.context
      (inputValues p.bools p.bits) mems initial
      (instEN ``pick [] (.fvar i0) [.fvar i1])
      (.bits 8 (BitVec.ofNat 8 (pickF [(sS.val t).toNat, (xS.val t).toNat]))) := by
    refine Or.inr ⟨``pick, [], [], [.fvar i0, .fvar i1],
      [Value.bits 2 (sS.val t), Value.bits 8 (xS.val t)], rfl, (by simp), rfl, rfl, rfl, tagR,
      rfl, ?_, hsem, ?_⟩
    · intro k hk hk' we fuel
      rcases k with _ | k
      · exact input_contract_fuel hS fuel
      · rcases k with _ | k
        · exact input_contract_fuel hX fuel
        · exact absurd hk (by simp)
    · intro y' hy'
      rw [hy] at hy'
      cases hy'
      exact kid
  have value := Q (.fvar i0) 0 1 (fun _ => 8) (fun _ => .fvar i0)
    (fun _ => instEN ``pick [] (.fvar i0) [.fvar i1]) (fun _ => false)
    (fun _ w => BitVec.ofNat w (pickF [(sS.val t).toNat, (xS.val t).toNat]))
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
  exact ⟨⟨result, hev, hout⟩, linked⟩

/-! ## The full entry -/

set_option maxRecDepth 8192 in
/-- **`wrapPick`: the cache entry of `pick` exists and the observation holds
against it** (the gate-term form). Binders: the run, `GateDefines` (NOT
ALLOWED, ruling pending — unchanged), `ChildBnd` (ALLOWED), `EntryDefines` of
`pick` (ALLOWED). -/
theorem wrapPick_gate_cone_runKT {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``wrapPick) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref ``wrapPick wrapPickBinders wrapPickBody)
    (bnd : ChildBnd mref cref w)
    (centry : EntryDefines mctx mref cctx cref ``pick
      Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gateValue) :
    ∃ (M : Sparkle.IR.AST.Module) (envR : Lean.Environment) (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      CacheInv mref cref mF ∧
      Sparkle.Compiler.isHardwareModule envR ``pick = true ∧
      ∃ y : Res, mF.get? ``pick = some y ∧ WrapPickObservesT (ownChild y) M := by
  obtain ⟨M, Dd, envR, a5, a6, mF, hpost, hname, hmods, henv, hacc, hcache, hcone, hentry⟩ :=
    gate_cone_runGE hr gdef bnd
  have tagR := wrapPick_tag hacc
  obtain ⟨y, hy⟩ := hentry ``pick
    (fun L' _ hD ids len => wrapPick_entryWN L' hD tagR ids len)
  have hreal : RealChild mref cref ``pick y := hcache ``pick y hy
  exact ⟨M, envR, mF, hpost, hcache, tagR, y, hy,
    wrapPick_coneKT hcone tagR hy (fun v hv =>
      Tools.ShippingGateKid.kidFacts_of_gate' (F := pickF) centry
        Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gate_old
        Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gate_peel
        Sparkle.Tests.Compiler.ShippingMachineInstTest.pick.gate_wf
        (Tools.ShippingGateChild.bool_positions (by decide))
        (Tools.ShippingGateChild.bits_positions (by decide))
        (by decide) (fun _ _ => rfl) hreal pickTermSem 2 (by decide) v (hv.trans rfl)
        pickTermSem_hC)⟩

end Sparkle.Tests.Compiler.GateConeWrapPickTest

#print axioms Sparkle.Tests.Compiler.GateConeWrapPickTest.wrapPick_sel
#print axioms Sparkle.Tests.Compiler.GateConeWrapPickTest.wrapPick_tag
#print axioms Sparkle.Tests.Compiler.GateConeWrapPickTest.wrapPick_entryWN
#print axioms Sparkle.Tests.Compiler.GateConeWrapPickTest.pickTermSem_hC
#print axioms Sparkle.Tests.Compiler.GateConeWrapPickTest.wrapPick_coneKT
#print axioms Sparkle.Tests.Compiler.GateConeWrapPickTest.wrapPick_gate_cone_runKT

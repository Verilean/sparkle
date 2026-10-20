import Tools.ShippingInstanceMeaningP
import Tests.Compiler.ShippingHierarchySoundnessTest
import Tests.Compiler.ShippingMachineInstTest
import Tests.Compiler.SlotlessParentProbeTest

/-! # `wrapPick` under the compiler's last-#ports reading (worker W, units 1 and 2)

Round 1 BUILT; round 2 WRITTEN, NOT BUILT (the meaning extended in place:
`Meaning` reads the last `ChildSem.ports mn` arguments; the old reading is
`MeaningD`). TARGET-ONLY (`lake build Tests.Compiler.WrapPickMeaningTest`;
not in `Tests.AllTests`).

`wrapPick sel x := pick sel x` (`Tests/Compiler/SlotlessParentProbeTest.lean`);
`pick` (`Tests/Compiler/ShippingMachineInstTest.lean`) has NO domain binder:
the call's spine is `[sel, x]`, both ports.

* `wrapPick_body`: the real declaration's peeled body IS `instEP ``pick [] []
  [bvar 1, bvar 0]` (checked by evaluation on the environment).
* `addSem_arityOK`: the child semantics of the seven existing gate parents
  satisfies `ArityOK` — so `meaningD_agree` applies to them: their leaves'
  new meaning is exactly their old one (`wrapAdd_leaf_agree`).
* `pickSem`: `pick`'s source function on packed values (the body's mux on
  `sel = 0`, `sel = 1`, else; written out as `pickFn`), `pickSem_arityOK`.
* `wrapPick_meaning`: the body has the (new) meaning `pickFn sel x` at any
  inputs `sel`, `x`.
* `wrapPick_no_old_meaning`: under the same semantics the body has NO old
  meaning (`MeaningD`; the round-9 finding as a theorem).

The cone theorem in the shape of `wrapAdd_gate_cone_runK'` is
`Tests/Compiler/GateConeWrapPickTest.lean`. -/
namespace Sparkle.Tests.Compiler.WrapPickMeaningTest
open Lean Elab Command Meta Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedMeaning
open Tools.ShippingInstanceMeaningP
open Tools.ShippingInstanceEntrySoundness (instEN)
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest (addSem childAdd)
open Sparkle.Tests.Compiler.ShippingMachineInstTest (pick)

/-! ## The body of the real declaration -/

/-- `wrapPick`'s body over its two binders, as the compiler's spine reads it:
no prefix, two port arguments. -/
abbrev wrapPickBodyB : Lean.Expr := instEP ``pick [] [] [.bvar 1, .bvar 0]

run_cmd liftTermElabM do
  let some ci := (← getEnv).find? ``Sparkle.Tests.Compiler.SlotlessParentProbeTest.wrapPick
    | throwError "wrapPick is not in the environment"
  let some v := ci.value? | throwError "wrapPick has no value"
  match mixedGatePeel v with
  | some (bs, body) =>
    unless bs.length == 2 do throwError "wrapPick: {bs.length} binders, expected 2"
    unless body == wrapPickBodyB do
      throwError "wrapPick's peeled body is not `instEP pick [] [] [bvar 1, bvar 0]`: {body}"
    unless instSpineArgs body == [.bvar 1, .bvar 0] do
      throwError "wrapPick's spine is not its two port arguments"
    logInfo m!"WRAPPICK body = instEP pick [] [] [bvar 1, bvar 0]; spine = the two ports"
  | none => throwError "wrapPick does not peel"

/-! ## The existing child semantics -/

/-- The seven gate parents' child semantics is defined only at two
arguments, `childAdd`'s port count: `ArityOK`, so the compatibility layer
applies to them. -/
theorem addSem_arityOK : @ArityOK addSem := by
  intro mn vs v h
  have h' : (if mn = ``childAdd ∧ vs.map Value.kind = [.bits 8, .bits 8] then
      some (Value.bits 8 (BitVec.ofNat 8 ((vs.map Value.toNat).sum))) else none) = some v := h
  split at h'
  · rename_i hc
    obtain ⟨hmn, hk⟩ := hc
    subst hmn
    have hl : vs.length = 2 := by
      have := congrArg List.length hk
      simpa using this
    show vs.length = 2
    exact hl
  · cases h'

/-- `wrapAdd`'s leaf (the domain-carrying call `instEN childAdd [] defaultDomain
[a, b]`): wherever it has an old meaning `v`, its new meanings are exactly
`v` — the meaning the seven parents' theorems use is unchanged. -/
theorem wrapAdd_leaf_agree {inputs : FVarId → Option Value} {i0 i1 : FVarId} {v : Value}
    (h : @MeaningD addSem inputs
      (instEN ``childAdd [] (.const ``Sparkle.Core.Domain.defaultDomain []) [.fvar i0, .fvar i1])
      v) (v' : Value) :
    @Meaning addSem inputs
      (instEN ``childAdd [] (.const ``Sparkle.Core.Domain.defaultDomain []) [.fvar i0, .fvar i1])
      v' ↔ v' = v := by
  letI : ChildSem := addSem
  exact meaningD_agree addSem_arityOK h v'

/-! ## `pick`'s child semantics -/

/-- `pick`'s body on packed values: `sel = 0` → `x`, `sel = 1` → `x + 1`,
else `x ^^^ 0xFF`. -/
def pickFn (s x : Nat) : BitVec 8 :=
  if s = 0 then BitVec.ofNat 8 x
  else if s = 1 then BitVec.ofNat 8 x + 1#8
  else BitVec.ofNat 8 x ^^^ 0xFF#8

/-- `pick`'s source function, defined only on a 2-bit and an 8-bit value;
`pick` has two ports. -/
def pickSem : ChildSem where
  childSem mn vs :=
    if mn = ``pick ∧ vs.map Value.kind = [.bits 2, .bits 8] then
      some (.bits 8 (pickFn ((vs.map Value.toNat).getD 0 0) ((vs.map Value.toNat).getD 1 0)))
    else none
  ports _ := 2

theorem pickSem_arityOK : @ArityOK pickSem := by
  intro mn vs v h
  have h' : (if mn = ``pick ∧ vs.map Value.kind = [.bits 2, .bits 8] then
      some (Value.bits 8 (pickFn ((vs.map Value.toNat).getD 0 0)
        ((vs.map Value.toNat).getD 1 0))) else none) = some v := h
  split at h'
  · rename_i hc
    obtain ⟨hmn, hk⟩ := hc
    subst hmn
    have hl : vs.length = 2 := by
      have := congrArg List.length hk
      simpa using this
    show vs.length = 2
    exact hl
  · cases h'

/-! ## The body's meanings -/

/-- `wrapPick`'s body with its binders opened to free variables. -/
abbrev wrapPickE (i0 i1 : FVarId) : Lean.Expr := instEP ``pick [] [] [.fvar i0, .fvar i1]

/-- **The meaning of `wrapPick`'s body** (the in-place extended `Meaning`):
`pick`'s source function of BOTH port arguments (`sel` is a port, not a
domain). -/
theorem wrapPick_meaning {inputs : FVarId → Option Value} {i0 i1 : FVarId}
    {s : BitVec 2} {x : BitVec 8}
    (h0 : inputs i0 = some (.bits 2 s)) (h1 : inputs i1 = some (.bits 8 x)) :
    @Meaning pickSem inputs (wrapPickE i0 i1) (.bits 8 (pickFn s.toNat x.toNat)) := by
  letI : ChildSem := pickSem
  refine meaning_instP (pre := []) (argsE := [.fvar i0, .fvar i1])
    (vs := [Value.bits 2 s, Value.bits 8 x]) rfl rfl rfl ?_ ?_
  · intro i ha hv
    rcases i with _ | i
    · exact .input rfl h0
    · rcases i with _ | i
      · exact .input rfl h1
      · exact absurd ha (by simp)
  · show (if ``pick = ``pick ∧
        [Value.bits 2 s, Value.bits 8 x].map Value.kind = [.bits 2, .bits 8] then _ else none) = _
    rw [if_pos ⟨rfl, rfl⟩]
    rfl

/-- **The finding as a theorem**: under `pick`'s semantics the body has NO
OLD meaning (`MeaningD.inst` reads `sel` as a domain and `[x]` as the
arguments, at which `pickSem` is undefined). -/
theorem wrapPick_no_old_meaning {inputs : FVarId → Option Value} {i0 i1 : FVarId}
    {v : Value} : ¬ @MeaningD pickSem inputs (wrapPickE i0 i1) v := by
  letI : ChildSem := pickSem
  refine no_meaningD_of_portsSpine pickSem_arityOK (mn := ``pick) (lvls := []) rfl
    (instEP_getAppFn _ _ _ _) ?_
  rw [instEP_spineArgs]
  try rfl

end Sparkle.Tests.Compiler.WrapPickMeaningTest

#print axioms Sparkle.Tests.Compiler.WrapPickMeaningTest.addSem_arityOK
#print axioms Sparkle.Tests.Compiler.WrapPickMeaningTest.wrapAdd_leaf_agree
#print axioms Sparkle.Tests.Compiler.WrapPickMeaningTest.pickSem_arityOK
#print axioms Sparkle.Tests.Compiler.WrapPickMeaningTest.wrapPick_meaning
#print axioms Sparkle.Tests.Compiler.WrapPickMeaningTest.wrapPick_no_old_meaning

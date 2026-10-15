import Tests.Compiler.WrapPickMeaningTest

/-! # The scope of `Meaning.inst`: the prefix is discarded (worker D)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.MeaningPrefixScopeTest`;
not in `Tests.AllTests`). Companion of `docs/parallel/D-meaning-prefix-scope.md`.

`Tools.ShippingUnifiedMeaning.Meaning.inst` reads an instance call by the
compiler's rule: the spine is split as `pre ++ args` with
`args.length = ChildSem.ports mn`, the value is `ChildSem.childSem mn` of the
meanings of `args`, and `pre` is DISCARDED. `Meaning` therefore says nothing
about (1) whether `ports` is the callee's real port count, or (2) whether the
discarded prefix terms are source-meaningless (a domain, nothing). Both are
guaranteed per declaration by the SOURCE BRIDGE, not by `Meaning`. These
examples exhibit the gap on the meaning model ALONE:

* (a) `onePortPickSem`: `pick` given ONE port (wrong; `pick` has two). It
  even satisfies `ArityOK` (`onePortPickSem_arityOK`), so `ArityOK` is a
  consistency property of a `ChildSem`, not a correspondence with the
  callee. Under it, `wrapPick`'s real body `pick sel x` MEANS `x`
  (`wrongPorts_meaning`): `sel` falls into the discarded prefix. With
  `sel = 1`, `x = 0` that is NOT `pick`'s function (`pickFn 1 0 = 1`):
  `wrongPorts_disagree`, `wrongPorts_not_source`.
  Excluded in the real theorem (`wrapPick_gate_cone_runK'`) because the
  semantics used there is `pickTermSem` (`ports _ := 2`), tied to the compiled
  child by `kidFacts_of_gate'` (`hn`: two non-domain binders; `pickTermSem_hC`:
  defined only at two values; `KidFacts`: `y.1.inputs.length = argsE.length`),
  and to `pick` itself by `pickF_source`.
* (b) `tailSem` at a hypothetical callee `addK {dom} (k : BitVec 8) (x : Signal
  dom (BitVec 8))` whose FIRST EXPLICIT argument `k` is DATA: the call
  `addK (dom := defaultDomain) k x` with `ports = 1` has prefix `[dom, k]`, and
  its meaning is `x` for EVERY value of `k` (`extraPrefix_meaning` has no
  hypothesis on `k`'s input), not `addKFn k x = x + k`
  (`extraPrefix_not_source`). The model can express the right reading when
  the `ChildSem` is right (`twoPortSem`, `ports = 2`, prefix `[dom]`:
  `extraPrefix_meaning_twoPorts`) — the correspondence lives in the choice of
  `ChildSem`, i.e. in the bridge. None of the eight gate parents has such a
  call: their peels (`parentUse_peel`, …, `wrapAdd_peel`, the `wrapPick`
  `run_cmd` peel check) fix the prefix to a domain binder, the constant
  `defaultDomain`, or nothing.

Proofs are `Meaning` constructors (via `meaning_instP`), `rfl` and `decide` only. -/
namespace Sparkle.Tests.Compiler.MeaningPrefixScopeTest
open Lean
open Tools.ShippingUnifiedMeaning
open Tools.ShippingInstanceMeaningP (instEP meaning_instP ArityOK)
open Sparkle.Tests.Compiler.WrapPickMeaningTest (pickFn pickSem wrapPickE wrapPick_meaning)
open Sparkle.Tests.Compiler.ShippingMachineInstTest (pick)

/-! ## (a) Wrong `ports` -/

/-- A child semantics with the WRONG port count for `pick` (one, not two):
it passes its single argument through. -/
def onePortPickSem : ChildSem where
  childSem mn vs :=
    if mn = ``pick ∧ vs.map Value.kind = [.bits 8] then
      some (.bits 8 (BitVec.ofNat 8 ((vs.map Value.toNat).getD 0 0)))
    else none
  ports _ := 1

/-- `ArityOK` holds for the wrong semantics too: it is internal consistency
(defined only at its own `ports`), not correspondence with the callee. -/
theorem onePortPickSem_arityOK : @ArityOK onePortPickSem := by
  intro mn vs v h
  have h' : (if mn = ``pick ∧ vs.map Value.kind = [.bits 8] then
      some (Value.bits 8 (BitVec.ofNat 8 ((vs.map Value.toNat).getD 0 0))) else none) = some v := h
  split at h'
  · rename_i hc
    obtain ⟨hmn, hk⟩ := hc
    subst hmn
    have hl : vs.length = 1 := by
      have := congrArg List.length hk
      simpa using this
    show vs.length = 1
    exact hl
  · cases h'

/-- **Wrong ports**: under `onePortPickSem`, `wrapPick`'s real body
`pick sel x` (no prefix in the source; spine `[sel, x]`) is split as
`pre = [sel]`, `args = [x]`, and means `x`, whatever `sel` is. -/
theorem wrongPorts_meaning {inputs : FVarId → Option Value} {i0 i1 : FVarId} {x : BitVec 8}
    (h1 : inputs i1 = some (.bits 8 x)) :
    @Meaning onePortPickSem inputs (wrapPickE i0 i1) (.bits 8 (BitVec.ofNat 8 x.toNat)) := by
  letI : ChildSem := onePortPickSem
  -- the same expression, written with the split `[sel] ++ [x]`
  show Meaning inputs (instEP ``pick [] [.fvar i0] [.fvar i1]) _
  refine meaning_instP (mn := ``pick) (lvls := []) (pre := [.fvar i0]) (argsE := [.fvar i1])
    (vs := [Value.bits 8 x]) rfl rfl rfl ?_ ?_
  · intro i ha hv
    rcases i with _ | i
    · exact .input rfl h1
    · exact absurd ha (by simp)
  · show (if ``pick = ``pick ∧ [Value.bits 8 x].map Value.kind = [.bits 8] then _ else none) = _
    rw [if_pos ⟨rfl, rfl⟩]
    rfl

/-- The wrong meaning is not `pick`'s function: at `sel = 1`, `x = 0`,
`pick` gives `x + 1 = 1`. -/
theorem pickFn_one_zero : pickFn (1#2).toNat (0#8).toNat ≠ BitVec.ofNat 8 (0#8).toNat := by
  decide

/-- **The same expression, two semantics, two values**: under the right
`pickSem` (two ports) the body means `pick`'s function; under the wrong
`onePortPickSem` it means `x`; the two differ. `Meaning` alone does not pick
the right one. -/
theorem wrongPorts_disagree {inputs : FVarId → Option Value} {i0 i1 : FVarId}
    (h0 : inputs i0 = some (.bits 2 1#2)) (h1 : inputs i1 = some (.bits 8 0#8)) :
    @Meaning pickSem inputs (wrapPickE i0 i1) (.bits 8 (pickFn (1#2).toNat (0#8).toNat)) ∧
    @Meaning onePortPickSem inputs (wrapPickE i0 i1) (.bits 8 (BitVec.ofNat 8 (0#8).toNat)) ∧
    pickFn (1#2).toNat (0#8).toNat ≠ BitVec.ofNat 8 (0#8).toNat :=
  ⟨wrapPick_meaning h0 h1, wrongPorts_meaning h1, pickFn_one_zero⟩

/-- Under the wrong semantics the body has NO meaning equal to `pick`'s
function (by determinism). -/
theorem wrongPorts_not_source {inputs : FVarId → Option Value} {i0 i1 : FVarId}
    (h1 : inputs i1 = some (.bits 8 0#8)) :
    ¬ @Meaning onePortPickSem inputs (wrapPickE i0 i1)
      (.bits 8 (pickFn (1#2).toNat (0#8).toNat)) := by
  letI : ChildSem := onePortPickSem
  intro h
  have hEq := Meaning.deterministic h (wrongPorts_meaning (i0 := i0) h1)
  have hn := congrArg Value.toNat hEq
  exact absurd hn (by decide)

/-! ## (b) An extra prefix whose dropped term is data -/

/-- A hypothetical callee `addK {dom} (k : BitVec 8) (x : Signal dom (BitVec 8))
:= x + pure k`: its first EXPLICIT argument is data. Only its name is used
(`Meaning` reads expressions; no declaration is needed). -/
abbrev addKName : Name := `MeaningPrefixScope.addK

/-- `addK`'s source function on values. -/
def addKFn (k x : BitVec 8) : BitVec 8 := x + k

/-- A semantics that reads `addK` with ONE port (`x`). -/
def tailSem : ChildSem where
  childSem mn vs :=
    if mn = addKName ∧ vs.map Value.kind = [.bits 8] then
      some (.bits 8 (BitVec.ofNat 8 ((vs.map Value.toNat).getD 0 0)))
    else none
  ports _ := 1

/-- The call `addK (dom := defaultDomain) k x`: spine `[dom, k, x]`. -/
abbrev addKE (ik ix : FVarId) : Lean.Expr :=
  instEP addKName [] [.const ``Sparkle.Core.Domain.defaultDomain [], .fvar ik] [.fvar ix]

/-- **The data prefix is discarded**: with `ports = 1` the prefix is
`[dom, k]`, and the call means `x` for EVERY input of `k` (there is no
hypothesis on `ik`). -/
theorem extraPrefix_meaning {inputs : FVarId → Option Value} {ik ix : FVarId} {x : BitVec 8}
    (hx : inputs ix = some (.bits 8 x)) :
    @Meaning tailSem inputs (addKE ik ix) (.bits 8 (BitVec.ofNat 8 x.toNat)) := by
  letI : ChildSem := tailSem
  refine meaning_instP (mn := addKName) (lvls := [])
    (pre := [.const ``Sparkle.Core.Domain.defaultDomain [], .fvar ik]) (argsE := [.fvar ix])
    (vs := [Value.bits 8 x]) rfl rfl rfl ?_ ?_
  · intro i ha hv
    rcases i with _ | i
    · exact .input rfl hx
    · exact absurd ha (by simp)
  · show (if addKName = addKName ∧ [Value.bits 8 x].map Value.kind = [.bits 8]
      then _ else none) = _
    rw [if_pos ⟨rfl, rfl⟩]
    rfl

/-- Under `tailSem`, the call has no meaning equal to `addK`'s function at
`k = 1`, `x = 0` (the meaning is `0`, the function `1`). -/
theorem extraPrefix_not_source {inputs : FVarId → Option Value} {ik ix : FVarId}
    (_hk : inputs ik = some (.bits 8 1#8)) (hx : inputs ix = some (.bits 8 0#8)) :
    ¬ @Meaning tailSem inputs (addKE ik ix) (.bits 8 (addKFn 1#8 0#8)) := by
  letI : ChildSem := tailSem
  intro h
  have hEq := Meaning.deterministic h (extraPrefix_meaning (ik := ik) hx)
  have hn := congrArg Value.toNat hEq
  exact absurd hn (by decide)

/-- The right semantics for `addK`: two ports `k`, `x`. -/
def twoPortSem : ChildSem where
  childSem mn vs :=
    if mn = addKName ∧ vs.map Value.kind = [.bits 8, .bits 8] then
      some (.bits 8 (addKFn (BitVec.ofNat 8 ((vs.map Value.toNat).getD 0 0))
        (BitVec.ofNat 8 ((vs.map Value.toNat).getD 1 0))))
    else none
  ports _ := 2

/-- With the right `ChildSem` the SAME expression is split `[dom] ++ [k, x]`
and means `addK`'s function: what `Meaning` says depends on the `ChildSem`,
whose correspondence with the callee is the bridge's job. -/
theorem extraPrefix_meaning_twoPorts {inputs : FVarId → Option Value} {ik ix : FVarId}
    {k x : BitVec 8} (hk : inputs ik = some (.bits 8 k)) (hx : inputs ix = some (.bits 8 x)) :
    @Meaning twoPortSem inputs (addKE ik ix)
      (.bits 8 (addKFn (BitVec.ofNat 8 k.toNat) (BitVec.ofNat 8 x.toNat))) := by
  letI : ChildSem := twoPortSem
  -- the same expression, written with the split `[dom] ++ [k, x]`
  show Meaning inputs
    (instEP addKName [] [.const ``Sparkle.Core.Domain.defaultDomain []] [.fvar ik, .fvar ix]) _
  refine meaning_instP (mn := addKName) (lvls := [])
    (pre := [.const ``Sparkle.Core.Domain.defaultDomain []]) (argsE := [.fvar ik, .fvar ix])
    (vs := [Value.bits 8 k, Value.bits 8 x]) rfl rfl rfl ?_ ?_
  · intro i ha hv
    rcases i with _ | i
    · exact .input rfl hk
    · rcases i with _ | i
      · exact .input rfl hx
      · exact absurd ha (by simp)
  · show (if addKName = addKName ∧
        [Value.bits 8 k, Value.bits 8 x].map Value.kind = [.bits 8, .bits 8]
      then _ else none) = _
    rw [if_pos ⟨rfl, rfl⟩]
    rfl

end Sparkle.Tests.Compiler.MeaningPrefixScopeTest

#print axioms Sparkle.Tests.Compiler.MeaningPrefixScopeTest.onePortPickSem_arityOK
#print axioms Sparkle.Tests.Compiler.MeaningPrefixScopeTest.wrongPorts_meaning
#print axioms Sparkle.Tests.Compiler.MeaningPrefixScopeTest.wrongPorts_disagree
#print axioms Sparkle.Tests.Compiler.MeaningPrefixScopeTest.wrongPorts_not_source
#print axioms Sparkle.Tests.Compiler.MeaningPrefixScopeTest.extraPrefix_meaning
#print axioms Sparkle.Tests.Compiler.MeaningPrefixScopeTest.extraPrefix_not_source
#print axioms Sparkle.Tests.Compiler.MeaningPrefixScopeTest.extraPrefix_meaning_twoPorts

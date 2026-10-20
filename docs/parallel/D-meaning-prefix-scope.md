# D — the scope of `Meaning.inst`: the discarded prefix

Worker D, 2026-10-15, branch `par/w-3` (from poc `c1c651a0`). **WRITTEN, NOT BUILT.**
Companion Lean file: `Tests/Compiler/MeaningPrefixScopeTest.lean` (target-only, not in
`Tests.AllTests`; built as a module of the existing `lean_lib «Tests»`, so no new
`lean_lib` line).

Ruling (reviewer, 2026-10-15): `Meaning.inst` DISCARDS the prefix `pre`. Two things are the
job of the SOURCE BRIDGE (the per-declaration correspondence with the Lean function), not of
`Meaning`: that the prefix terms are not source-meaningful arguments, and that
`ChildSem.ports` is the callee's real port count. Keep the bridges for `wrapPick` and the seven
existing gate parents. Do not generalise "ArityOK is always settled by evaluation" to an
arbitrary `ChildSem`. Document wrong-arity and extra-prefix examples as the scope of the
meaning model.

## 1. What `Meaning.inst` asserts

`Tools/ShippingUnifiedMeaning.lean`, `Meaning.inst`:

```
| inst {e mn lvls pre args vs v} : view e = none → e.getAppFn = .const mn lvls →
    instSpineArgs e = pre ++ args → args.length = ChildSem.ports mn →
    vs.length = args.length →
    (∀ i …, Meaning inputs args[i] vs[i]) →
    ChildSem.childSem mn vs = some v → Meaning inputs e v
```

It asserts:

* `e` is an application headed by a constant `mn` that the pure `view` does not read.
* The spine splits as `pre ++ args`, where `args` has exactly `ChildSem.ports mn` elements.
  This is the compiler's rule in `translateInstanceUncachedWith`,
  `args.drop (args.length - #ports)` (`portArgs_eq` / `inst_args_eq` in
  `Tools/ShippingInstanceMeaningP.lean`).
* The value is `ChildSem.childSem mn` applied to the meanings of `args`.
* The meaning is deterministic (`Meaning.deterministic`). The split is fixed by `ports mn`, so
  two readings read the same `args`.

It does NOT assert:

* **Anything about `pre`.** No constraint is placed on the prefix terms: they may be a domain,
  a width, data, or anything else. They are never evaluated, so the meaning is the same for
  every value of a prefix term.
* **That `ChildSem.ports mn` is the callee's real port count.** `ports` is a field of the
  consumer-chosen `ChildSem` class. `Meaning` reads whatever split it dictates.
* **That `ChildSem.childSem mn` is the callee's source function.** That is also a choice of the
  consumer.
* **That `ArityOK` makes either of the above hold.** `ArityOK` (`childSem` defined only at
  `ports`) is internal consistency of a `ChildSem`. A `ChildSem` with the wrong port count
  can satisfy it (`onePortPickSem_arityOK`, below). The discharges `addSem_arityOK` and
  `pickSem_arityOK` (`Tests/Compiler/WrapPickMeaningTest.lean`) are per-semantics evaluations.
  They are not a general fact, and they say nothing about the callee.

`Meaning` is therefore a model of "what the compiler's reading of the call computes, given a
`ChildSem`". It becomes a statement about the SOURCE only together with the bridge.

## 2. Where the source bridge provides the correspondence: the eight gate parents

In every end-to-end theorem, the conclusion is about the real Lean function:
`result "out" = ((P aS bS).val t).toNat`, or `encodeBool (…)` for `parentCmp`. It is not
about `Meaning`. `Meaning` is internal. It appears as `LeafMeaning C inputs e v` (=
`@Meaning C inputs e v`), the premise `hm` of `leafK_contractW` / `meaning` of
`inst_leaf_contractWE` (`Tools/ShippingGateConeW.lean`), and it is used for cache coherence
(determinism) and cone composition. The leaf VALUE `v` is pinned independently by `InstLeafK`:

* `childSem mn vs = some v` on the arguments `argsE`;
* `∀ y, mF.get? mn = some y → KidFacts children C mn argsE.length v y`.

`KidFacts` (`Tools/ShippingGateConeW.lean`) contains `y.1.inputs.length = n`, where
`n = argsE.length` is the real compiled child's input count. It also contains "whenever
`C.childSem mn vs = some u`, the compiled child's body evaluates to `u`". In each parent's
leaf proof, `meaning_instP … rfl rfl rfl …` uses the SAME `argsE` for `Meaning`. Its second
`rfl` is `argsE.length = ChildSem.ports mn`. So within the real theorems,
`ports mn = argsE.length = y.1.inputs.length`, the real compiled callee's port count.

The per-parent facts are:

| parent | prefix dropped | peel (body + prefix pinned) | child semantics / ports ↔ callee | source step | end-to-end theorem |
|---|---|---|---|---|---|
| `parentUse` | `[dom]`: binder 0 is `` (`dom, .domain) `` | `parentUse_peel` (`ShippingHierarchySoundnessTest.lean:240`, `instE2 childAdd [] (bvar dom) a b`, `rfl`) | `addSem` (`ports _ := 2`, defined only at `[bits 8, bits 8]`); `addSem_spec` (`GateConeKidTest.lean:65`: `vs.length = [`x,`y].length`, value = `childAdd`'s fragment); `kidFacts_of_first' centry childAdd_fe_wf … addSem_spec`, with `EntryDefines … ``childAdd childAddValue` | final `rfl` / `BitVec.ofNat_toNat` against `(parentUse aS bS).val t` | `parentUse_gate_cone_runK'` (`GateConeUseTest.lean:215`) |
| `parentMix` | `[dom]` | `parentMix_peel` (`ShippingHierarchySoundnessTest.lean:803`) | same (`addSem_spec`, `kidFacts_of_first'`) | same | `parentMix_gate_cone_runK'` (`GateConeEntryTest.lean:99`) |
| `parentTwoCalls` | `[dom]` (both calls) | `parentTwoCalls_peel` (`GateConeTwoCallsTest.lean:412`) | same | same | `parentTwoCalls_gate_cone_runK'` (`:382`) |
| `parentRepeat` | `[dom]` | `parentRepeat_peel` (`GateConeRepeatTest.lean:302`) | same | same | `parentRepeat_gate_cone_runK'` (`:273`) |
| `parentCmp` | `[dom]` | `parentCmp_peel` (`GateConeCmpTest.lean:311`) | same | same (Bool, `encodeBool`) | `parentCmp_gate_cone_runK'` (`:282`) |
| `parentNested` | `[dom]` (both calls; the inner call is a PORT argument of the outer one, not prefix) | `parentNested_peel` (`ShippingHierarchySoundnessTest.lean:1256`) | same | same | `parentNested_gate_cone_runK'` (`GateConeNestedTest.lean:314`) |
| `wrapAdd` | `[const defaultDomain]` | `wrapAdd_peel` (`ShippingHierarchySoundnessTest.lean:1461`; `wrapE` = `instEN childAdd [] (const defaultDomain) [a, b]`) and the `mixedGatePeel wrapAddValue = … := rfl` example (`GateConeWrapAddTest.lean:59`) | same | final `rfl` against `(wrapAdd aS bS).val t` | `wrapAdd_gate_cone_runK'` (`GateConeWrapAddTest.lean:319`) |
| `wrapPick` | `[]` (nothing dropped) | `run_cmd` peel checks: `GateConeWrapPickTest.lean` (`peel = (wrapPickBinders, wrapPickBody)`) and `WrapPickMeaningTest.lean:46` (body = `instEP pick [] [] [bvar 1, bvar 0]`, `instSpineArgs body = [bvar 1, bvar 0]`: the spine is the two ports) | `pickTermSem` (`ports _ := 2`); `pickTermSem_hC` (`GateConeWrapPickTest.lean:188`: `vs.length = 2`, `InRange` of `pick`'s non-domain binders, value = `pickF`); `kidFacts_of_gate'` (`Tools/ShippingGateKid.lean:192`; `hn`: `pick`'s non-domain binder count = 2), with `EntryDefines … ``pick pick.gateValue` | `pickF_source` (`GateConeWrapPickSourceTest.lean:41`: `pick`'s gate term = `pick` on constant signals, definitional) | `wrapPick_gate_cone_runK'` (`GateConeWrapPickSourceTest.lean:86`) |

Also relevant: `addSem_arityOK` and `wrapAdd_leaf_agree` (`WrapPickMeaningTest.lean:65,83`) show
that the seven `childAdd` parents read the same leaf value under the new and old meanings
(`meaningD_agree`). `pickSem_arityOK` / `wrapPick_meaning` (`:111,135`) give `wrapPick`'s body
`pick`'s function under `pickSem`. These are per-semantics evaluations. Each one holds for
its named `ChildSem` only.

Per parent, the correspondence is closed as follows:

1. **The prefix is source-meaningless.** The peel pins the body. The prefix is the domain
   binder (six `childAdd` parents; their binder lists start with `` (`dom, .domain) ``), the
   closed constant `defaultDomain` (`wrapAdd`), or empty (`wrapPick`). In all three cases it
   is the callee's implicit `{dom}` or nothing. `childAdd {dom} (x y)` and `pick (sel x)`
   have no other explicit non-port argument.
2. **`ports` is the callee's real port count.** `ports = argsE.length` (the `rfl` in
   `meaning_instP`), `argsE.length = y.1.inputs.length` (`KidFacts`), and `KidFacts` comes from
   `kidFacts_of_first'` / `kidFacts_of_gate'`. These derive it from the callee's
   `EntryDefines` and its real `RealChild` run: `hinLen` uses the callee's own non-domain
   binders, and the child semantics' own arity comes from `addSem_spec` / `pickTermSem_hC`.
3. **`childSem` is the callee's function.** `KidFacts` says the compiled child computes the
   value of `childSem`. The final source step says that value equals the Lean function: for
   `childAdd`, the `rfl` closing each `…ObservesC`; for `pick`, `pickF_source`.

## 3. The scope: what `Meaning` says outside the bridge, and why the end-to-end theorems are unaffected

Out of scope of the meaning model (exhibited in `Tests/Compiler/MeaningPrefixScopeTest.lean`):

**(a) Wrong `ports`.** `onePortPickSem` gives `pick` one port and passes it through. It
satisfies `ArityOK` (`onePortPickSem_arityOK`). Under it, `wrapPick`'s real body `pick sel x`
splits `[sel] ++ [x]`, and its meaning is `x` whatever `sel` is (`wrongPorts_meaning`). At
`sel = 1`, `x = 0` the meaning is `0`, while `pick` gives `1`:

* `wrongPorts_disagree`: the same expression has `pickFn 1 0` under `pickSem` and `0` under
  `onePortPickSem`, and these values differ;
* `wrongPorts_not_source`: under `onePortPickSem` there is no meaning equal to `pick`'s
  function.

So `Meaning` alone assigns a value that does not match the callee.

**(b) Extra prefix, where a dropped term is data.** Take a hypothetical callee
`addK {dom} (k : BitVec 8) (x : Signal dom (BitVec 8)) := x + pure k`. Its first EXPLICIT
argument is data. `tailSem` has `ports = 1`. The call `addK (dom := defaultDomain) k x`
splits `[dom, k] ++ [x]`. Its meaning is `x` for EVERY value of `k`: `extraPrefix_meaning`
has no hypothesis on `k`. It is not `addKFn k x = x + k` (`extraPrefix_not_source`). With
the right semantics (`twoPortSem`, `ports = 2`), the same expression splits `[dom] ++ [k, x]`
and means `addKFn k x` (`extraPrefix_meaning_twoPorts`). The meaning model can express the
right reading, but it does not choose it. Choosing it is the bridge's job.

Further cases in the same scope (not given separate Lean examples):

* `ports` larger than the spine: no split exists, and the call has no meaning.
* A width-generic callee whose width argument is in the prefix (`childW w x y`): the width
  is source-meaningful but dropped. On the compiler side, a call at a width other than the
  child's compiled one is REFUSED by `instLinkCheck` (`instUncached_linkedE`,
  `Tests/Compiler/NarrowArgPortTest.lean`). On the meaning side nothing ties the width.
  None of the eight parents calls a width-generic child.

**Are the end-to-end theorems affected? No, for these eight parents. The reasons:**

* The conclusions are about the real Lean function (`(P aS bS).val t`) and the compiled
  module's linked evaluation. `Meaning` appears only internally, under a FIXED `ChildSem`
  (`addSem` or `pickTermSem`). That `ChildSem` is chosen per declaration and tied to the
  callee as in §2.
* Suppose someone substituted a wrong `ChildSem`, such as `onePortPickSem`, into the generic
  cone (`HierConePreservesK` / `InstLeafK` / `leafK_contractW`). `InstLeafK` needs
  `KidFacts … argsE.length v y` with `y.1.inputs.length = argsE.length` for the REAL child
  (`pick` has two inputs), and `childSem mn vs = some v` on those two values.
  `onePortPickSem` is undefined at two values, so the leaf premise cannot be discharged. In
  general the leaf value `v` is pinned by `childSem` on the compiler's own connected
  arguments (`argsE`, the last `y.1.inputs.length` spine terms) and by the compiled child's
  computation (`KidFacts`). `Meaning` must agree with that `v`, so a mis-split `Meaning`
  either has no proof at `v` (the premise is unprovable) or coincides with it. Either way no
  false conclusion follows.
* The step from `v` to the Signal source is the per-declaration closing step (the final
  `rfl` for the `childAdd` parents, `pickF_source` for `wrapPick`). It holds only for the
  semantics actually used, which is the callee's real function.

**What IS affected, precisely.** Any statement whose conclusion is phrased in `Meaning` with a
universally quantified or consumer-chosen `ChildSem` is a statement RELATIVE to that
`ChildSem`. This covers the generic cone/contract theorems and `Meaning.deterministic`. Read
alone, such a theorem does not say the compiled module matches the source when the call has
a data prefix or a mis-declared `ports`, because then the `ChildSem` is not the callee's
function. These theorems are not wrong. They are conditional on `C`. Source correspondence
for a NEW parent therefore needs its own bridge, of the shape in §2:

* a peel pinning the prefix to a domain or nothing;
* a `ChildSem` whose arity is discharged against the callee's non-domain binders (via
  `kidFacts_of_first'` / `kidFacts_of_gate'` from `EntryDefines`);
* a closing source step.

`ArityOK` by evaluation is not a substitute for any of these.

## 4. Status

* WRITTEN, NOT BUILT. Lean file: `Tests/Compiler/MeaningPrefixScopeTest.lean`. It imports
  `Tests.Compiler.WrapPickMeaningTest`, which is built, and uses `pickFn`, `pickSem`,
  `wrapPickE` and `wrapPick_meaning`.
* No compiler change. No existing statement changed. No `sorry`, no axioms, no
  `native_decide`.

## Integration (integrator, 2026-10-15) — BUILT as written
Base poc c1c651a0. Run `d1` (cgrun, 3 GiB, swap 0, `-j 1`): `Tests.Compiler.MeaningPrefixScopeTest` exit 0
(target-only, module of the `Tests` lib). Axioms: `onePortPickSem_arityOK`, `wrongPorts_meaning`,
`wrongPorts_disagree`, `extraPrefix_meaning`, `extraPrefix_meaning_twoPorts` [propext, Quot.sound];
`wrongPorts_not_source`, `extraPrefix_not_source` [propext, Classical.choice, Quot.sound].
Kernel-checked scope examples: a `ChildSem` satisfying `ArityOK` with the WRONG port count gives a `Meaning`
that differs from the callee's function; a dropped prefix holding DATA gives a `Meaning` independent of that
data. The eight gate parents' end-to-end theorems are not affected (their bridges fix the prefix, the arity
and the child semantics against the real callee); any statement over a caller-chosen `ChildSem` is only
relative to it.

# Worker W, round 1 (par/w-1) — WRITTEN, NOT BUILT

Base: poc `3b7fc95d`. No compiler file, no ALLOWED list, no existing definition changed.

## Unit 1 — calls without a domain argument (`wrapPick`)

Files: `Tools/ShippingInstanceMeaningP.lean` (new lean_lib), `Tests/Compiler/WrapPickMeaningTest.lean`
(target-only). Build order: `Tools.ShippingInstanceMeaningP`, then `Tests.Compiler.WrapPickMeaningTest`
(it imports `Tests.Compiler.SlotlessParentProbeTest` for the real `wrapPick`, and
`Tests.Compiler.ShippingMachineInstTest` for `pick`).

New definitions (nothing existing changed):
* `ChildPorts` (class, `ports : Name → Nat`) — the port count of each callee.
* `MeaningP` — `Meaning` verbatim except the instance constructor:
  `instSpineArgs e = pre ++ args`, `args.length = ChildPorts.ports mn`, ANY `pre`.
  `portArgs_eq` / `MeaningP.inst_args`: `args = (instSpineArgs e).drop (length - ports)`, the compiler's
  rule in `translateInstanceUncachedWith` (it never narrows what the compiler accepts: any prefix).
* `MeaningP.deterministic` (the cache-insertion obligation; both readings split one spine at one port count).
* `ArityOK` := the child semantics is defined only at the callee's port count.
* COMPATIBILITY: `meaningP_of_meaning (hA : ArityOK) : Meaning e v → MeaningP e v`;
  `meaningP_agree : Meaning e v → (MeaningP e v' ↔ v' = v)` — where the old meaning is defined the new one
  is exactly it. `addSem_arityOK` (the seven parents' semantics) and `wrapAdd_leaf_agree` instantiate it.
  The seven gate parents' theorems are stated over `Meaning` and are untouched.
* No weakening: `MeaningP` adds nothing beyond reading the compiler's arguments; `ArityOK` is a property
  of the consumer's `ChildSem`, discharged for `addSem` and `pickSem` by evaluation, not assumed.
* `no_meaning_of_portsSpine` — the round-9 finding as a theorem: under `ArityOK`, a call whose spine is
  exactly its port arguments has NO old meaning. `wrapPick_no_old_meaning` instantiates it.
* `wrapPick_meaningP`: `wrapPick`'s body `instEP pick [] [] [sel, x]` has the new meaning
  `pickFn sel x` under `pickSem` (`pickFn` is pick's mux written on packed values; NOT proved equal to the
  Signal body here).
* Compiler side for any prefix: `instEP` (+ spine / getAppFn lemmas, `instEN = instEP [dom]` by `rfl`),
  `instUncached_shapeE` (`instUncached_shape` for `instSpineArgs e = pre ++ argsE`; `hdrop` generalized),
  `instUncached_shape_of_E` (the old lemma as the corollary at `pre = [dom]`).

`pick` is NOT a first-gate child: `kidFacts_of_first` needs `EntryDefines c (quoteDecl dn names n fe)` —
a leading implicit `DomainConfig` binder, all inputs of ONE width `n`, an `FExpr` body (inputs, literals,
binary operators). `pick` has no domain binder, inputs of widths 2 and 8, and a mux of compares. Its child
facts would come from the mixed-gate child theorem (`Tools.ShippingGateChild.gate_child_full` →
`ChildFn`, as `#gate_child pick` generates); a `kidFacts_of_gate` (ChildFn → `KidFacts`) is not written.

NEXT OBSTACLE (why there is no `wrapPick_gate_cone_runK'` yet): the whole unified recursion is stated
over `Meaning` — `Records` (`Tools/ShippingUnifiedCache.lean`: a recorded wire carries every `Meaning` of
its expression), `Inv`, `Outcome`, `cached_outcome`, `Contract`, `LeafMeaning`, `HierConePreserves(K)`,
`InstLeafK` (`e = instEN …`), `inst_leaf_contract` (`meaning : Meaning (instEN …) v`). For a domain-free
call the leaf premise `LeafMeaning C inputs e v` is unprovable (`no_meaning_of_portsSpine`), and the
expression-cache hit of such a call is unconstrained by `Records` (no old meaning ⇒ no clause). Covering
it needs the recursion indexed by `MeaningP`: either (i) IN PLACE — replace `Meaning.inst` by the
`MeaningP.inst` form and add `[ChildPorts]` beside every `[ChildSem]` (needed because `Records`/`Inv` are
not parametric in the meaning relation; the seven parents are re-established by `meaningP_of_meaning` +
`addSem_arityOK`), or (ii) a parallel copy of the cache/invariant/contract layer over `MeaningP` (larger).
Ruling needed. The compiler-side piece (`instUncached_shapeE` at `pre = []`) is ready for either.

Risks (not built): `MeaningP.deterministic`'s `grind` branch is copied from `Meaning.deterministic`;
`view (instEP pick [] [] [fvar, fvar]) = none` is closed by `rfl` (as `wrapAdd`'s 3-argument call is);
`instUncached_shapeE` is the old proof with `hsp` for `instEN_spineArgs` and an explicit arity bound.

## Unit 2 — a narrower argument into a wider port

Files: `Tests/Compiler/NarrowArgPortTest.lean` (target-only; `lake build Tests.Compiler.NarrowArgPortTest`,
after `Tests.Compiler.ShippingHierarchySoundnessTest`), and `instUncached_linkedE` added to
`Tools/ShippingInstanceMeaningP.lean` (rebuild that lib first).

Answer: YES, a type-correct source exists — Lean's typing does NOT force exact widths at a call of a
WIDTH-GENERIC child: `parentW4 a b := childW 4 a b` (4-bit arguments) type-checks, while `childW` is
compiled ONCE at the fallback width 8 (`extractWidth`'s `return 8`), so its ports are 8 bits. It is not
accepted: every emit site (`Sparkle/Compiler/Elab.lean` lines ~6759, ~6775 legacy; ~8601, ~8663 certified)
runs `instLinkCheck` before `emitInstance`, refusing any connection whose parent wire is not declared at
exactly the port width. PREDICTION for the test's `run_cmd`: `NARROWARG parentW4 REFUSED: Instance of …childW:
a connected wire's width differs from the port's width …` (the twin of the BUILT `parentW16` refusal); if
it compiles instead, the `run_cmd` FAILS the build with the module's shape (a finding).
For a FIXED-width child no type-correct narrow argument exists: there is no width-changing coercion
between Signals (`Signal.lean` has `Coe (BitVec n) (Signal dom (BitVec n))`, `Coe Bool (Signal dom Bool)`
only), so the source must widen explicitly. `parentZext a b := child16 (setWidth 16 <$> a) (… b)` —
PREDICTION: compiles, ONE instance, `designLinked` true, each argument a 16-bit parent wire assigned the
zero-extended byte; `out = (zext a + zext b) mod 2^16`, which IS the source. The SV is logged
(`NARROWARG parentZext SV:`). `#check_failure` records that `child16 a b` with bytes does not elaborate.

The machine route (`closeInsts` / `instStmt`) has NO width guard, but its call reader only reads children
with literal-width binders (`machInstCall?` → `instSignature?` → `telescopeKinds` →
`mixedGateBinderKind?`), so a width-generic child is never a machine-route call, and the argument `let`
is typed at the child's binder kind (= the argument's Lean type). Not proved here; a reading.

General lemma (`instUncached_linkedE`): an uncached lowering of a call with ANY prefix (`pre ++ argsE`,
width arguments included) that returns either hit the validated cache, or put ONE `.inst` into
`t.module.body` with `Linked t.module mc conns` — every connection a parent name declared at exactly its
port's width. Width agreement is by the compiler's guard, NOT by typing.

## Integration (integrator, 2026-10-15) — BUILT with one fix
Applied on poc 17560812 (lakefile conflict: appended lean_libs at the end — kept both; second commit applied
as a diff). Run `w1` (cgrun, 3 GiB, swap 0, `-j 1`): `Tools.ShippingInstanceMeaningP`,
`Tests.Compiler.WrapPickMeaningTest` exit 0 as written; `Tests.Compiler.NarrowArgPortTest` failed only because
a doc comment preceded `#check_failure` (changed to a line comment); then exit 0.
Axioms: `MeaningP.deterministic`, `meaningP_agree`, `instUncached_shapeE`, `instUncached_shape_of_E`,
`instUncached_linkedE` [propext, Classical.choice, Quot.sound]; `meaningP_of_meaning`,
`no_meaning_of_portsSpine`, `wrapPick_meaningP`, `wrapPick_no_old_meaning` [propext, Quot.sound].
MEASURED log lines:
* `WRAPPICK body = instEP pick [] [] [bvar 1, bvar 0]; spine = the two ports`
* `NARROWARG childW compiled ports: inputs [(_gen_x, 8), (_gen_y, 8)], outputs [(out, 8)]`
* `NARROWARG parentW4 REFUSED: Instance of …childW: a connected wire's width differs from the port's width. …`
  (as predicted: a type-correct source with a 4-bit argument into a width-generic child compiled at 8 is
  REFUSED by `instLinkCheck`, not miscompiled)
* `NARROWARG parentZext: 4 statements, 1 instance statements, designLinked true …`; the printed SV connects
  `._gen_x(({8'd0, _gen_a} & 16'd65535))`, `._gen_y(({8'd0, _gen_b} & 16'd65535))` to the 16-bit child —
  the zero-extension expressions (prediction said "16-bit wires": after printing, the connections are the
  extension expressions), equal to the source's `setWidth 16`; the child computes `(x + y) & 16'd65535`.
Status: `MeaningP` (compiler's last-#ports rule) agrees with `Meaning` wherever the latter is defined;
`wrapPick` has the new meaning and provably no old one. A `wrapPick` cone theorem is BLOCKED: the cache /
invariant / contract layer is stated over the old `Meaning` — either (i) in place: `Meaning.inst` to the new
form with `[ChildPorts]`, the seven re-established via the agreement lemma, or (ii) a parallel copy over
`MeaningP`. `pick` is not a first-gate child (needs `kidFacts_of_gate`, not written). The machine route's
instance emission has no width guard; width-generic children do not reach it BY READING only.

# DG-READKINDS U7 freeze (Issue sparkle-gen5-dg-readkinds; base 36318286 on kjob/g5rk-r6, branch kjob/g5rk-r7) — DESIGN ONLY, no Lean yet

Extends `DG_READKINDS_FREEZE.md`, `..._U5_FREEZE_REV3_1.md`, `..._U6_FREEZE.md`. Sections not named here are unchanged.
New Lean only in NEW files `Tools/ShippingGen5ReadKindsU7.lean`, `Tests/Gen5/ReadKindsU7Check.lean` (lakefile `lean_lib` additions only).
No edit of the compiler, `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, `Tools/Prototype/DGenProv.lean`, `Tools/ShippingGen5Env.lean`;
no new TRUSTED boundary / law / axiom; FG not reduced; `GenWF` not strengthened; no sorry / native_decide.

Wording: "not supplied / this survey found no route" describes this survey, not impossibility. A "mutant" is a rejection by signature/defeq of a changed
statement, not a semantic counterexample. A result resting on a named premise is **conditional = intermediate**, never counted as a supply.
Nothing below is a real-run tie, reader coverage, or an FG supply; the Issue stays open.

## 1. T3 — remaining `Read` fields (`Tools/ShippingMachineCommand.lean:390-413`, `readMachine` `:440-541`)

Same method as U6d (`readMachine_root`): repeat the `readMachine_run` walk and keep, in the conclusion, facts that the walk's `generalize … = o` hypotheses give. Nothing about
`partial` defs is unfolded. `Read` has 18 fields; status of each (E := `GenEntry ci env`, T := `E.type`, `S := structEnv env`):

| field | status | statement kept (real names) |
|---|---|---|
| `shape`, `entry` | closed (U-prior, `ReadConcl`) | — |
| `rootLets`, `sel?`, `hasOuter` | closed (U6d, `ReadRoot`) | — |
| `nDecl` | **closes (U7)** | `r.nDecl = bsIn.length`, `mixedGatePeel (packTupleInputs entryV) = some (bsIn, b0)`, `E.value? = some entryV` |
| `nIn` | **closes (U7)** | `r.nIn = r.nDecl + r.shape.insts.length` |
| binder count | **closes (U7)** (the `unless` guard) | `r.shape.binders.length = r.nIn + r.shape.layout.slots.length + r.shape.layout.lets` |
| `tuple` | **closes (U7)** | `r.tuple = machTupleKinds? T` |
| `ctor?`, `outNames` | **closes (U7)** | `∃ outKinds, (match machTupleKinds? T with \| some ks => some (none, [("out", MixedGateBinder.bits (ks.map machWidth).sum)]) \| none => machOuts? S T) = some (r.ctor?, outKinds) ∧ r.outNames = outKinds.map (·.1)` |
| `bposL`, `vposL`, `vwL` | **closes (U7)** | functions of `r.shape.binders.map (·.2)` (the `idx.filterMap` expressions of the source, written out) |
| `dom` | **partly (U7)**: existence of the source domain expression only | `∃ srcDom' snd, machDom? (r.shape.insts.length + r.shape.layout.slots.length + r.shape.layout.lets) srcDom' = some (r.dom, snd)` |
| `srcDom` | **not closed** by this survey: 4-way branch (`run?`, `Expr.find?`, `readMachine.loopLet`, `readMachine.resDom`) and `bvar` shift; relating `srcDom'` to `r.srcDom` needs all branches. Route exists in principle (more cases of the same walk); not in U7 | — |
| `ls`, `outs`, `nexts` | **not closed**: they are results of `typed … : MetaM (List AnyTerm)` (`mapM` in MetaM with `throwError`) and of the `partial` `unq`; this survey found no `RunsTo`-for-`mapM` lemma and no theorem about `unq` | — |

Exact definition (U7a), all binders explicit, no `variable`:
```lean
def ReadFields (ci : Lean.ConstantInfo) (env : Lean.Environment) (r : Read) : Prop :=
  ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (b0 : Lean.Expr),
    (GenEntry ci env).value? = some entryV ∧
    mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, b0) ∧
    r.nDecl = bsIn.length ∧
    r.nIn = r.nDecl + r.shape.insts.length ∧
    r.shape.binders.length = r.nIn + r.shape.layout.slots.length + r.shape.layout.lets ∧
    r.tuple = machTupleKinds? (GenEntry ci env).type ∧
    (∃ outKinds : List (String × MixedGateBinder),
      (match machTupleKinds? (GenEntry ci env).type with
        | some ks => some (none, [("out", MixedGateBinder.bits (ks.map machWidth).sum)])
        | none => machOuts? (structEnv env) (GenEntry ci env).type) = some (r.ctor?, outKinds) ∧
      r.outNames = outKinds.map (·.1)) ∧
    r.bposL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (p, k) => if k == .bool then some p else none) ∧
    r.vposL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (p, k) => match k with | .bits _ => some p | _ => none) ∧
    r.vwL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (_, k) => match k with | .bits w => some w | _ => none) ∧
    ∃ (srcDom' : Lean.Expr) (snd : Sparkle.IR.Type.ResetKind),
      machDom? (r.shape.insts.length + r.shape.layout.slots.length + r.shape.layout.lets) srcDom' = some (r.dom, snd)

theorem readMachine_fields {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w') :
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ ReadConcl ci env r ∧ ReadFields ci env r
```
(`ReadRoot` is kept as is; U7 does not restate it. If the combined theorem is wanted later it is a conjunction of two walks.) Proof route: the U6d walk with `ReadFields` as the goal predicate;
the pieces come from the walk's `hv`, `hp`, `hx_nDecl…`, `hd`, `hk`, `hx_tupq`. Risk: memory/time of a second copy of the walk (U6d built in 816 jobs without trouble). If it does not build, it is
recorded as "route found, not built", not as closed. The exact shape of `tup?` match (`some ks`/`none`) in the source is rendered as the `match` above; if the elaborated form differs
the Check's independent Expected is the arbiter and any difference is reported, not patched into the Expected.

## 2. hX / hw — what supplies the premises of `readMachine_agrees_runReads`

Premises of U6b: `hX : declName = X`, `hg : GetEnvFrame …`, `hw : envAt cref w = envAt cref w1`.

* `hX`: the `X` of `RunReadsAt` is the target of `synthesizeCombinationalCore X`; `declName` is the argument of `readMachine`. This survey found no theorem or definition relating the two runs
  (`RunReadsAt` has no `readMachine` field; `Tools/ShippingGen5RunReads.lean:38-73`). **Not supplied / this survey found no route.** It stays a hypothesis.
* `GetEnvFrame`: the only definition/uses are in `Tools/ShippingEnvSnapshot.lean` (`EnvFrame`, `GetEnvFrame`, `envFrame_getConstInfo`) and the lemmas of `Tools/ShippingGen5Env.lean`
  (E3 `ReadsAt.of_frame`, E6 premise); grep of `Tools/` found no proof of `GetEnvFrame` (it is about the opaque `ST.Ref.get`). **Not supplied / this survey found no route.**
* `hw`: `ReadsAt env₀ cref u` (E1-E6) is a ONE-WAY inclusion of constants plus equality of the three derived arguments (`instancePredicate`, `userInliner`, `structEnv`); it does not give
  `envAt cref w = envAt cref w1` (equality of whole environments). So `hw` is **not** supplied by E1-E6.
* What E1-E6 do give: with `ReadsAt env₀ cref u` at the relevant worlds the entry arguments of the two runs coincide with those of `env₀`, which is all `r.entry`/`r.shape` mention. So `hw`
  and `hg` can be replaced by the single DG-ENV premise `hall : ∀ u, ReadsAt env₀ cref u` (the premise of E6, "supplied nowhere"). That is a different CONDITIONAL result, not a supply:

```lean
/-- U7b, CONDITIONAL (intermediate): replaces U6b's `hg` and `hw` by the DG-ENV premise `hall`. `hX` stays. -/
theorem readMachine_agrees_runReads_of_readsAt {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {w1 w2 w3 w5 : Void IO.RealWorld} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment}
    {shape : MachineShape}
    (hget : RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2)
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3)
    (henv' : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5)
    (hshape : machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (structEnv envR') = some shape)
    {env₀ : Lean.Environment} (hall : ∀ u, Tools.ShippingGen5Env.ReadsAt env₀ cref u) (hX : declName = X) :
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape
```
Proof route: `readMachine_run`; `getEnv_value`, `getConstInfo_value`; `ci_of_readsAt`, `envR_of_readsAt` (E4/E5) at the worlds `w`, `v1`, `w1`, `w2`, `w3`; `Option.some.inj`.
The `ci` of `readMachine` and the `ci` of `hget` are both `env₀.find? X`, so equal; the three derived arguments rewrite to `env₀`'s. The imports add `Tools.ShippingGen5Env`.
`hall` is a premise that no theorem here supplies, `hX` likewise; U6b is kept unchanged. Not claimed: `hentry` supplied, `RunReadsAt` supplied, DG-ENV C0 supplied.

## 3. hq — NO law is added; the exact statement a law would need

hq = "the terms read off the body quote back to it" (`readMachine`'s `unless q.equal shape.body do throwError`). Rows (from U6 §2, unchanged unless stated):

* **Q1**: `Lean.Expr.equal` is `opaque` (`Tools/ShippingCacheSoundness.lean:15-45`); `readMachine` branches on its `Bool` result. A route from `q.equal shape.body = true` to `q = shape.body` needs, as a statement:
  ```lean
  -- NOT ADDED. Would be a TRUSTED soundness law about the opaque (extern) function:
  Lean.Expr.equal_sound : ∀ a b : Lean.Expr, Lean.Expr.equal a b = true → a = b
  ```
  Impact: it is a new trust boundary (an assumption about the Lean runtime's `Expr` equality, i.e. extern code) that `Laws` does not contain; with it the success of `readMachine` gives
  `quote … packed = shape.body` (hq) for the walked `packed`/`dom`, the other half of what coverage needs together with Q2. This survey found no route from the guard to the equation that avoids the opaque call (this is the extent of the survey; it does not show impossibility or that this law is necessary). Adding it is the user's decision (new law); this unit does not add it, and does not ask for it now.
* **Q2** (`unq c shape.body = some whole` is `partial`, `ShippingMachineCommand.lean:93`): this survey found no theorem relating `unq` to `readN`/`readTot`; stays "not supplied / route not found". No law named here.
* **Q3**: hq from `readN` success via `readN_sound` + `machine_body_of_readN` (U3): conditional on `hread : readN cfg k body = some r`, which is the coverage question; it remains a premise (coverage side), not supplied.
* U7 adds no theorem for hq.

## 4. Check plan (`Tests/Gen5/ReadKindsU7Check.lean`)

* TYPE: independently written `Exp…` statements (written from this document, not copied from the Lean) vs `readMachine_fields`, `ReadFields` (def, body compared), `readMachine_agrees_runReads_of_readsAt`;
  same reducible comparator `Tests.Gen3.ExpectedType`; positive control (comparator accepts a copy). Count = comparisons excluding summary lines.
* MUTANT (signature/defeq rejection only, not semantic counterexamples), counted as actually rejected: `ReadFields` with `r.nIn = r.nDecl` (insts dropped); with `r.tuple = none`; with `bposL` and `vposL` swapped;
  U7b with `envR'` in the entry; U7b without `hX`; U7b without `hall`; U7b conclusion without the shape conjunct.
* CLOSURE: explicit-value scan as in `ReadKindsU6Check`; `T1Hyp`/`T1HypND`/`Laws` not reached; `Lean.Expr.equal/eqv` reached only through the program `readMachine` (logged as a fact, not a law used);
  unknown constant = fail.
* AXIOMS: only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
* STATUS line lists NOT supplied: `GetEnvFrame`, `hX`, `hw`/`hall`, `srcDom`, `ls/outs/nexts`, hq (Q1: needs `Expr.equal_sound`; Q2; Q3 premise `hread`), real-run tie, coverage, FG.

## 5. Not claimed
hq; `Expr.equal_sound` (not added); `hentry`; `RunReadsAt` / `GetEnvFrame` / `hX` / `hall` supplied; `srcDom`, `ls`, `outs`, `nexts`; real-run tie; reader coverage; FG, M5, DG-COVER, DG-READKINDS completion.
After Lean commits the Issue stays `doing` (clean build is the coder's).

## 6. Addendum (reviewer note, non-blocking)
* ReadRoot (U6d) and ReadFields (U7a) are separate walks. If they are ever combined, the existence witnesses (`ci`/`env`/`entryV`/body) must not be identified by a mere conjunction of two existence conclusions: either prove the witnesses equal, or state both facts from one and the same walk. U7 does not combine them.

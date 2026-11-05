# DG-READKINDS U5 freeze, rev3 (Issue sparkle-gen5-dg-readkinds; base 069c7556, branch kjob/g5rk-r4)

Extends `scripts/gen5/DG_READKINDS_FREEZE.md` (rev2 + §9/§10). Sections not named here are unchanged.
**Status: design only. No Lean written for U5 in this revision, nothing built for it. Lean for §2 is not started until the reviewer approves.**
New Lean (if approved) goes in a NEW file `Tools/ShippingGen5ReadKindsU5.lean` and a new check `Tests/Gen5/ReadKindsU5Check.lean`
(lakefile `lean_lib` additions only). No compiler / `Tools/ShippingGen2Defs.lean` / `T1Hyp` / `T1HypND` / `Elab*.lean` edit; no new
TRUSTED boundary, law, FG/guarantee change; FG is not reduced; `GenWF` is not strengthened.

Wording: "not supplied / this survey found no source or route" describes this survey, not impossibility. A "mutant" is a rejection by
signature/defeq of a changed statement, not a semantic counterexample. Results below that rest on a named premise are
**conditional = intermediate**, never counted as a supply.

What was read for this revision (read-only): `Tools/ShippingShapeDecomp.lean` (whole), `Sparkle/Compiler/Elab.lean:5056-5100`
(`machineShape?`) and `:5272-5282` (`entryConst`), `Tools/ShippingMachineCommand.lean:440-541` (`readMachine`),
`Tools/ShippingGen5RunReads.lean:38-73` (`RunReadsAt`), `Tools/ShippingGen5ReadKinds.lean` (U1-U4, `RootFacts`),
`DGEN_FREEZE.md` (par/gen5-t2) rows DG-COVER / DG-DATAOF and §2.4 R5. `kjob lake build Tools.ShippingShapeDecomp` ran in this pod:
exit 0, 229 jobs (so the file the rev2 text called "build status not checked" builds on this tree; recorded as a fact about this tree).
`dataOf` / `GenWF` / `GenData` exist only as design text in par/gen5-t2 `DGEN_FREEZE.md`; they are not in this tree, so §2.2 uses the
shapes `readMachine` computes, not `dataOf`.

---

## 1. P3 — can the peel / float halves of `RootFacts` be derived from `shapeEq` through `machineShape?_decomp`?

`RootFacts` (U5, type only, `Tools/ShippingGen5ReadKinds.lean`):
```lean
structure RootFacts (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder))
    (entryBody₀ entryBody : Lean.Expr) : Prop where
  pack  : mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, entryBody₀)
  float : entryBody = Sparkle.Compiler.MachRawSurface.rootFloat entryBody₀
```

### 1.1 Peel half (`pack`): a route was found; it closes in two steps, one gap remains named

`ShapeDecomp.peel` (`ShippingShapeDecomp.lean:63`) is literally
`mixedGatePeel (packTupleInputs d.value) = some (bs, e)`, and `machineShape?_decomp` (`:71`) produces it from
`machineShape? sym params (.defnInfo d) senv allow = some sp`. `RunReadsAt.shapeEq` has the form
`machineShape? false [] E (structEnv envR') = some shape` with `E := entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)`
(a `ConstantInfo`, not syntactically `.defnInfo d`). `machineShape?` returns `none` on every non-`defnInfo` constructor
(the `match ci with | .defnInfo d => … | _ => none`; to be confirmed on the `_` arm when written), so `E` is a `defnInfo`.

Planned lemmas (complete types; proofs not tested):
```lean
/-- (a) `machineShape?` returning a shape forces a definition and gives the peel at ITS value. -/
theorem peel_of_machineShape {sym : Bool} {params : List (String × Nat)} {ci : Lean.ConstantInfo}
    {senv : Sparkle.Compiler.Elab.StructEnv} {allow : Bool} {sp : MachineShape}
    (h : Sparkle.Compiler.Elab.machineShape? sym params ci senv allow = some sp) :
    ∃ (d : Lean.DefinitionVal) (bs : List (Lean.Name × MixedGateBinder)) (e : Lean.Expr),
      ci = .defnInfo d ∧ ci.value? = some d.value ∧
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e)

/-- (b) the `pack` field of `RootFacts`, at the value of the constant the shape came from. -/
theorem rootFacts_pack_of_machineShape {sym : Bool} {params : List (String × Nat)} {ci : Lean.ConstantInfo}
    {senv : Sparkle.Compiler.Elab.StructEnv} {allow : Bool} {sp : MachineShape}
    (h : Sparkle.Compiler.Elab.machineShape? sym params ci senv allow = some sp) :
    ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (entryBody₀ : Lean.Expr),
      ci.value? = some entryV ∧
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, entryBody₀)

/-- (c) at a `RunReadsAt` run (instance of (b) at `shapeEq`). -/
theorem rootFacts_pack_of_runReads {mctx cref …} {X w w' raw D b ci envR envR' shape w5 w6}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6) :
    ∃ entryV bsIn entryBody₀,
      (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)).value? = some entryV ∧
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, entryBody₀)
```
(binder list of (c) to be written in full from `RunReadsAt` at implementation; it is the same list as `RunReadsAt`'s, no new variable.)

**What this closes and what it does not.** It closes: for the constant that the compiler core's `machineShape?` accepted, the peel equation
holds at that constant's value. It does **not** supply `RootFacts` at *`readMachine`'s* `entryV`: `readMachine` rebuilds
`entry := entryConst true false [] ci (instancePredicate env) (userInliner env) senv` with its own `env ← getEnv` and `ci ← getConstInfo declName`.
Identifying that `entry` with the `RunReadsAt` one needs `ci`, `env` (vs `envR`), and `senv` (vs `structEnv envR'`) to agree. `RunReadsAt`
exposes `envR` and `envR'` as two separate `getEnv` results and does not claim `envR = envR'` (its header: "Not claimed: … `envR = envR'`, `ci ∈ envR`");
the `readMachine` call is not part of it (P1). So the peel half is **closed against the compiler core's own entry; not linked to `readMachine`'s entry.**
Uniqueness (`Option.some.inj`) makes any two peel equations at the same `entryV` agree, so *given* an entry equality `hentry` the link is immediate; `hentry` itself is the unsupplied part.

### 1.2 Float half (`float`): this survey found no route; not supplied

* `readMachine` applies `rootFloat` directly to the peeled body (`ShippingMachineCommand.lean:467`).
* `machineShape?` applies `rootFloat` to `zeroLit … (inlFoldNat (machNorm senv e))` and then `machLoopAsLet` (`Elab.lean:5088`), i.e. to a
  different argument, and `ShapeDecomp` has **no field about it** (its fields: `peel outsEq binders slots layoutOuts lets`; the body of `sp`
  is not a field).
* `rootFloat` is `partial def` (`MachRawSurface.lean:198`): no equation lemma, so `shape.body` cannot be unfolded to a statement about
  `rootFloat` of anything. A statement `entryBody = rootFloat entryBody₀` is a *definition* in `readMachine` (a `let`), true by `rfl` of that
  program's text *if a run of `readMachine` is available*; from `shapeEq` alone this survey found no route (the two compositions differ and no lemma relates them).
* Therefore: float half = **not supplied; no route found in this survey.** It is *new information about a `partial` composition* and is not attempted by
  any of the lemmas in §1.1. This is not an impossibility claim.

### 1.3 Decision for U5(P3)
Implement §1.1 (a)(b)(c) only (pure, uses an already-built file `ShippingShapeDecomp`, adds no law). Report the float half as unsupplied. Nothing is
counted as `RootFacts` supplied; the combined `RootFacts` still requires `float` and `hentry`.

---

## 2. P2 — `RootFacts` as a named premise of DG-COVER (conditional = intermediate; not a supply)

Because `dataOf` is not in this tree, the premise is stated on what `readMachine` computes, as a **Prop-valued definition** with all variables bound:

```lean
/-- DG-COVER's use of the root computation, as a NAMED PREMISE. A proof of it is a producer; none is supplied (§1). -/
def RootFactsAt (E : Lean.ConstantInfo) : Prop :=
  ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (entryBody₀ entryBody : Lean.Expr),
    E.value? = some entryV ∧ RootFacts entryV bsIn entryBody₀ entryBody

/-- Conditional transport (INTERMEDIATE): if the premise holds at the entry constant, the facts `readMachine` recomputes are those. -/
theorem rootFacts_unique {entryV : Lean.Expr} {bsIn bsIn' : List (Lean.Name × MixedGateBinder)} {b₀ b₀' b b' : Lean.Expr}
    (h : RootFacts entryV bsIn b₀ b) (h' : RootFacts entryV bsIn' b₀' b') :
    bsIn = bsIn' ∧ b₀ = b₀' ∧ b = b'
```
`rootFacts_unique` is a determinism fact (from `Option.some.inj` and `rfl`/`Eq.trans` on `float`); it adds no law. `RootFactsAt` appears only as a
hypothesis of future DG-COVER statements; no theorem concludes `RootFactsAt E`. The Check records: TYPE of both, MUTANT (`float` with wrong argument,
`rootFacts_unique` without `h'`), AXIOMS, CLOSURE (as for U1-U4), and states in its log that `RootFactsAt` has **no producer in the tree**.

---

## 3. P1 — extension of `RunReadsAt` / a `readMachine` run (proposal only; NOT implemented)

`RunReadsAt` is the shared DG-RUNREADS definition (approved separately); changing it, or adding a `readMachine` run, is a shared-definition change and is
outside this Issue. Recorded as a proposal:

| option | change | effect on `RootFacts` | cost / risk | other consumers |
|---|---|---|---|---|
| P1-a | add a field `readRun : RunsTo (readMachine X) … w? r w?'` to `RunReadsAt` | `float` becomes the `let` of `readMachine`'s program text; `pack` too; `hentry` becomes the same run's `entry` | edits a shared structure; every producer (`runReads_of_run`, RR3) must now produce a `readMachine` run, i.e. prove `readMachine` succeeds on every accepted run (that is the DG-COVER coverage, not given) | all `RunReadsAt` users |
| P1-b | a separate structure `ReadMachineAt` next to `RunReadsAt`, carrying the `readMachine` run and an equation of its `ci`/`env`/`senv` with the core's | no edit to the shared structure | new definition (needs reviewer + user approval since it extends the shared evidence); still needs the coverage producer | only new users |
| P1-c | (no change) keep `RootFactsAt` as a premise (§2) | conditional | none | none |
Note on the shape of the run: `Read` (the result of `readMachine`) has no `entryBody` field; `entryBody` influences `rootLets`, `sel?`, `run?`, `dom` only. So even
with a run, `float` is visible only through those fields, not as a returned value; P1 would therefore also need a statement relating them to `rootFloat entryBody₀`.
Recommendation: keep P1-c until the reviewer/user decide; P1-a/b are not adopted and not requested here.

---

## 4. hq (body-is-quotation, B1-B4) — which rows close from existing theorems

Statement (DG-COVER remainder, rev2 §3): *for every body of a successful machine-route run there is `t` with `body = quote … t`.*

| row | route | uses | closes `hq` for an arbitrary successful run? | status |
|---|---|---|---|---|
| H1 | per declaration with endpoint | `f.machine_body` by `Eq.refl` (`ShippingNoPortsCommand.lean:127`, `ShippingSatCert2Command.lean:46-52`) | **No**: it is a per-declaration kernel term produced by `#machine_endpoint`, not a theorem over runs | closes the declarations that have an endpoint only |
| H2 | from a successful `readN` | `readN_sound` (`ShippingReaderApp.lean:349`) + `machine_body_of_readN` (U3) | **Conditional**: `hread : readN cfg k body = some r` is the premise; its existence on a run is the *coverage* question itself (reader-completeness on bodies, not on quotations) | gives quote-back from a reading; reading supply is the open part |
| H3 | `quote` ∘ `readN` roundtrip | `readN_quote`, `readTot_quote` (U1/U2) | **Direction wrong**: these go from `body = quote t` to reading, so they presuppose `hq` | no |
| H4 | `Expr.equal` check of `readMachine` (`:533`) | none: `Expr.equal` is `opaque` (`ShippingCacheSoundness.lean:15-45`); no `Expr.equal a b = true → a = b` theorem in `Tools/` (grep of `equal_eq` / `equal_iff` found none) | **No** | = B1 (new law), not adopted |
| H5 | `unq` equation | `unq` is `partial` (`ShippingMachineCommand.lean:93`); `Tools/Prototype/DGenProv.lean:77` only generalizes `unq c shape.body = o` as a premise | **No** | = B4/B2 (agreement with a `partial`), no route found |
| H6 | `ShapeDecomp` | fields `peel outsEq binders slots layoutOuts lets` | **No**: no field about `sp.body`; it covers binders/layout only | no |
| H7 | `RunReadsAt` | has `shapeEq`, `gates`, `chain`; no body field | **No** | no |
| H8 | coverage theorem takes `hq` | B3 | closes only conditionally | intermediate (conditional) |

Result of the table: **no row closes `hq` for an arbitrary successful run from existing theorems.** H1 covers declarations that already carry an endpoint
term; H2 turns a reading into `hq` (the converse of what DG-COVER needs). This is a statement about this survey (rows examined above), not an impossibility claim.

---

## 5. Implementation plan (after approval; Lean not started)

| step | content | lines (estimate) |
|---|---|---|
| 1 | `peel_of_machineShape`, `rootFacts_pack_of_machineShape`, `rootFacts_pack_of_runReads` (new file, imports `Tools.ShippingShapeDecomp`, `Tools.ShippingGen5RunReads`, `Tools.ShippingGen5ReadKinds`) | 40-100 |
| 2 | `RootFactsAt`, `rootFacts_unique` | 15-30 |
| 3 | `Tests/Gen5/ReadKindsU5Check.lean`: TYPE (5 items) against independent `Exp…`; MUTANT (`pack` at wrong value, `rootFacts_pack_of_runReads` with `envR'` for `envR`, `rootFacts_unique` without `h'`); AXIOMS (standard 3); CLOSURE (same scanner pattern as `ReadKindsCheck`, with same-reducible comparator, positive and negative controls, unknown = fail); a log line "RootFactsAt: no producer" | 150-250 |
Build: `kjob lake build` one target at a time; after Lean commits the issue stays `doing` with the note "clean build は coder". Risks: (R-a) the `_` arm of
`machineShape?` may not reduce by `simp` after `unfold` (then use `cases ci` and `unfold` per arm); (R-b) `ConstantInfo.value?` on `defnInfo` takes an `allowOpaque` default argument,
(c)'s statement is then stated with that default as written in the source; (R-c) `RunReadsAt` has many implicit parameters, the exact binder list is copied when written.

## 6. Review questions
* **Q5.** Approve §1.1 (peel half only, pure, no law) as U5's sole implemented unit, with float/`hentry` reported as unsupplied?
* **Q6.** Approve `RootFactsAt` + `rootFacts_unique` (§2) as the named conditional premise form (intermediate, not a supply)?
* **Q7.** P1-a/b/c (§3): leave to a separate shared-definition decision; default P1-c.

## 7. Not claimed
* Not claimed: `RootFacts` supplied; the float half supplied or impossible; `hentry` (RunReadsAt entry = readMachine's entry) supplied; `hq` supplied for any run beyond endpoint declarations; reader coverage on bodies; FG, M5, DG-COVER, quotation, a real run connection.
* The `ShippingShapeDecomp` build (229 jobs, exit 0) is a pod build on this tree, not a clean issue-linked build.
* §1.1 lemmas are targets: not yet written, not elaborated.

# DG-READKINDS U5 freeze, rev3.1 (Issue sparkle-gen5-dg-readkinds; base 28a0a1f7, branch kjob/g5rk-r5)

Amends `scripts/gen5/DG_READKINDS_U5_FREEZE_REV3.md` (rev3, reviewer changes_requested R1/R2). Sections of rev3 not named here are unchanged:
the peel route (a)(b) of §1.1, `rootFacts_unique`, the hq table §4 (limited "no row closes in this survey" report) and P1 (§3, no change needed).
New Lean goes in a NEW file `Tools/ShippingGen5ReadKindsU5.lean` and `Tests/Gen5/ReadKindsU5Check.lean` (lakefile `lean_lib` additions only).
No compiler / `Tools/ShippingGen2Defs.lean` / `T1Hyp` / `T1HypND` / `Elab*.lean` edit; no new TRUSTED boundary, law, FG/guarantee change; FG not reduced; `GenWF` not strengthened.
A new auxiliary definition (below: `RootFactsAt`, `RootFactsTie`) is a Prop-valued definition over existing types; it is not a guarantee, law, shared definition or trust change.

Wording: "not supplied" = this survey found no source or route; it is not an impossibility claim. A "mutant" is a rejection by signature/defeq of a
changed statement, not a semantic counterexample.

## R1. Existence version = a corollary of the peel; fixed-body tie = separate, unsupplied

`RootFactsAt` quantifies `entryBody` existentially. Given a peel `mixedGatePeel (packTupleInputs v) = some (bs, b0)`, take `entryBody := rootFloat b0`;
`float` is `rfl`. Nothing about the `partial def rootFloat` is unfolded, and no `readMachine` run is used. So the existence version IS supplied by
the peel (§1.1 (a)(b)). rev3 §1.3/§2/§5 "no producer" / "float unsupplied" is withdrawn for this proposition and kept only for the tie below.

Two different propositions (types fixed here; `E : Lean.ConstantInfo`):

```lean
/-- EXISTENCE version. SUPPLIED (corollary of the peel). entryBody is existential. -/
def RootFactsAt (E : Lean.ConstantInfo) : Prop :=
  ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (entryBody₀ entryBody : Lean.Expr),
    E.value? = some entryV ∧ RootFacts entryV bsIn entryBody₀ entryBody

/-- TIE to an externally FIXED body. NOT supplied: `entryBody` is a parameter, not chosen here. -/
def RootFactsTie (E : Lean.ConstantInfo) (entryBody : Lean.Expr) : Prop :=
  ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (entryBody₀ : Lean.Expr),
    E.value? = some entryV ∧ RootFacts entryV bsIn entryBody₀ entryBody
```
(`E.value?` uses the default `allowOpaque := false`, as in the source.)

Supplied lemmas (complete types; this file's `variable`/`open` list: `Lean`, `Sparkle.Compiler.Elab`, `Tools.ShippingGen5ReadKinds`, `Tools.ShippingShapeDecomp`, `Tools.ShippingGen5RunReads`;
`mixedGatePeel`, `MixedGateBinder`, `MachineShape`, `StructEnv` as in `ShippingShapeDecomp`):

```lean
theorem peel_of_machineShape {sym : Bool} {params : List (String × Nat)} {ci : Lean.ConstantInfo}
    {senv : Sparkle.Compiler.Elab.StructEnv} {allow : Bool} {sp : MachineShape}
    (h : Sparkle.Compiler.Elab.machineShape? sym params ci senv allow = some sp) :
    ∃ (d : Lean.DefinitionVal) (bs : List (Lean.Name × MixedGateBinder)) (e : Lean.Expr),
      ci = .defnInfo d ∧ ci.value? = some d.value ∧
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e)

theorem rootFacts_of_peel {entryV : Lean.Expr} {bsIn : List (Lean.Name × MixedGateBinder)} {entryBody₀ : Lean.Expr}
    (h : mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, entryBody₀)) :
    RootFacts entryV bsIn entryBody₀ (Sparkle.Compiler.MachRawSurface.rootFloat entryBody₀)      -- ⟨h, rfl⟩

theorem rootFactsAt_of_machineShape {sym : Bool} {params : List (String × Nat)} {ci : Lean.ConstantInfo}
    {senv : Sparkle.Compiler.Elab.StructEnv} {allow : Bool} {sp : MachineShape}
    (h : Sparkle.Compiler.Elab.machineShape? sym params ci senv allow = some sp) :
    RootFactsAt ci                                   -- ⟨v,bs,b0, rootFloat b0, hvalue, rootFacts_of_peel hpeel⟩

theorem rootFactsAt_of_runReads
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {X : Lean.Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6) :
    RootFactsAt (Sparkle.Compiler.Elab.entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
      (Sparkle.Compiler.Elab.userInliner envR) (Sparkle.Compiler.Elab.structEnv envR))
    -- from R.shapeEq : machineShape? false [] (entryConst …) (structEnv envR') = some shape

theorem rootFacts_unique {entryV : Lean.Expr} {bsIn bsIn' : List (Lean.Name × MixedGateBinder)} {b₀ b₀' b b' : Lean.Expr}
    (h : RootFacts entryV bsIn b₀ b) (h' : RootFacts entryV bsIn' b₀' b') : bsIn = bsIn' ∧ b₀ = b₀' ∧ b = b'

theorem rootFactsTie_unique {E : Lean.ConstantInfo} {b b' : Lean.Expr}
    (h : RootFactsTie E b) (h' : RootFactsTie E b') : b = b'

theorem rootFactsAt_iff_tie {E : Lean.ConstantInfo} : RootFactsAt E ↔ ∃ body : Lean.Expr, RootFactsTie E body
```
Binders of `rootFactsAt_of_runReads` are those of `RunReadsAt` in `ShippingGen5RunReads.lean:38-41` (`mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6`), all implicit,
types copied verbatim (the section `variable`s `mctx mref cctx cref` are listed explicitly because the new file has no `variable` line); `Void`, `MachineShape`, `StructEnv` resolve
with the same `open` list as `ShippingGen5RunReads` (checked when the file is written; a mismatch is fixed by qualifying, not by changing a type). The conclusion's constant is the `E` of
`RunReadsAt.shapeEq` with its `structEnv envR` argument (not `envR'`); `shapeEq` uses `structEnv envR'` only as the `senv` of `machineShape?`, which `peel_of_machineShape` leaves free.

The `machineShape?` non-`defnInfo` arm is `| _ => none` (`Elab.lean:5200`), so `h` forces `ci = .defnInfo d`.

## What is supplied and what is not (types separated)

| proposition | status | route |
|---|---|---|
| `RootFactsAt (entryConst … )` at a `RunReadsAt` run | **supplied** (peel corollary) | `rootFactsAt_of_runReads` |
| `RootFactsAt ci` at an accepted `machineShape?` | **supplied** | `rootFactsAt_of_machineShape` |
| `RootFactsTie E body` for the body `rootFloat entryBody₀` of `E`'s own peel | supplied (`rootFacts_of_peel`) | trivially |
| `RootFactsTie E body` for a body FIXED outside this statement (`readMachine`'s `entryBody`, a Read result, `shape.body`) | **not supplied; this survey found no route** | needs the body's provenance |
| `hentry`: `readMachine`'s `entry` = the `RunReadsAt` entry (`ci`, `env` vs `envR`, `senv` vs `structEnv envR'` agree) | **not supplied** | `RunReadsAt` keeps `envR`/`envR'` separate and has no `readMachine` run |
| `hq` | **not supplied** (rev3 §4 table unchanged) | — |

Not claimed: any real-run tie, reader coverage, quotation, FG, M5, DG-COVER completion. `RootFactsAt` being supplied does NOT make `RootFacts` hold for `readMachine`'s `entryBody`.

## R2. §1.1(c) — binder-complete (replaces the `{mctx cref …}` text of rev3)

Replaced by `rootFactsAt_of_runReads` above (all 16 binders typed, scope as stated). Differences from rev3 (c): the conclusion is `RootFactsAt (entryConst …)` instead of an
untyped `∃ entryV bsIn entryBody₀, … value? …`; the peel-only unfolded statement is `peel_of_machineShape` (a) at `ci := entryConst …`.

## Check plan (`Tests/Gen5/ReadKindsU5Check.lean`)

* TYPE: each theorem above against an independently written `Exp…` statement, same comparator as `ReadKindsCheck` (`Tests.Gen3.ExpectedType.checkExpected`, reducible binder-by-binder); `RootFactsAt`/`RootFactsTie` by comparing definition bodies (`stmtOf`) with independent `Exp…Def`.
* MUTANT (signature/defeq rejection only): `rootFactsAt_of_runReads` with `envR'` in place of `envR` in `structEnv`; `rootFactsTie_unique` without `h'`; `RootFactsTie` with `∀` for `∃`; `rootFacts_of_peel` with `entryBody₀` in place of `rootFloat entryBody₀`; `RootFactsAt` with the roles of `entryBody` and `entryBody₀` swapped.
* Positive/negative comparator control: the comparator accepts a copy of a statement and rejects each mutant (mutant failures are asserted, an accepted mutant throws).
* CLOSURE: explicit-value scan as in `ReadKindsCheck` from the new theorems; must not reach `T1Hyp`/`T1HypND` (name, raw proj, rec/casesOn/recOn), `Laws`, `Expr.equal`, `Expr.eqv`; positive control reaches `machineShape?_decomp`-free constants as stated by the proof; unknown constant = fail; fixture controls for single-constant forbid reused.
* AXIOMS: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry` / `axiom` / `native_decide`.
* The check log does NOT carry a "no producer" line for `RootFactsAt`. It records: `RootFactsAt` supplied by the peel; `RootFactsTie` at an externally fixed body, `hentry`, `hq`: not supplied.

Build: `kjob lake build` one target at a time in the pod; after Lean commits the issue stays `doing` ("clean build は coder").

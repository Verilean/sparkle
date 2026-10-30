# DC-CONNECT: DeclConnect on the actual source — full-type freeze (rev2)

Issue `sparkle-gen5-dc-connect` (parent `sparkle-gen5-decl-bridge`; units DC-FORM / DC-SUPPLY / DG-DECLCONNECT).
Base: `par/gen3-combined` 9d26005c (S1 integration). Design sources (read with `git show par/gen5-t2:...`, c398021c):
`DGEN_FREEZE.md` rev2 §2.6 (cited `DGEN:§2.6`), `T2COVER_FREEZE.md` rev2 §2, `DG_ENV_FREEZE.md` rev2.2, and
`scripts/gen2/GENERAL_SPEC.md` (FG §1.1, M5 §5 lines 489-507, §6 table line 535).

**Revision rev2 (answers review R1-R3 on rev1 08293159).** rev1 `adapterOf` (an opaque function into `Σ α, SigAdapter`) is replaced by a CONCRETE `sigShape?` + `SigShape.Ty/applyArgs/obsRes` (§1): the adapter is a function of the actual type, built so that arguments, domain and results are preserved BY CONSTRUCTION; unknown shapes are `none` (never `PUnit`). `DataSoundAt` and `FG_COMPLETE` are fully typed (§1.1, §3). The DCF study (§4a) is written before the pure units.

**Status: design only. No Lean written, nothing elaborated or built.** Every Lean text below is a PROPOSAL; names,
binders and elaboration are unverified. The Lean implementation does not start before the reviewer approves this freeze.

Wording rules used throughout:
- "not supplied" / "this survey found no source or route" is a statement about THIS survey. It is not a claim that
  something is impossible or underivable.
- A "mutant" in §4 is a rejection by signature or defeq of a changed statement. It is not a semantic counterexample.
- Nothing here is a new TRUSTED boundary, law, FG or guarantee change, compiler change, or edit of shared definitions
  (`Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`). Everything that would need one is in §6 and is NOT
  adopted.
- New Lean goes in NEW files only: `Tools/ShippingGen5DeclConnectAbs.lean` (abstract U1-U6) and later `Tools/ShippingGen5DeclConnect.lean` (+ `lean_lib` entries), checks
  `Tests/Gen5/DeclConnectAbsCheck.lean`.

## 0. What is and is not in scope

| item | status |
|---|---|
| (1) full type of `DeclConnect` (and `ConstValueOk`, `SigShape`, `sigShape?`, `SigShape.obs`), dependencies as PREMISES | this freeze, §1 |
| (2) table of what the actual source side supplies (declarations, environment, `ReadsAt`) | this freeze, §2 |
| (3) insertion point in FG's schema, and the check that FG is not shrunk | this freeze, §3 |
| (4) units of pure lemmas that do not depend on DG-SEM / DG-DATAOF / DG-ACC | this freeze, §4 (Lean after approval) |
| final connection that USES the dependencies' results | an INTERMEDIATE result `declConnect_of_rows` (§4 U6, abstract), stated with the dependencies' types as explicit premises. NOT completion |
| `ConstValue` formulation (DC-FORM) | study §4a (done in this revision as a study; Lean text only after Q4); possibly ends as a user decision (§6) |

Completion of this issue's goal is `FG-REF ∧ ConstValueOk ∧ DeclConnect env₀ (genP env₀) Tgt` (DGEN:§2.6). Neither
defining `ConstValue`, nor `DeclConnectImp`, nor `ConstValueOk` alone, nor `DeclConnect` for a `Tgt` narrower than all
successful targets completes it. This freeze completes none of those.

## 1. Full types (rev2)

Namespace `Tools.ShippingGen5DeclConnect`. Imports (present at 9d26005c): `Tools.ShippingGen2Defs` (`Pkgs`, `Pkg`, `T1Hyp`),
`Tools.ShippingGen5Env` (`ReadsAt`). Opens `Lean`, `Sparkle.Compiler.Elab (structEnv MixedGateBinder mixedGateBinderKind?)`,
`Tools.ShippingMachineAuto (MachineData)`, `Sparkle.Core.Signal`, `Sparkle.Core.Domain`.

### 1.0 What the actual source types are (the survey R1/R3 need)

Facts read at 9d26005c (`Sparkle/Compiler/Elab.lean`):
- Binder kinds: `mixedGateBinderKind?` (:2337): `DomainConfig` ↦ `.domain`; `Signal _ Bool` ↦ `.bool`; `Signal _ (BitVec n)` ↦ `.bits n`
  (`n` a canonical positive literal). **It ignores the domain argument of `Signal`.** `telescopeKinds` (:4367) maps a type's
  Pi-telescope to kinds, `none` if one binder is not a hardware binder. `machineShape?` (:5072) requires `parameters = []`,
  `symbolicMode = false`, and `ci` a `defnInfo`.
- Result kinds: `machOuts?` (:3859) after the telescope: `Signal _ Bool` ↦ one port `out : bool`; `Signal _ (BitVec n)` ↦ `out : bits n`;
  `Prod a b` of two Signal types ↦ `out_0`, `out_1`; a user structure `S ..` (via `senv.fields`) ↦ one port per field;
  `Signal _ (A × B …)` (`machTupleKinds?` :3835) ↦ ONE port `out` of the packed width (`machWidth` sum). `machResultKind?` (:4326).
- Source observation: `Pkg.src p : ∀ i, (Nat → Signal (dom i) Bool) → ((j n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)`
  (`Tools/ShippingGen2Pkg.lean`). The bool/bit stream for the binder at telescope POSITION `q` (domain binders included in the
  count) is `bools q` / `bits q n` (`decB`/`decV`, `Tools/ShippingMachineChild.lean:53-58`: `vals.getD (portIdx bs q)`, with
  `portIdx` counting the non-domain binders before `q`; `boolsOf`/`bitsOf` `Tools/ShippingMachineSeqChild.lean:24,29`; the quotation
  `inputExpr (bpos j)`). So the INPUT CORRESPONDENCE is positional: the actual function's `q`-th argument is `bools q` (`.bool`),
  `bits q n` (`.bits n`), `dom i` (`.domain`).
- Output observation: the list has one entry per port in `layout.outs` order (`MachineData.outs`); a Bool entry is `0/1`.
- State: the actual machine's state is internal (`runCircuitH`/`stateLoop`/`Signal.loop`), not an argument or a result. So
  "state preservation" is the content of `DeclConnect`'s equation, carried by the value `v` (which contains the loop) and
  proved with rows 3/4 (§2), NOT by the adapter. The adapter preserves arguments and results only; it never touches state.

### 1.1 `SigShape`, a concrete adapter (R1)

```lean
/-- Result shape of the actual type (the fragment of `machOuts?` this freeze supports). -/
inductive ResShape
  | one  (k : MixedGateBinder)               -- Signal D Bool / Signal D (BitVec n); k = .bool | .bits n
  | pair (ka kb : MixedGateBinder)           -- Signal D A × Signal D B   (Prod of two Signals)
  -- `struct` (user structure of Signals) and `packedTuple` are NOT in this fragment: `sigShape?` = none. §1.3.

structure SigShape where
  args : List MixedGateBinder               -- the binders AFTER the leading domain binder; no `.domain` among them
  res  : ResShape

def ResShape.Ty (D : DomainConfig) : ResShape → Type
  | .one .bool => Signal D Bool | .one (.bits n) => Signal D (BitVec n) | .one .domain => Empty
  | .pair a b => (ResShape.Ty D (.one a)) × (ResShape.Ty D (.one b))
def SigShape.ArgsTy (D : DomainConfig) : List MixedGateBinder → Type → Type
  | [], R => R
  | .bool :: ks, R => Signal D Bool → SigShape.ArgsTy D ks R
  | .bits n :: ks, R => Signal D (BitVec n) → SigShape.ArgsTy D ks R
  | .domain :: ks, R => Empty → SigShape.ArgsTy D ks R      -- unreachable: `sigShape?` never produces it
def SigShape.Ty (sh : SigShape) : Type := (D : DomainConfig) → SigShape.ArgsTy D sh.args (sh.res.Ty D)

/-- Apply the actual function to the reference streams: binder `q` (telescope position, domain = position 0) gets
`bools q` / `bits q n`, exactly `decB`/`decV`'s indexing. -/
def SigShape.applyArgs {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j n : Nat) → Signal D (BitVec n)) :
    (ks : List MixedGateBinder) → (q : Nat) → {R : Type} → SigShape.ArgsTy D ks R → Option R   -- `none` only for `.domain` (unreachable)
def ResShape.obs {D : DomainConfig} : (r : ResShape) → r.Ty D → List (Nat → Nat)
  -- one .bool: [fun t => (s.atTime t).toNat? : Bool→Nat as 0/1] ; one (.bits n): [fun t => (s.atTime t).toNat]; pair: obs a ++ obs b
def SigShape.obs (sh : SigShape) (v : sh.Ty) : (i : ι) → (Nat → Signal (dom i) Bool) →
    ((j n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)
  -- fun i bools bits => (applyArgs bools bits sh.args 1 (v (dom i))).elim [] (sh.res.obs)   (the elim is the unreachable case)

/-- Total, computed from the actual type by the same walk as `telescopeKinds`/`machOuts?`: the FIRST binder must be
`DomainConfig`, every later binder `Signal (bvar d) Bool` / `Signal (bvar d) (BitVec n)` where `bvar d` is exactly that first binder
(de Bruijn index = depth - 1; a second domain binder, a different domain term, or a closed domain constant gives `none`), and the
result a `Signal d Bool` / `Signal d (BitVec n)` / `Prod` of two such. Everything else is `none`. -/
def sigShape? (ty : Lean.Expr) : Option SigShape
/-- What the shape must match in the package (ties the adapter to THIS package, R1): the declared non-domain port kinds and the
output port list. -/
def ShapeMatches (sh : SigShape) (d : MachineData) (kD : Nat) : Prop :=
  d.bsIn.take kD |>.map (·.2) = MixedGateBinder.domain :: sh.args ∧
  d.shape.layout.outs.map (fun o => (o.ty, o.width)) = sh.res.outPorts      -- outPorts: (bit,1) / (bitVector n, n), in order
```

Remarks (all part of the freeze):
- **What is preserved, by construction.** Arguments: `applyArgs` feeds `bools q`/`bits q n` at the binder's position `q`, the
  indexing the source stream uses; the kinds list is checked to equal `p.d.bsIn.take p.kD` by `ShapeMatches`. Domain: the
  leading binder receives `dom i`, and `sigShape?` rejects any type whose Signals use another domain term. Results:
  `ResShape.obs` produces the list in port order and `ShapeMatches` ties its length/types to `layout.outs`. State: §1.0, not
  the adapter's job. There is no free `toSig` and nothing a user can choose: an adapter is a function of `ci.type` alone.
- **Unknown shapes.** `HWType.bitVectorDim`/`array`, user structures, packed tuple results, closed-domain declarations, `Type`-quantifying
  declarations, and a declaration with `levelParams ≠ []` all give `sigShape? = none`. They are NOT mapped to `PUnit` and have no
  fake meaning. **Coverage is kept**: the existence conjunct of `DeclConnect` requires `sigShape? ci.type = some sh`, so a
  successful target outside the fragment makes `DeclConnect` false on it. The coverage obligation (DC-COVER, §2) is therefore
  "every name a successful FG run reaches has `sigShape? = some`", unsupplied (this survey found no route for it); if a corpus top
  falls outside, the fragment is extended (a `ResShape` constructor with its meaning), never the statement weakened.
- **§1.3 struct results.** To give `struct` a real meaning the observation of field `f_k` is `CV` of the projection constant
  `S.f_k` applied to `v`. That needs `CV` rows for projections and is added with `ResShape.struct`, after DCF. Until then `none`.
- This replaces rev1's `SigAdapter`/`adapterOf`/`OutSigs`/`obsOuts`/`SigFunOf`/`sigObs`/Q2/Q3/Q5. `SigAdapter.args` as data (Q2) is
  now `sh.args` itself. Universe: `SigShape.Ty : Type`, so `CV : Environment → Name → (α : Type) → α → Prop`.

### 1.2 `ConstValueOk` and `DeclConnect` (rev2, rev3 of the statement)

```lean
abbrev ConstValueRel := Environment → Name → (α : Type) → α → Prop
def ConstValueFunctional (CV : ConstValueRel) : Prop :=
  ∀ env c α β (v : α) (w : β), CV env c α v → CV env c β w → α = β ∧ HEq v w
def ConstValueOk (CV : ConstValueRel) (V3 : ConstValueRel → Prop) : Prop := ConstValueFunctional CV ∧ V3 CV

def DeclConnect (CV : ConstValueRel) (env₀ : Environment) (P : Pkgs ι dom) (Tgt : Name → Prop) : Prop :=
  ∀ X, Tgt X → ∀ p, P X = some p →
    ∃ (ci : ConstantInfo) (sh : SigShape) (v : sh.Ty),
      env₀.find? X = some ci ∧ sigShape? ci.type = some sh ∧ ShapeMatches sh p.d p.kD ∧
      CV env₀ X sh.Ty v ∧
      ∀ i bools bits, sh.obs v i bools bits = p.src i bools bits

def DeclConnectImp (CV : ConstValueRel) (env₀ : Environment) (P : Pkgs ι dom) (Tgt : Name → Prop) : Prop :=   -- INTERMEDIATE
  ∀ X, Tgt X → ∀ p, P X = some p → ∀ ci, env₀.find? X = some ci → ∀ sh, sigShape? ci.type = some sh → ShapeMatches sh p.d p.kD →
    ∀ (v : sh.Ty), CV env₀ X sh.Ty v → ∀ i bools bits, sh.obs v i bools bits = p.src i bools bits
```

`CV env₀ X sh.Ty v` must carry that `ci.type` denotes `sh.Ty` (DCF rule T, §4a): otherwise a `v : sh.Ty` unrelated to `X`'s
declared type could be offered. So `ConstValueE`'s clause includes `TypeDenotes env ci.type α`.

`Tgt` is a binder; for the completion statement it is `Tgt_run` (§3), never narrower.

### 1.3 The dependencies, as PREMISES, fully typed (R2)

```lean
/-- DG-SEM / DG-ACC (DGEN:§2.5 C1-C6) about the assignment and one name. NOT proved here. `entry₀`, `genData₀`, `GenData`, `CallEdge`,
`ordCallees` are DGEN:§2.5's names (DG-SEM's Lean); their argument lists are DG-SEM's, mirrored here as premises. -/
def GenPInv (env₀ : Environment) (P : Pkgs ι dom) (X : Name) (p : Pkg ι dom) : Prop :=
  P X = some p ∧
  ∃ (E : ConstantInfo) (g : GenData E (structEnv env₀)),
    entry₀ env₀ X = some E ∧ genData₀ env₀ E = some g ∧ p.d = g.d ∧ Acc (flip (CallEdge env₀)) X ∧
    (∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∃ pc, P (p.d.shape.insts[k]'hk).1 = some pc)

/-- DG-DATAOF `dataOf_sound`'s conclusion for `p`, with every argument bound: the package's data is OK, its body is the quotation
of its packed term, and its slot initial values are the layout's. -/
def DataSoundAt (p : Pkg ι dom) : Prop :=
  p.d.ok = true ∧
  p.d.shape.body = Tools.ShippingUnifiedSource.quote p.d.dom
    (fun j => inputExpr p.d.shape.binders.length (p.d.bpos j))
    (fun j => inputExpr p.d.shape.binders.length (p.d.vpos j)) p.d.packed ∧
  (∀ s ∈ p.d.shape.layout.slots, ∃ a, s.init = a)     -- PLACEHOLDER row for the init agreement: DG-DATAOF's `initOk`; its exact
                                                      -- statement is that issue's. Until it is fixed, U6 does not take this clause.
```
`Pkg.ok` and `Pkg.body_eq` (Tools/ShippingGen2Pkg.lean) already give the first two conjuncts for every `Pkg` by cases; the third is
DG-DATAOF's. rev1's `quote p.d.dom … p.d.packed` ellipsis is replaced by the full text of `Pkg.body_eq`. The `initOk` clause is marked
PLACEHOLDER: this freeze does not invent DG-DATAOF's statement; `declConnect_of_rows` (U6) does NOT use `DataSoundAt` or `GenPInv`
as hypotheses (only `hstep`, §4), so nothing depends on the placeholder.

## 2. Supplier table: what the actual-source side gives

`[S]` = present at 9d26005c. "no route found" means this survey found no existing export; it is not a non-derivability
claim. Rows 0-5 are DGEN:§2.6's route rows; conjunct names refer to `DeclConnect`.

| need | supplier found at 9d26005c | gives | does NOT give / open |
|---|---|---|---|
| `env₀.find? X = some ci` (conjunct 1) | `ci_of_readsAt` (E4), `Tools/ShippingGen5Env.lean:52` [S], at a `getConstInfo` run from a `ReadsAt env₀` world | the constant a run read is `env₀`'s | `ReadsAt` at the run's worlds is C0 (DG_ENV_FREEZE §0 S1): NOT supplied. Alternatively `GenPInv.entry₀` gives `env₀.find? X = some ci` with no run at all (it is `entry₀`'s own `find?`) — **the proposed supplier**, and it is independent of C0 |
| the same `ci` is the one the reader/translator used | `ci_of_readsAt` + `envR_of_readsAt` (E5) [S] | read `ci`, `structEnv envR` = `env₀`'s | only under `ReadsAt` (C0, unsupplied) at the read worlds. Needed ONLY for the evidence side (`MachineDefines`), not for `DeclConnect`'s own statement, which fixes `env₀` |
| `structEnv env₀` used by `sigShape?`/`ShapeMatches` is the reader's | `ReadsAt` 4th conjunct, `envR_of_readsAt` [S] | `structEnv envR = structEnv env₀` | as above; for `DeclConnect` alone the statement reads `env₀` by definition |
| row 0 existence: `∃ α v, CV env₀ X α v` | none. `Tools/Prototype/DGenStored.lean:14-18` [S] says `ConstValue` is NOT FORMULATED ("impossibility is NOT claimed") | — | UNSUPPLIED; DCF (U7) decides whether `CV` is definable |
| row 0 adapter: `sigShape? ci.type = some sh` ∧ `ShapeMatches` | `telescopeKinds` (Elab.lean:4367 [S]) reads the binder kinds of an actual type; `structEnv` (:4394 [S]) is the structure map | the raw ingredient (binder kinds, structure fields) | `sigShape?` is defined in §1.1 (not yet in Lean). Its success on every successful target is the coverage obligation DC-COVER, UNSUPPLIED |
| row 1 entry: `ci.value ↦ entryConst …` | `entryConst` (Elab.lean:5272 [S]) is definition unfolding. `EntryDefines` (ShippingInlineSoundness.lean:48-57) and `entry_kept` (ShippingEntrySoundness.lean:1132) relate Exprs and RUNS | — | "unfolding preserves `CV`" UNSUPPLIED (depends on `CV`) |
| row 2 shape/body | `dataOf_sound` (DG-DATAOF, doing), via `readTerm_sound` (Tools/ShippingReaderTerm.lean:1129 [S]) / `readN_expr_sound` (ShippingReaderApp.lean:356 [S]); `Pkg.body_eq` (Tools/ShippingGen2Pkg.lean) turns a package's facts into `body_eq` | `d.shape.body = quote … d.packed` | the DG-DATAOF result is a dependency, not yet done |
| row 3 quote/eval | none (needs `CV`'s Expr form) | — | one row per node kind of the reader's finite table; UNSUPPLIED |
| row 4 state loop | per declaration: `X.machine_source` (ShippingMachineCommand.lean:2599-2610 [S]); `stateLoop`/`obsR` (ShippingMachineSource.lean:74 [S]); the package side is `GenFacts.source` (a package field) | the equation `src = obsR of stateLoop`, per declaration / for packages that carry `GenFacts` | uniform "the SOURCE's `Signal.loop` value equals `obsR` of `stateLoop`" UNSUPPLIED |
| row 5 calls | DG-ACC (`Acc`), E1 at the `ext` position (T2COVER §1); memory entries: DC-SUPPLY separate row | induction skeleton | the IH at direct ordinary callees is a pure `Acc` induction (U5 here); the per-call semantic step is row 3 + row 4 at the callee |
| `Tgt X ⇒ P X = some p` | DG-PKGASSIGN / `genP` (DG-SEM, DG-ACC) | the package exists for the targets | dependency, not done |

Table conclusion: the supplied pieces are (a) the `find?` conjunct (from `entry₀`), (b) the `ReadsAt` lemmas E1-E6 as
evidence-side tools, (c) the `Acc` induction skeleton. This survey found no supplier for `CV` itself, for `sigShape?` coverage,
or for rows 1, 3, 4 uniformly.

## 3. Where `DeclConnect` sits in FG, and FG is not shrunk (rev2)

FG (GENERAL_SPEC.md:88-93), schema NOT edited:
`FG : ∀ L declName parameters mctx cctx w b D w', Start L mctx cctx w → (RunsTo (synthesizeCombinational declName) … ∨ RunsTo (synthesizeCombinationalWithParameters declName parameters) …) → ReflectsAll L declName parameters → ∃ p n, Pk declName = some p ∧ TopShips p n declName b raw D`.

**`FG_COMPLETE`, fully bound** (a statement in the new file; every variable of FG appears; nothing is a literal):

```lean
inductive TgtRun (P : Pkgs ι dom) (declName : Name) : Name → Prop     -- least predicate: declName, and ordinary callees of reached
  | top : TgtRun P declName declName
  | call {c : Name} {q : Pkg ι dom} (hc : TgtRun P declName c) (hq : P c = some q) (k : Nat) (hk : k < q.d.shape.insts.length)
      (ord : (q.d.shape.instOrigins.getD k .ord).child? = none) : TgtRun P declName (q.d.shape.insts[k]'hk).1
def FG_COMPLETE {mref cref} (CV : ConstValueRel) (V3 : ConstValueRel → Prop) (L : Laws mref cref) : Prop :=
  ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w : Void IO.RealWorld) (b : Bool) (D : …FG's `D` type…) (w' : Void IO.RealWorld),
    Start L mctx cctx w →
    (RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w' ∨
     RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w') →
    ReflectsAll L declName parameters →
    let env₀ := envAt cref w                                   -- the START world's environment (E1 `readsAt_self`)
    (∃ p n, genP env₀ declName = some p ∧ TopShips p n declName b raw D) ∧     -- FG with Pk := genP env₀ (FG-REF); `raw` as FG
    ConstValueOk CV V3 ∧
    DeclConnect CV env₀ (genP env₀) (TgtRun (genP env₀) declName)
```
(`D`'s type and `raw` are copied from FG's own text at implementation; this freeze only fixes that they are FG's binders, not
new ones. `parameters` appears twice: in the route disjunct and in `ReflectsAll`, as in FG; with `parameters ≠ []` the machine
`machineShape?` is `none` so the second route has no machine target by itself; `Tgt_run` is the set of names the run reaches, and
for a parametric run whose package assignment has no machine entry, `genP env₀ X = none` makes `DeclConnect` vacuous at X only
because no package exists — that is `Pk declName = some p` (FG's conjunct), not a weakening of `DeclConnect`.)
`env₀ := envAt cref w` with `ReadsAt env₀ cref w` from E1; `start` is `Start L mctx cctx w`; `run` is the two-way disjunct. `Tgt_run` is the
`TgtRun` predicate above — equal in shape to `T1Hyp.closed`'s `Reach` (Tools/ShippingGen2Defs.lean:218), which is a parameter of
`T1Hyp` and the supplier of `TgtRun ⊆ Reach` is G-REACH (unsupplied).

Composition for the top: from the first conjunct and `TgtRun declName` (`TgtRun.top`), `DeclConnect` gives `p.src = sh.obs v` for the
elaborated value `v` of `declName`.

Not-shrunk checklist (each is a property the Lean unit must preserve; the check file asserts them by `example`):

| FG property | preserved by | how it is checked |
|---|---|---|
| FG's text, quantifiers and conclusion unchanged | no edit of `Tools/ShippingGen2Defs.lean` / `T1Hyp*`; this issue adds only a new file | `git diff` over the protected paths is empty |
| all successful runs (both entries) | `Tgt_run` is defined from the run's names, not from a corpus | no `Tgt` literal list; U2 (`declConnect_mono`) is the only way `Tgt` shrinks and it is a lemma, not an instance |
| no per-declaration premise | `DeclConnect`'s binders are `CV env₀ P Tgt` only; no `∀ X` hypothesis `hX : …X…` in `declConnect_of_rows` beyond the uniform rows | binder-table listing in the check file |
| `DeclConnect` not vacuous | rev2 existence inside; U3 shows the rev1 form is true for the empty relation while rev2 is false there | U3 |
| `GenWF` not strengthened, no new law | nothing here mentions them | grep in the check file's header audit |
| `ConstValueOk` is not assumed | it is a conjunct of the goal, parameterised by `CV` | statement text |

## 4a. DCF study (R3): concrete `ConstValue` rules against the actual source types

Done BEFORE the pure units. "ANY `CV` that is functional and `V3`" is not the actual-source meaning (a relation true only at
the lone name `declName` would satisfy the statement). So `V3` is fixed here as "`CV` IS `ConstValueE`", the least relation closed
under the rules below, and the rules are matched to what the machine route accepts.

What an accepted declaration's value looks like (`machineShape?` Elab.lean:5072, `machRunApp?` :3675): after peeling the leading
`fun (D : DomainConfig) (b : Signal D Bool) (v : Signal D (BitVec n)) …`, a body built from: `Sparkle.Core.runCircuitH D αs _ _ _ _ inits (fun regs => …)`,
the register handles `Prod.fst/snd`, `Signal.register`/`Signal.loop`-based reads, `Bool`/`BitVec` operations and literals
(`OfNat`, `BitVec.ofNat`), `ite`/`Bool` matchers, tuple/structure constructors (`Prod.mk`, user `S.mk`), `let`, and calls to other
`@[hardware_module]` declarations (user constants).  Types in play: `Signal`, `Bool`, `BitVec n`, `Nat`, `Prod`, `HList`, `DomainConfig`.

Rules (a proposal for U7; names are proposals):

| rule | content | status |
|---|---|---|
| lit | `Expr.lit (natVal n)` ↦ `n : Nat` | by structure |
| bvar | variable ↦ valuation entry | by structure |
| lam/app | `fun x => b` ↦ Lean function over the denotation of `b` in the extended valuation; application ↦ application, with the type check `TypeDenotes` | by structure |
| const-unfold | `c` a `defnInfo` of `env` with value `e` ↦ the denotation of `e`, well-founded on the environment | by structure (needs a recursion measure: an `Acc` on definitional-dependence, or restriction to the acyclic user declarations; the kernel guarantees acyclicity, but proving it of an arbitrary `Environment` is NOT available — so the rule is stated with the derivation as the inductive witness, no termination claim) |
| const-prim | `c` in a finite TABLE ↦ a named Lean constant (`Signal.register`, `Signal.loop`, `runCircuitH`, `BitVec.*`, `Bool.*`, `Prod.mk/fst/snd`, `ite`, `Nat.add`, …) | **the item Q4**: each table entry is a pair `Name ↦ Lean term` whose agreement (the `Name` is that constant) is a meta-level fact that Lean's kernel cannot check about `Environment` data |
| typeDenotes | `ci.type` ↦ the `Type` `sh.Ty` (needed by `DeclConnect`, §1.2) | by structure for the fragment, from `sigShape?` |

Study conclusions (statements about this survey):
1. V3 can be made definitional (`CV := ConstValueE`, an inductive family), V2 then follows by induction if the prim table is
   functional in the `Name` (distinct names, one entry each). So `ConstValueOk` is not an extra assumption beyond the table.
2. The rule set is finite and matches the reader's node table: each prim entry corresponds to one node kind the machine reader
   accepts. The mapping of entries to reader nodes is a TABLE-COVERAGE row (every constant that appears in an accepted value is
   either an unfoldable user definition or in the table); this survey did not find a supplier for it.
3. The table is the only place the semantics is stipulated rather than derived. If it is accepted as a stated list, GENERAL_SPEC.md:505-506
   makes it a USER item (new TRUSTED boundary). Not adopted. This study ends at that point: a decision document is written only
   if the user-visible choice becomes necessary (§6); the pure units do not depend on it.
4. Not claimed: that `ConstValueE` is the true kernel semantics; that the table is complete; that `ExprDenotes` is a well-founded recursion.

## 4. Units of pure lemmas (rev2: explicit shape parameters, R2)

Units U1-U5 and U6 are stated over an ABSTRACT interface so that they hold without `sigShape?`/`ShapeMatches` being defined (these
are parameters, R2): `{E N CI Pk : Type}`, `find : E → N → Option CI`, `Shape : Type`, `Ty : Shape → Type`,
`shapeOf : CI → Option Shape`, `Match : Shape → Pk → Prop`, `Obs : Pk → (sh : Shape) → Ty sh → Prop`,
`CV : E → N → (α : Type) → α → Prop`, `P : N → Option Pk`. The concrete instance (`CI := ConstantInfo`, `Shape := SigShape`,
`shapeOf := fun ci => sigShape? ci.type`, `Match sh p := ShapeMatches sh p.d p.kD`, `Obs p sh v := ∀ i bools bits, sh.obs v i bools bits = p.src i bools bits`)
is the later file; the abstract file does not mention `Pkg`, `MachineData` or `sigShape?`.

```lean
def DCAt (env) (X) : Prop := ∀ p, P X = some p → ∃ ci sh (v : Ty sh), find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v
def DCGen (env) (Tgt : N → Prop) : Prop := ∀ X, Tgt X → DCAt env X
def DCImp (env) (Tgt) : Prop := ∀ X, Tgt X → ∀ p, P X = some p → ∀ ci, find env X = some ci → ∀ sh, shapeOf ci = some sh → Match sh p → ∀ v : Ty sh, CV env X (Ty sh) v → Obs p sh v
theorem dcGen_iff               : DCGen env Tgt ↔ ∀ X, Tgt X → DCAt env X                      -- U1 (by Iff.rfl; recorded)
theorem dcGen_mono (h : ∀ X, Tgt' X → Tgt X) : DCGen env Tgt → DCGen env Tgt'               -- U2
theorem dcImp_of_empty : DCImp (CV := fun _ _ _ _ => False) env Tgt                         -- U3a
theorem not_dcGen_of_empty (hT : Tgt X) (hP : P X = some p) : ¬ DCGen (CV := fun _ _ _ _ => False) env Tgt     -- U3b
theorem dcImp_of_dcGen (hV2 : Functional CV) (hfind : ∀ ci ci', find env X = some ci → find env X = some ci' → ci = ci') : DCGen env Tgt → DCImp env Tgt   -- U4a
theorem dcGen_of_imp_exists (hImp : DCImp env Tgt) (hEx : ∀ X, Tgt X → ∀ p, P X = some p → ∃ ci sh (v : Ty sh), find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v) : DCGen env Tgt   -- U4b
theorem dcAt_of_acc {R : N → N → Prop} (hstep : ∀ X, (∀ c, R c X → Ready c) → Ready X) : ∀ X, Acc R X → Ready X      -- U5
theorem dcGen_of_rows (hAcc : ∀ X, Tgt X → Acc R X) (hclosed : ∀ X c, Tgt X → R c X → Tgt c)
    (hstep : ∀ X, Tgt X → (∀ c, R c X → Tgt c → DCAt env c) → DCAt env X) : DCGen env Tgt      -- U6 (INTERMEDIATE)
```
(U4a: `find` is a function, so two `ci` for X coincide — a hypothesis, supplied by `Environment.find?` being a function at the concrete
instance, `rfl`.) `hstep` is the UNSUPPLIED content of rows 0-4; U6 is the Acc assembly only and is reported as "skeleton, rows
unsupplied". The old "U7 = DCF" is now §4a; no Lean for it in this freeze.


## 5. Open questions (do not block the pure units)

- **Q1** coverage of `sigShape?` on the successful targets (DC-COVER); extension of `ResShape` (struct, packedTuple) after DCF.
- **Q4** the prim table (§4a): definition vs trusted statement. User item only if adopted (§6).
- **Q6** `DataSoundAt`'s `initOk` clause: DG-DATAOF's statement (placeholder here; not used by U1-U6).
- **Q7** the exact `D` type and `raw` of FG's conclusion in `FG_COMPLETE` (to be copied from the text at implementation).

## 6. Decision items (not adopted; none is needed to approve this freeze)

If the prim table (Q4) is judged a stated trusted list, GENERAL_SPEC.md:505-506 makes it a USER item (new TRUSTED boundary). That would be a
separate decision document with impact, options and cost, and the issue set to `decision`. Not triggered by this freeze.

## 7. Not claimed

- No claim that `ConstValue`, `sigShape?` coverage, `DeclConnect` or any row is supplied, or supplyable by a specific route.
- No claim that FG, FG-REF or M5 is complete. `dcGen_of_rows` is an intermediate Acc assembly.
- No claim about elaboration of the proposal Lean text (nothing but the abstract units U1-U6 is built; see the Check file).
- DG-SEM, DG-DATAOF and DG-ACC are not done; their results enter only as premises.
- No new law, TRUSTED boundary, FG or guarantee change; no edit of compiler/shared definitions.
- A mutant in the check is a signature/defeq rejection, not a semantic counterexample.

## 8. Order

1. (this revision) abstract U1-U6 in `Tools/ShippingGen5DeclConnectAbs.lean` + `Tests/Gen5/DeclConnectAbsCheck.lean` (TYPE/MUTANT/AXIOMS/closure).
2. Concrete `SigShape`/`sigShape?` file after rev2 approval; DCF Lean only after the Q4 outcome.
3. The final connection waits for DG-SEM / DG-DATAOF / DG-ACC.

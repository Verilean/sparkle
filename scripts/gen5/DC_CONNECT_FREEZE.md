# DC-CONNECT: DeclConnect on the actual source — full-type freeze (rev1)

Issue `sparkle-gen5-dc-connect` (parent `sparkle-gen5-decl-bridge`; units DC-FORM / DC-SUPPLY / DG-DECLCONNECT).
Base: `par/gen3-combined` 9d26005c (S1 integration). Design sources (read with `git show par/gen5-t2:...`, c398021c):
`DGEN_FREEZE.md` rev2 §2.6 (cited `DGEN:§2.6`), `T2COVER_FREEZE.md` rev2 §2, `DG_ENV_FREEZE.md` rev2.2, and
`scripts/gen2/GENERAL_SPEC.md` (FG §1.1, M5 §5 lines 489-507, §6 table line 535).

**Status: design only. No Lean written, nothing elaborated or built.** Every Lean text below is a PROPOSAL; names,
binders and elaboration are unverified. The Lean implementation does not start before the reviewer approves this freeze.

Wording rules used throughout:
- "not supplied" / "this survey found no source or route" is a statement about THIS survey. It is not a claim that
  something is impossible or underivable.
- A "mutant" in §4 is a rejection by signature or defeq of a changed statement. It is not a semantic counterexample.
- Nothing here is a new TRUSTED boundary, law, FG or guarantee change, compiler change, or edit of shared definitions
  (`Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`). Everything that would need one is in §6 and is NOT
  adopted.
- New Lean goes in NEW files only: `Tools/ShippingGen5DeclConnect.lean` (+ `lean_lib` entry) and a check
  `Tests/Gen5/DeclConnectCheck.lean`.

## 0. What is and is not in scope

| item | status |
|---|---|
| (1) full type of `DeclConnect` (and `ConstValueOk`, `SigAdapter`, `adapterOf`, `sigObs`), dependencies as PREMISES | this freeze, §1 |
| (2) table of what the actual source side supplies (declarations, environment, `ReadsAt`) | this freeze, §2 |
| (3) insertion point in FG's schema, and the check that FG is not shrunk | this freeze, §3 |
| (4) units of pure lemmas that do not depend on DG-SEM / DG-DATAOF / DG-ACC | this freeze, §4 (Lean after approval) |
| final connection that USES the dependencies' results | an INTERMEDIATE result `declConnect_of_rows` (§4 U6), stated with the dependencies' types as explicit premises. NOT completion |
| `ConstValue` formulation (DC-FORM) | unit DCF (§4 U7), a study with a Lean text as output; possibly ends as a user decision (§6) |

Completion of this issue's goal is `FG-REF ∧ ConstValueOk ∧ DeclConnect env₀ (genP env₀) Tgt` (DGEN:§2.6). Neither
defining `ConstValue`, nor `DeclConnectImp`, nor `ConstValueOk` alone, nor `DeclConnect` for a `Tgt` narrower than all
successful targets completes it. This freeze completes none of those.

## 1. Full types

Namespace `Tools.ShippingGen5DeclConnect`. Imports (all present at 9d26005c): `Tools.ShippingGen2Defs` (`Pkgs`,
`Pkg`), `Tools.ShippingGen5Env` (`ReadsAt`). Opens `Lean`, `Sparkle.Compiler.Elab (structEnv telescopeKinds entryConst
machineShape?)`, `Tools.ShippingMachineAuto (MachineData)`.

```lean
universe u
variable {ι : Type} {dom : ι → DomainConfig}

/-- The output sorts of a machine, as signals of one domain: one component per `OutField`, by its `HWType`
(`bit` ↦ `Signal D Bool`, `bitVector n` ↦ `Signal D (BitVec n)`; other `HWType` constructors ↦ `PUnit`, i.e. they
carry no observation — see §5 Q3). Total, by recursion on the list. -/
def OutSigs (D : DomainConfig) : List OutField → Type
/-- The observation of those components as the `List (Nat → Nat)` that `Pkg.src` returns (`fun t => (s.atTime t).toNat`
per component, `Signal.atTime`, Sparkle/Core/Signal.lean:105). Total. -/
def obsOuts (D : DomainConfig) : (outs : List OutField) → OutSigs D outs → List (Nat → Nat)

/-- Signal-function type determined by `d.shape.layout.outs`: bool inputs, bit inputs, result components
(the same input shape as `Pkg.src`, Tools/ShippingGen2Pkg.lean). -/
def SigFunOf (d : MachineData) (dom : ι → DomainConfig) : Type :=
  (i : ι) → (Nat → Signal (dom i) Bool) → ((j n : Nat) → Signal (dom i) (BitVec n)) → OutSigs (dom i) d.shape.layout.outs
def sigObs (d : MachineData) {dom : ι → DomainConfig} (f : SigFunOf d dom) :
    (i : ι) → (Nat → Signal (dom i) Bool) → ((j n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat) :=
  fun i bools bits => obsOuts (dom i) d.shape.layout.outs (f i bools bits)

/-- The adapter from X's actual type to the reference signal-function type (DATA, DGEN:§2.6). -/
structure SigAdapter (d : MachineData) (dom : ι → DomainConfig) (α : Sort u) where
  toSig : α → SigFunOf d dom
/-- Total, computed from the actual type and the structure environment. `none` = no adapter. -/
def adapterOf (ty : Lean.Expr) (senv : StructEnv) (d : MachineData) (dom : ι → DomainConfig) :
    Option (Σ α : Sort u, SigAdapter d dom α)
```

Remarks on §1 (all part of the freeze):
- `sigObs` takes the `MachineData` so that `SigFunOf`'s result type is `d`'s. The rev2 text writes
  `sigObs p.d (A.toSig v i bools bits)`; here `A.toSig v : SigFunOf d dom` is applied inside `sigObs`. The two are the
  same observation. The binder order is fixed in this freeze as above.
- `adapterOf` additionally takes `dom` (rev2's text left it implicit). The components `dom`/`args`/`result`/`state` of
  DGEN:§2.6 are DESIGN requirements on `adapterOf`'s definition. `SigAdapter` exposes only `toSig`.
  **Q2 (open)**: ARGW's VT row (SRC_ARGW_SUPPLY_FREEZE.md:776, :836) wants the `args` map as DATA or an
  `adapterOf_portWidths` lemma. The first proposal here is that `SigAdapter` gets a second field
  `args : List (Name × MixedGateBinder)` with `args = d.bsIn.take kD` (a lemma, not a field-by-assumption) — to be
  decided with the SRC-ARGW owner. It changes no statement of `DeclConnect`. It is not adopted by this freeze.
- `universe u`: `DeclConnect.{u}` is instantiated at the universe of the reference signal functions (`Type`, so
  `u := 1`). A declaration whose actual type quantifies over `Type` arguments gets no adapter in this fragment (no
  `adapterOf` result), so its existence conjunct fails. That is the intended coverage test, not a loophole (§5 Q1).

```lean
/-- ABSTRACT formulation parameters. The pure lemmas (§4 U1-U5) hold for ANY `CV`; only U7 (DCF) constructs one. -/
abbrev ConstValueRel := Environment → Name → (α : Sort u) → α → Prop

/-- `ConstValueOk` (DGEN:§2.6): functional (V2) and defined by rules (V3).  V3 is the Lean statement
`ConstValueDefinedByRules CV` of DCF (U7); it is a PARAMETER here, not assumed anywhere. -/
def ConstValueFunctional (CV : ConstValueRel.{u}) : Prop :=
  ∀ env c α β (v : α) (w : β), CV env c α v → CV env c β w → α = β ∧ HEq v w
def ConstValueOk (CV : ConstValueRel.{u}) (V3 : ConstValueRel.{u} → Prop) : Prop :=
  ConstValueFunctional CV ∧ V3 CV

/-- rev2: existence of the actual value, its adapter, and the equation, in ONE obligation, uniform over `Tgt`. -/
def DeclConnect (CV : ConstValueRel.{u}) (env₀ : Environment) (P : Pkgs ι dom) (Tgt : Name → Prop) : Prop :=
  ∀ X, Tgt X → ∀ p, P X = some p →
    ∃ (ci : ConstantInfo) (α : Sort u) (v : α) (A : SigAdapter p.d dom α),
      env₀.find? X = some ci ∧
      CV env₀ X α v ∧
      adapterOf ci.type (structEnv env₀) p.d dom = some ⟨α, A⟩ ∧
      ∀ i bools bits, sigObs p.d (A.toSig v) i bools bits = p.src i bools bits

/-- rev1's implication form, INTERMEDIATE only (true if `CV` is empty). `ci` is the one `env₀` holds. -/
def DeclConnectImp (CV : ConstValueRel.{u}) (env₀ : Environment) (P : Pkgs ι dom) (Tgt : Name → Prop) : Prop :=
  ∀ X, Tgt X → ∀ p, P X = some p → ∀ ci, env₀.find? X = some ci →
    ∀ (α : Sort u) (v : α) (A : SigAdapter p.d dom α), CV env₀ X α v →
      adapterOf ci.type (structEnv env₀) p.d dom = some ⟨α, A⟩ →
      ∀ i bools bits, sigObs p.d (A.toSig v) i bools bits = p.src i bools bits
```

`Tgt` is a binder of `DeclConnect`. For the completion statement it is instantiated by the names of a successful FG run
(§3), never by a narrower predicate.

### 1.1 The dependencies, as PREMISES (the boundary)

These are the types of what DG-SEM / DG-DATAOF / DG-ACC are to supply (from DGEN:§2.1, §2.5). This issue uses them
only as hypotheses of the intermediate result `declConnect_of_rows` (§4 U6). It does not state them as supplied, and
it adds no field to them.

```lean
/-- DG-SEM / DG-ACC (C1-C6 of DGEN:§2.5), as a Prop about the assignment `P` and one name. NOT proved here.
`entry₀`, `genData₀`, `CallEdge`, `genS`, `genSem` are DGEN:§2.5's definitions (their Lean is DG-SEM's). -/
def GenPInv (env₀ : Environment) (P : Pkgs ι dom) (X : Name) (p : Pkg ι dom) : Prop :=
  P X = some p ∧
  ∃ (E : ConstantInfo) (g : GenData E (structEnv env₀)),
    entry₀ env₀ X = some E ∧ genData₀ env₀ E = some g ∧ p.d = g.d ∧ Acc (flip (CallEdge env₀)) X ∧
    (∀ k ∈ ordCallees g.d, ∃ pc, P (g.d.shape.insts[k]).1 = some pc)
/-- DG-DATAOF: `dataOf_sound`'s conclusion for `p.d` (ok, body_eq, init). -/
def DataSoundAt (p : Pkg ι dom) : Prop :=
  p.d.ok = true ∧ p.d.shape.body = quote p.d.dom … p.d.packed
```

Boundary summary: `GenPInv` stands for `genS_some_inv` + `genP_generated` (DG-SEM, DG-ACC); `DataSoundAt` for
`dataOf_sound` (DG-DATAOF). Their exact Lean is those issues'; if their final types differ from the shapes above, only
the premise types of U6 change, never `DeclConnect`.

## 2. Supplier table: what the actual-source side gives

`[S]` = present at 9d26005c. "no route found" means this survey found no existing export; it is not a non-derivability
claim. Rows 0-5 are DGEN:§2.6's route rows; conjunct names refer to `DeclConnect`.

| need | supplier found at 9d26005c | gives | does NOT give / open |
|---|---|---|---|
| `env₀.find? X = some ci` (conjunct 1) | `ci_of_readsAt` (E4), `Tools/ShippingGen5Env.lean:52` [S], at a `getConstInfo` run from a `ReadsAt env₀` world | the constant a run read is `env₀`'s | `ReadsAt` at the run's worlds is C0 (DG_ENV_FREEZE §0 S1): NOT supplied. Alternatively `GenPInv.entry₀` gives `env₀.find? X = some ci` with no run at all (it is `entry₀`'s own `find?`) — **the proposed supplier**, and it is independent of C0 |
| the same `ci` is the one the reader/translator used | `ci_of_readsAt` + `envR_of_readsAt` (E5) [S] | read `ci`, `structEnv envR` = `env₀`'s | only under `ReadsAt` (C0, unsupplied) at the read worlds. Needed ONLY for the evidence side (`MachineDefines`), not for `DeclConnect`'s own statement, which fixes `env₀` |
| `structEnv env₀` used by `adapterOf` is the reader's | `ReadsAt` 4th conjunct, `envR_of_readsAt` [S] | `structEnv envR = structEnv env₀` | as above; for `DeclConnect` alone `adapterOf` reads `env₀` by definition |
| row 0 existence: `∃ α v, CV env₀ X α v` | none. `Tools/Prototype/DGenStored.lean:14-18` [S] says `ConstValue` is NOT FORMULATED ("impossibility is NOT claimed") | — | UNSUPPLIED; DCF (U7) decides whether `CV` is definable |
| row 0 adapter: `adapterOf ci.type … = some _` | `telescopeKinds` (Elab.lean:4367 [S]) reads the binder kinds of an actual type; `structEnv` (:4394 [S]) is the structure map | the raw ingredient (binder kinds, structure fields) | `adapterOf` is not defined at 9d26005c (no `adapterOf`/`SigAdapter` in any Lean file; grep). Its success on every successful target is a coverage obligation (like DG-COVER), UNSUPPLIED |
| row 1 entry: `ci.value ↦ entryConst …` | `entryConst` (Elab.lean:5272 [S]) is definition unfolding. `EntryDefines` (ShippingInlineSoundness.lean:48-57) and `entry_kept` (ShippingEntrySoundness.lean:1132) relate Exprs and RUNS | — | "unfolding preserves `CV`" UNSUPPLIED (depends on `CV`) |
| row 2 shape/body | `dataOf_sound` (DG-DATAOF, doing), via `readTerm_sound` (Tools/ShippingReaderTerm.lean:1129 [S]) / `readN_expr_sound` (ShippingReaderApp.lean:356 [S]); `Pkg.body_eq` (Tools/ShippingGen2Pkg.lean) turns a package's facts into `body_eq` | `d.shape.body = quote … d.packed` | the DG-DATAOF result is a dependency, not yet done |
| row 3 quote/eval | none (needs `CV`'s Expr form) | — | one row per node kind of the reader's finite table; UNSUPPLIED |
| row 4 state loop | per declaration: `X.machine_source` (ShippingMachineCommand.lean:2599-2610 [S]); `stateLoop`/`obsR` (ShippingMachineSource.lean:74 [S]); the package side is `GenFacts.source` (a package field) | the equation `src = obsR of stateLoop`, per declaration / for packages that carry `GenFacts` | uniform "the SOURCE's `Signal.loop` value equals `obsR` of `stateLoop`" UNSUPPLIED |
| row 5 calls | DG-ACC (`Acc`), E1 at the `ext` position (T2COVER §1); memory entries: DC-SUPPLY separate row | induction skeleton | the IH at direct ordinary callees is a pure `Acc` induction (U5 here); the per-call semantic step is row 3 + row 4 at the callee |
| `Tgt X ⇒ P X = some p` | DG-PKGASSIGN / `genP` (DG-SEM, DG-ACC) | the package exists for the targets | dependency, not done |

Table conclusion: the supplied pieces are (a) the `find?` conjunct (from `entry₀`), (b) the `ReadsAt` lemmas E1-E6 as
evidence-side tools, (c) the `Acc` induction skeleton. This survey found no supplier for `CV` itself, for `adapterOf`,
or for rows 1, 3, 4 uniformly.

## 3. Where `DeclConnect` sits in FG, and FG is not shrunk

FG (GENERAL_SPEC.md:88-93), with the schema NOT edited:
`FG : ∀ L declName parameters mctx cctx w b D w', Start … → (RunsTo … ∨ RunsTo …) → ReflectsAll … → ∃ p n, Pk declName = some p ∧ TopShips p n declName b raw D`.

Insertion (rev2 completion, DGEN:§2.6) — three places, none of them a new premise of FG:

1. **`Pk := genP env₀`**, with `env₀ := envAt cref w` for the START world `w` (E1 `readsAt_self` gives `ReadsAt env₀ cref w`).
   This yields FG-REF (INTERMEDIATE): hardware ↔ `p.src`.
2. **`ReflectsAll`'s G3 rows** (GENERAL_SPEC.md:535 table): G3-GEN and G3-SHAPE are DG-SEM / DG-DATAOF / DG-ENV's.
   The "(link)" row — "`body` is `X.machineBody`, the declaration's own value", "G3-DECL (per declaration)" — is
   exactly what `DeclConnect` replaces by ONE uniform proposition. It is NOT a binder of FG; it is a separate
   conjunct of the completion statement (next item).
3. **The completion statement** (not an edit of FG):
   `FG_COMPLETE := FG[Pk := genP env₀] ∧ ConstValueOk CV V3 ∧ DeclConnect CV env₀ (genP env₀) Tgt_run`
   where `Tgt_run X` := X is `declName` or a name `T1Hyp.closed` (Tools/ShippingGen2Defs.lean:218 [S]) reaches from it.
   Composition for the top: from FG's `Pk declName = some p` and `Tgt_run declName`, `DeclConnect` gives
   `p.src = sigObs (A.toSig v)` for the elaborated value `v` of `declName`; so TopShips' `src := p.src` is the
   observation of the declaration's actual value.

Not-shrunk checklist (each is a property the Lean unit must preserve; the check file asserts them by `example`):

| FG property | preserved by | how it is checked |
|---|---|---|
| FG's text, quantifiers and conclusion unchanged | no edit of `Tools/ShippingGen2Defs.lean` / `T1Hyp*`; this issue adds only a new file | `git diff` over the protected paths is empty |
| all successful runs (both entries) | `Tgt_run` is defined from the run's names, not from a corpus | no `Tgt` literal list; U2 (`declConnect_mono`) is the only way `Tgt` shrinks and it is a lemma, not an instance |
| no per-declaration premise | `DeclConnect`'s binders are `CV env₀ P Tgt` only; no `∀ X` hypothesis `hX : …X…` in `declConnect_of_rows` beyond the uniform rows | binder-table listing in the check file |
| `DeclConnect` not vacuous | rev2 existence inside; U3 shows the rev1 form is true for the empty relation while rev2 is false there | U3 |
| `GenWF` not strengthened, no new law | nothing here mentions them | grep in the check file's header audit |
| `ConstValueOk` is not assumed | it is a conjunct of the goal, parameterised by `CV` | statement text |

## 4. Units of pure lemmas

Each unit below depends on none of DG-SEM / DG-DATAOF / DG-ACC. Names are proposals; statements are the frozen part.
All are `theorem`s in `Tools/ShippingGen5DeclConnect.lean`; none uses `sorry`, an axiom or `native_decide`.

```lean
-- U1: unfolding form (the recorded way DeclConnect is read per name)
def DCAt (CV) (env₀) (P : Pkgs ι dom) (X : Name) : Prop :=
  ∀ p, P X = some p → ∃ ci α (v : α) (A : SigAdapter p.d dom α), env₀.find? X = some ci ∧ CV env₀ X α v ∧
    adapterOf ci.type (structEnv env₀) p.d dom = some ⟨α, A⟩ ∧
    ∀ i bools bits, sigObs p.d (A.toSig v) i bools bits = p.src i bools bits
theorem declConnect_iff (CV env₀ P Tgt) : DeclConnect CV env₀ P Tgt ↔ ∀ X, Tgt X → DCAt CV env₀ P X

-- U2: Tgt can only be narrowed by an explicit inclusion
theorem declConnect_mono {Tgt Tgt'} (h : ∀ X, Tgt' X → Tgt X) :
    DeclConnect CV env₀ P Tgt → DeclConnect CV env₀ P Tgt'

-- U3: the rev2 form is not vacuous, the rev1 form is (a statement about the two formulations)
theorem declConnectImp_of_empty (env₀ P Tgt) : DeclConnectImp (fun _ _ _ _ => False) env₀ P Tgt
theorem not_declConnect_of_empty {X p} (hT : Tgt X) (hP : P X = some p) :
    ¬ DeclConnect (fun _ _ _ _ => False) env₀ P Tgt

-- U4: rev2 ⇒ rev1 under functionality; the converse needs the existence conjunct
theorem declConnectImp_of_declConnect (hV2 : ConstValueFunctional CV) :
    DeclConnect CV env₀ P Tgt → DeclConnectImp CV env₀ P Tgt
theorem declConnect_of_imp_exists
    (hImp : DeclConnectImp CV env₀ P Tgt)
    (hEx : ∀ X, Tgt X → ∀ p, P X = some p → ∃ ci α (v : α) (A : SigAdapter p.d dom α),
        env₀.find? X = some ci ∧ CV env₀ X α v ∧ adapterOf ci.type (structEnv env₀) p.d dom = some ⟨α, A⟩) :
    DeclConnect CV env₀ P Tgt

-- U5: the Acc skeleton of row 5 (the IH is only at the direct callees)
theorem dcAt_of_acc {R : Name → Name → Prop} (Ready : Name → Prop)
    (hstep : ∀ X, (∀ c, R c X → Ready c) → Ready X) : ∀ X, Acc R X → Ready X
-- (instantiated with `R := flip (CallEdge env₀)`, `Ready := DCAt CV env₀ P`; the step is rows 0-4 at X given DCAt at the
--  callees; a thin wrapper `declConnect_of_acc_step` states it for `DeclConnect` with `Tgt` closed under callees and
--  `hAcc : ∀ X, Tgt X → Acc R X`)

-- U6: INTERMEDIATE, premise-explicit connection (does NOT use any dependency's proof; NOT completion)
theorem declConnect_of_rows
    (hAcc : ∀ X, Tgt X → Acc R X) (hclosed : ∀ X c, Tgt X → R c X → Tgt c)
    (hstep : ∀ X, Tgt X → (∀ c, R c X → Tgt c → DCAt CV env₀ P c) → DCAt CV env₀ P X) :
    DeclConnect CV env₀ P Tgt
-- `hstep` is the UNSUPPLIED content of rows 0-4 (§2); it is the only place those rows enter.  U6 is the Acc assembly
-- only. `hclosed` is the callee-closure of `Tgt` (`T1Hyp.closed`, G-REACH — unsupplied).
```

U5/U6 prove nothing about the rows; they fix where the rows are consumed. They are reported as "skeleton, rows
unsupplied". U4's `declConnect_of_imp_exists` shows the existence conjunct is the whole difference between rev1 and rev2.

```lean
-- U7 (DCF, DC-FORM): the study unit.  Output = a Lean text + a list of which of V2/V3 are provable. Frozen question,
-- not a frozen definition.
inductive ExprDenotes (env : Environment) : List (Σ α : Type, α) → Lean.Expr → (α : Type) → α → Prop
  -- proposal of constructors: lit (Nat/String literals), bvar (valuation), const-unfold (env.find? c = some ci,
  -- ci.value? = some e, recursive), const-prim (a table entry), app, lam (∀ a, body denotes in the extended valuation)
def ConstValueE (env : Environment) (c : Name) (α : Type) (v : α) : Prop :=
  ∃ ci e, env.find? c = some ci ∧ ci.value? = some e ∧ ExprDenotes env [] e α v
```

DCF's questions, to be answered by its own report (DGEN:§2.6): (a) is the relation definable for delta-unfolding of the
constants `entryConst` unfolds + the reader's node table + the types `Signal`, `Bool`, `BitVec n`, tuples/structures,
`DomainConfig`; (b) universe handling (`Type` only, here); (c) V2 (functionality) and V3 (defined by rules) for the
definition. The point to settle first is **Q4**: the `const-prim` table (for each primitive such as `Signal.register`,
`Signal.loop`, `BitVec.ofNat`, a hand-written pair name ↦ Lean value) is a list of facts "this `Name` denotes this Lean
constant". Whether such a table is a definition or a trusted statement is not decided here; it is §6's item.

## 5. Open questions (do not block the pure units)

- **Q1** the universe/fragment of `adapterOf`: declarations whose type is outside the fragment get `none`. Which
  successful targets those are is a coverage question for DC-SUPPLY, not decided by an example.
- **Q2** `SigAdapter.args` as data (§1 remark; coordinate with SRC-ARGW, which is implementing in `kjob/g3aw-impl`).
- **Q3** `HWType` constructors `bitVectorDim` / `array` in `OutSigs`: whether machine-route outputs ever use them is
  not established by this survey; the `PUnit` fallback would make the equation trivial for them, so they must be
  excluded by a coverage lemma (DG-COVER) or given a real component. Until then they are an open row.
- **Q5** `MachineData.dom : Lean.Expr` vs `dom : ι → DomainConfig`: the relation of the two is part of the `dom`
  component of `adapterOf` and of row 0.

## 6. Decision items (not adopted; none is needed to approve this freeze)

If DCF finds `ConstValue` cannot be a definable relation without a primitive table, or the table is judged a trusted
statement, GENERAL_SPEC.md:505-506 makes that a USER item (new TRUSTED boundary). It would then be written up with
impact, options and cost in a separate document and the issue set to `decision`. That is not triggered by this freeze.

## 7. Not claimed

- No claim that `ConstValue`, `adapterOf`, `DeclConnect` or any row is supplied, or is supplyable by a specific route.
- No claim that FG, FG-REF or M5 is complete. `declConnect_of_rows` is an intermediate Acc assembly.
- No claim about the Lean text's elaboration: nothing was built.
- DG-SEM, DG-DATAOF and DG-ACC are not done; their results enter only as the premises of §1.1 / U6.
- No new law, TRUSTED boundary, FG or guarantee change; no edit of compiler/shared definitions.

## 8. Order after approval

1. U1-U5 (+ `DeclConnectCheck` with the mutants of §3: each a signature/defeq rejection, not a semantic counterexample).
2. U6 skeleton.
3. DCF (U7) as a separate study; its outcome decides whether rows 0, 1, 3 become units or go to §6.
4. The final connection waits for DG-SEM / DG-DATAOF / DG-ACC.

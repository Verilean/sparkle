# DG-ENV T2 unit U2 freeze: `EnvFrameEnd` rows for class B′ (IO lift) and class C (docs only, before any Lean)

Issue `sparkle-gen5-dg-env`. Base: `kjob/g5env-r5` a14f2479 (U1 approved as a conditional result).
Extends `scripts/gen5/DG_ENV_T2_FREEZE_R3.md` (rev3.1) §1.1 rows B′ and C. Nothing here adds a law, a `Laws` field, a TRUSTED
boundary, a premise name or a shared definition, narrows FG, or supplies C0 / QuietStrength / AdmDown / hA′ / L′ / Start L′.
Like U1, U2 is a CONDITIONAL algebra: the cell premises stay hypotheses of the lemmas. Class D, telescope / Diag / AdmCtx /
InertUnfold keep their status in the rev3.1 table (no route found by this survey).

## 0. Probe results (Lean 4.32.1 in this Pod, scratch files, NOT committed)
These are what was checked before writing the types; a probe is not a proof of the theorem below.
* B′: `(liftM (ST.Ref.get r : IO σ) : MetaM σ) = (ST.Ref.get r : MetaM σ)` closes by `rfl`; the same for `ST.Ref.set`,
  `ST.Ref.modify`, `ST.Ref.modifyGet` (4 `example … := rfl` accepted). So the 8 B′ constructors reduce to the U1 lemmas with
  no new premise and no unfolding beyond `rfl`.
* C `metaGet`: the `key` equation (`get : MetaM Meta.State` at the applied world is `ST.Ref.get mref`) holds by `rfl`; a full
  proof with `ReadWorld mref` (U1-7 pattern) was accepted.
* C `fvarThrowUnknown`: `liftM (id.throwUnknown : CoreM α) : MetaM α` at the applied world equals, by `rfl`, a read of
  `cref` followed by `.error` with the world of that read (`addMessageContextPartial` = `getEnv`, `getOptions`, `pure`).
* C `coreModifyTrace`: the `key` equation (it is `ST.Ref.modifyGet cref` with the record rebuild that keeps `env := s.env`) holds by `rfl`.
* C `constInfo`: `getConstInfo` = `getEnv` then `match find?`; the throw path = `getRef`, `mkUnknownIdentifierMessage`
  (`getEnv`, an `if`, `pure`), `throwErrorAt` = `withRef` (context change only) of `throwError`, which is `getRef`,
  `addMessageContextFull` (`getEnv`, `getMCtx` (a read of `mref`), `getLCtx`, `getOptions`, `pure`), `throw`. A skeleton proof of
  `throwError` from `ReadWorld cref` and `ReadWorld mref` reached its last goal (`getMCtx`), which the `get mref` pattern closes.
  The remaining unfoldings (`mkUnknownIdentifierMessage`, `withRef`) were NOT probed to the end.
* C `metaModify`, `freshFVar`: statement shape only. `modify f : MetaM Unit` / `mkFreshFVarId` were not proved in the probes.

## 1. Rows served (counted per FramedA constructor; classes disjoint; from `ShippingChildInvA.lean` `FramedA`)
| class | constructor | lemma | hypotheses |
|---|---|---|---|
| B′ get | `sideGetIO exprCacheGetIO localGetIO` (3) | U2-1 | `ReadWorld r` |
| B′ set | `sideSetIO localSetIO` (2) | U2-2 | `r.ref ≠ cref.ref`, `SetFrame r cref` |
| B′ modify | `sideModifyIO localModifyIO` (2) | U2-3 | `ReadWorld r`, `r.ref ≠ cref.ref`, `SetFrame r cref` |
| B′ modifyGet | `sideModifyGetIO` (1) | U2-4 | same as U2-3 |
| C | `metaGet` | U2-5 | `ReadWorld mref` |
| C | `metaModify` | U2-6 | `ReadWorld mref`, `mref.ref ≠ cref.ref`, `SetFrame mref cref` |
| C | `coreModifyTrace` | U2-7 | `ReadWorld cref`, `SetGet cref` |
| C | `freshFVar` | U2-8 | `ReadWorld cref`, `SetGet cref` |
| C | `fvarThrowUnknown` | U2-9 | `ReadWorld cref` |
| C | `constInfo` | U2-10 | `ReadWorld cref`, `ReadWorld mref` |

Counting rule: per constructor. B′ = 3+2+2+1 = 8 (rev3.1 §1.1 wrote 3+2+3: its "3 modify" included `sideModifyGetIO`, which U2-4 serves).
C = 6. Total constructors served if every theorem closes: 14 of the 40; the 13 class-B ones are U1. Nothing is claimed for the
remaining 13 (class D).

`SetGet` already exists (`ShippingStRefCorrespondence`), as do `ReadWorld` and `SetFrame`. `ReadWorld mref` / `ReadWorld cref` /
`SetGet cref` are further PREMISES of the same kind as U1's, about the opaque `ST.Ref.get/set`; they are not supplied for the
runtime. `U2-7/8` need `SetGet cref` because they are writers of `cref` itself (record rebuild), so `SetFrame` cannot be used.

## 2. Types (frozen). New file `Tools/ShippingGen5EnvFrame2.lean` (lean_lib `Tools.ShippingGen5EnvFrame2`), imports `Tools.ShippingGen5EnvFrame`
```lean
namespace Tools.ShippingGen5EnvFrame2
open Lean
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingChildInv (endW)
open Tools.ShippingStRefCorrespondence (ReadWorld SetFrame SetGet)
open Tools.ShippingGen5EnvFrame (EnvFrameEnd)
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

-- auxiliary lemmas (counted separately from the rows)
/-- (A1) a run that leaves the world unchanged keeps `envAt`. -/
theorem envFrameEnd_keep {α : Type} {x : MetaM α}
    (h : ∀ w, endW mctx mref cctx cref x w = w) : EnvFrameEnd x mctx mref cctx cref
/-- (A2) `throwError` reads only `cref` / `mref` / the contexts. -/
theorem envFrameEnd_throwError {α : Type} (msg : MessageData) (hc : ReadWorld cref) (hm : ReadWorld mref) :
    EnvFrameEnd (Lean.throwError msg : MetaM α) mctx mref cctx cref
/-- (A3) a state update of `cref` that keeps `env`. -/
theorem envFrameEnd_coreModifyGet {β : Type} (g : Core.State → β × Core.State)
    (henv : ∀ s, (g s).2.env = s.env) (hc : ReadWorld cref) (hs : SetGet cref) :
    EnvFrameEnd (ST.Ref.modifyGet cref g : MetaM β) mctx mref cctx cref

-- B′ rows
/-- (U2-1) -/ theorem envFrameEnd_getIO {σ : Type} {r : IO.Ref σ} (hr : ReadWorld r) :
    EnvFrameEnd (liftM (ST.Ref.get r : IO σ) : MetaM σ) mctx mref cctx cref
/-- (U2-2) -/ theorem envFrameEnd_setIO {σ : Type} {r : IO.Ref σ} (v : σ) (hne : r.ref ≠ cref.ref)
    (hf : SetFrame r cref) : EnvFrameEnd (liftM (ST.Ref.set r v : IO Unit) : MetaM Unit) mctx mref cctx cref
/-- (U2-3) -/ theorem envFrameEnd_modifyIO {σ : Type} {r : IO.Ref σ} (f : σ → σ) (hr : ReadWorld r)
    (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref) :
    EnvFrameEnd (liftM (ST.Ref.modify r f : IO Unit) : MetaM Unit) mctx mref cctx cref
/-- (U2-4) -/ theorem envFrameEnd_modifyGetIO {σ β : Type} {r : IO.Ref σ} (f : σ → β × σ) (hr : ReadWorld r)
    (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref) :
    EnvFrameEnd (liftM (ST.Ref.modifyGet r f : IO β) : MetaM β) mctx mref cctx cref

-- C rows (each is recorded as a GAP in the file header if its proof does not close; no hypothesis is added to make it close)
/-- (U2-5) -/ theorem envFrameEnd_metaGet (hm : ReadWorld mref) :
    EnvFrameEnd (get : MetaM Meta.State) mctx mref cctx cref
/-- (U2-6) -/ theorem envFrameEnd_metaModify (f : Meta.State → Meta.State) (hm : ReadWorld mref)
    (hne : mref.ref ≠ cref.ref) (hf : SetFrame mref cref) :
    EnvFrameEnd (modify f : MetaM Unit) mctx mref cctx cref
/-- (U2-7) -/ theorem envFrameEnd_coreModifyTrace (f : TraceState → TraceState) (hc : ReadWorld cref) (hs : SetGet cref) :
    EnvFrameEnd (liftM (modifyTraceState f : CoreM Unit) : MetaM Unit) mctx mref cctx cref
/-- (U2-8) -/ theorem envFrameEnd_freshFVar (hc : ReadWorld cref) (hs : SetGet cref) :
    EnvFrameEnd (mkFreshFVarId : MetaM FVarId) mctx mref cctx cref
/-- (U2-9) -/ theorem envFrameEnd_fvarThrowUnknown {α : Type} (id : FVarId) (hc : ReadWorld cref) :
    EnvFrameEnd (liftM (id.throwUnknown : CoreM α) : MetaM α) mctx mref cctx cref
/-- (U2-10) the `endW` form of `getConstInfo`, including the throwing path (proved without `GetEnvFrame`). -/
theorem envFrameEnd_constInfo (n : Name) (hc : ReadWorld cref) (hm : ReadWorld mref) :
    EnvFrameEnd (getConstInfo n : MetaM ConstantInfo) mctx mref cctx cref
end Tools.ShippingGen5EnvFrame2
```
Proof plans. U2-1..4: `exact` the U1 lemma (`envFrameEnd_get/set/modify/modifyGet`) after the `rfl` of §0 (if the elaborator does not
accept the term as is, `show` the MetaM term). U2-5: U1-7 pattern with `mref`. U2-6: view `modify f` as `ST.Ref.modify mref f` at the
applied world (`rfl`) and use U1-5 for `r := mref`. A3: unfold `modifyGet` to the world of `get` then `set`; with `ReadWorld cref` the world is
`setW cref (g (readOf cref w)).2 w`, and `SetGet cref` gives `readOf cref (setW …)` = that state, whose `env` is the old `env` by `henv`.
U2-7: A3 with `g := fun s => ((), {s with traceState := f s.traceState})`, `henv := fun _ => rfl`. U2-8: `mkFreshId` = `getNGen`; `setNGen`
(`modify` rebuilding the record with `env := s.env`): `envFrameEnd_bind` with a `ReadWorld cref` read and A3. U2-9: `rfl` shape of §0, then `ReadWorld cref`.
U2-10: `getEnv` (U1-7) then, on `none`, `throwUnknownConstant` through A2 (the `withRef` step is a context change only; A2 is
general in `mctx`/`cctx`, so it applies at the changed context). A1 by `rw`. None uses `GetEnvFrame`, `EnvSnapshot`,
`getEnvFrame_of_readKeeps`, `envFrame_getConstInfo` (whose type mentions `GetEnvFrame`), or any `Laws` / `T1Hyp` / `T1HypND` field.

Counting: 13 items = 3 auxiliary (A1-A3) + 4 B′ (U2-1..4) + 6 C (U2-5..10). A private helper (e.g. `getMCtx` as a read of `mref`) is
allowed inside A2 and is not part of the frozen list; every theorem it contributes to is checked by the closure audit.

## 3. Class C rows that do not close, and Tier-1 (new-law) rows
Decided at implementation. A C theorem whose proof does not close is NOT given extra hypotheses: it is deleted from the file, listed in the file
header and the Issue note as "未供給 / この調査で経路未発見" with the step that did not unfold, and the table status of its constructor stays C.
No new TRUSTED clause or law is adopted in U2. If a row can only close with a new law, the exact law statement and its impact are written in the note
only (not adopted). At this freeze no such row is known.

## 4. Checks (`Tests/Gen5/EnvFrame2Check.lean`, lean_lib `Tests.Gen5.EnvFrame2Check`), written from §2 of THIS file, not from the implementation
Imports `Tools.ShippingGen5EnvFrame2`, `Tests.Gen5.EnvFrameCheck` (reuses its `reach` walker with root-self judgement, unknown-name fail and
helper-type-only unresolved control, its `mkForbid`, its fixtures; no walker change) and `Tests.Gen3.ExpectedType`.
* TYPE: Expected propositions elaborated from §2 for A1-A3 and U2-1…U2-10 (13), one comparator `withReducible checkExpected` for positive and negative.
* MUTANT: well-typed single changes of the signatures, rejected by the same comparator (signature / defeq rejections, NOT semantic counterexamples):
  N1 U2-1 with `ReadKeeps r` for `ReadWorld r`; N2 U2-2 without `hne`; N3 U2-2 without `hf`; N4 U2-3 without `hr`; N5 U2-4 without `hr`;
  N6 U2-6 without `hf`; N7 U2-7 without `hs`; N8 U2-8 with `ReadKeeps cref` for `ReadWorld cref`; N9 U2-10 without `hm`;
  N10 A3 without `henv`; N11 U2-9 with the conclusion replaced by `envAt cref w = envAt cref w` for all `w` (frame statement dropped).
  The conclusions of these theorems are single equations (no conjunction), so there is no conjunct-dropping mutant; N11 is the corresponding conclusion mutant. MUTANT total = 11.
* CLOSURE: roots = the 13 items (those that exist after §3); each must reach none of the forbidden constants of `mkForbid`
  (Laws / RefLawsAOps / RefLawsATele / T1Hyp / T1HypND fields, recursors, raw `Expr.proj`, `GetEnvFrame`, `EnvSnapshot`, `getEnvFrame_of_readKeeps`),
  type and value, the root itself judged, an unresolved name is `throwError` with the intended name and path asserted. Controls: the U1 suite is re-run
  against the same walker (direct + helper negatives, unresolved including `ht2` (name only in the helper's type), self-root, clean), and two new
  controls: a fixture that reaches `envFrame_getConstInfo` (must be flagged through `GetEnvFrame`, intended name asserted), and a fixture that
  reaches `getEnvFrame_of_readKeeps` only through a helper type. Counts are reported as `n roots / n negatives (direct + helper) + n unresolved + n self-root / n clean`.
* AXIOMS: standard only (`propext`, `Classical.choice`, `Quot.sound`) for every root; no `sorry`, no `native_decide`.
* `lakefile.lean`: two `lean_lib` entries; one build target at a time, `kjob lake build Tests.Gen5.EnvFrame2Check` (incremental, `-c 2`).
Lean commit ⇒ the Issue stays `doing`, the note says "clean build は coder".

## 5. Not claimed
* No claim that the cell premises (`ReadWorld`, `SetFrame`, `SetGet`, distinctness) hold of the runtime; C0, `defines`, FG, M5, QuietStrength, `L′` are not supplied.
* No claim that class D or the telescope / Diag / AdmCtx / InertUnfold rows are underivable; "no route found" is a result of this survey.
* Probes in §0 are not proofs. Mutants are signature/defeq rejections, not semantic counterexamples.
* No change to `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, the compiler, FG or `GenWF`; no edit of any existing file except `lakefile.lean` (two `lean_lib` entries).

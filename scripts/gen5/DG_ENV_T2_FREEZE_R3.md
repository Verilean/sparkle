# DG-ENV freeze rev3.1: route T2 (runtime-model correspondence) survey, and the first closing unit (docs only)

Issue `sparkle-gen5-dg-env`. Base: `kjob/g5cr-r6` f3a29dbb (S1 43977202; unit (d) 3db43dcb/2b4b7b1a included).
Inputs read in full: `par/gen5-t2:scripts/gen5/DG_ENV_FREEZE.md` (§0, §4.2 axis T, §4.3, §4.4, §4.5),
`Tools/ShippingHeapModel.lean`, `Tools/ShippingHeapProvenance.lean` (header table), `Tools/ShippingStRefCorrespondence.lean`,
`Tools/ShippingEnvSnapshot.lean`, `Tools/ShippingChildInvA.lean` (`FramedA`, `RefLawsAOps`, `RefLawsATele`, `AdmCtx`),
`Tools/ShippingChildInv.lean` (`Diag`, `Throws`, `Op`, `endW`, `Keeps`), `Tools/ShippingGen5Env{,R,Q}.lean`.

Rev3.1 (docs sync, no type change): R1 U1-7 is proved directly (no `getEnvFrame_of_readKeeps`, §2.1 prohibition kept); R2 necessity wording
limited to what was surveyed (§0.1, §1 row 10-13, §3); U1 is a conditional algebra that keeps the cell premises and is NOT a supply of C0.

Status: FREEZE for review. Nothing here adds a law, a `Laws` field, a TRUSTED boundary or a shared definition, narrows FG,
or claims C0 / QuietStrength / AdmDown / hA′ / L′ / Start L′ is supplied. Every "未供給 / この調査で経路未発見" below is a result of
THIS survey (what was read at f3a29dbb), not a claim of impossibility or of necessity of a new law.

## 0. Findings (summary)
1. **The heap model has no environment cell.** `Heap σ` = `cache, synth, depth, other, next, reg` (HeapModel.lean:92-98);
   `HeapLaws` has exactly the fields `frameT excOk frameQ cacheSetQ depthSetQ frame cacheSet depthSet`, about `cv/sv/dv`/`quiet` only.
   In the existing model no `envAt` and no correspondence to the real environment is defined, so this survey found no way to state "EnvFrame / Keeps (ReadsAt env₀)" over `Heap σ` (a statement would need such a definition added; not claimed impossible). The HeapModel header
   itself lists `diag`, `telescope`, `lamTelescope`, `localDecl`, `letDecl`, the Meta-primitive constructors of `Framed` and `excOk` on
   Lean exceptions as having NO counterpart.
2. **What T2 can mean here is the REAL-type route** already started in `ShippingStRefCorrespondence.lean`: cell premises
   `ReadWorld r` / `ReadKeeps r` / `SetGet r` / `SetFrame r r'` about the opaque `ST.Ref.get/set`, plus the proved
   `envFrame_set` (and `getEnvFrame_of_readKeeps`, which U1 does not use). These are PREMISES (the "fit", open); the heap model supplies their model-side
   analogues (`runsTo_getM`, `get_set_other`, `modify_split`, `FramedR.keeps`) but is not connected to them. Using them adds no
   law/TRUSTED boundary only as long as they stay hypotheses of the lemmas; they are not supplied for the real runtime.
3. **`EnvFrame` has the wrong shape for the `Laws` clauses.** `EnvFrame x` (EnvSnapshot.lean:51) speaks about SUCCESSFUL runs
   (`RunsTo`). The clauses `frameQ frameT diag cacheSetQ …` speak about `endW` (either outcome). The needed object is
   `EnvFrameEnd x := ∀ w, envAt cref (endW mctx mref cctx cref x w) = envAt cref w` (§2). For ops that never throw
   (`ST.Ref.get/set/modify` of a ref) the two coincide in strength; for ops that may throw (`getConstInfo`, Meta library) `EnvFrame`
   does not give the `endW` statement.
4. **Verified unfoldings** (`#print` at Lean 4.32.1 in this Pod, probe not committed): `ST.Prim.Ref.modify` and `ST.Prim.Ref.modifyGet`
   are `def`s = `get` then `set` (so the modify class reduces to get + set); `Lean.Meta.whnf` and `Lean.Meta.inferType` are `opaque`;
   `IO.getEnv`, `IO.monoMsNow`, `ST.Prim.mkRef` are `opaque`; `Lean.mkFreshFVarId` goes through `MonadNameGenerator CoreM`'s
   `setNGen`, a `modify` of the Core state that rebuilds the record with `env := s.env`; `Lean.FVarId.throwUnknown` unfolds to
   `throwError`; `isClass?`, `whnfUntil`, `instantiateForall`, `mkLambdaFVars`, `mkAppM`, `unfoldDefinition?`, `reduce`, the four
   telescope/decl combinators are `def`s whose bodies call Meta internals (`isClassImp?`, `whnfHeadPred`, `liftMkBindingM`,
   `whnfMatcher`, …) and the opaque `whnf`/`inferType`; this survey did not unfold them further.
5. **Result:** by this route, 13 of the 40 `FramedA` constructors close for `EnvFrameEnd` from existing premise names with a
   law-free lemma (§2, class B), 8 more by the same lemmas if the `IO` lift unfolds (B′), 6 are candidates needing an unfolding
   check (C), and 13 have no route found (D). The telescope family, `Diag`, `AdmCtx`/`InertUnfold` have no route found. Hence
   `QuietStrength` (an `L′`) is NOT obtained by T2, and C0 is NOT supplied generically.

## 1. Clause-class table (rows are Laws fields; counted per field, 13 fields)
`Fields` = `RefLawsAOps` (9: diag frameT excOk frameQ cacheSetQ depthSetQ frame cacheSet depthSet) + `RefLawsATele` (4:
telescope lamTelescope localDecl letDecl). Target (TQ, FREEZE §4.4.2): `L′.O.quiet w ↔ L.O.quiet w ∧ ReadsAt env₀ cref w`. A field of
`L′` is built from the field of `L` plus the stated extra; "env-free" = the conclusion is only `cv/sv/dv`/`OkExc`.

| # | field of `L′` | what the env part needs (full type below in §2) | T2 closes? | what is missing |
|---|---|---|---|---|
| 1 | `frame` | nothing (conclusion `cv/sv/dv`; from `L.frame` with `quiet′ ⇒ quiet`) | env-free | `AdmDown L L′` (C-ADM new ⇒ old) |
| 2 | `cacheSet` | nothing | env-free | `AdmDown` |
| 3 | `depthSet` | nothing | env-free | `AdmDown` |
| 4 | `excOk` | nothing | env-free | `AdmDown` |
| 5 | `frameQ` | `ReadsAt env₀ cref (endW p w)` for each `FramedA` constructor `p` | partly: classes B/B′ (21 of 40) | classes C (6), D (13); `AdmDown` |
| 6 | `cacheSetQ` | `ReadsAt` after `sparkleChildCache.set v` (success run) | yes, conditional: `envFrame_set` (existing) with `SetFrame sparkleChildCache cref`, `sparkleChildCache.ref ≠ cref.ref` | both premises unsupplied (fit); `AdmDown` |
| 7 | `depthSetQ` | same for `sparkleSynthDepth` | yes, conditional (as 6) | same |
| 8 | `frameT` | `ReadsAt` at `endW p w` for `Throws p` (`throwError`, lifted `throwError`) | candidate (C): unfold `throwError` to reads of `mref`/`cref`; `ReadWorld mref`, `ReadWorld cref`. NOT checked | the unfolding; `AdmDown` |
| 9 | `diag` | `ReadsAt` at `endW p w` for `Diag p` (`profLog ppExpr ioEprintln msgToString ioGetStderr stderrFlush ioHandleMk ioHandlePutStrLn ioHandleFlush`) | no route found (D): `ppExpr` runs registered printers; the others are opaque `IO` prims | a premise per class (not an existing premise name) |
| 10-13 | `telescope lamTelescope localDecl letDecl` | the stability premise of `L′`'s field gives `quiet′ w → quiet′ w′` for the continuation; `L.T`'s premise form cannot produce `envAt w′ = envAt w` | no route found by this survey (D): the heap model has no counterpart; bodies are Meta `def`s over opaque `whnf` | 4 stronger clauses (TQ-F): unsupplied candidate specification; whether they are needed is not established; not requested |

Count by rule "per Laws field": env-free 4 (rows 1-4); closes conditionally 2 (6, 7); partly 1 (5); candidate unchecked 1 (8); no route 5
(9, 10-13). 4+2+1+1+5 = 13.

`AdmCtx` / `InertUnfold` (the context quantifier of every field): the callback `canUnfold? = some f` is an ARBITRARY
`Meta.Config → ConstantInfo → CoreM Bool`. The heap model's `frame_all_false` is the model-side reason a frame statement cannot be
derived for caller-supplied actions. `InertUnfold quiet′ f` says nothing about `f` at worlds that are `quiet` but fail `ReadsAt`; an
`f` that tests `envAt` and behaves inertly only where `ReadsAt env₀` holds would satisfy the `quiet′` clause without the `quiet` one
(shape of a possible counterexample; NOT constructed here, no claim). So `AdmDown` / `hA′`: no route found by T2.

### 1.1 `FramedA` constructors (the 40 of `frameQ`), classes disjoint, counted per constructor
| class | constructors | count | status |
|---|---|---|---|
| B (direct) | get: `cacheGet synthGet depthGet sideGet exprCacheGet localGet`; set: `sideSet localSet`; modify: `sideModify sideModifyGet localModify exprCacheModify`; `env` (= `getEnv`) | 6+2+4+1 = 13 | law-free lemma in unit U1 from `ReadWorld r` / `SetFrame r cref` + `r.ref ≠ cref.ref` (`ReadWorld cref` for `env`); premises unsupplied |
| B′ (IO lift) | `sideGetIO exprCacheGetIO localGetIO sideSetIO localSetIO sideModifyIO localModifyIO sideModifyGetIO` | 3+2+3 = 8 | same statements through `liftM (… : IO _)`; counted closed only after the lift is confirmed to unfold to the B term (`rfl`, as `envFrame_set`'s `key`); not typed in U1 |
| C (unfold check) | `constInfo` (success-only closed by existing `envFrame_getConstInfo`; `endW` of the throwing path open), `metaGet`, `metaModify` (instance to `ST.Ref.get/modify mref`), `coreModifyTrace`, `freshFVar` (record-rebuild writers of `cref` itself: need `SetGet cref` + `ReadWorld cref`, not `SetFrame`), `fvarThrowUnknown` (→ `throwError`) | 6 | candidates; not checked |
| D (no route found) | `mkExprCache localMk` (opaque `mkRef`: no allocation premise exists among `ReadKeeps/ReadWorld/SetGet/SetFrame`; the model's `alloc_spec` has no `cref` cell); `ioEnv monoMs` (opaque OS `IO` prims, no premise class); `whnf inferType isClass? whnfUntil instantiateForall mkLambdaFVars mkAppM unfoldDefinition? reduce` (Meta library) | 2+2+9 = 13 | HeapProvenance's own table marks these OPEN |
Total 13+8+6+13 = 40 = number of constructors of `FramedA` at f3a29dbb (counted from the source).

Distinctness premises: `r.ref ≠ cref.ref` for the 24 `SideRef` cells, `sparkleChildCache`, `sparkleChildSynth`, `sparkleSynthDepth`, and for
`Fresh` local refs. HeapProvenance proves non-aliasing only inside the pure model (`prov_ne_valid`, "valid at the start world"); no
real-type counterpart exists. These are further premises of the same kind as `SetFrame`; not supplied.

## 2. Unit U1 (first implementation): law-free `EnvFrameEnd` rows for class B
New files: `Tools/ShippingGen5EnvFrame.lean` (lean_lib `Tools.ShippingGen5EnvFrame`), `Tests/Gen5/EnvFrameCheck.lean`
(lean_lib `Tests.Gen5.EnvFrameCheck`). Imports: `Tools.ShippingGen5Env`, `Tools.ShippingStRefCorrespondence`. No edit of any existing file
except `lakefile.lean` (two `lean_lib` entries).

Why U1 first: (i) it is the only group whose route exists in the repository (modify reduces to get;set — verified; `envFrame_set` and
`getEnvFrame_of_readKeeps` exist), (ii) it types the `endW` form that every later row (C and `frameQ` of `L′`) needs, so the
success-only `EnvFrame` of E3 is replaced by the form the clauses actually use, (iii) it uses no `Laws`/`T1Hyp` field and adds no
boundary: the cell premises stay hypotheses, (iv) it is a conditional algebra: the cell premises stay as hypotheses, so U1 is not a supply of C0; (v) it states exactly which premises the 13 rows need, which is the input for the
user-judgment material (§3). It does NOT make the premises true and does not give `frameQ` for `L′`.

```lean
namespace Tools.ShippingGen5EnvFrame
open Lean
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingChildInv (endW)
open Tools.ShippingStRefCorrespondence (ReadWorld SetFrame)
open Tools.ShippingGen5Env (ReadsAt)
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The `endW` (either outcome) form of an environment frame, the shape the `Laws` clauses use. -/
def EnvFrameEnd {α : Type} (x : MetaM α) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  ∀ w : Void IO.RealWorld, envAt cref (endW mctx mref cctx cref x w) = envAt cref w

/-- (U1-1) -/ theorem envFrameEnd_pure {α : Type} (a : α) :
    EnvFrameEnd (Pure.pure a : MetaM α) mctx mref cctx cref
/-- (U1-2) -/ theorem envFrameEnd_bind {α β : Type} {m : MetaM α} {f : α → MetaM β}
    (hm : EnvFrameEnd m mctx mref cctx cref) (hf : ∀ a, EnvFrameEnd (f a) mctx mref cctx cref) :
    EnvFrameEnd (m >>= f) mctx mref cctx cref
/-- (U1-3) get -/ theorem envFrameEnd_get {σ : Type} {r : IO.Ref σ} (hr : ReadWorld r) :
    EnvFrameEnd (ST.Ref.get r : MetaM σ) mctx mref cctx cref
/-- (U1-4) set -/ theorem envFrameEnd_set {σ : Type} {r : IO.Ref σ} (v : σ) (hne : r.ref ≠ cref.ref)
    (hf : SetFrame r cref) : EnvFrameEnd (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref
/-- (U1-5) modify = get;set -/ theorem envFrameEnd_modify {σ : Type} {r : IO.Ref σ} (f : σ → σ)
    (hr : ReadWorld r) (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref) :
    EnvFrameEnd (ST.Ref.modify r f : MetaM Unit) mctx mref cctx cref
/-- (U1-6) modifyGet -/ theorem envFrameEnd_modifyGet {σ β : Type} {r : IO.Ref σ} (f : σ → β × σ)
    (hr : ReadWorld r) (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref) :
    EnvFrameEnd (ST.Ref.modifyGet r f : MetaM β) mctx mref cctx cref
/-- (U1-7) getEnv -/ theorem envFrameEnd_getEnv (hr : ReadWorld cref) :
    EnvFrameEnd (Lean.getEnv : MetaM Environment) mctx mref cctx cref
/-- (U1-8) the consumer form: `ReadsAt` survives an `EnvFrameEnd` operation (E2 composed). -/
theorem readsAt_endW {env₀ : Environment} {α : Type} {x : MetaM α}
    (hx : EnvFrameEnd x mctx mref cctx cref) {w : Void IO.RealWorld} (h : ReadsAt env₀ cref w) :
    ReadsAt env₀ cref (endW mctx mref cctx cref x w)
end Tools.ShippingGen5EnvFrame
```
Proof sketches: U1-1 `pure_world`; U1-2 case on `m` at `w` (error: `hm w`; ok: `hf` at the middle world composed with `hm`);
U1-3/4 unfold to the `ST` term as `envFrame_set`'s `key` (`rfl`) then `ReadWorld` (`getW r w = w`) / `SetFrame`; U1-5/6 by
`ST.Prim.Ref.modify`/`modifyGet` unfolding then U1-2/3/4; U1-7 directly inside the lemma: `Lean.getEnv` unfolds to `cref.get` (key lifted as in `envFrame_set`), `ReadWorld cref` gives
`getW cref w = w` / the read value via `readOf_get`, so `endW` returns `w` and `envAt` is unchanged. It does NOT call
`getEnvFrame_of_readKeeps` and does not reach `GetEnvFrame` (§2.1 prohibition kept); U1-8 `ReadsAt.of_envEq`. If a step does not unfold by `rfl`, U1 records that theorem as a gap in the header instead of adding a
hypothesis.

Counting: 1 def + 8 theorems = 9 items. Rows they serve: 13 class-B constructors (6 get via U1-3, 2 set via U1-4, 3 modify via U1-5
(`sideModify localModify exprCacheModify`), 1 modifyGet via U1-6 (`sideModifyGet`), 1 env via U1-7) and fields 6, 7 of §1 (U1-4 at
`sparkleChildCache`/`sparkleSynthDepth`).

### 2.1 Checks (`Tests/Gen5/EnvFrameCheck.lean`), written from this text, not from the implementation
- TYPE: `EnvFrameEnd` body and U1-1…U1-8 against Expected propositions elaborated from §2 (same reducible comparator `withReducible
  isDefEq`, same path for positive and negative controls). Total TYPE = 9.
- MUTANT (signature/defeq rejections, NOT semantic counterexamples), each a single change, rejected by the same comparator:
  M1 `EnvFrameEnd` with the conclusion replaced by `envAt cref w = envAt cref w` (frame statement dropped); M2 U1-3 with
  `ReadKeeps r` instead of `ReadWorld r`; M3 U1-4 without `hne`; M4 U1-4 without `hf`; M5 U1-5 with `hr` dropped; M6 U1-2 with `hf`
  dropped; M7 U1-8 without the `ReadsAt` premise `h`. Total MUTANT = 7 (M1-M7).
- CLOSURE (walker over the proof terms and their dependencies; an unknown name is `throwError`): positive roots U1-1…U1-8 must not
  reach any `Laws`/`RefLawsAOps`/`RefLawsATele`/`T1Hyp`/`T1HypND` field (named projection, raw `Expr.proj`, recursor), nor
  `GetEnvFrame`/`EnvSnapshot`/`getEnvFrame_of_readKeeps` (`ReadWorld`/`SetFrame` appear only as hypothesis binders; no name is
  exempted, so type and value closure of every root, U1-7 included, must avoid them). Negative controls: one root per forbidden class (a Laws projection, a `T1Hyp` field, `EnvSnapshot`)
  and an unresolved name (must `throwError`), plus clean controls (a closed lemma that passes). helper value / helper type negatives as
  in `EnvQCheck`. Counts are stated as `n roots / n negatives / n clean` in the check output.
- AXIOMS: standard only (`propext`, `Classical.choice`, `Quot.sound`) for every root; no `sorry`, no `native_decide`.
- `lakefile.lean`: two `lean_lib` entries; build `kjob lake build Tests.Gen5.EnvFrameCheck` (one target at a time, `-c 4`).
Lean commit ⇒ Issue stays `doing`, note says "clean build は coder".

## 3. Rows with no T2 route found: candidate specifications (unsupplied; need for a new TRUSTED boundary is NOT established) — statements for the user-judgment material, NOT adopted
Format as FREEZE §4.3. These are candidate statements only; this survey found no route for these rows, which does not show that none exists. All in `RefLawsAOps`-style, over the restricted class lists (a law over arbitrary actions is false in the model:
`frame_all_false`; a law over `whnf` etc. that does not restrict `canUnfold?` could have the same defect — not checked).

T1-D (classes D of §1.1, one clause; or split by class):
```lean
  envFrameD : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx quiet mctx cctx →
    ∀ (p : MetaM α), EnvOpD p → ∀ w, quiet w →
    envAt cref (endW mctx mref cctx cref p w) = envAt cref w
```
with `EnvOpD` the closed inductive of the 13 D constructors (`mkExprCache localMk ioEnv monoMs whnf inferType isClass? whnfUntil
instantiateForall mkLambdaFVars mkAppM unfoldDefinition? reduce`). T1-Diag: same with `Diag p` (9 constructors). T1-Throws (only if
class C fails): same with `Throws p`. T1-Tele ×4: the four `RefLawsATele` fields with the stability premise
`(cv/sv/dv equal → (quiet w → quiet w′) → envAt w′ = envAt w → I w → I w′)`. T1-Unfold: `InertUnfold` strengthened to keep `envAt`.
Impact (same as FREEZE §4.4.4/§4.4.6): adds ≈ 8-10 TRUSTED clauses about `envAt`; the `L′` construction still needs `AdmDown`/C-ADM for
`canUnfold? = some f`; guarantee table unchanged from §4.4.6 row "TQ-F + D2". Reversible until a downstream theorem imports them.

## 4. Q-series and C0 under T2 (what this route does for each)
| item | under T2 | status |
|---|---|---|
| `QuietStrength L L′ env₀` (an `L′`) | needs all 13 fields of §1 for `L′`; rows 9-13 and classes C/D of row 5 have no T2 route | not supplied |
| `AdmDown` / `hA′` (C-ADM) | callback `f` is arbitrary; no T2 handle (§1 note) | not supplied; route not found |
| `L′` construction | = rows of §1 + the two above | not supplied |
| Start L′ | `jq_start` (Q9) avoids the cache half via RR1 after the head; `Start L′` itself needs `CacheInvA L′.O (cv w₀)` (`RealChildA L′.O` entries) — T2 does not change this | not supplied |
| C0 (generic, all worlds) | would be an induction over every operation the compiler runs; classes C/D include opaque Meta/IO operations | not supplied |
| rows B | `ReadsAt` survives each B operation given the cell premises | after U1: lemma exists, premises unsupplied |

## 5. Not claimed
- No claim that U1's premises (`ReadWorld`, `SetFrame`, distinctness) hold of the runtime, or that C0, `defines`, `GeneratedAt`, FG, M5 hold.
- No claim that classes C/D are underivable; "no route found" = this survey did not find one.
- Mutants are rejected by signature/defeq comparison; they are not semantic counterexamples.
- No change to `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, compiler, FG or `GenWF`.

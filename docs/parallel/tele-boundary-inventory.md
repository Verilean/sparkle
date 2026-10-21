# `RefLawsATele` (T) runtime-boundary inventory (unit C2)

T = `RefLawsATele quiet mref cref` (Tools/ShippingChildInvA.lean:301): four fields `telescope`
(`forallTelescopeReducing`), `lamTelescope` (`lambdaTelescope`), `localDecl` (`withLocalDeclD`), `letDecl`
(`withLetDecl`). T is an ADDED boundary beyond `RefLawsAOps`. It is a PREMISE; it is NOT proved, and its
logical inconsistency is NOT PROVEN (only the degenerate `quiet = False` model is exhibited).
`projFieldNameA` is therefore NOT premise-free: it takes `T`.

Status words: PROVED / PREMISE / OPEN. "Evidence" = what exists that the real `MetaM` implementation
satisfies the field. Honest summary: for EVERY row the evidence is behavioural only (the corpus/tests run
the code) — there is NO proof and NO structural argument in the repo that the real telescope satisfies T.
`Tests/Compiler/ShippingHierarchySoundnessTest.lean:1735` is a single `projFieldName?` input/output check
(`TwoOut.hi` ↦ `"hi"`), not a law check.

## 1. Rows on the path (Elab.lean line numbers at base par/int-r2)

| # | Elab line | Site | T field | Continuation's effects | Evidence | Avoids T? |
|---|---|---|---|---|---|---|
| 1 | 8504 | `projFieldName?` (`forallTelescopeReducing ctorInfo.type`) | `telescope` | `getUserName` of an fvar of the telescope (local-context read; `throwError` of an `OkMsg` if unknown); no side-ref access | tests only (corpus, one direct check above); no proof | Not without editing the compiler (a pure read of the constructor's binder names would do). Compiler is out of scope. |
| 2 | 6478 | `handleDefinitionUnfold`, inline copy of row 1 (via `CompilerM.liftMetaM`) | `telescope` (B's name: `ForallTelescopeLawA`) | same as row 1 (`getUserName`, string result) | tests only | same as row 1; could call `projFieldName?` instead (compiler edit) |
| 3 | 136–139 → 5855 | `CompilerM.withLocalDecl` in `handleApplicative`'s `lower` | `localDecl` | `translateExprToWire` inside `withVarMapping`; full CompilerM translator recursion (state-threading: the wrapper returns `(res,newS)`) | tests only | no: the fvar must be in the local context for `whnf`/`inferType` of the body |
| 4 | 6205 | `handleLoop` | `localDecl` | `withVarMapping`, body translation, wire cache write | tests only | no (same reason) |
| 5 | 7313 | D9: `Signal.map` composite-body lambda (`toIR` host) | `localDecl` | `withVarMapping`, bespoke `toIR` walk, `try extractBitVecLiteral catch` | tests only | no |
| 6 | 7428/7431/7437/7454/7457 | D12: `Prod.rec`/`casesOn` (1–2 nested decls) | `localDecl` | `rec`, `lctx.find?`, `throwError`, circuit-state writes | tests only | no |
| 7 | 7913 | F `.letE` (non-logic let) | `localDecl` | `sparkleLetWireCache` read/modify, `makeWire`/`emitAssign`, `rec` | tests only | no |
| 8 | 7927 | F `.letE` (logic let) | `letDecl` (`LetDeclLawA`) | as row 7 | tests only | no |
| 9 | 7961/7969 | F `.lam` | `localDecl` | `inferHWTypeFromSignal`, `makeWire`, `addInput`, `rec` | tests only | no |
| 10 | 5359 | `synthesizeFromConst` legacy tail: `lambdaTelescope body` | `lamTelescope` | `splitReturnLeaves`, `emitLeaves`, `bindInputsLegacy`, the whole translation and `finishSynth`: the heaviest continuation | tests only | Only by being in the certified/mixed/machine branch (those do not reach it); the legacy tail itself needs T |
| 11 | 1877 | `splitReturnLeavesStep`: `lambdaTelescope e` (e a lambda) | `lamTelescope` | recursive `splitReturnLeaves`, `mkLambdaFVars` | tests only | no |
| 12 | 1934 | `splitReturnLeavesStep`: `forallTelescopeReducing ctorInfo.type` (field names) | `telescope` | `getUserName` only | tests only | as row 1 |
| 13 | 1997, 2031 | `openRecordInputs`: nested `forallTelescopeReducing` (params; ctor fields) | `telescope` | recursive `walk`, `whnf`/`inferType`, `getConstInfoInduct`, `mkLambdaFVars` | tests only | no |

Rows 10–13 are the legacy tail of `synthesizeFromConst` (`openRecordInputs`, `lambdaTelescope`,
`splitReturnLeaves`); the main-theorem route through the certified/mixed/machine front ends (FrontCP)
does not reach them, but `LegacyTailA` stays in the type for machine-route constants (see FrontCP). Whether
rows 10–13 are on the final path of a given theorem statement depends on that theorem's `LegacyTailA`
premise; I did not re-derive this.

Other lines grep'd that are NOT uses: 1991/1992/2003 (comments), 2112, 2240–2267, 3499, 4253–4390, 5051–5154,
5352–5354 (comments or the pure `telescopeKinds`, which does not run `MetaM`).
`Tools/ReflectSource.lean:119` uses `lambdaTelescope` outside the compiler path (not counted).

## 2. What is PROVED about each field (all conditional on T)

`keeps_forallTelescopeReducing / lambdaTelescope / withLocalDeclD / withLetDecl` and the `keepsCP_*` lifts
(Tools/ShippingChildTeleCP.lean): each is the field instantiated with `StableA`'s two components. They
prove nothing about the real `MetaM`. `projFieldNameA` (ProjFieldA.lean) PROVED from `T.telescope` plus
walks of `getConstInfoInduct/Ctor`, `getUserName`, `try/catch` (no further premise).

## 3. Why T is used at all: IMPLEMENTATION CHOICE, not a necessity result (correction of REPORT-C)

REPORT-C said "any proof of ProjFieldNameA must use a telescope law". That is an over-claim. What is true:
the proof I wrote uses `T.telescope` because it treats the continuation of `forallTelescopeReducing` as an
arbitrary callback. Whether another proof route avoids T (e.g. a law specialised to a continuation that
only reads `getUserName`, or a model of the telescope) is NOT shown either way.

## 4. Feasibility probe (C2-2): proving the telescope from RefLawsAOps by unfolding

Tools/ShippingChildTeleProbe.lean (tp5 exit 0; header has the full result). Outcome: NOT feasible by
unfolding, with the stuck point identified:
* `forallTelescopeReducing` → `forallTelescopeReducingImp` (safe defs, unfold) → `forallTelescopeReducingAux`,
  an `opaque` constant (a `partial def`; kernel-opaque, no equation lemma; same for `…AuxAux`,
  `…AuxAux.process`, `lambdaTelescopeImp.process`, `withNewLocalInstancesImp`, `isClassExpensive?`).
  The goal `Keeps … I (forallTelescopeReducingAux ty none k …)` has no unfolding step. A law about that opaque
  constant is exactly what `RefLawsATele.telescope` states.
* `withLocalDeclImp`/`withLetDeclImp`/`withLocalContextImp` ARE safe defs: `mkFreshFVarId` (a write to
  `Core.State.ngen` via `cref`; no `FramedA` operation covers it), `withReader` (PROVED: `keeps_withReader`,
  by `h`), `withNewFVar` (→ `isClass?`, `withNewLocalInstances`, opaque partial workers). So `localDecl` /
  `letDecl` are stuck at the opaque workers and at `mkFreshFVarId`.
* Therefore: the only piece provable from today's boundary is the reader update; the primitives needing a law
  not in RefLawsAOps are `forallTelescopeReducingAux`(+`process`), `lambdaTelescopeImp.process`,
  `withNewLocalInstancesImp`/`isClassExpensive?`, and the `ngen` write of `mkFreshFVarId`.
  The probe does NOT show that no other route exists.

## 5. What would shrink T (OPEN, not done)
* A specialised law per use (rows 1,2,12: continuation = `getUserName`, no side-ref access).
* Compiler edit of rows 1/2/12 to read binder names without a telescope (excluded by the brief).
* Laws about the opaque workers and `ngen` (a different, finer assumption family; not smaller in trust).

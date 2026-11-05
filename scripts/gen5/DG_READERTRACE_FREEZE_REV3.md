# DG-READERTRACE freeze rev3 — next unit U-R3a (fuel-induction reduction + the non-`app`/non-`letE` arms of `convStep`)

Issue `sparkle-gen5-dg-readertrace`. Base: `kjob/g5rt-r7`, header-sync commit `55f72df6` on top of `1815e012` (U-R1b approved: 13 definitions + 5 leaf lemmas, build `rt6v-1815e012` exit 0, 724 jobs).
Continues `DG_READERTRACE_FREEZE.md` (rev0), `..._REV1.md`, `..._REV2.md`. **Docs only; no Lean is written or elaborated before this freeze is approved.** The Lean texts below are unelaborated proposals read against the files named; an elaboration error found later is fixed in a rev addendum, never silently.
Wording: "not found / 未供給" = this investigation found no supplier or route, never "impossible"; a mutant is a signature/defeq rejection, not a semantic counterexample; conditional results are INTERMEDIATE; approving definitions or a unit is not approval that `TraceGood senv nDecl (readF senv n)` holds.
No new law / TRUSTED boundary / shared-definition change (`Tools/ShippingGen5Cover*.lean`, `ShippingReaderFuelDefs`, `ShippingLetsReaderInv*` are only imported) / FG change / GenWF strengthening is needed or proposed; **no decision is requested.**
Still **not approved and not supplied**: `TraceGood senv nDecl (readF senv n)` as a whole, every arm other than those in §2, U-R2 (extractors), `PhFacts`, `ShapeInputs`, R-in/R-nl/R-dom for `readF` calls, the real run and FG.

## 0. What was read to choose the unit

Read at this base: `convStep … loopRootStep`, `step`, `readF` (`ShippingReaderFuelDefs.lean` 262–600), `Pre/Post/Good`, `step_good`, `readF_good` and the combinators `satp_*` (`ShippingLetsReaderInv.lean` 42–236, 1009–1040), `RdOk/EnvOk/Adv/PureFacts` (`ShippingLetsReaderInvBase.lean`), `InRange/FullInv/FStep` (Cover3), `FReachC/reachC_trans/reachC_sizes_mono` (Cover6), the U-R1/U-R1b files.

**Finding A (a reduction, not a proof).** `TracePost c v = Post c v ∧ FReachC … ∧ PhPost …`. The `Post c v` conjunct is *already* a theorem of the tree: `readF_good senv F n : Good (readF senv n)` (`F : PureFacts senv`, the existing record of named `LetOk` premises) gives `Post c v` from `Pre c` and `readF senv n c = some (some v)`. So in the fuel induction only `FReachC` and `PhPost` need to be proved per arm; `Post` is taken from `readF_good` (the inner calls' `Post`, needed to rebuild `Pre` of the next sub-call, come from `TraceGood` of the table at fuel `n`). `Pre c` itself is *not* implied by `PhPre` (`RdOk` contains `NoLetAlias st.lets`, which is not a conjunct of `FullInv`/`CtlPh`; `EnvOk` is a `LetOk` statement and `InRange` does not descend `letE/mdata/proj`), so each arm still rebuilds `Pre` of its sub-calls from the parent's `Pre` plus `Adv` of earlier sub-calls (the same bookkeeping as `*_sat`).

Rows examined (what closes from existing names, at this base):

| row | finding |
|---|---|
| fuel induction `n = 0` / `n+1` with `Post` from `readF_good` | **closes** (§1.3): `fuel Φ (n+1) c = (Φ c).run (fuel Φ n)` is `rfl`; uses `readF_good`. |
| `convStep` arm `bvar` | **closes**: `convBvar_trace` (U-R1) with `hI,hE` from `PhPre`, `BvarLt (d+|env|+nDecl) (.bvar j)` is the `PhPre` conjunct for `e = .bvar j`; state unchanged ⇒ `FReachC.refl`. |
| arms `mdata`, `proj` | **closes**: `failO`, run is `some none ≠ some (some v)`. |
| catch-all `okO (e, st)` (`fvar mvar sort const lit`) | **closes** with two small new lemmas (§1.1): `NoPh` ⇒ `InRange` for these atoms (`MentionsPh` is `t = tag ∧ j = i` on `fvar ⟨.num (.str .anonymous t) j⟩`, `False` on every other atom, and `NoPh` gives `!phTag t`); `NoLoose d` (`LooseOcc` is `False` off `bvar/app/lam/forallE`). |
| arms `lam`, `forallE` | **closes**: two `cConv` calls (`d`, `d+1`), `reachC_trans`, `envPh_mono`, `reachC_sizes_mono` + `inRange_mono` to carry the first result to the final state, new lemmas `inRange_lam/forallE`, `noLoose_lam/forallE` (§1.1); `d+1+|env|+nDecl = (d+|env|+nDecl)+1` by `omega`. |
| `chainStep` `Circuit.pure'` arm | closes (expected): one `cConv env 0 v`, `NoPh`/`BvarLt` of `v` by the definitions (explicit constructor pattern). **Not in this unit** (kept for the next one so this unit stays one pattern). |
| `convStep` `app` arms 2–8 and generic application | need `RegViewPh/RunAppPh/InstCallPh/InstCallSPh/MemCallPh` + `GetAppArgsPh`, `BundleIotaPh/ProjIotaPh` (U-R2): **この調査で辿った候補経路では未供給**. |
| `convStep` `letE` | needs `rootFloat`/`lift` (`PhFacts`, `partial`/`extern`), `bindLetAlias`-free path only for the default branch; **未供給** here. |
| `nestedStep`, `instStep`, `instSStep`, `loopBodyStep` tail, `loopRootStep` | need U-R2 extractors, `machReserve` reach, `foldO_js_length`, `mapM_length_some`, `SigTyPh`, `InstSFieldsDet`: **未供給** here. |
| `loopBodyStep` `letE` | needs `bindLetAlias_reach` (`resolve` range lemma, rev2 §0): **この調査では既存補題が見つからなかった**. |
| `shapeStart/RootLet/Body`, `ShapeInputs`, `machineShapeF_reach` | **未供給 / 経路未調査**. |

**Chosen unit: U-R3a.** Reasons: (1) every row in it closes from names that already exist (no `PhFacts`, no extern/partial fact, no dg-env/dg-dataof output); (2) the reduction in §1.3 fixes the exact shape in which all later arms are stated (`hstep`: only `FReachC` and `PhPost`, `Post` free), so the later units are written once against it; (3) `lam/forallE` exercise, on the smallest example, the pattern every later arm needs (sub-call `TracePre` rebuilt from the parent's `TracePre` and the earlier sub-call's `TracePost`, state chaining by `reachC_trans`, range carried forward by `inRange_mono`, de Bruijn index arithmetic), so a wrong shape of `PhPre/PhPost` would show up here first; (4) `bvar` is the R-in creation site proved in U-R1, so this unit is its first real consumer.
It is **not** a proof of `TraceGood … (readF …)`: it is a reduction lemma and six of the eleven `convStep` arms.

## 1. Full types (new file `Tools/ShippingGen5ReaderTraceArms.lean`, namespace `Tools.ShippingGen5ReaderTrace`)

Imports: `Tools.ShippingGen5ReaderTraceCtl`. `set_option autoImplicit false`. Opens: `Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv`. `lakefile.lean`: one `lean_lib` for the file and one for its Check (additions only). No existing Lean file is edited.

### 1.1 Atoms, lam/forallE glue (all in-tree facts; no hypothesis beyond the stated ones)

```lean
def IsAtom : Lean.Expr → Prop
  | .fvar _ => True
  | .mvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .lit _ => True
  | _ => False

def ConvBasic : Lean.Expr → Prop
  | .bvar _ => True
  | .lam _ _ _ _ => True
  | .forallE _ _ _ _ => True
  | .mdata _ _ => True
  | .proj _ _ _ => True
  | .fvar _ => True
  | .mvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .lit _ => True
  | .app _ _ => False
  | .letE _ _ _ _ _ => False

theorem inRange_atom {nDecl k : Nat} {st : MachRead} {e : Lean.Expr}
    (ha : IsAtom e) (hn : NoPh e = true) : InRange nDecl st k e

theorem noLoose_atom {d : Nat} {e : Lean.Expr} (ha : IsAtom e) : NoLoose d e

theorem inRange_lam {nDecl k : Nat} {st : MachRead} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo}
    (ht : InRange nDecl st k t) (hb : InRange nDecl st k b) : InRange nDecl st k (.lam nm t b bi)

theorem inRange_forallE {nDecl k : Nat} {st : MachRead} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo}
    (ht : InRange nDecl st k t) (hb : InRange nDecl st k b) : InRange nDecl st k (.forallE nm t b bi)

theorem noLoose_lam {d : Nat} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo}
    (ht : NoLoose d t) (hb : NoLoose (d + 1) b) : NoLoose d (.lam nm t b bi)

theorem noLoose_forallE {d : Nat} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo}
    (ht : NoLoose d t) (hb : NoLoose (d + 1) b) : NoLoose d (.forallE nm t b bi)
```
Proof outlines (not elaborated): `inRange_lam/forallE` = componentwise `Or.elim` exactly as `inRange_app` (`MentionsPh` of `lam/forallE` is the disjunction, Cover2 line ~20); `noLoose_lam/forallE` = `fun b hb => hb.elim (ht b) (hb' b)` (`LooseOcc` of `lam/forallE` is the disjunction with `d+1`, Cover3:26); `noLoose_atom`: `LooseOcc` is `False` on atoms (`| _, _, _ => False`), `cases e` + `exact fun _ h => h`; `inRange_atom`: four clauses, `cases e`; for `fvar ⟨n⟩` split on `n = .num (.str .anonymous t) j`: the clause hypothesis is `t = tag ∧ j = i` for the tag of the clause, and `NoPh` gives `phTag t = false` (as in `noPh_letOk`), contradiction; every other shape: `MentionsPh = False`.

### 1.2 The `convStep` arms of this unit

```lean
theorem conv_basic_trace (senv : StructEnv) (nDecl : Nat) (n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead)
    (hb : ConvBasic e)
    (hpre : TracePre senv nDecl (Call.conv env d e st))
    (v : (Call.conv env d e st).Res)
    (hv : (convStep senv env d e st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d e st) v) ∧
    PhPost senv nDecl (Call.conv env d e st) v
```
`hpre` is used through `Pre` (parent's `RdOk/EnvOk/LetOk 0`, to rebuild `Pre` of the second sub-call of `lam/forallE`) and `PhPre`. `hT` is applied to `Call.conv env d t st` and `Call.conv env (d+1) b s1` (`lam`, `forallE`); for `bvar`, `mdata`, `proj`, atoms it is not used. This theorem takes no `PureFacts` (the `Post` conjunct is supplied by §1.3, not here). Proof outline: `cases e`; `bvar j`: `convStep` unfolds to `FM.pure (convBvar env d j st)`, `run_pure`, `convBvar_trace` ⇒ `r.2 = st`; `lam/forallE`: `satp_bindO` twice (the combinator of `ShippingLetsReaderInv`), first with `Q := TracePost senv nDecl (Call.conv env d t st)` obtained from `hT` and the `TracePre` assembled from `hpre`, second with `Call.conv env (d+1) b s1`; `mdata/proj`: `failO`; atoms: `okO (e, st)`, `FReachC.refl`.

### 1.3 The reduction

```lean
theorem readF_traceGood_of_step (senv : StructEnv) (F : PureFacts senv) (nDecl : Nat)
    (hstep : ∀ n : Nat, TraceGood senv nDecl (readF senv n) →
      ∀ c : Call, TracePre senv nDecl c → ∀ v : c.Res,
        (step senv c).run (readF senv n) = some (some v) →
        FReachC nDecl (callSt c) (callOut c v) ∧ PhPost senv nDecl c v) :
    ∀ n : Nat, TraceGood senv nDecl (readF senv n)
```
Proof outline: `n = 0`: `readF senv 0 c = none ≠ some (some v)`, vacuous (as `readF_good`); `n+1`: `intro c hpre v hv`; `hv : readF senv (n+1) c = some (some v)` is, by `fuel`, `(step senv c).run (readF senv n) = some (some v)`; `Post c v := readF_good senv F (n+1) c hpre.1 v hv`; the other two conjuncts `hstep n (ih) c hpre v hv'`. **`hstep` is a hypothesis: this theorem proves nothing about any arm.** The remaining content of `readF_traceGood` is exactly `hstep` for the seven bodies; this unit supplies it only for the `convStep` constructors `ConvBasic`.

## 2. Not in this unit (explicit)

`convStep` `app` arms 2–8 and generic application, `letE`; `nestedStep, instStep, instSStep, chainStep, loopBodyStep, loopRootStep`; `step_trace`/`readF_traceGood` as a theorem without the `hstep` hypothesis; `bindLetAlias_reach`; extractor `…Ph` lemmas (U-R2); `PhFacts`, `SigTyPh`, `InstSFieldsDet`, `ShapeInputs`, `DomAtomic`; R-in/R-nl/R-dom for `readF` calls beyond the `ConvBasic` constructors; FG. All **未供給** (this investigation did not close them; no claim they cannot be).
The result is conditional on `F : PureFacts senv` (existing record; used by `readF_good`) and, for `readF_traceGood_of_step`, on `hstep`; both are intermediate results and are reported as such.

## 3. Check (new `Tests/Gen5/ReaderTraceArmsCheck.lean`; same requirements as `ReaderTraceCtlCheck`)

* **TYPE.** `checkExpected` (`Tests/Gen3/ExpectedType.lean`) of every declaration of §1 (defs `IsAtom, ConvBasic`; theorems `inRange_atom, noLoose_atom, inRange_lam, inRange_forallE, noLoose_lam, noLoose_forallE, conv_basic_trace, readF_traceGood_of_step`) against an independent `Exp…` written from §1 in own spelling (no copy of the Tools file). Counting rule: one compared declaration = 1; defs and theorems counted separately.
* **Match defs `IsAtom`, `ConvBasic`**: independent `Exp` match version + a full-argument agreement theorem (`∀ e, IsAtom e ↔ ExpIsAtom e`, `∀ e, ConvBasic e ↔ ExpConvBasic e`, proved by `cases e` + `Iff.rfl`/`rfl`), plus a per-constructor comparer (the SAME comparer for the real def and for mutants).
* **MUTANT** (well-typed single changes only; signature/defeq rejections, **not** semantic counterexamples; ill-typed variants are not counted): `ConvBasic` with `.app` ↦ `True`; `ConvBasic` with `.letE` ↦ `True`; `ConvBasic` with `.bvar` ↦ `False`; `IsAtom` with `.sort` ↦ `False`; `IsAtom` with `.bvar` ↦ `True`; `noLoose_lam` with `NoLoose (d+1) b` ↦ `NoLoose d b`; `noLoose_forallE` likewise; `inRange_lam` without `hb`; `inRange_atom` without `hn`; `conv_basic_trace` without `hb`; `conv_basic_trace` conclusion without `FReachC`; conclusion without `PhPost`; `readF_traceGood_of_step` `hstep` conclusion without `PhPost`; `readF_traceGood_of_step` `hstep` without the `TraceGood … (readF senv n)` premise. Each compared by the same comparer, counted separately from TYPE.
* **AXIOMS**: `collectAxioms` per theorem: `propext / Classical.choice / Quot.sound` only.
* **CLOSURE**: value-closure walk from every new declaration as a root (the 2 defs and 8 theorems), `seen` membership of all 10 asserted; forbidden roots (`sorryAx / ofReduceBool / trustCompiler`) self-hit controls; unknown root / helper value / helper type controls with a clean control; negative controls inside `withoutModifyingEnv`; the intended `sorry` negatives are the only `sorry` and their count is written in the header as observed.
* Source: no `sorry`, `axiom`, `native_decide`. Real counts reported; mutants never described as semantic counterexamples.
* Build: `kjob lake build Tools.ShippingGen5ReaderTraceArms`, then `Tests.Gen5.ReaderTraceArmsCheck`, one at a time, logs outside the tree; success SHA recorded in the header by a comment-only commit; after the Lean commit the Issue stays `doing` with "clean build は coder". This freeze is committed **before** and separately from the Lean.

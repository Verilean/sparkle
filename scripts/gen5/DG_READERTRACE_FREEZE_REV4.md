# DG-READERTRACE freeze rev4 — next unit U-R3b (the two non-`letE` arms of `chainStep`)

Issue `sparkle-gen5-dg-readertrace`. Base: `kjob/g5rt-r9`, header-sync commit on top of `605cd7b4` (U-R3a approved: 2 definitions + 8 theorems, build `rt8v-605cd7b4` exit 0, 725 jobs).
Continues `DG_READERTRACE_FREEZE.md` (rev0) … `..._REV3.md`. **Docs only; no Lean is written or elaborated before this freeze is approved.** The Lean texts below are unelaborated proposals read against the files named; an elaboration error found later is fixed in a rev addendum, never silently.
Wording: "未供給 / not found" = this investigation found no supplier or route on the candidate paths traced, never "impossible"; a mutant is a signature/defeq rejection, not a semantic counterexample; conditional results are INTERMEDIATE; approving a unit is not approval that `TraceGood senv nDecl (readF senv n)` holds.
No new law / TRUSTED boundary / shared-definition change (`Tools/ShippingGen5Cover*.lean`, `ShippingReaderFuelDefs`, `ShippingLetsReaderInv*` are only imported) / FG change / GenWF strengthening is needed or proposed; **no decision is requested.**
Still **not approved and not supplied**: `TraceGood senv nDecl (readF senv n)` as a whole; `hstep` for any arm outside U-R3a ∪ U-R3b; U-R2 extractors; `PhFacts`; `ShapeInputs`; R-in/R-nl/R-dom for the remaining `readF` calls; the real run and FG.

## 0. What was read to choose the unit

Read at this base: `convStep … loopRootStep`, `step`, `readF` (`ShippingReaderFuelDefs.lean` ~262–600); `Pre`/`Post`/`ChainOut` and `chain_sat` (`ShippingLetsReaderInv.lean` 139–200, 843–925); `satp_*` (same file 42–135); `EnvOk/RdOk/Adv` (`…InvBase` 195–230); `FStep` (Cover3 319–335); the U-R1 / U-R1b / U-R3a files (`conv_basic_trace`, `readF_traceGood_of_step`, `envPh_mono`, `reachC_sizes_mono`, `inRange_mono`, `noPh_letOk`, `reachC_trans`).

Rows examined (what closes from existing names, at this base):

| row | finding |
|---|---|
| `chainStep` arm 1 (`Circuit.pure'` pattern) | **closes**: one `cConv env 0 v st`; `NoPh`/`BvarLt (env.length+nDecl)` of `v` are conjuncts of those of the 4-fold `app` (by `simp [NoPh, BvarLt]`); `hT` gives `TracePost`; `ChainPh` = `ExprPh` at `d = 0` with `ws = []`; `FReachC` is the conv result's. |
| `chainStep` arm 2 (`Circuit.bind` / `Circuit.next` / `.lam`) | **closes**: `cConv env 0 rhs st` (range/`NoLoose` from `hT`), then guarded by `i < s1.kinds.size`, then `cChain (.unit :: env) rest s1` (`hT`); needs one new glue lemma `envPh_cons_unit` (`EnvPh` constrains only `.val`/`.state`), `BvarLt (L+1) rest` from the `.lam` case of `BvarLt`, `reachC_trans`, and `reachC_sizes_mono` + `inRange_mono` to carry `rhs'` to the final state. `machHandleV` is only *used as a test*: the result `i` is checked against `s1.kinds.size` by the code itself, so no property of `machHandleV` is needed. |
| `chainStep` catch-all (`failO`) | **closes**: run is `some none`. |
| `chainStep` `letE` | needs `rootFloat`/`liftLooseBVars` facts (`PhFacts`) and `cLoopRoot`/`machTailV`/`machBindLet` glue: **この調査で辿った候補経路では未供給** (the `machBindLet`/`bindLet_reach` part exists; `rootFloat` range and `cLoopRoot` are not available). |
| `convStep` `app`: bare-register found (`bareRegs.find?`), `machLoopRead?`, `machReadV` arms | state unchanged, `machSlot i` with `i < kinds.size` (CtlPh `bareRegs` clause / the code's own guard) closes as *leaf* statements, but they only become part of `hstep` together with the dispatch over all `app` arms, which includes arms needing U-R2 extractors (`RegViewPh`, `RunAppPh`, `InstCallPh`, `InstCallSPh`, `MemCallPh`) and `BundleIotaRange`: **未供給**. Kept for the unit that covers the whole `app` dispatch. |
| `convStep` `letE`, `nestedStep`, `instStep`, `instSStep`, `loopBodyStep`, `loopRootStep` | as in rev3 §0: need U-R2 extractors / `PhFacts` / `machReserve` reach / `bindLetAlias_reach` etc.: **未供給**. |

**Chosen unit: U-R3b.** Reasons: (1) both arms close from names that already exist plus one tiny glue lemma — no `PhFacts`, no extractor, no extern/partial fact, no dg-env/dg-dataof output; (2) it is the first consumer of `ChainPh` (`ws` clauses) and of the `FStep.ws`-free `ws` bookkeeping, so a wrong shape of `ChainPh` would show up here; (3) it exercises the `.unit :: env` environment extension and the 2-call chain `cConv`→`cChain` that `nestedStep`, `loopBodyStep` and `letE` later reuse; (4) it keeps the same hypothesis pattern as `conv_basic_trace` (`hT` at fuel `n`, `hpre`, successful run), so `hstep` for the `chain` constructor is later assembled from it plus the `letE` arm.
It is **not** a proof of `TraceGood … (readF …)`.

## 1. Full types (new file `Tools/ShippingGen5ReaderTraceChain.lean`, namespace `Tools.ShippingGen5ReaderTrace`)

Imports: `Tools.ShippingGen5ReaderTraceArms`. `set_option autoImplicit false`. Opens: `Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv`. `lakefile.lean`: one `lean_lib` for the file and one for its Check (additions only). No existing Lean file is edited.

```lean
def ChainBasic : Lean.Expr → Prop
  | .letE _ _ _ _ _ => False
  | _ => True

theorem envPh_cons_unit {nDecl : Nat} {st : MachRead} {env : List MachVal}
    (h : EnvPh nDecl st env) : EnvPh nDecl st (MachVal.unit :: env)

theorem chain_basic_trace (senv : StructEnv) (nDecl : Nat) (n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (e : Lean.Expr) (st : MachRead)
    (hb : ChainBasic e)
    (hpre : TracePre senv nDecl (Call.chain env e st))
    (v : (Call.chain env e st).Res)
    (hv : (chainStep senv env e st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.chain env e st) v) ∧
    PhPost senv nDecl (Call.chain env e st) v
```
`ChainBasic` is a match definition (checked in §3 by an all-argument agreement theorem and a constructor comparison). `envPh_cons_unit` proof outline: `⟨fun v hv => h.1 v (mem of tail), fun b n hbn => h.2 b n (mem of tail)⟩`, the head is `.unit`, which is neither `.val` nor `.state` (`List.mem_cons` + constructor disjointness, as `envPh_cons_val` does the head case).
`chain_basic_trace`: `hpre` is used through `Pre` (to rebuild `Pre` of the sub-calls: `RdOk` of the next state from `Adv`, `EnvOk` by `envOk_mono`/`envOk_cons`, `LetOk 0` of the sub-expression by `noPh_letOk`) and `PhPre`. `hT` is applied to `Call.conv env 0 v st` (arm 1), to `Call.conv env 0 rhs st` and `Call.chain (MachVal.unit :: env) rest s1` (arm 2). The theorem takes no `PureFacts` and no `hstep`. Proof outline (not elaborated): `unfold chainStep; split` (same case split as `chain_sat`); arm 1: `satp_bindO` once, then `satp_okO` with `ws = []` (`ChainPh` vacuous on `ws`); arm 2: `satp_bind` on `cConv env 0 rhs st`, case on the pair `(machHandleV env 0 h, r)`; the `none`/non-matching cases are `satp_failO`; the matching case is `satp_ite` on `i < s1.kinds.size` with `satp_failO` on the false side, then `satp_bindO` on the recursive `cChain`; result state chaining by `reachC_trans`, `ws` clause for the new head `(i, rhs')` from `hX.2.1` carried by `reachC_sizes_mono` (`kinds` and `lets`, `insts` sizes); catch-all: `satp_failO`; the `.letE` constructor is excluded by `hb`.

## 2. Not in this unit (explicit)

`chainStep` `.letE` arm; every `convStep` `app` arm (including the leaf arms noted in §0) and `convStep` `.letE`; `nestedStep, instStep, instSStep, loopBodyStep, loopRootStep`; `step_trace`/`readF_traceGood` without the `hstep` hypothesis; `bindLetAlias_reach`; U-R2 extractors; `PhFacts`, `SigTyPh`, `InstSFieldsDet`, `ShapeInputs`, `DomAtomic`; FG. All **未供給** (this investigation did not close them on the candidate paths traced; no claim they cannot be).
The result is conditional on `hT : TraceGood senv nDecl (readF senv n)` (the table at fuel `n`) and on the successful-run hypothesis; it is an intermediate result.

## 3. Check (new `Tests/Gen5/ReaderTraceChainCheck.lean`; same requirements as `ReaderTraceArmsCheck`)

* **TYPE.** `checkExpected` (`Tests/Gen3/ExpectedType.lean`) of every theorem of §1 (`envPh_cons_unit`, `chain_basic_trace`) and the def `ChainBasic` against an independent `Exp…` written from §1 in own spelling (no copy of the Tools file). One compared declaration = 1; defs and theorems counted separately.
* **Match def `ChainBasic`**: independent `Exp` match version + full-argument agreement theorem (`∀ e, ChainBasic e ↔ ExpChainBasic e`) + per-constructor comparer over all 12 `Expr` constructors (the SAME comparer for the real def and the mutants).
* **MUTANT** (well-typed single changes only; signature/defeq rejections, **not** semantic counterexamples; ill-typed variants are not counted; the count is whatever is measured): `ChainBasic` with `.letE` ↦ `True`; `ChainBasic` with `.app` ↦ `False`; `envPh_cons_unit` conclusion with `MachVal.unit` ↦ `MachVal.handle 0`; `envPh_cons_unit` without `h`; `chain_basic_trace` without `hb`; conclusion without `FReachC`; conclusion without `PhPost`; `hT` at `readF senv (n+1)`; `hpre` for `Call.chain env e st` ↦ `Call.conv env 0 e st` is ill-typed and therefore NOT counted; `hv` ↦ `loopBodyStep`-free variant is likewise not counted.
* **AXIOMS**: `collectAxioms` per theorem: `propext / Classical.choice / Quot.sound` only.
* **CLOSURE**: value-closure walk from every new declaration (`ChainBasic`, `envPh_cons_unit`, `chain_basic_trace`, the agreement theorem) as roots, `seen` membership of all asserted; forbidden roots (`sorryAx / ofReduceBool / trustCompiler`) self-hit controls; unknown root / helper value / helper type controls with a clean control; negative controls inside `withoutModifyingEnv`; intended `sorry` negatives are the only `sorry`, their count written in the header as observed.
* Source: no `sorry`, `axiom`, `native_decide`. Real counts reported; mutants never described as semantic counterexamples.
* Build: `kjob lake build Tools.ShippingGen5ReaderTraceChain`, then `Tests.Gen5.ReaderTraceChainCheck`, one at a time, logs outside the tree; success SHA recorded in the header by a comment-only commit; after the Lean commit the Issue stays `doing` with "clean build は coder". This freeze is committed **before** and separately from the Lean.

# The refusal ledger

Every shape the proof tooling REFUSES, and what investigating it found.

## Why this file exists

All 14 shipping bugs found by the proof work came from a checker
refusing a shape and someone treating that refusal as a bug report
rather than as a proof limitation (see the inventory in
`CertifiedRoundtrip-design.md`).  Bug 9 was found by pressing a width
disagreement that "read like a proof limitation".  Bug 14 was found by
pressing "why can't a zero-width net exist".

Until now each refusal lived wherever it was noticed — a `throwError`
string, a "known boundary" paragraph, or nothing — so there was no way
to ask *which refusals has nobody investigated yet?*  That question is
the one that finds omissions, and a TODO list cannot answer it, because
a TODO only records what someone already thought of.

**The rule:** a refused shape is a HYPOTHESIS ABOUT A BUG until
measured otherwise.  Every entry below must end in one of four
verdicts:

* **BUG** — investigating it found a real defect (with the bug number).
* **REAL** — measured to be a genuine semantic divergence that the
  fragment is correct to exclude (with what was measured).
* **COST** — no divergence; the checker refuses for proof-engineering
  reasons (with the measurement, and what the fix would be).
* **UNEXAMINED** — nobody has pressed it yet.  These are the actionable
  rows.

## Deep route (`#verify_elab_deep`, `Tools/DeepElab.lean`)

| Refusal | Verdict | Evidence |
|---|---|---|
| multi-port memories | COST, semantics validated (pressed 2026-09-10) | The refusal is the DEEP ROUTE's (`CdoM` carries one write port per memory), not the semantics'. The IR semantics DOES model multi-port: `memWritePorts` folds extra ports in order, later enabled port wins. That rule is pinned by `#guard`s in `Semantics.lean` (incl. a collision case), and re-measured here: two ports writing address 3 in one cycle with data 0xAA then 0xBB yields 0xBB. So extending `CdoM` to a port LIST is reification work against an already-validated rule, not a semantic unknown. |
| memory read address reads another combinational read | COST, semantics guarded (pressed 2026-09-10) | The deep route refuses it because read SLOTS are valued before the cones see them, so a chain needs slot ordering. MEASURED that the IR semantics handles the chain correctly when ordered — memory A read at address 1 yields 2, memory B read at that value yields 0x77 — and, importantly, that it is ORDER-SENSITIVE: with B before A the fold silently yields 0 for B, since `rdA` is not yet in the environment. That is not a latent hole, because `stmtWrites` counts a combinational read's DATA as a write and `stmtReads` counts its ADDRESS as a read, so `woCheck` covers it: measured `woCheck [] good = true`, `woCheck [] bad = false`. So the chain is safe at the IR level today and the deep-route fix is slot ordering (value the read slots in dependency order, exactly as `deepOrderBody` already does for statements). |
| combinational read inside a read address (`read slot … inside a read address`) | COST (same measurement as the row above) | Same shape seen from the reifier's `toShallow`: a read slot appearing inside another read's address. Covered by the same finding — the IR semantics is correct and `woCheck`-guarded; only the deep route's slot valuation is unordered. |
| `.inst` / non-single-module designs | REAL | Instances are open-module no-ops by design; closed hierarchical semantics is a research item (F6/D). Composition covered dynamically by hier co-sim. |
| no IR register block matches the DSL's registers | BUG (twice) | This refusal caught the nested-`circuit do` register duplication (5 registers for 3) and, later, the two-pass memory duplication. Fixed by RegDedup; now guarded by the state-correspondence checks (section C). |
| `{repr e} outside the deep grammar` (cone shapes) | COST | Measured on `crc16CcittHW`: the inlined cone is 16 MB of `repr` text vs 43 chars shared, so the refusal is cone SIZE, not a semantic gap. Fix scoped in section C (cone sharing). |
| register types / initial values not closed literals | **BUG — fixed 2026-09-12** (generator scope leak, not a boundary) | Pressing this row found a real defect: `Signal.reg k` with `k` a value parameter died in `#verify_elab_deep` with an internal `unknown free variable`, while the emitter was correct (IR `init=7`). **Cause, observed then confirmed by the fix:** `openLams`/`openLams'` open the definition's lambdas with `withLocalDecl` and RETURNED the collected `runCircuitH` applications out of that scope at both the root and helper sites; `nodeOf` then analysed them outside the local context they mention (`hasFVar = true` measured). **Fix:** analyse inside the callback; only validated `LoopNode`s cross the boundary. No traversal change was needed. **Evidence:** `Tests/Verification/ValueParamInitRepro.lean` — before: `unknown free variable`; after: PROVEN with `_deep_trace` + `_deep_signal_run`. Axioms (CORRECTED — an earlier version of this row claimed standard-only for both, read off a truncated line): `_deep_trace` depends on `propext`/`Classical.choice`/`Quot.sound` only; `_deep_signal_run` additionally depends on `native_decide`-generated axioms (23 for `initCirc7`, from 7 replay lemmas), i.e. `Lean.ofReduceBool` trust in the compiler's evaluation of the checkers — the replay chain's documented trust boundary (design doc "`native_decide` in the obligations"; TODO F2 tracks removing it). No `sorryAx`. A `run_cmd` in the repro file checks exactly these axiom classes per circuit. Covers literal init, param-in-body, param-as-init, `Nat`-derived init, two-level wrapper chain (5 circuits; CI requires exactly 5 PROVEN). Full verification suite exit 0 after the change. **Method note:** three sessions of hypothesis-elimination failed to find this; one session of stage observation (`STAGE ok:` markers under `SPARKLE_DEEP_DEBUG`) located it. Two earlier "ruled out" claims were retracted as unfounded (the `NOTHM` flag does not bound emission; unfired guards may be unreached). |
| negative const | COST (pressed 2026-09-10) | MEASURED: the proven semantics encodes `.const (-1) 8` to 255 and `.const (-128) 8` to 128, and that is exactly `mask w (two's-complement encode)` — the value the reifier could emit, since `CExpr.const` takes a `Nat`. So it is a reifier limit, not a semantic gap, and the one-line fix is to encode at reification instead of refusing. Impact bounded: `spiMasterHW` and `uartTxHW` contain 0 negative consts in their emitted IR. Left refused rather than fixed blind, because a wrong encoding here would be silent. |
| `Signal` return but N ports / no outputs / no registers | COST | Shape restrictions of the reifier, not statements about the circuit. |
| ≥ 16 state slots (`Fin`-literal name table) | COST | Measured: `Fin` literal matches stop being exhaustive past 15 arms. A list-backed table clears that but the not-a-slot reader then needs a literal-count enumeration. No semantic content. |

## Cone level (`Tools/ConeFold.lean`)

| Refusal | Verdict | Evidence |
|---|---|---|
| memories / dynamic indexing in a cone | BUG-adjacent | The `.index` path is where bug 7 (RMW write data losing its array reads) and bug 12 (the reference semantics' own placeholder-width defect) lived. Now modelled by `evalPayload`; the cone-level refusal remains for `#verify_emit` v1. |
| symbolic-width slices | REAL for `sliceDim`; the ZeroWidth SKIP is UNREACHABLE today (pressed 2026-09-10) | `sliceDim` is refused everywhere by the cone passes. The load-bearing related claim — `ZeroWidth.lean` skips modules with symbolic-width ports, asserting zero-width tails "only ever occur in fully concrete `circuit do` designs" — was pressed, because bug 14 WAS a zero-width tail reaching the text. MEASURED, both directions: (a) a Sparkle-native symbolic-width `circuit do` cannot reach the emitter at all — synthesis refuses it ("Cannot synthesise runCircuitH: not inlinable and not a hardware module"), and `dividerQ` (the one `W+1` design in the tree) instantiates at concrete widths, emitting `allConcrete=true, 0 zero-width wires, 0 symbolic ports`; (b) the XiangShan corpus has 0 modules with `parameter`. So the skip is currently unreachable from both directions and the claim holds vacuously. It becomes live the moment either a parameterised SV module enters the corpus or native symbolic-width synthesis is supported — worth a guard then, not now. |

## M4 forward fragment (`Tools/SVParser/EmitSem.lean`)

| Refusal | Verdict | Evidence |
|---|---|---|
| `x1 << 32'd9` (1-bit value, 32-bit literal amount) | REAL (bookkeeping) | Measured against iverilog at widths 1/5/10/32/40: VALUES agree everywhere; only `widthSV = widthOf` fails. Two repair routes tried and both closed (change `widthOf` breaks roundtrip congruence; weaken the invariant kills the immunity bridge). |
| `sub 0'7 x` under a 32-bit xor (CVT32 cone) | REAL | Measured: subtraction is not carry-free, so the cone genuinely diverges (W=32: emission 0 vs IR 4294967168). Permanent exclusion, confirmed in indexed form too. |
| mixed-width bare arithmetic `(x4+y4)+z8` | REAL | Measured 3 ways: formal 0, evalSV 16, iverilog 16, CSim 16 — the FORMAL semantics was the outlier, and the census already classified such modules outside. Full fix is context-directed widening in lowering; parked. |

## How to use this

When adding a checker refusal, add a row with verdict UNEXAMINED.  When
a circuit fails to verify, find the row before assuming the proof is
weak.  The UNEXAMINED rows are the omission-hunting worklist; the fact
that this session's two new refusals both measured as COST is the rule
working correctly in the negative direction.

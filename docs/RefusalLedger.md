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
measured otherwise.  Every entry below must end in one of three
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
| multi-port memories | UNEXAMINED | Never pressed.  Single-port, both read kinds, are proven; nothing says the multi-port IR semantics is right. |
| memory read address reads another combinational read | UNEXAMINED | v1 restriction; no measurement of whether the IR/Verilog timing agrees for that shape. |
| combinational read inside a read address (`read slot … inside a read address`) | UNEXAMINED | Same class as above. |
| `.inst` / non-single-module designs | REAL | Instances are open-module no-ops by design; closed hierarchical semantics is a research item (F6/D). Composition covered dynamically by hier co-sim. |
| no IR register block matches the DSL's registers | BUG (twice) | This refusal caught the nested-`circuit do` register duplication (5 registers for 3) and, later, the two-pass memory duplication. Fixed by RegDedup; now guarded by the state-correspondence checks (section C). |
| `{repr e} outside the deep grammar` (cone shapes) | COST | Measured on `crc16CcittHW`: the inlined cone is 16 MB of `repr` text vs 43 chars shared, so the refusal is cone SIZE, not a semantic gap. Fix scoped in section C (cone sharing). |
| register types / initial values not closed literals | UNEXAMINED | Value-parameter circuits go through a specialised wrapper; whether a non-literal init is a real divergence or only a reification limit was never measured. |
| negative const | COST (pressed 2026-09-10) | MEASURED: the proven semantics encodes `.const (-1) 8` to 255 and `.const (-128) 8` to 128, and that is exactly `mask w (two's-complement encode)` — the value the reifier could emit, since `CExpr.const` takes a `Nat`. So it is a reifier limit, not a semantic gap, and the one-line fix is to encode at reification instead of refusing. Impact bounded: `spiMasterHW` and `uartTxHW` contain 0 negative consts in their emitted IR. Left refused rather than fixed blind, because a wrong encoding here would be silent. |
| `Signal` return but N ports / no outputs / no registers | COST | Shape restrictions of the reifier, not statements about the circuit. |
| ≥ 16 state slots (`Fin`-literal name table) | COST | Measured: `Fin` literal matches stop being exhaustive past 15 arms. A list-backed table clears that but the not-a-slot reader then needs a literal-count enumeration. No semantic content. |

## Cone level (`Tools/ConeFold.lean`)

| Refusal | Verdict | Evidence |
|---|---|---|
| memories / dynamic indexing in a cone | BUG-adjacent | The `.index` path is where bug 7 (RMW write data losing its array reads) and bug 12 (the reference semantics' own placeholder-width defect) lived. Now modelled by `evalPayload`; the cone-level refusal remains for `#verify_emit` v1. |
| symbolic-width slices | UNEXAMINED | `sliceDim` is refused everywhere. XiangShan modules with symbolic widths exist (the zero-width pass skips them because `bitWidth` panics on `W+1`) — nobody has checked whether that panic hides anything. |

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

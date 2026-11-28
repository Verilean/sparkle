# Silent-wire audit of the elaborator (work notes)

Audit base: 16858ddd (the audit itself changed no `Sparkle/Compiler/*` file: probes only). The fixes are on
branch `fix/silent-wire` (PR #187); the "Fixed" column gives the commit for each. Line numbers refer to
`Sparkle/Compiler/Elab.lean` at the audit base.

Run: `kjob lake exe silent-wire-regression-test` (CI, core-dsl; it replaced the `silent-wire-probe` exe, prints the same
verdict lines and exits 1 when a verdict differs from its expected class). Sources:
`Tests/Compiler/SilentWireProbe{,Lib,Symbolic}.lean`, `Tests/Compiler/SilentWireRegressionTest.lean`, driver `Tests/Drivers/SilentWireRegressionTestMain.lean`.
Each probe synthesizes a tiny module at elaboration time and reduces the first register input (or the
output) to "where does it read from" (`counter.done`, `in:p[8:1]`, ...); the verdict is compared with the
unambiguous correct wiring and printed per probe. (The original probe exe always exited 0; the regression test does not.) Checks are structural (IR
wiring at ONE observation point: the first register input or the first output), not by JIT value comparison.
The wrong wirings found are of three kinds: a wrong port or out-of-range slice (#1-#4), a wrong operand order or a
dropped operation (#5), and a wrong port width (#6). A value run was not done.

Classes: (a) silently wrong, confirmed by probe; (b) refused with an error; (c) the observed point has the expected
structure (this is not a claim that the whole module is correct); (d) not confirmed in this audit: no probe reached
the site. (d) is NOT a proof that the site is unreachable; only where an argument is written out below is it more.

## Findings

| # | site | file:line | reach condition | probe(s) | class | suggested fix | Fixed (commit: new verdict) |
|---|------|-----------|-----------------|----------|-------|---------------|-------|
| 1 | `.proj` 2-field slice, `@[hardware_module]` multi-output call hidden behind a non-constant head (`(id (counter s)).done`) | Elab.lean:2356-2359 (`lo := (1-idx)*width`) after port-map miss at 2312-2322 | `recArg.getAppFn` is not the hardware-module const (here `id`), so the branch at 2250-2257 and the port-map lookup both miss; the slice is taken off the instance's FIRST port | pj01, pj02 | **(a)** `.done` reads `counter.val[0:0]`; `.val` reads `counter.val[15:8]` (an 8-bit wire sliced at 15:8, out of range) | exact wiring: after `translateExprToWire eStruct`, if the instance was emitted, look the field up in the port map by the call key of the WHNF'd head, not of `recArg`; otherwise refuse | 43bfa3f6: pj01, pj02 now **(c)** |
| 2 | same, plain (non-attributed) 2-field def with DIFFERENT field widths | 2356-2359 | as 1, with `plainPair` (BitVec 8, Bool) | pj05, pj06 (direct/let forms pj03, pj04 are (c)) | **(a)** `.flag` reads `plainPair.a[0:0]`, `.a` reads `plainPair.a[15:8]` | as 1 | 43bfa3f6: pj05, pj06 now **(c)** |
| 3 | same, plain 3-field def, fields 0 and 1 | 2330 (`if idx <= 1 then pure 2` skips the field-count check), 2356-2359 | as 1 with `plainThree`; the `numFields > 2` refusal never runs for idx 0/1 | pj07, pj08 (idx 2, pj09, is (c) via constructor reduction) | **(a)** `.flag` reads `plainThree.a[0:0]`, `.a` reads `plainThree.a[15:8]` | run the field-count check for every idx (it is only skipped for the heartbeat budget); refuse when numFields > 2 and the port map missed | 43bfa3f6: pj07, pj08 now **(c)** |
| 4 | `.proj` of an `extends` record of a `@[hardware_module]` (`w.done` is `.proj TwoOut 1 (.proj Wide 0 w)`) | 2250-2257 / 2312-2322: outer recArg is a `.proj`, not a const app; port names are flattened (`toTwoOut_done`) while lookups use direct field names | `structure Wide extends TwoOut`, read an inherited field | pe01 (own field `extra`, pe02, is (c)) | **(a)** `r <~ w.done` reads `counter.val[0:0]`; the elaborator also instantiates `counter` separately next to `wide` | exact wiring: map inherited fields through `getStructureFieldsFlattened` names, or refuse when `recArg` is itself a `.proj` | 43bfa3f6: pe01 now **(c)** (`wide.toTwoOut_done`) |
| 5 | Name-based dispatch `name.toString.endsWith ".mux"` / `".register"` (also `.registerWithEnable`, `.memory`, `.memoryComboRead`, `.lutMuxTree`, `.memoize`, `.loop`) | 2900, 2914, 2936, 2961, 2980, 3032, 3086, 3121 | any user def whose last name component matches (`Mine.mux`, `Mine.register`) and enough args | pn01, pn02 (control pn03: `Signal.register` written directly) | **(a)** user `Mine.mux c t e := Signal.mux c e t` is lowered as `mux(c,t,e)` (swapped); `Mine.register` that adds 1 to its input loses the `+1` (register input is the raw input) | match on the exact constant (`Sparkle.Core.Signal.Signal.mux`, ...) instead of `endsWith`; or require the namespace prefix | 36b1dc1e: pn01, pn02 now **(c)** |
| 6 | Width default `extractWidth ... | _ => return 8` (and 510) in `inferHWType` | 510-511 | `BitVec w` whose `w` does not whnf (default transparency) to a literal/closed Nat op: an `@[irreducible]` constant, or a free variable `{n}` in non-parameterized synthesis | pw01, pw02 (control pw03: concrete 16 bits) | **(a)** input port of `BitVec W12` (12) becomes 8 bits; `BitVec n` with `n` never instantiated also becomes 8 bits instead of being refused; no error | refuse (throw "cannot determine width of ...") instead of 8; use `.all` transparency like the surrounding `whnf` | b3e8a3c1: pw02 now **(b)** (refused, names `n`); pw01, pw03 stay (c) |
| 7 | `getWireWidth` returns 8 for an unknown wire name | 257 | wire not in module wires/inputs/outputs | none (no source trigger found) | (d) | throw; `symbolicMode` already throws for known wires | 5630f3d1: throws, naming the wire (no probe reaches it; still (d) as a site) |
| 8 | `match hwType with .bitVector w => w | .bit => 1 | _ => 8` (≥10 sites: 1686,1689,1704,1803,1932,1933,2356,2366,2588,2591,2607,2641,2644,2663,3686) | listed | hwType is `.array` or `.bitVectorDim`. `.bitVectorDim` occurs in parameterized synthesis; in the four symbolic probes the width read went through `getWireWidth`, which refused the symbolic width (not checked for the other sites). for `.array`, `inferHWType` of a Prod containing an array returned `none` (an error) in the cases read; other paths not checked | sy01-sy04 (symbolic Signal.fst/snd, map Prod.fst, map lambda) | (b) for the four `.bitVectorDim` probes (refused: "has a symbolic width"); (d) for `.array` (not confirmed: no probe reached a width default; line 3686 caches 8 for an array-typed sub-module output port) | replace `_ => 8` by `bitWidth` of the hwType (exact for arrays) or throw; keep as is only where unreachable and add an assertion | not changed (sy01-sy04 stay (b); `.array` still (d)) |
| 9 | `numFields` default `pure 2` | 2330-2344 | only evaluated for idx ≥ 2; the `_ => pure 2` arms need a struct type that is not a single-constructor inductive after `whnf`; no probe produced one | none | (d) not confirmed (the confirmed defect is #3: idx ≤ 1 is not checked at all) | throw in the default arms | 5630f3d1: the default arms throw and name the missing type/constructor (at 6c4e474d the `numFields != 2` check already refused; no probe reaches it) |
| 10 | Prod.rec continuation `pure (t1, t1) -- assume same types`, widths `width1+width2` | 1927-1936 | `Prod.rec`/`casesOn` that `reduce` leaves stuck with a single-lambda continuation | pr01 (`match unbundle2 p`) | (b) pr01 is refused earlier ("Unbound variable ... dom"); one probe only, no stuck `Prod.rec` form was found; (d) for the fallback itself (not confirmed) | throw "Expected two-binder continuation" instead of duplicating the type | 5630f3d1: single-lambda continuation throws (pr01 stays (b), refused earlier) |
| 11 | `Prod.fst/snd`, `Signal.fst/snd` slices clamped with `min wireWidth typeTotal` | 1686-1712, 2570-2668 | wire width differs from type-derived width | ps01-ps09: 8x1, 1x8, 3-level nested, `map Prod.fst/snd`, `bundle2` of 8/1 | (c) for the nine probes (consistent widths); the clamp changes the slice only when an UPSTREAM wire has the wrong width (e.g. the first-port placeholder of #1); no probe produced a mismatch by itself, so (d) for the clamp itself | replace `min` by an equality check that throws when `wireWidth != typeTotal` (turns upstream bugs like #1 into errors) | 22cd3baa: `min` clamps replaced by `checkProjWireWidth` (throws when wire width != Prod type width); ps01-ps09 stay (c) |
| 12 | Multi-output call returns the FIRST port wire as placeholder | 3638-3697 | a struct-returning call used as a whole value instead of through the port map | feeds #1-#4 | see #1-#4 | return a sentinel that the slice code refuses, not a real port | open: the first-port placeholder is still returned; its consumers are guarded by #1-#4 and #11 |
| 13 | `outputType` default `.bitVector 8` for an output leaf wire with no declaration | 4337 | leaf wire not in wires/inputs | none | (d) | throw | 5630f3d1: throws, naming the port and leaf wire (no probe reaches it) |
| 14 | Dedup keys: single-output instance cache keyed by parent#child#connections (~3660); multi-output by `canonHardwareKey` | 3660ff | two calls with the same wires reuse one instance (correct: pure module); different args must not collide | pd01 (two calls with different args stay two instances) | (c) | none | none needed (c) |
| 15 | `Signal.lit`-style `.lit` width from `hwType` | 2366 | raw Nat literal typed by `inferHWTypeFromSignal` | none | (d) | none | open (not confirmed) |

Counts over the 36 probes at the audit base: (a) 11 probes, (b) 5, (c) 20 (two of the (c) are the controls pn03 and pw03).
At the branch head (regression test run): (a) 0, (b) 6 (pw02, pr01, sy01-sy04), (c) 30 (including controls pn03, pw03).

## Not probed / open

At the audit base (16858ddd):
- #7, #9, #13, #15: not confirmed; no probe in this audit reached them. #7, #9 and #13 silently picked a default
  (8 bits, 2 fields, 8 bits); #15 types a literal from `hwType`.
- `.array` width default (#8): not probed (an HWVector-typed Signal.map or instance port would be the next probe);
  whether existing IP reaches it was not checked.

At the branch head (PR #187):
- #7, #9, #13 no longer default: they throw (5630f3d1). Still no probe reaches them, so only "existing IP builds
  are not refused" is verified for these guards.
- Still open, unchanged from the base: #8 (the `_ => 8` arms for `.array`; `.bitVectorDim` is refused upstream,
  sy01-sy04), #12 (first-port placeholder, consumers guarded by #1-#4 and #11), #15 (not confirmed).
- #10 beyond pr01: not probed further.
- Value-level (JIT `#sim`) comparison was not done. The (a) findings are visible in the printed IR as: a slice of the
  wrong port or outside the wire (#1-#4), swapped mux operands or a missing `add` in the register input (#5), and an
  8-bit input port where 12 bits are declared or the width is unresolved (#6).
- `Sparkle/IR/RegDedup.lean` (post-pass that merges duplicate hardware) was not audited: out of scope (not Compiler/*).
- Ranking by likely real-world impact: #1/#4 (a hardware module's flag silently replaced by data bit 0 — the original
  Keccak failure shape, still reachable through `id`-like wrappers and `extends`), #5 (any user def named `*.mux`),
  #6 (width-generic code whose width does not reduce), #2/#3.

# Certified-roundtrip — open work

Living checklist for the certified-compilation track (branch
`poc/roundtrip-proof`, PR #134).  Grouped by area; ordering within a
group is rough priority.  Update as items land.

## A. Composition chain (Signal ≡ emitted SystemVerilog)

- [x] The seam: `inlineConeT` / `resolveSlicesT` total twins +
  width/eval preservation (`cone_agrees_with_fold`,
  `cone_resolved_agrees_with_fold`); goal generators call the twins.
- [x] `#verify_elab` per-instance chain: `regstep` / `state_trace` /
  `signal_runModule` / `signal_sv` (Signal ≡ runModule ≡ runModuleSV).
- [x] Deep-side G1 glue (`{f}_deep_coneEval_*`): the general-theorem
  route's `Cdo.irState` cone terms land on the bridge language.
- [ ] **Replay the bridge stack over `Cdo.irState`** — deep analogues
  of regstep/state_trace/signal_runModule/signal_sv, using G1 +
  `irState_eq`-based boundedness (`irState = stateAt.toNat < 2^w` is
  free).  This finishes the deep route's end-to-end chain.
- [ ] **`evalOk` — absolute fold-success.**  `hrun`/`hSV`/`hstep` are
  hypotheses today; `evalExpr` fails only on shape (sliceDim / index /
  arity), so a decidable `evalOk` checker + soundness discharges fold
  success unconditionally.  Removes the last hypotheses from the
  per-instance corollaries.

## B. IR → Verilog remainders

- [ ] **Optimizer preservation.**  File-level identity with the
  shipping emitter now reduces exactly to this: every elaborator
  module classifies `.optRewritten` (alias-canonical fallback), none
  `.bad`.  Prove `optimizeDesign` trace-preserving on the fragment (or
  keep `#verify_emit` per-instance validation as the validated shell).
- [ ] **M3 string layer** — printed text ↔ `SVExpr` parse/print
  inverse (or a tested-TCB framing).  Currently the twin↔shipping-text
  join rests on M0 parse-equality + corpus validation.
- [ ] **M4 residual fragment** — the honest exclusions: byte-strobe
  RMW `shl` width rule, `CVT32ModuleS0`'s `sub 0'7 x` cone (not
  carry-free).  Revisit only via a width-indexed `emit_sem` if ever
  worth it (measured payoff was ~1 array; parked).

## C. Deep-elaborator coverage

- [ ] **uart orphan goal** — `uartTxHW` is 21→1; the last is an
  ill-scoped postponed-unifier side goal.  Needs a deep-API change:
  remove `Γr.get` from the cone types (per-circuit literal-width
  fields, or an explicit width-vector variant), not another tactic.
- [ ] Nested `circuit do` composition.
- [ ] Non-Signal value parameters.
- [ ] Memories / sub-instances (`.inst`) in the deep grammar.
- [ ] Bridge v1 limits: register inputs that aren't `.ref` wires
  (emission currently skipped); memory-bearing modules (memFree
  premise).

## D. Trust base

- [ ] **`native_decide` → `decide` hardening** where feasible.  Many
  checker/equation discharges ride `ofReduceBool`.  HashMap paths
  can't kernel-reduce (USize hashing); list-shaped stop sets / width
  tables could.
- [ ] Closed hierarchical semantics (`.inst` as state trees /
  flattening proof).  Research boundary; hier co-sim covers it
  dynamically today.

## E. Housekeeping

- [x] CI green (Build: umbrella imports + `sparkleModuleDeps` +
  SVParser hard-link args; zero-width symbolic-width guard).
- [x] PR #134 body refreshed (seam / composition / bug #14).
- [ ] `docs/CertifiedRoundtrip-design.md` — add the seam / composition
  / bug #14 sections; the bug numbering there and in older session
  notes drifted (an earlier "bugs 9–12" batch overlaps a separately
  numbered "#9 zero-width"; the canonical list is the PR table, now 14).
- [ ] Zero-width pin test (`Tests/…`): assert emitted Verilog carries
  no `logic [0:0]` pack remnant and an 8-bit counter counts 1..N —
  belt-and-suspenders beyond the M4 checker + iverilog spot check.
- [ ] Untracked scratch files at repo root (`episode.json`,
  `multiDeck.json`, `schedule`, resubmission draft) — decide keep vs
  gitignore vs remove.

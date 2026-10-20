# What remains, by kind (state at poc after the review of 3a45a5f4, 2026-10-20)

This replaces a count of premises with the KIND of each remaining item. Every theorem named below is
built locally under cgrun (3 GiB, swap 0, -j 1); runs and exits in `docs/parallel/O-origin-integration.md`
(round "review of 3a45a5f4"). Not CI; nothing pushed; full corpus not re-run.

The end-to-end statement for a parent is `<p>_sat` / `<p>_satC` / `<p>_satC2`: from the premises
`hr` (a successful run of the full entry), `MachineDefines`, `EntryDefines` (`hR0`), `ChildBnd`, for every
typed input stream and every `T`, a closed run of the emitted design objects from the constructed
start state exists and shows the source, and every such run shows it. Below: what stands between that
and an unconditional claim.

## 1. Runtime (the `ChildBnd` premise; IO/ST refs, MetaM, printers)

| item | status |
|---|---|
| depth balance of an OUTERMOST entry, success and exception; start condition carried to the next entry | **PROVED relative to the laws** (`Tools/ShippingChildBalance.lean`: `core_balance`, `full_balance`, `core_bnd0`, `core_then_core`, `endSeq_bnd`, `seq_start_bnd`). Only one `RefLaws` witness used; no law added. |
| refs' contents at the FIRST entry (`sparkleChildSynth = some synthesizeChild`, depth 0; `initialize`, `IO.mkRef`) | OPEN (R13/R14) — premise of the first entry's `ChildBnd0`. |
| commands run BETWEEN two entries (non-Sparkle elaboration) | OPEN — `endSeq` assumes each entry starts in the previous one's end world. |
| ref-only fragment of `RefLawsCore` (get/set/modify of the three refs, non-aliasing of distinct refs, read frame, quiet kept by ref writes) | **satisfied in a PURE heap model only** (`Tools/ShippingHeapModel.lean`, `HeapLaws.model`, `heapLaws_sat`; no axioms). Not a statement about Lean's runtime. |
| fit of the pure model to the `@[extern] opaque` `ST.Prim.Ref.get/set` and `Void IO.RealWorld` | OPEN (ledger row b, `docs/parallel/heap-model-audit.md`). Includes non-aliasing of SAME-typed refs (`sparkleSubModuleCache` has the cache's type; several `IO.Ref Nat`). |
| `diag` (printers, stderr, file handles, logger), `excOk` (T3: Lean primitives' exceptions are `OkMsg`), the Meta-primitive part of `frame`/`frameQ` (`whnf`, `inferType`, …), `telescope`/`lamTelescope`/`localDecl`/`letDecl` | OPEN, not modelled (rows c). |
| joint satisfiability of the full `RefLawsCore` (R0) | OPEN — every `ChildBnd`-premised theorem may be vacuous until it is shown. |
| six fields the audit flags as FALSE of the real runtime (not logically inconsistent): every-context quantification meets the caller-supplied `Meta.Context.canUnfold?` callback; native reduction (`reduceNative?`) under `frame`; re-typed aliases of the cache cell via caller-supplied refs; `diag` over arbitrary file handles; `OkMsg` content of Lean's own exceptions; no concurrency statement | NEEDS A DECISION — the repairs suggested in `heap-model-audit.md` change the laws' scope. Nothing changed. |

## 2. Reflection (the declaration's value is the reified source)

| item | status |
|---|---|
| `MachineDefines` (parent), `EntryDefines` of the gate child (`hR0`) with the gate source's `old`/`peel`/`wf` | premises; checked per declaration by the generators' kernel `rfl`s (translation validation), not proved for all declarations (shape reader, Stage 3, open). |
| closing `MachineClosesAt` (`<p>_closesR`) and the value equation | per-parent proofs; not produced by the certificate. |
| inliner candidate (six env premises, `passF ≈ passM`, `replaceNoCache` vs extern `replace`) | OPEN, unchanged. |

## 3. Input coverage (which compiler-accepted inputs the theorems reach)

| item | status |
|---|---|
| certificate route (`gateParentCertOk`, `memGateOk`, `satDataOk`, `satOfCert`, `generateCert2W`; `<p>_satC2` needs per parent only data, `closesR`, the value equation and the outer premises) | covers: one gate child, one memory origin, data width ≠ 1, the one-level composed route (`composedGW_of_T`, `Reset1`). Instances: the four collision parents. It does NOT cover all compiler-accepted inputs. |
| nonzero slot inits | probe nz3: on the LEAF route a dead register with init 7 is removed by the optimizer (`weS = 0`, so `st0 = init` violates `Bounded`); in the probe's instance parents `opt == b`. GENERALISED (built): head `machine_design_noPortsTBS` (separate target start state `stO`, agreement on names both drive, `BoundOff st0`), `hierRefineCheck_linkedS`, `weS_driven_checkedOptimize`, run lemma `slotRegs_runMT` (every core register is a slot's, at its width), assembly `sat_of_designClosedBS` (data `init < 2^width`; `st0` = slot inits, `stO` = `st0` cleared where the optimizer removed a driven name; on this route `mergeChecked` is the identity, so no slot register is lost before the optimizer). Instance: `<p>_satS` for the four collision parents (their inits are 0, so this checks the route only). OPEN: an instance parent with a NONZERO init (needs its own per-parent chain, or a certificate variant `satOfCertS`); the leaf route's heads are not generalised. |
| other routes (leaf heads, memory-bearing parents with registers outside this certificate, multi-level hierarchies) | not addressed by this round. |
| corpus-level coverage | not re-measured (no full corpus run). |

## 4. SV text bridge (from emitted objects to the printed string)

| item | status |
|---|---|
| the emitted design OBJECTS (`emitAssigns`/`emitRegs`/`emitMemWrites`) run under `DesignSV`/`TextRun` as the source | PROVED (forward simulation, `design_sv_runN`, and the `_sat` conclusions). |
| the printed bytes (`toVerilog`/`toVerilogDesign`) denote those objects | TRUSTED printer (TrustBase §6c); parse-back is validation only, on the suite. |
| uniqueness of the closed run (the connected texts admit no other run) | the `_sat` conclusion states "every run shows the source" for runs of the `DesignSV` relation; nothing about Verilog simulators' scheduling. |

## 5. The run itself

`hr` — that the compiler's run on the declaration succeeds — is a premise. No theorem claims a successful
run exists.

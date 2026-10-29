# Loop-form package and the real-IP instance: result

Issue `sparkle-gen2-loop-pkg` (milestone `sparkle-gen2`).
- **Plan:** scripts/gen2/LOOPPKG_FREEZE.md: §5 (rev1, step 0 + R1 accepted 752b0084) and §6 (rev2, approved f8622fb4).
- **Branch:** `par/gen2-spec`.
- **Changes:** new proof/test files, the mechanical refactor of the gen2 files (§6 rule), and lakefile registrations.
  No production or compiler change.

## Steps and builds (all issue-linked, head = base)
| step | content | job (exit 0) |
|---|---|---|
| 0 | generator probe on `quantModule` (`#machine_endpoint`, `#machine_composedT`, inventory) | `g2lp-1ff48ce9` |
| 1 | `Tools/ShippingGen2Loop.lean`: `machine_traceL_of_loop_causalRA_ranA` (A-boundary), `LoopFacts`, `SrcPkgL`, `genTraceL`, `letObsLoop_hl` | `g2lp-84865a42` |
| 2a | `Tools/ShippingGen2Pkg.lean`: `Pkg`, accessors, theorems `Pkg.trace`/`ok`/`body_eq`/`lsrc_hl` (by cases), `Pkgs.lift`, `DataOkLiftCompat` | `g2lp-cc71fc33` |
| 2b | refactor: `SrcPkg` split to `Tools/ShippingGen2SrcPkg.lean` (text unchanged), Defs over `Pkg`, Tools files per the §6 rule; no new premise | `g2lp-60465f83` |
| 2c | regressions through `Pkg.gen`: U0Check, CallDecInstance, AdaptInstance, MemParentInstance | `g2lp-0e4cdf99` |
| 2d | `Tests/Gen2/PkgCompat.lean` (old texts from f1a4367f) | `g2lp-45c937c1` |
| 3 | `Tools/ShippingGen2LoopRestrict.lean` (`loopFacts_restrict`), `Tests/Gen2/QuantInstance.lean` | **`g2lp-94ed8609`**, 741 jobs, log SHA-256 prefix `01c28f6f058224ba` |

Failed diagnostics, none of which changed a statement:
- `g2lp-6619ad15`, `g2lp-f1bde40d`: inventory script;
- `g2lp-97db82ab`: INVALID, a process error (the target file was missing);
- `g2lp-c3a564e1`, `g2lp-ad1a6492`, `g2lp-158b70d2`, `g2lp-7df988dc`: instances, names, a stray docstring;
- `g2lp-5f70fa3c`, `g2lp-b87691e3`, `g2lp-1816e946`, `g2lp-d65f94b3`: the step-3 elaboration path (a whnf timeout fixed by the generic restriction, `kD` measured as 10 by `#reduce`, explicit call arguments, distinct named holes).

The Tools gen2 files are unchanged after 2b, except the new `ShippingGen2LoopRestrict.lean`. Steps 2c/2d therefore
cover the refactored Tools as built at 3.

## Axioms (`#print axioms`)
- **`g2lp-94ed8609`:**
  - `quant_hcausal`: `[propext, Quot.sound]`;
  - `q_memDec`, `q_extInS`, `q_dataOk`, `q_ships`, `memParent_ships`, `Pkg.trace`, `genTraceL`:
    `[propext, Classical.choice, Quot.sound]`.
- **`g2lp-45c937c1` (PkgCompat):** `shipsRes_eq`, `t1Hyp_iff`, `stepStmt_compat`, `t1Stmt_compat`, `servedShips_compat`
  and `keepChild_eq` are standard.
- No `sorry` in the new files.
- `Tests/Gen2/QuantInstance.lean` sets `maxHeartbeats 8000000` at file scope, for the `decide` elaboration over the large
  generated data. It applies to every later declaration in that file.

## The real-IP instance `q_ships` (Tests/Gen2/QuantInstance.lean)
`memParent_ships L qPkg …` for `qPkg := Pkg.loop qL`, the loop package of
`Sparkle.IP.Video.H264.QuantSynth.quantModule`, at `Unit`.

| premise | supplier |
|---|---|
| package `LoopFacts` | `quant_facts`: the generated `machine_ok`, `_body`, `_inits`, `_reset`, `_writes`, `_result`, `_source` (refl-checked by the generator) and `quant_hcausal`, restricted to `Unit` by the generic `loopFacts_restrict` |
| `hcausal` (source-level causality obligation) | `quant_hcausal`, assembled as `loopCalls`: `CtxAgree.of_state`, `machine_causal_0`/`_1`, two `extendBits_val` steps; the Bool side by `rfl` (no Bool call). Kernel-checked, named, no proof-term extraction |
| `MemDec` (both calls) | `q_memDec`: `MemFacts` over `letObsLoop` / `ext (Signal.loop f)`. Call 0 is `combo 4 16` with args `[7,8,9,6]`; call 1 is `sync 4 16` with args `[6,28,3,29]`. The generator's `memTactic` steps (`rfl`/`decide`) |
| `MemOrigin` | `memOrigin_of_memDec` (Unit) |
| `ExtInS` | `q_extInS`: `machineExtB` is the input family (`rfl`); `machineExt` is `extendBits` at positions `≥ kD = 10` (split + `omega`) |
| `MemParentDataOk` | `q_dataOk`: `machine_ok` + `decide` on the rows |
| case premises | `q_insts_ne`, `q_fne`, `q_slotsNe` (`decide` on `machineData`) |
| run premises (`AdmCtx`, `JQC`, the run, `hpost`, `MachineDefines`, `MachineTaken`) | hypotheses |

**What the instance shows and does not show:**
- It is a CONDITIONAL instance: package and data satisfiability on a real IP top, with the compiler-run premises as
  hypotheses. It is NOT evidence that an actual successful run exists.
- `machine_source` ties the generated `src` to the generated loop. That this is `quantModule`'s own meaning is G3-DECL
  by construction, and it is not derived by the kernel.

## Compatibility (PkgCompat, §6 rules)
- **rfl at `.gen`:** `ChildShips`, `CallDec`, `MemDec`, `TopShips`, `MemParentDataOk`, `ExtInS`, `MemOrigin`.
- **Equal at `Pkgs.lift`:** `ShipsRes`, `ShipsAt`, `CacheShips`, `InvAt`, `IHAt`, `BodyKeepsInv`, `ChildKeepsInv`,
  `KeepBodyStmt`, `KeepChildStmt`.
- **iff:** `T1Hyp`, with `DataOkLiftCompat` (tests only).
- **NEW → OLD:** `MemParentStmt'`, `MemParentStmt`, `LeafStmt`, `StepStmt`, `T1Stmt`, `ServedShipsStmt`.

## Not claimed / open
- **Not claimed:** the existence of an actual successful run; generic loop-package coverage (that every loop
  declaration is accepted by the generator and yields `quant_*`-style suppliers); M5 G3-GEN/G3-DECL; M2/T1/FG
  completion.
- **Still open:** G-MEMCALLS (a generic `MemDec`), the generic supply of `ExtInS`, data/`MemOrigin` coverage,
  G-CLOSES-FRESH, and every other named gap.
- **The M2 IP item.** M2 required a non-vacuous memory-parent instance on a real IP top. `q_ships` supplies it as the
  conditional instance planned, and that item's acceptance is the reviewer's.

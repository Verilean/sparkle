# SRM9 type diff: the `composed` binder of `Tools.ShippingShipsFree.machine_ships_hierC_at_free` vs `ComposedNW`
Full binder tuples (index, binderInfo, name, isProp, type): `scripts/srm9/PREMISES.txt` (8 theorems, 158 binders; compared EXACTLY by `Tests/Compiler/Srm9AuditTest.lean`). Row `composed` of `machine_ships_hierC_at_free`, `ComposedG`/`ComposedNW`: source in `Tools/ShippingMachineShipsHier.lean:115`, `Tools/ShippingMachineDepthRun.lean:34`.

Binder: `∀ {mctx mref cctx cref w w' m design}, RunsTo (synthesizeCombinationalCore declName [] false) … w (m, design) w' → MachineDefines … declName d.shape → C mctx mref cctx cref → Bnd mctx mref cctx cref w m design → memFree m.body → ComposedG KS Reset declName d kD m design dom src ext extB`
(`KS` = `fun D => KSn (childMap D.modules) n`, `Reset` = a free parameter of the endpoint).

| # | `ComposedG KS Reset …` (binder) | `ComposedNW n …` (SRM4 `topshare*_composedNW`, `memCallee_composedNW`) | status |
|---|---|---|---|
| 1 | `∃ ids, nodup ∧ length, ∃ cache regs, nodup ∧ length` | same | identical |
| 2 | no `lets` | extra `∃ lets, lets.length = d.letBs.length` | NW stronger; dropped by `composedG_of_NW` |
| 3 | no `MachineWired` | extra `MachineWired declName d.shape ids cache m dsn regs lets` | NW stronger; dropped |
| 4 | state of the kids `kids : String → σ` | `kids : String → KT n` | σ := KT n |
| 5 | hypothesis `Reset m dsn kids` (abstract `Reset`) | hypothesis `∀ iname mc, (∃ conns, inst mc.name iname conns ∈ m.body) → moduleByName dsn.modules mc.name = some mc → ResetN dsn n mc (kids iname)` | `ResetNk n m dsn kids` is DEFINITIONALLY this hypothesis, so the binder holds at `Reset := ResetNk n`; for another `Reset` an implication `Reset m dsn kids → ResetNk n m dsn kids` would be needed (hRI is satisfied at `Inv = True` by `true_inv`, independent of this) |
| 6 | stepper `runModuleTG (KS dsn)` | `runModuleTG (KSn (childMap dsn.modules) n)` | identical at `KS := fun D => KSn (childMap D.modules) n` |
| 7 | extra antecedent `Tools.ConeFold.memFree m.body` | none | binder weaker; the antecedent is unused |
| 8 | ∀ run with only `C` and `Bnd` as boundary | needs `O`, `T`, `AdmCtx`, `JQC O 0 w`, the `MachineDefines` of all callees, `hcalls`/`hF`/`hgrp` | NOT derivable from `C`/`Bnd` generically; instance bundles `TmBnd`/`TqBnd` (PREMISES) |
| 9 | any depth `n` of the endpoint | `topshare*_composedNW` is at depth 2 | endpoint instantiated at `n = 2` |

Bridge 1..7: the GENERIC, pre-existing `Tools.ShippingMachineShipsDepth.composedG_of_NW : ComposedNW n … → ComposedG (fun D => KSn (childMap D.modules) n) (ResetNk n) …` (`ResetNk` is that file's definition of row 5). Row 8 is the only open generic gap; SRM9 closes it for `topshareM`/`topshareQ` only.
SRM8's supplier `memCallee_composedNW` applies to a CALLEE whose calls are all memory entries; `topshareM`/`topshareQ` call ordinary callees (`child? = none`), so their suppliers are `topshareM_composedNW`/`topshareQ_composedNW`.

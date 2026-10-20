# Pair-of-Signals call results: `out_0`/`out_1` vs packed `out` (reviewer 2026-10-19)

Integrator, 2026-10-19, compiler = poc 6e70d28a + the applied origin-tag patch (working tree; see
`S-memname-collision.md` §5.4). Probe `Tests/Compiler/ProdResultProbe.lean` (never-failing), runs `pr1`–`pr5`,
3 GiB, swap 0, `-j 1`, exit 0 (pr4 exit 1: a syntax error in the probe's `cMatch`, rewritten for pr5).

## Measured (actual parent compilation, both routes, instances and connections printed)

| parent | callee result | machine shape at `entryConst` | certified route | legacy route |
|---|---|---|---|---|
| `cPair` / `cSnd` / `cSame` (`circuit do`, `k.1`/`k.2`) | pair OF Signals (`kPair`, `pairOf`) | none | callee INLINED (no instance; e.g. `slice w 15 4` in the top) | the same |
| `useFst` / `useBoth` (`Signal.loop`, `p.1`/`p.2`) | pair OF Signals | none | inlined | inlined |
| `pRet` (the call is the result) | pair OF Signals | none | top outputs `out_0`, `out_1`, callee inlined | the same |
| `cMatch` (`match kPair w with \| (_, y) => …`) | pair OF Signals | none | throws (`cMatch.match_1` not inlinable) | throws (same) |
| `cSig` / `useSig` (`Signal.fst p`) | Signal OF a pair (`sigPair`) | none | instance of `sigPair`, ONE port `out : bitVector 16` connected whole | the same |
| `cTwo` (control, user structure `Two`) | structure of Signals | entries `(kTwo,[0],bits 4)`, `(kTwo,[0],bits 12)`, fields `[lo, hi]`, origins `[field 0, field 1]` | one instance, `lo`/`hi` connected to `inst0`/`inst1` | one instance, same ports |

No parent tested puts a pair-of-Signals call on the machine route, so no emitted `out_0`/`out_1`-vs-`out`
connection exists to be wrong in these cases.

## Source review (not measured)

* `machOuts?` (Elab.lean ~3865) gives `out_0`/`out_1` for a type `Prod (Signal …) (Signal …)`; `machTupleKinds?`
  (~3840) matches only `Signal dom (Prod …)` (a Signal OF a pair, packed `out`). For a pair-OF-Signals callee,
  `declOuts?` (`Tools/ShippingMachineShapeUnfold.lean:87`) = `machTupleKinds?` (none) else `machOuts?` → ALSO
  `out_0`/`out_1`. The S-STRUCT worker's side note ("callee reads a tuple result as one packed `out`, so
  `StructRes` fails") conflated the two types: for a pair OF Signals both sides are `out_0`/`out_1`; for a Signal
  OF a pair the parent's `machInstanceS` refuses (`machOuts?` on `Signal …` → `senv.fields Signal` = none).
* Why the pair arm is not reached: `machProjIota` resolves projections through `senv.proj = userProjection?`,
  which admits only user-module, non-class projections (`inlUserModule`) — `Prod.fst`/`Prod.snd` are not, so
  `k.1` of a call is not read as a field input and the parent is refused (legacy inlines the callee). Whether
  some other parent form reaches `machInstanceS` with a `Prod` result is NOT settled by this probe.

## Interface obligation

Matching-output-width alone (`ChildLinkStruct`, `KidOutsOk`) is vacuous when no output carries the field name.
The real closing does check existence and uniqueness at run time (`instStmtG`, MachineInstG.lean 37–38:
`fields.all (fun f => mc.outputs.any (·.name == f))`, `fields.Nodup`, output names Nodup), so a missing port
makes `closeInstsG` return none (machine route refused), never an unconnected port. The proof-side strengthening
(existence + uniqueness of the selected output from the derived layout) is a worker task (O-EXIST).

No fix staged: nothing reproducible to fix. `StructResAt` remains an open obligation; structure coverage is not
complete.

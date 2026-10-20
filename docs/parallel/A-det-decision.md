# Closing `mixDeep`: three ways on, for a decision

Round par/a-40, base poc `e6f68394`. **WRITTEN, NOT BUILT**; nothing here was
compiled or run by its author. This is a note for the reviewer. No option is
implemented; the only code of this round is a MEASUREMENT for option 2
(`Tools/ShippingNoRepeat.lean`, `Tests/Compiler/NoRepeatFamilyTest.lean`).

## The open statement

`mixDeep.machine_design_noPortsNR2` carries the premise
`MachineClosesAt mixDeep`: at EVERY invariant world of positive depth the
machine synthesis of `mixDeep` returns a module. `mixDeep` reaches `midH`
(and `rcH`) twice, through `mid2` and directly, so its closing compares
same-named modules found in the world's child cache.

BUILT so far:

* `mixDeep.closes_shared : MachineClosesAtS …` — the closing, RELATIVE to
  the cache agreeing on the callees' modules;
* `mixDeep_closes_outermost` — the closing for a core run that STARTS at
  depth 0, from the reflections of the five declarations only (the cache is
  cleared, every entry is then written by this run: provenance);
* `machineClosesAt_of_det` — `MachineClosesAt` at all worlds from
  `MachineClosesAtS`, `DetN` (two real compiles of one declaration return
  the same module) for `mid2`, `midH`, `rcH`, `cnt`, and a provenance fact
  about the callees' designs (`hreal`, not instantiated).

`DetN` is the missing fact. It is FALSE in general (finding I: the legacy
route, a constructed state; fix proposal on `fix/singleout-nested`). For the
certified route it is neither proved nor refuted; one dependency is not
controlled by the present laws: what a READ of the run-local translation
cache returns (`docs/parallel/A-determinism.md`, item B).

## Option 1 — a value law for run-local translation caches

**What would be added** (as an extension structure, the way `RefLawsM`
extends `RefLaws` for the memo, `Tools/ShippingMemoLaws.lean` 88; `RefLaws`
itself unchanged):

| field | says |
|---|---|
| `xval : IO.Ref (ExprStructMap String) → World → ExprStructMap String` | the map of each such ref in each world |
| `xlive : IO.Ref (ExprStructMap String) → World → Prop` | the ref has been allocated |
| `exprNew` | after a successful `IO.mkRef v` returning `r`: `xval r w' = v`, `r` was not live and is now, every other ref's `xval` and liveness are unchanged |
| `exprGet` | a successful `r.get` returns `xval r w` and leaves every `xval` |
| `exprModify`, `exprSet` | after `r.modify f` / `r.set v` the map of `r` is `f (xval r w)` / `v`; the other refs' maps are unchanged |
| `exprFrame` | every OTHER operation the laws already list (`Framed`, `Diag`, the cache / synthesis-ref / depth operations) leaves every `xval` and keeps liveness |

`xlive` is not decoration: a nested compile allocates its own cache while
the parent's is in use, and "the child's writes do not change the parent's
map" needs the two refs to be different, i.e. freshness of `mkRef`.

**Why it is ordinary ref semantics.** These are the laws of `ST.Ref`: a new
reference holds its initial value and is distinct from the existing ones; a
read returns the content; a write changes that reference only. Nothing in
them mentions the compiler. The present `RefLaws` already assumes the same
for three NAMED refs (`val`, `sval`, `dval` with get / set / modify and the
frame); the memo extension did it for a fourth.

**What changes.**

* A new structure `RefLawsX extends RefLaws` and a boundary `ChildBndX`
  (the pattern of `ChildBndM`, `Tools/ShippingMemoLaws.lean` 259). For an
  ENDPOINT to lose `MachineClosesAt mixDeep`, its boundary premise becomes
  `ChildBndX` instead of `ChildBnd`: a STRONGER allowed premise on that
  endpoint. That is an extension of the trusted boundary and needs a ruling;
  the law audit and `docs/ShippingCompiler-TrustBase.md` get one more item.
* Then the proof of `DetN` itself, which the law does not give for free: a
  RELATIONAL walk — two runs of one term, two lists of fresh variable ids,
  two cache refs; states related by "same module, design, counter, used
  names; records and cache maps equal up to the renaming of the ids". One
  arm per constructor of the fragment, then the harness shell and the entry.
  Size: about `Tools/ShippingWalkStill.lean` plus
  `Tools/ShippingHarnessStill.lean` again, with a two-run logic in place of
  `WHo`. Then `hreal`, then the `_closed` endpoint.

**Covers**: the whole certified fragment, any nesting, every invariant
world. **Does not cover**: legacy-route descendants (finding I and the
legacy memo), which stay outside.

## Option 2 — a side condition instead of a law

If no non-variable subterm of the walked term occurs twice, every validated
lookup misses whatever the ref holds (a hit is honoured only if the
builder's own record names the wire for an equal expression, and the record
gets an expression only when it was lowered). Then the walk needs no law
about the cache. The side condition is a `Bool` on the term: `noRepeat`
(`Tools/ShippingNoRepeat.lean`).

**The measurement** (`Tests/Compiler/NoRepeatFamilyTest.lean`; kernel
`decide`, logged by a command that tries both polarities). PREDICTED by
reading the sources and `machineShape?` — the integrator's build gives the
observed values:

| declaration | `noRepeat` | `noRepeatNonLit` |
|---|---|---|
| `rcH` | true | true |
| `cnt` | true | true |
| `midH` | true | true |
| `mid2` | **false** | true |
| `mixDeep` | true | true |

`mid2` packs TWO Bool fields — its call's argument `en` and its result
`hit` — and each Bool is packed as `mux b 1#1 0#1` (`machBoolBits`, Elab
4280): the literals `1#1` and `0#1` occur twice. A repeated literal is a
real case of the dependency, not an artefact of the predicate: the second
`Signal.pure 1#1` is looked up (`translateCoreShape`), and in the real run
it HITS (one wire, shared).

**So, if the prediction holds, option 2 does not cover the family**:
`DetN mid2` is one of the four facts `machineClosesAt_of_det` needs. More
generally any machine with two Bool fields (a Bool argument and a Bool
result, two Bool results, two Bool slots) fails `noRepeat`; so does any body
using one literal twice. The condition is too narrow to be the route.

**Cost if it were taken anyway**: the same relational walk as option 1
(minus the cache component of the relation), plus the record's invariant
("its values are the quotations of the subterms already lowered") and
"equal quotations have equal keys" — neither proved.

A variant "inputs and literals may repeat" (`noRepeatNonLit`, predicted true
for all five) does NOT remove the dependency: literals are looked up.

## Option 3 — the endpoint at OUTERMOST starts

A real synthesis always starts at depth 0 (a command), and the entry clears
the child cache there. `mixDeep_closes_outermost` is the closing for exactly
those runs, with no premise beyond the reflections.

**What would be written**: a NEW, separately named design-level endpoint
for `mixDeep` (not a change of `machine_design_noPortsNR2`, and not "the
endpoint losing a premise"): start condition "the synthesis ref is set, the
world is quiet, the depth is 0" in place of `ChildBnd`'s "depth 0 or an
invariant cache", and no `MachineClosesAt` premise.

**Which consumers need restating.** `MachineClosesAt` enters the design
level as a hypothesis `closes` of the port / design lemmas
(`Tools/ShippingCallsChildPorts.lean` 171, 354;
`Tools/ShippingCallsPortsG.lean` 86, 284) and of the generated endpoints
built on them. They use it at ONE world — the world of the run in hand — to
know that the machine synthesis of that run returned `some`. Each needs a
sibling taking that fact for the run in hand (a run-indexed hypothesis:
"this run's machine synthesis returned a module") instead of the all-worlds
statement; the bodies should carry over, since they only ever instantiate
`closes` at the run. I have read the statements, NOT the proofs line by
line: the count of lemmas between `closes` and the endpoint is not
established.

**Scope, plainly**:

* narrower start: runs from depth 0 only. A run of `mixDeep`'s entry that
  starts NESTED in an arbitrary invariant world is not covered — that is the
  case only the all-worlds statement speaks about, and no real command
  produces it;
* `mixDeep` as a CHILD of a larger top is still reachable by the same
  technique, anchored at the top's depth-0 start: the provenance invariant
  is preserved through nested entries (`EntryOk` per callee, BUILT for
  `cnt`, `midH`, `mid2`); the parent's endpoint would need `EntryOk mixDeep`
  (not written) — not `MachineClosesAt mixDeep`;
* no change of the trusted boundary; no new law; no relational walk.

## Recommendation

**Option 3 now; option 1 only if a statement about arbitrary nested starts
is wanted for its own sake; not option 2.**

1. Option 2 is ruled out by the measurement if `mid2` comes out `false` (and
   it is fragile even where it holds: one repeated literal breaks it).
2. Option 3 closes `mixDeep` for every run a command can start, from
   reflections only, with what is already BUILT plus restated consumers. It
   must be reported as what it is: a new endpoint at outermost starts, the
   existing endpoint and its premise unchanged, `MachineClosesAt mixDeep`
   at nested starts still open.
3. Option 1 buys the all-worlds statement at the price of a larger trusted
   boundary AND the largest proof of the three (the relational walk). What
   it adds over option 3 is coverage of starts that no real compile has. I
   would take it only after a ruling that the all-worlds form is required.

If option 1 is chosen, the first deliverable should be the law's statement
alone (the structure, the boundary, the audit entry), reviewed before any
proof is built on it.

## Build queue for the measurement (integrator)

`lakefile.lean` (not edited):

    lean_lib «Tools.ShippingNoRepeat» where
      roots := #[`Tools.ShippingNoRepeat]

`Tests/AllTests.lean`: nothing. Order: `Tools.ShippingNoRepeat` (imports
`Tools.ShippingUnifiedSource` only; three kernel-decided sanity examples on
closed terms), then `Tests.Compiler.NoRepeatFamilyTest` alone (imports
`Tests.Compiler.MixDeepOutermostTest`); read the `NOREPEAT` lines (standard
error and the message log). Most likely not to elaborate: `Key.beq` (a
two-argument match over 21 constructors; it must stay structural for the
kernel to reduce it), the `#norepeat_log` command (it elaborates an
`example` in a saved-and-restored command state). The test file lists the
explicit `example` pairs to fall back on.

## What I am unsure of

* The `noRepeat` predictions (read, not run), `mid2` in particular: they
  rest on the argument of the call being packed as a Bool `let` field.
* Option 3's cost: the consumers' proofs were not read line by line.
* Option 1's field list is a sketch; whether `exprSet` is needed depends on
  whether a rollback (`restoreWireCaches`) can occur on the certified route
  (by reading: only on the legacy route).

## Integrator's build record (2026-10-13) — MEASURED

BUILT on tree `aaa63f61376cc55fac5e9df18384a52b23239d80` (poc 0a0a4f71 + these files), cgrun 3 GiB swap 0, run `a40` (exit 0, peak 0.84 GB),
worker's files unchanged, first attempt. `NoRepeatFamilyTest` (target-only, kernel-decided), as predicted:
`noRepeat`: rcH true, cnt true, midH true, **mid2 false**, mixDeep true; `noRepeatNonLit` true for all
five; both sanity lines as expected.
So OPTION 2 does not cover the family (`DetN mid2` is one of the four facts the reduction needs).
Remaining for the reviewer: option 1 (value law for the run-local translation cache — extends the trusted
boundary, plus a relational two-run walk) or option 3 (a NEW endpoint form at outermost starts on the
built `mixDeep_closes_outermost`; existing endpoint and premise unchanged; nested starts stay open).
No option is implemented. `mixDeep` stays OPEN.

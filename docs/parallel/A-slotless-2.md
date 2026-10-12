# A / G1, unit U5a, second round: `twinCalls`, `mesh2x2` by hand, and the generator `#machine_no_ports_seq` (round par/a-21, base poc `23a6f28c`)

Status of everything below: **WRITTEN, NOT BUILT**. Nothing was run (no
`lean`, no `lake`); no premise counts as removed until the integrator
builds. "READ" = read in the source; "MEASURED" = in a built log
(`docs/parallel/verification-a20.md`); "INFERRED" = concluded from what was
read, not measured.

## 1. Files (all NEW; no existing file edited)

    Tools/ShippingNoPortsSlotlessCommand.lean            #machine_no_ports_seq, #machine_no_ports_seq_try
    Tests/Compiler/NoPortsSlotlessLib.lean               logData, audit (shared meta code; imports the engineOnce test)
    Tests/Compiler/NoPortsSlotlessTwinCallsTest.lean     hand instance, twinCalls
    Tests/Compiler/NoPortsSlotlessMesh2x2Test.lean       hand instance, mesh2x2
    Tests/Compiler/NoPortsSlotlessSeqFamilyTest.lean     the generator: compare on engineOnce and parent, generation of twinCalls / mesh2x2, refusals — TARGET-BUILT ONLY

No new general theorem: the hand tests and the generator apply the BUILT
`kids_runFactsS`, `kids_designCheckS`, `seqKid_of_leafAt`,
`kids_outsCheck`, `kids_maskedN`, `leafKid_facts`,
`machine_design_noPorts`.

## 2. Per declaration: endpoint — premise — predicted state

| declaration | endpoint | premise | predicted state |
|---|---|---|---|
| `twinCalls` | `twinCalls.machine_design_svNR1` (NEW base, built command; MEASURED to go through) | `shipsHierCheck`, `kidsMaskedN`, `designCheck 1`, `outsCheck 1`, `MachineClosesAt twinCalls`, boundary `ChildBnd ∧ MachineDefines pe` | all present (the inventory the audit asserts) |
| | `twinCalls.machine_design_noPortsNR1` | the four checks | ABSENT; `MachineClosesAt twinCalls` still a binder |
| | `twinCalls.machine_design_noPortsNR1_closed` | `MachineClosesAt twinCalls` | ABSENT (by `twinCalls.machine_closes_at`, built generator). Left: the run, `MachineDefines twinCalls`, `MachineDefines pe`, `ChildBnd ∧ MachineDefines pe` under the existentials — all ALLOWED; gap theorem with no gap hypothesis |
| `mesh2x2` | `mesh2x2.machine_design_svNR1` (NEW base; MEASURED to go through) | the same six | all present |
| | `mesh2x2.machine_design_noPortsNR1` | the four checks | ABSENT |
| | `mesh2x2.machine_design_noPortsNR1_closed` | `MachineClosesAt mesh2x2` | ABSENT; the same four premises left, with `mesh2x2`; no gap hypothesis |
| `engineOnce` | `engineOnce.machine_design_noPortsNR1(_closed)` (BUILT, hand) | — | nothing removed: REBUILT by the generator, `isDefEq`, kept as `…_regen` (family test) |
| `parent` | `parent.machine_design_noPortsNR1(_closed)` (BUILT, `#machine_no_ports`) | — | nothing removed: REBUILT by the generator through `SeqKid`, `isDefEq`, kept as `…_regen` (family test) |

Relative to what: `twinCalls` and `mesh2x2` had no design-level endpoint;
the closed forms are NEW statements. Against the base endpoint generated in
the same file the four checks and the closing premise are gone and nothing
is added.

## 3. The hand tests

Both are `NoPortsSlotlessEngineOnceTest.lean` (BUILT) at the declaration's
data, step for step: `nDecl := 4` (`twinCalls`), `nDecl := 7` (`mesh2x2`);
theorems `tw_*` / `mesh_*` for `engine_*`. Differences:

* `pe.machine_leafKid` (and `pe.machine_closes`, `pe.seq_child_runN`) are
  IMPORTED from the engineOnce test, asserted present in step 1, never
  recreated.
* The data log and the audit are the functions of `NoPortsSlotlessLib`.
* `mesh2x2`'s decided statements and run theorems are under
  `maxHeartbeats 0` (the base commands were measured under it); plain
  `by decide` as in the built generators.
* Per-entry facts through ONE decided ∀-statement: `mesh_entry :
  ∀ k hk, (insts[k]).1 = pe := by decide`, independent of the entry count;
  the tables `kidOuts`, `kidIns` are constant functions. No case split over
  the entries.

## 4. Hypotheses that read the argument `let`s

| hypothesis | where | depends on DISTINCT argument lets? |
|---|---|---|
| `callArgsOk d nDecl (fun _ => declWidths pe)` | `kids_designCheckS` (hand: `tw_callArgs`, `mesh_callArgs`) | NO — reads each entry's argument lets, their widths only; true whether or not entries share arguments |
| `callWidthsOk d nDecl (fun _ => pe outs)` | `kids_runFactsS`, `kids_designCheckS` | NO — fields and output binders only |
| `callsOk nDecl` (`a < ls.length` per argument) | all four | NO — bounds only |
| `SeqKid` | `kids_runFactsS`, `kids_designCheckS` | NO — entry 0 alone |
| **`hfieldsNd`** of `machineClosesAt_of_seqKids` | inside `f.machine_closes_at` (built generator, `by decide`) | **YES** |

`hfieldsNd` (READ, `Tools/ShippingCallsSeqKids.lean:70`):

    ∀ k hk k' hk', (insts[k]).1 = (insts[k']).1 → (insts[k]).2.1 = (insts[k']).2.1 →
      instFields.getD k "" = instFields.getD k' "" → k = k'

Evaluation:

* `twinCalls` — INFERRED (source, and MEASURED `lets = 3`: the three
  argument lets are shared by the two calls): entries `(pe, args, aOut)`,
  `(pe, args, pOut)`. The argument clause does NOT separate them; the
  hypothesis holds by the FIELD clause. It does not depend on distinct
  arguments here. (A variant reading the same field of both calls,
  `e1.aOut + e2.aOut`, would be one instance and one field: true only if
  the reader makes ONE entry of it — not examined, no such declaration.)
* `mesh2x2` — INFERRED from the source: the callee is always `pe` and
  several entries read the same field of different instances (`pOut` of
  `pe00`, `pe01`, `pe11`; `aOut` of `pe00`, `pe10`, and `pe11` if the dead
  `let _` is read). Those are told apart by the argument lets ONLY; the
  hypothesis is true because the four calls have four different argument
  lists (they differ already in the weight input). TRUE on the data:
  MEASURED — `#machine_closes_at mesh2x2` went through at 23a6f28c (the
  kernel decided it).
* The entry tables themselves were NOT in the built log excerpt (the
  `NOPORTS SLOTLESS DATA` lines are cut after the first callee). The new
  tests log one `… ENTRY f [k]: callee, argument lets, field` line per
  entry and a `… FIELDSND` line with the entry pairs separated by the field
  only / by the arguments only / by neither; and they restate `hfieldsNd`
  verbatim and decide it (`tw_fieldsNd`, `mesh_fieldsNd`; not used by a
  proof). Read those lines after the build; this section's INFERRED rows
  are to be replaced by them.

## 5. The generator

`Tools/ShippingNoPortsSlotlessCommand.lean`:

    #machine_no_ports_seq f n
    #machine_no_ports_seq_try f n        -- a refusal LOGGED (NOPORTS SEQ REFUSED), nothing kept

For a parent under the general closing, WITH OR WITHOUT a register, whose
every distinct callee is a leaf register machine with `k.machine_closes`.
`hck : slots ≠ [] ∨ SeqKid` is ALWAYS discharged by the second disjunct
(every callee in scope is sequential) — no generated proof reads the
parent's slots.

New generated statements:

    f.machine_seqKidS {mctx mref cctx cref} (hR0 : MachineDefines mctx mref cctx cref k₀ k₀.machineData.shape) … :
      Tools.ShippingSlotlessClk.SeqKid mref cref f.machineData
    f.machine_runFactsK{n}   -- statement of the built runTheorems; proof kids_runFactsS … (Or.inr (f.machine_seqKidS …)) …
    f.machine_designPK{n}    -- statement of the built runTheorems; proof kids_designCheckS … (Or.inr (f.machine_seqKidS …)) …

Reuse by import (`Tools.ShippingNoPortsKidsCommand`, BUILT): `Ctx` (all
kinds `.leaf`, no gate), `kidsTheorem` (`f.machine_kidsK{n}`),
`runTheorems` — it generates each of its four theorems only if absent, so
the two above are generated first under ITS names and it adds
`f.machine_outsGK{n}`, `f.machine_maskedGK{n}` —, `endpointTerm`,
`closedTerm`, `addOrCompare` (compare path: existing ⇒ rebuilt, `isDefEq`,
kept as `…_regen`, an error otherwise; never a silent return);
`Tools.ShippingNoPortsCommand.leafKidTheorem`. If `…_runFactsK{n}` /
`…_designPK{n}` exist BEFORE the command, they are kept and the log line
says `EXISTING` for each (the family test then THROWS: it checks that the
proof terms apply the `S` theorems).

Refusal lines (`scopeS`, in this order): no machine endpoint; no call; a
MEMORY child; a parent without a register whose callees are ALL
combinational — "NOT COVERED … needs a head change"; one-output closing; a
callee without a machine endpoint; a callee with calls of its own; a callee
without a register; a leaf callee without `machine_closes`; no
`f.machine_ships_hierNR{n}`.

NOT EXERCISED by a test: the all-combinational refusal (no declaration of
that shape is known); the several-distinct-callees branch of
`seqKidTheorem` (`∀ k hk, k = 0 → (insts[k]).1 = k₀` by `decide`) — all
four test declarations have ONE callee.

## 6. Build queue (integrator)

`lakefile.lean`:

```
lean_lib «Tools.ShippingNoPortsSlotlessCommand» where
  roots := #[`Tools.ShippingNoPortsSlotlessCommand]
```

`Tests/AllTests.lean`:

```
import Tests.Compiler.NoPortsSlotlessTwinCallsTest
import Tests.Compiler.NoPortsSlotlessMesh2x2Test
```

NOT in `Tests.AllTests`: `Tests.Compiler.NoPortsSlotlessSeqFamilyTest`
(target-built only).

Order: `Tools.ShippingNoPortsSlotlessCommand` →
`Tests.Compiler.NoPortsSlotlessLib` →
`Tests.Compiler.NoPortsSlotlessTwinCallsTest` →
`Tests.Compiler.NoPortsSlotlessMesh2x2Test` →
`Tests.Compiler.NoPortsSlotlessSeqFamilyTest` (target) → `Tests.AllTests`.

Name clashes:

* the family test and the two hand tests create the same `twinCalls.*` /
  `mesh2x2.*` constants (`machine_ships_hierNR1`, `machine_design_svNR1`,
  `machine_closes_at`, `machine_design_noPortsNR1(_closed)(_gap)` and what
  `#machine_design_svNR` leaves besides) — never import them together; the
  family test's step 1 throws if the hand tests are in its imports;
* the family test creates `engineOnce.*` and `parent.*`:
  `machine_kidsK1`, `machine_seqKidS`, `machine_runFactsK1`,
  `machine_designPK1`, `machine_outsGK1`, `machine_maskedGK1`,
  `machine_design_noPortsNR1_regen`, `…_closed_regen`.
  `Tests/Compiler/NoPortsKidsFamilyTest.lean` (target-only) creates the
  `parent.*` ones too (`_try`, kept on success): never import the two
  family tests together;
* the two hand tests are compatible with each other and with the engineOnce
  test (distinct declarations; `pe.*` imported).

## 7. UNVERIFIED, in risk order

1. `mesh2x2`'s `by decide`s in the hand theorems (`callsOk 7`, the domain
   binders, `callWidthsOk`, `callArgsOk`, `mesh_fieldsNd` — a double
   bounded quantifier over the entries with `Name` / `List Nat` / `String`
   equalities). The same conditions were decided by the built base commands
   on this declaration, but in other terms; `maxRecDepth` is the default in
   the hand file.
2. `seqKidTheorem`: `have he : (insts[0]'h0).1 = k₀ := (by decide : ∀ k hk,
   (insts[k]).1 = k₀) 0 h0`, then `rw [he]` under `refine seqKid_of_leafAt
   … ?_` (the hand form is `rw [engine_entry 0 h0]`, BUILT; the generated
   form with the explicit `'h0` is new). Macro hygiene across the two
   quotations (`h0` is named in both).
3. The reuse of `runTheorems` by pre-seeding two of its names: the
   statements written here must be accepted where `endpointTerm` applies
   them (`mkAppM facts #[hcore, hpost, entry, closes]`, then the boundary's
   conjuncts) — the binders are copied from `runTheorems`.
4. Compare path on `parent`: `closedTerm` takes `parent.closes_deep` if it
   exists in the family test's imports, else `machine_closes_at`; the built
   kids family test rebuilt `parent`'s closed form `isDefEq` in a larger
   import set (`verification-a14b.md`), not in this one.
5. `NoPortsSlotlessLib.logData`: the row type `Nat × Name × List Nat ×
   String` (READ: `insts : List (Name × List Nat × MixedGateBinder)`), the
   `Prop`-to-`Bool` coercion of `a.1 < b.1 && …`.
6. The family test's proof-term check (`ti.value.find? (·.isConstOf
   kids_runFactsS)`): assumes the application is not hidden in an auxiliary
   declaration.
7. `scopeS` on `seqMem` / `grand` / `pe`: the refusal lines expected are
   "memory child" / "calls of its own" / "no call"; another earlier line
   would still be a logged refusal (the audit only checks that nothing was
   left).

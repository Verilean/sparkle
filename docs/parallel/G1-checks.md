# G1 — the output checks: inventory and first derivations

Worker A, branch `par/g1-checks` (base `a9b3a6b1`). Audit reference:
`docs/ShippingCompiler-GeneralTheorem-Audit.md` §2, §7 (G1).

**Status: UNVERIFIED.** No Lean process was run. Definitions below were read
in the sources; "derivable" means "I see the proof from the cited facts",
not "proved", unless a theorem name of `Tools/ShippingChecksDerived.lean` is
given (and that file is itself unbuilt).

## 0. Findings first

1. **A machine without calls never passes the instance-route bundles.**
   `shipsHierCheck` and `shipsHierHCheck` start with `hierBinds b`, and
   `hierBinds b = hierGate b && …` where `hierGate` asks `b.body.any isInst`.
   On a body of assignments and registers both bundles are `false`
   (`shipsHierCheck_false_of_seqOk`, `shipsHierHCheck_false_of_seqOk`;
   `leaf_run_noHier` for every run). So "the leaf case of `shipsHierHCheck`"
   does not exist: `ships_design_svN_all` / `ships_design_svH_all` are heads
   for modules WITH instances only. A machine without calls ships through
   `machine_ships_wired` (registers) or the combinational head.
2. **The leaf head's structural gates are already derived**
   (`Tools.ShippingMachineShipsW.machine_ships_wired`, from `MachineWired`):
   the cleanup is the identity on the body / widths / ports, `rst` is an
   input, the layout's outputs are the module's, the core body is
   assignments and registers with a register, the merge is a checked
   refinement or the identity. What it still asks, per declaration:
   * `simpleBody b = false` — **NOT derivable from the listed facts**: `b`
     may be `mergeChecked r0` kept under `refineCheck r0 b`, and
     `refineCheck` allows the output to have FEWER registers than the input
     ("every register of `m` has a next value (the dropped ones too)"); the
     merge itself (`mergeDuplicatesParts`, an `Id.run` loop over `HashMap`s)
     has no theorem. Missing run fact: "the merge of a body with a register
     keeps a register statement". (Alternative that needs no such fact:
     extend the head to the `simpleBody b = true` branch of
     `checkedOptimize`.)
   * `seqCheck wof (weOf wof) (checkedOptimize b).body` and the width
     agreement on `seqNames` — the emitted-text check. **Neither derived nor
     run by the compiler**: `seqCheck` lives in `Tools/SVParser/EmitSem.lean`
     and constrains the optimizer's output expression by expression
     (`sf4Check`). Either the printer path runs it (then "the run succeeded"
     gives it), or it needs a theorem about `optimizeModule`'s output forms.
3. **Every conjunct that inspects only instance statements is free on a
   module without instances**, and the checked optimizer keeps "no instance"
   (`checkedOptimize_seqOk_all`: its output is kept only under `optCheck` /
   `refineCheck`, both of which check the output's statement kinds). This is
   what `Tools/ShippingChecksDerived.lean` proves and instantiates on a run.

## 1. The checks, conjunct by conjunct

`b` = the full entry's module (`dropZeroWidthModule raw` or its checked
merge), `o = checkedOptimize b` = what is printed, `C = childMap D.modules`.

Legend — **F**: follows from the run facts listed in the task
(`closedBody_kinds_of_run`, `MachineWired`, `seqChild_iface`,
`kidsChild_iface`, `closeInstsG_some`, `closeInstsG_of_facts`);
**K**: a check the compiler itself runs gives it (named);
**V**: vacuous without instances (proved in `ShippingChecksDerived`);
**G**: gap — neither.

### `outsCheck C n o` (asked by `ships_design_svN_all`, `ships_design_svH_all` at `n = 0`)

    outsCheck C 0 o     = kidsPass C outsLeaf o.body
    outsCheck C (n+1) o = kidsPass C (fun c => outsAssigned c && outsCheck C n c) o.body

| Conjunct (per instance statement of `o.body`) | Status |
|---|---|
| the instance's module resolves in `C` | **F** for `b.body` (`MachineWired`: `moduleByName dsn.modules mn = some mc`); for `o.body` it needs "the optimizer keeps the instance statements" — **K**: `hierRefineCheck b o'` (run inside `checkedOptimize`; its comment says "the same instance statements"), no lemma located |
| the child's outputs are assigned (`outsLeaf` / `outsAssigned`) | **G** as a run fact: `closeMachine` ends its body with `outAssigns w lay.outs` (one assignment per output — pure, provable), the cleanup keeps the body (**F**), but the child's checked merge may rewrite it; under `refineCheck r0 b` every output has a normal form in `b` (`dO.lookup p.name = some _`), which should give an assignment — a lemma about `rNormBody` is missing |
| `outsCheck C n child` for a child without calls | **V** — `outsCheck_of_seqOk`; on every run of such a child `leaf_run_outsCheck` |
| whole check, module without instances | **V** — `outsCheck_of_seqOk` |
| whole check at depth 0, from per-instance facts | `outsCheck0_of_insts` (reduction, proved) |

### `designCheck C n o` (same heads)

    designCheck C 0 o     = textCheckI C o && kidsPass C leafCheck o.body
    designCheck C (n+1) o = textCheckI C o && kidsPass C (designCheck C n) o.body
    textCheckI C o = o.body.all seqStmtOkI
      && seqCheck (wofOf o) (weS o) o.body
      && (seqNames o.body).all (fun x => declWidth o x == weS o x)
      && linkedWF C o.body && decide (instNames o.body).Nodup
      && noSelfRead C o.body && portsMatchB C o
      && o.body.all (inst ⇒ (C mn).isSome)

| Conjunct | Status |
|---|---|
| `o.body.all seqStmtOkI` | **K** when `b.body` is assignments / registers / instances: `checkedOptimize` keeps its output only under `refineCheck` / `hierRefineCheck`; without instances `checkedOptimize_seqOk_all` + `seqStmtOkI_of_ok` |
| `seqCheck (wofOf o) (weS o) o.body` | **G** — emitted-text check, not run by the compiler, no theorem about optimizer output forms |
| `declWidth o x == weS o x` on `seqNames` | **G** — width tables of the printed module; the raw module's widths are in `MachineWired` (`weOf`), nothing carries them through the optimizer |
| `linkedWF C o.body` | for `b`: **F** (`MachineWired.linkedOk`, `linkedOk_eq`); for `o`: `hierCheck` asks it again (`wfO`) — **G** unless `hierRefineCheck` implies it (not inspected) |
| `(instNames o.body).Nodup` | for `b`: **F** (`MachineWired`: instance names distinct, with `instFields`); for `o`: **K** if the optimizer keeps instance statements |
| `noSelfRead C o.body` | **F** for `b` (`noSelfFeed` in `MachineWired`, with `instFields`); **V** without instances (`noSelfRead_of_seqOk`) |
| `portsMatchB C o` | **G** — instance connection widths vs child port widths in the PRINTED tables; `closeInstsG_of_facts` gives the port names, not `weS` |
| instances resolve | **F** for `b`, as above |
| `kidsPass C leafCheck o.body` | per child: `leafCheck` = statement kinds (**F** for a child without calls), `memOpsRefs` (**V** without memories), width agreement and `seqCheck` / `seqCheckM` of the CHILD's module (**G**, same as above) |

### `shipsHierCheck C b` / `shipsHierHCheck ms b` (instance heads; `machine_ships_hierC`, `machine_ships_hierHC`)

    hierCheck C b = hierBinds b && linkedWF C o.body
      && decide (instNames b.body).Nodup && decide (instNames o.body).Nodup
      && noSelfRead C o.body && outsExtracted C b && "rst" ∈ b.inputs
    shipsHierCheck C b   = hierCheck C b && instOutWidthsOk C (declWidth b) b.body
    shipsHierHCheck ms b = hierCheck (childMap ms) b && kidsLocal ms o.body && hierTyped (childMap ms) b

| Conjunct | Status |
|---|---|
| `hierBinds b` = `hierGate b && refineCheck flat flat` | `hierGate`: **F** (a call ⇒ an instance statement, `MachineWired`; kinds from `closedBody_kinds_of_run` + instance statements). `refineCheck flat flat` (normal forms of the extracted interface): **K** only in the sense that `checkedOptimize` tests `hierBinds m` itself — but it tests it to CHOOSE a branch, a `false` does not fail the compile. So: **G** (it is the domain condition of the checked hierarchy route; a module where it is `false` is shipped unchecked — G2-like) |
| `linkedWF C o.body`, `(instNames o.body).Nodup`, `noSelfRead C o.body` | as in `designCheck` |
| `(instNames b.body).Nodup` | **F** (`MachineWired`) |
| `outsExtracted C b` | **G** — relates instance output wires to `HierCheck.openIns b`; not among the facts (definition of `openIns` not inspected) |
| `"rst" ∈ b.inputs` | **F** with slots or sequential children (`MachineWired`: `extra` ports / `slots ≠ [] → "rst" ∈ …`); FALSE for a slotless parent of combinational children — then the H head must not ask it (not inspected) |
| `instOutWidthsOk C (declWidth b) b.body` | **G** — declared width of each instance output wire = child port width; `closeInstsG_of_facts` has the wires and ports, the width equation is not stated there |
| `kidsLocal ms o.body` | per child: no memory, reads closed, outputs written, outputs not inputs — **F** for gate children (`gate_child_comb`, `kidsCombB` which the compiler RUNS in `closeInsts`: **K**) on `b.body`; on `o.body` needs the optimizer to keep instances |
| `hierTyped (childMap ms) b` | **G** (not inspected beyond its definition: `kidsTyped … && openIns` vs outputs) |
| whole bundle, module without instances | `false` — finding 1 |

### The kids checks (`kidsMixed`, `kidsMem`, `kidsMaskedN`, `kidsComb`)

All are `body.all (fun st => match st with | .inst … => <about the child> | _ => true)`.

| Check | Without instances | With instances |
|---|---|---|
| `kidsComb ms o.body` | **V** `kidsComb_of_seqOk` | the five conjuncts of `kidsCombB`, which `closeInsts` RUNS on `b`'s instances (**K**) — on `o.body` again modulo "the optimizer keeps instances" |
| `kidsMem C body` | **V** `kidsMem_of_seqOk` | child is the built memory module: **F** (`MachineWired`, memory calls: `mc = md.1`), `out_rdata` not connected: from `CallStmtG` (not assembled) |
| `kidsMasked` / `kidsMixed C body` | **V** `kidsMixed_of_seqOk` | `outMasked` of each child output: **G** (a property of the child's body expressions) |
| `kidsMaskedN ms body` | **V** `kidsMaskedN_of_seqOk` | `outsMaskedN child`: **G**, same |

### The leaf head (`machine_ships_wired`) — see §0.2

`simpleBody b = false`: **G**. `seqCheck …`, widths: **G**. Everything else
it needed: **F**, done there.

## 2. What `Tools/ShippingChecksDerived.lean` contains

Pure: `all_of_seqOk`, `any_false_of_seqOk`; `kidsPass_of_seqOk`,
`outsCheck_of_seqOk`, `kidsMasked_of_seqOk`, `kidsMem_of_seqOk`,
`kidsMixed_of_seqOk`, `kidsMaskedN_of_seqOk`, `kidsComb_of_seqOk`,
`kidsLocal_of_seqOk`, `noSelfRead_of_seqOk`; `checkedOptimize_seqOk_all`;
`hierGate_false_of_seqOk` … `shipsHierHCheck_false_of_seqOk`;
`kidsPass_of_insts`, `outsCheck0_of_insts`.

From a run of the full entry on a machine without calls (premises of
`seqChild_iface`: `d.ok`, the body equation, `insts = []`, the outputs'
types, `InvW`, the run, `MachineDefines`, `MachineCloses`):
`leaf_run_seqOk`, `leaf_run_outsCheck`, `leaf_run_kids`, `leaf_run_noHier`.

## 3. A machine with calls — the statement (not derived)

Target, for a parent with calls whose children have no calls (depth 0):

    outsCheck (childMap D.modules) 0 (checkedOptimize b) = true

`outsCheck0_of_insts` reduces it to: every instance statement of
`(checkedOptimize b).body` resolves in `childMap D.modules` to a child with
`outsLeaf`. The three hypotheses a run would have to supply, in the
`ChildIfaceD` style:

1. (parent, **F**) every instance statement of `b.body` is a call's, and
   its module name resolves to the call's child in the design —
   `MachineWired` conjuncts 5–6 / the `instFields ≠ []` conjuncts;
2. (optimizer, **K**, lemma missing) the instance statements of
   `(checkedOptimize b).body` are those of `b.body` — from
   `hierRefineCheck b (deinline b o)` or `checkedOptimize b = b`;
3. (child, **G**) each child's full-entry module assigns every output —
   to be added to `ChildIfaceG` / `ChildIfaceD` as a field
   `outsA : outsAssigned b = true`; provable for the child's RAW module from
   `closeMachine` (`outAssigns`) and the cleanup; through the checked merge
   it needs "`refineCheck m o` ⇒ every output of `o` is assigned in `o`".

With 1–3 the proof is `outsCheck0_of_insts` and `outsAssigned ⇒ outsLeaf`
(a one-line lemma, not written). At depth `n + 1` the child's own
`outsCheck C n child` is `leaf_run_outsCheck` for a child without calls and
the same statement recursively otherwise.

## 4. Order of work suggested

1. Build `Tools.ShippingChecksDerived` (imports `ShippingSeqChildIface`,
   `ShippingShipsDesignSVAll`, `ShippingHierPremises`,
   `ShippingMachineDepthH`, `ShippingMachineShipsDepth`,
   `ShippingMachineShipsComb`).
2. Hypothesis 2 above: a lemma "`hierRefineCheck m o' = true` ⇒ the instance
   statements of `o'` are `m`'s" (read `Sparkle/IR/RefineCheck.lean`,
   `hierRefineCheck`). It unlocks every "on `o.body`" row at once.
3. `outsAssigned` for the raw closed module and through `refineCheck`.
4. Decide what to do with the emitted-text checks (`seqCheck`, width
   agreement, `portsMatchB`): they are the bulk of G1 and are properties of
   the optimizer's and printer's tables — run them in the compiler, or prove
   them of `optimizeModule`.

## Integrator's build (2026-10-12)

`Tools.ShippingChecksDerived` built through the protected queue with no
change (base `f0f9e654`); `leaf_run_outsCheck`, `leaf_run_kids`,
`leaf_run_noHier` depend on standard axioms only. What this does NOT give is
the list at the top of this note: the emitted-text checks (`seqCheck`,
widths, `portsMatchB`), `simpleBody b = false`, and every check on the
optimized body of a module WITH instances.

## 5. Round 6 (branch `par/g1-checks-2`, base `3a291ec6`) — UNVERIFIED, not built

`Tools/ShippingChecksDerived2.lean`:

* `hierRefineCheck_inst_iff`, `checkedOptimize_inst_iff` (under `hierBinds b`):
  the instance statements of the printed module are the full entry's, AS A
  SET — the exact content of `instsKept` both ways.
* per-instance checks moved to the printed body: `kidsPass_opt`,
  `kidsComb_opt`, `kidsLocal_opt`, `kidsMem_opt`, `kidsMasked_opt`,
  `kidsMixed_opt`, `kidsMaskedN_opt`, `noSelfRead_opt`, `resolved_opt`.
* `refineCheck_outs_assigned` / `outsAssigned_of_refineCheck`,
  `mergeChecked_outsAssigned` (body with a non-assignment),
  `outsLeaf_of_assigned`.
* `outsCheck0_opt`: the depth-0 `outsCheck` of the printed module of a
  machine with calls, from `hierBinds b`, resolution of `b`'s instances in
  the design's modules, and `outsA` per resolved child.

Corrections to §1 after reading `instsKept` and `deinline`:

* `(instNames (checkedOptimize b).body).Nodup` is **G**, not **K**:
  `instsKept` is membership; a duplicated instance statement in the
  optimizer's output passes `hierRefineCheck`. It needs "the optimizer does
  not duplicate instance statements" or a list-level check.
* `linkedWF C (checkedOptimize b).body` (order-sensitive) likewise is not
  given by `hierRefineCheck`.
* the run-level form of `outsCheck0_opt` waits for an export: "every
  instance statement of the full entry's module resolves in the full entry's
  design to a child's module" is proved inside `kidsChild_iface` but is not
  a field of `ChildIfaceD` (which keeps the names only).

`Tools/ShippingNameSep.lean` (edited): `not_mem_map_of`, `disjoint_map_of`,
`nodup_map_of_inj`, `nodup_map_of`, over `L.map (fun n => n.toString)`.

## 6. Round 7 (branch `par/g1-checks-3`) — UNVERIFIED, not built

Build of round 6: `Tools.ShippingChecksDerived2` failed on a guessed
namespace (`outsAssigned` / `outsAssigned_sound` live in
`Tools.ShippingDesignSVBack`, inside `Tools/ShippingDesignSVLeaf.lean`);
everything before those lemmas elaborated. Fixed: the real names, and the
two "assigned ⇒ check" lemmas now unfold the definition and prove the
predicate on `Stmt.assign p.name r` explicitly.

New: `Tools/ShippingChecksDerived3.lean` — `closeMachine_outs_assigned`,
`closeMachine_outsAssigned`, `outsAssigned_congr`, `entry_outsAssigned`
(pure; the run composition needs `packedWire?` of the `closeLets` result,
which no lemma states).

### Proposal (for the user's decision): making `instNames` nodup and `linkedWF` of the printed body derivable

Today `hierRefineCheck m o` = `instsKept m o && instsKept o m && connAgreeOk …
&& (o drives no extracted input) && refineCheck (flat m) (flat o)`.
`instsKept` is: every instance statement of one body occurs in the other.

**(P1) Instance statements as a list.** Add one conjunct

    o.body.filter isInst = m.body.filter isInst

(`isInst` as in `hierGate`). It subsumes both `instsKept` conjuncts. From it:
`instNames o.body = instNames m.body` (`instNames` reads only the instance
statements, in order — a three-line induction), hence
`(instNames (checkedOptimize b).body).Nodup` from `(instNames b.body).Nodup`
(which `MachineWired` gives), and every multiplicity-sensitive fact about
instances. What it rejects that is accepted today: an optimizer output whose
instance statements are a permutation of the input's, or contain a
duplicate. `deinline` emits the instance statements in the order of the
optimizer's output, once each; whether `optimizeModule` ever reorders or
duplicates instance statements is NOT known to me (its definition was not
read) — to be measured by evaluating the new conjunct on the corpus'
instance-bearing modules next to the old check. A rejected output is not a
compile failure: `checkedOptimize` then ships `m` unoptimised (the emitted
text of that module changes, its function does not).

**(P2) `linkedWF` of the printed body.** List equality of the instance
statements does NOT give it: `linkedWF` constrains the ASSIGNMENTS relative
to the instances (an assignment neither targets nor reads an output wire of
a LATER instance; an instance's output wires are never written afterwards;
the wires it reads are not written afterwards), and the optimizer rewrites
and reorders assignments. It also needs the children's output ports
(`instOutWires child.outputs conns`), which `checkedOptimize : Module →
Module` does not see. Two forms, smallest first:

* P2a — a design-free sufficient check inside `hierRefineCheck`: with
  `I := the wires any instance statement connects by a reference`
  (`HierCheck.connRefs`, already defined), ask that `o.body` has the shape
  `linkedWF` needs with `I` in place of the instance outputs: no assignment
  after an instance targets a wire of `I` connected by that instance or an
  earlier one, and no assignment before an instance reads a wire of `I`
  that a later instance connects and nothing assigns. This over-approximates
  (it treats every connected wire as a possible output) and so rejects more
  than P2b; it keeps `checkedOptimize` a function of the module alone. Its
  soundness lemma (`⇒ linkedWF C o.body` for every `C` whose children's
  output wires are among `I`) would have to be proved.
* P2b — check `linkedWF (childMap design.modules) o.body` itself where the
  design is at hand: at the print call (`toVerilog (checkedOptimize m)` per
  module of a design), fall back to `m` when it is false. `m`'s own
  `linkedWF` is a run fact (`MachineWired.linkedOk`), so the fallback always
  passes. This changes the print path's signature, not the optimizer.

In both, what is rejected is an optimizer output, never a source; the cost
is an unoptimised module text in those cases. Which outputs would be
rejected today: unknown without measurement. On a parent whose shipped
endpoint discharges `hierCheck` by `decide` (the audit's description of the
generated endpoints; I did not check which parents these are), `linkedWF …
(checkedOptimize b).body` is true, so P2b rejects nothing there by
definition; P2a might.

Recommendation: P1 (cheap, clearly sound, removes a per-declaration
`decide`), and P2b over P2a (no new soundness lemma, exact).

## Integrator's builds (2026-10-12, rounds 6–7)

`Tools.ShippingChecksDerived2` (after one repair round: a wrong namespace)
and `Tools.ShippingChecksDerived3` built through the protected queue with no
further change. `ChildIfaceD` now exports instance resolution
(`ChildIfaceD.resolves`, integrator). The strengthening proposals P1 / P2 of
§6 are NOT implemented: they change what the compiler's checked optimizer
accepts and are the user's decision.

## 7. Round 8 (branch `par/g1-checks-4`) — UNVERIFIED, not built

* `Tools/ShippingChecksPacked.lean`: `closeLets_packed`, `transition_out`,
  `transition_packed` (the harness's module ends in `assign out = w`, from
  `harness_spine_at` with the instantiation `transition_closed` uses).
* `Tools/ShippingChecksRun.lean`:
  `leaf_run_outsAssigned` / `leaf_real_outsAssigned` (a machine without
  calls and with a register: the full entry's module assigns every output —
  over every run; hypotheses of `seqChild_iface` plus a slot), and
  `parent_run_outsCheck0` (hypotheses of `kidsChild_iface`, the gate
  `hierBinds b`, and `outsA` on the design's modules): the depth-0
  `outsCheck` of the printed module and the resolution of its instances.
* `Tests/Compiler/ChecksDerivedTest.lean`: on every parent with a
  `machineData`, the gate (`hierBinds`), today's bundles, `outsA`, and the
  proposed P1 / P2b checks, one `CHECKS` line each.

What `parent_run_outsCheck0` would replace in an endpoint: the premise
`outsCheck (childMap D.modules) 0 (checkedOptimize b) = true` of
`ships_design_svN_all` (at `n = 0`) and `ships_design_svH_all`, PROVIDED the
heads' `D` is the full entry's design (not checked) — at the price of
`outsA`. The resolution conjunct is the last conjunct of `textCheckI` (inside
`designCheck`, not separately removable while `designCheck` is one Bool).
`hierBinds b` is already a conjunct of the `shipsHierCheck` those heads take,
so it adds no premise there.

Still missing for `outsA` over runs: which module of the design each child
is (an export next to `resolves`: every module of the full entry's design is
a real child's full-entry module or a module of its design).

## 8. Round 9 (branch `par/g1-checks-5`) — UNVERIFIED, not built

* `Tools/ShippingChecksRun.lean` repaired: the "a slot ⇒ a register name"
  step no longer rewrites with the wiring's length fact (which is about
  `d.slotBs`, not `d.ss`); it is `omega` from that fact,
  `d.slotBs.length = d.ss.length` (from `ok`'s first conjunct) and the
  hypothesis `d.ss.length = slots.length`.
* `Tests/Compiler/ChecksDerivedTest.lean` no longer imports the theorems.
* `Tools/ShippingChecksRun2.lean`: `kidsDesign_real` (every module of the
  full entry's design is a real child's module or a module of a real
  child's design), `parent_run_outsCheck0_kids` (`outsA` replaced by one
  fact per real child), `leaf_real_kidA` (that fact for a child without
  calls and with a register).

With these, for a parent whose children are machines without calls and with
a register, the premise `outsCheck (childMap D.modules) 0 (checkedOptimize b)
= true` needs: the parent's and the children's data conditions and
reflections (already premises of the closing), and the gate `hierBinds b`.

## Integrator's builds and run (2026-10-12, rounds 8–9)

`Tools.ShippingChecksPacked`, `Tools.ShippingChecksRun` (after one repair
round) and `Tools.ShippingChecksRun2` built through the protected queue with
no further change. `Tests/Compiler/ChecksDerivedTest.lean` RAN on every
declaration with a `machineData` and calls in the imported test modules:
31 real parents (`CHECKS TOTAL: parents 31, hierBinds true 31, errors 3`; the
3 errors are gate-route declarations, logged by design). On all 31: `hierGate = true`, `hierBinds = true` (the gate
hypothesis of `parent_run_outsCheck0_kids` holds), `outsCheck0 = true`,
`outsA = true`, and the proposals' checks hold — `P1 = true` (the optimized
body has the module's instance statements as a LIST), `instNamesNodup = true`,
`P2b = true` (`linkedWF` of the printed body). So P1 / P2b would reject none
of these outputs. `kept = false` on all (the optimizer changes every body).
`shipsHierHCheck` is true only for the one-output combinational parents.
This is a measurement of the test modules, not of the corpus; P1 / P2 remain
unimplemented (the user's decision).

<!-- worker round (its own numbering) -->

## 9. Round 10 (branch `par/g1-checks-6`) — UNVERIFIED, not built

Measurement of round 9 (integrator's run, 27 real parents): `hierGate`,
`hierBinds`, `outsCheck0`, `outsA`, P1, `instNamesNodup(o)`, P2b all true on
every one; `kept` false on all (the optimizer's output is always kept);
`shipsHierHCheck` true only on the one-output combinational parents.

### 9.1 Which design is the heads' `D`? (read from the sources)

* `machine_ships_hierC` (`Tools/ShippingMachineShipsHier.lean`) takes
  `hr : RunsTo (synthesizeCombinational declName) … (b, design) w'` and
  concludes `∃ raw D, (b = dropZeroWidthModule raw ∨ b = mergeChecked …) ∧
  (shipsHierCheck (childMap D.modules) b = true → …)`. Its proof starts with
  `obtain ⟨raw, D, w1, hcore, hpost⟩ := synthesizeCombinational_checked hr`:
  `(raw, D)` is the result of the CORE run
  (`synthesizeCombinationalCore declName [] false`) inside the full entry.
  **`D` is the core run's design, not the `design` the full entry returns.**
* `ships_design_svN_all` / `ships_design_svH_all`
  (`Tools/ShippingShipsDesignSVAll.lean`) take the previous conclusion as
  their hypothesis `H` and return the same `∃ raw D, …` with two more
  premises inside: `designCheck (childMap D.modules) n (checkedOptimize b)`
  and `outsCheck (childMap D.modules) n (checkedOptimize b)`. Same `D`.
* The generated endpoints (`Tools/ShippingShipsDesignSVCommand.lean`,
  `compose`) are `ships_design_svN_all n Reset Bnd Bd … (ships xs)`: they do
  NOT discharge the two checks. The checks stay as premises INSIDE the
  existential; `Tools/ShippingPremiseEval.lean` and the tests evaluate them
  on the real modules (evidence). So there is no `decide` to replace in the
  endpoint: the premise has to be removed from the head.
* The two designs: by `synthesizeCombinational_designL`,
  `design.modules = D.modules` when no module of `D` has the top module's
  name (the full entry post-processes the modules of that name only);
  `kidsChild_iface` / `kids_run_kid` derive that condition from `hself`.
  `kidsDesign_real` and `parent_run_outsCheck0_kids` (round 9) are about
  `design`; `core_kids_facts` and `core_outsCheck_all` (this round) are
  about `D`.

**The exact statement that removes the premise** — a head proved with the
core run in hand. In `machine_ships_hierC`'s proof, right after
`synthesizeCombinational_checked hr` gives `hcore` and `hpost`:

    core_outsCheck_all d ok hbody hC hslots hdomB hins outTy hnomem hkidA hkidR
      hw hcore hpost entry closes hbind n
      : outsCheck (childMap D.modules) n (checkedOptimize b) = true

with `hbind : hierBinds b = true` (the first fact `shipsHierCheck_sound`
gives from the head's own premise). The types match the heads' literally
(`childMap D.modules`, any depth `n`, the module `checkedOptimize b`).
What the head needs in addition to what it has: `hw : InvW mref cref w`
(the closing's world invariant; where the head would get it from its `Bnd` was not traced),
`closes : MachineClosesAt …` (it takes a generic `C`; at the `…RA` heads
`C` is that), the data conditions `ok`, `hbody`, `callsOk`, `hslots`,
`hdomB`, `hins`, `hnomem` (all already asked by the closing), and per child
`hkidA` / `hkidR` (`leaf_real_kidA`, `leaf_real_kidR`; `kids_real_kid` for a
child with calls). Because the existential hides the core run, this cannot
be done from OUTSIDE the head: either a variant of
`ships_design_svN_all` whose hypothesis `H` exposes
`RunsTo (synthesizeCombinationalCore declName [] false) … (raw, D) w1`
next to `hpost`, or the derivation inside `machine_ships_hierC` and a
conjunct `outsCheck … = true` added to its conclusion.

### 9.2 `hkidA` / `hkidR` at depth

`core_outsCheck_all` gives every depth at once from a design closed under
resolution (`outsCheck_opt_all`, pure). `kids_real_kid` produces both facts
for a child with calls from the same facts of its children, so
`grand → mid → cnt` is: `leaf_real_kidA` + `leaf_real_kidR` at `cnt`,
`kids_real_kid` at `mid`, `core_outsCheck_all` at `grand` with `n = 1`.

### 9.3 `designCheck` for a parent whose design modules are machines without calls

`designCheck C 0 o = textCheckI C o && kidsPass C leafCheck o.body` is a
conjunction of Bools; `designCheck0_of` assembles it from nine named facts.

| # | Conjunct | Kind | Status |
|---|---|---|---|
| 1 | `o.body.all seqStmtOkI` | structural | compiler-checked in principle (`hierRefineCheck`'s `refineCheck` on the extracted pair), no lemma from `openFlat o` back to `o.body`; trivially from `b` when `o = b` — never the case on the 27 parents |
| 2 | `seqCheck (wofOf o) (weS o) o.body` | TEXT | gap |
| 3 | `declWidth o x == weS o x` on `seqNames` | TEXT (width tables) | gap |
| 4 | `linkedWF C o.body` | structural | gap (P2); true on all 27 (P2b) |
| 5 | `(instNames o.body).Nodup` | structural | gap (P1); true on all 27 |
| 6 | `noSelfRead C o.body` | structural | `noSelfRead_opt` from `noSelfRead C b.body`; the latter from `MachineWired`'s `noSelfFeed` — the two predicates are not related by any lemma I found |
| 7 | `portsMatchB C o` | TEXT (widths of connections) | gap |
| 8 | instances resolve | structural | DERIVED (`core_kids_facts` + `resolved_opt`) |
| 9a | each child: `body.all seqStmtOkA`, `body.all memOpsRefs` | structural | from `ChildIfaceG.seqOk` per real child (not assembled: `seqStmtOkA` / `memOpsRefs` definitions not read) |
| 9b | each child: width agreement, `seqCheck` | TEXT | gap |

So the structural part is {1, 4, 5, 6, 8, 9a}; of it only 8 is derived, 6
and 9a are within reach, 1 needs an `openFlat` lemma, 4 and 5 need P2 / P1.
The text part {2, 3, 7, 9b} is untouched.

**Factoring proposal** (a Tools definition, the integrator's to change):

    def designStruct (C) (o : Module) : Bool :=
      o.body.all seqStmtOkI && linkedWF C o.body && decide (instNames o.body).Nodup &&
      noSelfRead C o.body && o.body.all (inst ⇒ (C mn).isSome) &&
      kidsPass C (fun c => c.body.all seqStmtOkA && c.body.all memOpsRefs) o.body
    def designText (C) (o : Module) : Bool :=
      seqCheck (wofOf o) (weS o) o.body &&
      (seqNames o.body).all (fun x => declWidth o x == weS o x) && portsMatchB C o &&
      kidsPass C (fun c => (leafNames c.body).all (fun x => declWidth c x == weS c x) &&
        (if hasSyncMem c.body then seqCheckM … else seqCheck …)) o.body
    theorem designCheck0_split : designCheck C 0 o = (designStruct C o && designText C o)

(`kidsPass C (f && g) = kidsPass C f && kidsPass C g` is the one lemma the
split needs.) The heads then take `designText` as their premise and
`designStruct` becomes a derived fact, conjunct by conjunct as above.

## Integrator's build (2026-10-12, round 10)

`Tools.ShippingChecksDepth` and `Tools.ShippingChecksCore` built through the
protected queue with no change; `core_outsCheck_all` depends on standard
axioms only. Not done: no endpoint head uses it yet (the heads hide that
their `(raw, D)` is a core run) — that connection is the integrator's.

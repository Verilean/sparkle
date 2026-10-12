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

# B — memory children at depth ≥ 1 on the machine route (round par/b-38)

Branch `par/b-38` from poc `202093d6`. **WRITTEN, NOT BUILT**; no `lean`,
`lake` or `iverilog` was started. Marks: [R] read (file:line at 202093d6),
[M] measured by the integrator earlier, [P] predicted, [?] not known.

**How far it got:** unit 1 (state of play) and unit 2 (the smallest
declarations and a never-failing probe of the existing commands) are
written. Unit 3 (the bridge) is NOT written: the missing chain is identified
down to its statements (§4) and stops before the first lemma — I ran out of
room to mirror `Tools/ShippingGenKid.lean` (420 lines) against the memory
variants responsibly in this round. No hypothesis was put in its place.

## 1. State of play, by reading

### 1.1 How a memory appears

A certified-route memory is an INSTANCE of a memory-only submodule (project
decision "memory as submodule"): in the reader's shape a memory read is a
call entry whose callee name is a placeholder `SparkleMem.{combo|sync}.aw.dw`
(`Sparkle.Compiler.MachMemory.memChild? c = some (memModule cb aw dw)`), and
the closing takes for it the BUILT module, not a child run. `Kid mref cref c
y` [R: `Tools/ShippingKid.lean` 33–36] is that disjunction: `memChild? c =
some y ∨ (memChild? c = none ∧ RealChild mref cref c y)`.

So a machine with a memory (`memCounter`) is already a PARENT at the design
level: `DesignSV C 0` with the memory modules as its kids (the `R0` forms).
A parent of such a machine is at depth 1, and its kid is a machine WITH call
entries (the memory placeholders) — the shape the depth generators call a
"general-closing callee".

### 1.2 What exists

| shape | closed form | generator | built evidence |
|---|---|---|---|
| a register machine whose calls are ALL memory placeholders (`memCounter`, `twoMems`, `mixedMems`, `withMemory`) as an ENTRY | `machine_design_noPortsR0_closed` (`…_closedN`) | `#machine_no_ports_mem` (`Tools/ShippingNoPortsMemCommand.lean`) | 9 declarations COVERED [M, census 0a0a4f71] |
| a register machine whose calls MIX leaf register machines and memory placeholders (`seqMem`, `seqAccSync`) as an ENTRY, depth 0 | `machine_design_noPortsR0_closed` | `#machine_no_ports_memseq` (`ShippingNoPortsMemSeqCommand.lean` 1–60: "Depth 0 only") | in the 9 above |
| the interface of a callee "that may be a memory" | `KidFactsM mref cref c outs ins n` over `Kid`, `flat` in the place of `masked` (`Tools/ShippingMemKidFacts.lean` 423–449); `kidFacts_toM` (453); **`memKid_facts … 0`** (468–470: a placeholder's facts at depth **0** only) | — | built |
| the parent-side theorems over `KidFactsM` | `kidsM_runFacts` (564), `kidsM_outsCheck` (594), `core_kidsMixedM` (627), `kidsM_mixed` (665), `kidsM_designCheck` (694–739, general in the depth `n`, against the run's OWN design `childMap D.modules`) | — | built |
| the closing over kids that may be memories | `machineClosesAt_of_kidsDM` (`Tools/ShippingMemClosesKids.lean` 419), `machineClosesAt_memOnly` (`ShippingMemOnlyCloses.lean` 85) | `#machine_closes_at` branches | built |
| a callee WITH calls of its own, as a kid of a deeper parent | `GenKid` → `GenKid.facts : KidFacts … c … (n + 1)` (`Tools/ShippingGenKid.lean` 230–420) | `#machine_no_ports_deep` | `grand`, `topD2`, … |

### 1.3 What is refused, with the refusing line

A parent whose CHILD has a memory (the child a register machine whose calls
are placeholders):

| command | refusal [R] |
|---|---|
| `#machine_no_ports f n` | `ShippingNoPortsCommand.lean` 91: a callee must be a leaf register machine (`LeafKid.leaf : shape.insts = []`); a callee with call entries is not a leaf |
| `#machine_no_ports_kids f 1` | accepts leaf register machines and one-output callees; "REFUSES a callee whose own calls are tied by the general closing" (`ShippingNoPortsDeepCommand.lean` 9–11) |
| `#machine_no_ports_deep f n` | `scopeD` (159–200): the callee is "general" (`instFields ≠ []`); its ONE callee `s` is read by `readKid` (139–155), which throws at **149**: `"{who} {k} is a memory child (no KidFacts for it)"` — `who` = "the general-closing callee k's callee". Also `n ≥ 2` is asked (163), while this parent is at depth 1 |
| `#machine_no_ports_seq` | `ShippingNoPortsSlotlessCommand.lean` 105: "a memory child (no KidFacts for a memory…)" for a DIRECT placeholder; a callee with calls is not a leaf |
| `#machine_no_ports_mem` / `_memseq` | depth 0; call entries must be placeholders (and leaves): a callee with calls is neither |
| the closing generators | `ShippingMachineClosesAtGenG.lean` 38 "a memory child (not derived here)" for the kids' sub-closings |

The reason under all of them is ONE structure field: `GenKid.nomem`
[R: `Tools/ShippingGenKid.lean` 247]

    nomem : ∀ c ∈ dk.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none

with `kidsLo` / `kidsHi : KidFacts mref cref (dk.shape.insts[k]).1 …` (over
`RealChild`, 265–268) and the inner theorem `kids_designCheck_in` taking
`hnomem` (109–128). A callee whose entries are placeholders has no
`RealChild` of them and fails `nomem`.

The same for a callee that is itself a memory+register machine with leaf
children (`seqAccSync`-like) used as a callee: its entries mix placeholders
and leaves — `nomem` fails.

## 2. The smallest uncovered shape (new declarations)

`Tests/Compiler/MemDepthProbeTest.lean` (target-only):

* `memCounterH` — `memCounter` tagged `@[hardware_module]` (the untagged one
  would be inlined into a caller).
* `memParent1` — a register parent whose ONLY call is `memCounterH`. One
  `BitVec` output ⇒ PREDICTED the one-output closing (`instFields = []`;
  the note of `DepthRegsChildTest.lean` 79–86), a different class.
* `memParent` — the same with a second call of the structure-result child
  `cnt`: the general closing. **This is the smallest shape of the class.**
* `memGrand` — a register parent of `memParent` and `cnt` (two levels).

Each existing command is run under `#mem_depth_try "label" in …` (the built
`#drc_try`, copied): `OK` or `FAILED` with the command's own message, the
environment put back; the file is an error in no case and asserts nothing.

## 3. PREDICTED outcomes of the probe

| step | PREDICTED | basis |
|---|---|---|
| C1–C5 `memCounterH` as an entry (`#machine_endpoint`, `#machine_composedT`, `#machine_ships_hier`, `#machine_design_svR0`, `#machine_no_ports_mem`) | OK ×5 — the chain of `memCounter` (the tag does not change an entry's compile) | [M] for `memCounter` |
| P1.1 `#machine_endpoint memParent1` | [?] — the per-call fact (`causalFactE`) accepts a sequential child whose endpoint is `_of_loop`; `memCounterH`'s is the loop-with-calls head | `DepthRegsChildTest.lean` 70–78 |
| P1.2–P1.4 | FAILED — one-output closing: `generateCoreNR` "one-output combinational calls" | same note, 79–86 |
| P2.1 `#machine_endpoint memParent` | [?] as P1.1 |
| P2.2 `#machine_design_svNR memParent 1` | [?] — the grouped depth generator's head table must have a branch for a child whose endpoint has calls (memory reads) of its own (`ShippingMachineDepthCommandR.lean` 827: "neither a memory read nor a grouped entry" is the refusal for an unknown entry) |
| P2.3 `#machine_closes_at memParent` | FAILED — the kid `memCounterH`'s own closing over a placeholder is "not derived here" (`ShippingMachineClosesAtGenG.lean` 38), unless the generator reuses `memCounterH.machine_closes_at` from C5 [?] |
| P2.4 `#machine_no_ports_kids memParent 1` | FAILED — a callee whose own calls are tied by the general closing |
| P2.5 `#machine_no_ports_deep memParent 2` | FAILED — depth, or line 149 "… is a memory child (no KidFacts for it)" |
| G.1–G.4 | FAILED where `memParent`'s steps fail |

The probe's value is the FIRST failing step per declaration: it says whether
the gap starts at the ship level (the depth generator, P2.2) or only at the
check-free level (P2.3–P2.5), which decides how much of §4 is needed.

## 4. The missing bridge, exactly (NOT written)

Target: `KidFacts mref cref memCounterH memCounterH.machineData.shape.layout.outs
(argWidths …) 1` — the interface the BUILT parent-side theorems
(`kids_runFacts`, `kids_designCheck`, the head of `#machine_no_ports_deep`)
take of a callee. With it, a generator branch "kid kind `genM`" applies the
existing heads to `memParent` unchanged.

The chain, in dependency order (each the M-variant of a built lemma):

1. **A placeholder's facts at every depth.** `memKid_facts` is at depth 0
   (`ShippingMemKidFacts.lean` 468–470). Needed at `n + 1` for `kidsHi`:

       theorem memKid_facts_succ (hc : memChild? c = some (memModule cb aw dw)) (n : Nat) :
           KidFactsM mref cref c (memOuts dw) (memIns aw dw) (n + 1)

   Eight fields are the depth-0 proof's (they do not mention `n`); `check`
   needs `kidCheck (childMap ms) (n + 1) (memModule cb aw dw).1 = designCheck
   (childMap ms) n … = true`: `textCheckI` of the memory module (the depth-0
   proof shows `leafCheck` of it — which conjuncts differ is [?]) and
   `kidsPass … []`-like (`mem_noInst`, 291: the module has no instance).
2. **`kidsM_designCheck_in`**: `kidsM_designCheck` (694) against ANY module
   list that resolves the run's design modules to themselves — the M-variant
   of `kids_designCheck_in` (`ShippingGenKid.lean` 109–228), i.e. its proof
   with `core_portsMatch_rawM`, `core_hierGateM`, `core_kidsPass_deepM`,
   `core_designCheck_runM` (the lemmas `kidsM_designCheck` already calls) in
   their `_in` forms [? whether `_inM` forms of those four exist; the non-M
   `_in` forms are in `ShippingGenKid.lean` / `ShippingChecksDesign.lean`].
3. **`GenKidM`**: `GenKid` (230–275) without `nomem`, with

       kid    : ∀ k hk y, Kid mref cref (dk.shape.insts[k]).1 y → KidNames (dk.shape.insts[k]).1 (namesK k) y.1 y.2
       kidsLo : ∀ k hk, KidFactsM mref cref (dk.shape.insts[k]).1 (kidOuts k) (kidIns k) n
       kidsHi : ∀ k hk, KidFactsM mref cref (dk.shape.insts[k]).1 (kidOuts k) (kidIns k) (n + 1)

   and its lemmas `core`, `outsIn`, `kidAR`, `ports`, `typedIn`, `masked`,
   `clk`, `check` (280–400) re-proved over `kidsM_*`, ending in

       theorem GenKidM.facts (K : GenKidM mref cref c dk nDecl namesK kidOuts kidIns n) :
           KidFacts mref cref c dk.shape.layout.outs (argWidths dk nDecl) (n + 1)

   Open point [?]: `KidFacts.masked` asks `outsMaskedN y.1` of the callee's
   module. `GenKid.masked` (352) proves it for a callee without memories;
   whether its proof goes through for a module with a memory instance, or
   the conclusion has to be `KidFactsM` (`flat`) and the PARENT then has to
   use the `kidsM_*` heads — in which case the parent's generator is the
   memseq one at depth 1 rather than the deep one — I could not decide by
   reading 12 lines of it.
4. **`KidNames` of a placeholder** for `kid` (the built `memKid_iface`,
   `ShippingMemClosesKids.lean` 239–243, gives the name list
   `[(memModule cb aw dw).1.name]`).
5. **The generator branch** in a NEW command file: kind `genM` — a callee
   with a register, the general closing, whose entries are placeholders
   (then: placeholders and leaves); `k.machine_genKidM{n}` from the data
   (`decide`s as `GenKid`'s), `memKid_facts` / `memKid_facts_succ` per
   entry; the parent's endpoint by the BUILT head. Plus the sweep / audit /
   census recognition (the form is the existing `machine_design_noPortsNR{n}_closed`,
   so the census needs no change).

## 5. Could not be determined by reading

* Whether `#machine_endpoint` accepts a parent of a loop-with-memory child
  (P1.1 / P2.1) and whether the grouped depth generator has a head for it
  (P2.2) — the probe measures both.
* §4 item 1: which conjunct of `textCheckI` a memory module needs beyond its
  `leafCheck`.
* §4 item 2: whether `_in` forms of the four `core_*M` lemmas exist.
* §4 item 3: `masked` for a module with a memory instance.
* Whether the reader puts `memParent1` under the one-output closing (the
  note I rely on is about a bare-register child).

## 6. Integrator

No `lean_lib` line (no new Tools file). A target for
`Tests.Compiler.MemDepthProbeTest` (imports `Sparkle`, the command files and
`Tests.Compiler.ShippingMachineSeqTest`). Not for `Tests/AllTests.lean` (a
probe). Risk: the four definitions are not wrapped — if one does not
elaborate (`memCounterH` is a copy of the built `memCounter`; the three
parents are `circuit do` bodies of the shape of `caller` / `callerNested`)
the file fails there.

## Integrator's build record (2026-10-13) — MEASURED

BUILT on poc 28adf9af + this file, run `backlog2`. Integrator fix: the probe lacked
`import Tools.ShippingMachineSeqCommandR` (`#machine_design_svR0`). The probe asserts nothing.
* `memCounterH` as an entry: `#machine_endpoint` OK, `#machine_composedT` OK, `#machine_ships_hier` OK,
  `#machine_no_ports_mem` OK; `#machine_design_svR0` FAILED "no sequential child" (not the command for a
  memory-only machine).
* `memParent1` (register parent of `memCounterH` only): `#machine_endpoint` FAILED — "the machine
  synthesis does not tie the lets"; every later step fails for lack of `machineData`.
* `memParent` (+ `cnt`), `memGrand`: `#machine_endpoint` FAILED — "the child memCounterH's endpoint is
  not machine_trace_of_data(_ext/_causal) or _of_loop"; later steps fail for lack of `machine_sound`.
CONSEQUENCE: for a parent whose child has a memory the gap starts at the SHIP level (`#machine_endpoint`:
the nested-child composition has no head for a child whose endpoint is the memory one), not only at the
check-free design level. The bridge of §4 (the `GenKidM` interface) presupposes the parent's ship-level
endpoints and is therefore NOT the next step; the next step is the semantic composition of a parent with a
memory-machine child.

# C — the check-free design-level endpoint for a parent of a memory-only kid (round par/c-4)

Branch `par/c-4` from poc `8deae5a4`. **WRITTEN, NOT BUILT.** No `lean`,
`lake` or `iverilog` was started; nothing below is proved-and-built. Marks:
[R] read (file:line at 8deae5a4), [M] measured by the integrator, [P]
PREDICTED, [?] not known.

**How far it got — short.** Step 0 was done for the kid interface and the
parent's check chain, NOT for the heads (`machine_design_noPorts`,
`#machine_no_ports_kids`' finish) and not for `closesDeep`'s body. Step 1 is
answered by reading with a NEGATIVE result that changes the plan
(`KidFacts … memCounterH … 1` is FALSE, and so is `KidFactsM`; §2). ONE new
file is written: the parent side for the interface that IS true
(`Tools/ShippingKidFactsT.lean`, §3). The kid side (`KidFactsT … memCounterH
… 1`), the hand endpoint (step 2), `memGrand` (3) and the generator (4) are
NOT written; §4 gives the exact next statements and which built lemmas
exist for them. No hypothesis was put in the place of a missing proof.

## 1. What was read

| what | where [R] |
|---|---|
| `KidFacts` (all fields), `kids_runFacts`, `kids_outsCheck`, `kids_maskedN`, `kids_designCheck` (statements and proofs), the header | `Tools/ShippingKidFacts.lean` 1–252 (whole file) |
| `core_kids_self` (statement and proof), `core_kidsPass_deep` (statement and proof), `core_kidsMaskedN_top` (statement and proof), the header | `Tools/ShippingKidsSelf.lean` 1–233 (whole file) |
| `core_callConns` (statement, first proof lines) | `Tools/ShippingPortsMatchRaw.lean` 244–287 |
| `GenKid`: header, `kidCheck_succ`, `kids_designCheck_in` (statement and proof), the structure (incl. `nomem` 247), `GenKid.core`, `.outsIn`, `.kidAR`, `.ports`, `.typedIn`, `.masked`, `.clk`, `.check`, `.facts` | `Tools/ShippingGenKid.lean` 1–422 (whole file) |
| `KidFactsM` (all fields), `kidFacts_toM`, `memKid_facts` (statement, first lines) | `Tools/ShippingMemKidFacts.lean` 418–475 |
| `textCheckI`, `kidsPass`, `designCheck`; `leafCheck`; `seqStmtOkI`; `kidCheck`; `outsMaskedN`, `kidsMaskedN` | as in `C-mem-depth-ships.md` §1 |
| the NAMES (declaration lines only, not statements) of the built `M` theorems | `Tools/ShippingMemKidFacts.lean`, `ShippingMemKidCore.lean`, `ShippingMemKidPorts.lean`, `ShippingMemOnly.lean`, `ShippingMemOnlyCloses.lean`, `ShippingCoreFromM.lean` (grep of `^theorem`) |

NOT read (the task's step 0 asked for them): `machine_design_noPorts` and
the other heads of `Tools/ShippingNoPorts*.lean`; what
`#machine_no_ports_kids f 1` emits after its scope test
(`ShippingNoPortsKidsCommand.lean` 498–620); `closesDeep`'s body; the
statements of the `M` core theorems listed in §4. They are needed for the
steps that are not written.

## 2. Step 1, decided by reading: `KidFacts … memCounterH … 1` is FALSE; so is `KidFactsM`

**The field that fails is `check`, not `masked`.**

`KidFacts.check` [R `ShippingKidFacts.lean` 94–99]:

    ∀ y, RealChild mref cref c y → ∀ ms, moduleByName ms y.1.name = some y.1 →
      (∀ g ∈ y.2.modules, moduleByName ms g.name = some g) →
      kidCheck (childMap ms) n y.1 = true ∧ ∀ g ∈ y.2.modules, kidCheck (childMap ms) n g = true

— `kidCheck C n` of the callee's module AND of EVERY module of its design,
at the SAME depth index. For `c := memCounterH`, `n := 1`: its design
contains the memory module `g := (memModule true 4 8).1`, and

    kidCheck C 1 g = designCheck C 0 g = textCheckI C g && …        (kidCheck 119–122, designCheck 122–124)
    textCheckI C g = g.body.all seqStmtOkI && …                     (ShippingDesignSV.lean 103–104)
    g.body = [.memory …, .assign …]                                 (MachMemory.lean 59–61)
    seqStmtOkI (.memory …) = false                                  (ShippingHierSVSoundness.lean 30–34)

so the second conjunct is false for a `ms` that resolves the modules (the
real design does). The same at every `n ≥ 1`. At `n = 0` the FIRST conjunct
fails instead (`kidCheck C 0 y.1 = leafCheck y.1`, and `memCounterH`'s module
has an instance — the built header says the leaf form is false of a module
with instances, 30–34). So there is no `n` at which `KidFacts mref cref
memCounterH …` holds. `KidFactsM.check` is the same statement over `Kid`
[R `ShippingMemKidFacts.lean` 443–449]: also false. `memKid_facts` (a
placeholder at depth 0) is fine — there the design is the module itself and
`kidCheck C 0 = leafCheck` accepts a memory statement.

This is the correction of `C-mem-depth-ships.md` §7.2 taken one step
further: not only "placeholders stay at depth index 0" — a kid WITH a
memory below it has no `KidFacts` at all, because `KidFacts` checks the
whole design below the kid at one depth index, and a design with a memory
module has no single index.

**`masked`** (the field the coordinator asked about): `outsMaskedN y.1 =
noMem y.1.body && y.1.outputs.all (outMasked … ∧ no connection names the
port)` [R `ShippingMachineShipsDepth.lean` 155–160] is about the kid's OWN
module only, whose body has an INSTANCE of the memory module and no memory
statement: nothing in the definition makes it false. Whether it is DERIVED
needs the `M` form of `GenKid.masked`'s two inputs (`CallsPorts`,
`core_conn_refsG`; §4) — not read.

**Where the uniform conjunct is consumed.** In one place of the parent's
chain: `core_kidsPass_deep` [R `ShippingKidsSelf.lean` 195–198], for the
case "the module an instance of the parent resolves to is a module of some
child's DESIGN" (`hin`). (`GenKid.check` consumes it too, 399–403 — one
level up, for the same reason.) Under the general closing every instance
resolves to a real child's OWN module (`core_callConns`, 265–268 — the fact
`core_kidsMaskedN_top` uses to ask `masked` of own modules only); with the
names separated that module is not also a module below a child. So the
conjunct is not needed by a parent whose names are separated — §3.

## 3. Written: `Tools/ShippingKidFactsT.lean` (new) — the parent side over own-module checks

    structure KidFactsT (mref) (cref) (c : Name) (outs : List OutField) (ins : List Nat) (n : Nat) : Prop
      -- KidFacts' fields outsIn, outTys, kidA, kidR, masked, portsIn, inW, clk unchanged, and
      check : ∀ y, RealChild mref cref c y → ∀ ms, moduleByName ms y.1.name = some y.1 →
        (∀ g ∈ y.2.modules, moduleByName ms g.name = some g) → kidCheck (childMap ms) n y.1 = true

    theorem KidFacts.toT : KidFacts mref cref c outs ins n → KidFactsT mref cref c outs ins n

    theorem core_kidsPass_top … (the premises of core_kidsPass_deep, hkidK with the first conjunct only)
        (namesK : Nat → List String)
        (hname : ∀ k hk y, RealChild mref cref (d.shape.insts[k]).1 y →
          y.1.name = ModuleName.ofDecl (d.shape.insts[k]).1 ∧ ∀ g ∈ y.2.modules, g.name ∈ namesK k)
        (hsep : ∀ k (_ : k < d.shape.insts.length) k' (_ : k' < d.shape.insts.length),
          ModuleName.ofDecl (d.shape.insts[k]).1 ∉ namesK k')
        hB hcore hpost entry closes :
        kidsPass (childMap D.modules) (kidCheck (childMap D.modules) n) (checkedOptimize b).body = true

    theorem kidsT_runFacts / kidsT_outsCheck / kidsT_maskedN     -- kids_* over KidFactsT, statements otherwise unchanged
    theorem kidsT_designCheck … (kids_designCheck's premises over KidFactsT) (namesK) (hname) (hsep) … :
        designCheck (childMap D.modules) n (checkedOptimize b) = true

How it was made: by script from the built files, with asserted
single-occurrence replacements. `core_kidsPass_top` is `core_kidsPass_deep`'s
proof (`ShippingKidsSelf.lean` 139–199) with `core_callConns` added and the
`hin` case replaced by a contradiction: the instance's module is `y₂.1` for a
real child `y₂` of an entry `k₂` (its name `ofDecl (insts[k₂]).1` by
`hname`), and it is below the child of entry `k` (its name in `namesK k`):
`hsep k₂ k`. The four `kidsT_*` are the built proofs (104–251) — they read
the interface field by field — with `KidFactsT` for `KidFacts` and, in the
last, `core_kidsPass_top namesK hname hsep` for `core_kidsPass_deep`.

`hname` and `hsep` do not rename the conclusion: `hname` is two fields of
the children's `ChildIfaceD` (`name`, `desNames` — for `memParent`: the
built leaf interface of `cnt` and the built hand theorem `memCounterH_iface`),
`hsep` is the name separation the closing already asks (`hselfD` and the
first half of `hdisjD`), for `memParent` `ofDecl_not_mem_allMem`
(`Tools/ShippingMemNamesP.lean`).

`lakefile.lean`:

    lean_lib «Tools.ShippingKidFactsT» where
      roots := #[`Tools.ShippingKidFactsT]

Builds alone (imports the built `Tools.ShippingKidFacts`). Nothing uses it
yet.

## 4. NOT written: the exact next statements

### 4.1 The kid side (step 1's real content)

    theorem memCounterH_factsT {mref cref}
        (hR : ∀ mctx' cctx', MachineDefines mctx' mref cctx' cref ``memCounterH memCounterH.machineData.shape) :
        KidFactsT mref cref ``memCounterH memCounterH.machineData.shape.layout.outs
          (argWidths memCounterH.machineData 3) 1

i.e. `GenKid.facts` at `n = 0` for a kid whose callees are placeholders, with
the conclusion weakened to `KidFactsT` (what is true) — a `GenKidM` whose
`kidsLo` is `KidFactsM … 0` (`memKid_facts`) and which has NO `kidsHi`.
Field by field, against `GenKid`'s proofs [R `ShippingGenKid.lean` 280–420];
"built M" = a theorem of that NAME exists (its statement was NOT read):

| field | `GenKid` uses (all with `hnomem`) | built `M` form | status |
|---|---|---|---|
| the bridge `core` (served module = post-processing of a core run, served design = the run's) | `synthesizeCombinational_designL`, `core_kids_facts`, `KidNames` of the grandkids | `core_raw_facts_fromM` (`ShippingCoreFromM.lean` 66) [?]; `KidNamesP` + `memKidNamesP` (c-2/c-3) | to write; the name step is `kidsChild_ifaceM`'s `hvisN` |
| `outsIn` | `kidsChild_of_real` | `kidsChild_of_realM` (built, c-2) — it is `memCounterH_iface.outsIn` | HAVE |
| `kidA`, `kidR` | `kids_real_kid` (`ShippingChecksCore`) | none found by name | MISSING |
| `outTys`, `inW` | `core_calls_portsG` → `CallsPorts` | `core_callPorts_fromM` (`ShippingCoreFromM.lean` 135) [?] | not read |
| `portsIn` | `core_closed_typedIn` | `core_closed_typedInM` (`ShippingMemKidPorts.lean` 53) | built |
| `masked` | `outsMaskedN_of_callsG` + `core_conn_refsG` | none found by name (`mem_conns_noRdata`, `ShippingMemKidFacts.lean` 393, is a piece) | MISSING |
| `clk` | `core_clk` | `core_clkM` (`ShippingMemKidPorts.lean` 300) | built |
| `check` (own module: `designCheck (childMap ms) 0 y.1`) | `kids_designCheck_in` | none; its ingredients have `M` forms: `kidsM_runFacts` (564), `core_linkedWFM` (`ShippingMemKidCore.lean` 98), `core_closed_typedInM`, `core_portsMatch_rawM` (732), `core_kids_selfM` (841), and `memKid_facts` for the kids' check at 0 | to assemble (`kids_designCheck_inM`, a copy of 109–224) |

Three of these (`kidA`/`kidR`, `masked`, the `_in` check) are proofs over
built theorems I have not read; I did not write them blind.

### 4.2 The hand endpoint (step 2)

With 4.1, for `memParent` (no memory entry of its own: `hnomem` decided):

    theorem memParent_design_noPorts1_closed {mctx mref cctx cref w w' b design}
        (hr : RunsTo (synthesizeCombinational ``memParent) mctx mref cctx cref w (b, design) w')
        (hP : MachineDefines … ``memParent …) (hRc : MachineDefines … ``cnt …)
        (hRm : MachineDefines … ``memCounterH …) :
        ∃ raw D, (b = … raw ∨ …) ∧ (ChildBnd mref cref w → DesignSV …)

by the check-free head that `#machine_no_ports_kids` applies, on
`memParent.machine_ships_hierNR1` [M built: S2.b], with its four facts from
`kidsT_runFacts`, `kidsT_outsCheck`, `kidsT_maskedN`, `kidsT_designCheck`
(`hkid` : `cnt` ↦ `(leafKid_facts …).toT`, `memCounterH` ↦
`memCounterH_factsT`), the closings from `memParent_closes` and
`memCounterH.noPortsMem_closes`. NOT written, for two reasons: 4.1 is
missing, and I did not read the head (`machine_design_noPorts`: its exact
argument list, how the depth endpoint's boundary premises — `MachineRunNC`'s
ingredients for the kid, the closing of the kid under `ChildRanIn` — are
discharged there). The predicted obstacle-free part: the head takes the four
facts as functions of the run binders (`ShippingNoPortsKidsCommand.lean`
536–562: "run-facts", "output-check", "children-bound", "design-check"
hypotheses), so the `kidsT_*` conclusions are of the right form [? binder
counts 6, 7, 6, 6 not matched against `kidsT_*`].

### 4.3 `memGrand` (step 3) — an obstacle visible already

`memGrand`'s kid `memParent` is a general-closing kid WITH a memory below it
(two levels). Its `KidFactsT … memParent … 2` needs, for the own-module
check `designCheck C 1 memParent_module`, the children's check of
`memParent`'s kids at `kidCheck C 1` — own modules only, by
`core_kidsPass_top`'s argument in the `_in` form — i.e. a `GenKidT`:
`GenKid` with `kidsLo : KidFactsT … n`, no `kidsHi`, the names for `hsep`,
and conclusion `KidFactsT … (n + 1)`. That is the general unit; 4.1 is its
instance with memory kids at `n = 0` (where `kidsLo` is `KidFactsM`, the
memory-aware core lemmas). So the right order is: `GenKidT` over `KidFactsT`
(non-memory kids; the built core lemmas with `hnomem` apply unchanged, only
`check` changes) FIRST — it is a smaller edit of `GenKid` than 4.1 — then
4.1 with the `M` lemmas.

### 4.4 The generator (step 4)

Not started. The census re-checks statements, so a `…_closed` theorem of
the existing form needs no census change — I did not verify this against
the census code [?].

## 5. PREDICTIONS

| item | PREDICTED |
|---|---|
| `Tools.ShippingKidFactsT` builds | yes [P] — risks: the `obtain` pattern for `core_callConns`' conclusion (copied from the built `core_kidsMaskedN_top`); `rw [← e, e2]` in `h1`; the anonymous binders `(_ : k < …)` in `hsep` |
| the claim of §2 | checkable without a build of mine: `example : kidCheck C 1 (memModule true 4 8).1 = false := by decide`-style evaluation is the integrator's to run if wanted; by reading it is `seqStmtOkI (.memory …) = false` |

## 6. Risks, in order

1. §2 rests on reading four definitions; if `textCheckI`'s first conjunct
   were not what line 104 says for a memory statement, the plan would
   revert to `KidFacts`. I re-read the lines; I did not evaluate anything.
2. `core_kidsPass_top`'s `hsep` is asked for ALL pairs of entries (also two
   entries of one callee, also `k = k'`). For `mixDeep`-like shapes (a
   callee that is also a descendant of another callee) it is FALSE — there
   the built `core_kidsPass_deep` with the uniform check is the one that
   applies. `KidFactsT` does not replace `KidFacts`; it is a second route for
   shapes with separated names.
3. The copied proofs in `ShippingKidFactsT` rely on the built file's `open`s
   (copied) and on `core_kidsPass_top` being found unqualified.

## 7. Not determined by reading

* The heads of the check-free chain and what the kids generator emits after
  its scope test.
* The statements of `core_raw_facts_fromM`, `core_callPorts_fromM`, and
  whether `M` forms of `kids_real_kid`, `core_conn_refsG`,
  `outsMaskedN_of_callsG`, `core_calls_portsG` exist under other names.
* `closesDeep`'s body.
* Whether the census recognises a hand `…_closed` statement of this shape.

## Integrator's build record (2026-10-13)

BUILT on poc 8deae5a4 + this file, cgrun 3 GiB swap 0, run `c4` (exit 0, peak 0.86 GB), worker's file
unchanged, first attempt: `Tools.ShippingKidFactsT` (`KidFactsT`, `KidFacts.toT`, `core_kidsPass_top`,
`kidsT_runFacts`, `kidsT_outsCheck`, `kidsT_maskedN`, `kidsT_designCheck`). Used by nothing yet.
The claim of §2 (`KidFacts … memCounterH … n` is false for every n because the kid's whole design is
checked at one depth index and it contains a memory module) is BY READING; not measured.
STATE: the check-free endpoint for `memParent` is not written. Next statements: `GenKidT` (the deep-kid
interface concluding `KidFactsT`), `memCounterH_factsT`, then the hand endpoint.

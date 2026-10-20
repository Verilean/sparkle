# A: `mixDeep` for outermost starts; what the existing premise needs — round par/a-38

Base: `poc/roundtrip-proof` 2f9211ff (par/a-37 BUILT and integrated).
Branch `par/a-38`. **NOTHING here was built or run**: WRITTEN, NOT BUILT.
"READ" = read at 2f9211ff. No built file, endpoint or generator is modified;
`RefLaws` untouched.

## 0. Result

* `EntryOk` of `cnt` and of `mid2` are written as theorems from reflections
  only (target-only test).
* The depth-0 sibling of `core_reads_val` is written (`core_reads_val0`),
  and with it a NEW, separately named theorem with its scope in its name:
  **`mixDeep_closes_outermost`** — for an OUTERMOST core run of `mixDeep`
  the machine synthesis the entry performs returns the run's result.
  Premises: the five reflections and the depth-0 start condition.
* It is NOT the existing endpoint losing a premise, and the existing
  endpoint `mixDeep.machine_design_noPortsNR2` cannot be applied to it (§3).
* On whether `MachineClosesAt mixDeep` is false at some nested start or true
  but unprovable: neither can be decided from what is built; it comes down
  to ONE statement nobody has stated or refuted — determinism of the real
  compile of the shared descendants across worlds (§3).

## 1. What is written

### `Tools/ShippingCacheCoherentOuter.lean`

```lean
def InvE (L) (C Dp : Prop) (w) : Prop := InvC L C Dp w ∧ (C → L.val w = {})
theorem invE_pure, invE_framed, invE_depthSet
theorem invE_clear (h : RunsTo (sparkleChildCache.set {} : MetaM Unit) … w u w')
    (hw : InvE L C Dp w) : InvE L True Dp w'
-- tactic `peel_e L h hw` (the text of `peel_inv` over these lemmas)

theorem core_reads_val0 (L) (hB : ∀ L', BodyRel L') (hs : L.sval w = some synthesizeChild)
    (hq : L.quiet w) (hd0 : L.dval w = 0)
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w') :
    ∃ b envR ci w1 w2 w3 w4 w5 w6,
      RunsTo (getConstInfo declName) … w1 ci w2 ∧ RunsTo getEnv … w5 envR w6 ∧
      RunsTo (synthesizeFromConst … (profLogIO b) declName [] false true (entryConst …) (instancePredicate envR)) … w3 (M, D) w4 ∧
      InvV L w3 ∧ L.dval w3 ≠ 0 ∧ L.val w3 = {} ∧ InvV L w4 ∧ L.val w' = L.val w4

theorem coreVia0_of (L) (hB) (hH : ∀ L', HarnessRel L')
    (entry : MachineDefines mctx mref cctx cref c shape)
    (hclose : ∀ b w9 r w10, InvV L w9 → L.dval w9 ≠ 0 → Prov (L.val w9) →
      RunsTo (synthesizeMachineCertified … (profLogIO b) c shape) mctx mref cctx cref w9 r w10 → r ≠ none)
    (hs : L.sval w = some synthesizeChild) (hq : L.quiet w) (hd0 : L.dval w = 0)
    (hr : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w') :
    ∃ b w9 w10, RunsTo (synthesizeMachineCertified … (profLogIO b) c shape) … w9 (some (M, D)) w10 ∧
      InvV L w9 ∧ L.dval w9 ≠ 0 ∧ Prov (L.val w9)
```

READ (`Sparkle/Compiler/Elab.lean`): at depth 0 the saved reads are `pure
{}` (5446–5492), the clear block is 5493–5505 with
`sparkleChildCache.set {}` at 5498 (`RefLaws.cacheSet`: the value is the
written one), the other resets are side refs, the depth bump 5517, the
`finally` 5532–5541 restores nothing at depth 0. From the clear to the
machine synthesis every step is a frame (`sfc_machine_val`, BUILT), so the
cache there is `{}` and `prov_empty` applies.

The start condition is `L.sval w = some synthesizeChild`, `L.quiet w`,
`L.dval w = 0` for a witness `L` — exactly the depth-0 disjunct of
`ChildBnd w` (`∃ L, StartV L w ∧ L.quiet w`, `StartV` =
`sval ∧ (dval = 0 ∨ CacheInv)`), with the witness named so that "the depth
reads 0" can be said.

### `Tests/Compiler/MixDeepOutermostTest.lean` (target-only)

```lean
theorem cnt_entryOk (L) (K) (hRc : MachineDefines … ``cnt cnt.machineData.shape) : EntryOk L ``cnt K
theorem mid2_wf, mid2_frag, mid2_harnessStill, mid2_callees
theorem mid2_entryOk (L) (hR2 : MachineDefines … mid2 …) (hRm : MachineDefines … midH …)
    (hRr : EntryDefines … rcH rcH.gateValue) : EntryOk L ``mid2 (fun k => k = ``midH ∨ k = ``rcH)
theorem mixDeep_wf, mixDeep_frag, mixDeep_harnessStill, mixDeep_callees, mixDeep_general
def KD (k) : Prop := k = ``mid2 ∨ k = ``midH ∨ k = ``rcH ∨ k = ``cnt
theorem mixDeep_closes_prov (L) (hR2) (hRm) (hRr) (hRc) (b w9 r w10) (hw9 : InvV L w9)
    (hd9 : L.dval w9 ≠ 0) (hp9 : Prov (L.val w9))
    (hrun : RunsTo (synthesizeMachineCertified … (profLogIO b) ``mixDeep mixDeep.machineData.shape) … w9 r w10) :
    r ≠ none
theorem mixDeep_closes_outermost (L) (hRg : MachineDefines … mixDeep …) (hR2) (hRm) (hRr) (hRc)
    (hs : L.sval w = some synthesizeChild) (hq : L.quiet w) (hd0 : L.dval w = 0)
    (hr : RunsTo (synthesizeCombinationalCore ``mixDeep [] false) mctx mref cctx cref w (M, D) w') :
    ∃ b w9 w10, RunsTo (synthesizeMachineCertified … (profLogIO b) ``mixDeep mixDeep.machineData.shape)
        mctx mref cctx cref w9 (some (M, D)) w10 ∧ InvV L w9 ∧ L.dval w9 ≠ 0 ∧ Prov (L.val w9)
```

Ingredients, all theorems: `mixDeep.closes_shared` (BUILT; its four
reflection premises are filled by `assumption`, their order not being
asserted), `machine_closes_of_entryOk`, `harnessStill_frag` on the packed
terms of `mid2` and `mixDeep` (kernel `decide` of `wfrag` — NOT evaluated
before; if one is `false` that theorem does not compile), `hout_of_data`
over the built data facts, `mid2_coreVia`, `midH_entryOk_closed`,
`rcH_entryStill`, `cnt_entryStill` (BUILT), `seqChild_of_real` for `cnt`'s
name and design, the callee lists and name conditions by `decide`.

The run command THROWS if the statement of `cnt_entryOk`, `mid2_entryOk` or
`mixDeep_closes_outermost` mentions `HarnessStill`, `EntryStill`, `CoreVia`
or `MachineClosesAt`, or does not mention `MachineDefines`; and if
`mixDeep.machine_design_noPortsNR2_closed` exists.

The conclusion is about the CORE run, because that is where the closing
premise is consumed: `MachineClosesAt` speaks of the machine synthesis, and
the built consumers reach it from the core run of the full entry
(`machine_run_of_core` / `machine_children_realA`,
`Tools/ShippingChildRun.lean` 462–526: `closes b _ _ _ (invW …) (depthPos …)
hrun`). `mixDeep_closes_outermost` gives, for the one run, what that
application gives: the machine synthesis returned `some`.

## 2. PROVED (written) vs. NOT shown

| statement | state |
|---|---|
| `core_reads_val0`, `coreVia0_of` | PROVED (written), from `RefLaws` + built lemmas |
| `cnt_entryOk`, `mid2_entryOk` | PROVED (written), reflections only |
| `mixDeep_closes_prov` | PROVED (written): no fall-back from `Prov` worlds, four reflections |
| `mixDeep_closes_outermost` | PROVED (written): OUTERMOST starts only |
| `MachineClosesAt mixDeep` (every `InvW` world of positive depth) | **NOT shown**, and not refuted (§3) |
| `mixDeep.machine_design_noPortsNR2_outermost` | NOT written: not a direct application (§3) |

## 3. The existing premise `MachineClosesAt mixDeep`: false somewhere, or true and out of reach?

**What a counter-world would be.** `MachineClosesAt` quantifies over every
world with `InvW` and a positive depth. `InvW`'s cache half is `CacheInv`:
each entry is a `RealChild` — the result of SOME returning run of the real
entry of its key from SOME invariant world, in SOME contexts
(`Tools/ShippingChildInv.lean` 451–463). Take a start world whose cache is

    mid2 ↦ y₂     with  M₁ ∈ y₂.2.modules,  M₁.name = ofDecl midH
    midH ↦ y_H    with  y_H.1 = M_H,          M_H.name = ofDecl midH,   M₁ ≠ M_H

The harness of `mixDeep` leaves the cache (`mixDeep_harnessStill`); the
closing's `mapM` gets `y₂` and `y_H` as HITS (`synthesizeChild_post`,
BUILT); `designWith` keeps the FIRST visited module named `ofDecl midH`
(`Sparkle/IR/Machine.lean` 302–305) — `M₁` or `M_H`, by the order of the
call entries — and the closing's own check that every child module and
every module of a child's design resolves to ITSELF in the joined design
(the last `children.all …` conjunct of `closeInstsG`,
`Sparkle/IR/MachineInstG.lean`) fails for the other one: `closeInstsG`
returns `none`, the machine synthesis returns `none`. So in THAT world the conclusion of
`MachineClosesAt mixDeep` is false.

**Is that world admissible?** It is iff `CacheInv` admits the two entries,
i.e. iff there are `RealChild mid2 y₂` and `RealChild midH y_H` as above.
`y₂`'s `midH` module is the result of a real compile of `midH` (the built
kid facts of `mid2` on `RealChild`; its closing took a real child). So the
world exists iff

    ¬ Det midH,   where  Det c := ∀ y y', RealChild c y → RealChild c y' → y.1 = y'.1

(and the same question for `rcH`, whose module both designs hold). Under
the reflections the endpoint carries (`MachineDefines midH`, `EntryDefines
rcH`, for every world and — by `….ctx` — every context) every real compile
of `midH` takes the machine route on the same shape with a real `rcH`
child, so `Det midH` comes down to: the certified harness returns the same
MODULE for the same `(declName, binders, body)` from every world.

**What is built says nothing either way.** The soundness of the walk fixes
the returned module's meaning and shape (`transition_facts`,
`closedBody_kinds_of_run`: value, ports, statement kinds, name), not the
module itself; no theorem states `Det`, and none refutes it. By READING it
holds: nothing a world can vary enters the builder's output — wire names
come from the builder's counter and the hints (`CompilerM.makeWire`), the
translation cache is a fresh ref per harness run (`IO.mkRef`, 2962), the
fresh variable ids are only keys of the reader's map, the clock values go
to the log. I cannot exhibit two different real compiles of `midH`, and no
test can (a test builds real worlds; two runs of one declaration there
return equal modules as far as anything observed says).

**So: (ii), not (i) — with the qualification that (ii) is by reading.**
`MachineClosesAt mixDeep` is true if `Det midH` and `Det rcH` hold, and
they hold by reading; it is NOT provable by the cache-provenance route for
nested starts, because that route needs a history of the start cache that
`CacheInv` does not record. The two candidate next steps therefore are not
the two the question lists but three:

1. **A second endpoint FORM for `mixDeep` with the depth-0 start** — what
   `mixDeep_closes_outermost` supports. It needs the consumers restated
   (below). Scope: outermost runs.
2. **The determinism route**: prove `Det c` for machine / gate declarations
   in the fragment — "the harness's result is a function of its arguments".
   It is a RESULT-level walk (the builder state after the translator as a
   function of the body), a third pass over the same induction as
   `fuel_contract_leaves` / `walk_still`; with it `Agree` holds for EVERY
   `CacheInv` cache and `MachineClosesAt mixDeep` follows at its PRESENT
   scope, with no cache history at all. This is the only route I see that
   removes the premise from the existing endpoint as it stands.
3. **The invariant route (par/a-35-aux)**: does not reach nested starts
   either (`aux` is not part of `InvW` / `ChildBnd`); for outermost starts
   it gives nothing this branch does not already give for `mixDeep`.

**Why the built endpoint cannot be applied to `mixDeep_closes_outermost`.**
`mixDeep.machine_design_noPortsNR2` takes `closes : MachineClosesAt mctx
mref cctx cref mixDeep shape` — a statement about every world — and hands
it on unchanged: `Tools/ShippingKidFacts.lean` `kids_runFacts` (128–134),
`kids_outsCheck` (157–164), `kids_maskedN` (188–192), `kids_designCheck`
(222–251), each of which passes `closes` to further lemmas
(`… hB hcore hpost entry closes …`) down to the one place it is USED, the
application at the run's machine-synthesis world in `machine_children_realA`
/ `machine_run_of_core`. A depth-0 endpoint form needs those four and the
lemmas between them and that application restated with, instead of
`closes`, the fact it yields for the run: "the machine synthesis this core
run performs returned `some`" (the conclusion of `coreVia0_of`). I did not
read the intermediate lemmas one by one; the list of what takes `closes` as
an argument is `grep -n closes` over `Tools/ShippingKidFacts.lean` and the
files it calls. Not done in this round, by instruction.

## 4. Build queue (integrator)

`lakefile.lean` (not edited):

    lean_lib «Tools.ShippingCacheCoherentOuter» where
      roots := #[`Tools.ShippingCacheCoherentOuter]

`Tests/AllTests.lean`: nothing (target-only test).

Order: (1) `Tools.ShippingCacheCoherentOuter` (imports
`Tools.ShippingCacheCoherentVia`); (2)
`Tests.Compiler.MixDeepOutermostTest` (imports `CacheChainClosedTest`,
`CallsKidsSharedMixDeepTest`).

## 5. UNVERIFIED, in risk order

1. `wfrag` of `mid2`'s and `mixDeep`'s packed terms (`decide`; by reading
   they use the constructors `cnt` / `midH` use, which are `true`), and the
   two position conditions per machine.
2. `mixDeep_closes_prov`: `apply mixDeep.closes_shared <;> assumption` (the
   generated theorem's binders); `hout_of_data … (nDecl := 1)` with three
   `decide`s (for `mid2`: `nDecl := 2`, as `mid2_kid` decides them).
3. `core_reads_val0`: `peel_e` through the clear block (the clone of
   `peel_inv` with `invE_clear` at the cache's `set`); the `finally` at
   depth 0 (three shapes tried).
4. `cnt_entryOk`: `seqChild_of_real cnt.machineData cnt.machine_ok
   cnt.machine_body rfl (by decide) hRc (fun mc cc => cnt.machine_closes mc
   _ cc _) hy` (the argument forms of `Tests/Compiler/ChecksRawTest.lean`
   115–116) and its fields `name`, `design`.
5. `mid2_entryOk`: `EntryOk.mono` by dot notation; the `rcases` on the key
   set; the name inequality by `decide`.
6. `coreVia0_of`: the text of `coreVia_of` (BUILT) with `hclose`.

## Integrator's build record (2026-10-13)

BUILT on tree `23774b6c972f5337a17c2c7d4e62a063c10ae3f3` (poc 20ab638e + these files), cgrun 3 GiB swap 0, run `a38` (exit 0, peak 0.84 GB),
worker's files unchanged, FIRST ATTEMPT: `Tools.ShippingCacheCoherentOuter`,
`Tests.Compiler.MixDeepOutermostTest` (target-only). Printed by the test: `cnt_entryOk`, `mid2_entryOk`,
`mixDeep_closes_prov`, `mixDeep_closes_outermost` on `[propext, Classical.choice, Quot.sound]`; the
statement check passed (none mentions `HarnessStill`, `EntryStill`, `CoreVia`, `MachineClosesAt`; no
`mixDeep.machine_design_noPortsNR2_closed` exists).

WHAT THIS IS: for an OUTERMOST core run of `mixDeep` (`L.dval w = 0`, with `sval` and `quiet` — the
depth-0 disjunct of `ChildBnd` for a named witness), the machine synthesis it performs returns `some`
(the closing succeeds), from the reflections of `mixDeep`, `mid2`, `midH`, `rcH`, `cnt` only.
The chain initial (cache cleared ⇒ `Prov`) → preserved (`EntryOk` of each callee) → consumed
(`machine_closes_of_entryOk` with the built `mixDeep.closes_shared`) is explicit and has no underived
hypothesis.
WHAT THIS IS NOT: the endpoint `mixDeep.machine_design_noPortsNR2` has NOT lost its premise
`MachineClosesAt mixDeep` — that premise quantifies over every invariant world of positive depth, and the
endpoint's consumers take it in that form. `mixDeep` stays OPEN in the census. Whether the all-worlds
premise is true at nested starts is undecided (it needs determinism of the shared descendants' compiles).

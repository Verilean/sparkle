# B — slotless leaves as entries at the design level: the route, what is missing, the open endpoint, a measurement (round par/b-32)

Branch `par/b-32` from `poc/roundtrip-proof` 35208d70. Worker B.

**NOTHING HERE IS BUILT OR RUN.** No `lean`, `lake` or simulator was started.
Every Lean file is WRITTEN, NOT BUILT. **No design-level endpoint of the
final goal's form is produced for any slotless declaration, and none is
claimed**: the answer to the round's question is (b) — the refusal reflects
missing theorems. What is written is the part that IS derivable (an OPEN
endpoint with two named obligations) and a measurement that will say, per
declaration, which missing theorem it needs.

Marks: **[R]** read at 35208d70; **[B]** built per the integration records
(not re-run); **[M]** measured by the integrator's build of 35208d70;
**[P]** PREDICTED.

## 0. Commits and files

| unit | commit | files |
|---|---|---|
| 1 | 6b6f2d48 | `Tools/ShippingLeafSweepExpect.lean` (new); the twelve `Tests/Compiler/LeafSweep{Closes,Entry,Crypto256,Uart,Loop,LoopIP,Nest,Norm,Raw,Tele,Fuse,Regs}Test.lean` (assertions appended) |
| 2a | 64dff297 | `Tools/ShippingCombLeafDesign.lean` (new) |
| 2b | b6a7075d | `Tools/ShippingCombLeafCommand.lean` (new); five `Tests/Compiler/CombSweep{Raw,ApplicativeA,ApplicativeB,Comb,SignOps}Test.lean` (new, target-only) |
| 3 | the commit after b6a7075d | this file |

No existing generator, theorem or statement was changed. Unit 1 edits twelve
test files (appends only).

## 1. Unit 1 — the measured class asserted

`#leaf_sweep_expect f "CLASS" ["reason"]` reads the row `#leaf_sweep f` left
and is an error when the class differs, when a GENERATED row's audit is not
`OK` / it has a NOT ALLOWED line / `f.machine_design_leaf0` is absent, or
when a refusal's reason does not contain the text. Appended to the twelve
files in `AllTests`: `"GENERATED"` for the 48 names of the build record
(taken from `docs/parallel/B-leaf-sweep.md` by script; the script asserts
that the 48 names of the record are exactly the swept names that are not the
two refusals), `"REFUSED" "has calls"` for `hftByte`, `"REFUSED" "memory"`
for `withMemory`. Each assertion is its own command (one failure does not
hide the others). The three `Slotless…` sweep files are unchanged.

`lakefile.lean`: `lean_lib «Tools.ShippingLeafSweepExpect» where roots := #[`Tools.ShippingLeafSweepExpect]`.

Risk: `r:(str)?` as an optional syntax argument of `elab`; the reason
strings against the scan's actual texts ("has calls [...] — a parent …",
"memory: call entries … are memories …" [R
`Tools/ShippingLeafEntryCommand.lean` 198–199]).

## 2. The route of the 32, and why they are refused

### 2.1 The route — machine route with no slot, for all 32

[M] all 32 were REFUSED with the reason "slotless". [R] that refusal
(`Tools/ShippingLeafEntryCommand.lean` 162–202) is reached only after (i)
`Tools.ShippingMachineCommand.readMachine f` SUCCEEDED — the declaration is
on the machine route, not the gate / mixed / legacy route (a gate-route
declaration is refused earlier, "not a machine declaration", as `plain` is
in `LeafDesignFamilyTest`); (ii) the shape has NO call entry (else "memory" /
"has calls"); (iii) `shape.layout.slots = []`. So, measured: **all 32 are
machine-route declarations with no call and no register** (the machine route
at K ≥ 0 hardware `let`s and zero slots). None is a gate-route declaration;
the gate-route theorems (`#gate_child`, `gate_real_kidK`) do not apply to
them as entries.

Their endpoints today [R `Tools/ShippingMachineCommand.lean` 2590–2664]:
`f.machine_sound` (head `machine_trace_of_comb` when the generator took the
combinational head), `f.machine_ships` (gates as premises), and — when the
head is `machine_trace_of_comb` — `f.machine_ships_comb`. Whether
`f.machine_ships_comb` exists for each of the 32 is a build fact I do not
have (the scan logs it in its `LEAFDESIGN DATA` line: "In the environment").

### 2.2 The ship-level endpoint and its three check antecedents

[R `Tools/ShippingMachineShipsComb.lean` 202–235] `machine_ships_comb`:
under `∃ raw`, for every `wof`,

    simpleBody b = true →
    seqCheck wof (weOf wof) (checkedOptimize b).body = true →
    ((seqNames (checkedOptimize b).body).all fun n => declWidth (checkedOptimize b) n == weOf wof n) = true →
    MachineShipsComb f d (dropZeroWidthModule raw) (checkedOptimize b) wof dom src

For a REGISTER leaf the three antecedents of `machine_ships_wired` are
discharged from the run by `leaf_entry_textChecks_closed` [B], because the
compiler guards that branch twice with `printOk`. For a slotless leaf the
compiler takes OTHER branches [R `Sparkle/IR/RefineCheck.lean` 260–275,
387–402]:

| step | register leaf | slotless leaf |
|---|---|---|
| `mergeChecked m` | `refineCheck && masksKept && printOk r && !(all isAssign)` else `m` | body assignment-only: `mergeDuplicates m`, NO print guard |
| `checkedOptimize m`, `simpleBody m` | never (a register is not simple) | `optCheck m o && assignmentOrderCheck o.body` else `m`; `optCheck`'s print conjunct is `!moduleCheck m ‖ (moduleCheck o && inputWidthsAgree m o)` — it binds only inside the uniform-width gate fragment |
| `checkedOptimize m`, not simple | `refineCheck m o && printOk o` else `m` | the same branch — but there is NO slotless ship-level theorem for it |

### 2.3 What is missing, exactly

**(S1) `simpleBody b = true`** for the full entry's module of a slotless
machine. [R] the only theorem concluding `simpleBody` is the scalar route's
(`Tools/ShippingPostSoundness.lean` 685 `simpleBody_of`, from
`SimpleStmts`); for a closed machine the built facts are about WIDTHS
(`TypedIn`, `Tools.ShippingLeafEntryBnd.leaf_run_typedIn_bnd`), not about
the shapes of right-hand sides. Two ways out, neither written:
(a) a theorem "the transition's and `closeMachine`'s assignments are of the
simple shape" (about `translateExprToWire`'s emission and `outAssigns`);
(b) a slotless ship-level theorem for the NON-simple branch — the analogue
of `machine_ships` (`Tools/ShippingMachineShipping.lean`) without a reset
input: `machine_ships_wired` cannot be used, it asks `slots ≠ []` and uses
it for `"rst" ∈ inputs` and for a register statement [R
`Tools/ShippingMachineShipsW.lean` 55, 83–106].

**(S2) the text of the SHIPPED module on the simple branch**:
`checkedOptimize b = b ∨ printOk (checkedOptimize b) = true`. On the
register branch this is `checkedOptimize_instFree_print` [B]. On the simple
branch the compiler has no such guard. Ways out:
(a) the guard, in `Sparkle/IR/RefineCheck.lean` 389–390 (NOT edited — out of
my scope): `if optCheck m o && assignmentOrderCheck o.body && printOk o then
o else m`; with it (S2) is the lemma `checkedOptimize_instFree_print`
restated for `simpleBody m = true`;
(b) without a compiler change: [B] `checkedOptimize b = b` whenever
`simpleBody b` and the body has a slice / concatenation / NOT
(`Tools.ShippingControlOptSoundness.checkedOptimize_cast` 102) or a
comparison (`checkedOptimize_control` 59). [R] `closeMachine` drives every
output by a slice of the packed wire (`docs/parallel/A-comb-kids.md`,
quoted in `Tools/ShippingCombKidText.lean` 62–75), so (S2) would follow
from (S1) plus "the full entry's module of a machine has a slice
assignment" — again a fact about shapes, of the same kind as (S1a).

**(S3) several outputs, or one output not named `out`**: the text of
`mergeDuplicates m`. [B] for the one output `out`:
`Tools.ShippingCombKidText.mergeChecked_text_out`. For several outputs the
`TypedIn` statement is FALSE (an output can become an alias of another
output) and the true statement is about `outAssigns`
(`docs/parallel/A-comb-kids.md` §2.3). Not written.

So the missing theorems are ONE family: the SHAPE of the statements of a
closed machine module (simple right-hand sides; an output slice; distinct
output slices). `TypedIn` does not carry it.

### 2.4 Groups, by reading of the bodies

All: machine route, no call, no slot [M]. "one output" = the result type is
one `Signal`; the port NAME `out` is [P] (the machine route names the one
output of a `Signal` result `out`: [B] `ShippingMachineLoopTest` (the route check before its endpoints) asserts
`["out"]` for its register declarations; not asserted for these).

| group | declarations | body [R] | outputs | (S1) [P] | (S2) [P] | (S3) |
|---|---|---|---|---|---|---|
| A. lifted 4-bit arithmetic | `ApplicativeSemanticsTest.` `reversed`, `reversedSurface`, `nestedSurface`, `constantRight`, `constantLeft`, `duplicate`, `withConstant`, `nested`, `rightAssociated`, `permutedFour` (10) | `-`, `+`, `^^^` on `BitVec 4`, a constant `3#4` (12–30) | one [B: `check` asserts `m.outputs.length == 1`, 34] | true: binary operators of `isBinOp` on references, constants | true by the output slice | not needed |
| B. lifted, a NOT / concatenation / comparison | `….complement` (`~~~`), `concatReverse` (`++`, 8-bit result), `orderedLess` (`BitVec.ult`, `Bool` result) (3) | 24–28 | one [B] | true: `.op .not [.ref]`, `.concat [.ref,.ref]`, `lt_u` are simple shapes | true (a cast or a control statement besides the slice) | not needed |
| C. negation, bundle projections, tuple inputs | `ShippingMachineRawTest.` `negSig`, `negLift` (`-a`, read as `0 - x`), `addThree`, `useHalf`, `triBundle` (`bundle2/3` then projections), `tupFst`, `tupMapFst`, `tupSum`, `tupHwLet3` (a tuple-typed input: ONE packed port, projections are slices) (9) | 24–80 | one | true [low confidence: the projections' slices / concatenations must be of the listed forms `slice (ref)`, `concat [ref, ref]`] | true | not needed |
| D. byte tables / mux trees | `ShippingMachineCombTest.pickByte` (slices, `^^^`, `+`, `===`, three `mux`); `Sparkle.IP.Net.HTTP.httpGetByte` (18 constants, a mux tree on a 6-bit counter); `Sparkle.IP.Net.IPv4.ipv4HeaderByte` (a deep mux tree); `Sparkle.IP.Net.IPv4.ipv4HeaderChecksumSig` (an adder tree with carries) (4) | `ShippingMachineCombTest.lean` 20–27; `IP/Net/HTTP.lean` 86; `IP/Net/IPv4.lean` 163, 213 — the IP bodies were NOT read beyond their signatures | one | true for `pickByte`; the three IP bodies NOT PREDICTED | true if (S1) | not needed |
| E. sign operations | `ShippingSignOpsTest.` `sext` (`signExtend 16`), `ashrK` (`sshiftRight x 10`), `shiftSurface` (`sshiftRight x y.toNat`, lifted), `ashrSig` (`Signal.ashr`), `scaleMul` (two `signExtend 80`, an 80-bit `*`, `extractLsb' 24 32`); `Sparkle.IP.YOLOv8.Primitives.Requantize.requantize` (6) | `ShippingSignOpsTest.lean` 14–28; `Requantize.lean` 60 (signature only) | one | NOT PREDICTED. The machine route reads sign extension and arithmetic shifts through `Sparkle/Compiler/MachSignOps.lean` (`signExtend (k+w) x ↦ fill k (msb x) ++ x`, 6–13); `.op .asr` is NOT a simple shape (`isPrintBinOp` = `isBinOp ‖ shr ‖ shl`, `OptCheck.lean` 31–38) — whether an `.asr` statement is emitted on this route I did not determine | if (S1) false: the `refineCheck` branch — (S2) holds there by the built guard, and what is missing is the ship-level theorem (S1b) | not needed |

So, by reading: for groups A–C and `pickByte` (23 declarations) the
obstacle is that (S1) and (S2) are TRUE but UNPROVED (the shape theorem);
for group E it may be the missing non-simple ship-level theorem; for the
three IP declarations of D not predicted. The sweep measures exactly this.

## 3. What is written

### 3.1 `Tools/ShippingCombLeafDesign.lean`

```lean
structure CombKid (c : Name) (dk : MachineData) : Prop   -- ok, body, calls, dom, leaf,
    -- slots : dk.shape.layout.slots = [], ss : dk.ss.length = 0, outTy,
    -- one : dk.shape.layout.outs.map (·.name) = ["out"], outName, outScalar

theorem comb_entry_text_out … (hbnd : ChildBnd mref cref w) (hr : RunsTo (synthesizeCombinational c) …)
    (entry) (closesM) (hon) (hoty) (hbout : b.outputs.map (·.name) = ["out"]) :
    seqCheck (wofOf b) (weS b) b.body = true ∧
      (seqNames b.body).all (fun x => declWidth b x == weS b x) = true

theorem seedR_of_inputs (h : o.inputs = m.inputs) (ins) : seedR o ins = seedR m ins

theorem comb_design_of_ships (hs : o.body.all seqStmtOk = true) (hpost : b = raw ∨ b = mergeChecked raw)
    (h : MachineShipsComb declName d raw o (wofOf o) dom src) :
    ∃ ids, … ∃ cache, ∀ i bools bits T ins st0 mems, (four use conditions) →
      ∃ envsO, runModule … = some envsO ∧ (∀ C kids, DesignSV C 0 o (seedR b ins) T ⟨st0, mems, kids⟩ envsO) ∧
        envsO.length = T ∧ (the source on the outputs) ∧ (∀ C kids envs', DesignSV … envs' → envs' = envsO)

theorem comb_entry_outputs (soundL) (hnoI) (houtTy) (hr) (entry) (closes) :
    b.outputs.map (·.name) = d.shape.layout.outs.map (·.name)

theorem comb_entry_design0_out (d : MachineData) (soundL) (K : CombKid declName d)
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines …) (closes : MachineCloses …) :
    ∃ raw, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
      (ChildBnd mref cref w →
       simpleBody b = true →                                                    -- (S1) OPEN
       (checkedOptimize b = b ∨ Sparkle.IR.PrintGuard.printOk (checkedOptimize b) = true) →  -- (S2) OPEN
       ∃ ids, ids.Nodup ∧ ids.length = d.shape.binders.length ∧ ∃ cache,
         ∀ i bools bits T ins st0 mems (kids : String → KT 0),
           (SourceInputs … (seedR b ins t st)) →
           (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
           (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) →
           Bounded (weS (checkedOptimize b)) st0 →
           (∃ envsO, DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedR b ins) T ⟨st0, mems, kids⟩ envsO ∧
               envsO.length = T ∧ (the source on the outputs))
           ∧ ∀ envs', DesignSV … envs' → envs'.length = T ∧ (the source on the outputs))
```

How: `machine_ships_comb` [B] for `hships`; the output names from the wired
trace (`comb_entry_outputs`, the destructuring of `machine_ships_comb`'s own
proof); the text of `b` by `leaf_run_typedIn_bnd` [B] (it does not ask a
slot: `Tools/ShippingLeafEntryBnd.lean` 69–86) and `mergeChecked_text_out`
[B]; the text of the shipped module by `text_shipped_of_print` [B] from (S2);
`DesignSV` and the uniqueness by `designSV0_of_leaf` /
`designSV0_leaf_unique` [B].

Against `f.machine_ships_comb`: conclusion `DesignSV` + "every closed run
shows the source"; `ChildBnd` ADDED (allowed); the two text antecedents
(`seqCheck`, the width agreement, at every `wof`) GONE; `simpleBody b = true`
STAYS; (S2) is NEW. Two NOT ALLOWED premises against three.

Against `f.machine_design_leaf0` (register leaves): the same shape and the
same allowed premises; additionally (S1), (S2); no register list, no
start-register conditions, no `rst` condition; the seeding is `seedR b ins`
(the inputs, `rst` low) — `machine_ships_comb`'s own, not `seedIn`.

(S1) and (S2) are not renamings of the conclusion: each is a Boolean fact
about the module the run returned, decided by evaluation on a concrete
module, and §2.3 names the theorem each one waits for.

### 3.2 `Tools/ShippingCombLeafCommand.lean`

* `#machine_comb_design f` — `f.machine_combKid`, then
  `f.machine_design_comb0_open` (the term above; `soundL` is argument 7 of
  the VALUE of `f.machine_ships_comb`, which must be `machine_ships_comb` on
  11 arguments). Its statement check (`checkOpen`) ASSERTS: no checker /
  `seqCheck` / `seqNames` / `MachineCloses` / `InvW` constant; exactly the
  run and `MachineDefines f` as proposition binders; exactly three
  antecedents under `∃ raw` — `ChildBnd` (ALLOWED), one mentioning
  `simpleBody`, one mentioning `printOk` (NOT ALLOWED); `DesignSV` over
  `childMap`. Standard axioms of the three constants. Refusals: file header.
* `#comb_sweep f` — never an error: `COMBSWEEP START` (also stderr); the
  MEASUREMENT on the real module (`COMBSWEEP MODULE f: …`); the generator's
  data, premise lines, class and reason; `COMBSWEEP RESULT`.
* `#comb_sweep_summary` — rows, counts, the declarations with (S1) false /
  (S2) false / (S2) not given by a built theorem; an error only on an
  inconsistency of what the file measured.

### 3.3 The five sweep files (target-only)

| file `Tests/Compiler/…` | imports | n |
|---|---|---|
| `CombSweepRawTest` | `ShippingMachineRawTest` | 9 (group C) |
| `CombSweepApplicativeATest` | `ApplicativeSemanticsTest` | 7 (group A) |
| `CombSweepApplicativeBTest` | `ApplicativeSemanticsTest` | 6 (A: 3, B: 3) |
| `CombSweepCombTest` | `ShippingMachineCombTest` | 4 (group D) |
| `CombSweepSignOpsTest` | `ShippingSignOpsTest` | 6 (group E) |

## 4. PREDICTED outcome per declaration (nothing below is measured)

`#comb_sweep` class [P]: GENERATED (the OPEN endpoint) for a declaration
whose `f.machine_ships_comb` exists, whose output is named `out` and whose
`f.machine_closes` is derivable; else REFUSED with the reason. I predict
GENERATED for the 23 of groups A–C and `pickByte`, and do NOT predict the
three IP declarations of D and group E (their `machine_ships_comb` and
`machine_closes` are not known to me).

Measurement [P]: (S1) true and (S2) true (by the output slice) for groups
A–C and `pickByte`; group E and the IP declarations not predicted.

In every case the PREDICTED number of design-level endpoints of the final
goal's form produced by this round is **0**.

## 5. For the integrator

`lakefile.lean` (not edited):

```lean
lean_lib «Tools.ShippingLeafSweepExpect» where
  roots := #[`Tools.ShippingLeafSweepExpect]

lean_lib «Tools.ShippingCombLeafDesign» where
  roots := #[`Tools.ShippingCombLeafDesign]

lean_lib «Tools.ShippingCombLeafCommand» where
  roots := #[`Tools.ShippingCombLeafCommand]
```

`Tests/AllTests.lean`: nothing to add (the twelve edited sweep files are
already imported; the five `CombSweep…` files are target-only).

Build order:

1. unit 1: `Tools.ShippingLeafSweepExpect`, then `Tests.AllTests` (the
   twelve files). Expected log: 50 lines `LEAFSWEEP EXPECT f: … as measured`.
2. `Tools.ShippingCombLeafDesign` (imports the built
   `Tools.ShippingLeafDesign`, `Tools.ShippingCombKidText`).
3. `Tools.ShippingCombLeafCommand`.
4. `Tests.Compiler.CombSweepRawTest` first (the smallest bodies), then the
   other four, one target at a time.

How to read the log:

    grep -E "COMBSWEEP (START|MODULE|RESULT|ROW|SUMMARY)|COMBDESIGN (GENERATED|REBUILT|REFUSED|FAILED)"

* `COMBSWEEP MODULE f: … (S1) simpleBody b = …; (S2) … holds on this run: …;
  … by the BUILT checkedOptimize_cast / _control: …` — which obstacle the
  declaration has: (S1) false → the non-simple ship-level theorem (§2.3
  S1b); (S1) true, "by the BUILT …" true → only the SHAPE theorem is
  missing; (S1) true, (S2) false → the optimizer changed a simple module
  and the result does not pass the print guard: a compiler guard is needed
  (§2.3 S2a) — that would be a FINDING;
* `COMBDESIGN REFUSED f: (S3) …` / `no f.machine_ships_comb …` / `not
  machine_ships_comb on 11 arguments …`: out of this command's scope;
* `COMBDESIGN FAILED f: …`: a generated proof or the statement check failed;
* `COMBDESIGN GENERATED f` / `COMBSWEEP RESULT f: GENERATED — the OPEN
  endpoint …`: `f.machine_design_comb0_open` exists, with the two NOT
  ALLOWED obligations listed in the `COMBDESIGN PREMISE … NOT ALLOWED (OPEN)`
  lines.

What may be recorded after a green build: "the OPEN endpoint
`f.machine_design_comb0_open` exists for ⟨list⟩: premises the run,
`MachineDefines f`, `ChildBnd`, and two NOT ALLOWED obligations (S1), (S2);
measured on one run each: ⟨…⟩". NOT: "a slotless leaf has a design-level
endpoint", and not "(S1) / (S2) hold" (one evaluated run is not a proof).

## 6. Risks (unbuilt), in order

1. `comb_entry_outputs`: the destructuring of `MachineTraceL` / `MachineWired`
   by anonymous patterns, copied from the built proof of `machine_ships_comb`
   (lines 241–243); then `rw [hbo, ho, houts]` and a small induction for
   `(L.map (fun o => ⟨o.name, o.ty⟩)).map (·.name) = L.map (·.name)`.
2. `comb_entry_design0_out`: `c2' := c2`, `c3' := c3` rely on
   `weS o = weOf (wofOf o)` by unfolding (the built register proof relies on
   the same in `leaf_entry_textChecks_bnd`); `rw [K.slots]` then `exact K.ss`
   for `d.ss.length = d.shape.layout.slots.length`.
3. `comb_design_of_ships`: `have htext : TextRun o … := hsv` (the built
   register bridge does the same with `MachineShips`' clause).
4. `endpointTerm`: argument positions 1 and 6 of `f.machine_ships_comb`'s
   value; `mkAppM` with six explicit arguments, the wired trace among them.
5. `combKidTheorem`: eleven fields by `decide` / `rfl` on reflected data
   (`leafKidTheorem` [B] is the model; `one`, `slots`, `ss` are new).
6. `measure`: runs the real entry inside a command; `checkedOptimize b == b`
   (`BEq` on modules, as `ShippingControlOptSoundnessTest` 56 [B]); the
   environment and messages are restored afterwards, the compiler's caches
   are not.
7. `checkOpen` recognises (S1) / (S2) by the printed text of the antecedent
   containing `simpleBody` / `printOk`.
8. Two `initialize … IO.Ref` tables in two modules (the pattern built in
   `ShippingLeafSweepCommand`).

## 7. What I could not determine by reading

* Whether `f.machine_ships_comb` exists for each of the 32 (the scan's DATA
  line of the b-31 build says; I do not have those logs).
* The output port NAME of each (predicted `out`).
* (S1) for groups C (partly), D (the IP bodies) and E; whether an `.asr`
  statement is emitted on the machine route.
* Whether (S2) can actually FAIL on a real module (a simple module the
  optimizer changes into one that does not pass `printOk`): by reading the
  optimizer falls back on every body with a slice, and every closed machine
  module has one — so predicted not, but that is the unproved shape fact.
* The bodies of `ipv4HeaderByte`, `ipv4HeaderChecksumSig`, `httpGetByte`,
  `requantize` beyond their signatures and doc comments.
* Kernel cost of `f.machine_combKid`'s decides on `ipv4HeaderByte` /
  `ipv4HeaderChecksumSig` (large bodies).

## Integrator's build record (2026-10-13) — MEASURED

BUILT on tree `f0aae8d3a1f2c2b6206c8e633f0b7b42b00a9fb4` (poc 5693c63a + these files), cgrun 3 GiB swap 0, run `b32` (exit 0, peak 0.97 GB),
worker's files unchanged, first attempt: `Tests.AllTests` 1308 jobs green with 50 `LEAFSWEEP EXPECT … as
measured` lines (48 GENERATED, `hftByte` has calls, `withMemory` memory — now asserted per declaration);
`Tools.ShippingCombLeafDesign`, `Tools.ShippingCombLeafCommand`; the five `CombSweep…` files (target-only,
2–4 s each; logs in `~/sparkle-work/comb-sweep/`).

Slotless sweep over the 32: the OPEN endpoint `f.machine_design_comb0_open` GENERATED for 26, REFUSED for
6 (the sign-operation group and `requantize`: "`machine_ships_comb`: not machine_ships_comb on 11
arguments — a transported endpoint or another construction: not handled"), FAILED 0.
An OPEN endpoint has two NOT ALLOWED antecedents, (S1) and (S2): it is NOT a check-free endpoint and is
not counted. Design-level endpoints of the final goal's form for slotless leaves: 0.

Measured on ONE run of the real entry per declaration, all 32 (including the 6 refused): (S1)
`simpleBody b = true`; `checkedOptimize b == b`: true; `printOk (checkedOptimize b)`: true. No case of
(S1) true with (S2) false. An evaluation of one run, not a proof.

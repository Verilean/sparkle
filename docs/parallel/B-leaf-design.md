# B — the leaf `MachineShips` → `DesignSV` connection: the general bridge and `cnt` as one unit (round par/b-27)

Branch `par/b-27` from `d287f2ac`. **WRITTEN, NOT BUILT** — nothing below is
removed or proved until the integrator builds it. No existing file changed.

Marks: **[R]** read in a file of `d287f2ac`; **[B]** built on `d287f2ac`
(per the round's STATE); **[I]** inferred, not checked by a build.

## 0. Files

| file | content |
|---|---|
| `Tools/ShippingLeafDesign.lean` | the general bridge: `post_ports`, `declWidth_of_wires`, `textRun_unique`, `designSV0_leaf_text`, `designSV0_leaf_unique`, `leaf_design_of_ships`, `leaf_design0_of_checks`, `leaf_entry_design0_of_wired`, `leaf_entry_design`, `leaf_entry_design_all` |
| `Tools/ShippingLeafDesignCommand.lean` | `#machine_leaf_design f`, `#machine_leaf_design_try f "GENERATED\|REBUILT\|REFUSED\|FAILED"`; `endpointTerm`, `checkStatement(With)`, `inner`, `audit`, `sweep` |
| `Tests/Compiler/LeafDesignCntTest.lean` | `cnt.machine_design_leaf0` by hand over the bridge; the command's compare path (`REBUILT`, `isDefEq`); audit by the parents' tools |
| `Tests/Compiler/LeafDesignFamilyTest.lean` | `acc`, `pe`, `twoHW`, `toggle`, `loopPair`, `toggleL` GENERATED and audited; four REFUSED |

## 1. The route: the parents' head does NOT degenerate — `MachineShips` + `designSV0_of_leaf`

Question of the task: can `machine_design_noPorts` / `machine_design_svH_free`
be instantiated with `insts = []`?  **No**, and not because a clause is
vacuous:

* **[R]** `Tools/ShippingNoPorts.lean` 86–92: the head's hypothesis `hFacts`
  must give `Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b`.
  **[R]** `Tools/ShippingGuardsSound.lean` 314–322: its first field is
  `gate : hierGate b = true`. **[R]** `Sparkle/IR/RefineCheck.lean` 196–200:
  `hierGate m = m.body.any isInst && …`. On a body without an instance this
  is `false`: `hFacts` cannot be supplied.
* **[R]** the head's proof is `design_at_free … (machine_ships_hierC_at_free
  …)`: the branch of `checkedOptimize` for instance-bearing modules
  (`hierBinds` → `hierRefineCheck`, else the `hierGate` fallback,
  `RefineCheck.lean` 394–400). **[R]** an instance-free assign + register
  module that is not of simple shape takes the branch of lines 391–392
  (`refineCheck m o && printOk o`). Different branch, different proof.
* **[R]** the data theorems the parents' generators feed the head ask
  `d.shape.insts ≠ []` and `d.shape.instFields ≠ []` (`hins`, `hfne` of
  `core_portsMatch_raw_leaf`, `Tools/ShippingPortsMatchRawLeaf.lean`), and
  `composed` asks `ComposedG` (the composition with the children).

`KidFacts` over an empty range would be vacuous, `callsOk` holds; the
obstruction is `hierGate` and the branch. So the route is the one a leaf's
module actually takes: `MachineShips` (**[B]** `leaf_entry_ships_closed`, or
its pieces `machine_ships_wired` + `leaf_entry_textChecks_closed`) and
**[B]** `designSV0_of_leaf`.

## 2. The precise relation between `MachineShips` and `DesignSV` for a leaf

**[R]** `MachineShips f d raw b o wof dom src`
(`Tools/ShippingMachineShipping.lean` 62–102), under its ten use conditions,
gives ONE `envsO` with

  (a) `runModule (declWidth o) o.body (seedIn raw ins) T st0 mems = some envsO`;
  (b) `∃ pairs regs' mprog, emitAssigns wof o.body = some pairs ∧ emitRegs … ∧
      emitMemWrites … ∧ runModuleSV wof pairs regs' mprog (seedIn raw ins) T
      st0 mems = some envsO`;
  (c) `envsO.length = T`; (d) the source on the output ports.

**[R]** `TextRun m seed T st mems envs` (`Tools/ShippingDesignSVLeaf.lean`
25–31) is clause (b) at `wof := wofOf m`. So at the emitter's own width map
(what `f.machine_ships_leafC` states) **clause (b) IS `TextRun o (seedIn raw
ins) T st0 mems envsO`, by unfolding** [I: `have htext : TextRun … := hsv`].

**[R]** `DesignSV C 0 o seed T s envs` (`Tools/ShippingDesignSV.lean` 80–88)
is `TextRun o (oracle C o.body (envAt envs T) seed) T s.st s.mems envs ∧
Resolved C o.body ∧ PortsMatch C o ∧ (per-instance clause)`. For
`o.body.all seqStmtOk`:

* **[B]** `designSV0_of_leaf`: `TextRun o seed … → DesignSV C 0 o seed …`
  (`oracle_seq`: the oracle seeding is the seeding; the three instance
  clauses quantify over `Stmt.inst … ∈ o.body`, empty);
* **NEW** `designSV0_leaf_text`: the converse, `DesignSV C 0 o seed T s envs
  → TextRun o seed T s.st s.mems envs` (first conjunct, `oracle_seq`).

So for a leaf, **`DesignSV C 0 o seed T ⟨st0, mems, kids⟩ envs` ⟺ `TextRun o
seed T st0 mems envs`**, for every `C` and every `kids`. And **NEW**
`textRun_unique`: `TextRun` is functional in `envs` (the three emitters and
`runModuleSV` are functions returning `Option`).

Consequences, stated exactly:

| | `MachineShips` at `wofOf o` (`machine_ships_leafC`) | parents' conclusion form at depth 0 | leaf, here |
|---|---|---|---|
| IR run of the shipped module, same `envsO` | YES (a) | not stated | `leaf_design_of_ships`, `leaf_entry_design_all`: YES; `machine_design_leaf0`: not stated |
| a closed run of the emitted text showing the source exists | YES as (b)+(d), not in the form `DesignSV` | YES | YES, for EVERY child map |
| EVERY closed run from the same seeding and states shows the source | not stated | YES (from `design_sv_backN`: needs `designCheck`, `outsCheck`, width conditions) | YES — from `textRun_unique`; NO width premise, no check |
| seeding | `seedIn (dropZW raw) ins` | `seedIn b ins` | `seedIn b ins` (`mergeChecked_ports`) |

**Earlier finding, confirmed and sharpened**: "`DesignSV C 0` of an
instance-free module adds only vacuous clauses; `MachineShips` says more".
What `MachineShips` says more is (a). What the design-level form says more
is the uniqueness half — which is a THEOREM of the emitted-text semantics
for a leaf, not extra content of the compiler run.

## 3. The design-level endpoint of an entry without calls (item 1)

    f.machine_design_leaf0 :
      ∀ {mctx mref cctx cref w w' b design}
        (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
        (entry : MachineDefines mctx mref cctx cref f f.machineData.shape),
        ∃ raw,
          (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
          (ChildBnd mref cref w →
            ∃ ids, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
            ∃ cache regs, regs.Nodup ∧ regs.length = d.ss.length ∧
              ∀ i bools bits T ins st0 mems (kids : String → KT 0),
                (∀ t st, t < T → SourceInputs f d.bsIn ids cache
                  (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
                  (seedIn b ins t st)) →
                (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
                (∀ t, ins t "rst" = 0) →
                (∀ k r f, regs[k]? = some r → d.shape.layout.slots[k]? = some f → st0 r = f.init) →
                (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
                (∀ r ∈ seqRegs b, st0 r.1 < 2 ^ declWidth b r.1) →
                (∀ r ∈ seqRegs (dropZeroWidthModule raw),
                  st0 r.1 < 2 ^ declWidth (dropZeroWidthModule raw) r.1) →
                (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) →
                Bounded (weS (checkedOptimize b)) st0 →
                (∃ envsO,
                  DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedIn b ins) T
                    ⟨st0, mems, kids⟩ envsO ∧
                  envsO.length = T ∧
                  ∀ j hj k q f, d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
                    envsO[j] q.name = f j)
                ∧ ∀ envs', DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedIn b ins) T
                      ⟨st0, mems, kids⟩ envs' →
                    envs'.length = T ∧
                    ∀ j hj k q f, d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
                      envs'[j] q.name = f j)

(`d` is `f.machineData`; `dom`, `src` are those of `f.machine_ships_wired`.)

Premises: exactly the run, `MachineDefines f` (binders), `ChildBnd` (the one
antecedent under `∃ raw`, where the parents' closed endpoints have it —
**[R]** `docs/parallel/verification-b14.md` 87).

### The returned design `D` of a leaf entry, and `childMap D.modules`

* **[R]** `Sparkle/Compiler/Elab.lean` 5546–5560
  (`synthesizeCombinationalWith`): the entry returns `(mergeChecked m', top
  mergeChecked (top dropZeroWidthModule d))` (or without the merge under
  `SPARKLE_NO_REGDEDUP`), `d` the CORE design; `top g` maps `g` over the
  modules of `d` named like the top module.
* **[B]** `Tools.ShippingChecksDerived.leaf_run_seqOk` (via
  `seqChild_iface`): for a machine without calls the returned design has NO
  module, `design.modules = []` — proved under `InvW`, which is NOT an
  allowed premise; there is no `ChildBnd` form. So: **[I]**
  `childMap design.modules = fun _ => none` (`moduleByName [] _ = none`),
  not the module itself. This is NOT used and NOT stated in the endpoint.
* It is not needed: the conclusion holds for EVERY child map
  (`leaf_design0_of_checks C`, `leaf_design_of_ships`: `∀ C kids`). The
  endpoint instantiates the returned design's.

### Differences from a parent's depth-0 endpoint — all of them

1. `∃ raw`, not `∃ raw D`: a parent's `D` is the CORE run's design (a
   witness of `synthesizeCombinational_checked`), the one that holds its
   children. Here the child map is the RETURNED design's (a binder). A
   consumer that wants the literal `∃ raw D, P ∧ (Bnd → …)` gets it with the
   witness `design` (nothing to prove); and any other `D` from
   `leaf_design0_of_checks`.
2. use conditions — common: source inputs on the seeding, registers pass,
   `rst` low, start registers at the reset values, inputs within
   `declWidth b`, start registers of `b` within `declWidth b`, inputs within
   the emitted widths, `Bounded (weS (checkedOptimize b)) st0`.
   Absent (a parent has them; not needed): `seedIn b ins t st "clk" = 0`,
   `Reset raw D kids`, the bound on `openIns b`, `InvN` of the instances'
   states; `SourceInputs` is on `d.bsIn` and the inputs themselves, not
   `d.bsIn.take kD` on the inputs extended by calls.
   **EXTRA**: the start registers of `dropZeroWidthModule raw` within its
   declared widths. A parent has no such line because **[R]** an
   instance-bearing module is never merged (`mergeChecked_inst`, `b = raw`);
   a leaf may be, and `refineCheck_transfer` across the merge
   (`machine_ships`, `hfitRaw`) needs it. `MachineShips`' own condition,
   kept verbatim — not hidden.
3. `MachineShips` has two INPUT conditions over `raw.inputs`. The one at
   `declWidth raw` is DISCHARGED from the one at `declWidth b`:
   `b.inputs = raw.inputs` and `b.wires = raw.wires` (**[R]**
   `mergeChecked_ports`), `declWidth` reads `Module.wires` only (**[R]**
   `Sparkle/IR/RegDedup.lean` 172–176). The one at the emitted widths is
   restated over `b.inputs` (the same list). The leaf endpoint has nine use
   conditions, `machine_ships_leafC` ten.
4. `kids` is quantified as in the parents; nothing reads it.

## 4. New theorems (`Tools/ShippingLeafDesign.lean`)

    theorem post_ports {b r} (h : b = r ∨ b = mergeChecked r) :
        b.inputs = r.inputs ∧ b.wires = r.wires
    theorem declWidth_of_wires {m o} (h : o.wires = m.wires) : declWidth o = declWidth m
    theorem textRun_unique (h1 : TextRun m seed T st mems envs)
        (h2 : TextRun m seed T st mems envs') : envs = envs'
    theorem designSV0_leaf_text (C) (hs : o.body.all seqStmtOk = true)
        (h : DesignSV C 0 o seed T s envs) : TextRun o seed T s.st s.mems envs
    theorem designSV0_leaf_unique (C) (hs : o.body.all seqStmtOk = true)
        (h1 : TextRun o seed T st mems envs)
        (h2 : DesignSV C 0 o seed T ⟨st, mems, kids⟩ envs') : envs' = envs
    theorem leaf_design_of_ships (hs : o.body.all seqStmtOk = true)
        (hpost : b = raw ∨ b = mergeChecked raw)
        (h : MachineShips declName d raw b o (wofOf o) dom src) :
        ∃ ids, … ∃ cache regs, … ∀ i bools bits T ins st0 mems, (the nine use conditions of §3) →
          ∃ envsO,
            runModule (declWidth o) o.body (seedIn b ins) T st0 mems = some envsO ∧
            (∀ C kids, DesignSV C 0 o (seedIn b ins) T ⟨st0, mems, kids⟩ envsO) ∧
            envsO.length = T ∧ (the source on the outputs) ∧
            ∀ C kids envs', DesignSV C 0 o (seedIn b ins) T ⟨st0, mems, kids⟩ envs' → envs' = envsO
    theorem leaf_design0_of_checks (C) {A : Prop}
        (hships : the conclusion of machine_ships_wired)
        (hchk : A → the three checks at wofOf (checkedOptimize b))
        (hs : A → (checkedOptimize b).body.all seqStmtOk = true) :
        ∃ raw, (b = … ∨ b = …) ∧ (A → the body of §3 at C)
    theorem leaf_entry_design0_of_wired (hships : …)
        (K : LeafKid mctx mref cctx cref c dk)
        (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w') :
        ∃ raw, (b = … ∨ b = …) ∧ (ChildBnd mref cref w → the body of §3 at childMap design.modules)
    theorem leaf_entry_design (d) (soundL : …) (K : LeafKid … declName d) (hr : RunsTo …) :
        the same conclusion                    -- the general bridge
    theorem leaf_entry_design_all (d) (soundL : …) (K : LeafKid … declName d)
        (hbnd : ChildBnd mref cref w) (hr : RunsTo …) :
        ∃ raw, (b = … ∨ b = …) ∧ the conclusion of leaf_design_of_ships
               at dropZeroWidthModule raw, b, checkedOptimize b

`leaf_entry_design` is the task's `LeafKid → ChildBnd → RunsTo → …` with
`ChildBnd` as the antecedent under `∃ raw` instead of a binder — because the
witness `raw` comes from `machine_ships_wired` (which needs no boundary) and
the parents' shape has the boundary there; with `ChildBnd` as a binder the
strongest form is `leaf_entry_design_all`. `soundL` is the wired twin of the
declaration's endpoint, as in `leaf_entry_ships_closed`.

No hypothesis renames a conclusion: `hships` is the stated conclusion of the
BUILT `machine_ships_wired`, `hchk` / `hs` those of the BUILT
`leaf_entry_textChecks_closed` / `leaf_entry_shipped_seq_closed`; the
generator and `leaf_entry_design0_of_wired` supply all three.

## 5. Generator and name

`#machine_leaf_design f` → `f.machine_design_leaf0`
`:= fun hr entry => leaf_entry_design0_of_wired (f.machine_ships_wired hr
entry (f.machine_closes mctx mref cctx cref)) (f.machine_leafKid entry) hr`.

Name: the parents' depth-0 names are `machine_design_sv0`, `…svR0`,
`…noPortsR0`, `…noPortsR0_closed` — `machine_design_` + a stage of the
parents' head + depth (+ `_closed`). A leaf has no head stage and no open
form; `machine_design_` + `leaf` + `0`. No clash (`grep`).

Reused by import: `Tools.ShippingLeafEntryCommand.scan` (scope + refusal
lines: not a machine / memory / has calls / slotless / no endpoint / no
`machine_ships_wired`), `Outcome`, `forbidden`, `checkConsts`;
`closesTheorem?`; `leafKidTheorem`; `addOrCompare` (compare path: existing
name ⇒ rebuilt, added as `_regen`, statements `isDefEq`, else an error).
The command does NOT need `f.machine_ships_leafC`.

`checkStatement` before adding: exactly two proposition binders (`RunsTo`,
`MachineDefines f`), exactly one existential, exactly one antecedent under
it and it is `ChildBnd`, 0 NOT ALLOWED; none of `simpleBody`, `seqCheck`,
`seqNames`, `MachineCloses`, `InvW`, `printOk`, `isAssign`, `portsMatchB`,
`kidsPass`, `designCheck`, `shipsHierCheck`, `outsCheck`, `kidsMaskedN`,
`hierCheck`; the conclusion mentions `DesignSV` and `childMap`.

The shape `∃ raw, P ∧ (A → C)` is what `#machine_goal_gap_of`
(`Tools.ShippingFinalGoalCommand.analyse`: any number of existentials) and
`Tests.Compiler.NoPortsTest.premiseLines` read **[R]**. So the tests audit
the leaf endpoint with the SAME tools as the parents': the gap theorem
`f.machine_design_leaf0_gap` must have no `gap_…` hypothesis (`ChildBnd` is
ALLOWED and witness-free: hoisted as `kid_0`), `premiseLines` 0 NOT ALLOWED,
none of `NoPortsTest.checkers`.

## 6. Endpoint — premise — predicted state (all [I] until built)

| endpoint | against | premise | predicted |
|---|---|---|---|
| `cnt.machine_design_leaf0` (hand) | `cnt.machine_ships_wired` | `simpleBody b = false`, `seqCheck …`, the `seqNames` width agreement | gone (as in `machine_ships_leafC`) |
| | | `MachineCloses cnt` binder | gone (`cnt.machine_closes`) |
| | `cnt.machine_ships_leafC` | use condition "inputs of raw within `declWidth raw`" | gone (from the one about `b`) |
| | | use condition "inputs of raw within the emitted widths" | stays, restated over `b.inputs` (the same list) |
| | | use condition "start registers of raw within `declWidth raw`" | STAYS |
| | | the run, `MachineDefines cnt`, `ChildBnd` | stay (`ChildBnd` moves from a binder to the antecedent under `∃ raw`) |
| | | conclusion | `MachineShips` (IR run + text run + source) → `DesignSV (childMap design.modules) 0` exists + every closed run shows the source; the IR-run clause is NOT in it |
| `cnt.machine_design_leaf0_regen` (command) | the hand one | — | statement `isDefEq` |
| `acc`, `pe`, `twoHW`, `toggle`, `loopPair`, `toggleL` `.machine_design_leaf0` | as `cnt` | as `cnt` | GENERATED, same premises |
| `pickByteH`, `parent`, `memCounter`, `plain` | — | — | REFUSED (slotless / has calls / memory / not a machine), nothing left |

No premise is added anywhere; nothing counts as removed until built.

## 7. What `machine_design_leaf0` gives that `machine_ships_leafC` did not — and what it does not

Gives: (1) the conclusion in the parents' object `DesignSV (childMap
design.modules) 0 (checkedOptimize b)`, in the parents' endpoint shape —
leaves and parents can be consumed and audited uniformly; (2) "EVERY closed
run from the same seeding and states shows the source"; (3) the parents'
seeding `seedIn b ins`; (4) one use condition fewer (nine against ten).

Does NOT give: (i) anything new about the VALUES — the closed run is clause
(b) of `MachineShips`; (ii) the IR run of the shipped module (dropped from
this form; kept by `leaf_entry_design_all`); (iii) `design.modules = []`
under allowed premises; (iv) the SV string, parse-back, `#sim`; (v) a
slotless leaf (`machine_ships_comb`: refused, unchanged); (vi) removal of
the pre-merge start-register condition; (vii) a use of this endpoint AS A
CHILD's fact by a parent (the parents' `LeafRun` clause of `DesignSV` at
depth 0 is discharged by `leaf_forward`, not by this).

## 8. A sweep over the remaining ≈ 48 register leaves — NOT run

`Tools.ShippingLeafDesignCommand.sweep (names : List Name)`: per name the
`LEAFDESIGN DATA` line and the outcome line, then one `LEAFDESIGN SWEEP`
line with the four classes; asserts nothing.

How: one target-only file (NOT in AllTests) importing the test files of
`A-leaf-gen.md` §5 and `Tests.Compiler.LeafDesignFamilyTest`, with

    set_option maxHeartbeats 0 in
    run_cmd Tools.ShippingLeafDesignCommand.sweep [``…, …]

* the names: the GENERATED / REBUILT list of the `#machine_leaf_entry` sweep
  (`A-leaf-gen.md` §6) — the two commands have the SAME scope scan and need
  the same three constants (`machine_ships_wired`, `machine_closes`,
  `machine_leafKid`); a declaration in one class there is predicted in the
  same class here [I].
* leave out the seven of this round or expect: the six family declarations
  REBUILT; `cnt` FAILED ("the compare path was run twice": its `_regen`
  exists).
* if the leaf-entry sweep file is imported, `machine_leafKid` exists and is
  reused; otherwise this sweep GENERATES `f.machine_leafKid` (and
  `f.machine_closes`) — then the two sweep files must not both be in one
  import closure.
* cost per declaration [I]: one application of
  `leaf_entry_design0_of_wired`; the kernel re-checks the stored statement
  of `f.machine_ships_wired` against the bridge's hypothesis (the same
  text) and instantiates a statement about three times the size of
  `machine_ships_leafC`'s; `collectAxioms` on three constants. No `decide`
  beyond `leafKidTheorem`'s.
* run through `cgrun.sh`, serial.

## 9. Integrator

`lakefile.lean` (after `Tools.ShippingLeafEntryCommand`):

    lean_lib «Tools.ShippingLeafDesign» where
      roots := #[`Tools.ShippingLeafDesign]

    lean_lib «Tools.ShippingLeafDesignCommand» where
      roots := #[`Tools.ShippingLeafDesignCommand]

`Tests/AllTests.lean` (after `import Tests.Compiler.LeafEntryFamilyTest`):

    import Tests.Compiler.LeafDesignCntTest
    import Tests.Compiler.LeafDesignFamilyTest

Names added: `Tools.ShippingLeafDesign.*` (ten theorems),
`Tools.ShippingLeafDesignCommand.*`, tokens `#machine_leaf_design`,
`#machine_leaf_design_try`; per declaration `f.machine_design_leaf0`,
`f.machine_design_leaf0_gap` (seven), `cnt.machine_design_leaf0_regen`.
`grep`: none of these exists at `d287f2ac`. No file has `ModuleName` in its
name; nothing about module naming is touched (worker A).

Build order: `Tools.ShippingLeafDesign` → `Tools.ShippingLeafDesignCommand`
→ `Tests.Compiler.LeafDesignCntTest` → `Tests.Compiler.LeafDesignFamilyTest`
→ `Tests.AllTests`.

## 10. Risks, most likely first (all in files of this round)

1. `leaf_design_of_ships`: `rw [e] at hsrc hpass` / `rw [e]` (`e : seedIn b
   ins = seedIn raw ins`) — if `rw` does not find the instance under the
   binders, replace by stating the theorem over a seeding `sd` with `hsd : sd
   = seedIn raw ins` and `subst`.
2. `declWidth_of_wires`: `unfold declWidth; rw [h]` on a `match` over
   `o.wires.find? …` (fallback: `simp only [Sparkle.IR.RegDedup.declWidth, h]`).
3. `designSV0_leaf_text`: `obtain ⟨h1, -⟩ := h` on `DesignSV C 0 …` (the
   built `design_sv_backN` destructs it the same way in its `zero` case).
4. `designSV0_of_leaf C hs (s := ⟨st0, mems, kids⟩) htext`: the named
   argument and the projection-of-constructor unification.
5. `endpointTerm`: `mkAppM leaf_entry_design0_of_wired #[ships, kidP, hr]` —
   the same unification as the built `leaf_entry_ships_of` on `ships`; new:
   `c`, `dk` from `kidP`, and the two `b` must agree.
6. `inner` / `checkStatementWith`: Meta code written against the built
   `innerAntecedents` and `checkStatement`; the structure `Inner`.
7. the hand term of `LeafDesignCntTest` (syntax quotation, as the built
   `LeafEntryCntClosedTest` §2).
8. `loopPair` / `toggle` / `toggleL`: GENERATED is predicted from the built
   leaf-entry family (same inputs); a FAILED there would be a unification
   difference in item 5.
9. Long lines (> 100 columns) in generated statement text of
   `Tools/ShippingLeafDesign.lean` — style only.

## Build record (integrator, 2026-10-13)

Verified tree `da3968872d89ba987dd6cff9235dc3746c6427d4` = poc d287f2ac + par/b-27 (8a11f742, worker files unchanged) + two `lean_lib` entries + two
imports in `Tests/AllTests.lean`. Everything built at the first attempt. cgrun 3 GiB, swap 0.
- `20261013-160831-b27-tests`: `lake build Tools.ShippingLeafDesign Tools.ShippingLeafDesignCommand Tests.Compiler.LeafDesignCntTest Tests.Compiler.LeafDesignFamilyTest ` — result=success, memory_peak_file=824500224; Build completed successfully (622 jobs).
- `20261013-160919-b27-alltests`: `lake build Tests.AllTests` — result=success, memory_peak_file=438222848; Build completed successfully (1281 jobs).

Established — the DESIGN-level endpoint of a leaf register machine as an entry, `f.machine_design_leaf0`, for
`cnt` (by hand over the general bridge, and REBUILT by the command: `isDefEq`) and for `acc`, `pe`, `twoHW`,
`toggle`, `loopPair`, `toggleL` (generated by `#machine_leaf_design`): two proposition binders — the run and
`MachineDefines f` — and one antecedent under `∃ raw`, `ChildBnd`; 0 NOT ALLOWED; none of `simpleBody`,
`seqCheck`, `seqNames`, `MachineCloses`, `InvW`, `printOk`, `isAssign`; goal-gap theorems with no gap
hypothesis (the same classifier as the parents'); standard axioms. Conclusion in the parents' depth-0 form:
`DesignSV (childMap design.modules) 0 (checkedOptimize b) …` has a closed run that shows the source, and
EVERY closed run shows the source. `pickByteH`, `parent`, `memCounter`, `plain` REFUSED with reasons.

Route: `MachineShips` + `designSV0_of_leaf` (the parents' head cannot be instantiated without an instance:
`hierGate b` needs one). General bridge theorems in `Tools/ShippingLeafDesign.lean`: `textRun_unique`,
`designSV0_leaf_text`, `designSV0_leaf_unique`, `leaf_design_of_ships`, `leaf_entry_design`,
`leaf_entry_design_all`.

Scope: one declaration each; a leaf register machine as an entry; depth 0; decided data conditions; the
runtime boundary; `DesignSV` of the module list, not the SV string, not `#sim`. Stays as a use condition of
the conclusion (not a compiler check): the start registers of the pre-merge module within their widths.
Slotless leaves are not covered; the other ≈ 48 register leaves predicted in scope were not run.

```
:140:0: LEAFDESIGN REBUILT Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt: REBUILT Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_design_leaf0: statement isDefEq the existing one (proof kept as Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_design_leaf0_regen). 
:170:0: LEAFDESIGN AUDIT OK Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_design_leaf0: exactly two proposition binders (the run, MachineDefines Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt) and one antecedent under ∃ raw (ChildBnd), 0 NOT ALLOWED; none of [Sparkle.IR.O
ean:144:0: LEAFDESIGN AUDIT OK Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_design_leaf0: exactly two proposition binders (the run, MachineDefines Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc) and one antecedent under ∃ raw (ChildBnd), 0 NOT ALLOWED; none of [Spa
ean:144:0: LEAFDESIGN AUDIT OK Sparkle.Tests.Compiler.MultiInstance.pe.machine_design_leaf0: exactly two proposition binders (the run, MachineDefines Sparkle.Tests.Compiler.MultiInstance.pe) and one antecedent under ∃ raw (ChildBnd), 0 NOT ALLOWED; none of [Sparkle.IR.OptCheck.simpleBod
ean:144:0: LEAFDESIGN AUDIT OK Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoHW.machine_design_leaf0: exactly two proposition binders (the run, MachineDefines Sparkle.Tests.Compiler.ShippingMachineEntryTest.twoHW) and one antecedent under ∃ raw (ChildBnd), 0 NOT ALLOWED; none of [S
ean:144:0: LEAFDESIGN AUDIT OK Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle.machine_design_leaf0: exactly two proposition binders (the run, MachineDefines Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle) and one antecedent under ∃ raw (ChildBnd), 0 NOT ALLOWED; none
ean:144:0: LEAFDESIGN AUDIT OK Sparkle.Tests.Compiler.ShippingMachineLoopTest.loopPair.machine_design_leaf0: exactly two proposition binders (the run, MachineDefines Sparkle.Tests.Compiler.ShippingMachineLoopTest.loopPair) and one antecedent under ∃ raw (ChildBnd), 0 NOT ALLOWED; none o
ean:144:0: LEAFDESIGN AUDIT OK Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL.machine_design_leaf0: exactly two proposition binders (the run, MachineDefines Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL) and one antecedent under ∃ raw (ChildBnd), 0 NOT ALLOWED; no
ean:144:0: LEAFDESIGN FAMILY AUDIT: [Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc: no gap hypothesis, 11 binders and antecedents listed, 0 not allowed,
ean:171:0: LEAFDESIGN REFUSED Sparkle.Tests.Compiler.ShippingMachineLinkedTest.pickByteH: slotless: no register slot (LeafKid.slots asks shape.layout.slots ≠ []). Its ship-level endpoint is Sparkle.Tests.Compiler.ShippingMachineLinkedTest.pickByteH.machine_ships_comb, which asks simpleB
ean:173:0: LEAFDESIGN REFUSED Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent: has calls [Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt, Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt] — a parent, not a leaf (LeafKid.leaf asks shape.insts = []). The generators for it: #machi
ean:175:0: LEAFDESIGN REFUSED Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter: memory: call entries [SparkleMem.combo.4.8] are memories — a certified-route memory is an INSTANCE of a memory-only submodule, so Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter 
ean:177:0: LEAFDESIGN REFUSED Sparkle.Tests.Compiler.ShippingMachineCommandTest.plain: not a machine declaration — the machine reader says: Sparkle.Tests.Compiler.ShippingMachineCommandTest.plain: a combinational gate takes it, not the machine route. (A declaration the certified gate co
```

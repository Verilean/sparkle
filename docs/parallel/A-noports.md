# A / G1: the depth endpoint with no compiler-check premise (round par/a-4)

Branch `par/a-4`, base poc `533a9822`. NOTHING here was built: every file was
written by reading sources. All statements below are PREDICTIONS until the
integrator's build returns.

## What was added

| file | content |
|---|---|
| `Tools/ShippingPortsMatchShippedLeaf.lean` | `core_portsMatch_shipped_leaf`: `portsMatchB (childMap D.modules) (checkedOptimize b) = true` under exactly the hypotheses of `core_portsMatch_raw_leaf` (composition with `portsMatchB_shipped`; the gate from `core_hierGate`, as `core_text_shipped` does) |
| `Tools/ShippingNoPorts.lean` | `machine_design_noPorts`: script copy of `machine_design_noKids`, the `portsMatchB` antecedent removed from `hDesign` and from the conclusion |
| `Tools/ShippingNoPortsCommand.lean` | `#machine_no_ports f n`, `#machine_no_ports_try f n`, `sweep n names` |
| `Tests/Compiler/NoPortsTest.lean` | the command on `parent 1`, `chained 1`; gap theorems; throwing assertions; premise lists |
| `Tests/Compiler/NoPortsSweepTest.lean` | logs only: the command over `HierBindsCensusTest.candidates` |

Generated per declaration `f` (children `c`): `c.machine_leafKid`,
`f.machine_portsG`, `f.machine_designP{n}`, `f.machine_design_noPortsNR{n}`,
`f.machine_design_noPortsNR{n}_closed` (and, by `#machine_goal_gap_of`,
`…_closed_gap`).

## Predicted premise list of `parent.machine_design_noPortsNR1_closed`

To be compared with the `NOPORTS PREMISE` lines of the build log.

    data binders: mctx mref cctx cref w w' b design
    hr     : RunsTo (synthesizeCombinational ``parent) mctx mref cctx cref w (b, design) w'
    entry  : MachineDefines mctx mref cctx cref ``parent parent.machineData.shape
    hR0    : MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape     -- from parent.machine_closes_at
    under ∃ raw D, (b = … ∨ b = …) ∧ :
      Bnd  : ChildBnd mref cref w ∧ MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape

`chained`: the same with `chained`. The exact conjunct structure of `Bnd` is
whatever `chained/parent.machine_ships_hierNR1` was generated with (it was
not read off a build); the generator only needs `ChildBnd` and the children's
reflections to be conjuncts of it. If `parent.machine_closes_at` carries a
name-separation premise (`hparent` / `hnames` / `hfresh`: they are discharged
by `decide` when the candidate renderings separate, which is expected for
`parent` / `cnt`), the test THROWS and names it.

## What the empty gap means — and what it does not

(i) **Data conditions the generator discharges by `decide`** (per
declaration; a failing one is an error of the command, the declaration is
then not covered):

* parent `f`, in `f.machine_portsG` (names of the hypotheses of
  `core_portsMatch_shipped_leaf`): `hC` (`callsOk nDecl`), `hslots`, `hdomB`,
  `hins` (`insts ≠ []`), `hfne` (`instFields ≠ []`), `outTy`, `hnomem`,
  `hsl` (`layout.slots ≠ []`), `hcw` (`callWidthsOk d nDecl (fun k => (kid
  k).shape.layout.outs)`), `hargs` (`callArgsOk d nDecl (fun k => declWidths
  (kid k))`), `hon` (output names, character-wise `charOk` then
  `sanitizeName_of_clean`), `hoty` (`scalarTy`), and in `hkid`: every
  entry's callee is the called declaration (`hall`);
* child `c`, in `c.machine_leafKid` (fields of `LeafKid`): `calls`, `dom`,
  `leaf` (`rfl`), `slots`, `ss`, `outTy`, `outName`, `outScalar`;
* and those of the generators called before: `f.machine_runFacts`,
  `f.machine_outsG{n}`, `f.machine_maskedG`, `f.machine_designG{n}`,
  `f.machine_designK{n}`, `f.machine_closes_at`.

(ii) **Compiler guards the result depends on.** The theorems are about the
compiler WITH these guards: the fallback of `checkedOptimize` to the input
module (gate holds, check does not bind), and the five guards on a kept
candidate — distinct instance names, design-free linked order, `printOk` of
the candidate's text, masked outputs stay masked under a register merge
(`mergeChecked`, itself print-guarded), `connsKept` (connected wires keep
their declared width). Nothing here says how often a guard fires (censuses:
0 real declarations so far) or that the optimizer's own output is correct
without them.

(iii) **What the conclusion is about.** `DesignSV (childMap D.modules) n
(checkedOptimize b) …`: the emitted-text semantics of the shipped module
over the children's modules of the run's design — a statement about the
module LIST. Not about the printed SV string, not about parsing it back,
not about a simulator. `#sim` is outside (it optimizes twice; `SimIndexTest`
shows its input numbering disagrees with the JIT C).

(iv) **Scope.** Parents with a register whose callees are all leaf register
machines; depth 1; instances: `parent`, `chained`. Refused with a reason:
no machine endpoint, no call, parent without a register, a callee that is a
memory child / has no machine endpoint / has calls of its own / has no
register, no depth endpoint `f.machine_ships_hierNR{n}`.

(v) **Standing runtime assumptions.** `ChildBnd` (the child cache's laws,
`RefLaws`, at the start world) and the reflections `MachineDefines` are
premises. Conditional: no model of the Lean runtime, no proof that an actual
elaborator run satisfies `RunsTo` / `ChildBnd`.

## NOT done

* Nothing built; no error returned yet.
* Multi-callee `kid` (`List.getD`) path is written but has NO instance in
  the tests (`parent` and `chained` both call only `cnt`).
* Parents of children with calls (depth ≥ 2), memory children, gate
  children, parents without a register: out of scope, refused.
* The SV string, the writer's text, `#sim`: untouched.
* The sweep is a prediction (2 of 27); not measured.

## Build queue (suggested order)

1. `Tools.ShippingPortsMatchShippedLeaf`
2. `Tools.ShippingNoPorts`
3. `Tools.ShippingNoPortsCommand`
4. `Tests.Compiler.NoPortsTest`
5. `Tests.Compiler.NoPortsSweepTest`

`lakefile.lean` (integrator):

    lean_lib «Tools.ShippingPortsMatchShippedLeaf» where
      roots := #[`Tools.ShippingPortsMatchShippedLeaf]

    lean_lib «Tools.ShippingNoPorts» where
      roots := #[`Tools.ShippingNoPorts]

    lean_lib «Tools.ShippingNoPortsCommand» where
      roots := #[`Tools.ShippingNoPortsCommand]

`Tests/AllTests.lean` (integrator):

    import Tests.Compiler.NoPortsTest
    import Tests.Compiler.NoPortsSweepTest

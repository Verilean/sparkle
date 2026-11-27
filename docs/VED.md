# VED: per-circuit proofs that the synthesised IR matches the Signal source

This is the developer page for `#verify_elab_deep` ("VED") and the `#ved_*` entry commands.
It describes what is supported today, which Check file tests each shape, and where each shape
stops. Results per IP row are in [research/Coverage327.md](research/Coverage327.md); the public
introduction is [research/README.md](research/README.md). The working notes this page replaces
(the `VED-*.md` pages) are kept as development records in [../notes/ved/](../notes/ved/); you do not
need to read them.

## What VED is

A VED entry takes one Lean declaration `f` written with `Signal` / `circuit do`, synthesises it
**once** with `synthesizeCombinational` (the function `#synthesizeVerilog` calls), and returns
the module (and, for hierarchies, the design) only together with a kernel-checked theorem
`f.ved_u1` saying that the returned IR computes the declaration's value: for every input stream
in range and every cycle, each output port equals the matching projection of `f`.

The statement is about the IR **returned by that synthesis run** (`f.ved_mod`, `f.ved_design`),
under the IR semantics of `Sparkle/IR/Semantics.lean` with reset held at 0. It is order-free:
`OutputsStmt` speaks about every arrangement of the body in which each wire is assigned before it
is read (`runModule_perm`, `Sparkle/IR/ReorderInvariance.lean`); the module itself is not
reordered. It is not about the optimised IR or the printed SystemVerilog.

`#verify_elab_deep f` is the deep preparation: it reifies the `circuit do` body into a deep
embedding (`Cdo`) and proves `f_deep_trace` and the related facts from the general theorem
`Cdo.elab_general`. Several entries reuse these facts.

## How to run it

```lean
import Tools.VedU1Entry
#ved_u1 delay8                  -- synthesise, prove, kernel-check, strict audit
#print axioms delay8.ved_u1
```

| Command | Use it for | Statement | File |
|---|---|---|---|
| `#verify_elab_deep f` | deep facts (`_deep_trace`, `_deep_next`, `_deep_inits`, `_deep_out`) used by other entries | `Cdo.elab_general` instance | `Tools/DeepElab.lean` |
| `#ved_u1 f` | single module: combinational bodies, `Signal.loop` registers, a `×`-tree or structure of output signals | `U1Stmt` | `Tools/VedU1Entry.lean` |
| `#ved_u1_deep f` | single module with k ≥ 1 registers, after `#verify_elab_deep f` | `U1Stmt` | `Tools/VedU1Deep.lean` |
| `#ved_u1_packed f` | result `Signal d (A × B)` (one packed port) | `PackedStmt` | `Tools/VedU1PackedEntry.lean` |
| `#ved_u1_struct f` | result that is a structure of signals | `U1Stmt` over the bundled fields | `Tools/VedU1StructOut.lean` |
| `#ved_u1_mem f`, `#ved_u1_mem_packed f` | single module with memories | `MemStmt` | `Tools/VedMemEntry.lean` |
| `#ved_u1_hier f` | parent with combinational children (H1) | `U1HStmt` | `Tools/VedU1HierEntry.lean` |
| `#ved_u2_hier f` | parent with child instances, with or without parent registers | `U2HStmt` / `U2HRStmt` (`U2HRStmtK` with `ved.compose.multiOut`) | `Tools/VedU2HierRegEntry.lean` |
| `#ved_write_checked KIND f "x.sv" "x_cppsim.h" [wires]` | check once, then write the SV / C++ / JIT files from exactly the checked design (`KIND` ∈ `u1`, `packed`, `mem_packed`, `u1_hier`, `u2_hier`) | the kind's theorem plus a design-equality guard | `Tools/VedWriteChecked.lean` |
| `#ved_strict_audit d`, `#ved_axioms_raw d` | audit a declaration's reachable axiom closure | | `Tools/VedStrictAudit.lean` |
| `#ved_mem_classify f` | print the memory and instance statements of the returned design (read-only) | | `Tools/VedMemClassify.lean` |

The `#ved_*_write` adapters (`Tools/VedWriteForms.lean`, `Tools/VedInvocation.lean`) run an
entry with its own synthesis and write nothing; only `#ved_write_checked` ties the checked
artifact to the written files (byte comparison in `Tests/Ved/WriteCheckedCheck.lean`).

The VED tools and Checks are `lean_lib` targets in `lakefile.lean` and are not default targets:
build them by name, for example `lake build Tests.Ved.U1EntryCheck`. CI
(`.github/workflows/ved.yml`) has two jobs: `ved-pr` (representative Checks, on pull requests
that touch the compiler, the VED tools or their tests) and `ved-full` (every VED Check, weekly
and on demand). Build times and the CI layout are in [research/BuildAndCI.md](research/BuildAndCI.md).

## Accepted and refused

An entry **accepts** (`VED U1 OK …`, `VED U2 HIER OK …`) only when all of these hold:

1. the generated proof elaborates against the full expected type, built from the original
   declaration constant and the registered module/design constants;
2. the kernel checks it synchronously, and the stored type is compared with `==` against the
   rebuilt expected type;
3. the strict audit accepts its axiom closure.

Otherwise it **refuses** with `VED U1 REFUSED f [stage]` (or the U2 form) and restores the
saved state, so no `ved_*` constant is left behind. Stages, in order: `table` (the declaration's
type is not readable as a port table), `multi-output` / `packed` (result shape not handled by
this entry), `synthesis`, `artifact`, `hier-shape`, `clkrst`, `order` (no admissible arrangement:
combinational cycle, self-read, undriven read, duplicate driver, write to an input), `scope`,
`conns`, `child`, `open`, `deep`, `type`, `proof` (the generated proof did not check within the
budget), `kernel`, `checker`, `audit`. A refusal is never turned into an acceptance of a weaker
statement, and budgets are not raised to make a row pass. When `f` has a leading implicit
`DomainConfig` binder, the theorem is about `@f defaultDomain` and the OK line says so.

## Trust base

The trusted parts are the Lean kernel, the statement definitions (`U1Stmt`, `PackedStmt`,
`MemStmt`, `U2HStmt`, `U2HRStmt`, and the IR semantics they unfold to) and the strict audit
`#ved_strict_audit`, which accepts only `propext`, `Classical.choice` and `Quot.sound` and rejects
`native_decide` (`Lean.ofReduceBool`) and `bv_decide` auxiliary axioms; name patterns are never
let through. Generators, tactics and the compiler are untrusted: they can make an entry refuse,
not accept a false theorem. The IR replay of `#verify_elab_deep` (`_deep_signal_run` and its
lemmas) uses `native_decide` and is **not** strict; "axioms clean" in its `PROVEN` message is not a
strictness claim. The options `sparkle.deepNoNative` and `sparkle.deepNoReplay`, set by the
checkers, generate closers without native steps and skip the replay. Details:
[research/appendix/B-TrustBase.md](research/appendix/B-TrustBase.md).

## Single module

### Single module: plain bodies

`#ved_u1` covers register-free bodies built from not/and/or/xor/add/sub/mux/slice, two-field
concatenation, `==` (1-bit result), constants, `kLut!` constant tables, and one-register delays.
A body with `==` is closed over the finite input domain by `decide +kernel` (suits 4- to 8-bit
table indices; cost grows with the product of the input ranges). The contract fixes ports from
the declaration's type; a `×`-tree of `Signal d _` results gets one port per leaf (`out` at the
root, `_0`/`_1` for product sides), checked against the module's output names.

* Checks: `Tests/Ved/U1ContractCheck.lean`, `U1EntryCheck.lean`, `U1MultiOutCheck.lean`,
  `U1EqLutCheck.lean`, `U1RconCheck.lean`, `U1DomainCheck.lean`, `U1StageCheck.lean`.
* Limits: shifts and concatenation of more than two fields are not covered by the plain script;
  large tables can stop at `maxRecDepth` in the checker.

### Single module: several registers

Two routes. `#ved_u1_deep` (after `#verify_elab_deep`) covers k ≥ 1 registers with Bool or
bit-vector inputs and one output; the invariant is `st (_nm i) = Cdo.irState … i` per register
slot, matched by name. `#ved_u1` itself handles `circuit do` bodies whose registers are one
`Signal.loop` over a state tuple: `loopScriptFor` proves by induction on the cycle that each
module register is the loop-state component it implements (`ved_loop_R`), the kernel checks the
match. Facts of `#verify_elab_deep` are looked up in the current namespace first, then the
declaration's (`deepScope`); if both exist and differ the entry refuses.

* Checks: `Tests/Ved/U1DeepCheck.lean`, `U1MultiRegCheck.lean`, `DeepNameCheck.lean`,
  `DeepInitCheck.lean`, `DeepHygieneCheck.lean`, `U1MultiLoopCheck.lean` (and
  `U1MultiLoopFull1`…`Full6`, `U1MultiLoopAll` on real declarations), `U1SeqCheck.lean`,
  `U1SmallRegCheck.lean`, `U1RegChainCheck.lean`, `U1CircuitLoopCheck.lean`,
  `U2HierNestedInlineCheck.lean` (nested inline stateful calls).
* Limits: one `simp`/`omega` script, so many registers together with many inputs can exceed the
  heartbeat budget (`[checker]`); a module whose registers are not all loop-state components is
  refused at `[proof]`.

### Single module: packed result

A result `Signal d (A × B)` is ONE port `out` of width `wA + wB`, the concatenation of its leaves,
first leaf in the high bits (`bundle2 a b` emits `concat [a, b]`, MSB-first; nesting keeps the
left-first leaf order). `#ved_u1_packed` proves `PackedStmt pc m f := PackCover pc ∧
U1Stmt pc.core m (packedF pc.tbl f) ∧ SlicesStmt pc m f`: the slice map derived from the type covers
the port exactly, the packed value satisfies the ordinary `U1Stmt`, and every slice equals the
declaration's own projection (`slices_of_outputs`). `#ved_u1` refuses such a result at
`[multi-output]`.

* Checks: `Tests/Ved/U1PackedCheck.lean` (swapped, overlapping, missing slices refused at
  `[packed]`; changed fields at `[proof]`).
* Limits: `Bool` / `BitVec w` leaves only; no parameters, structures or hierarchy.

### Single module: packed result with registers

The same `PackedStmt`, with the contract's clock/reset and register initial values filled from
the returned module (`PContract.clkRst`, `PContract.inits`; defaults keep the register-free
case unchanged). The proof is `packedLoopScript` (`Tools/VedU1MultiSeq.lean`): the loop invariant
over `packedF`, closed leaf by leaf; a register-free body the first script misses is retried with
`packedCombScript`.

* Checks: `Tests/Ved/U1MultiSeqCheck.lean`, `U1PackedSeq2Check.lean`, `U1PackedSeq3Check.lean`.
* Limits: bit-mask updates that need `&&&`/`|||` reasoning under `% 2^n`, `omega` over symbolic
  products of sign-extended operands, kernel `decide` of `OrderOk` on modules of several hundred
  statements, and FSM case splits with many states can exceed the budget.

### Single module: structure results

A result that is a structure of `Signal` fields (or a product of them) is read as the tuple of its
fields in constructor order; the statement is `U1Stmt c m (fun xs => bundle2 (D xs).f₁ …)` over the
original declaration, with one output port per field name, required to equal the module's output
names in order. `#ved_u1_struct` handles register-free bodies; `#ved_u1` handles a structure built
from a `Signal.loop`.

* Checks: `Tests/Ved/U1StructOutCheck.lean`, `U1StructSeqCheck.lean`, `U1StructWireCheck.lean`,
  `U1StructNamedCheck.lean`, `U1StructShareCheck.lean`.

### Single module: large shared DAG

Bodies whose unfolded step is a small DAG but an exponentially large tree (CRC chains that use
each intermediate value several times, wide signed products with clamps) are accepted with the
same statement. The loop script works on shared subterms: `ved_loop_unfold_share`,
`ved_loop_gen_share` (DAG walks and `Expr.replace` instead of tree walks and `kabstract`), and
`ved_wire` (`Tools/VedU1Wire.lean`), which turns every operation of the goal into a wire, proposes
equalities between wires from numeric samples and proves each by `omega` in a small context. The
samples only propose; the kernel checks the result.

* Checks: `Tests/Ved/U1WireShareCheck.lean` (8- and 16-bit CRC chains; another initial value,
  swapped arms or another polynomial refused at `[proof]`), `U1HeavyCheck.lean`,
  `U1MerkleWhnfCheck.lean`, `VedOmegaCCheck.lean`, `VedOmegaCacheCheck.lean`.
* Limits: any tactic that reads the goal as a tree again (a full `simp`, an `omega` discharger)
  brings the blow-up back; see [Design principle](#design-principle-decomposition-and-composition).

### Single module: memories

`#ved_u1_mem` / `#ved_u1_mem_packed` prove `MemStmt`: the U1 statement with "no instances" as the
shape clause and the order clause `OrderOkM`, and the same `OutputsStmt` from all memories 0. The
script proves, per memory, that the IR array equals the declaration's `memState` at every cycle,
and for a registered read that the data latch equals the declaration's read.

* Checks: `Tests/Ved/VedMemCheck.lean`, `VedMemWriteCheck.lean`, `VedMemShapeCheck.lean`,
  `VedMemOrderCheck.lean`, `VedMemWidthCheck.lean`, `VedMemPackCheck.lean`, `VedMemCloseCheck.lean`.
* Limits: one write port and one read port per memory, plain port names, no memory read inside a
  write payload, no instances; other shapes are refused at `shape`. Memories inside children are
  not covered by the hierarchy entries.

## Hierarchy

### Hierarchy: semantics and statement

`synthesizeCombinational` returns `(m, d)`: the top module and the design of child modules,
referenced by `Stmt.inst modName instName conns`. The IR semantics is open-module (an instance's
outputs are free inputs), so the hierarchy entries define a closed semantics from the returned
`(m, d)` only, never from the declaration (`Tools/VedU2HierSem.lean`): state `Path → String → Nat`
keyed by (instance path, register name), so two instances of one child have separate state; one
cycle evaluates the combinational part on the pre-update state, computes every register's next
value (parent and all children) from it, and applies all updates once at the end. Initial values
are each module's own register inits. Every failure (missing child, unconnected input, fuel) is
`none`, never a 0 value. `OrderOkHS` (`Tools/VedU2HierOrder.lean`) checks the arrangement across
assigns, registers and instances, taking each child output as depending on all its inputs
(conservative: false refusals possible, no false acceptance).

The proof treats each child as an oracle: the parent is proved as an open module whose instance
outputs are free wires (`fold_oracle`, `oracleIE`), and each oracle is supplied by the child's
**own** theorem `<decl>.ved_child.<child>.ved_u1`, bound by `decide` to the module resolved from
`d` (`kid_inst`). The final theorem has no unsupplied binder. Statement pins:
`Tests/Ved/U2HierPin.lean`, `Tests/Ved/U2HierSemCheck.lean`, `Tests/Ved/H2OpenParentProbe.lean`.

### Hierarchy: combinational children

`#ved_u1_hier` (H1, statement `U1HStmt`): depth 1, combinational leaf children with one output,
a combinational parent, the same child called several times. `Tests/Ved/U1HierCheck.lean`
(asymmetric children so that miswiring changes the value; swapped conns, altered child body,
missing or duplicate child, another design refused). Children with registers go through
`#ved_u2_hier`.

### Hierarchy: register-free parent

`#ved_u2_hier` with `U2HStmt` (contains `regsOf m.body = []`): depth 1, leaf children made of
assigns and registers with one output, every instance input a `ref` to a parent input (child
clock/reset ports to the parent's clock/reset). A child with registers needs
`#verify_elab_deep <child>` first (the entry does not run it; otherwise `[child]`). The open
parent `decl.ved_open` is generated by abstracting the child calls, and
`decl xs = decl.ved_open xs (g …)` is checked by the kernel (`rfl`).

* Checks: `Tests/Ved/U2HierCheck.lean` (37 refusal controls: netlist, clock/reset, wiring, child
  body/init, design mismatch, scope), `U2HierPin.lean`.

### Hierarchy: parent with registers

`U2HRStmt` (`Tools/VedU2HierReg.lean`) is `U2HStmt` without the `regsOf m.body = []` conjunct.
The entry runs `#verify_elab_deep` on the generated open parent and proves the composition
`outputsOnHS_of_stepR`: invariant on the parent registers, child outputs from the child theorems,
one cycle of the open fold. Parent register inits are tied by comparing the deep `_deep_inits`
with the module in the kernel.

* Checks: `Tests/Ved/U2HierRegCheck.lean` (changed init/next, swapped instance outputs,
  same-cycle state/next confusion, clock/reset misuse, cycles all refused), `U2HierNestedInlineCheck.lean`.
* Note: a parent register renamed to a child's register name is accepted, because state is
  keyed by path.

### Hierarchy: child input from a parent net

A child data port may read a parent net computed only from parent data inputs through assigns
(`kid_inst_net`, `Tools/VedU2HierNet.lean`): the child theorem is applied to the stream
`netIn … F`, where `F` is the declaration's call argument, and the generated proof shows that the
wire carries `F` on every cycle (`hrunF`). Statement unchanged.

* Checks: `Tests/Ved/U2HierWireCheck.lean`.
* Limits: refused at `[conns]` when the net reads a parent register output, another instance's
  output (without `ved.compose.connect`), or for a register-free parent; child clock/reset on a
  derived net refused at `[hier-shape]`; Bool nets and `===` comparisons in the net refused at `[proof]`.

### Hierarchy: child argument from parent register state

When the declaration is one call `g a` of a combinational child whose argument is the parent's
pre-update register state, `genOpenSt` (`Tools/VedU2HierStGen.lean`) proves `decl xs = g a` by
`Eq.refl`, the open parent's deep run exports its loop state (`<decl>_<port>_deep_state`), and
`outputsOnHS_of_stepRK` (`Tools/VedU2HierState.lean`) combines invariant, child output at the same
cycle (`kid_step`) and open step in one induction. Statement unchanged.

* Checks: `Tests/Ved/U2HierStateCallCheck.lean` (includes an original real-IP declaration),
  `U2HierPartialDeepCheck.lean` (a port the proof does not use may fail; it is reported as
  `VED U2 HIER PARTIAL-DEEP`).
* Limits: combinational children only on this path; an argument that is not a plain rewiring of
  registers (alias, slice) cannot be mapped to a slot and is refused.

### Hierarchy: open parents on real-IP shapes

The open parent's `#verify_elab_deep` and register-step proof are hardened for real-IP shapes:
`Fin` tail arms for more than 15 registers/inputs (`Tools/DeepFinArms.lean`), nested-circuit
register blocks and nested loop-state export (`Tools/DeepNestedState.lean`,
`Tools/VedU2HierStateArgs.lean`), `sparkle.deepContinue` (a failing unused port does not abort),
`sparkle.deepNoNative`, and the closer `ved_hier_close` (pack read-back, complements of bounded
values, one's-complement adders: `Tools/VedU2HierClose.lean`, `VedU2HierXor.lean`,
`VedU2HierBvAppend.lean`), `ved_rw_loops` (`Tools/VedU2HierLoopRw.lean`). Budget floors:
`ved.u2.hierRecDepth`, `ved.u2.hierHeartbeats`, `ved.u2.nestedRecDepth`, `ved.u2.nestedHeartbeats`.

* Checks: `Tests/Ved/U2HierOpenDeepCheck.lean`, `U2HierOpenDeep2Check.lean`,
  `U2HierOpenDeep3Check.lean` (each a few minutes and several GB).
* Limits: without the composition path below, the parent step is one `simp` over the whole body,
  which bounds the register count.

### Hierarchy: several child instances on parent state

When a child is called more than once inside the loop body and its output feeds the parent's
registers, the calls are found by reduction for a free state, each distinct call becomes an
oracle, and the open parent is the original `circuit do` with calls replaced by oracles
(`Tools/VedU2HierMultiGen.lean`). `loop_knot` (`Tools/VedU2HierMultiLoop.lean`) proves that the
declaration's loop equals the open loop with the oracle fixed along it; register-bundle reads use
`bundle_slice_fact`. Single-instance designs keep the previous path.

* Checks: `Tests/Ved/U2HierMultiCheck.lean` (same child on two nets, one net in two registers,
  two different children).
* Limits: the default parent proof evaluates the whole arrangement; large parents need
  [Composition: step](#composition-step) and [connect](#composition-connect).

### Hierarchy: children whose leaf proof failed

For a register-free child, the entries pick a proof route before the generated script
(`checkCombChild`, `Tools/VedH3ChildEntry.lean`): add-stage chains proved once per stage and
composed by induction (`Tools/VedH3ChildChain.lean`), else named constant tables read as data and
checked by `decide +kernel` (`Tools/VedH3ChildTbl.lean`, input width ≤ 10 bits), else the
generated script. A refusal of the chosen route falls back to the generated script. Statements
unchanged.

* Checks: `Tests/Ved/H3ChildCheck.lean`, `U1KTabCheck.lean`, `U1LeafCheck.lean`.

### Hierarchy: multi-output children

With `ved.compose.multiOut`, children with k ≥ 1 outputs are accepted under `U2HRStmtK`
(`Tools/VedU2HierMultiOut.lean`; `HierShapeK` instead of `HierShapeS`, every other conjunct the
same; `U2HRStmtK_iff` when every module has one output). The child theorem comes from the
structure route; sequential children are composed through `srcOf_prefix` (causality from the
child's own theorem) and `kid_seq_multi`. `U2HRStmtK` and the register-free `U2HStmtK`
(`Tools/VedU2HierMultiOutH.lean`) are marked candidates in their source headers.

* Checks: `Tests/Ved/MultiOutCheck.lean`, `MultiOutProbe.lean`.
* Limits: the `ved.compose.step` path is off for a multi-output design; nested structure results
  and 1-field structures are not handled.

### Hierarchy: limits

Refused today: children that themselves contain instances (depth ≥ 2, non-leaf modules in `d`),
memories in children, several clocks or a derived clock/reset, reset ≠ 0 (outside the statement),
a single child instance whose output feeds the parent's own state while the declaration is not
that call (`[open]`), and parents whose proof exceeds the budget. Unused modules in `d` are
refused, not dropped.

## Composition of proofs

### Composition: step

`step_local` (`Tools/VedComposeStep.lean`, option `ved.compose.step`, default off) takes the
open fold of the parent's arrangement apart once, for any body: the remaining obligation is
stated for an abstract environment `E` in which every assignment holds, inputs carry the cycle's
input, registers the pre-update state and instance outputs the oracle. Each register's next value
and each output is then proved from its own cone, not from an evaluation of all statements.
`hstep`'s statement is unchanged.

* Checks: `Tests/Ved/ComposeStepCheck.lean`, `ComposeDeadSlotCheck.lean`.

### Composition: connect

`cone_connect` / `reg_connect` / `out_connect` (`Tools/VedComposeConnect.lean`, generator
`Tools/VedComposeConnectGen.lean`, option `ved.compose.connect` together with `ved.compose.step`)
close each cone by connecting the returned IR's inlined, bundle-normalised cone to the open
parent's deep cone literal (`_deep_fidelity_r`) under a slot renaming, with widths
(`WOKb`), needed-leaf ranges and the register table checked by one kernel Bool each (`RegsOk`).
There is no per-cone `simp` fallback in this mode; every connection logs `VED COMPOSE CONNECT`.
Under `connect`, chained instances (a child fed by another instance's output) and a declaration
port that is directly a child's output (`sparkle.deepExportState`) are also handled.

* Checks: `Tests/Ved/ComposeConnectCheck.lean`; independent post-checks of real rows
  (not in CI): `ComposeConnectR193Check.lean`, `R194`, `R227`, `R230`, `R232`, `R246`.

### Composition: fused circuits

With `ved.compose.multiCircuit`, a top that reads several closed `circuit do` blocks (chains,
fan-in, shared readers, pure-wiring tops over a structure constructor) is fused into one open
parent: `fuse_run` and `fuse_indep` (`Tools/VedComposeMultiCircuit.lean`) prove that the run over
the appended registers equals the composed runs, and the generator applies them repeatedly, once
per shared circuit (`fuseShared`). Under `connect`, `ved.compose.noReach` is the default: the
side-condition proofs use pointwise child lemmas, not unfolding candidates of the child's
definitions. `Tools/VedComposeMultiLoop.lean` holds lemmas not yet wired into the generator.

* Checks: `Tests/Ved/ComposeConnectCheck.lean` (fusion toys and controls).
* Limits: the kernel definitional check of a large unfolded fused body can dominate; fused real
  circuits can stop in the deep stage.

## Design principle: decomposition and composition

Decomposition and composition theorems are the basic axis of VED work, not a performance fix.
Every extension (a new shape, a new kind of child, a new statement) is designed in four parts:

1. **Local meaning and contract**: the new piece has its own semantics and a contract checkable
   on its own (a child's `U1Stmt`, `connsOkK`, `fuse_run`).
2. **Connection through the real child theorem**: the parent uses the child's theorem constant,
   never an unfolding of the child's body (`reg_connect`, `kid_inst`, `bundle_causal_agree`).
3. **Composition that keeps every guarantee**: widths, every output once, causality, initial
   state and per-instance state (`WOKb`, `HierShapeK`, `srcOf_prefix`, `loop_append`).
4. **DAG sharing from generation onwards**: terms and proofs stay shared (memoised walks, one
   kernel Bool per arrangement such as `RegsOk`).

Large parents are split internally into local lemmas per wire and per state update; users are not
asked to split their source. Do not give back what composition saved: no full unfolding before
the split, no re-unfolding of a child body, no copying a child's script into the parent, no
return to one large `simp`. When a large `simp` or a bigger budget seems necessary, first name the
cause: (a) a missing local theorem (state it), or (b) lost sharing (which term, where); then do
the smallest unit that fixes it. Measure on a representative real row and a small scaling
series, reporting generation time, kernel time and proof size separately. The final contract,
the std3 axioms and the same-artifact guarantee do not change.

## Related methods

Two published methods reduce recombination of decomposed proofs to one generic theorem plus one
per-design check; VED follows the same pattern.

* **ACL2 SV decomposition** (`centaur/sv`, `svtv-generalize.lisp`): a theorem about the design
  with internal signals overridden by free values is generalised so the override becomes the
  observed value of the same signal in the same run; the bridge is override transparency,
  established per design by a syntactic check with a semantic fallback. In VED the cut signals
  are instance outputs (oracles), transparency is `fold_oracle`, the observation is `hkid`, and
  the per-design check is the ordering check (`OrderOkHS`). Unlike ACL2, VED must also show that
  the returned IR computes the cone the open parent was proved about, because the simulated
  object and the proved object are different terms.
* **Kami modular refinement** (ICFP 2017, Theorems 5.4 to 5.6): substitution of refined modules
  under disjoint registers and methods, verified inlining, and refinement from an initial
  relation plus a one-step simulation. The VED counterparts are the child theorem, the state keyed
  by `(path, name)`, `cone_connect`, and `h0`/`hstep` of `outputsOnHS_of_stepRK`. Kami's widths
  are in its types; in VED they are re-established (`WOKb`). This is an analogy: nothing in Lean
  instantiates Kami's theorems.

Cone-of-influence partitioning of instances was not pursued: `fold_oracle` needs every instance
output. A wider comparison with Kami, Kôika, SV/SVL/SVEXL and RP-Rewriter is in
[research/RelatedWork.md](research/RelatedWork.md).

## Where to read next

* [research/README.md](research/README.md): the public entry to verified synthesis (guarantee
  ladder, smallest example, reading map).
* [tutorial/md/Ch07c_VerifiedSynthesis.md](tutorial/md/Ch07c_VerifiedSynthesis.md): a guided
  `#ved_u1` run, what the theorem says, how the proof is built.
* [research/PerCircuitVerification.md](research/PerCircuitVerification.md): what is proved, the
  reused lemmas, worked examples.
* [research/BuildAndCI.md](research/BuildAndCI.md): build times and the VED CI jobs.
* [research/OpenProblems.md](research/OpenProblems.md): open problems with reproductions.

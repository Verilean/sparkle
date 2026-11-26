# Per-circuit verification: what is proved, on what, and how

This page is for readers who have read the [overview](README.md). It explains the proof that
the verified synthesis commands attach to one circuit, which general lemmas that proof reuses,
what kinds of circuits pass and which do not, and what is still being tried. The
Lean statements are in [appendix A](appendix/A-Statements.md), the trusted base in
[appendix B](appendix/B-TrustBase.md). The other effort, a theorem over *all* sources, is a
separate document: [CompilerGeneralTheorem.md](CompilerGeneralTheorem.md).

## 1. The idea on one page

You write a circuit as a Lean function `f` on clocked streams. The synthesiser turns it into a
hardware module; the verified entry calls the synthesiser **once** and then tries to build and
kernel-check a theorem of the shape

```
U1Stmt  f.ved_contract  f.ved_mod  f
```

where `f.ved_mod` is the returned module written down as a closed term and `f` is your original
definition. In words: for every input sequence whose values fit their widths, with reset held
low, and for every way of ordering the module body in which each wire is assigned before it is
read, the module's outputs at every cycle equal the outputs of `f` at that cycle. If any step
fails, the command refuses and makes no claim. It also removes the constants the checker had
generated after it started; it does not undo the synthesis step, and it does not restore the
environment before synthesis, `IO.Ref`s, caches or files.

**On which artifact.** On the module object the synthesiser returned in that very command. It
is *not* the optimised module, and not the printed SystemVerilog. For writing files,
`#ved_write_checked` hands the writer exactly the module that was checked (section 2), but it
does not prove the printer.

## 2. The commands and what each proves

| Command | For which circuits | Theorem shape (name) |
|---|---|---|
| deep preparation (`#verify_elab_deep f`) | circuits in a small closed expression grammar; it produces per-circuit facts used by the next entries | uses the general theorem over that grammar (`Cdo.elab_general`) |
| basic entry (`#ved_u1 f`) | combinational bodies, registers, loops with several registers, several outputs as a tree of ports | `U1Stmt` |
| deep entry (`#ved_u1_deep f`) | `k ≥ 1` registers, Bool or bit-vector inputs, one output | `U1Stmt`, built from the deep facts |
| packed entry (`#ved_u1_packed f`) | a result of type `Signal d (A × B)`: **one** signal whose value is a pair (nested pairs allowed, leaves `Bool` or `BitVec w`), packed into one port with the first leaf in the high bits. Not `(Signal d A) × (Signal d B)`, a pair *of* signals: that has two output ports and goes through the basic entry | `PackedStmt` |
| memory entry (`#ved_u1_mem f`) | one module with a memory (one write port and one read port) | `MemStmt` |
| hierarchy entry (`#ved_u2_hier f`) | a parent module that instantiates children; parents with registers | `U2HStmt` (no registers in the parent), `U2HRStmt` (with registers) |
| checked writer (`#ved_write_checked KIND f "x.sv" "x_cppsim.h"`) | any kind above | the kind's theorem, plus an equality guard: the writer gets the checked design |

A theorem counts as **strict** only if a separate audit (`#ved_strict_audit`) finds that it uses
nothing beyond the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and no
`native_decide`. The link from the deep facts to the emitted IR in the deep route uses
`native_decide` and is therefore **not** strict; strict rows use the other routes or the audited
variants.

**What a refusal stage means.** The entry's name for the stage that stopped (`[stage]` in the
message): `table` (the declaration's shape is not one the port table can read), `multi-output` or
`packed` (the result shape is not handled by this route), `order` (no arrangement exists in which
every wire is assigned before it is read, for example a combinational cycle), `hier-shape`, `scope`,
`conns`, `open` (obligations of hierarchies), `proof` (the generated proof did not check inside
the fixed budget), `prep` (the deep preparation did not succeed). A budget is never raised to make a
row pass.

## 3. The general lemmas that are reused

The per-circuit proof scripts are **generated and untrusted**: the kernel checks the result
against the stored statement. What they reuse was proved once:

| In plain words | Lean name | File |
|---|---|---|
| All orderings of a module body that assign each wire before reading it give the same run | `runModule_perm` | `Sparkle/IR/ReorderInvariance.lean` |
| From one checked ordering to the statement over every ordering; the in-order form is recovered when the body is already ordered | `outputs_of_order`, `outputs_body` | `Tools/VedU1Contract.lean` |
| For **every** circuit of the closed deep grammar (constants, variables, add, subtract, select, equality, and, or, xor), every input stream and every cycle, the Signal output equals the output of the compiled expression cone. The only per-circuit obligation is that slot names are distinct | `Cdo.elab_general` | `Tools/DeepElab.lean` |
| How a loop with several registers unfolds | `loop_val_unfold` | `Tools/VedU1Loop.lean` |
| The state induction for a module with memories | `outputs_of_step_mem` | `Tools/VedMem.lean` |
| Assembling the run of a parent from its children, per instance path, using the children's own statements | `instEval_laws`, `outputsOnHS_of_oracle` | `Tools/VedU1HierComp.lean`, `Tools/VedU2HierEntry.lean` |

These are theorems about the **checker's machinery**. They are not a soundness theorem for the
compiler: for a circuit outside the grammar, the link to the real synthesiser is built per
circuit by the generated proof, or not at all. That is the difference to the general theorem
explained in [CompilerGeneralTheorem.md](CompilerGeneralTheorem.md).

## 4. Worked examples, by role

Each example says what the circuit is for, what goes in and out, its size, which proof passes,
and why it matters. Every example is a file you can build; the commands are in the
[contributor guide](CONTRIBUTING-research.md).

**An 8-bit register** (`delay8`, [example file](examples/Delay8.lean)). Purpose: the smallest
stateful circuit, the output is the input one cycle earlier. State: 8 bits. The basic entry
returns a theorem; the [tutorial chapter](../tutorial/md/Ch07c_VerifiedSynthesis.md) reads it
part by part and shows that a mutated module, or another circuit's proof, is refused.

**A parent with sub-modules** (`Tests/Ved/U2HierRegCheck.lean`). Purpose: an 8-bit accumulator
used as a child, instantiated once and three times inside a parent that has its own registers.
The hierarchy entry's theorem has exactly the type `U2HRStmt`, the audit passes, and the closed
run of the parent is evaluated on concrete values. Each control alters one piece of the returned
design and must be refused at a named stage, after which the constants the checker generated
are absent from the environment (the check looks at those names; it does not claim that
anything done by the synthesis step before the checker is undone).

**Writing the files** (`Tests/Ved/WriteCheckedCheck.lean`). Purpose: show that what is written is
what was checked. The test compares the written files byte for byte with what the ordinary
writer writes, and checks that a design that differs from the checked one is refused. It says
nothing about whether the printed SystemVerilog means the same thing (rungs 3 to 6 of the
[ladder](README.md#the-guarantee-ladder)).

**A protocol state machine that passes: the TCP connection state machines.** The server and
client state machines of `Tests/IP/Net/TCPStateTest.lean` take the parsed TCP flags and a few
control pulses, and produce the connection state, an "established" flag and a "send a packet"
request. Their state is a small enumeration plus a few counters. All five output rows of that file
are strict. They are typical of the families that pass: control logic with narrow registers.

**A point-operation circuit that does not pass: P-256 elliptic-curve point operation**
(declared as `wPointOp` in `IP/Crypto/P256SignDemo.lean`, built from `pointOpHW` in
`IP/Crypto/P256PointOpHW.lean`). Purpose: one step of elliptic-curve cryptography on the NIST
P-256 curve. It performs **either a point doubling or a point addition** on curve points in
Jacobian coordinates (X, Y, Z, each a 256-bit number), as a small state machine that asks an
*external* field multiplier for up to sixteen modular multiplications through a start/done handshake.
Inputs: a start pulse, a double-or-add flag, two points (six 256-bit values), the multiplier's
result and done signal. Outputs: the result point (three 256-bit values), a done pulse, and the
multiplier's request (start pulse and two 256-bit operands). State: about twenty-two 256-bit
registers plus a step counter. Result at the snapshot: the three output rows of this circuit
are all **refused** at the `proof` stage, while the same kind of circuit for the Ed25519 curve
passes. It is a research problem because the unfolded proof term is a tree whose size grows
exponentially in the number of arithmetic stages even though the circuit is a graph with shared
parts; keeping the sharing through the whole proof is open work (see
[OpenProblems.md](OpenProblems.md#1-large-arithmetic-circuits-without-losing-sharing)).

**A hash sponge that does not pass: the Keccak-256 sponge** (`IP/Crypto/Keccak256Sponge.lean`).
Purpose: absorb a padded message in blocks of 136 bytes into a 1600-bit state and squeeze a
256-bit digest. State: 25 lanes of 64 bits. Both output rows of its test are refused at the
snapshot. Its smaller neighbour, the table of Keccak round constants, passes. The one run that
accepted these outputs used the nested-hierarchy route described in section 6.

## 5. What worked, and where it stops

At the snapshot **243 of 327 command rows are strict** (real IP 168 of 220, regression rows 75
of 107). The family-by-family list with the main stopping stage is on
[Coverage327.md](Coverage327.md); every row is in [appendix F](appendix/F-AllCommandRows.md); which
approval backs which count is in [appendix D](appendix/D-Evidence.md). Of the 243, 43 were
already strict at the earlier baseline, 42 have a separate approved measurement of an earlier
commit, and 158 are measured only. The 84 rows that are not strict carry no claim; 10 of them
could not be run at all.

What the counts do not say: they say nothing about the optimiser, the printed SystemVerilog or
hardware. A row is one invocation of a fixed synthesis command (a single-output wrapper, or one declaration
bundling several outputs), not an IP and not an output signal. The time and memory in the
tables are one run, including the loading of imports; there is no performance claim.

**What limits it today** (from the stopping stages and the design records):

* **Memories in sub-modules.** Instances are covered for the shapes the hierarchy statements
  handle; memories inside children are not.
* **Deep nesting.** Sub-modules that themselves contain sub-modules, beyond the shapes of the
  design records ([VED-HIER-H2D](../VED-HIER-H2D.md), [VED-HIER-H2E](../VED-HIER-H2E.md)).
* **Large arithmetic.** Wide arithmetic and cryptographic cones whose unfolded term is
  exponentially large ([VED-U1-WIRE-SHARE](../VED-U1-WIRE-SHARE.md)).
* **Budgets.** Elaboration, heartbeat and kernel limits are fixed; a proof that does not fit is
  refused at `proof`, never accepted with a smaller statement.
* **Reset low.** The statements cover runs with reset deasserted from the start.

**Methods that worked.**

* *Local lemmas proved once*, applied with only their direct dependencies, instead of one large
  simplification over the whole goal.
* *Sharing kept from generation to the end.* Reading a shared term as a tree caused most large
  blow-ups (a CRC chain: a graph of about 160 nodes whose tree has 2.5 × 10⁸).
* *Classify every wall before changing anything*: a missing local theorem and lost sharing need
  different remedies.
* *Never raise a budget to get a row.* Options that change limits are floors, behind an option,
  with the default unchanged.
* *Refusal controls.* Every new lemma or route comes with mutants that must be refused (one
  changed next value, two registers swapped, another circuit's module), so that acceptance is not
  vacuous.
* *Measure separately*: heartbeats for budget walls; elaboration time, kernel time and peak memory
  as three numbers.

## 6. In progress, not in this release, not reviewed

These lines of work exist on unmerged branches or local lines. **None of it is part of the
release, none of it is counted in the 243 of 327, and nothing in it has been reviewed.**
Publishing the release does not wait for any of it.

### 6.1 Single observed runs

Every item below carries all five labels: **single observed run**, **candidate line** (the
line it ran on, not the release code), **not reviewed**, **not in the release**, **not counted**
in any coverage number.

| Circuit | What was observed | Candidate line |
|---|---|---|
| The two outputs of the Keccak-256 sponge (rows R163 and R164 of the full table) | accepted once by the nested-hierarchy route of the hierarchy entry (option `ved.compose.nested`, statement `U2HRStmtR`) with a long option set; about 20 minutes and 19.5 GB peak each (figures from the run report, not re-checked: the run's line is not pushed) | an unpushed local line (the public branch `ved/nested` is the nearest published state). They stay **refused** in [Coverage327.md](Coverage327.md) |
| The P-256 point-operation circuit of section 4 | its returned module (560 statements, 26 registers) accepted once by the single-module entry through a node-table route: standard axioms only, no fallback, about 18 minutes end to end, 11.2 GB peak, 37 % of the default proof budget (figures from the run report, not re-checked: the line is not pushed) | a local line (not public). The circuit's declarations exist in the release; the node-table route and this proof do not. It stays **refused** in [Coverage327.md](Coverage327.md) |

### 6.2 Boundary: what the release contains and what it does not

Names below were checked with `git grep` in the release snapshot (present), and on the public
branches named (present there, **absent in the release**).

| Theorem or command | In the release? | Where |
|---|---|---|
| `U1Stmt`, `outputs_of_step` (one module) | **yes** | `Tools/VedU1Contract.lean`, `Tools/VedU1Entry.lean`; `#ved_u1` |
| `PackedStmt` (packed ports) | **yes** | `Tools/VedU1Packed.lean` |
| `MemStmt`, `outputs_of_step_mem` (memory in one module) | **yes** | `Tools/VedMem.lean` |
| `U2HStmt`, `U2HRStmt` (hierarchy, with registers) | **yes** | `Tools/VedU2HierStmt.lean`, `Tools/VedU2HierReg.lean`; `#ved_u2_hier` |
| `Cdo.elab_general` (deep grammar) | **yes** | `Tools/DeepElab.lean`; `#verify_elab_deep` |
| `#ved_write_checked` | **yes** | `Tools/VedWriteChecked.lean` |
| **Composition route**: options `ved.compose.step`, `ved.compose.connect`, `ved.compose.multiCircuit`, `sparkle.deepExportState`; lemmas such as `step_local` (`Tools/VedComposeStep.lean`), `ren_eval`, `tauOf` (`Tools/VedComposeConnect.lean`) | **no** (0 hits in the release) | public branch `meas/ved-route-compose` (the development snapshot of [appendix E](appendix/E-DevelopmentSnapshot.md)); lemma lines also on `ved/compose-connect`, `ved/proof-compose` |
| **Nested route**: `ved.compose.nested`, `U2HRStmtR`, `U2HRStmtR_iff_K`, `U2HRStmtR_of_S` | **no** (0 hits) | public branch `ved/nested` (`Tools/VedU2HierRec*.lean`, `Tests/Ved/U2HierRec*Check.lean`); 210 commits beyond the release; not reviewed |
| **Table route** (in the style of the SVEXL tool): a node table with a per-node soundness lemma, a literal cut check and cone satisfiability (proposed lemma shapes `key_sound`, `conn_equal_many`) | **no** (0 hits) | **not public**: no branch on the public remote contains these names |

A *research direction* says what would be proved and why. A row marked "no" is code or a theorem
that exists, if at all, only on the named unmerged line, and this repository must not be read as
claiming it for the release.

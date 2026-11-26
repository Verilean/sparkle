# Sparkle verified synthesis: what it does, what it guarantees, how to help

Sparkle is a Lean 4 library for describing hardware as functions on clocked streams of values
(`Signal`) and turning those functions into SystemVerilog. This directory is about one
extension of it: **synthesis that hands back a proof**. You can read, run and extend all of it
from a public checkout. It is a research release, not a product announcement.

## 1. What the system builds

The ordinary command `#synthesizeVerilog f` turns a Lean function `f` into a hardware module
and prints it. Nothing checks that the module computes what `f` says: you trust the compiler.

The verified entries (the `#ved_*` commands, "VED" for *verified elaboration, deep*) do the same
synthesis **once**, and then try to build a theorem, checked by Lean's kernel, that *the very
module that was just returned* computes what `f` computes. If they cannot build the theorem,
they refuse and return nothing. A refusal does not tell you whether your circuit is right or
wrong: it only means that this checker produced no proof. The reason can be an unsupported
construct, a resource limit (time or memory), a mismatch between the returned module and the
statement, or something else; the stage in the message says where it stopped.

## 2. Inputs and outputs

| | |
|---|---|
| **Input** | a Lean definition of type `Signal domain A → … → Signal domain B`, written with the Sparkle DSL (registers, `Signal.loop`, memories, sub-modules) |
| **Output, success** | the returned hardware module (Sparkle's intermediate representation, "IR"), and a theorem about it, kernel-checked and using only the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). With `#ved_write_checked` the SystemVerilog file is written from exactly that checked module |
| **Output, failure** | a message `VED U1 REFUSED f [stage]` that names the stage that stopped (no module, no theorem; the constants the checker had generated after it started are removed, see below) |

## 3. The guarantee, in plain words

**What the theorem says.** For every input sequence whose values fit their bit widths, with the
reset line held low, the outputs of the returned module at every clock cycle equal the outputs
of your Lean function at that cycle. The right-hand side is computed from your function itself,
not from a copy of it. The theorem is generated per circuit and checked each time.

**What a refusal leaves behind.** When the checker fails after it has started, it restores
the Lean state it had at its start: the constants it generated (the module, contract, output
list and theorem constants) and its messages are removed. It does **not** claim to undo what
the synthesis step did before: the environment as it was before synthesis, `IO.Ref`s and caches,
and files are not rolled back, and nothing here is a rollback of the whole synthesis. (Code:
`Tools/VedU1Entry.lean`, the comment on `checkU1`.)

**What it does not say.** It is a statement about the *returned IR*. It does not say anything
about the optimiser that runs afterwards, about the printed SystemVerilog, about timing, or
about a chip. Circuits that are refused have no claim at all, and the reset line is assumed
low.

**Two different things that must not be mixed.** The first is the per-circuit theorem above
("VED"). The second is a *general theorem* that would say: for **every** source the old compiler
accepts, the output is preserved. That second theorem would make the first unnecessary, but it
is **not proved**: it needs facts about the Lean runtime that nobody has been able to supply, so
it is paused ([CompilerGeneralTheorem.md](CompilerGeneralTheorem.md)). The per-circuit route
reuses a few *general lemmas about the checker's own machinery*; these are not a soundness
theorem for the compiler.

### The guarantee ladder

A circuit passes through several representations. Each step has its own statement, and only the
second is covered by the results below.

1. **Lean function → deep description.** For circuits inside a small closed grammar of
   expressions there is one general theorem, plus per-circuit facts that are generated. Not
   total over all Lean functions.
2. **Lean function → returned IR module.** The per-circuit theorem of this page. This is what
   a "strict" result means everywhere in this directory.
3. **Returned IR → optimised IR.** No theorem in this release.
4. **IR → SystemVerilog text and back.** Only a fragment of the expression layer is proved.
5. **SystemVerilog text → its meaning.** No theorem: no semantic model of SystemVerilog is
   connected to Sparkle's.
6. **SystemVerilog → hardware.** Outside this work (synthesis tools, place and route, silicon).

There is one extra guard for file writing: `#ved_write_checked` makes sure the writer receives
the module that was checked (a tampered module is refused). That ties rung 2 to the file, not
rung 2 to rungs 3 to 6. The exact Lean statements are in
[appendix A](appendix/A-Statements.md); the trusted base per rung is in
[appendix B](appendix/B-TrustBase.md).

## 4. The smallest working example

[`examples/Delay8.lean`](examples/Delay8.lean) is a real file of this repository: an 8-bit
register, then one circuit that is refused.

```lean
import Tools.VedU1Entry
open Sparkle.Core.Domain Sparkle.Core.Signal

def delay8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 x

#ved_u1 delay8              -- synthesise, build and check the theorem
#print axioms delay8.ved_u1 -- ask Lean which axioms the theorem uses
```

Run it from the repository root. The verified tools are library targets that are not in the
default build, so build the one you need by name. The first build compiles the Sparkle library
first. On a clean 4-vCPU CI runner, the normal build took 83 s and `Tools.VedU1Entry` 60 s more
(one run, [BuildAndCI.md](BuildAndCI.md)).
Running the file itself took about 13 seconds once the target was built.

```bash
lake build Tools.VedU1Entry
lake env lean docs/research/examples/Delay8.lean ; echo "exit $?"
```

The expected exit status is **0**: the refusal of the second circuit is an intended result and
is pinned in the file with `#guard_msgs (error)`, so it prints nothing; if the refusal text
changes or the circuit is accepted, the file fails with a message diff. The output we obtained
(Lean 4.32.1; the printed module is shortened here with `…`, the other lines are verbatim):

```text
VED U1 OK delay8.ved_u1: [Classical.choice, Quot.sound, propext]
{ name := "delay8",
  inputs := [{ name := "_gen_x", ty := Sparkle.IR.Type.HWType.bitVector 8 },
             { name := "clk", … }, { name := "rst", … }],
  outputs := [{ name := "out", ty := Sparkle.IR.Type.HWType.bitVector 8 }],
  body := [Sparkle.IR.AST.Stmt.register "_gen_out" "clk" ("rst", Sparkle.IR.Type.ResetKind.synchronous)
             (Sparkle.IR.AST.Expr.ref "_gen_x") 0,
           Sparkle.IR.AST.Stmt.assign "out" (Sparkle.IR.AST.Expr.ref "_gen_out")],
  … }
'delay8.ved_u1' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

The first line is the success report of the entry, the second block is the returned module, the
next line is Lean's own axiom report for the theorem. The second circuit of the file (one `Signal`
whose value is a pair; the basic entry does not take it, the pair entry `#ved_u1_packed` does) is refused with `[multi-output]`; that
refusal is the expected message pinned by `#guard_msgs`, so nothing is printed for it. The
theorem itself is the constant `delay8.ved_u1`; the tutorial chapter
[7c](../tutorial/md/Ch07c_VerifiedSynthesis.md) reads its statement part by part and shows
how mutated modules are refused.

## 5. Method and results

**Method, in four sentences.** The checker synthesises the circuit once and writes the
returned module down as a closed Lean term. It then generates a proof script that unfolds both
sides and closes the goal with lemmas that were proved once for all circuits (order of
statements in a module body does not matter; how a register-and-loop machine unfolds; how
a parent module is assembled from proved children). The kernel checks the result against a
fixed statement; the script itself is not trusted. Details and the circuits that exercise each
lemma: [PerCircuitVerification.md](PerCircuitVerification.md).

**Results.** A fixed list of **327 command rows** (the `#synthesizeVerilog` and
`#writeDesign` commands of the repository, in 136 files; they are not 327 separate IPs) was
run against the release. **243 are strict** (a kernel-checked theorem of the shape above),
84 are not (74 refused, 10 not runnable). By circuit family:

| Circuit family | Rows | Strict |
|---|---|---|
| Finite-field and modular arithmetic (multipliers, modular inverse) | 24 | 21 |
| Elliptic-curve point operations, scalar multiplication, pairings | 22 | 11 |
| Signature engines (ECDSA, Ed25519) and signing demos | 19 | 12 |
| Hash functions and MACs (SHA-2, Keccak, HMAC, HKDF, Merkle) | 17 | 13 |
| Block cipher and authenticated encryption (AES, GCM) | 7 | 7 |
| Blockchain transaction encoding | 7 | 7 |
| Network packet parsers and protocol state machines | 37 | 31 |
| Field buses and serial links (CAN, I2C, SPI, PCIe, USB, …) | 24 | 22 |
| Controllers and filters (PID, LQR, IIR) | 15 | 9 |
| Processor and SoC building blocks (RV32 core, CSR, AXI4-Lite) | 20 | 16 |
| Video codec (H.264) | 12 | 6 |
| Neural-network accelerator (YOLOv8) | 16 | 13 |
| Language, compiler and example regressions | 107 | 75 |

One caveat on reading the counts: a row is **one invocation of a fixed synthesis command**
(`#synthesizeVerilog` or `#writeDesign` on one declaration, at one place in a file). A row can be
a wrapper around a single output, or one declaration that bundles several outputs; so a row is
neither an IP nor an output signal, and the 327 can be neither divided into IPs nor into outputs.
A "strict" row proves the theorem for that command's declaration; it does not by itself say that a
whole IP is verified. The table comes from the generated page [Coverage327.md](Coverage327.md), which also says why
each family's remaining rows stop. The complete row-by-row table with files and conditions is
[appendix F](appendix/F-AllCommandRows.md). Of the 220 rows that are real IP (not tests or
examples), 168 are strict. Not claimed: any statement about the optimiser, the printed
SystemVerilog or performance; no comparison with other tools (those are discussed in
[RelatedWork.md](RelatedWork.md), not measured).

The production acceptance gate agreed with the maintainers (measured performance, circuit-size
and coverage criteria) is **not met**.

## 6. Open problems

One line each; every item has a command to reproduce it, a minimal goal, the lemma needed and a
success condition in [OpenProblems.md](OpenProblems.md).

* **Memories inside sub-modules**: extend the hierarchy theorem to children that own memories.
* **Large arithmetic circuits**: close elliptic-curve and hash circuits whose unfolded
  proof term is exponentially large because shared sub-expressions are copied.
* **Deeper hierarchies**: compose proofs through two or more levels of sub-modules.
* **Compose a parent's theorem from its children's theorems**: a general lemma instead of unfolding.
* **The optimiser and the printer**: a preservation theorem or a validated translation check.
* **Parametric statements**: one theorem for all bit widths instead of one per instance.
* **The runtime-law witness** (the general theorem): a jointly satisfiable model of the facts
  the old compiler's proof needs, with a bridge to the real run.
* **Applying the system to a large SoC**, and **same-condition comparison with other tools**.

## 7. How to contribute

* Start from [CONTRIBUTING-research.md](CONTRIBUTING-research.md): how to build, how to run one
  check, where lemmas and entries live, what a pull request must contain (a new lemma comes with
  an accept test and refuse controls).
* Pick a task from [OpenProblems.md](OpenProblems.md) and open an issue before large work;
  report the commit you ran and the output.
* For adding a new IP to the library itself (not to the proofs), see the root
  [CONTRIBUTING.md](../../CONTRIBUTING.md).

## 8. Reading map

| If you want… | Read |
|---|---|
| A guided example you can run | [Tutorial chapter 7c](../tutorial/md/Ch07c_VerifiedSynthesis.md) |
| What is proved, on which artifact, which lemmas are reused, worked examples | [PerCircuitVerification.md](PerCircuitVerification.md) |
| Results by circuit family | [Coverage327.md](Coverage327.md) |
| The general theorem: what was attempted, what is missing | [CompilerGeneralTheorem.md](CompilerGeneralTheorem.md) |
| Open problems with how to reproduce them | [OpenProblems.md](OpenProblems.md) |
| Other tools (Kami, SVEXL, SVL, RP-Rewriter) compared | [RelatedWork.md](RelatedWork.md) |
| Install and build times, CI | [BuildAndCI.md](BuildAndCI.md) (clean-runner measurements and a CI split proposal) |
| Full Lean statements, trust base, reproduction, evidence | [appendices A to D](appendix/A-Statements.md), [E](appendix/E-DevelopmentSnapshot.md) (development snapshot, not in the release), [F](appendix/F-AllCommandRows.md) (all 327 rows) |

## Snapshot box

Every number in this directory names the code it was measured on. This box is the one place
that lists the commits.

| Item | Value |
|---|---|
| **The reader's checkout** (code + these pages + the example + the scripts; every short procedure in this directory starts here) | the branch `docs/research-release` of `https://github.com/Verilean/sparkle` (`git clone https://github.com/Verilean/sparkle && cd sparkle && git checkout docs/research-release`). Once the pull request is merged, the checkout is the merge commit on `main` (or the release tag, if one is made); until then it is this branch. Its code is exactly the code SHA below: `git diff --stat 2bcf256b HEAD` touches only `docs/`, `scripts/research/`, `.github/workflows/research-ux.yml` (a measurement workflow that runs only on request), `README.md` and `CONTRIBUTING.md` |
| Code SHA (provenance: the code the release contains) | `2bcf256b`: head of pull request #163, branch `ved/consolidated-1`. It has the code but **not** these pages, the scripts or the example, so it is not a checkout to follow the procedures on |
| Measured SHA (what the harness ran on) | `fb7124fc`, branch `meas/ved-pr16-fb71`. Not the same commit: it is the code SHA plus the measurement harness, and `git diff --stat 2bcf256b fb7124fc` touches only `scripts/ved/` |
| Strict command rows | **243 / 327** (real-IP rows 168 / 220, regression rows 75 / 107; 84 not strict), 7 proof routes; approved ledger `pr16-fb71` |
| Earlier baseline | `d331ff24` (an earlier candidate, not `main`): 43 / 327 |
| `main` | `6c29b9b8`: it has the deep route and the basic `#ved_u1` entry, but not the packed, hierarchy and `#ved_write_checked` entries described here |
| Not in this snapshot, not counted | work in progress: [PerCircuitVerification.md, section 6](PerCircuitVerification.md#6-in-progress-not-in-this-release-not-reviewed), and the development snapshot of [appendix E](appendix/E-DevelopmentSnapshot.md) |
| Page generation | `python3 -I scripts/research/coverage_table.py --check`, `python3 -I scripts/research/check_links.py` |

The two SHAs `2bcf256b` and `fb7124fc` are provenance of the numbers, not something to check
out for the short procedures; the retrospective and the measurement harness need their own
worktrees ([appendix C](appendix/C-Reproduction.md)).

The 327 are command rows, not IPs. If the head of the pull request moves, the snapshot and the
generated tables must be regenerated; a change of meaning or of proof generation does not
inherit the coverage.

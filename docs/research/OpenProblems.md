# Open problems, and how to pick one up

Each problem below can be started from a public checkout of the repository. For each we give
what it is in plain words, a command that shows the situation today, the smallest goal worth
reaching, the lemma or construction needed (as a proposition when we know its shape), the
input/output contract, what counts as success, where in the tree the new lemma goes, and
which check to add. Nothing here is a promise of results, funding or support. To discuss a
problem, open an issue and tell us which commit you ran and what you saw. How to build and
how a contribution is checked: [CONTRIBUTING-research.md](CONTRIBUTING-research.md).

Status of the code: the release snapshot named in the [README](README.md#snapshot-box). "The
release" below means that snapshot. The commands need the reader's checkout (the commit
`3af3889f` on `main`; see the [snapshot box](README.md#snapshot-box)
and [appendix C](appendix/C-Reproduction.md)); the commit `2bcf256b` has the same code but not
these pages or scripts.

| Problem | Kind | Needs |
|---|---|---|
| [0. Reproduce what exists](#0-reproduce-what-exists) | start here | a checkout, an hour |
| [1. Large arithmetic circuits without losing sharing](#1-large-arithmetic-circuits-without-losing-sharing) | proof engineering | Lean, a lemma about shared terms |
| [2. Memories inside sub-modules](#2-memories-inside-sub-modules) | new statement | Lean |
| [3. Deeper hierarchies and the composition theorem](#3-deeper-hierarchies-and-the-composition-theorem) | new theorem | Lean |
| [4. The optimiser and the printer](#4-the-optimiser-and-the-printer) | new theorem | Lean, SystemVerilog knowledge |
| [5. One theorem for all bit widths](#5-one-theorem-for-all-bit-widths) | new statement | Lean |
| [6. The general theorem: a witness for the runtime laws](#6-the-general-theorem-a-witness-for-the-runtime-laws) | research | Lean metaprogramming, semantics |
| [7. A same-condition comparison with other tools](#7-a-same-condition-comparison-with-other-tools) | measurement | the other tool |
| [8. Applying the system to a large SoC](#8-applying-the-system-to-a-large-soc) | collaboration | a real design |

## 0. Reproduce what exists

*Plain description.* Check that the results of the release reproduce on your machine.

*Commands.*

```bash
git clone https://github.com/Verilean/sparkle && cd sparkle
git checkout 3af3889f                # the reader's checkout of the snapshot box (code + pages + scripts)
lake build Tests.Ved.U1EntryCheck Tests.Ved.U2HierRegCheck Tests.Ved.WriteCheckedCheck
python3 -I scripts/research/coverage_table.py --check     # exit 0: the tables match their data
python3 -I scripts/research/check_links.py                # exit 0: no broken link
```

*Contract.* Every positive example is accepted with the standard axioms, every control is
refused, and the build exits 0. *Success.* Exit 0 on a clean checkout, and a report of your
time and memory (to compare with the clean-runner numbers in
[BuildAndCI.md](BuildAndCI.md)). A deeper task: re-run a sample of at least 20 of the 327 rows
with the public measurement harness (appendix C) and report any row that disagrees with
[appendix F](appendix/F-AllCommandRows.md). Another: read
[appendix A](appendix/A-Statements.md) and report any place where the Lean statement says less
than [PerCircuitVerification.md](PerCircuitVerification.md) says in words.

## 1. Large arithmetic circuits without losing sharing

*Plain description.* Cryptographic and hash circuits are long chains of arithmetic. As a
circuit they are a graph in which sub-results are shared; as a proof goal, unfolded naively,
they become a tree that is exponentially larger (a CRC chain: a graph of about 160 nodes, a tree
of 2.5 × 10⁸). The checker already keeps the sharing for CRC chains and some other bodies. It does
not yet for the point-operation circuits of elliptic-curve cryptography.

*The concrete target.* The P-256 point-operation circuit (one point doubling or addition in
Jacobian coordinates; `pointOpHW` in `IP/Crypto/P256PointOpHW.lean`). Its three output rows, and
those of the same operation on the secp256k1 curve, are refused at the `proof` stage in the
release, while the Ed25519 version and the P-256 scalar multiplier pass.

*Reproduce.* In the release checkout, the test file `Tests/IP/Crypto/P256PointOpHWTest.lean`
defines three one-output wrappers of the circuit (`synth_p256PointOpX`, `..Done`, `..MulStart`).
Put a copy of the file in a scratch directory, replace each `#synthesizeVerilog name` line
by `#ved_u1 name`, add `import Tools.VedU1Entry`, and run `lake env lean FILE`. The ledger records
the refusal (stage `proof`) after about 245 s and 15.8 GB peak memory for the first wrapper; we
did not re-run it for this page, so treat the figures as the harness's. The smallest case that
**passes** and shows the technique is `Tests/Ved/U1WireShareCheck.lean` (CRC chains).

*Minimal goal.* Accept the done-pulse output of the P-256 point-operation circuit (the smallest
of its three rows) at the default budgets, with refusal controls.

*Needed lemma (proposed shape, not yet in the tree).* A per-node soundness lemma for a table of
the circuit's nodes, and a connection lemma that equates the table's evaluation with the
declaration's value, each proved once:

```
-- schematic, not checked Lean
key_sound      : ∀ n ∈ table, evalNode table env n = valueOf decl env n
conn_equal_many: evalTable table env = outputsOf decl env
```

so that each cone is closed with only its direct dependencies. After a literal cut, the
arithmetic facts needed per node (`BitVec` identities modulo `2^w`, carry facts for shifts) have to
be listed as lemmas and proved once; that list is part of the task.

*Input/output contract.* Input: the declaration and its returned module (one synthesis). Output:
a proof of `U1Stmt contract mod decl` that passes the strict audit (standard axioms only).

*Success.* The refused rows above are accepted at default budgets, the table of
[appendix F](appendix/F-AllCommandRows.md) is regenerated from an approved measurement of the
changed code, and a mutant (one changed constant, one swapped operand) is refused.

*Where.* Lemmas next to `Tools/VedU1WireShare.lean` and `Tools/VedU1Wire.lean`; script changes in
`Tools/VedU1Entry.lean`. *Check to add.* `Tests/Ved/<Name>Check.lean` with the accept case and
the controls, a `lean_lib` entry in `lakefile.lean` and a step in `.github/workflows/ved.yml`.

## 2. Memories inside sub-modules

*Plain description.* The hierarchy statement covers a parent with registers and instances of
children. The memory statement covers one module with a memory. A parent whose **children own
memories** is covered by neither, and such rows are refused.

*Reproduce.* Write a small parent in the style of `Tests/Ved/U2HierRegCheck.lean` whose child
uses `Signal.memory`, and run the hierarchy entry (`#ved_u2_hier name`) on it. The expected result
is a refusal at the stage `hier-shape` or `shape` (not run for this page; the design records
[VED-HIER-H2D](../VED-HIER-H2D.md) list the supported shapes).

*Minimal goal.* One parent with one child that owns a read/write memory, accepted.

*Needed construction.* A closed run of the parent in which each instance path has its own memory
array, and the memory invariant (`MemInv`, `Tools/VedMem.lean`) lifted through the composition
lemmas of `Tools/VedU1HierComp.lean` and `Tools/VedU2Hier*.lean`.

*Contract.* Input: parent and child declarations, the returned design. Output: a hierarchy
statement of the shape of `U2HRStmt` extended with memory arrays per instance path, strict audit.

*Success.* One real row with a memory child accepted, and a refusal control (a mutated memory
write must be refused). *Where.* `Tools/VedU2HierReg.lean` (statement), `Tools/VedMem.lean`
(invariant). *Check.* `Tests/Ved/U2HierMemCheck.lean` (new) as in problem 1.

## 3. Deeper hierarchies and the composition theorem

*Plain description.* A parent's proof should use the children's proofs as lemmas instead of
unfolding them. In the release this works for **one level** of hierarchy with registers.
Modules that nest to depth two or more, optionally with memories, are refused, and the number of
instances should not change the statement.

*The statement, where its shape is known.* A parent's correctness does **not** follow from the
children's correctness and the wiring alone: the parent has its own output expressions, its own
next-state equations and its own initial state, and a parent with a wrong output or next-state
equation can still have correct children and correct wiring. So a composition theorem has to
say what is **reused** from the children and what the parent must **prove for itself**. The
release does this for one level of hierarchy (the theorem `outputsOnHS_of_stepR`, statement
`U2HRStmt`, `Tools/VedU2HierReg.lean`): the parent's proof is done against the *open parent*,
the parent in which every instance output is a free value, and the children are used only
through their own statements.

```
-- schematic, NOT checked Lean; names are illustrative.
-- "open parent": the parent's body in which each instance output is a free oracle value `o`.
theorem parent_of_children
  -- (1) REUSED from the children, not unfolded: each child's own theorem
  (hkids : ∀ i, KidStmt (kid i))
  -- (2) CONNECTION only (ports and renaming, per instance): the child's inputs are the
  --     parent's expressions at the call site; the child's outputs are read back by name,
  --     both after renaming the child's signals into the parent's namespace.
  --     This premise does not mention the parent's outputs or correctness.
  (hconn : Connected parent kids)
  -- (3) PROVED BY THE PARENT, against the open-parent meaning and the declaration:
  --     a state relation R between the parent's registers (and, for deeper hierarchies,
  --     the instance states) and the declaration's state
  (hinit : R 0 (initial_state parent))                       -- parent's own register inits
  (hout  : ∀ t s o, R t s → kids_give o s →                  -- own output equations
             open_outputs parent s o = declaration_outputs t)
  (hnext : ∀ t s o, R t s → kids_give o s →                  -- own next-state equations
             R (t+1) (open_next parent s o))
  : U2HRStmt contract mod design decl                        -- the parent's statement
```

In the release, `hinit`, `hout` and `hnext` are not premises of the user: the entry generates
and proves them for the parent from the facts of the deep preparation (`h0` and `hstep` in
`Tools/VedU2HierReg.lean`), and the children's outputs depend only on the parent's input streams, not on its registers, so the
state relation constrains the parent's own registers. The open point is a theorem of this shape
that stays true when instance states enter the relation (a child that keeps state the parent
reads back, depth two, memories) and that is uniform in the number of instances.

What is *not* known is the shape for depth two or more together with memories, and for
a statement uniform in the number of instances.

*Reproduce.* In the release, the refused nested-hierarchy rows show up in
[appendix F](appendix/F-AllCommandRows.md) with blocker `hier-shape`. The work in progress on
this problem is described, unreviewed, in
[PerCircuitVerification.md](PerCircuitVerification.md#6-in-progress-not-in-this-release-not-reviewed)
and the [development snapshot](appendix/E-DevelopmentSnapshot.md); do not rely on it.

*Minimal goal.* The statement and proof of `parent_of_children` over the release's definitions
(or an explicitly named extension) for depth exactly two, for one real parent.

*Success.* Stated and proved in Lean; a generator that produces it for a real parent; accepted
under the strict audit; refusal controls (a mutated connection, a swapped child, another
circuit's facts are refused). A pen-and-paper sketch is useful input but is not the success
condition. *Where.* `Tools/VedU2HierStmt.lean`, `Tools/VedU2HierReg.lean`,
`Tools/VedU1HierComp.lean`. *Check.* A `Tests/Ved/*Check.lean` with accept and refuse cases.

## 4. The optimiser and the printer

*Plain description.* After the returned module is checked, an optimiser rewrites it and a printer
writes SystemVerilog. Neither has a preservation theorem in the release, so the guarantee stops
before them (rungs 3 to 5 of the [ladder](README.md#the-guarantee-ladder)).

*Reproduce.* `lake build Tests.Ved.WriteCheckedCheck` shows the part that exists: the writer
receives the checked module.

*Statements wanted.* (a) `optimizeModule m` has the same outputs as `m` on every run; (b) the
printed text parses to a module with the same outputs. Today only a fragment of the expression
layer is proved (`roundtrip_sem`, `Tools/SVParser/RoundtripProof.lean`).

*Minimal goal.* (a) for the fragment the strict rows use, or a translation check that is validated
once and run per circuit (as the checker itself is). *Contract.* Input: a module; output: a proof
of equal outputs, or a refusal. *Success.* Accepted for the strict rows' fragment with refusal
controls. *Where.* `Sparkle/Backend/` (optimiser, printer) with the proof next to
`Sparkle/IR/ReorderInvariance.lean`; the SystemVerilog side next to `Tools/SVParser/`.

## 5. One theorem for all bit widths

*Plain description.* Today each circuit instance gets its own theorem. A parametric design (a
multiplier of width `w`) should get one theorem, uniform in `w`; other tools do this for
their parametric designs.

*Minimal goal.* The per-circuit statement for one family (an `n`-bit register or an adder),
proved once for all `n` over a parametric declaration. *Contract.* Input: a declaration with a
width parameter; output: `∀ w, U1Stmt …`. *Success.* Accepted under the strict audit with a
control at a width where the module is wrong. *Where.* a new file under `Tools/` beside
`Tools/VedU1Contract.lean`.

## 6. The general theorem: a witness for the runtime laws

*Plain description.* A theorem for *every* source the compiler accepts needs facts about the
Lean runtime in which the compiler runs. Those facts ("laws") have been stated, but nobody has
shown that a model exists in which they all hold together and that matches the real run
([CompilerGeneralTheorem.md](CompilerGeneralTheorem.md)).

*Statement wanted.* A *non-vacuous*, jointly satisfiable model of the laws, with a bridge from
the real compiler run to the model: a proof that the real run satisfies the laws, or a
replacement of them by a different boundary that the kernel can discharge.

*Reproduce.* The conditional theorems and the refutations of the older laws are on public
branches listed in [CompilerGeneralTheorem.md](CompilerGeneralTheorem.md); building them is
described in [appendix C](appendix/C-Reproduction.md).

*Success.* Either the laws are shown satisfiable by the real runtime for the entry's executions
(then the class-general theorem loses premises), or a precise argument, stated as a theorem,
that the boundary cannot be crossed in Lean without a stronger primitive. A model that only
satisfies the laws vacuously does not count.

## 7. A same-condition comparison with other tools

*Plain description.* [RelatedWork.md](RelatedWork.md) compares approaches by their documents. No
number there is a comparison.

*Minimal goal.* One design that Sparkle and one other tool both verify, for the *same* property,
with machine, versions and effort reported. *Success.* A published benchmark that someone else
can rerun.

## 8. Applying the system to a large SoC

*What a collaborator brings.* A real design of SoC scale (several blocks, memories, a bus,
registers across hierarchy levels) that can be written in the Sparkle DSL or ported to it, and
knowledge of what it must guarantee. Knowing which synthesis flow and checks the team already
trusts is as useful as proof skill.

*Where to start.* Do problem 0. Then take one block and try the entries in the order of the
[ladder](README.md#the-guarantee-ladder): the basic entry for a block without instances, the
hierarchy entry for a parent with registers, then the checked writer. Record for each block
whether it was accepted or refused and the stage that stopped it (`table`, `order`,
`hier-shape`, `proof`, …; [Coverage327.md](Coverage327.md)). That list of refusal reasons is the
first deliverable.

*Success.* (1) The list of blocks with accept or refuse and the first blocker; (2) at least one
block refused in the release for a reason in problems 1 to 3 and then accepted by reviewed code,
with a refusal control; (3) time and memory of each accepted block on your machine. A whole-SoC
proof is **not** the success condition of a first step, and the release makes no claim that one
is reachable.

## What would count as success for the release effort

* A third party reproduces problem 0 from public refs only.
* One of problems 1 to 3 closes a row that is refused in the release, with reviewed code and a
  refusal control, and the tables are regenerated from an approved measurement of the changed code.
* The general theorem is picked up again only under the condition in
  [CompilerGeneralTheorem.md](CompilerGeneralTheorem.md#6-what-is-kept-and-when-the-effort-could-resume).

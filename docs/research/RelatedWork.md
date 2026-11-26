# Related work

Closest neighbours of Sparkle's verified synthesis: Kami (and Kôika), SV / SVL / SVEXL, and
RP-Rewriter. For each: the object the theorem is about, the trust boundary of the artifact
that comes from Verilog or goes to Verilog, and the composition method, and how Sparkle differs.

**How facts were checked.** Every statement about another tool below was re-read at its primary
source for this revision: the Kami ICFP 2017 paper (full text), the Kôika PLDI 2020 paper and
repository README, the SVL CAV 2020 paper (PMC7363191), the RP-Rewriter paper (arXiv 2009.13765,
HTML version) and the SVEXL, SV and VL files in the ACL2 repository. The section or file is
given with each claim. Two limits: the SV/VL manual pages were not reachable, so "not stated"
about the Verilog translation means "not stated in the files we read"; and the follow-up
arXiv 2205.11703 was read at the abstract only. Nothing here is a claim about unread parts.
Two older candidates (Vericert, Lutsig) were taken out of this page because we did not re-read them.

**Performance.** There is **no same-condition comparison** between Sparkle and any tool below:
no common benchmark, machine, property or proof effort has been run. Numbers cited for other
tools are the authors' own, on their own designs and machines, and say nothing about Sparkle.
Sparkle's own times (in [appendix F](appendix/F-AllCommandRows.md)) are single runs including import
loading and carry no performance claim.

## Summary table

| | Kami / Kôika | SV / SVL / SVEXL (ACL2) | RP-Rewriter (ACL2) | Sparkle (this release) |
|---|---|---|---|---|
| Theorem is about | Kami: Bluespec-style modules as labelled transition systems in Coq. Kôika: a Coq-verified compiler from its rule language to a minimal circuit language | `svex` expressions and SVL netlists inside ACL2 | ACL2 conjectures with large terms | the IR module returned by one synthesis run |
| Proof relation | Kami: refinement (trace inclusion). Kôika: the circuits compute the same results as the source (`compiler_correct`) | SVL: soundness of the method proved in ACL2; SVEXL: `svex-eval` equals `svexl-eval` of the converted node array | the rewriter is a verified clause processor | kernel-checked theorem per circuit: IR outputs = Signal outputs |
| Verilog / hardware-text boundary | Kami: the Kami-to-Bluespec step is not verified (paper, section 7). Kôika: a "thin unverified" layer produces Verilog (README; paper section 6.5) | the Verilog-to-SV (VL) translation: no verification is stated in the sources we read; the SVL paper is silent | not part of the paper | printer and optimiser are outside the theorem (ladder rungs 3 to 5) |
| Composition | Kami: refinement is reflexive and transitive, composition is associative and commutative, refinement is modular (section 5.1) | SVL: a recursive run function over the hierarchy (section 2) | n/a | hierarchy statements per instance path; per-circuit, not parametric |

## Kami and Kôika

* **Kami.** J. Choi, M. Vijayaraghavan, B. Sherman, A. Chlipala, Arvind. *Kami: A Platform for
  High-Level Parametric Hardware Specification and Its Modular Verification.* Proc. ACM Program.
  Lang. 1(ICFP), Article 24, 2017. DOI 10.1145/3110268.
  <https://adam.chlipala.net/papers/KamiICFP17/KamiICFP17.pdf>, <https://github.com/mit-plv/kami>.
  Checked against the full paper.
  * *Theorem inside the model* (abstract, introduction, sections 3.2 and 5). Hardware components
    are labelled transition systems in Coq, for designs "in the style of the Bluespec language".
    The relation proved is refinement; the paper proves trace inclusion by a simulation relation
    between states, built from rule and method correspondences.
  * *Composition* (section 5.1). Theorem 5.1: refinement is reflexive and transitive. Theorem
    5.2: composition of modules is associative and commutative with respect to it. Modular
    refinement substitutes one module for another. Designs are parametric: the multicore system
    was verified for an arbitrary number of cores and arbitrary cache sizes (section 7).
  * *Boundary of the hardware text* (section 7). "Currently, the entire synthesis process is part
    of Kami's trusted base. The compilation from Kami to Bluespec is not verified, but it is very
    straightforward." The extracted OCaml program prints a Bluespec program; the Bluespec
    compiler and the Xilinx toolkit below it are unverified. This item lists only the boundary
    added on the way to hardware text; it is not a list of the whole trusted base (the proofs
    themselves rest on Coq).
  * *Case study* (abstract, sections 1, 6, 7). An infinite family of multicore systems with
    cache-coherent shared memory and pipelined RISC-V cores (the base integer subset), correct
    with respect to sequential consistency; "about 25,000 lines of code" for the whole Kami
    infrastructure (section 6.5). A 4-core configuration was synthesised and run on a Virtex-7
    FPGA (section 7.1). We cite no timing or speed numbers from it.
* **Kôika.** T. Bourgeat, C. Pit-Claudel, A. Chlipala, Arvind. *The Essence of Bluespec: A Core
  Language for Rule-Based Hardware Design.* PLDI 2020. <https://adam.chlipala.net/papers/KoikaPLDI20/>,
  <https://github.com/mit-plv/koika>. Checked against the paper and the README.
  *Inside the model:* a compiler from the rule language to a minimal circuit language in Coq,
  with the theorem `compiler_correct` (`coq/CircuitCorrectness.v`): the produced circuits compute
  the same results as the source programs (README; paper section 6.5). *Boundary:* the paper
  (section 6.5) converts the circuit language to Verilog "with a thin unverified pretty-printing
  layer", and the README says the same of `cuttlec`; tools below that are not verified either.
* **Differences.** Kami and Kôika verify *designs written in their own rule languages* (Kami:
  parametric, modular refinement, hand-written proofs); the text that goes to the hardware tools
  is produced by an unverified step. Sparkle does not prove a theorem about its language as a
  whole for the old shipping compiler: the general theorem is unfinished, and what exists is
  conditional ([CompilerGeneralTheorem.md](CompilerGeneralTheorem.md)). Instead it generates a
  proof for each concrete circuit from the compiler's own output and refuses when it cannot.
  The one general, unconditional theorem it has covers a small closed grammar
  (`Cdo.elab_general`). Sparkle has no refinement theory across designs yet and no parametric
  statement; Kami has no per-instance check of an unverified compiler's output.

## SV, SVL and SVEXL (ACL2, Centaur books)

For each tool the page separates (i) the theorem *inside the model* from (ii) the trust
boundary of a *Verilog-derived artifact*: the step that turns Verilog text into the model the
theorem is about. Statements are what the cited sections say; "not stated" means the cited text
is silent, not that the step is unverified or verified.

* **SV and VL.** ACL2 community books `centaur/sv` and `centaur/vl`. The SV documentation
  (`books/centaur/sv/top.lisp`) says SV "is integrated with VL so that you can translate
  SystemVerilog and Verilog designs", and the topic `vl-to-svex` is described as the "translation
  of VL designs into an SVEX design". *(i) inside the model:* `svex` expressions have an
  evaluator `svex-eval`, and ACL2 proves theorems about them. *(ii) boundary:* neither the SV
  source file nor the VL documentation file (`books/centaur/vl/doc.lisp`) that we read makes a
  statement that the Verilog-to-SV translation is proved correct; the VL file carries an alpha-status
  warning. We did not read the VL manual topic pages (the manual site was not reachable), so we
  claim only: **no verification of the VL-to-SV step is stated in the sources we could read**.
* **SVL.** M. Temel, A. Slobodová, W. A. Hunt Jr. *Automated and Scalable Verification of Integer
  Multipliers.* CAV 2020, LNCS 12224. DOI 10.1007/978-3-030-53288-8_23.
  <https://pmc.ncbi.nlm.nih.gov/articles/PMC7363191/>. *(i) inside the model:* the abstract says
  "We have proved the soundness of this method using the ACL2 theorem prover"; the lemmas are
  proved in ACL2 and their proofs are omitted from the paper. Netlists in SVL form are kept
  hierarchical and are simulated by a recursive run function that traverses the occurrences of a
  module (section 2, preliminaries). Adders are rewritten first (each adder's gate-level logic
  against a specification built from sum and carry functions), then summation trees and partial
  products including Booth; the final specification is **word-level** multiplication of the
  inputs, truncated to the output width. Reported results: multipliers up to 1024 × 1024, from 3
  generators and, in the paper's words, 8 different types, verified "in less than 10 min" by this
  tool, with memory growing "as big as 30 GB" for the largest (results section and Table 3; the
  per-type values are in the table). Stated limits: the method "relies on maintaining circuit
  hierarchy"; "we have not proved the completeness of this method"; a failed proof gives no
  user-friendly message; array multipliers are the type for which the tool "struggles to scale".
  *(ii) boundary:* the Verilog is converted to SVL netlists with the SV and VL libraries; **the
  paper does not state whether that translation is verified or trusted**, and we found no
  trusted-base statement in the paper.
* **SVEXL.** ACL2 books `centaur/svl/svexl/`
  (<https://github.com/acl2/acl2/tree/master/books/centaur/svl/svexl>). *(i) inside the model:*
  the directory contains `svexl.lisp`, `svexl-correct.lisp`, `svexl-eval-dollar*.lisp`,
  `svexl-fasteval*.lisp` and `svtv-run-with-svexl.lisp`. Expressions are a node array whose
  entries are `:quote`, `:var`, `:node id` (an index) or `:call`; a call term that occurs more than once
  (and is larger than a size threshold) becomes a node. `svexl-correct` (in `svexl-correct.lisp`),
  under the hypothesis `(svex-p svex)`, states
  `(equal (svex-eval svex env) (svexl-eval (svex-to-svexl svex) env))`; companions
  `svexllist-correct` and `svexl-alist-correct` do the same for lists and alists. We found no theorem
  in the other direction. This is the closest analogue to a Sparkle node table, but it is
  expression sharing only, not cycle semantics. *(ii) boundary:* as for SV; the theorem is
  about `svex` objects, not about the Verilog text.
* **Differences.** SV/SVL verify *given* netlists (typically arithmetic circuits) by rewriting
  to a specification inside ACL2. The theorems are inside the SV/SVL model; how well that model
  represents the original Verilog depends on the Verilog-to-SV translation, for which no
  verification is stated in the sources we read, so the guarantee for a Verilog file is **not**
  "the ACL2 logic" alone. Sparkle's object is its own compiler's IR, tied to the Signal source by
  a kernel proof (theorem inside Lean's model); the printed SystemVerilog and the optimiser are
  outside that theorem (ladder rungs 3 to 5). SVEXL's node-table idea is the model for an
  in-progress Sparkle route (see [PerCircuitVerification.md](PerCircuitVerification.md),
  section 6; not in this release).

## RP-Rewriter

* M. Temel. *RP-Rewriter: An Optimized Rewriter for Large Terms in ACL2.* ACL2 Workshop 2020,
  EPTCS 327, pp. 61-74. DOI 10.4204/EPTCS.327.5. <https://arxiv.org/abs/2009.13765>
  (read in its HTML version). *(i) inside the model:* section 5, "Verification of RP-Rewriter":
  "RP-Rewriter is a verified clause processor"; soundness is organised around three invariants
  (evaluation preserved with an evaluator, valid side conditions, well-formed term syntax;
  subsections 5.1 to 5.3), and `meta-extract` facts are used (5.4). The paper does not give a
  separate trusted-base statement. Applications: multiplier proofs up to 1024 × 1024
  (section 3.1) and SVEX simplification (3.2; there the main function is used as a logic-mode
  function rather than as a clause processor). Limits (sections 2.1 and 4): a hypothesis or
  right-hand side cannot contain a variable that is not in the left-hand side (no `bind-free`);
  the left-hand side cannot contain `if`; lambda expressions are beta-reduced before rewriting;
  `dont-rw` stops the rewriter at a marked term. *(ii) boundary:* it takes ACL2 conjectures as
  input; the Verilog-to-term step is not part of this paper (the multiplier work uses SVL, above).
  Follow-up: M. Temel, *Verified Implementation of an Efficient Term-Rewriting Algorithm for
  Multiplier Verification on ACL2*, arXiv <https://arxiv.org/abs/2205.11703> (abstract only
  read: a verified program that verifies multiplier designs).
* **Difference.** RP-Rewriter makes a *rewriting engine* sound once so that large terms can be
  simplified; the lesson Sparkle shares is the value of not rewriting shared subterms twice. It
  verifies no compiler. Sparkle's analogue is its generated, untrusted scripts whose result the
  kernel checks (the Lean kernel checks the theorem; the scripts need not be trusted); the strict
  audit forbids `native_decide` and any axiom outside the standard three (see
  [appendix/B-TrustBase.md](appendix/B-TrustBase.md)).

## Verifying the compiler once, or each output

Kôika (above) is an example of verifying the compiler once and for all; Sparkle's old shipping
compiler is not verified, and the attempt at a general theorem is unfinished
([CompilerGeneralTheorem.md](CompilerGeneralTheorem.md)). Sparkle instead verifies *each output*
(translation validation) on the returned IR.

## What this comparison does not claim

* No claim that Sparkle is faster, smaller, or more scalable than any of the above.
* No claim of a stronger or weaker guarantee in general: the objects differ (own language vs
  netlists vs the output of an unverified compiler), as do the TCBs and the stage of the flow
  covered. The ladder in the [README](README.md#the-guarantee-ladder) shows where Sparkle stops.

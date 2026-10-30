# DC-CONNECT: the primitive table of `ConstValue` — decision material (NOT adopted)

Issue `sparkle-gen5-dc-connect`. Written with `scripts/gen5/DC_CONNECT_FREEZE.md` rev4 (§C.6). **Nothing here is adopted.** Approval of the Part C freeze does not depend on it.
Status of the issue: this is a candidate NEW TRUSTED boundary; the issue stays under reviewer review; if the user's decision is needed for the final goal the issue goes to `decision` then.

## 1. What the question is, with no prior knowledge

The final theorem of the gen5 line says: for every declaration the compiler succeeds on, the hardware equals the package `p.src`, AND `p.src` equals what the
declaration *means* in Lean. The second half is `DeclConnect`: "there is a Lean value `v` which is the meaning of the declaration `X`, and the package's
observation equals `v`'s observation". For that to be a theorem and not a per-declaration check, "the meaning of a declaration" must be a relation
`ConstValue env X α v` defined **once, for all declarations**, over the compiler's own data (`Lean.Environment`, `ConstantInfo`, `Expr`).

Lean's logic cannot look at its own constants as data. So the relation is built as an interpreter of `Expr`: literals, variables, lambda, application, let, and
"unfold a definition" are written once (these are ordinary definitions, nothing is stipulated). But an interpreter must also say what a *name that cannot be unfolded* means:
`Signal.register`, `Signal.loop`, `BitVec.add`, `Prod.mk`, `ite`, `Nat.add`, the types `Signal`/`BitVec`/`Prod`… Each such statement is a row
`Name ↦ Lean term` ("the constant called `Prod.mk` is Lean's `Prod.mk`"). Lean cannot check that sentence, because it is about the correspondence between a `Name`
datum and a constant of the logic. That list of rows is the **primitive table**. Whoever relies on the final theorem relies on the table being right.

Today this link exists only per declaration, outside the logic: the compiler emits `X.machine_source` and the kernel checks it by `rfl` for that declaration
(`GENERAL_SPEC.md:494-495`: "G3-DECL … a meta-level fact, generated per declaration today"; `Tools/Prototype/DGenStored.lean:14-18`: `ConstValue` "NOT FORMULATED … impossibility is NOT claimed").

## 2. Effect on the Project/Milestone goal

`DeclConnect` is the uniform G3-DECL of M5 ("FG proved with uniform premises only", `GENERAL_SPEC.md:498-500`). Without a decision on the table the issue can still deliver
the pure units (shape, adapter, abstract core, `FG_COMPLETE`'s statement) but not the row "`∃ α v, ConstValue env₀ X α v`" nor the final connection; the stopped successors are the final
`FG-REF ∧ ConstValueOk ∧ DeclConnect` assembly of `sparkle-gen5-decl-bridge` and M5's G3-DECL discharge. FG itself is not shrunk by any option below unless option C is chosen.

## 3. Options

| | option | what the user sees | trusted content | cost | notes |
|---|---|---|---|---|---|
| **A** | Adopt a stated primitive table `primTable₀` as a new TRUSTED boundary (G-PRIM): the rows are listed in the report, FG's final statement is "uniform" and relative to it | one more named trusted list in the guarantee statement, next to G7 | the table's rows | writing the table (size not measured, see §5), the `ConstValueE` freeze and proofs of rows 0-5; a build-time meta check per row (name resolves, `inferType` of the constant equals the row's type) as an audit — an execution check, **not** a proof | the table is a plain `def`; no axiom |
| **B** | A *minimal* table: unfold every `defnInfo` (const-unfold) and leave in the table only the constants with nothing to unfold (constructors, recursors, quotient primitives, opaque/`extern`/`implemented_by`, type formers) | the same kind of boundary, smaller and uniform | the rows for kernel primitives only; rows come mechanically from `ConstantInfo` kinds | a larger derivation per declaration (more unfolding); the recursor rows need a general rule from `RecursorVal.rules` | not measured: it is not known how large the residue is for the corpus; it may need the recursor rule to be written as a definition over `Expr` reduction, which is a bigger formalisation |
| **C** | Do not adopt a table: keep G3-DECL per declaration (state (i) of `GENERAL_SPEC.md:501-503`, a CONDITIONAL result reported row by row) | FG is reported as conditional on G3-DECL per declaration | none new | none now | this is a **guarantee change** (`GENERAL_SPEC.md:503-504`: moving the goal from completion to (i) needs the user), not recommended unless A/B prove infeasible |
| **D** | Have the compiler emit a kernel-checked per-declaration link and take a uniform statement from it | unchanged guarantee text, stronger evidence | none new | a compiler change (`Elab*.lean`): forbidden without user approval; unknown size | listed for completeness; not designed here |

## 4. Recommendation

Prefer **B, adopted as A's stated boundary** (a minimal, mechanically derived table, with the per-row build-time meta check as an audit and clearly reported as TRUSTED), because it keeps FG's
strength, adds no axiom, and keeps the table as small as the unfolding allows. This is a recommendation for the user to accept or reject; it is not a decision, and the survey that would size the residue
(count the distinct non-unfoldable constants after maximal unfolding over the accepted corpus declarations) has NOT been run. The recommendation is conditional on that size being reviewable.

## 5. Reversibility, and what happens without a decision

- **Reversible:** yes. The table is additive Lean (a `def`), no existing file or proof changes; dropping it later returns to the present state. If the table is adopted and a row is later found wrong, only the rows depending on it change.
- **Without a decision:** the units U-UNIV, U-SHAPE1/2, U-ENTRY, U-ROWS of the Part C plan proceed; DCF (`ConstValueE`) and the existence row stay unsupplied; the final theorem stays an intermediate result (FG-REF plus the abstract `DeclConnect`), reported as such. Nothing is claimed complete.
- **Not measured:** the number of rows; how many of them are type formers; whether the recursor rows can be derived from `RecursorVal.rules`; whether the corpus needs `Signal.loop` as a primitive or can unfold it.

## 6. Evidence

- `scripts/gen5/DC_CONNECT_FREEZE.md` rev4 §C.6 (rule classification) and §C.7 (supplier table).
- `scripts/gen2/GENERAL_SPEC.md:488-507` (M5 boundary discharge, reporting rule), `:535` (§6 table, link row).
- `Tools/Prototype/DGenStored.lean:14-18` (the same meta-fact for stored constants: "NOT FORMULATED").
- `Tools/ShippingGen2Pkg.lean:55`, `Tools/ShippingMachineSource.lean` (`stateLoop`), `Tools/ShippingMachineCommand.lean:2599-2610` (`X.machine_source`: the per-declaration link).
- `git show par/gen5-t2:scripts/gen5/DGEN_FREEZE.md` §2.6 (why the implication form is not enough: it is true for the empty relation).

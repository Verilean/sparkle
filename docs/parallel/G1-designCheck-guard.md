# G1: a print guard on the accepted optimizer candidate — DESIGN ONLY (round optfb-5)

Status: paper. Nothing here is implemented; no compiler file was touched.
The Lean files this note refers to as "this round"
(`Tools/ShippingClosedTyped.lean` and the files it imports) were NOT built
at the time of writing.

## What the guard is for

`designCheck (childMap D.modules) n (checkedOptimize b)` is the one
remaining check premise of the generated depth SV endpoints of `parent` and
`chained`. Of its parent-module conjuncts, 2 (`seqCheck`) and 3 (the width
tables) are checks on the EMITTED TEXT of the shipped module
`o = checkedOptimize b`.

* When `o = b` (the two fallback branches), this round derives both from
  the core run: `core_text_raw`
  (`seqCheck (wofOf b) (weS b) b.body = true ∧ widths`, for the RAW module,
  no optimizer in the statement) under two data conditions on the output
  ports (`hon`, `hoty`: stable names, scalar types).
* When `o` is an accepted candidate `o' = deinline b (optimizeModule b)`,
  nothing gives them: `hierRefineCheck b o'` is a check on values over the
  extracted interface and has no name, declaredness or operand-width
  conjunct (`docs/parallel/G1-designCheck-text.md`, section D). On the
  census the optimizer changes EVERY measured real parent, so this is the
  case real parents are in.

The guard turns the second case into the first by a case split:

    textGuard o' :=
      seqCheck (wofOf o') (weS o') o'.body &&
      (seqNames o'.body).all (fun x => declWidth o' x == weS o' x)

    keep the candidate only if textGuard o' ; otherwise ship the input module

Then, for every run,

    shipped = o' and textGuard o' = true      -- conjuncts 2, 3 hold BY the guard
    or shipped = b                            -- conjuncts 2, 3 hold by core_text_raw

and `core_designCheck_rest` would keep only `hports` (`portsMatchB`) and
`hkids` (the children). The guard is a fallback, never a rejection: the
compiler always ships a module, as with the existing guards G2 / G4 and
`masksKept`.

## Where it would go — two places, different blast radius

### P1: in `checkedOptimize`'s hier branch (`Sparkle/IR/RefineCheck.lean` 356–358)

    else if RefineCheck.hierBinds m then
      let o' := Sparkle.IR.HierCheck.deinline m o
      if RefineCheck.hierRefineCheck m o' && textGuard o' then o' else m

Touched: every lemma that unfolds `checkedOptimize` down to this branch or
rewrites with its equation. Counted by `grep` on this branch (files with a
site that unfolds `checkedOptimize` or uses `checkedOptimize_binding` /
`_not_binding`): 18 files, 34 sites. The ones about the hier branch, which
need a real edit (the condition of the `if` changes):

* `Tools/ShippingGuardsSound.lean`: `checkedOptimize_binding` (statement:
  the `if`'s condition), `checkedOptimize_facts` (its `by_cases hacc`),
  `checkedOptimize_not_binding` (unaffected in statement; its `simp only`
  list may need the new name);
* `Tools/ShippingChecksDepthGate.lean` (`checkedOptimize_inst_iff_gate`, 2
  sites), `Tools/ShippingChecksDerived2.lean` (`checkedOptimize_inst_iff`),
  `Tools/ShippingHierShipsSV.lean` (`checkedOptimize_inputs`),
  `Tools/ShippingShipsFree.lean` (4 sites, `checkedOptimize_fallback`),
  `Tools/ShippingShipsHierFree.lean` (2), `Tools/ShippingShipsNoOuts.lean`
  (1), `Tools/ShippingMachineShipsHier.lean` / `…HierH.lean` (1 each),
  `Tools/ShippingOptSoundness.lean` (`checkedOptimize_wires_sublist`,
  `_ports`, `_sound`: 3 sites — they split all four branches).

The other sites (`simpleBody` and `seqStmtOk` branches: `ShippingSVBridge`,
`ShippingPrintSoundness`, `ShippingControlOptSoundness`, …) unfold the same
definition; with the guard added only in the hier branch their `simp only`
lists should still close, but each must be rebuilt. Each accepted-case
proof gets one more conjunct to split (`Bool.and_eq_true`); the pattern is
the one used when `masksKept` was added to `mergeChecked`
("three existing proof sites repaired by `and_left_true`").

### P2: inside `keepGuarded` (`Sparkle/IR/HierCheck.lean` 204–206)

    def keepGuarded (m o : Module) : Module :=
      if decide (instNamesOf o.body).Nodup && linkedWFX ((openIns m).map (·.name)) o.body
          && textGuard o then o
      else m

`checkedOptimize` is NOT changed textually, so none of the 34 sites above
is touched by unfolding. Touched instead: `keepGuarded_cases` and
`deinline_cases` (a third conjunct in the left disjunct) and their users —
6 sites in `Sparkle/IR/HierCheck.lean`, 1 in
`Tools/ShippingGuardsSound.lean` (`deinline_guards`), 1 in
`Tools/ShippingOptSoundness.lean`; each is an `rcases … with ⟨e, h1, h2⟩ | e`
that gets one more component.

Semantics of P2: the guard is evaluated on the candidate BEFORE
`hierRefineCheck`; when it fires, `deinline m o = m` and `checkedOptimize`
then evaluates `hierRefineCheck m m` (as it already does when G2 / G4
fire). The shipped module is `m` either way.

P2 is the smaller change. P1 states the intent at the place the decision is
made. Either gives the same case split for the proof:

    theorem core_text_shipped (… core_text_raw's hypotheses …) :
      seqCheck (wofOf (checkedOptimize b)) (weS (checkedOptimize b)) (checkedOptimize b).body = true ∧
      (seqNames (checkedOptimize b).body).all (declWidth … == weS …) = true
    -- by: checkedOptimize b = b (three ways) → core_text_raw;
    --     checkedOptimize b = o' with the guard true → the guard, verbatim

## The obstacle that decides the cost: where `seqCheck` lives

`seqCheck`, `sf4Check` and what they call (`exprWidthT`, `shlOperand`,
`immuneE`, `isShlLit`, `shlSideOK`, and for the memory arm
`readPortsCheck`, `payloadCheckC`) are defined in
`Tools/SVParser/EmitSem.lean` (imports `Tools.SVParser.EmitAst`,
`Tools.SVParser.SVSemantics`). `Sparkle/IR/RefineCheck.lean` and
`Sparkle/IR/HierCheck.lean` import no `Tools` module (stated policy in
`Sparkle/IR/PrintCheck.lean`: "No proof-only `Tools` module is imported
here"), and nothing under `Sparkle/Compiler` or `Sparkle/IR` imports
`Tools`. So the guard cannot call `Tools.SVParser.EmitSem.seqCheck` from
either place. Three ways, in order of size:

1. A Sparkle-side executable twin `Sparkle.IR.PrintCheck.seqTextCheck`
   (assignments, registers, instances; no memory arm — the hier gate has
   already excluded memories) with its own `sf4`-twin, and a Tools-side
   theorem `seqTextCheck (widths o) … o.body = true → seqCheck (wofOf o) (weS o) o.body = true`.
   `Sparkle.IR.PrintCheck.widths` is already the same function as
   `moduleWof` (same lookup, same type cases). The twin of `sf4Check` is
   ~60 lines of definition; the bridge is an induction over `Expr` with the
   usual two-matchers problem (no `rfl` across the two definitions). A
   one-directional bridge (twin ⇒ original) suffices and lets the twin be
   STRICTER and simpler than `sf4Check` (e.g. no `bitwiseShl` route) — at
   the price that the guard may fire where `seqCheck` would pass; the census
   below must then be re-run with the twin.
2. Move the executable checks out of `Tools/SVParser/EmitSem.lean` into a
   `Sparkle/IR` module and re-export them. No twin, no bridge; but
   `EmitSem.lean` is 4.6k lines of proofs keyed on these definitions' names
   and equation lemmas.
3. Keep `checkedOptimize` as it is and apply the guard one level up, in the
   printing entry (`Sparkle/Compiler/Elab.lean` 8828,
   `toVerilog (checkedOptimize module)`), from a module allowed to import
   `Tools.SVParser`. This changes what "the shipped module" is in every
   head (`checkedOptimize b` appears in the statements of the generated
   endpoints) and makes the compiler import the SV parser's semantics file.
   Not recommended.

Recommendation, for the user to decide: P2 with way 1.

## What the census says

`DESIGNTEXT CENSUS` (`Tests/Compiler/DesignTextTest.lean`, compiled
evidence, nothing asserted): over the 30 candidate declarations,
`seqCheck` is true on `b` for 30 of 30 and on the shipped module for 30 of
30; `checkedOptimize b == b` on none of the real parents. So the
`seqCheck` half of the guard would NOT fire on any measured declaration:
the shipped text of all 30 is unchanged by the guard.

Not in the census line: the width-table half (conjunct 3) is logged per
declaration (`widths=` column, for `b` and for the shipped module) but is
not aggregated. It must be read from the build log (or the census extended
by one counter) before the decision; with way 1 the census must count the
TWIN's verdict, not `seqCheck`'s.

Not measured: the compile-time cost. `sf4Check` is linear after the fix
recorded in its definition's comment (one recursive call on the left
operand; "249 nodes became 19.7 M calls" before), and `seqNames` /
`declWidth` are list lookups (quadratic in the worst case, as in the
existing `forwardCheck`). The guard runs once per instance-bearing module
whose candidate passed G2 / G4.

## What the guard does not close

* Conjunct 7, `portsMatchB` (connection widths against the CHILD's emitted
  map): it needs the child map, and `keepGuarded` is design-free. A guard
  for it would have to live where the children are known. Unchanged: a
  hypothesis.
* The children's check (`hkids`).
* The fallback itself: when the guard fires the shipped module is `b`, and
  conjuncts 2, 3 then rest on `core_text_raw` — i.e. on the two data
  conditions on the declaration's output ports (`hon`: names
  sanitize-stable; `hoty`: one bit or bit vectors). For a declaration that
  fails one of them, `seqCheck` is false on `b` (the output assignment
  fails `sanitizeName l == l` or `wof l == some _`), the guard fires on
  every candidate that keeps the output assignment's target, and
  `designCheck` is false of the shipped module: no theorem can discharge it.
  That is a property of the declaration, decidable per declaration.
* Instance-free register machines (`machine_ships_wired`): their two text
  antecedents (`seqCheck … (checkedOptimize b).body`, the width tables) are
  in the `refineCheck m o` branch of `checkedOptimize`, which this guard
  does not touch. The same guard in that branch, with
  `closeMachine_typed` at `M = closeMachine lay t'` (no closing of calls:
  the simpler half of this round's chain), would discharge them the same
  way. Not designed further here.

## What exists after this round for the fallback side (all UNVERIFIED until built)

    transition_typed_of_run   Tools/ShippingTransitionTyped.lean
    closedTransition_of_run   Tools/ShippingClosedTransitionTyped.lean
    closeMachine_typed        Tools/ShippingCloseMachineTyped.lean
    TypedIn, TypedIn.text, TypedIn.seqCheck   Tools/ShippingTextTyped.lean
    core_closed_typedIn, core_closed_typed, core_text_raw   Tools/ShippingClosedTyped.lean

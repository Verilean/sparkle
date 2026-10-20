# G1 — `kidsMaskedN` for leaf children: what blocks it (round 15)

Nothing here was built or run; it is read from the sources.

## The blocker

`kidsMaskedN` asks, per output port `p` of a child module,
`outMasked`: one writer, and a statement `assign p.name r` with `r` a
CONSTANT or a SLICE (`selfMasked`, `Tools/ShippingMachineShipsHier.lean`)
no wider than the port.

A leaf child's module in the design is its full entry's result:
`dropZeroWidthModule M` or `mergeChecked (dropZeroWidthModule M)`, with `M`
the closed machine. In `M` the output assignments are
`assign o.name (slice (ref w) (lo + width - 1) lo)` — masked.

`mergeChecked m` is `m` or `mergeDuplicates m`
(`Sparkle/IR/RefineCheck.lean`, `mergeChecked_cases`), and
`mergeDuplicatesParts` (`Sparkle/IR/RegDedup.lean`, lines 234–294) ends with

    let body := m.body.map fun st =>
      match definedNode st with
      | some n => match subst.get? n with
        | some r => .assign n (.ref r)          -- the node becomes an ALIAS
        | none => mapStmtExprs rename st
      | none => mapStmtExprs rename st

Its comment says so explicitly: "Every non-representative becomes an alias —
user-named ones too". (`outputSet` is computed at the top of the function
and not used.) So if the partition refinement puts an output's node in a
class with an EARLIER node, the output's statement becomes
`assign out (ref rep)`: a reference, which `selfMasked` REJECTS.

`refineCheck m r` (the acceptance test of the merge on a body with
registers) compares normalised definitions: it constrains what the output
computes, not the syntax of its right-hand side. `refineCheck_outs_assigned`
gives "assigned", nothing about the form.

I believe the bad case does not happen for a closed machine with positive
output widths: the output slices are of the packed wire `w` at pairwise
different offsets, the `next` assignments are slices of `w` at the slots'
offsets, nothing in the transition body reads `w`, so no earlier node has an
output's signature. The measurement agrees (`kidsMaskedN` is true on all 27
parents). But PROVING it needs a theorem about the partition-refinement loop
itself — `Id.run do` with three `HashMap`s, two nested `for`s and a `break`
— and no lemma about `mergeDuplicatesParts` exists beyond
`mergeDuplicates_ports`. That is the blocker; (b) and (c) below are not.

## What is not blocked

For the UNMERGED module (`y.1 = dropZeroWidthModule M`, body `M.body`):
* (b) single writer: `closeMachine_body` gives
  `M.body = B ++ (nexts ++ (registers ++ outAssigns w outs))` and
  `Acyclic (B ++ (nexts ++ outAssigns w outs))`; `Acyclic.nodup` gives
  distinct writes; `stmtWrites` of a register is `[]`
  (`Sparkle/IR/ReorderInvariance.lean:76`), so the registers add no writer.
* (c) width: `0 < o.width` from `outsOk`, `p.ty.bitWidth = o.width` from
  `outTy`.
Not written this round: without the merged case it removes nothing.

## Ways out (a decision, not mine)

1. A guard in `mergeChecked`, as a FALLBACK (same spirit as the P1 patch):
   keep the merge only if every output port that is assigned by a
   self-masked expression in `m` still is in the merged module, else return
   `m`. Then `mergeChecked m = m ∨ masksKept m (mergeChecked m) = true` is
   a two-line lemma and the leaf fact follows from (b), (c). It never
   rejects a source. It changes the shipped module only where an output
   would have become an alias — by the measurement, nowhere in the corpus;
   to be confirmed with `compare_outputs.py`.
2. Make `mergeDuplicatesParts` skip module outputs (use the `outputSet` it
   already computes). Changes the compiler's merge; still needs a lemma
   through the loop to say the final `map` is what ran.
3. Weaken the check instead of the compiler: let `outMasked` accept
   `assign p (ref x)` when `x` is itself assigned once by a masked
   expression of that width (one alias step). `KSn_boundedIn`'s proof needs
   the corresponding extra case; then the merged case needs "the alias
   target is the representative's slice", which again is a fact about the
   loop — so this does NOT avoid the blocker.
4. Prove the property of the loop. Possible in principle (the kernel
   unfolds it), expensive, and fragile against any edit of the pass.

Option 1 is the only one whose proof obligation is small.

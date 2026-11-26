import Lean

/-!
# The resource budget of the hierarchical checker's register-parent route (H2e)

The checker for a parent with registers (`Tools/VedU2HierRegEntry.lean`) and the state export of its nested circuits
(`Tools/DeepElab.lean`, `Tools.DeepNested.exportNested`) used FIXED limits: the whole check ran with `maxRecDepth 100000`
and `maxHeartbeats 8000000` whatever the caller had set, and the nested export with 65536 and 1600000 (which also
LOWERED a larger caller limit).  They are now options in the style of `ved.u1.proofRecDepth` / `ved.u1.proofHeartbeats`
(`Tools/VedU1Entry.lean`), with the same formula `max caller floor`: a finite caller limit below the floor is raised to
it, one above is kept; a caller limit of `0` (unlimited) combined with a floor `> 0` becomes the FINITE floor, so an
unlimited caller limit is not kept in that case.  `0` as the option means no extra floor (the caller's limit applies as
it is, unlimited included).  The defaults are the former constants.

* `ved.u2.hierRecDepth`, `ved.u2.hierHeartbeats` (thousands): the register-parent check as a whole;
* `ved.u2.nestedRecDepth`, `ved.u2.nestedHeartbeats` (thousands): the export of the state theorems of nested loops.

A limit is a bound, not a check: the kernel still checks the result in full.
-/

open Lean

namespace Tools.VedU2HierBudget

register_option ved.u2.hierRecDepth : Nat := {
  defValue := 100000
  descr := "VED U2 hier (register parent): lower bound on maxRecDepth for the whole check (0 = the caller's limit only)" }
register_option ved.u2.hierHeartbeats : Nat := {
  defValue := 8000000
  descr := "VED U2 hier (register parent): lower bound (thousands) on maxHeartbeats for the whole check (0 = the caller's limit only)" }
register_option ved.u2.nestedRecDepth : Nat := {
  defValue := 65536
  descr := "VED U2 hier: lower bound on maxRecDepth while exporting the state theorems of nested loops (0 = the caller's limit only)" }
register_option ved.u2.nestedHeartbeats : Nat := {
  defValue := 1600000
  descr := "VED U2 hier: lower bound (thousands) on maxHeartbeats while exporting the state theorems of nested loops (0 = the caller's limit only)" }

/-- The options of a command scope with `maxRecDepth` / `maxHeartbeats` raised to the floors. -/
def floorOpts (o : Options) (recOpt : Lean.Option Nat) (hbOpt : Lean.Option Nat) : Options :=
  let o := Lean.maxRecDepth.set o (max (Lean.maxRecDepth.get o) (recOpt.get o))
  Lean.maxHeartbeats.set o (max (Lean.maxHeartbeats.get o) (hbOpt.get o))

/-- `k` with the core context's limits raised to the nested-export floors. -/
def withNestedBudget {m : Type → Type} [MonadWithReaderOf Core.Context m] {α} (k : m α) : m α :=
  withTheReader Core.Context
    (fun c => { c with
      maxRecDepth := max c.maxRecDepth (ved.u2.nestedRecDepth.get c.options),
      maxHeartbeats := max c.maxHeartbeats (ved.u2.nestedHeartbeats.get c.options * 1000) }) k

end Tools.VedU2HierBudget

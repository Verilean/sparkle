import Lean
import Tools.VedMemLoop
import Tools.VedMemS94Local

/-!
# Opaque `memState` atoms for the local closers (`ved.mem.s94Opaque`, sparkle-ved-mem-s94, s94s)

Observed (s94r, `ved_tree_diag`): the 1e7 .. 3.5e7-node trees of the class-B goals are INSIDE the port arguments of the `memState` atoms
(`memState init writeAddr writeData writeEnable n addr`: the eight arguments before `addr` hold `Signal.mk (fun t => ..)` over `Signal.val (loop ..)`), while the arithmetic
of the goal only sees `memState .. addr : BitVec w` as an unknown word.  The size guard of the local closer (`ved_local_small`), `ved_cone_clear` and `omega` pay for those arguments
although no step ever opens them.

`ved_mem_opaque`: every distinct partial application `key = memState <8 arguments>` of the target (after the address step, `ved_mem_addr_l` / `memCanon` made two spellings
of one memory one key) is abstracted to a fresh variable `ved_M<i> : BitVec aw → BitVec dw`; the atoms become `ved_M<i> addr` (the address argument stays visible, and is itself
abstracted for the atoms it contains).  The abstraction is NOT a hypothesis-free weakening: the new goal is `∀ M, tgt[key := M]` and the old goal is closed by applying it to the
keys (the defining equation is `rfl`, kept aside as the proof term, nothing is added to the context), so a closer that proves the abstracted goal proves the original one,
and the kernel checks the instantiation.  The new route only (option `ved.mem.s94Opaque`, default false; the Entry hunk adds one stage step after the local route).
-/

namespace Tools.VedMemS94Opaque

open Lean Meta Elab Tactic Tools.VedU1WireShare Tools.VedMemS94Local

register_option ved.mem.s94Opaque : Bool := {
  defValue := false
  descr := "ved memory tail (class B): after the address step, abstract each distinct memState key (its eight port arguments) to a fresh variable before the local closer, so that no closer walks the port arguments; the old tail is the fallback (default false)"
}

/-- test seams / counters (LocalCheck) -/
initialize opaqueHits : IO.Ref Nat ← IO.mkRef 0
initialize opaqueRefuse : IO.Ref Bool ← IO.mkRef false
initialize opaqueFailLate : IO.Ref Bool ← IO.mkRef false

/-- `ved_mem_opaque`: see the module comment; fails when the target has no `memState` atom (nothing is changed then) -/
elab "ved_mem_opaque" : tactic => do
  if ← opaqueRefuse.get then throwError "ved_mem_opaque: refused (test seam)"
  let (g, n) ← memOpaque (← getMainGoal)
  if n == 0 then throwError "ved_mem_opaque: no memState atom in the target"
  opaqueHits.modify (· + 1)
  replaceMainGoal [g]
  if ← opaqueFailLate.get then throwError "ved_mem_opaque: failed after its work (test seam)"

/-- the class-B stage step: the opaque abstraction and the local closer on ONE goal; a goal that is not closed stays exactly as it was -/
macro "ved_mem_opaque_local" : tactic =>
  `(tactic| first | (ved_mem_opaque; ved_local_goal) | skip)

end Tools.VedMemS94Opaque

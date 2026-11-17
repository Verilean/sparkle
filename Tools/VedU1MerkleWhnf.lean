import Lean
import Tools.VedU1Loop
import Tools.VedU1WireShare

/-!
# `ved_bit_simp_pk`: read the packed state wire back before the bit step (U1, unit sparkle-ved-merkle-whnf)

On a goal below `shareMinTree` the loop script's bit step (`ved_bit_simp`) runs on the registers still
packed in one wire (`(a * m + b) / m % w`): each `&&&` / `|||` / `^^^` of such a slice is a rewrite
candidate whose side condition `omega` has to refuse (its own 2M-heartbeat budget each time), and the
refusals add up to the proof budget (R165 `merkleRootHW`, 8 registers, 72 goals, ~180 `&&&`).
The packing step `ved_pack_simp` (a later stage of the same script) turns the slices back into the
register atoms, after which the bit step's side conditions are trivial.  This tactic runs that step
first on a goal below `shareMinTree` that has a packed-state slice (`hasPackedSlice`), then the unchanged `ved_bit_simp_share`.  UNTRUSTED: the
kernel checks the proof that results.
-/

namespace Tools.VedU1MerkleWhnf

open Lean Meta Elab Tactic

/-- the goal has a packed-state slice: `(a * m + b) / m'` (what `div_pack` / `mod_pack` read back).  A goal without one
(the single-register CRC bodies of `Tests/Ved/U1WireShareCheck.lean`) is left to the unchanged bit step: the pack step
rewrites its `% 256` / `/ 256` terms into forms whose `omega` side conditions then fail. -/
def hasPackedSlice (e : Expr) : Bool :=
  (e.find? fun x =>
    x.isAppOfArity ``HDiv.hDiv 6 &&
      (let n := x.getArg! 4
       n.isAppOfArity ``HAdd.hAdd 6 &&
         ((n.getArg! 4).isAppOfArity ``HMul.hMul 6 || (n.getArg! 5).isAppOfArity ``HMul.hMul 6))).isSome

elab "ved_bit_simp_pk" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  if Tools.VedU1Loop.treeSizeVal tgt < Tools.VedU1Loop.shareMinTree && hasPackedSlice tgt then
    evalTactic (← `(tactic| try ved_pack_simp))
    -- the step may have closed the goal
    if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| ved_bit_simp_share))

end Tools.VedU1MerkleWhnf

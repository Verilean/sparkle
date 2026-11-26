import Lean
import Tools.VedU1Lemmas
import Tools.VedU2HierXorAttr

/-!
# `ved_xor`: the complement of a bounded value, as a rewrite on the literal

H2e (R228).  The checksum `~~~(sum)` reaches the register-step goals as `x ^^^ 65535`.  `omega` does not read `^^^`;
`Tools.VedU1Lemmas.xor_ones` states the complement for `2 ^ k - 1`, a form the goal does not have (it has the literal
`65535`).  One lemma per width `1 ..= 64`, `v < 2 ^ k → v ^^^ (2 ^ k - 1) = (2 ^ k - 1) - v` with both numbers
literals, in the simp set `ved_xor`; the bound is a side condition for `omega`.
-/

open Lean Elab Command in
run_cmd do
  for k in [1:65] do
    let n := mkIdent (Name.mkSimple s!"ved_xor_ones_{k}")
    let bound := quote (2 ^ k)
    let c := quote (2 ^ k - 1)
    elabCommand (← `(
      @[ved_xor] theorem $n (v : Nat) (h : v < $bound) : v ^^^ $c = $c - v := by
        have := Tools.VedU1Lemmas.xor_ones v $(quote k) h
        simpa using this))

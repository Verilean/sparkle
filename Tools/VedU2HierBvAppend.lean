import Lean
import Sparkle.Core.Signal

/-!
# `ved_toNat_append`: `BitVec.toNat` of a concatenation whose result width is a literal

H2e (R228).  The signal helper `onesAdd16Sig` builds `0#1 ++ x : BitVec 17`, `0#15 ++ c : BitVec 16`.  The core lemma
`BitVec.toNat_append` has the width `m + n` on its left side; simp's unifier cannot solve `?m + ?n =?= 17`, so the lemma
never fires on the elaborated term (its operands are `BitVec 1` and `BitVec 16`, the declared width the literal `17`) and
the goal keeps `(0#1 ++ _).toNat`, which `omega` cannot read.  The simproc reads the operand widths from the operands and
instantiates the lemma with them; the two sides differ only in `1 + 16` against `17`, a closed Nat computation.
-/

open Lean Meta Simp in
simproc_decl ved_toNat_append (BitVec.toNat _) := fun e => do
  let_expr BitVec.toNat _ x ← e | return .continue
  let_expr HAppend.hAppend α β _ _ a b ← x | return .continue
  unless α.isAppOf ``BitVec && β.isAppOf ``BitVec do return .continue
  let pf ← mkAppM ``BitVec.toNat_append #[a, b]
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  return .visit { expr := rhs, proof? := some pf }

/-!
## `ved_sigval_append`: `(a ++ b).val t` for signals whose width index is a literal

The same obstruction one level up: `sigval_append` is stated at width `m + n`, and `Signal.pure` unfolded by the checker's
simp set (`{ val := fun _ => c }`) is not type correct at the instance transparency simp matches with.  The reduction is
definitional (`(a ++ b).val t ≡ a.val t ++ b.val t`), so a `dsimproc` builds the right side from the operand types and
does not look at the operands.
-/

open Lean Meta Simp in
dsimproc_decl ved_sigval_append (Sparkle.Core.Signal.Signal.val _ _) := fun e => do
  let_expr Sparkle.Core.Signal.Signal.val dom _ x t ← e | return .continue
  let_expr HAppend.hAppend α β _ _ a b ← x | return .continue
  let_expr Sparkle.Core.Signal.Signal _ αa ← α | return .continue
  let_expr Sparkle.Core.Signal.Signal _ βb ← β | return .continue
  let_expr BitVec m ← αa | return .continue
  let_expr BitVec n ← βb | return .continue
  let va := mkApp4 (mkConst ``Sparkle.Core.Signal.Signal.val [Level.zero]) dom αa a t
  let vb := mkApp4 (mkConst ``Sparkle.Core.Signal.Signal.val [Level.zero]) dom βb b t
  let r ← try mkAppM ``HAppend.hAppend #[va, vb] catch _ => return .continue
  let _ := (m, n)
  return .visit r

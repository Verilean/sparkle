import Lean
import Tools.VedU1Lemmas

/-!
# `ved_hier_close`: the closer of the hierarchical checker's register-step goals

The goals are equalities over the (abstracted) register atoms `deep.irState nm (inpU ins) t i`, with `%`/`/`/`+`/`*`
by literals, `if`s, and the bit operators of the generated net.  H2d found three things that kept them open or
expensive on real IP (R211, R228):

* the state of a loop is a PACK, `a * K + (b * K' + c % K') % K`: reading a field of it is `/` and `%` by
  literals, repeated at every `if` of the goal.  `omega` introduces new variables for each and splits the cases
  of every `if`: minutes and gigabytes on ten registers.  The pack is read back first, by the two bounded
  lemmas below and `Nat.mod_eq_of_lt` (their side conditions are discharged by `omega` from the register bounds
  in the context), so the goal speaks of the atoms only.
* `omega` does not read `^^^`, `&&&`, `|||` (the `~~~` of a bit is `x ^^^ 1`); after the case split they are
  applied to numerals or to a bit and a numeral again, and the literal reductions below evaluate them.
* `(0#1).toNat` of a Bool input's encoding is an opaque atom for `omega`.
-/

theorem ved_div_add_mul (a c K : Nat) (h : c < K) : (a * K + c) / K = a := by
  have hK : 0 < K := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt h, Nat.zero_add]

theorem ved_add_mul_mod (a c K : Nat) (h : c < K) : (a * K + c) % K = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]

theorem ved_mul_add_mod (a b K M : Nat) (h : K % M = 0) : (a * K + b) % M = b % M := by
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  rw [← Nat.mul_assoc, Nat.mul_comm a M, Nat.mul_assoc, Nat.mul_add_mod]

open Lean Elab Tactic in
/-- `ved_rt t`: `t`, with a runtime exception (maximum recursion depth, heartbeats) turned into an ordinary failure, so
that `first`/`try` go on to the next alternative (they rethrow runtime exceptions). -/
elab "ved_rt " t:tacticSeq : tactic => do
  tryCatchRuntimeEx (evalTactic t) fun ex => do
    if ex.isRuntime then throwError "ved_rt: {← ex.toMessageData.toString}" else throw ex

open Lean Meta Elab Tactic in
/-- Is `e` a proposition `omega` reads: (in)equalities of `Nat`/`Int` joined by `¬ ∧ ∨ ↔ →`? -/
partial def isArithProp (e : Lean.Expr) : MetaM Bool := do
  let e ← whnfR (← instantiateMVars e)
  match e.getAppFnArgs with
  | (``Eq, #[α, _, _]) | (``LT.lt, #[α, _, _, _]) | (``LE.le, #[α, _, _, _])
  | (``GT.gt, #[α, _, _, _]) | (``GE.ge, #[α, _, _, _]) =>
    pure (α.isConstOf ``Nat || α.isConstOf ``Int)
  | (``Ne, #[α, _, _]) => pure (α.isConstOf ``Nat || α.isConstOf ``Int)
  | (``Not, #[p]) => isArithProp p
  | (``And, #[p, q]) | (``Or, #[p, q]) | (``Iff, #[p, q]) => do pure ((← isArithProp p) && (← isArithProp q))
  | _ => pure false

open Lean Meta Elab Tactic in
/-- Clear every hypothesis that is a proposition `omega` cannot read (the instantiation's structural facts: shape,
order, design well-formedness, ...).  Not needed for soundness; `omega` otherwise inspects each of them, and on the
register-step goals of ten registers that cost gigabytes. -/
elab "ved_arith_ctx" : tactic => withMainContext do
  let mut g ← getMainGoal
  let lctx ← getLCtx
  for d in lctx.decls.toList.reverse do
    let some d := d | continue
    if d.isImplementationDetail then continue
    if (← isProp d.type) && !(← isArithProp d.type) then
      g ← g.tryClear d.fvarId
  replaceMainGoal [g]

macro "ved_hier_close" : tactic =>
  `(tactic| (
    (ved_arith_ctx;
      (try (ved_rt simp (config := { maxSteps := 4000000 }) (disch := omega) only
        [ved_div_add_mul, ved_add_mul_mod, ved_mul_add_mod, Nat.mod_eq_of_lt])))
    <;> first
    | (ved_rt omega)
    -- the case split exposes literals; they are evaluated BEFORE `omega` sees the goal (`x &&& 0` and the like make it
    -- raise a recursion-depth error)
    | (ved_rt ((repeat' split) <;>
        ((try simp (config := { maxSteps := 4000000 }) only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *) <;>
          (try simp (config := { maxSteps := 4000000 }) only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceXor,
            Nat.reduceOr, Nat.reduceAnd, Nat.reduceEqDiff, eq_self, Tools.VedU1Lemmas.xor_one_one,
            not_true_eq_false, not_false_eq_true, true_and, and_true, false_and, and_false, Nat.zero_and, Nat.and_zero,
            Nat.zero_or, Nat.or_zero, Nat.zero_xor, Nat.xor_zero, Nat.and_one_is_mod, Nat.one_and_eq_mod_two,
            Nat.mod_mod_self] at *) <;>
          omega)))
    | (ved_rt ((repeat' split) <;> simp_all <;> omega))))

import Tests.Ved.U1EntryCheck

/-!
# Stage of runtime-limit refusals in the U1 checker (`checkU1E`)

A REAL heartbeat / max-recursion exception raised while the checker elaborates
the proof is refused at `[proof]`; one raised in its synchronous kernel
`addDecl` is refused at `[kernel]` (before: both reached the catch-all
`[checker]`).  Each case is pinned through `expectRefused` (stage + none of the
checker's constants left); no OK line is printed.
-/

namespace Tests.Ved.U1StageCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Tools.VedU1Contract Tools.VedU1Entry
open Tests.Ved.U1EntryCheck

/-- Run `act` with a local heartbeat budget of `n` thousand (the context field). -/
def withBudget (n : Nat) (act : TermElabM α) : TermElabM α :=
  Core.withCurrHeartbeats <|
    withTheReader Core.Context (fun c => { c with maxHeartbeats := n * 1000 }) act

/-- Elaboration of the proof is the expensive part: a `decide` over a long fold. -/
def costlyDecide : TermElabM Syntax :=
  `(by exact (by decide : (List.range 1000).foldl (· + ·) 0 = 499500) ▸ delay8.ved_u1)

-- proof side: heartbeats (a budget of 150k: the checker's own steps fit, the `decide` does not)
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `stHb) do
  let m ← modOf ``delay8
  let stx ← costlyDecide
  discard <| withBudget 150 (checkU1 ``delay8 `stHb ``delay8 m (.term stx))

-- proof side: max recursion depth
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `stRec) do
  discard <| checkU1 ``delay8 `stRec ``delay8 (← modOf ``delay8)
    (.term (← `(by
      set_option maxRecDepth 5 in
      exact (by decide : (List.range 1000).foldl (· + ·) 0 = 499500) ▸ delay8.ved_u1)))

def fib : Nat → Nat | 0 => 0 | 1 => 1 | n+2 => fib n + fib (n+1)
/-- unchecked assignment: elaboration is cheap, the kernel does the work -/
def slowProof (n : Nat) : Lean.Elab.Tactic.TacticM Unit := do
  let g ← Lean.Elab.Tactic.getMainGoal
  let q ← mkEq (mkApp (mkConst ``fib) (toExpr n)) (toExpr (fib n))
  let h := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (toExpr (fib n))
  g.assign (mkApp (mkLambda `h .default q (mkConst ``delay8.ved_u1)) h)

/-- only the OPTION (what `addDecl` hands the kernel), not the elaborator's context limit -/
def withKernelBudget (n : Nat) (act : TermElabM α) : TermElabM α :=
  withOptions (fun o => o.set `maxHeartbeats n) act

-- kernel side: the proof elaborates cheaply (an unchecked `Eq.refl` assignment),
-- the kernel must unfold `fib 15`; the option `maxHeartbeats 1` is what `addDecl` hands it
/-- info: refused [kernel], clean -/
#guard_msgs in
run_cmd expectRefused "kernel" (checkerNames `stKer) do
  let m ← modOf ``delay8
  let stx ← `(by run_tac slowProof 15)
  discard <| withKernelBudget 1 (checkU1 ``delay8 `stKer ``delay8 m (.term stx))

-- the same proof under the default limit is not refused for cost (control: the cost is the limit)
/-- info: ACCEPTED -/
#guard_msgs in
run_cmd liftTermElabM do
  let m ← modOf ``delay8
  let stx ← `(by run_tac slowProof 15)
  discard <| checkU1 ``delay8 `stCtl ``delay8 m (.term stx)
  logInfo "ACCEPTED"

end Tests.Ved.U1StageCheck

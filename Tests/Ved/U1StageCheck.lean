import Tests.Ved.U1EntryCheck

namespace Tests.Ved.U1StageCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Tools.VedU1Contract Tools.VedU1Entry
open Tests.Ved.U1EntryCheck

def withBudget (n : Nat) (act : TermElabM α) : TermElabM α :=
  Core.withCurrHeartbeats <|
    withTheReader Core.Context (fun c => { c with maxHeartbeats := n * 1000 }) act

def show' (b : Name) (n : Nat) (stx : TermElabM Syntax) : CommandElabM Unit := liftTermElabM do
  try discard <| withBudget n <| checkU1 ``delay8 b ``delay8 (← modOf ``delay8) (.term (← stx)); logInfo "ACCEPTED"
  catch e => logInfo m!"{e.toMessageData}"
  logInfo m!"left: {(← getEnv).contains (b ++ `ved_mod)} {(← getEnv).contains (b ++ `ved_u1)}"

run_cmd show' `h1 200 `(by exact (by decide : (List.range 1000).foldl (· + ·) 0 = 499500) ▸ delay8.ved_u1)
run_cmd show' `h2 50 `(by exact (by decide : (List.range 1000).foldl (· + ·) 0 = 499500) ▸ delay8.ved_u1)
run_cmd show' `h3 20 `(by exact (by decide : (List.range 1000).foldl (· + ·) 0 = 499500) ▸ delay8.ved_u1)

def fib : Nat → Nat | 0 => 0 | 1 => 1 | n+2 => fib n + fib (n+1)
/-- unchecked assignment: the kernel does the work -/
def slowProof (n : Nat) : Lean.Elab.Tactic.TacticM Unit := do
  let g ← Lean.Elab.Tactic.getMainGoal
  let q ← mkEq (mkApp (mkConst ``fib) (toExpr n)) (toExpr (fib n))
  let h := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (toExpr (fib n))
  g.assign (mkApp (mkLambda `h .default q (mkConst ``delay8.ved_u1)) h)

def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, a => a
  | n+1, a => iter f n (f a)
def ackS : Nat → Nat → Nat
  | 0 => Nat.succ
  | m+1 => fun n => iter (ackS m) (n+1) 1
def ackProof (m n : Nat) : Lean.Elab.Tactic.TacticM Unit := do
  let g ← Lean.Elab.Tactic.getMainGoal
  let v := ackS m n
  let q ← mkEq (mkApp2 (Lean.mkConst ``ackS) (toExpr m) (toExpr n)) (toExpr v)
  let h := mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Nat) (toExpr v)
  g.assign (mkApp (mkLambda `h .default q (Lean.mkConst ``delay8.ved_u1)) h)

run_cmd show' `a1 200 `(by run_tac ackProof 3 6)
run_cmd show' `a2 200 `(by run_tac ackProof 3 9)
run_cmd show' `a3 200 `(by run_tac ackProof 3 12)

end Tests.Ved.U1StageCheck

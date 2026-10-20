import Tools.ShippingTopoLinked

/-! # `closeInsts` returns a module: the conditions, named

`closeInsts` unfolded into its four steps — the instance statements, the
output wires, the reordering, the checks — so that each can be established
separately. Pure; nothing here says the conditions hold. -/
namespace Tools.ShippingCloseInstsSome
open Sparkle.IR.AST Sparkle.IR.Machine

/-- The instance statements of the calls. -/
def instStmtsOf (nIn kI n : Nat) (portNames : List String) (insts : List (List Nat))
    (children : List (Module × Design)) (m : Module) (d : Design) : Option (List Stmt) :=
  (List.range insts.length).mapM fun k => do
    let args ← insts[k]?
    let child ← children[k]?
    let mc ← moduleByName (designWith children d).modules child.1.name
    instStmt nIn kI n portNames k args mc m

/-- The calls' output wires. -/
def outWsOf (nIn : Nat) (portNames : List String) (insts : List (List Nat)) : Option (List String) :=
  (List.range insts.length).mapM fun k => portNames[nIn + k]?

/-- The checks `closeInsts` runs on the reordered body `body` of
`body0 = m.body ++ stmts`. -/
def closeChecks (portNames : List String) (children : List (Module × Design)) (mname : String)
    (d' : Design) (stmts body0 body : List Stmt) : Bool :=
  stmts.all isInst && decide portNames.Nodup && Sparkle.IR.Reorder.woCheck [] body0 &&
    Sparkle.IR.Reorder.woCheck [] body && Sparkle.IR.Reorder.isPermOf body0 body &&
    decide (seqOf body0 = seqOf body) &&
    decide (Sparkle.IR.Reorder.nextKeys body0).Nodup &&
    decide (body0.filterMap Sparkle.IR.Reorder.stmtMemName).Nodup &&
    linkedOk (moduleByName d'.modules) body &&
    children.all (fun c => decide (moduleByName d'.modules c.1.name = some c.1) &&
      c.2.modules.all (fun g => decide (moduleByName d'.modules g.name = some g))) &&
    noInstOfB mname body && d'.modules.all (fun g => noInstOfB mname g.body) &&
    kidsCombB d'.modules body

/-- **`closeInsts` returns a module when its four steps succeed.** -/
theorem closeInsts_some_of {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : List (Module × Design)} {m : Module} {d : Design}
    {stmts : List Stmt} {outWs : List String} {body : List Stmt}
    (hst : instStmtsOf nIn kI n portNames insts children m d = some stmts)
    (hout : outWsOf nIn portNames insts = some outWs)
    (htopo : topoBody (m.body ++ stmts) = some body)
    (hchk : closeChecks portNames children m.name (designWith children d) stmts
      (m.body ++ stmts) body = true) :
    (closeInsts nIn kI n portNames insts children (m, d)).isSome = true := by
  unfold instStmtsOf at hst
  unfold outWsOf at hout
  unfold closeChecks at hchk
  simp only [Option.bind_eq_bind] at hst hout
  unfold closeInsts
  simp only [Option.bind_eq_bind, hst, hout, htopo, Option.bind_some, hchk, if_true]
  rfl

end Tools.ShippingCloseInstsSome

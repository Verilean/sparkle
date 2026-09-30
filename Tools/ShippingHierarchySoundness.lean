import Sparkle.IR.Semantics
import Sparkle.Core.Signal

/-! # S6-1: compositional instance semantics, combinational layer

The compiler lowers a call to an `@[hardware_module]` child into one
`.inst` statement: child input ports connected to parent wires, child
output ports connected to fresh parent wires. The shipped `runModule`
semantics treats instance outputs as free inputs (the open-module
view); this file gives instances their LINKED meaning — a child's
outputs are the standard evaluation of its own body on the
connection-fed environment — and proves the canonical single-instance
parent observes exactly the child's evaluation. Sequential children
and nested instances are later layers; the linked walk skips registers
and memories like the combinational phase does. -/

namespace Tools.ShippingHierarchySoundness

open Sparkle.IR.AST Sparkle.IR.Semantics

/-- Connection-fed child environment: each child port reads the parent
wire its connection references (non-reference connections read 0 —
the canonical lowering only emits references). -/
def connEnv (conns : List (String × Expr)) (env : Env) : Env := fun n =>
  match conns.lookup n with
  | some (.ref w) => env w
  | _ => 0

/-- Write a child's outputs back through its connections. -/
def bindOuts (outs : List Port) (conns : List (String × Expr))
    (cres : Env) (env : Env) : Env :=
  outs.foldl (fun acc p =>
    match conns.lookup p.name with
    | some (.ref w) => fun n => if n = w then cres p.name else acc n
    | _ => acc) env

/-- One-level linked elaboration: an instance of a (combinational)
child is evaluated by the standard semantics on the connection-fed
environment, and its outputs drive the connected parent wires. -/
def evalAssignsH (we : WEnv) (children : String → Option (Module × WEnv))
    (mems : MEnv) : List Stmt → Env → Option Env
  | [], env => some env
  | .assign l r :: rest, env => do
    let v ← evalExpr we env r
    evalAssignsH we children mems rest (fun n => if n = l then v else env n)
  | .inst mn _ conns :: rest, env => do
    let (child, cwe) ← children mn
    let cres ← evalAssigns cwe mems child.body (connEnv conns env)
    evalAssignsH we children mems rest (bindOuts child.outputs conns cres env)
  | .register .. :: rest, env => evalAssignsH we children mems rest env
  | .memory .. :: rest, env => evalAssignsH we children mems rest env

theorem lookup_append_right {α : Type} [BEq α] {l1 l2 : List (α × Expr)} {k : α}
    (h : ∀ p ∈ l1, (k == p.1) = false) :
    (l1 ++ l2).lookup k = l2.lookup k := by
  induction l1 with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨pk, pv⟩ := p
    show (match k == pk with
      | true => some pv
      | false => List.lookup k (rest ++ l2)) = _
    rw [h (pk, pv) List.mem_cons_self]
    exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- The canonical single-instance parent body: one instance whose
inputs read parent wires and whose single output drives `outW`, then
the output alias. -/
def instBody (mn instName : String) (inConns : List (String × Expr))
    (childOut outW : String) : List Stmt :=
  [ .inst mn instName (inConns ++ [(childOut, .ref outW)]),
    .assign "out" (.ref outW) ]

/-- The linked evaluation of the canonical parent, computed: the child
runs once on the connection-fed environment, and both the output wire
and `out` observe the child's output. -/
theorem instBody_linked {we : WEnv} {mems : MEnv}
    {children : String → Option (Module × WEnv)}
    {mn instName : String} {inConns : List (String × Expr)}
    {childOut outW : String} {child : Module} {cwe : WEnv} {cres : Env}
    {env0 : Env} {ty : Sparkle.IR.Type.HWType}
    (hchild : children mn = some (child, cwe))
    (houts : child.outputs = [{ name := childOut, ty := ty }])
    (hfresh : ∀ p ∈ inConns, (childOut == p.1) = false)
    (hrun : evalAssigns cwe mems child.body
      (connEnv (inConns ++ [(childOut, .ref outW)]) env0) = some cres)
    (hout_ne : outW ≠ "out") :
    ∃ envF, evalAssignsH we children mems
      (instBody mn instName inConns childOut outW) env0 = some envF ∧
      envF "out" = cres childOut ∧ envF outW = cres childOut := by
  have hlook : (inConns ++ [(childOut, Expr.ref outW)]).lookup childOut =
      some (.ref outW) := by
    rw [lookup_append_right hfresh]
    simp [List.lookup]
  have hbind : bindOuts child.outputs (inConns ++ [(childOut, .ref outW)]) cres env0 =
      fun n => if n = outW then cres childOut else env0 n := by
    rw [houts]
    show (match (inConns ++ [(childOut, Expr.ref outW)]).lookup childOut with
      | some (.ref w) => fun n => if n = w then cres childOut else env0 n
      | _ => env0) = _
    rw [hlook]
  refine ⟨fun n => if n = "out" then cres childOut
    else if n = outW then cres childOut else env0 n, ?_, by simp, by simp [hout_ne]⟩
  show (do
    let cp ← children mn
    let cr ← evalAssigns cp.2 mems cp.1.body
      (connEnv (inConns ++ [(childOut, Expr.ref outW)]) env0)
    evalAssignsH we children mems [.assign "out" (.ref outW)]
      (bindOuts cp.1.outputs (inConns ++ [(childOut, Expr.ref outW)]) cr env0)) = _
  rw [hchild]
  show (do
    let cr ← evalAssigns cwe mems child.body
      (connEnv (inConns ++ [(childOut, Expr.ref outW)]) env0)
    evalAssignsH we children mems [.assign "out" (.ref outW)]
      (bindOuts child.outputs (inConns ++ [(childOut, Expr.ref outW)]) cr env0)) = _
  rw [hrun]
  show evalAssignsH we children mems [.assign "out" (.ref outW)]
    (bindOuts child.outputs (inConns ++ [(childOut, Expr.ref outW)]) cres env0) = _
  rw [hbind]
  show (do
    let v ← evalExpr we (fun n => if n = outW then cres childOut else env0 n)
      (.ref outW)
    evalAssignsH we children mems []
      ((fun n => if n = "out" then v
        else (fun n => if n = outW then cres childOut else env0 n) n))) = _
  show some ((fun n => if n = "out" then
      (if outW = outW then cres childOut else env0 outW)
    else (fun n => if n = outW then cres childOut else env0 n) n)) = _
  simp

/-- Connection-fed inputs read exactly the connected parent wires. -/
theorem connEnv_at {conns : List (String × Expr)} {env : Env}
    {k : String} {w : String}
    (h : conns.lookup k = some (.ref w)) : connEnv conns env k = env w := by
  simp [connEnv, h]

end Tools.ShippingHierarchySoundness

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

/-- The linked evaluation of a one-instance parent with ANY connection list
(multi-output children included): the child runs once on the connection-fed
environment, its outputs are written back through the connections, and `out`
observes whatever the aliased wire holds afterwards. -/
theorem instAlias_linked {we : WEnv} {mems : MEnv}
    {children : String → Option (Module × WEnv)}
    {mn instName : String} {conns : List (String × Expr)}
    {outW : String} {child : Module} {cwe : WEnv} {cres : Env} {env0 : Env}
    (hchild : children mn = some (child, cwe))
    (hrun : evalAssigns cwe mems child.body (connEnv conns env0) = some cres) :
    ∃ envF, evalAssignsH we children mems
      [.inst mn instName conns, .assign "out" (.ref outW)] env0 = some envF ∧
      envF "out" = bindOuts child.outputs conns cres env0 outW := by
  refine ⟨fun n => if n = "out" then bindOuts child.outputs conns cres env0 outW
    else bindOuts child.outputs conns cres env0 n, ?_, by simp⟩
  show (do
    let cp ← children mn
    let cr ← evalAssigns cp.2 mems cp.1.body (connEnv conns env0)
    evalAssignsH we children mems [.assign "out" (.ref outW)]
      (bindOuts cp.1.outputs conns cr env0)) = _
  rw [hchild]
  show (do
    let cr ← evalAssigns cwe mems child.body (connEnv conns env0)
    evalAssignsH we children mems [.assign "out" (.ref outW)]
      (bindOuts child.outputs conns cr env0)) = _
  rw [hrun]
  rfl

/-- Connection-fed inputs read exactly the connected parent wires. -/
theorem connEnv_at {conns : List (String × Expr)} {env : Env}
    {k : String} {w : String}
    (h : conns.lookup k = some (.ref w)) : connEnv conns env k = env w := by
  simp [connEnv, h]

/-! ## The stateful linked layer: sequential children advance per cycle -/

/-- Connection-fed child environment with the child's own register state
underneath: connected ports read the parent, everything else (the child's
registers and internal wires) reads the child's state. -/
def connEnvS (conns : List (String × Expr)) (env : Env)
    (cst : String → Nat) : Env := fun n =>
  match conns.lookup n with
  | some (.ref w) => env w
  | _ => cst n

/-- One linked CYCLE: like `evalAssignsH`, but an instance advances the
child by one `stepModule` cycle on the connection-fed, state-backed
environment, threading the child's register state and memories. -/
def stepAssignsH (we : WEnv) (children : String → Option (Module × WEnv)) :
    List Stmt → Env → (String → Nat) → MEnv →
    Option (Env × (String → Nat) × MEnv)
  | [], env, cst, mems => some (env, cst, mems)
  | .assign l r :: rest, env, cst, mems => do
    let v ← evalExpr we env r
    stepAssignsH we children rest (fun n => if n = l then v else env n) cst mems
  | .inst mn _ conns :: rest, env, cst, mems => do
    let (child, cwe) ← children mn
    let (cres, nexts, mems') ← stepModule cwe child.body (connEnvS conns env cst) mems
    stepAssignsH we children rest (bindOuts child.outputs conns cres env)
      (applyNexts cst nexts) mems'
  | .register .. :: rest, env, cst, mems => stepAssignsH we children rest env cst mems
  | .memory .. :: rest, env, cst, mems => stepAssignsH we children rest env cst mems

/-- The linked k-cycle run of a parent body: per cycle, the parent inputs
come from `seedP`, the child's registers persist in `cst`. The per-cycle
post-elaboration parent environments are the observable trace (oldest
first, with `seedP`'s index counting down like `runModule`'s). -/
def runH (we : WEnv) (children : String → Option (Module × WEnv))
    (body : List Stmt) (seedP : Nat → Env) :
    Nat → (String → Nat) → MEnv → Option (List Env)
  | 0, _, _ => some []
  | k + 1, cst, mems => do
    let (envF, cst', mems') ← stepAssignsH we children body (seedP k) cst mems
    let rest ← runH we children body seedP k cst' mems'
    some (envF :: rest)

/-- One linked cycle of the canonical parent, computed from one child
step: `out` and the output wire both observe the child's output, and the
child's state advances by its own register updates. -/
theorem instBody_stepH {we : WEnv} {mems mems' : MEnv}
    {children : String → Option (Module × WEnv)}
    {mn instName : String} {inConns : List (String × Expr)}
    {childOut outW : String} {child : Module} {cwe : WEnv}
    {cres : Env} {nexts : List (String × Nat)}
    {env0 : Env} {cst : String → Nat} {ty : Sparkle.IR.Type.HWType}
    (hchild : children mn = some (child, cwe))
    (houts : child.outputs = [{ name := childOut, ty := ty }])
    (hfresh : ∀ p ∈ inConns, (childOut == p.1) = false)
    (hstep : stepModule cwe child.body
      (connEnvS (inConns ++ [(childOut, .ref outW)]) env0 cst) mems =
      some (cres, nexts, mems'))
    (hout_ne : outW ≠ "out") :
    ∃ envF, stepAssignsH we children
      (instBody mn instName inConns childOut outW) env0 cst mems =
      some (envF, applyNexts cst nexts, mems') ∧
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
    let (cres', nexts', mems'') ← stepModule cp.2 cp.1.body
      (connEnvS (inConns ++ [(childOut, Expr.ref outW)]) env0 cst) mems
    stepAssignsH we children [.assign "out" (.ref outW)]
      (bindOuts cp.1.outputs (inConns ++ [(childOut, Expr.ref outW)]) cres' env0)
      (applyNexts cst nexts') mems'') = _
  rw [hchild]
  show (do
    let (cres', nexts', mems'') ← stepModule cwe child.body
      (connEnvS (inConns ++ [(childOut, Expr.ref outW)]) env0 cst) mems
    stepAssignsH we children [.assign "out" (.ref outW)]
      (bindOuts child.outputs (inConns ++ [(childOut, Expr.ref outW)]) cres' env0)
      (applyNexts cst nexts') mems'') = _
  rw [hstep]
  show stepAssignsH we children [.assign "out" (.ref outW)]
    (bindOuts child.outputs (inConns ++ [(childOut, Expr.ref outW)]) cres env0)
    (applyNexts cst nexts) mems' = _
  rw [hbind]
  show (do
    let v ← evalExpr we (fun n => if n = outW then cres childOut else env0 n)
      (.ref outW)
    stepAssignsH we children []
      ((fun n => if n = "out" then v
        else (fun n => if n = outW then cres childOut else env0 n) n))
      (applyNexts cst nexts) mems') = _
  show some ((fun n => if n = "out" then
      (if outW = outW then cres childOut else env0 outW)
    else (fun n => if n = outW then cres childOut else env0 n) n),
    applyNexts cst nexts, mems') = _
  simp

/-- The linked k-cycle run of the canonical parent forwards the child's
`runModule` trace: whenever the child runs for `k` cycles on the
connection-fed, state-backed seeds, the parent's linked run exists and
its `out` observes the child's output at every cycle. -/
theorem instBody_runH {we : WEnv}
    {children : String → Option (Module × WEnv)}
    {mn instName : String} {inConns : List (String × Expr)}
    {childOut outW : String} {child : Module} {cwe : WEnv}
    {seedP : Nat → Env} {ty : Sparkle.IR.Type.HWType}
    (hchild : children mn = some (child, cwe))
    (houts : child.outputs = [{ name := childOut, ty := ty }])
    (hfresh : ∀ p ∈ inConns, (childOut == p.1) = false)
    (hout_ne : outW ≠ "out") :
    ∀ (k : Nat) (cst : String → Nat) (mems : MEnv) (envsC : List Env),
    runModule cwe child.body
      (fun t cst' => connEnvS (inConns ++ [(childOut, .ref outW)]) (seedP t) cst')
      k cst mems = some envsC →
    ∃ envsP, runH we children (instBody mn instName inConns childOut outW)
        seedP k cst mems = some envsP ∧
      envsP.length = envsC.length ∧
      ∀ j (hj : j < envsP.length) (hj' : j < envsC.length),
        (envsP[j]'hj) "out" = (envsC[j]'hj') childOut := by
  intro k
  induction k with
  | zero =>
    intro cst mems envsC hrun
    cases hrun
    exact ⟨[], rfl, rfl, fun j hj _ => absurd hj (by simp)⟩
  | succ k ih =>
    intro cst mems envsC hrun
    unfold runModule at hrun
    obtain ⟨⟨cres, nexts, mems'⟩, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hrun
    obtain ⟨rest, hrestRun, hcons⟩ := Option.bind_eq_some_iff.mp hrest
    cases hcons
    obtain ⟨envF, hstepH, hout, -⟩ := instBody_stepH (we := we)
      (instName := instName) hchild houts hfresh hstep hout_ne
    obtain ⟨envsP, hrunP, hlen, hobs⟩ := ih (applyNexts cst nexts) mems' rest hrestRun
    refine ⟨envF :: envsP, ?_, by simpa using hlen, ?_⟩
    · unfold runH
      rw [hstepH]
      show (do
        let restP ← runH we children (instBody mn instName inConns childOut outW)
          seedP k (applyNexts cst nexts) mems'
        some (envF :: restP)) = _
      rw [hrunP]
      rfl
    · intro j hj hj'
      cases j with
      | zero => exact hout
      | succ j => exact hobs j (by simpa using hj) (by simpa using hj')

end Tools.ShippingHierarchySoundness

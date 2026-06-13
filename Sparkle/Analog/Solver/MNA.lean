import Sparkle.Analog.IR.Netlist
import Sparkle.Analog.Num
import Sparkle.Analog.Symbolic.Diff
import Sparkle.Analog.Solver.LinAlg

/-!
# Modified Nodal Analysis

Turns a `Circuit` into a square algebraic system and solves it by Newton's
method. The unknowns are the non-ground net potentials and every branch current
(full MNA: each device keeps its own current unknown, so voltage sources and
inductors are handled uniformly — that is the "modified" part).

For a circuit with `netCount` nets (net 0 = ground) and `B` branches the system
has `N = (netCount − 1) + B` unknowns and `N` equations:

* one acausal device law per branch (with `v := V(pos) − V(neg)`, `i := I(b)`),
  Backward-Euler–discretized so `ddt` becomes algebraic; and
* Kirchhoff's current law at each non-ground net.

The residual is evaluated and the Jacobian is taken by dual-number AD
(`AExpr.derivWrt`). A linear circuit converges in a single Newton step from any
start; a nonlinear one iterates.
-/

namespace Sparkle.Analog

/-- Number of MNA unknowns: non-ground potentials plus branch currents. -/
def Circuit.dim (c : Circuit) : Nat := (c.netCount - 1) + c.branchCount

/-- Column index → unknown. Non-ground net potentials come first (net `k` at
column `k-1`), then branch currents. -/
def Circuit.columns (c : Circuit) : Array Unknown := Id.run do
  let mut cols := #[]
  for net in [1:c.netCount] do
    cols := cols.push (.netPotential net)
  for b in [0:c.branchCount] do
    cols := cols.push (.branchFlow b)
  return cols

/-- Operating-point lookup from a solution vector: ground is pinned to zero, the
rest read out at the matching column. -/
def Circuit.envOf (c : Circuit) (x : Array Float) : Unknown → Float := fun u =>
  match u with
  | .netPotential 0 => 0.0
  | .netPotential net => x[net - 1]!
  | .branchFlow b => x[(c.netCount - 1) + b]!

/-- All equations of the system, *undiscretized*: each branch's acausal law (with
`v := V(pos) − V(neg)`, `i := I(b)`, `ddt` left intact), then the controlled-source
constraint rows, then KCL at each non-ground net. The differential operators
survive here; the transient path lowers them with Backward Euler (`equations`),
while AC analysis interprets them as `jω`. Row order — device-law rows in branch
order, then controlled-source constraints, then KCL — is the shared contract both
paths rely on. -/
def Circuit.equationsRaw (c : Circuit) : Array Equation :=
  let vNode (p n : Nat) : AExpr := AExpr.netV p - AExpr.netV n
  -- Pair each controlled source with its output-branch index (from
  -- `placements.length` up) where it carries one; `none` for the current-output
  -- kinds. A prefix scan: the running counter is the only sequential state.
  let ctrlInfo : Array (CtrlSource × Option Nat) :=
    (c.controlledSources.foldl
      (fun (acc, nb) cs =>
        if cs.needsBranch then (acc.push (cs, some nb), nb + 1)
        else (acc.push (cs, none), nb))
      ((#[] : Array (CtrlSource × Option Nat)), c.placements.length)).1
  -- Device-law rows (one per two-terminal device, branch order).
  let deviceRows : Array Equation :=
    (Array.range c.placements.length).flatMap fun b =>
      let p := c.placements[b]!
      (p.law (vNode p.pos p.neg) (AExpr.branchI b)).toArray
  -- Controlled-source constraint rows (one per output-branch unknown).
  let ctrlRows : Array Equation :=
    ctrlInfo.filterMap fun (cs, _) =>
      match cs.kind with
      | .vcvs => some (vNode cs.outP cs.outN ≡ cs.gain * vNode cs.inP cs.inN)
      | .ccvs => some (vNode cs.outP cs.outN ≡ cs.gain * AExpr.branchI (cs.ctrlBranch.getD 0))
      | .opamp => some (vNode cs.inP cs.inN ≡ (0 : AExpr))
      | _ => none  -- vccs/cccs have no constraint row
  -- The signed contribution of one controlled source to the KCL sum at `net`.
  let ctrlKCL (net : Nat) (sum : AExpr) : (CtrlSource × Option Nat) → AExpr :=
    fun (cs, mb) =>
      let outCurrent : AExpr := match cs.kind, mb with
        | .vccs, _ => cs.gain * vNode cs.inP cs.inN
        | .cccs, _ => cs.gain * AExpr.branchI (cs.ctrlBranch.getD 0)
        | _, some j => AExpr.branchI j          -- vcvs/ccvs/opamp output branch
        | _, none => (0 : AExpr)
      let sum := if cs.outP == net then sum + outCurrent else sum
      if cs.outN == net then sum - outCurrent else sum
  -- KCL at each non-ground net `k+1`: two-terminal branch currents plus
  -- controlled-source contributions, summed over the respective lists.
  let kclRows : Array Equation :=
    (Array.range (c.netCount - 1)).map fun k =>
      let net := k + 1
      let deviceSum := (Array.range c.placements.length).foldl
        (fun sum b =>
          let p := c.placements[b]!
          let sum := if p.pos == net then sum + AExpr.branchI b else sum
          if p.neg == net then sum - AExpr.branchI b else sum)
        (0 : AExpr)
      (ctrlInfo.foldl (ctrlKCL net) deviceSum) ≡ (0 : AExpr)
  deviceRows ++ ctrlRows ++ kclRows

/-- All equations of the discretized system at a timestep: `equationsRaw` with
every branch law Backward-Euler–discretized against the previous point (KCL and
controlled-source rows, having no `ddt`, pass through unchanged). -/
def Circuit.equations (c : Circuit) (dt tPrev : Float) (prev : Unknown → Float) :
    Array Equation :=
  c.equationsRaw.map (·.discretizeBE dt tPrev prev)

/-- Solve one (possibly nonlinear) timestep by Newton's method. `tNow` is the
current time (the value of `time` nodes); `prev`/`tPrev` are the previous point
the differential terms were discretized against; `x0` seeds the iteration.
Returns the solution vector, or `none` if the Jacobian is singular. -/
def Circuit.newtonStep (c : Circuit) (dt tPrev tNow : Float) (prev : Unknown → Float)
    (x0 : Array Float) (maxIter : Nat := 50) (tol : Float := 1e-10) :
    Option (Array Float) := Id.run do
  let eqs := c.equations dt tPrev prev
  let cols := c.columns
  let n := cols.size
  let mut x := x0
  for _ in [0:maxIter] do
    let env := c.envOf x
    let mut f := Array.replicate n 0.0
    let mut jac := Array.replicate n (Array.replicate n 0.0)
    for r in [0:n] do
      let res := eqs[r]!.residual
      f := f.set! r (res.evalFloat env tNow)
      let mut row := jac[r]!
      for col in [0:n] do
        row := row.set! col (res.derivWrt cols[col]! env tNow)
      jac := jac.set! r row
    let mut nf := 0.0
    for r in [0:n] do
      let af := Float.abs f[r]!
      if af > nf then nf := af
    if nf < tol then
      return some x
    match linSolve jac (f.map (fun z => -z)) with
    | none => return none
    | some d =>
      let mut x' := x
      for idx in [0:n] do
        x' := x'.set! idx (x[idx]! + d[idx]!)
      x := x'
  return some x

/-- DC operating point: solve with no time dependence (sources at `time = 0`,
no previous point). -/
def Circuit.solveDC (c : Circuit) : Option (Array Float) :=
  c.newtonStep 1.0 0.0 0.0 (fun _ => 0.0) (Array.replicate c.dim 0.0)

end Sparkle.Analog

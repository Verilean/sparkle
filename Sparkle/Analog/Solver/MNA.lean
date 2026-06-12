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

/-- All equations of the discretized system at a timestep: each branch's law
(with `ddt` discretized against the previous point) followed by KCL at each
non-ground net. -/
def Circuit.equations (c : Circuit) (dt tPrev : Float) (prev : Unknown → Float) :
    Array Equation := Id.run do
  let mut eqs := #[]
  for b in [0:c.placements.length] do
    let p := c.placements[b]!
    let v := AExpr.sub (AExpr.netV p.pos) (AExpr.netV p.neg)
    let i := AExpr.branchI b
    for eq in p.law v i do
      eqs := eqs.push (eq.discretizeBE dt tPrev prev)
  for net in [1:c.netCount] do
    let mut sum : AExpr := (0 : AExpr)
    for b in [0:c.placements.length] do
      let p := c.placements[b]!
      if p.pos == net then sum := sum + AExpr.branchI b
      if p.neg == net then sum := sum - AExpr.branchI b
    eqs := eqs.push (sum ≡ (0 : AExpr))
  return eqs

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

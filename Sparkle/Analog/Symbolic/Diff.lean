import Sparkle.Analog.IR.Expr
import Sparkle.Analog.Num

/-!
# Symbolic differentiation and time discretization

Two source-to-source passes the solver needs:

* `AExpr.deriv u` — symbolic partial derivative with respect to an unknown,
  producing the Jacobian entries the Newton solver stamps. This is the symbolic
  counterpart to the dual-number route (`AExpr.derivWrt`); having both lets each
  cross-check the other.
* `AExpr.discretizeBE` — Backward-Euler rewrite of the differential operators
  into algebraic companion terms, so a transient timestep becomes an ordinary
  (possibly nonlinear) algebraic system. A capacitor's `i = C·ddt v` becomes
  `i = C·(v − vₚᵣₑᵥ)/dt`; an inductor's `v = L·ddt i` likewise.

Differentiation expects an algebraic expression: discretize first, then
differentiate the residual.
-/

namespace Sparkle.Analog

/-- Symbolic partial derivative `∂e/∂u`. Standard rules; `ddt` differentiates to
zero because it is expected to have been discretized away first. -/
def AExpr.deriv (u : Unknown) : AExpr → AExpr
  | .lit _ => 0
  | .time => 0
  | .unknown v => if v = u then 1 else 0
  | .add a b => a.deriv u + b.deriv u
  | .sub a b => a.deriv u - b.deriv u
  | .mul a b => a.deriv u * b + a * b.deriv u
  | .div a b => (a.deriv u * b - a * b.deriv u) / (b * b)
  | .neg a => -(a.deriv u)
  | .exp a => exp a * a.deriv u
  | .log a => a.deriv u / a
  | .sin a => cos a * a.deriv u
  | .cos a => -(sin a) * a.deriv u
  | .ddt _ => 0

/-- Backward-Euler discretization at step size `dt`, given the previous solution
point (`prev` for unknowns, `tPrev` for time). `ddt a` becomes `(a − aₚᵣₑᵥ)/dt`,
where `aₚᵣₑᵥ` is `a` evaluated at the previous step (a constant). -/
def AExpr.discretizeBE (dt tPrev : Float) (prev : Unknown → Float) : AExpr → AExpr
  | .ddt a =>
    let aCur := a.discretizeBE dt tPrev prev
    let aPrev : Float := a.evalFloat prev tPrev
    (aCur - aPrev) / dt
  | .lit c => .lit c
  | .unknown u => .unknown u
  | .time => .time
  | .add a b => .add (a.discretizeBE dt tPrev prev) (b.discretizeBE dt tPrev prev)
  | .sub a b => .sub (a.discretizeBE dt tPrev prev) (b.discretizeBE dt tPrev prev)
  | .mul a b => .mul (a.discretizeBE dt tPrev prev) (b.discretizeBE dt tPrev prev)
  | .div a b => .div (a.discretizeBE dt tPrev prev) (b.discretizeBE dt tPrev prev)
  | .neg a => .neg (a.discretizeBE dt tPrev prev)
  | .exp a => .exp (a.discretizeBE dt tPrev prev)
  | .log a => .log (a.discretizeBE dt tPrev prev)
  | .sin a => .sin (a.discretizeBE dt tPrev prev)
  | .cos a => .cos (a.discretizeBE dt tPrev prev)

/-- The residual `lhs − rhs`, differentiated with respect to `u`: a Jacobian
entry for this equation. -/
def Equation.residualDeriv (u : Unknown) (eq : Equation) : AExpr :=
  eq.residual.deriv u

/-- Discretize both sides of an equation. -/
def Equation.discretizeBE (dt tPrev : Float) (prev : Unknown → Float) (eq : Equation) : Equation :=
  ⟨eq.lhs.discretizeBE dt tPrev prev, eq.rhs.discretizeBE dt tPrev prev⟩

end Sparkle.Analog

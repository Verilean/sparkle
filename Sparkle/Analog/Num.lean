import Sparkle.Analog.IR.Expr

/-!
# The `Analog` numeric carrier

`Analog α` is the interface an `AExpr` is interpreted into. One interpreter
(`AExpr.eval`) therefore yields several semantics depending on the carrier:

* `Float` — direct numeric evaluation for simulation.
* `Dual`  — forward-mode automatic differentiation, giving exact Jacobian
  entries for the Newton solver with no finite-difference error.

It is deliberately Mathlib-free (this is a small, fixed set of scalar ops, not a
`Field`) so the simulator keeps the project's light dependency footprint and the
WASM build intact. A `Real` instance for the verification layer is added later,
behind its own library.
-/

namespace Sparkle.Analog

/-- π, computed from `acos` rather than written as a digit literal, so the
constant has a single source of truth across the solver (AC frequencies, phase
conversion, pole placement). -/
def pi : Float := Float.acos (-1.0)

/-- Scalar operations an analog expression can be evaluated into. -/
class Analog (α : Type) where
  ofFloat : Float → α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  neg : α → α
  exp : α → α
  log : α → α
  sin : α → α
  cos : α → α

instance : Analog Float where
  ofFloat := id
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  neg := (- ·)
  exp := Float.exp
  log := Float.log
  sin := Float.sin
  cos := Float.cos

/-- Forward-mode dual number `val + eps·ε`, where `eps` carries the derivative
with respect to a single seeded variable. -/
structure Dual where
  val : Float
  eps : Float
  deriving Repr, Inhabited

namespace Dual

/-- A constant: derivative zero. -/
def const (x : Float) : Dual := ⟨x, 0.0⟩

/-- The variable being differentiated against: derivative one. -/
def var (x : Float) : Dual := ⟨x, 1.0⟩

instance : Analog Dual where
  ofFloat := const
  add a b := ⟨a.val + b.val, a.eps + b.eps⟩
  sub a b := ⟨a.val - b.val, a.eps - b.eps⟩
  mul a b := ⟨a.val * b.val, a.eps * b.val + a.val * b.eps⟩
  div a b := ⟨a.val / b.val, (a.eps * b.val - a.val * b.eps) / (b.val * b.val)⟩
  neg a := ⟨-a.val, -a.eps⟩
  exp a := let e := Float.exp a.val; ⟨e, a.eps * e⟩
  log a := ⟨Float.log a.val, a.eps / a.val⟩
  sin a := ⟨Float.sin a.val, a.eps * Float.cos a.val⟩
  cos a := ⟨Float.cos a.val, -a.eps * Float.sin a.val⟩

end Dual

/-- Interpret an expression into an `Analog` carrier, given a value for each
unknown, for `time`, and a handler `onDdt` for the differential operator.

`ddt` is not a pointwise scalar function, so its meaning depends on the analysis:
the transient engine lowers it to companion terms (`onDdt _ = 0` after
discretization), while AC small-signal analysis maps `ddt a ↦ jω·a`. Factoring it
into a handler lets one evaluator serve both — see `AExpr.eval` and `evalAC`. -/
def AExpr.evalWith [Analog α] (env : Unknown → α) (t : α) (onDdt : AExpr → α) : AExpr → α
  | .lit c => Analog.ofFloat c
  | .unknown u => env u
  | .time => t
  | .add a b => Analog.add (a.evalWith env t onDdt) (b.evalWith env t onDdt)
  | .sub a b => Analog.sub (a.evalWith env t onDdt) (b.evalWith env t onDdt)
  | .mul a b => Analog.mul (a.evalWith env t onDdt) (b.evalWith env t onDdt)
  | .div a b => Analog.div (a.evalWith env t onDdt) (b.evalWith env t onDdt)
  | .neg a => Analog.neg (a.evalWith env t onDdt)
  | .exp a => Analog.exp (a.evalWith env t onDdt)
  | .log a => Analog.log (a.evalWith env t onDdt)
  | .sin a => Analog.sin (a.evalWith env t onDdt)
  | .cos a => Analog.cos (a.evalWith env t onDdt)
  | .ddt a => onDdt a

/-- Interpret an expression into an `Analog` carrier, given a value for each
unknown and for `time`.

Precondition: `e` is algebraic (`AExpr.isAlgebraic`). `ddt` is not
pointwise-evaluable; the transient engine lowers it to algebraic companion terms
first. A raw differential node here evaluates to `0` rather than failing, so
callers should lower before evaluating. -/
def AExpr.eval [Analog α] (env : Unknown → α) (t : α) (e : AExpr) : α :=
  e.evalWith env t (fun _ => Analog.ofFloat 0.0)

/-- Numeric value of an algebraic expression at an operating point. -/
def AExpr.evalFloat (env : Unknown → Float) (t : Float) (e : AExpr) : Float :=
  e.eval env t

/-- Exact partial derivative `∂e/∂u` at an operating point, via dual numbers:
seed `u` with derivative one and every other unknown with derivative zero. This
is the AD route to a Jacobian entry, cross-checking the symbolic differentiator. -/
def AExpr.derivWrt (u : Unknown) (point : Unknown → Float) (t : Float) (e : AExpr) : Float :=
  let env : Unknown → Dual := fun v =>
    if v = u then Dual.var (point v) else Dual.const (point v)
  (e.eval env (Dual.const t)).eps

end Sparkle.Analog

-- Brings the Heron linter into the analog subsystem's import closure so every
-- module built on top of `Sparkle.Analog.IR.Expr` is linted (enabled repo-wide
-- via the `weak.linter.heron` option in the lakefile). Imported once at the root.
import Heron

/-!
# Analog expression IR

The real-valued expression tree that analog device laws are built from, plus the
`Equation` value that pairs two expressions into an acausal relation.

This is the spine of the analog subsystem: device models reduce to `Equation`s
over `AExpr`, the solver stamps from it, the symbolic-differentiation pass walks
it, and (later) the verification layer reasons about it. It is deliberately
independent of `Sparkle.IR` — there are no bit widths here, only continuous reals.

Authoring ergonomics come from the arithmetic instances below: a device law such
as `i ≡ Is * (exp (v / Vt) - 1)` is ordinary Lean, where `*`, `/`, `-` and the
`exp` wrapper build `AExpr` nodes and `Float` parameters coerce in.
-/

namespace Sparkle.Analog

/-- An unknown in the analog system: either the potential of a net (a node
voltage) or the flow through a branch (a branch current). Modified Nodal Analysis
solves for exactly these two kinds of unknown. Nets and branches are identified
by `Nat` handles assigned during circuit elaboration. -/
inductive Unknown where
  | netPotential (net : Nat)
  | branchFlow (branch : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Real-valued analog expression.

Exhaustive by design: the algebraic and transcendental fragment is what device
laws need, and the differential operator `ddt` is a first-class node because it
cannot be expressed as a pointwise scalar function — the transient engine rewrites
it into companion-model terms before numeric evaluation. -/
inductive AExpr where
  | lit (value : Float)
  | unknown (u : Unknown)
  /-- Absolute simulation time (`$abstime` in Verilog-A); lets sources be `time`-dependent. -/
  | time
  | add (a b : AExpr)
  | sub (a b : AExpr)
  | mul (a b : AExpr)
  | div (a b : AExpr)
  | neg (a : AExpr)
  | exp (a : AExpr)
  | log (a : AExpr)
  | sin (a : AExpr)
  | cos (a : AExpr)
  | ddt (a : AExpr)
  deriving Repr, BEq, Inhabited

namespace AExpr

/-- A net potential, by handle. -/
def netV (net : Nat) : AExpr := .unknown (.netPotential net)

/-- A branch flow, by handle. -/
def branchI (branch : Nat) : AExpr := .unknown (.branchFlow branch)

instance : Coe Float AExpr := ⟨AExpr.lit⟩
instance : OfNat AExpr n := ⟨AExpr.lit (OfNat.ofNat n)⟩

instance : Add AExpr := ⟨AExpr.add⟩
instance : Sub AExpr := ⟨AExpr.sub⟩
instance : Mul AExpr := ⟨AExpr.mul⟩
instance : Div AExpr := ⟨AExpr.div⟩
instance : Neg AExpr := ⟨AExpr.neg⟩

/-- Mixing `Float` parameters with `AExpr` is the common case in device laws
(`R * i`, `v / Vt`, `Is * …`), so the heterogeneous operators coerce the `Float`
side to a literal node. -/
instance : HMul Float AExpr AExpr := ⟨fun r e => .mul (.lit r) e⟩
instance : HMul AExpr Float AExpr := ⟨fun e r => .mul e (.lit r)⟩
instance : HDiv AExpr Float AExpr := ⟨fun e r => .div e (.lit r)⟩
instance : HDiv Float AExpr AExpr := ⟨fun r e => .div (.lit r) e⟩
instance : HAdd Float AExpr AExpr := ⟨fun r e => .add (.lit r) e⟩
instance : HAdd AExpr Float AExpr := ⟨fun e r => .add e (.lit r)⟩
instance : HSub Float AExpr AExpr := ⟨fun r e => .sub (.lit r) e⟩
instance : HSub AExpr Float AExpr := ⟨fun e r => .sub e (.lit r)⟩

/-- `true` if the expression contains no `ddt`; such expressions are the ones the
numeric evaluator can handle directly (the transient pass lowers the others
first). -/
def isAlgebraic : AExpr → Bool
  | ddt _ => false
  | add a b | sub a b | mul a b | div a b => a.isAlgebraic && b.isAlgebraic
  | neg a | exp a | log a | sin a | cos a => a.isAlgebraic
  | lit _ | unknown _ | time => true

end AExpr

/-- The transcendental wrappers are exposed at the namespace level so device laws
read as `exp (v / Vt)` once `Sparkle.Analog` is open. -/
def exp (a : AExpr) : AExpr := .exp a
def log (a : AExpr) : AExpr := .log a
def sin (a : AExpr) : AExpr := .sin a
def cos (a : AExpr) : AExpr := .cos a

/-- An acausal device law: `lhs` and `rhs` are asserted equal. This is a *value*
(`Equation`), deliberately distinct from the propositional `=`, so equations are
ordinary data the solver and differentiator manipulate. Build them with `≡`. -/
structure Equation where
  lhs : AExpr
  rhs : AExpr
  deriving Repr, Inhabited

/-- `v ≡ R * i` builds the `Equation` relating branch voltage and current. Binds
looser than arithmetic so the operands parse as whole expressions. -/
scoped infix:50 " ≡ " => Equation.mk

/-- Normal form `lhs - rhs = 0`, the residual the Newton solver drives to zero. -/
def Equation.residual (eq : Equation) : AExpr := .sub eq.lhs eq.rhs

end Sparkle.Analog

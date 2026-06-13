import Sparkle.Analog.Solver.MNA
import Sparkle.Analog.Complex

/-!
# AC small-signal analysis

Linearizes the circuit about its DC operating point and solves the complex
admittance system `Y(ω)·X = B` at each frequency, giving node-voltage phasors.

The whole analysis reuses the existing MNA machinery. `Y(ω)` is the Jacobian of
the *undiscretized* residuals (`equationsRaw`) at the DC bias, evaluated over the
`Complex` carrier with the differential operator interpreted as `ddt a ↦ jω·a`
(`evalAC`). Because differentiation drops constants, every independent DC source
falls out of `Y` — i.e. it becomes an AC ground, exactly as small-signal analysis
requires. The right-hand side `B` carries only the independent AC sources'
amplitudes (`Placement.acAmp`). One complex linear solve per frequency, no Newton
iteration (the system is already linear once linearized).
-/

namespace Sparkle.Analog

/-- Evaluate an expression into an `Analog` carrier with the differential operator
read as multiplication by `jw`: `ddt a ↦ jw · a`. This is the AC counterpart to
the transient lowering — instead of a Backward-Euler companion term, a reactive
element contributes its `jωC` / `1/(jωL)` admittance. -/
partial def AExpr.evalAC [Analog α] [Inhabited α] (env : Unknown → α) (jw : α) (e : AExpr) : α :=
  e.evalWith env (Analog.ofFloat 0.0) (fun a => Analog.mul jw (a.evalAC env jw))

/-- The complex small-signal admittance `∂(residual)/∂u` at the DC bias, with
`ddt ↦ jω`. Forward-mode AD over the dual-complex carrier: seed `u` with
derivative one, read the derivative off `.eps`. -/
def AExpr.derivWrtAC (u : Unknown) (bias : Unknown → Complex) (jw : Complex) (e : AExpr) :
    Complex :=
  let env : Unknown → DualC := fun v =>
    if v = u then DualC.var (bias v) else DualC.const (bias v)
  (e.evalAC env (DualC.const jw)).eps

/-- Assemble the AC system `(Y, B)` at angular frequency `ω`, linearized at the DC
`bias`. `Y[r][c] = ∂(residualᵣ)/∂(unknown_c)` with `ddt ↦ jω`; `B` holds the AC
source amplitudes at their device-law rows (row index = branch index, since each
device contributes exactly one law equation, emitted in branch order). -/
def Circuit.acStamp (c : Circuit) (bias : Unknown → Complex) (omega : Float) :
    Array (Array Complex) × Array Complex :=
  let cols := c.columns
  let jw : Complex := ⟨0.0, omega⟩
  -- Y row r, column u: ∂(residualᵣ)/∂u at the bias with ddt→jω.
  let y : Array (Array Complex) :=
    c.equationsRaw.map fun eq => cols.map fun u => eq.residual.derivWrtAC u bias jw
  -- B: the AC source amplitude at each device-law row (one row per branch, in
  -- order), zero on the controlled-source and KCL rows.
  let b : Array Complex :=
    (Array.range cols.size).map fun r =>
      match (c.placements[r]?).bind (·.acAmp) with
      | some amp => ⟨amp, 0.0⟩
      | none => Complex.ofFloat 0.0
  (y, b)

/-- AC sweep: node-voltage phasors at each frequency in `freqs` (in hertz). The
DC operating point is solved once to set the linearization bias (it only affects
nonlinear devices; a linear circuit's small-signal stamps are bias-independent).
Returns `none` if any frequency's system is singular. -/
def Circuit.solveAC (c : Circuit) (freqs : Array Float) :
    Option (Array (Float × Array Complex)) :=
  let bias : Unknown → Complex :=
    match c.solveDC with
    | some x => fun u => Complex.ofFloat ((c.envOf x) u)
    | none => fun _ => Complex.ofFloat 0.0
  -- `mapM` in the `Option` monad short-circuits to `none` on the first singular
  -- frequency; otherwise collects every phasor solution.
  freqs.mapM fun f =>
    let (y, b) := c.acStamp bias (2.0 * pi * f)
    (linSolveComplex y b).map (f, ·)

/-! ## Reporting -/

/-- The phasor at net `net` in an AC solution row (ground is `0`). Net potentials
occupy the leading columns, so net `k` is at index `k − 1`. -/
def acNet (net : Nat) (x : Array Complex) : Complex :=
  if net == 0 then Complex.ofFloat 0.0 else x[net - 1]!

/-- Magnitude in decibels: `20·log₁₀ |z|`. -/
def magDb (z : Complex) : Float := 20.0 * (Float.log z.magnitude / Float.log 10.0)

/-- Phase in degrees. -/
def phaseDeg (z : Complex) : Float := z.phase * 180.0 / pi

/-- The −3 dB bandwidth at net `net`: the lowest swept frequency whose magnitude
has fallen to `1/√2` of the passband (first-sample) magnitude. Assumes a
low-pass–shaped response over an ascending sweep. -/
def bandwidth3dB (net : Nat) (sweep : Array (Float × Array Complex)) : Option Float :=
  sweep[0]?.bind fun (_, x₀) =>
    let thresh := (acNet net x₀).magnitude / Float.sqrt 2.0
    (sweep.find? fun (_, x) => (acNet net x).magnitude ≤ thresh).map (·.1)

end Sparkle.Analog

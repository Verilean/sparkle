import Sparkle.Analog.Solver.MNA

/-!
# Transient analysis

Steps the circuit forward in time with Backward Euler: at each step the
differential operators are discretized against the previous solution and the
resulting algebraic system is solved by Newton. The result is a `Trace` of
`(time, solution)` samples.

The previous solution is fed back in as both the discretization point and the
Newton seed, so reactive elements (capacitor/inductor) carry state across steps.
The initial state is zero (e.g. an uncharged capacitor), which is the natural
condition for a step response.
-/

namespace Sparkle.Analog

/-- A transient result: `(time, solution-vector)` per step, including the initial
`t = 0` sample. -/
abbrev Trace := Array (Float × Array Float)

/-- Run `steps` Backward-Euler steps of size `dt`. Stops early (returning the
trace so far) if a step's Jacobian is singular. -/
def Circuit.transient (c : Circuit) (dt : Float) (steps : Nat) : Trace := Id.run do
  let x0 := Array.replicate c.dim 0.0
  let mut x := x0
  let mut trace : Trace := #[(0.0, x0)]
  for k in [0:steps] do
    let tPrev := dt * Float.ofNat k
    let tNow := dt * Float.ofNat (k + 1)
    let prev := c.envOf x
    match c.newtonStep dt tPrev tNow prev x with
    | some x' =>
      x := x'
      trace := trace.push (tNow, x')
    | none => return trace
  return trace

/-- L∞ distance between two solution vectors (the local-error estimate). -/
private def vecDist (a b : Array Float) : Float := Id.run do
  let mut m := 0.0
  for i in [0:a.size] do
    let d := Float.abs (a[i]! - b[i]!)
    if d > m then m := d
  return m

/-- Adaptive Backward-Euler transient with step-doubling local-error control.

Each tentative step compares one full step of size `dt` against two half-steps;
their difference estimates the local truncation error. A step is accepted — taking
the more accurate two-half-step result — when the error is within `tol`, and `dt`
is then grown or shrunk by the standard order-1 controller `dt·√(tol/err)`
(safety-clamped to ×[0.25, 4]); otherwise it is halved and retried. This is the
unconditionally-stable implicit scheme verified in `Sparkle.Analog.Proofs.RC`, now
with automatic step sizing: fine where the solution moves fast, coarse where slow.
Returns the trace at the accepted (non-uniform) time points. -/
def Circuit.transientAdaptive (c : Circuit) (tStop dtInit tol : Float)
    (maxSteps : Nat := 100000) : Trace := Id.run do
  let x0 := Array.replicate c.dim 0.0
  let dtMin := dtInit * 1e-9
  let mut x := x0
  let mut t := 0.0
  let mut dt := dtInit
  let mut trace : Trace := #[(0.0, x0)]
  for _ in [0:maxSteps] do
    if t ≥ tStop then
      return trace
    if t + dt > tStop then
      dt := tStop - t
    let prev := c.envOf x
    match c.newtonStep dt t (t + dt) prev x,
          c.newtonStep (dt / 2.0) t (t + dt / 2.0) prev x with
    | some xFull, some xH1 =>
      match c.newtonStep (dt / 2.0) (t + dt / 2.0) (t + dt) (c.envOf xH1) xH1 with
      | some xH2 =>
        let err := vecDist xFull xH2
        if err ≤ tol || dt ≤ dtMin then
          x := xH2
          t := t + dt
          trace := trace.push (t, xH2)
          let raw := 0.9 * Float.sqrt (tol / err)
          let factor := if err == 0.0 || raw > 4.0 then 4.0
                        else if raw < 0.25 then 0.25 else raw
          dt := dt * factor
        else
          dt := dt / 2.0
      | none => return trace
    | _, _ => return trace
  return trace

/-- Extract `(time, V(net))` over a trace. -/
def Trace.sampleNet (c : Circuit) (net : Nat) (tr : Trace) : Array (Float × Float) :=
  tr.map (fun (t, x) => (t, (c.envOf x) (.netPotential net)))

/-- The net potential at the final step. -/
def Trace.finalNet (c : Circuit) (net : Nat) (tr : Trace) : Float :=
  match tr.back? with
  | some (_, x) => (c.envOf x) (.netPotential net)
  | none => 0.0

end Sparkle.Analog

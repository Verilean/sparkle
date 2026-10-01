
# Chapter 15 — A fluid and a plasma: stencil circuits, exact conservation, and a controller's proven limits

Two physics circuits, chosen because each needs something the earlier
chapters did not have:

| | Part A — a fluid | Part B — a plasma |
|---|---|---|
| what | a lattice-Boltzmann fluid, one hardware cell per lattice site | vertical stabilisation of a tokamak plasma: plant model + controller |
| new construct | `torus_grid%`: a lattice whose cells read all eight neighbours | — (plain `circuit do`) |
| what is exact | mass and momentum, rounding included (theorems) | the recoverable region of the saturating controller (theorems) |
| what is measured | viscosity against theory; circuit == model; GPU == CPU | circuit == model; recovery inside, loss outside |
| files | `IP/Fluid/LBM.lean`, `Tests/FluidLbmTest.lean` | `IP/Plasma/VerticalStab.lean`, `Tests/PlasmaTest.lean` |

Both follow the pattern of Chapter 12: a **reference model** in plain Lean
with the same fixed-point arithmetic as the circuit; **theorems** about the
model; the **circuit** compared with the model cycle by cycle.  What is
proven and what is only tested is stated for each — read §15.9 before
relying on either.

```lean
import Sparkle
import Sparkle.Compiler.Elab
import IP.Fluid.LBM
import IP.Plasma.VerticalStab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Ch15

```

# Part A — a fluid

## 15.1 A lattice of cells: `torus_grid%`

A stencil computation updates every site of a grid from its neighbours.
As a circuit that is one cell per site, each wired to the cells around it.
The systolic array of Chapter 13 passes data one way (left to right, top
to bottom), so its cells are a chain of `let`s.  A stencil's cells depend
on each other in both directions; the lattice is therefore one
`Signal.loop` over the outputs of *all* cells, and `torus_grid%` writes it.

Here is the smallest example — heat spreading on a 4 × 4 torus.  The cell
holds one number and replaces it by a weighted mean of itself and its
four neighbours:

```lean
structure HeatOut (dom : DomainConfig) where
  u : Signal dom (BitVec 32)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (HeatOut dom) dom := ⟨⟩

/-- u ← (4u + n + s + w + e)/8, or the initial value while `load`. -/
@[hardware_module] def heatCell {dom : DomainConfig}
    (n s w e init : Signal dom (BitVec 32)) (load : Signal dom Bool) : HeatOut dom :=
  circuit do
    let r ← Signal.reg 0#32
    let u := (r : Signal dom (BitVec 32))
    let u2 := u + u
    let total := u2 + u2 + n + s + w + e
    -- divide by 8: drop three bits
    let eighth := (Signal.pure 0#3 : Signal dom (BitVec 3)) ++ total.map (BitVec.extractLsb' 3 29 ·)
    r <~ Signal.mux load init eighth
    return ({ u := u } : HeatOut dom)

/-- One hot site, at (0, 0). -/
def hot (i j : Nat) : BitVec 32 := BitVec.ofNat 32 ((1 - (i + j)) * 4096)

def heat4 (load : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 512) :=
  torus_grid% 4 4
    (fields := u) (width := 32)
    (cell i j nb => heatCell nb.n.u nb.s.u nb.w.u nb.e.u (Signal.pure (hot i j)) load)

/-- The 4 × 4 values of a packed state, row by row. -/
def rows4 (st : BitVec 512) : List (List Nat) :=
  (List.range 4).map fun i => (List.range 4).map fun j =>
    (st.extractLsb' ((i * 4 + j) * 32) 32).toNat

#eval do
  let load : Signal defaultDomain Bool := ⟨fun t => t == 0⟩
  for t in [1, 2, 3, 12] do
    IO.println s!"cycle {t}: {rows4 ((heat4 load).val t)}"

```

(`load` is high in cycle 0, so the hot site appears in cycle 1.  The heat
spreads to the four neighbours — including the ones "behind" row 0 and
column 0: the lattice wraps.)

```text
cycle 1: [[4096, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
cycle 2: [[2048, 512, 0, 512], [512, 0, 0, 0], [0, 0, 0, 0], [512, 0, 0, 0]]
cycle 3: [[1280, 512, 128, 512], [512, 128, 0, 128], [128, 0, 0, 0], [512, 128, 0, 128]]
cycle 12: [[298, 276, 254, 276], [276, 254, 232, 254], [254, 232, 211, 232], [276, 254, 232, 254]]
```

Reading the macro call:

* `torus_grid% 4 4` — rows, columns.  The lattice wraps around in both
  directions.
* `(fields := u) (width := 32)` — the output fields of the cell, each a
  `Signal dom (BitVec 32)`.  They must be registers: there has to be a
  register between any two cells.
* `(cell i j nb => …)` — the cell at row `i`, column `j`.  `i` and `j`
  become numerals (so `hot i j` is a constant per cell); `nb.n.u` is field
  `u` of the northern neighbour.  Directions: `n s w e nw ne sw se`.
* The value is every field of every cell, packed: field `f` of cell
  (i, j) at bit `((i·C + j)·F + f)·width`.

What you get in hardware is R·C instances of one cell module with direct
cell-to-cell wires (`#synthesizeVerilogDesign heat4` shows it); the packed
state exists only as the output port.

> **A bug this construct found.**  Instances wired in a *cycle* — every
> lattice — were simulated wrongly by the C backend (`#sim`, JIT): it
> evaluated and clocked the instances one after the other, so each cell
> saw some neighbours one cycle late.  A ring of four cells diverged from
> `Signal.val` in its second cycle.  The backend now recognises a cycle
> through Moore instances, refreshes their outputs first, and clocks
> everything afterwards; `Tests/TorusGridTest.lean` pins it (macro ==
> hand-written wiring == JIT, every cycle).

## 15.2 Lattice-Boltzmann in one page

Each site holds nine *populations* f₀…f₈ — how much fluid is about to
move along each of nine lattice velocities:

```text
   7  4  8        0 rest
    ╲ │ ╱         1 E   2 S   3 W   4 N
   3─ 0 ─1        5 SE  6 SW  7 NW  8 NE
    ╱ │ ╲
   6  2  5        (x = column, east +;  y = row, south +)
```

One time step:

1. **stream** — population i moves to the neighbour in direction i;
2. **collide** — at each site the populations relax towards the local
   equilibrium, `fᵢ ← fᵢ + ω·(eqᵢ − fᵢ)`, which depends only on the
   site's density ρ = Σfᵢ and momentum j = Σcᵢfᵢ.

The fluid that results obeys the Navier–Stokes equations at low speed,
with kinematic viscosity **ν = (1/ω − 1/2)/3**.  That one formula is what
§15.4 measures.

As a circuit, streaming is *wiring* (cell (i, j) takes population 1 from
its western neighbour, population 2 from its northern one, …) and
collision is the cell: nine registers and 22 multiplies (three products
of the momentum, eleven by constants, eight by ω).  One lattice time step
per clock, all sites at once.

```lean
open Sparkle.IP.Fluid.LBM in
#check @lbmCell      -- the cell: 8 incoming populations, the initial condition, ω, load

open Sparkle.IP.Fluid.LBM in
/-- A 4 × 4 lattice with a Taylor–Green vortex as the initial condition
    (this is `tg4` in the IP file). -/
def fluid4 (omega : Signal defaultDomain (BitVec 32)) (load : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 4608) :=
  torus_grid% 4 4
    (fields := g0 g1 g2 g3 g4 g5 g6 g7 g8) (width := 32)
    (cell i j nb => lbmCell nb.w.g1 nb.n.g2 nb.e.g3 nb.s.g4 nb.nw.g5 nb.ne.g6 nb.se.g7 nb.sw.g8
      (Signal.pure (tgRho 4 i j)) (Signal.pure (tgJx 4 i j)) (Signal.pure (tgJy 4 i j))
      omega load)

```

## 15.3 Conservation that survives rounding

The numbers are Q7.24 fixed point.  Every multiply rounds, and a fluid
simulation runs for thousands of steps — so the question is what the
rounding does in the long run.

The collision is written so that **mass and momentum are conserved
exactly**, whatever the rounding did: after the eight moving populations
have been relaxed, the east and south populations absorb the momentum
the rounding lost and the rest population absorbs the mass.  These are
theorems about the reference model — for every input and every ω,
wrap-around included:

```lean
open Sparkle.IP.Fluid.LBM in
#check @collide_mass   -- (collide ω f).mass = f.mass
open Sparkle.IP.Fluid.LBM in
#check @collide_jx     -- (collide ω f).jx = f.jx
open Sparkle.IP.Fluid.LBM in
#check @collide_jy     -- (collide ω f).jy = f.jy

open Sparkle.IP.Fluid.LBM in
#eval do
  let omega := omegaOf 4 5                -- τ = 0.8: ω = 1.25, ν = 0.1
  let l0 := tgLattice 16
  let l := l0.run omega 300
  IO.println s!"mass      {l0.mass.toInt} → {l.mass.toInt}"
  IO.println s!"momentum  ({l0.momentum.1.toInt}, {l0.momentum.2.toInt}) → ({l.momentum.1.toInt}, {l.momentum.2.toInt})"
  IO.println s!"a population that did change: {(l0.get 3 5).g1.toInt} → {(l.get 3 5).g1.toInt}"

```

(units of 2⁻²⁴; the totals are not zero because the initial condition is
itself rounded.)

```text
mass      -80 → -80
momentum  (-96, -96) → (-96, -96)
a population that did change: 64061 → 6
```

This is not cosmetic.  The first version conserved only mass; momentum
drifted by a fraction of a unit of 2⁻²⁴ per collision.  That sounds
harmless and is not: the drift correlates with the flow, and on a 64-row
shear wave the measured viscosity was 0.2 % off a double-precision run of
the same method (0.5 % with truncating multiplies).  With exact
conservation the difference is below 0.001 %.  The lesson generalises: in
a long-running fixed-point simulation, make the invariants exact *by
construction* and let the rounding go where no invariant lives.

## 15.4 Does it behave like a fluid?

A shear wave — velocity along x varying sinusoidally along y — decays as
exp(−ν·k²·t).  Measuring the decay gives the viscosity, to compare with
(1/ω − 1/2)/3:

```lean
namespace Shear
open Sparkle.IP.Fluid.LBM

def toF (x : BitVec 32) : Float := Float.ofInt x.toInt / 16777216.0

/-- Amplitude of the fundamental mode: (2/R)·Σᵢ jx(i, 0)·sin(2πi/R). -/
def amplitude (l : Lattice) : Float :=
  (List.range l.rows).foldl (fun acc i =>
    acc + toF (l.get i 0).jx * Float.sin (2.0 * 3.141592653589793 * i.toFloat / l.rows.toFloat))
    0.0 * 2.0 / l.rows.toFloat

def measured (rows steps : Nat) (omega : BitVec 32) : Float :=
  let l0 := shearLattice rows 2
  let k := 2.0 * 3.141592653589793 / rows.toFloat
  Float.log (amplitude l0 / amplitude (l0.run omega steps)) / (k * k * steps.toFloat)

#eval do
  for (n, d, steps) in [(1, 1, 60), (4, 5, 100), (5, 8, 200)] do
    let omega := omegaOf n d
    let theory := (1.0 / toF omega - 0.5) / 3.0
    IO.println s!"ω = {toF omega}: ν measured {measured 32 steps omega}, theory {theory}"

end Shear
```

```text
ω = 1.000000: ν measured 0.166666, theory 0.166667
ω = 1.250000: ν measured 0.100740, theory 0.100000
ω = 1.600000: ν measured 0.042184, theory 0.041667
```

The remaining difference is the method's, not the arithmetic's: the test
runs the same method in double precision and finds the same viscosity to
0.0004 %, and the difference from theory shrinks four-fold when the
lattice is refined from 32 to 64 rows (second order, as the method
promises):

| ω | ν theory | fixed point vs double | method vs theory, 32 rows | 64 rows |
|---|---|---|---|---|
| 1.0 | 0.16667 | 0.00038 % | 0.00028 % | 0.00002 % |
| 1.25 | 0.1 | 0.00042 % | 0.74 % | 0.18 % |
| 1.6 | 0.04167 | 0.00032 % | 1.24 % | 0.31 % |

A two-dimensional check, the Taylor–Green vortex on 32 × 32, decays at
0.00776 per step against 2νk² = 0.00771 (0.6 % off).

## 15.5 The circuit against the model

`Lattice.step` is the reference; the circuit is compared with it bit for
bit — every population of every site:

```lean
open Sparkle.IP.Fluid.LBM in
#eval do
  let omega := omegaOf 4 5
  let load : Signal defaultDomain Bool := ⟨fun t => t == 0⟩
  let lat := fluid4 (Signal.pure omega) load
  -- `load` is high in cycle 0: the registers hold the initial condition
  -- in cycle 1 and step t−1 of the model in cycle t
  let same := (List.range 4).all fun t =>
    (lat.val (t + 1)).toNat == ((tgLattice 4).run omega t).pack
  IO.println s!"4 × 4 circuit == model for 4 steps: {same}"

```

```text
4 × 4 circuit == model for 4 steps: true
```

`Tests/FluidLbmTest.lean` does the same for a 16 × 16 lattice compiled by
the JIT, at eight checkpoints up to step 200.

## 15.6 One GPU thread per site

A lattice is the shape the intra GPU backend of Chapter 13 is for: many
instances of one small module.  `#writeCudaIntraDesign` emits a kernel
with one thread per cell; `lake exe fluid-cosim` compiles it and runs it
against the C reference:

```text
SPARKLE_CUDA=1 lake exe fluid-cosim
```

```text
[perf] …tg16Top (256 sites, block kernel): CPU 8.301e+04 steps/s, GPU 1.310e+06 steps/s, GPU/CPU 15.79; mass 4294967216 == 4294967216
COSIM PASS (…tg16Top: 64 single-cycle launches, one 1000-cycle and one 200000-cycle launch)
[perf] …tg32Top (1024 sites, block kernel): CPU 2.109e+04 steps/s, GPU 3.802e+05 steps/s, GPU/CPU 18.03; mass 4294966864 == 4294966864
COSIM PASS (…tg32Top: 64 single-cycle launches, one 1000-cycle and one 200000-cycle launch)
```

(RTX 4070 Ti.)  Every population matches after each of 64 single steps,
after 1000 steps and after 200 000; the total mass on the GPU after
200 000 steps equals the initial mass exactly.

Read the ratio with its baseline in mind: "CPU" is the generated C
reference in the same file, on one core.  For a lattice it evaluates each
cell twice per step (outputs first, then the next state) and assembles
the packed output every step; a hand-written C loop over the lattice
would be several times faster than it.  The GPU side is cycle-exact
simulation of the *circuit*, not a GPU fluid solver.

Two changes to the backend came out of this workload (details in
`docs/CudaIntraSim-design.md`):

* **The instance lives in a thread-local variable, and instances talk
  through a small exchange area.**  The generated C reads and writes a
  struct field for every wire; in the GPU's memory that was the whole
  cost.  Held in a local, the struct becomes registers; per cycle a
  thread stores its outputs in the exchange area and loads its inputs
  from it — nothing else.  The exchange area (36 bytes per cell) fits in
  shared memory where the state (196 bytes per cell) does not.  The
  outputs of the new state are computed on a scratch copy, so the
  compiler drops whatever does not feed an output.  Measured on this
  lattice: 1024 sites went from 1.2·10⁴ steps/s (slower than the CPU) to
  3.8·10⁵; the systolic arrays of Chapter 13 gained 5× as well.
* **A refused launch is an error.**  A cell held in registers can need
  more than the 64 a thread gets in a 1024-thread block; the launch is
  then refused, and the old host code returned the state unchanged — a
  run that "did nothing" at an impossible speed.  Now the refusal selects
  the grid kernel, and any other kernel failure aborts with the CUDA
  error.

# Part B — a plasma

## 15.7 The plant, and the one number that matters

An elongated tokamak plasma is vertically unstable: displace it and the
shaping field pushes it further.  Passive structure slows the motion to
a growth rate γ; an active coil, driven by a power supply, pushes back.
The reduced model has three states — position z, coil current I, supply
voltage V — and one input, the commanded voltage, which **saturates**:

```text
z' = z + z/64 + I/16          growth γ = 250 /s,  dt = 1/16 ms
I' = I − I/64 + V/16          coil L/R = 4 ms
V' = V + 7·(V_cmd − V)/64     supply lag ≈ 0.57 ms,   |V_cmd| ≤ V_max = 2
```

(forward Euler with every coefficient a shift; Q15.16; divisions round
down.)  The matrix has one eigenvalue outside the unit circle, 65/64, and
its left eigenvector is (1, 2, 1).  So one combination of the states
carries the instability:

```text
ξ = z + 2·I + V            ξ' = (65/64)·ξ + (7/64)·V_cmd
```

Two things follow at once.  If |ξ| ≥ 7·V_max = 14, even full opposing
voltage cannot stop ξ growing: **the plasma is lost, whatever the
controller**.  And inside, the saturating law

```text
V_cmd = clamp(−4·ξ, ±V_max)
```

recovers everything: ×37/64 per step when unsaturated, still decreasing
when saturated.  The controller is three adds, two shifts and a clamp.

```lean
open Sparkle.IP.Plasma.VerticalStab in
#check @controller   -- z, I, V measurements in; the supply command out
open Sparkle.IP.Plasma.VerticalStab in
#check @closedLoop   -- plant + controller, for simulation: alarm ++ V_cmd ++ z

open Sparkle.IP.Plasma.VerticalStab in
/-- States of the closed loop after one displacement `z0` (units of 2⁻¹⁶). -/
def afterKick (z0 : Int) (n : Nat) : Array State := Id.run do
  let mut s : State := default
  let mut out : Array State := #[]
  for t in [0:n] do
    out := out.push s
    s := step true s (if t == 0 then z0 else 0)
  return out

open Sparkle.IP.Plasma.VerticalStab in
#eval do
  for cm10 in [50, 139, 141] do
    let tr := afterKick (cm10 * 65536 / 10) 3000
    let settled := (List.range 3000).find? fun (t : Nat) => t > 0 && (xi tr[t]!).natAbs < 16
    let wall := (List.range 3000).find? fun (t : Nat) => (tr[t]!).z == zWall
    IO.println s!"displaced {cm10 / 10}.{cm10 % 10} cm: recovered after {settled} steps, wall after {wall} steps"

```

```text
displaced 5.0 cm: recovered after (some 41) steps, wall after none steps
displaced 13.9 cm: recovered after (some 331) steps, wall after none steps
displaced 14.1 cm: recovered after none steps, wall after (some 330) steps
```

13.9 cm comes back (in 331 control periods, 21 ms); 14.1 cm reaches the
wall with the supply at its limit the whole way.

## 15.8 Proving the region

Simulation shows three displacements.  The theorems cover all states, and
they are about the model **with its rounding** — integers, floors and
all — not about the real-valued equations:

```lean
open Sparkle.IP.Plasma.VerticalStab in
#check @recoverable_invariant  -- the region |ξ| ≤ 14 − 2⁻⁷ is never left
open Sparkle.IP.Plasma.VerticalStab in
#check @recoverable_progress   -- inside it, |ξ| decreases while it is ≥ 16 units
open Sparkle.IP.Plasma.VerticalStab in
#check @recovers               -- so |ξ| < 16 units is reached, in ≤ |ξ| steps
open Sparkle.IP.Plasma.VerticalStab in
#check @beyond_is_lost         -- for |ξ| ≥ 14 + 2⁻⁷ and ANY |V_cmd| ≤ V_max, |ξ| grows

end Notebooks.Ch15
```

The proofs are `omega` — linear integer arithmetic with the floors — so
they are checked by Lean's kernel; no solver is trusted.  Two details
worth knowing:

* **The rounding shows up in the theorem.**  The first statement used the
  region |ξ| ≤ 14 − 2⁻⁹ and was false: the prover returned a state on the
  negative edge that leaves it by one unit.  The floors can move ξ by up
  to 5 units per step, always downwards, which costs the negative side
  320 units.  Hence 14 − 2⁻⁷ inside and 14 + 2⁻⁷ outside; the 0.016 cm in
  between is not covered either way.
* **Take the `if`s out before calling `omega`.**  With the two clamps
  unfolded the goal had thousands of case combinations and did not finish
  in ten minutes; with each clamp replaced by a variable and three linear
  facts about it (`clamp_spec`) all five theorems take two seconds.

## 15.9 What is and is not established

| claim | status |
|---|---|
| LBM collision conserves mass, x- and y-momentum exactly | **proven** for the reference model (`collide_mass`, `_jx`, `_jy`) |
| lattice totals constant over a run | tested (300 steps, exact equality) — the lattice-level theorem (streaming is a permutation) is not written |
| viscosity = (1/ω − 1/2)/3 | measured: within 1.3 % at 32 rows, 0.3 % at 64 rows, three values of ω |
| LBM circuit == reference model | tested: 4 × 4 `Signal.val`, 16 × 16 JIT up to step 200; **not proven** |
| GPU == C reference | tested: 256 and 1024 sites, single steps and a 200 000-step run |
| plasma: recoverable region invariant, |ξ| decreasing, recovery, loss beyond | **proven** for the integer model (`omega`) |
| plasma circuit == integer model | tested: 240 cycles `Signal.val`, 4000 cycles JIT; **not proven** |

Limits of the designs themselves:

* **Fluid.**  Periodic boundaries only — no walls, no inflow, no body
  force, so no channel or cavity flow yet.  One cell per site: fine for
  simulation and small lattices, but an FPGA implementation of a large
  lattice would time-multiplex one collision unit over block RAM.  Q7.24
  and the low-speed equilibrium limit the flow speed (the tests use
  0.03 lattice units).  The 32 × 32 lattice cannot be simulated with
  `Signal.val` (Lean's code generator overflows its stack on a function
  that size); the JIT and the GPU handle it.
* **Plasma.**  A reduced model with round-number parameters, not a
  machine.  The controller sees all three states exactly: no measurement
  noise, no delay, no estimator, no coil-current limit.  The discrete
  model is forward Euler.  The theorems say what this controller does to
  this model — which is the part a proof can settle — not that the model
  is right.

## Exercises

1. Change `heatCell` so that the total heat is conserved exactly (hint:
   the trick of §15.3 — compute what each neighbour pair exchanges once,
   and add it on one side and subtract it on the other).  Check with
   `Signal.val`.
2. Run the shear wave at ω = 1.9.  What viscosity do you expect, and how
   many rows do you need for 1 % agreement?
3. `collide_mass` is per site.  State the lattice-level theorem
   (`(l.step ω).mass = l.mass`) and say what you would need to prove
   about `Lattice.incoming`.
4. Halve the supply limit (`vMax`).  Where does the recoverable region
   end now?  Change `xiSafe` and the bound in `beyond_is_lost`
   accordingly and re-run the proofs.
5. The controller uses gain 4.  What is the largest power-of-two gain for
   which `recoverable_progress` still holds, and what fails beyond it?

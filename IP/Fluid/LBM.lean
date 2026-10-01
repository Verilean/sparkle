/-
  D2Q9 lattice-Boltzmann fluid — one hardware cell per lattice site.

  ## The method

  Each lattice site holds nine populations f₀…f₈: the amount of fluid
  about to move along one of nine lattice velocities

      7  4  8        (cx, cy):   0 (0,0)
       ╲ │ ╱                     1 (1,0) E    2 (0,1) S    3 (−1,0) W   4 (0,−1) N
      3─ 0 ─1                    5 (1,1) SE   6 (−1,1) SW  7 (−1,−1) NW 8 (1,−1) NE
       ╱ │ ╲
      6  2  5        x = column (east +),  y = row (south +)

  One time step is
    * streaming — population i moves to the neighbour in direction i;
    * collision — at every site the populations relax towards the local
      equilibrium:  fᵢ ← fᵢ + ω·(eqᵢ − fᵢ).
  Density and momentum are the moments  ρ = Σ fᵢ,  j = Σ cᵢ fᵢ, and the
  fluid that results has kinematic viscosity  ν = (1/ω − 1/2)/3  (lattice
  units).  This is the incompressible variant (He & Luo 1997): the
  equilibrium uses the momentum directly, so the cell needs no divider.

  ## The circuit

  A cell (`lbmCell`) is nine registers holding its post-collision
  populations.  Every clock it takes one population from each of its eight
  neighbours (the streaming step is wiring), collides, and registers the
  result — one lattice time step per clock, every site in parallel.
  `torus_grid%` instantiates R·C cells on a periodic lattice.

  The numbers are Q7.24 fixed point in `BitVec 32`, stored as the deviation
  from the fluid at rest (fᵢ − wᵢ), which is where the precision is needed.

  ## What is exact, and what is not

  * Mass and momentum are conserved EXACTLY by the collision, rounding and
    wrap-around included (`collide_mass`, `collide_jx`, `collide_jy`): after
    relaxing the eight moving populations, the east and south populations
    absorb the momentum the rounding lost and the rest population absorbs
    the mass (`conserve`).  Streaming only moves populations, so the totals
    over the lattice never change — the test checks this over hundreds of
    steps.
  * This is not cosmetic.  Without the momentum correction every collision
    loses or gains a fraction of a unit of 2⁻²⁴ of momentum, in a way that
    correlates with the flow; on a 64-row shear wave the measured viscosity
    was 0.2 % off the double-precision reference (0.5 % with truncating
    multiplies and constants).  With it: under 0.001 %.
  * Everything else is rounded: the viscous stress carries rounding noise
    of a few units of 2⁻²⁴ per site and step.
  * The pure functions below (`collide`, `step`) are the reference the
    circuit is compared against bit for bit, in simulation.  That the
    circuit computes them is tested, not proven.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.FixedPoint

namespace Sparkle.IP.Fluid.LBM

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.FixedPoint (sext32to64)

/-! ### Fixed point: Q7.24 -/

def fracBits : Nat := 24

/-- The Q7.24 word nearest to `n / d` (`d > 0`). -/
def q (n d : Int) : BitVec 32 := BitVec.ofInt 32 ((2 * n * 2 ^ 24 + d) / (2 * d))

/-- Half a unit of the last place of a product, before it is narrowed. -/
def half : BitVec 64 := BitVec.ofNat 64 (2 ^ 23)

/-- Signed Q7.24 multiply, rounded to nearest: `⌊a·b / 2²⁴ + 1/2⌋`.
    (Truncation would lose half a unit per multiply, always in the same
    direction.)  The constants below are rounded to nearest as well; 1/6
    and 1/12 then add up so that 4·(1/6 + 1/12) is exactly 1. -/
def mulF (a b : BitVec 32) : BitVec 32 :=
  BitVec.extractLsb' 24 32 (a.signExtend 64 * b.signExtend 64 + half)

def c9 : BitVec 32 := q 1 9
def c36 : BitVec 32 := q 1 36
def c6 : BitVec 32 := q 1 6
def c12 : BitVec 32 := q 1 12
def c4 : BitVec 32 := q 1 4

/-- Collision frequency for a given relaxation time τ = n/d (ω = d/n). -/
def omegaOf (n d : Int) : BitVec 32 := q d n

/-! ### One site -/

/-- The nine populations of a site (deviation from rest, Q7.24). -/
structure Pops where
  g0 : BitVec 32
  g1 : BitVec 32
  g2 : BitVec 32
  g3 : BitVec 32
  g4 : BitVec 32
  g5 : BitVec 32
  g6 : BitVec 32
  g7 : BitVec 32
  g8 : BitVec 32
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Density (deviation from 1). -/
def Pops.mass (p : Pops) : BitVec 32 :=
  p.g0 + (p.g1 + p.g2 + p.g3 + p.g4 + p.g5 + p.g6 + p.g7 + p.g8)

/-- Momentum along x (east). -/
def Pops.jx (p : Pops) : BitVec 32 := p.g1 - p.g3 + p.g5 - p.g6 - p.g7 + p.g8

/-- Momentum along y (south). -/
def Pops.jy (p : Pops) : BitVec 32 := p.g2 - p.g4 + p.g5 + p.g6 - p.g7 - p.g8

/-- Equilibrium populations 1…8 for density `rho` and momentum `(jx, jy)`:
    wᵢ·(ρ + 3 c·j + 4.5 (c·j)² − 1.5 j²), with the constants folded so that
    each direction costs one constant multiply. -/
structure Eq8 where
  e1 : BitVec 32
  e2 : BitVec 32
  e3 : BitVec 32
  e4 : BitVec 32
  e5 : BitVec 32
  e6 : BitVec 32
  e7 : BitVec 32
  e8 : BitVec 32

def equilibrium (rho jx jy : BitVec 32) : Eq8 :=
  let xx := mulF jx jx
  let yy := mulF jy jy
  let xy4 := mulF (mulF jx jy) c4
  let r9 := mulF rho c9
  let r36 := mulF rho c36
  let sq := xx + yy
  let twoX := jx + jx
  let twoY := jy + jy
  { e1 := r9 + mulF (xx + xx - yy + twoX) c6
    e2 := r9 + mulF (yy + yy - xx + twoY) c6
    e3 := r9 + mulF (xx + xx - yy - twoX) c6
    e4 := r9 + mulF (yy + yy - xx - twoY) c6
    e5 := r36 + mulF (sq + jx + jy) c12 + xy4
    e6 := r36 + mulF (sq - jx + jy) c12 - xy4
    e7 := r36 + mulF (sq - jx - jy) c12 + xy4
    e8 := r36 + mulF (sq + jx - jy) c12 - xy4 }

/-- Make eight moving populations carry exactly density `rho` and momentum
    `(jx, jy)`: the east population absorbs the missing x-momentum, the
    south population the missing y-momentum, and the rest population the
    missing mass.  The corrections are the rounding errors of the caller —
    a few units of 2⁻²⁴. -/
def conserve (rho jx jy g1 g2 g3 g4 g5 g6 g7 g8 : BitVec 32) : Pops :=
  let g1 := g1 + (jx - (g1 - g3 + g5 - g6 - g7 + g8))
  let g2 := g2 + (jy - (g2 - g4 + g5 + g6 - g7 - g8))
  { g0 := rho - (g1 + g2 + g3 + g4 + g5 + g6 + g7 + g8)
    g1, g2, g3, g4, g5, g6, g7, g8 }

theorem conserve_mass (rho jx jy g1 g2 g3 g4 g5 g6 g7 g8 : BitVec 32) :
    (conserve rho jx jy g1 g2 g3 g4 g5 g6 g7 g8).mass = rho := by
  simp only [conserve, Pops.mass]
  exact BitVec.sub_add_cancel _ _

theorem conserve_jx (rho jx jy g1 g2 g3 g4 g5 g6 g7 g8 : BitVec 32) :
    (conserve rho jx jy g1 g2 g3 g4 g5 g6 g7 g8).jx = jx := by
  simp only [conserve, Pops.jx]
  bv_omega

theorem conserve_jy (rho jx jy g1 g2 g3 g4 g5 g6 g7 g8 : BitVec 32) :
    (conserve rho jx jy g1 g2 g3 g4 g5 g6 g7 g8).jy = jy := by
  simp only [conserve, Pops.jy]
  bv_omega

/-- The site at equilibrium (the initial condition), with exactly the
    requested density and momentum. -/
def atEquilibrium (rho jx jy : BitVec 32) : Pops :=
  let e := equilibrium rho jx jy
  conserve rho jx jy e.e1 e.e2 e.e3 e.e4 e.e5 e.e6 e.e7 e.e8

/-- Collision: every moving population relaxes towards the equilibrium of
    the site's own density and momentum, which are then restored exactly. -/
def collide (omega : BitVec 32) (f : Pops) : Pops :=
  let rho := f.mass
  let jx := f.jx
  let jy := f.jy
  let e := equilibrium rho jx jy
  conserve rho jx jy
    (f.g1 + mulF omega (e.e1 - f.g1)) (f.g2 + mulF omega (e.e2 - f.g2))
    (f.g3 + mulF omega (e.e3 - f.g3)) (f.g4 + mulF omega (e.e4 - f.g4))
    (f.g5 + mulF omega (e.e5 - f.g5)) (f.g6 + mulF omega (e.e6 - f.g6))
    (f.g7 + mulF omega (e.e7 - f.g7)) (f.g8 + mulF omega (e.e8 - f.g8))

/-- Collision conserves mass exactly — for every input and every ω,
    rounding and wrap-around included. -/
theorem collide_mass (omega : BitVec 32) (f : Pops) :
    (collide omega f).mass = f.mass := by
  simp only [collide, conserve_mass]

/-- Collision conserves x-momentum exactly. -/
theorem collide_jx (omega : BitVec 32) (f : Pops) :
    (collide omega f).jx = f.jx := by
  simp only [collide, conserve_jx]

/-- Collision conserves y-momentum exactly. -/
theorem collide_jy (omega : BitVec 32) (f : Pops) :
    (collide omega f).jy = f.jy := by
  simp only [collide, conserve_jy]

/-- The equilibrium site has exactly the requested density and momentum. -/
theorem atEquilibrium_moments (rho jx jy : BitVec 32) :
    (atEquilibrium rho jx jy).mass = rho ∧ (atEquilibrium rho jx jy).jx = jx ∧
      (atEquilibrium rho jx jy).jy = jy := by
  simp only [atEquilibrium, conserve_mass, conserve_jx, conserve_jy, and_self]

/-! ### The lattice (reference model) -/

/-- R × C sites, row-major, periodic in both directions. -/
structure Lattice where
  rows : Nat
  cols : Nat
  cells : Array Pops
  deriving Repr, BEq

def Lattice.get (l : Lattice) (i j : Nat) : Pops :=
  l.cells.getD ((i % l.rows) * l.cols + (j % l.cols)) default

/-- The populations arriving at site (i, j): population d comes from the
    neighbour it was moving away from. -/
def Lattice.incoming (l : Lattice) (i j : Nat) : Pops :=
  let up := l.rows - 1      -- row i−1, modulo rows
  let left := l.cols - 1    -- column j−1, modulo cols
  { g0 := (l.get i j).g0
    g1 := (l.get i (j + left)).g1             -- moving east: from the west
    g2 := (l.get (i + up) j).g2               -- moving south: from the north
    g3 := (l.get i (j + 1)).g3                -- moving west: from the east
    g4 := (l.get (i + 1) j).g4                -- moving north: from the south
    g5 := (l.get (i + up) (j + left)).g5      -- moving south-east: from the north-west
    g6 := (l.get (i + up) (j + 1)).g6         -- moving south-west: from the north-east
    g7 := (l.get (i + 1) (j + 1)).g7          -- moving north-west: from the south-east
    g8 := (l.get (i + 1) (j + left)).g8 }     -- moving north-east: from the south-west

/-- One time step: stream, then collide, at every site. -/
def Lattice.step (omega : BitVec 32) (l : Lattice) : Lattice :=
  { l with cells := Array.ofFn (n := l.rows * l.cols) fun k =>
      collide omega (l.incoming (k.val / l.cols) (k.val % l.cols)) }

def Lattice.run (omega : BitVec 32) (l : Lattice) : Nat → Lattice
  | 0 => l
  | n + 1 => Lattice.run omega (l.step omega) n

/-- Total mass (sum of all populations of all sites). -/
def Lattice.mass (l : Lattice) : BitVec 32 :=
  l.cells.foldl (fun acc p => acc + p.mass) 0#32

/-- Total momentum (x, y). -/
def Lattice.momentum (l : Lattice) : BitVec 32 × BitVec 32 :=
  l.cells.foldl (fun (ax, ay) p => (ax + p.jx, ay + p.jy)) (0#32, 0#32)

/-- A lattice with every site at the equilibrium of the given field. -/
def Lattice.ofField (rows cols : Nat) (field : Nat → Nat → BitVec 32 × BitVec 32 × BitVec 32) :
    Lattice :=
  { rows, cols
    cells := Array.ofFn (n := rows * cols) fun k =>
      let (rho, jx, jy) := field (k.val / cols) (k.val % cols)
      atEquilibrium rho jx jy }

/-- All populations packed the way the circuit's output is: population d of
    site (i, j) in bits `[((i·C + j)·9 + d)·32 +: 32]`. -/
def Lattice.pack (l : Lattice) : Nat :=
  (List.range (l.rows * l.cols)).foldl (fun acc k =>
    let p := l.cells.getD k default
    let word (d : Nat) (v : BitVec 32) : Nat := v.toNat <<< ((k * 9 + d) * 32)
    acc ||| word 0 p.g0 ||| word 1 p.g1 ||| word 2 p.g2 ||| word 3 p.g3 ||| word 4 p.g4
        ||| word 5 p.g5 ||| word 6 p.g6 ||| word 7 p.g7 ||| word 8 p.g8) 0

/-! ### Initial conditions

Written with integer arithmetic on a sine table so that the synthesis
elaborator can evaluate them: every cell gets its initial density and
momentum as constants. -/

/-- sin(2π·k/64) in Q7.24. -/
def sinTable : List Int :=
  [0, 1644455, 3273072, 4870169, 6420363, 7908725, 9320922, 10643353,
   11863283, 12968963, 13949745, 14796184, 15500126, 16054795, 16454846, 16696429,
   16777216, 16696429, 16454846, 16054795, 15500126, 14796184, 13949745, 12968963,
   11863283, 10643353, 9320922, 7908725, 6420363, 4870169, 3273072, 1644455,
   0, -1644455, -3273072, -4870169, -6420363, -7908725, -9320922, -10643353,
   -11863283, -12968963, -13949745, -14796184, -15500126, -16054795, -16454846, -16696429,
   -16777216, -16696429, -16454846, -16054795, -15500126, -14796184, -13949745, -12968963,
   -11863283, -10643353, -9320922, -7908725, -6420363, -4870169, -3273072, -1644455]

def sinQ (k : Nat) : Int := sinTable.getD (k % 64) 0
def cosQ (k : Nat) : Int := sinQ (k + 16)

/-- A signed value as the 32-bit two's-complement word. -/
def word (x : Int) : BitVec 32 := BitVec.ofNat 32 (x % 4294967296).toNat

/-- Shear wave on an n-row lattice (n divides 64): velocity along x,
    varying along y,  jx = U·sin(2π·i/n),  U = 1/32. -/
def shearJx (n i : Nat) : BitVec 32 := word (sinQ (i * (64 / n)) / 32)

/-- Taylor–Green vortex on an n × n lattice (n divides 64), U = 1/32:
      jx = −U·cos(kx)·sin(ky)     jy = U·sin(kx)·cos(ky)
      δρ = −(3U²/4)·(cos 2kx + cos 2ky)          k = 2π/n, x = j, y = i. -/
def tgJx (n i j : Nat) : BitVec 32 :=
  word (-(cosQ (j * (64 / n)) * sinQ (i * (64 / n))) / (16777216 * 32))

def tgJy (n i j : Nat) : BitVec 32 :=
  word ((sinQ (j * (64 / n)) * cosQ (i * (64 / n))) / (16777216 * 32))

def tgRho (n i j : Nat) : BitVec 32 :=
  word (-(3 * (cosQ (2 * j * (64 / n)) + cosQ (2 * i * (64 / n)))) / 4096)

/-- The Taylor–Green vortex as a reference lattice. -/
def tgLattice (n : Nat) : Lattice :=
  Lattice.ofField n n fun i j => (tgRho n i j, tgJx n i j, tgJy n i j)

/-- The shear wave as a reference lattice (`rows` rows, `cols` columns). -/
def shearLattice (rows cols : Nat) : Lattice :=
  Lattice.ofField rows cols fun i _ => (0#32, shearJx rows i, 0#32)

/-! ### The cell -/

structure CellOut (dom : DomainConfig) where
  g0 : Signal dom (BitVec 32)
  g1 : Signal dom (BitVec 32)
  g2 : Signal dom (BitVec 32)
  g3 : Signal dom (BitVec 32)
  g4 : Signal dom (BitVec 32)
  g5 : Signal dom (BitVec 32)
  g6 : Signal dom (BitVec 32)
  g7 : Signal dom (BitVec 32)
  g8 : Signal dom (BitVec 32)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (CellOut dom) dom := ⟨⟩

/-- Signal-level Q7.24 multiply.  Mirrors `mulF`. -/
def mulFS {dom : DomainConfig} (a b : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  (sext32to64 a * sext32to64 b + (Signal.pure half : Signal dom (BitVec 64))).map
    (BitVec.extractLsb' 24 32 ·)

/-- One lattice site.  `f1`…`f8` are the populations arriving from the
    eight neighbours; the outputs are this site's nine post-collision
    populations, all registers (the cell is Moore).  While `load` is high
    the site is set to the equilibrium of (`rho0`, `jx0`, `jy0`). -/
@[hardware_module] def lbmCell {dom : DomainConfig}
    (f1 f2 f3 f4 f5 f6 f7 f8 : Signal dom (BitVec 32))
    (rho0 jx0 jy0 omega : Signal dom (BitVec 32)) (load : Signal dom Bool) : CellOut dom :=
  circuit do
    let r0 ← Signal.reg 0#32
    let r1 ← Signal.reg 0#32
    let r2 ← Signal.reg 0#32
    let r3 ← Signal.reg 0#32
    let r4 ← Signal.reg 0#32
    let r5 ← Signal.reg 0#32
    let r6 ← Signal.reg 0#32
    let r7 ← Signal.reg 0#32
    let r8 ← Signal.reg 0#32
    let f0 := (r0 : Signal dom (BitVec 32))
    -- moments of what arrived (or the initial condition)
    let rho := Signal.mux load rho0 (f0 + (f1 + f2 + f3 + f4 + f5 + f6 + f7 + f8))
    let jx := Signal.mux load jx0 (f1 - f3 + f5 - f6 - f7 + f8)
    let jy := Signal.mux load jy0 (f2 - f4 + f5 + f6 - f7 - f8)
    -- equilibrium
    let k9 := (Signal.pure c9 : Signal dom (BitVec 32))
    let k36 := (Signal.pure c36 : Signal dom (BitVec 32))
    let k6 := (Signal.pure c6 : Signal dom (BitVec 32))
    let k12 := (Signal.pure c12 : Signal dom (BitVec 32))
    let k4 := (Signal.pure c4 : Signal dom (BitVec 32))
    let xx := mulFS jx jx
    let yy := mulFS jy jy
    let xy4 := mulFS (mulFS jx jy) k4
    let r9 := mulFS rho k9
    let r36 := mulFS rho k36
    let sq := xx + yy
    let twoX := jx + jx
    let twoY := jy + jy
    let e1 := r9 + mulFS (xx + xx - yy + twoX) k6
    let e2 := r9 + mulFS (yy + yy - xx + twoY) k6
    let e3 := r9 + mulFS (xx + xx - yy - twoX) k6
    let e4 := r9 + mulFS (yy + yy - xx - twoY) k6
    let e5 := r36 + mulFS (sq + jx + jy) k12 + xy4
    let e6 := r36 + mulFS (sq - jx + jy) k12 - xy4
    let e7 := r36 + mulFS (sq - jx - jy) k12 + xy4
    let e8 := r36 + mulFS (sq + jx - jy) k12 - xy4
    -- relaxation (or, while loading, the equilibrium itself)
    let g1 := Signal.mux load e1 (f1 + mulFS omega (e1 - f1))
    let g2 := Signal.mux load e2 (f2 + mulFS omega (e2 - f2))
    let g3 := Signal.mux load e3 (f3 + mulFS omega (e3 - f3))
    let g4 := Signal.mux load e4 (f4 + mulFS omega (e4 - f4))
    let g5 := Signal.mux load e5 (f5 + mulFS omega (e5 - f5))
    let g6 := Signal.mux load e6 (f6 + mulFS omega (e6 - f6))
    let g7 := Signal.mux load e7 (f7 + mulFS omega (e7 - f7))
    let g8 := Signal.mux load e8 (f8 + mulFS omega (e8 - f8))
    -- restore the momentum and the mass exactly (`conserve`)
    let h1 := g1 + (jx - (g1 - g3 + g5 - g6 - g7 + g8))
    let h2 := g2 + (jy - (g2 - g4 + g5 + g6 - g7 - g8))
    r0 <~ rho - (h1 + h2 + g3 + g4 + g5 + g6 + g7 + g8)
    r1 <~ h1
    r2 <~ h2
    r3 <~ g3
    r4 <~ g4
    r5 <~ g5
    r6 <~ g6
    r7 <~ g7
    r8 <~ g8
    return ({ g0 := f0
              g1 := (r1 : Signal dom (BitVec 32)), g2 := (r2 : Signal dom (BitVec 32))
              g3 := (r3 : Signal dom (BitVec 32)), g4 := (r4 : Signal dom (BitVec 32))
              g5 := (r5 : Signal dom (BitVec 32)), g6 := (r6 : Signal dom (BitVec 32))
              g7 := (r7 : Signal dom (BitVec 32)), g8 := (r8 : Signal dom (BitVec 32)) } : CellOut dom)

/-! ### Lattices

Taylor–Green vortex on a periodic n × n lattice.  Inputs: the collision
frequency ω (Q7.24) and `load`; output: every population of every site
(see `Lattice.pack`).  Hold `load` high for one clock to set the initial
condition; from then on each clock is one time step. -/

/-- 4 × 4: 16 cells. -/
def tg4 {dom : DomainConfig} (omega : Signal dom (BitVec 32)) (load : Signal dom Bool) :
    Signal dom (BitVec 4608) :=
  torus_grid% 4 4
    (fields := g0 g1 g2 g3 g4 g5 g6 g7 g8) (width := 32)
    (cell i j nb => lbmCell nb.w.g1 nb.n.g2 nb.e.g3 nb.s.g4 nb.nw.g5 nb.ne.g6 nb.se.g7 nb.sw.g8
      (Signal.pure (tgRho 4 i j)) (Signal.pure (tgJx 4 i j)) (Signal.pure (tgJy 4 i j))
      omega load)

set_option maxRecDepth 100000 in
/-- 16 × 16: 256 cells. -/
def tg16 {dom : DomainConfig} (omega : Signal dom (BitVec 32)) (load : Signal dom Bool) :
    Signal dom (BitVec 73728) :=
  torus_grid% 16 16
    (fields := g0 g1 g2 g3 g4 g5 g6 g7 g8) (width := 32)
    (cell i j nb => lbmCell nb.w.g1 nb.n.g2 nb.e.g3 nb.s.g4 nb.nw.g5 nb.ne.g6 nb.se.g7 nb.sw.g8
      (Signal.pure (tgRho 16 i j)) (Signal.pure (tgJx 16 i j)) (Signal.pure (tgJy 16 i j))
      omega load)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- 32 × 32: 1024 cells — the largest lattice one GPU thread block holds.

    `noncomputable`: this lattice is for synthesis and for the C / GPU
    simulators.  Lean's own code generator overflows its stack on a
    function of this size (about 30 000 bindings), so `Signal.val` is not
    available for it; `tg16` is the lattice simulated inside Lean. -/
noncomputable def tg32 {dom : DomainConfig} (omega : Signal dom (BitVec 32)) (load : Signal dom Bool) :
    Signal dom (BitVec 294912) :=
  torus_grid% 32 32
    (fields := g0 g1 g2 g3 g4 g5 g6 g7 g8) (width := 32)
    (cell i j nb => lbmCell nb.w.g1 nb.n.g2 nb.e.g3 nb.s.g4 nb.nw.g5 nb.ne.g6 nb.se.g7 nb.sw.g8
      (Signal.pure (tgRho 32 i j)) (Signal.pure (tgJx 32 i j)) (Signal.pure (tgJy 32 i j))
      omega load)

end Sparkle.IP.Fluid.LBM

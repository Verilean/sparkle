import Sparkle.Analog.IR.Netlist

/-!
# Authoring DSL

Two interchangeable surfaces for assembling a `Circuit`, both lowering to the
same value:

* **Value-based** (canonical): `circuit fun a b => [ dev.between a b, … ]`. The
  `circuit` combinator allocates a fresh net for each binder via a small variadic
  typeclass, so it is arity-independent without any macro.
* **Monadic** (`CircuitM`, optional sugar for large flat netlists): allocate nets
  with `net`, add devices with `place`, then `runCircuit`.

Net `0` is `ground`; binders/`net` allocate from `1` up. This file also defines
the primitive electrical device set whose laws are single acausal equations.
-/

namespace Sparkle.Analog

/-- Differential-operator wrapper, so laws read `ddt v`. -/
def ddt (a : AExpr) : AExpr := .ddt a

/-- The ground net of any discipline (handle `0`); its potential is pinned to
zero, so it is never an MNA unknown. -/
def ground {d : Discipline} : Net d := ⟨Circuit.groundId⟩

/-- Build a two-terminal device from its acausal law. The discipline is inferred
from the result type's ascription (e.g. `: TwoPin .electrical`). -/
def twoPin {d : Discipline} (law : TwoPinLaw) : TwoPin d := ⟨law⟩

/-! ## Value-based assembly -/

/-- Net-allocation effect: a counter of the next free handle. -/
abbrev Alloc := StateM Nat

/-- Allocate the next fresh net. -/
def freshNet {d : Discipline} : Alloc (Net d) := fun s => (⟨s⟩, s + 1)

/-- Functions that, after being applied to freshly-allocated nets, yield a list
of placements. The base case is the placement list itself; each `Net d →`
argument allocates one net. This is what makes `circuit fun a b => …`
arity-independent. -/
class CircuitFn (α : Type) where
  collect : α → Alloc (List Placement)

instance : CircuitFn (List Placement) where
  collect pls := pure pls

instance {d : Discipline} {β : Type} [CircuitFn β] : CircuitFn (Net d → β) where
  collect f := do
    let n ← freshNet (d := d)
    CircuitFn.collect (f n)

/-- Assemble a circuit from a function of its nets. Each binder becomes a fresh
net (handles from `1`); ground is the predefined net `0`. -/
def circuit {α : Type} [CircuitFn α] (f : α) : Circuit :=
  let (pls, next) := (CircuitFn.collect f).run 1
  { netCount := next, placements := pls }

/-! ## Monadic assembly (optional sugar) -/

/-- Accumulator for the monadic builder. `placements` is built in reverse. -/
structure BuildState where
  nextNet : Nat := 1
  placements : List Placement := []

/-- A lawful `StateM` over a fresh-net supply and a device accumulator. It is
strictly additive sugar: `runCircuit` produces the same `Circuit` value the
combinator form would. -/
abbrev CircuitM := StateM BuildState

/-- Allocate a fresh net in the monadic builder. -/
def net {d : Discipline} : CircuitM (Net d) :=
  fun s => (⟨s.nextNet⟩, { s with nextNet := s.nextNet + 1 })

/-- Place a device between two nets in the monadic builder. -/
def place {d : Discipline} (dev : TwoPin d) (p n : Net d) : CircuitM Unit :=
  modify fun s => { s with placements := dev.between p n :: s.placements }

/-- Run a monadic builder to the canonical `Circuit` value. -/
def runCircuit (m : CircuitM Unit) : Circuit :=
  let s := (m.run {}).2
  { netCount := s.nextNet, placements := s.placements.reverse }

/-! ## Primitive electrical devices

Each is one acausal equation; together they exercise the resistive, reactive,
source and nonlinear cases the solver must handle. -/

/-- Resistor: `v = R·i`. -/
def resistor (R : Float) : TwoPin .electrical := twoPin fun v i => [v ≡ R * i]

/-- Capacitor: `i = C·dv/dt`. -/
def capacitor (C : Float) : TwoPin .electrical := twoPin fun v i => [i ≡ C * ddt v]

/-- Inductor: `v = L·di/dt` (naturally acausal — current-controlled). -/
def inductor (L : Float) : TwoPin .electrical := twoPin fun v i => [v ≡ L * ddt i]

/-- Independent voltage source with a time-dependent waveform: `v = e(time)`.
The branch current is left free (an MNA unknown). -/
def vsource (e : AExpr → AExpr) : TwoPin .electrical := twoPin fun v _i => [v ≡ e .time]

/-- Constant (DC) voltage source: `v = V`. -/
def vsourceDC (V : Float) : TwoPin .electrical := twoPin fun v _i => [v ≡ (V : AExpr)]

/-- Independent current source: `i = I`. -/
def isourceDC (I : Float) : TwoPin .electrical := twoPin fun _v i => [i ≡ (I : AExpr)]

/-- Shockley diode: `i = Is·(exp(v/Vt) − 1)`. -/
def diode (Is Vt : Float) : TwoPin .electrical := twoPin fun v i => [i ≡ Is * (exp (v / Vt) - 1)]

end Sparkle.Analog

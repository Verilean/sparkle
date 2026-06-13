import Sparkle.Analog.IR.Expr

/-!
# Netlist IR — disciplines, nets, device laws, circuits

The structural layer. A device is an *acausal law* relating its branch voltage
and branch current (Functional Hybrid Modelling style); a circuit is a list of
such devices placed between nets. No causality is fixed here — the law is a
relation, and the solver decides what is input and what is output.

Nets are discipline-typed at the Lean type level (`Net .electrical`), so a
two-terminal device's `between` only connects nets of one discipline; mixing
disciplines is a type error. Net *identities* are erased to `Nat` handles at the
value level (`Placement`), which is what the MNA stamper consumes.

Only the electrical discipline is wired through the solver for now; `thermal`
exists to keep the discipline machinery honestly polymorphic.
-/

namespace Sparkle.Analog

/-- A physical discipline. Each carries a *potential* nature (the across
quantity, e.g. voltage) and a *flow* nature (the through quantity, e.g. current);
for the electrical discipline these are volts and amperes. -/
inductive Discipline where
  | electrical
  | thermal
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A net (circuit node) of a given discipline. The discipline index makes
connecting mismatched disciplines a type error; `id` is the value-level handle. -/
structure Net (d : Discipline) where
  id : Nat
  deriving Repr, BEq

/-- The branch-voltage / branch-current law of a two-terminal device: given the
branch voltage `v` (across the device) and its branch current `i` (through it),
both as expressions, return the equations relating them. One law shape uniformly
covers resistor (`v ≡ R*i`), capacitor (`i ≡ C*ddt v`), inductor (`v ≡ L*ddt i`),
source (`v ≡ e`) and diode (`i ≡ Is*(exp (v/Vt) - 1)`). -/
abbrev TwoPinLaw := AExpr → AExpr → List Equation

/-- A two-terminal device of a given discipline: its acausal law plus, for an
independent AC source, the small-signal drive amplitude. The discipline index
propagates to the nets it connects (via `between`), which is what lets the
value-based builder infer net disciplines and rejects cross-discipline wiring. -/
structure TwoPin (d : Discipline) where
  law : TwoPinLaw
  /-- Small-signal AC drive amplitude (volts), if this device is an independent
  AC source; `none` for everything else. The transient/DC paths ignore it; AC
  analysis puts it on the right-hand side of the admittance system. -/
  acAmp : Option Float := none

/-- A device placed between two nets, with discipline erased to net handles. The
MNA stamper gives the branch its own current unknown, sets `v := netV pos -
netV neg`, emits the law's equations, and adds the branch current to the KCL sum
at `pos` and `neg`. -/
structure Placement where
  pos : Nat
  neg : Nat
  law : TwoPinLaw
  acAmp : Option Float := none
  deriving Inhabited

/-- Connect a two-terminal device between two nets of the same discipline. The
shared discipline index `d` is what rejects cross-discipline wiring at compile
time. -/
def TwoPin.between {d : Discipline} (dev : TwoPin d) (p n : Net d) : Placement :=
  { pos := p.id, neg := n.id, law := dev.law, acAmp := dev.acAmp }

/-- A controlled (dependent) source — the gain element a `TwoPin` law cannot
express, because it *senses* a quantity at one port and forces a response at
another. Four linear flavours plus the ideal op-amp (nullor):

* `vcvs` — voltage-controlled voltage source, `V(out) = μ·V(in)`;
* `vccs` — transconductance, `I(out) = gm·V(in)`;
* `ccvs` — transresistance, `V(out) = rm·I(ctrl)`;
* `cccs` — current gain, `I(out) = β·I(ctrl)`;
* `opamp` — ideal op-amp: the nullor constraint `V(inP) = V(inN)` with a free
  output current (its input draws none). The finite-gain/dominant-pole op-amp is
  built from `vccs` + R + C + buffer instead. -/
inductive CtrlKind
  | vcvs | vccs | ccvs | cccs | opamp
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A controlled source over net handles. `outP`/`outN` are the output port;
`inP`/`inN` the voltage-sense port (for V-controlled kinds and the op-amp);
`ctrlBranch` the current-sense branch (for I-controlled kinds); `gain` is μ, gm,
rm or β (unused for `opamp`). -/
structure CtrlSource where
  kind : CtrlKind
  outP : Nat
  outN : Nat
  inP : Nat := 0
  inN : Nat := 0
  ctrlBranch : Option Nat := none
  gain : Float := 0.0
  deriving Repr, Inhabited

/-- Whether this controlled source introduces its own output-branch current
unknown: the voltage-output kinds (and the op-amp's free output current) do; the
current-output kinds (`vccs`, `cccs`) inject directly into KCL and do not. -/
def CtrlSource.needsBranch (cs : CtrlSource) : Bool :=
  cs.kind == .vcvs || cs.kind == .ccvs || cs.kind == .opamp

/-- An assembled circuit: how many nets were allocated, the two-terminal devices,
and the controlled sources placed between them. Net `0` is ground (its potential
is pinned to zero), so it is never an MNA unknown. -/
structure Circuit where
  netCount : Nat
  placements : List Placement
  controlledSources : List CtrlSource := []
  deriving Inhabited

namespace Circuit

/-- The ground net handle. -/
def groundId : Nat := 0

/-- How many controlled sources carry their own branch-current unknown. -/
def ctrlBranchCount (c : Circuit) : Nat :=
  c.controlledSources.foldl (fun n cs => if cs.needsBranch then n + 1 else n) 0

/-- Branch count = one per two-terminal device, plus one per controlled source
that carries an output-branch current. -/
def branchCount (c : Circuit) : Nat := c.placements.length + c.ctrlBranchCount

end Circuit

end Sparkle.Analog

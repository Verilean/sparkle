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

/-- A two-terminal device of a given discipline: just its acausal law. The
discipline index propagates to the nets it connects (via `between`), which is
what lets the value-based builder infer net disciplines and rejects
cross-discipline wiring. -/
structure TwoPin (d : Discipline) where
  law : TwoPinLaw

/-- A device placed between two nets, with discipline erased to net handles. The
MNA stamper gives the branch its own current unknown, sets `v := netV pos -
netV neg`, emits the law's equations, and adds the branch current to the KCL sum
at `pos` and `neg`. -/
structure Placement where
  pos : Nat
  neg : Nat
  law : TwoPinLaw
  deriving Inhabited

/-- Connect a two-terminal device between two nets of the same discipline. The
shared discipline index `d` is what rejects cross-discipline wiring at compile
time. -/
def TwoPin.between {d : Discipline} (dev : TwoPin d) (p n : Net d) : Placement :=
  { pos := p.id, neg := n.id, law := dev.law }

/-- An assembled circuit: how many nets were allocated and the devices placed
between them. Net `0` is ground (its potential is pinned to zero), so it is never
an MNA unknown. -/
structure Circuit where
  netCount : Nat
  placements : List Placement
  deriving Inhabited

namespace Circuit

/-- The ground net handle. -/
def groundId : Nat := 0

/-- Branch count = number of placed devices (each contributes one branch). -/
def branchCount (c : Circuit) : Nat := c.placements.length

end Circuit

end Sparkle.Analog

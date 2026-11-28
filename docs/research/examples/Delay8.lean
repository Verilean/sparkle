-- The smallest verified-synthesis example: an 8-bit register.
-- Run from the repository root:
--   lake build Tools.VedU1Entry
--   lake env lean docs/research/examples/Delay8.lean
import Tools.VedU1Entry

open Sparkle.Core.Domain Sparkle.Core.Signal

def delay8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 x

-- Synthesise delay8 and, in the same command, build and kernel-check
-- a theorem that the returned module computes delay8.
#ved_u1 delay8

-- The theorem exists as a constant; ask Lean which axioms it uses.
#print axioms delay8.ved_u1

-- What the theorem states: its type. The statement names your own `delay8`,
-- the returned module `delay8.ved_mod` and the port table `delay8.ved_contract`.
-- docs/research/ReadingTheTheorem.md reads it part by part.
/-- info: delay8.ved_u1 : Tools.VedU1Contract.U1Stmt delay8.ved_contract delay8.ved_mod delay8 -/
#guard_msgs in
#check delay8.ved_u1

-- The statement is five parts joined by `∧`.
/--
info: def Tools.VedU1Contract.U1Stmt : (c : Contract) → Sparkle.IR.AST.Module → c.table.Ty → Prop :=
fun c m f => CorrStmt c ∧ ShapeStmt c m ∧ WidthStmt c m ∧ OrderStmt m ∧ OutputsStmt c m f
-/
#guard_msgs in
open Tools.VedU1Contract in
#print U1Stmt

-- A circuit whose result is a pair is refused by this entry: the command
-- reports an error and makes no claim. `#guard_msgs (error)` pins that
-- refusal as the expected result, so the file as a whole exits 0; if the
-- refusal text changes, or the circuit is accepted, the file fails.
def pair8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8 × BitVec 8) :=
  (fun v => (v, v)) <$> Signal.register 0#8 x

/--
error: VED U1 REFUSED pair8 [multi-output]: 2 output projections in one `Signal` (the synthesizer packs it into one port `out`); refused
-/
#guard_msgs (error) in
#ved_u1 pair8

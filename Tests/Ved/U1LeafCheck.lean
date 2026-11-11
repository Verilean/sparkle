import Tests.Ved.U1EqLutCheck
import IP.Bus.PCIe
import IP.Net.TCP
import IP.Net.IPv4

/-!
# `#ved_u1` on register-free leaf declarations of the existing IP

* `Sparkle.IP.Bus.PCIe.tlpHeaderByte` and `Sparkle.IP.Net.TCP.tcpHeaderByte` are the REAL
  declarations (imported, no copy).  Each is checked independently of the entry: the stored
  type of `<decl>.ved_u1` is, as an `Expr` compared with `==`, the hand-rebuilt
  `U1Stmt <decl>.ved_contract <decl>.ved_mod (@<decl> defaultDomain)`, and its axioms are
  within `propext`, `Classical.choice`, `Quot.sound` (std3).
* `leafOnes` is a faithful LOCAL COPY of one `IPv4.onesAdd16Sig` stage (it calls the real
  `onesAdd16Sig` on two inputs); it pins the signal-concatenation and carry slice path that
  the real `TCP.tcpHeaderChecksumSig` (14 chained stages) needs.
* Controls: a mutated module of the same declaration (a constant of the byte value, a
  selector constant, the carry constant) is refused at `[proof]` and leaves no `ved_*`.
* `leafOnes2` (two chained stages) and the real `TCP.tcpHeaderChecksumSig` are PINNED AS
  REFUSED at `[proof]`: this unit does not prove them (see the unit report).
-/

namespace Tests.Ved.U1LeafCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tests.Ved.U1EqLutCheck
open Sparkle.IP.Net

@[hardware_module] def leafOnes {dom : DomainConfig} (a b : Signal dom (BitVec 16)) :
    Signal dom (BitVec 16) :=
  IPv4.onesAdd16Sig a b

@[hardware_module] def leafOnes2 {dom : DomainConfig} (a b c : Signal dom (BitVec 16)) :
    Signal dom (BitVec 16) :=
  let s := IPv4.onesAdd16Sig a b
  IPv4.onesAdd16Sig s c

#guard_msgs (drop info) in
#ved_u1 Sparkle.IP.Bus.PCIe.tlpHeaderByte
#guard_msgs (drop info) in
#ved_u1 Sparkle.IP.Net.TCP.tcpHeaderByte
#guard_msgs (drop info) in
#ved_u1 leafOnes

/-- independent of the entry: exact type, std3 -/
def checkTy (decl : Name) : CommandElabM Unit := liftTermElabM do
  let nm := Names.ofBase decl
  let thm := decl ++ `ved_u1
  let stmt := mkApp (Lean.mkConst decl) (Lean.mkConst ``defaultDomain)
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not U1Stmt c m (@{decl} defaultDomain)"
  let r ← Tools.VedStrictAudit.strictAudit thm
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) && r.axioms.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  logInfo m!"OK {decl}: exact type, axioms {ax.size}"

/-- info: OK Sparkle.IP.Bus.PCIe.tlpHeaderByte: exact type, axioms 3 -/
#guard_msgs in
run_cmd checkTy ``Sparkle.IP.Bus.PCIe.tlpHeaderByte
/-- info: OK Sparkle.IP.Net.TCP.tcpHeaderByte: exact type, axioms 3 -/
#guard_msgs in
run_cmd checkTy ``Sparkle.IP.Net.TCP.tcpHeaderByte
/-- info: OK Tests.Ved.U1LeafCheck.leafOnes: exact type, axioms 3 -/
#guard_msgs in
run_cmd checkTy ``leafOnes

/-! ## Controls -/

-- the 4th header byte (`b3`, the constant 1) changed
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMut `ctlPcieByte ``Sparkle.IP.Bus.PCIe.tlpHeaderByte (bumpConst 8 2) <|
    [(5, "_gen_b3 := const 1:8", "_gen_b3 := const 2:8")]

-- a selector constant (`p3`) changed
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMut `ctlPcieSel ``Sparkle.IP.Bus.PCIe.tlpHeaderByte (bumpConst 4 2) <|
    [(15, "_gen_p3 := const 3:4", "_gen_p3 := const 4:4")]

-- the same on the 20-way TCP mux (the heartbeat and recursion budgets scale with the module)
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMut `ctlTcpSel ``Sparkle.IP.Net.TCP.tcpHeaderByte (bumpConst 5 3) <|
    [(23, "_gen_p4 := const 4:5", "_gen_p4 := const 5:5")]

-- the carry's zero-extension constant, and the 17-bit zero-prepend, changed
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMut `ctlOnesCarry ``leafOnes (bumpConst 15 0) <|
    [(6, "_tmp_concat_hi_1 := const 0:15", "_tmp_concat_hi_1 := const 1:15")]

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMut `ctlOnesPrepend ``leafOnes (bumpConst 1 0) <|
    [(0, "_tmp_concat_hi_0 := const 0:1", "_tmp_concat_hi_0 := const 1:1")]

-- a module of another declaration against the byte selector's statement
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do ctl `ctlPcieOther ``Sparkle.IP.Bus.PCIe.tlpHeaderByte (← liftTermElabM (modOf ``leafOnes))

/-! ## Pinned refusals (not proved in this unit) -/

def refusedAt (stage : String) (decl : Name) : CommandElabM Unit :=
  expectRefused stage decl do discard <| vedU1EntryS decl

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd refusedAt "proof" ``leafOnes2

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd refusedAt "proof" ``Sparkle.IP.Net.TCP.tcpHeaderChecksumSig

end Tests.Ved.U1LeafCheck

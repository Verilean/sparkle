import Tools.VedU2HierRegEntry
import Tools.VedU2HierRecEntry
import Tests.Ved.ComposeCheckUtil
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# The port series of the nested entry: the per-instance fact obtained ONCE (CANDIDATE; observed, single runs)

NOT a ledger row.  A parent with a register over a struct middle module with 2, 3, 4 and 10 output ports (one register, an instance of
a sequential leaf), through `#ved_u2_hier` with `ved.compose.multiOut` and `ved.compose.nested` ON.  The instance fact of the middle
module is obtained ONCE per instance (`hfact`: every output port at the cycle), each port's branch only selects its port
(`shareFact` of `scriptTextR`).  Measurement (env `VED_HIER_STATS=1`: script characters, elaboration, kernel `addDecl`; env
`VED_NESTED_NOONCE=1`: the per-port form of nested4, same build): see the unit report.
-/

namespace Tests.Ved.RecPorts

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil
open Tools.VedU1HierEntry Tools.VedU2HierRec

@[hardware_module] def leafs (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let r ← Signal.reg 0#4
    r <~ r + x
    return r

#verify_elab_deep leafs

structure P2 (dom : DomainConfig) where
  s0 : Signal dom (BitVec 4)
  s1 : Signal dom (BitVec 4)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (P2 dom) dom := ⟨⟩
@[hardware_module] def mid2 (x y : Signal defaultDomain (BitVec 4)) : P2 defaultDomain :=
  circuit do
    let r ← Signal.reg 0#4
    let c := leafs x
    r <~ r + c + y
    return ({ s0 := r, s1 := c } : P2 defaultDomain)
def top2 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := mid2 accS b
    acc <~ (accS + (c.s0 - c.s1) : Signal defaultDomain (BitVec 4))
    return accS

structure P3 (dom : DomainConfig) where
  s0 : Signal dom (BitVec 4)
  s1 : Signal dom (BitVec 4)
  s2 : Signal dom (BitVec 4)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (P3 dom) dom := ⟨⟩
@[hardware_module] def mid3 (x y : Signal defaultDomain (BitVec 4)) : P3 defaultDomain :=
  circuit do
    let r ← Signal.reg 0#4
    let c := leafs x
    r <~ r + c + y
    return ({ s0 := r, s1 := c, s2 := r + c } : P3 defaultDomain)
def top3 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := mid3 accS b
    acc <~ (accS + (c.s0 - c.s1) + c.s2 : Signal defaultDomain (BitVec 4))
    return accS

structure P4 (dom : DomainConfig) where
  s0 : Signal dom (BitVec 4)
  s1 : Signal dom (BitVec 4)
  s2 : Signal dom (BitVec 4)
  s3 : Signal dom (BitVec 4)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (P4 dom) dom := ⟨⟩
@[hardware_module] def mid4 (x y : Signal defaultDomain (BitVec 4)) : P4 defaultDomain :=
  circuit do
    let r ← Signal.reg 0#4
    let c := leafs x
    r <~ r + c + y
    return ({ s0 := r, s1 := c, s2 := r + c, s3 := r - y } : P4 defaultDomain)
def top4 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := mid4 accS b
    acc <~ (accS + (c.s0 - c.s1) + c.s2 + c.s3 : Signal defaultDomain (BitVec 4))
    return accS

structure P10 (dom : DomainConfig) where
  s0 : Signal dom (BitVec 4)
  s1 : Signal dom (BitVec 4)
  s2 : Signal dom (BitVec 4)
  s3 : Signal dom (BitVec 4)
  s4 : Signal dom (BitVec 4)
  s5 : Signal dom (BitVec 4)
  s6 : Signal dom (BitVec 4)
  s7 : Signal dom (BitVec 4)
  s8 : Signal dom (BitVec 4)
  s9 : Signal dom (BitVec 4)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (P10 dom) dom := ⟨⟩
@[hardware_module] def mid10 (x y : Signal defaultDomain (BitVec 4)) : P10 defaultDomain :=
  circuit do
    let r ← Signal.reg 0#4
    let c := leafs x
    r <~ r + c + y
    return ({ s0 := r, s1 := c, s2 := r + c, s3 := r - y, s4 := c + y, s5 := r + y, s6 := c - y, s7 := r + c + y, s8 := r - c, s9 := y - r } : P10 defaultDomain)
def top10 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := mid10 accS b
    acc <~ (accS + (c.s0 - c.s1) + c.s2 + c.s3 + c.s4 + c.s5 + c.s6 + c.s7 + c.s8 + c.s9 : Signal defaultDomain (BitVec 4))
    return accS

def expectedR (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``U2HRStmtR) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

/-- the accepted theorem, read independently of the entry (type, artifact, std3, kernel, the middle module's theorem occurs) -/
def acceptedP (decl midThm : Name) : CommandElabM Unit := do
  let (m, d) ← synthOf decl
  let (_, nDom) ← liftTermElabM (specialiseDomain decl)
  let nm := HNames.ofBase decl
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? nm.thm | throwError "{nm.thm} is not a theorem"
    unless ti.type == expectedR decl nDom do throwError "{nm.thm}: type is not U2HRStmtR c m d decl"
    let some ci := (← getEnv).find? nm.mod | throwError "{nm.mod} missing"
    unless ci.value! == toExpr m do throwError "{nm.mod} is not the declaration's own module"
    let some di := (← getEnv).find? nm.design | throwError "{nm.design} missing"
    unless di.value! == toExpr d do throwError "{nm.design} is not the declaration's own design"
    std3Only nm.thm
    let axs ← collectAxioms nm.thm
    if axs.contains ``sorryAx then throwError "{nm.thm}: sorryAx"
    unless ti.value.getUsedConstants.contains midThm do throwError "{nm.thm}: the middle module's theorem {midThm} does not occur"
    discard <| Tools.VedStrictAudit.strictAudit nm.thm
    logInfo m!"ACCEPTED {decl}: U2HRStmtR type ==, same artifact, std3, kernel, {midThm} occurs"

set_option ved.compose.multiOut true in
set_option ved.compose.nested true in
#ved_u2_hier top2
#eval acceptedP ``top2 `Tests.Ved.RecPorts.mid2.ved_u2r

set_option ved.compose.multiOut true in
set_option ved.compose.nested true in
#ved_u2_hier top3
#eval acceptedP ``top3 `Tests.Ved.RecPorts.mid3.ved_u2r

set_option ved.compose.multiOut true in
set_option ved.compose.nested true in
#ved_u2_hier top4
#eval acceptedP ``top4 `Tests.Ved.RecPorts.mid4.ved_u2r

set_option ved.compose.multiOut true in
set_option ved.compose.nested true in
#ved_u2_hier top10
#eval acceptedP ``top10 `Tests.Ved.RecPorts.mid10.ved_u2r

end Tests.Ved.RecPorts

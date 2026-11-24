import Tools.VedU2HierRegEntry
import Tools.VedComposeConnectGen
import Tests.Ved.ComposeCheckUtil
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Persistent regression of the dead trailing register slot, through the real entry `#ved_u2_hier`

(`Tools/VedU2HierRegEntry.lean`, option `ved.compose.multiCircuit` with `ved.compose.step` and `ved.compose.connect`.)  The
open parent's deep circuit keeps every register of the `circuit do` block; the synthesised module drops a register nothing live reads.
The entry accepts the extra TRAILING slots when `slotUnused` (an ENTRY check, evaluated by `Lean.Kernel.whnf`) holds; the generated proof
rests on `RegsOkNFp` / `outSpecNF` with `reg_connectN` / `out_connectN`, not on the prefix lemmas.  These are toys (width-4 registers,
one child `mkA`), not real-IP rows.

* `deadTx` (circuits `actC` (live register, child call) then `cntTop` whose counter register is read only by the unexported field `n`; the exported `b` is its input): accepted, `VED U2 HIER OK`; afterwards the stored
  type is `==` `U2HRStmt`, the stored MODULE is the declaration's own synthesis (the design value is not compared here), the artifact is the one the entry reported, std3, the
  child theorem occurs, and no old fallback (reg_connect/out_connect sites only).
* `deadLeadTx` (the dead counter circuit `cntG` FIRST, then the last circuit `actTop` with the live register read by the output and its
  own next state; both width 4): the synthesis drops the dead register, so the live register sits in the extra slot range of the deep
  circuit (2 slots against 1 register).  Refused at `[deep]` naming `slotUnused`; the state is restored and no constant of the
  declaration is left.  (The brief's "extra register read by a live register or by the output" is not constructible as such through the
  synthesis: a register read by a kept cone is kept.  The live-slot refusal through the real entry is this order shape: the dead block is
  not trailing.)
* `deadOffTx` (the `deadTx` shape) with `ved.compose.multiCircuit` off: the old refusal text, unchanged.
-/

namespace Tests.Ved.ComposeDeadSlotCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
  Tools.VedU2HierEntry Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil

@[hardware_module]
def mkA (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  (x + (Signal.pure 3#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))

structure CB (dom : DomainConfig) where
  b : Signal dom (BitVec 4)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (CB dom) dom := ⟨⟩
structure DeadOut (dom : DomainConfig) where
  b : Signal dom (BitVec 4)
  n : Signal dom (BitVec 4)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (DeadOut dom) dom := ⟨⟩

/-- the live circuit: a register with a child call in its next state -/
def actC (go : Signal defaultDomain Bool) : CB defaultDomain :=
  circuit do
    let r ← Signal.reg 0#4
    let o := (r : Signal defaultDomain (BitVec 4))
    r <~ Signal.mux go (mkA o) o
    return ({ b := o } : CB defaultDomain)

/-- the last circuit: its counter register is read only by the field `n`, which nobody exports; the field `b` is the input (the shape
of hftStrategy: the exported `outByte` comes from outside the loop, `cntR` is read by an unexported field) -/
def cntTop (x : Signal defaultDomain (BitVec 4)) : DeadOut defaultDomain :=
  circuit do
    let r ← Signal.reg 0#4
    let o := (r : Signal defaultDomain (BitVec 4))
    r <~ (o + x : Signal defaultDomain (BitVec 4))
    return ({ b := x, n := o } : DeadOut defaultDomain)

/-- the live circuit read by `cntTop`: the dead register is the TRAILING slot of the fused deep circuit -/
def deadP (go : Signal defaultDomain Bool) : DeadOut defaultDomain :=
  cntTop (actC go).b

def deadTx (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) := (deadP go).b

/-- the same, for the option-off control -/
def deadOffTx (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) := (deadP go).b

/-- a counter circuit (live only through the unexported field below) -/
def cntG (go : Signal defaultDomain Bool) : CB defaultDomain :=
  circuit do
    let r ← Signal.reg 0#4
    let o := (r : Signal defaultDomain (BitVec 4))
    r <~ Signal.mux go (o + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4)) o
    return ({ b := o } : CB defaultDomain)

/-- the last circuit: the live register `r`; the field `n` carries the dead circuit's output, nobody exports it -/
def actTop (x : Signal defaultDomain (BitVec 4)) (go : Signal defaultDomain Bool) : DeadOut defaultDomain :=
  circuit do
    let r ← Signal.reg 0#4
    let o := (r : Signal defaultDomain (BitVec 4))
    r <~ Signal.mux go (mkA o) o
    return ({ b := o, n := x } : DeadOut defaultDomain)

/-- the dead circuit comes FIRST: the live register follows it, so it sits in the extra slot range -/
def deadLeadP (go : Signal defaultDomain Bool) : DeadOut defaultDomain :=
  actTop (cntG go).b go

def deadLeadTx (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) := (deadLeadP go).b

/-- How many distinct (maximal) application sites of the constant `c` the term has (as in `ComposeConnectCheck`). -/
def countApps (e : Lean.Expr) (c : Name) : Nat := Id.run do
  let mut seen : Std.HashSet Lean.Expr := {}
  let mut todo : Array Lean.Expr := #[e]
  let mut n := 0
  while !todo.isEmpty do
    let x := todo.back!
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.insert x
    match x with
    | .app f a =>
      if x.getAppFn.isConstOf c then
        n := n + 1
        for y in x.getAppArgs do todo := todo.push y
      else todo := todo.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
    | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return n

/-- the accepted toy through `#ved_u2_hier` itself (the OK message carries timings, so it is captured, not pinned), then the
independent checks. -/
def checkDead (decl : Name) (kid : Name) : CommandElabM Unit := do
  let nMsg0 := (← get).messages.toList.length
  elabCommand (← `(#ved_u2_hier $(mkIdent decl)))
  let msgs := (← get).messages.toList.drop nMsg0
  let txt ← msgs.mapM fun msg => msg.data.toString
  let okLine := txt.filter fun s => s.startsWith s!"VED U2 HIER OK {decl}.ved_u1"
  modify fun s => { s with messages := (s.messages.toList.take nMsg0).foldl (fun l msg => l.add msg) {} }
  unless okLine.length == 1 && msgs.all (·.severity != .error) do throwError "{decl}: no single `VED U2 HIER OK` line / error: {txt.map (·.take 300)}"
  let conn := txt.filter fun s => (s.splitOn "VED COMPOSE CONNECT").length > 1
  let thm := (HNames.ofBase decl).thm
  let (m2, _) ← synthOf decl
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type == expectedOf decl 0 do throwError "{thm}: type is not U2HRStmt c m d decl"
    let nm := HNames.ofBase decl
    let some ci := (← getEnv).find? nm.mod | throwError "{nm.mod} missing"
    unless ci.value! == toExpr m2 do throwError "{nm.mod} is not the declaration's own module"
    unless (m2.body.filterMap (fun s => match s with | .register n .. => some n | _ => none)).length == 1 do
      throwError "{decl}: expected 1 synthesised register (the dead one dropped)"
    -- the dead-slot path was taken: the open parent's deep circuit has 2 register slots, the synthesised module 1
    let some dci := (← getEnv).find? (decl ++ Name.mkSimple s!"ved_open_Tests_Ved_ComposeDeadSlotCheck_{decl.getString!}_b_deep")
      | throwError "{decl}: the deep circuit constant is missing"
    unless (← ppExpr dci.type).pretty == "Cdo [4, 4] [1, 4] 4" do throwError "{decl}: deep circuit type {dci.type}"
    std3Only thm
    unless ti.value.getUsedConstants.contains kid do throwError "{thm}: the child theorem {kid} does not occur"
    let nr := countApps ti.value ``Tools.VedComposeConnect.reg_connect + countApps ti.value ``Tools.VedComposeConnect.reg_connectN
    let no := countApps ti.value ``Tools.VedComposeConnect.out_connect + countApps ti.value ``Tools.VedComposeConnect.out_connectN
    unless nr == 1 && no == 1 && conn.length == 2 do
      throwError "{decl}: reg_connect sites {nr}, out_connect sites {no}, log lines {conn.length} (expected 1, 1, 2)"
    logInfo m!"dead slot entry OK: accepted by #ved_u2_hier, type ==, std3, child theorem, 1 reg_connect + 1 out_connect, no fallback"

/-- info: dead slot entry OK: accepted by #ved_u2_hier, type ==, std3, child theorem, 1 reg_connect + 1 out_connect, no fallback -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option sparkle.deepExportState true in
set_option ved.compose.multiCircuit true in
run_cmd checkDead ``deadTx `Tests.Ved.ComposeDeadSlotCheck.deadTx.ved_child.Tests.Ved.ComposeDeadSlotCheck.mkA.ved_u1

/-- error: VED U1 REFUSED Tests.Ved.ComposeDeadSlotCheck.deadLeadTx [deep]: the parent has 1 registers, the open parent's circuit has 2; the extra slot(s) are read by the next-state cone of a parent register or by the output (slotUnused = false): not a dead register -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option sparkle.deepExportState true in
set_option ved.compose.multiCircuit true in
#ved_u2_hier deadLeadTx

/-- nothing of the declaration is left after a refusal: no constant `deadLeadTx.*` (the contract, module, design, deep theorems) -/
def noneLeft (decl : Name) : CommandElabM Unit := do
  let left := (← getEnv).constants.map₂.toList.filter (fun (n, _) => decl.isPrefixOf n && n != decl) |>.map (·.1)
  unless left.isEmpty do throwError "constants of {decl} left after the refusal: {left}"
  logInfo m!"{decl}: no constant left"

/-- info: Tests.Ved.ComposeDeadSlotCheck.deadLeadTx: no constant left -/
#guard_msgs in
run_cmd noneLeft ``deadLeadTx

/-- error: VED U1 REFUSED Tests.Ved.ComposeDeadSlotCheck.deadOffTx [open]: no call of a child in the circuit body -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option sparkle.deepExportState true in
#ved_u2_hier deadOffTx

/-- info: Tests.Ved.ComposeDeadSlotCheck.deadOffTx: no constant left -/
#guard_msgs in
run_cmd noneLeft ``deadOffTx

end Tests.Ved.ComposeDeadSlotCheck

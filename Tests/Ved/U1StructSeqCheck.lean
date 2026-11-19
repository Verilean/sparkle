import Tools.VedU1Entry
import Tools.VedU1StructOut

/-!
# Checks for structure results with registers (`#ved_u1` on a `Signal.loop` body)

A result that is a structure of `Signal defaultDomain _` fields, built from a `Signal.loop` (a `circuit do`
block), keeps ONE output port per field; the standard entry (`#ved_u1`) reads it as the tuple of its fields
(`Tools/VedU1StructSeq.lean`: `bundleTree`) and proves, for the contract with the clock/reset names and the
registers' initial values, one loop invariant and one equality for EVERY port against the original declaration's
own projections (not one packed port).

Positives: the registered theorem has EXACTLY the type `U1Stmt <ved_contract> <ved_mod> (fun xs => bundle2 …)`
written out by hand here; the contract (module name, clock/reset, table, port names, wires, register names and
initial values) is the hand-written one (the initial values are literals in this file); `ved_mod` is the module the
entry returns; the module's ports are the fields' names in order; standard three axioms.
Controls (refused at the stage named; no `ved_*` constant the checker registered is left): the module of a
declaration with two fields swapped, a register update swapped, a wrong initial value (in the declaration's
module and in the returned module itself), one output altered, a register update altered (a register read through
another output), the statement with exchanged projections, a body with plain (non-loop) registers.
-/

namespace Tests.Ved.U1StructSeqCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry

/-! ## Declarations (a loop of registers, result a structure) -/

structure S1 (dom : DomainConfig) where
  cnt : Signal dom (BitVec 8)
  sum : Signal dom (BitVec 8)

/-- ONE register, two fields -/
def ssOne (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) : S1 defaultDomain :=
  let st := Signal.loop fun state =>
    let c := projN! state 1 0
    bundleAll! [Signal.register 0#8 (Signal.mux en (c + d) c)]
  { cnt := projN! st 1 0, sum := (projN! st 1 0) + d }

structure S2 (dom : DomainConfig) where
  cnt : Signal dom (BitVec 8)
  hit : Signal dom Bool

/-- two registers (8 bits, 1 bit), two fields -/
def ssTwo (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) : S2 defaultDomain :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    bundleAll! [Signal.register 0#8 (Signal.mux en (c + d) c),
                Signal.register false (Signal.mux (c === 255#8) (Signal.pure true) f)]
  { cnt := projN! st 2 0, hit := projN! st 2 1 }

/-- the same with a non-zero initial value of the counter -/
def ssTwoInit (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) : S2 defaultDomain :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    bundleAll! [Signal.register 1#8 (Signal.mux en (c + d) c),
                Signal.register false (Signal.mux (c === 255#8) (Signal.pure true) f)]
  { cnt := projN! st 2 0, hit := projN! st 2 1 }

/-- the flag's register update altered (`254`) -/
def ssTwoFlag (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) : S2 defaultDomain :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    bundleAll! [Signal.register 0#8 (Signal.mux en (c + d) c),
                Signal.register false (Signal.mux (c === 254#8) (Signal.pure true) f)]
  { cnt := projN! st 2 0, hit := projN! st 2 1 }

/-- the counter's register update altered (`c - d`) -/
def ssTwoUpd (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) : S2 defaultDomain :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    bundleAll! [Signal.register 0#8 (Signal.mux en (c - d) c),
                Signal.register false (Signal.mux (c === 255#8) (Signal.pure true) f)]
  { cnt := projN! st 2 0, hit := projN! st 2 1 }

structure S3 (dom : DomainConfig) where
  acc : Signal dom (BitVec 8)
  dif : Signal dom (BitVec 8)
  top : Signal dom Bool

/-- two registers of the same width, THREE outputs (two registers and a combinational one) -/
def ssThree (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) : S3 defaultDomain :=
  let st := Signal.loop fun state =>
    let a := projN! state 2 0
    let b := projN! state 2 1
    bundleAll! [Signal.register 0#8 (Signal.mux en (a + d) a), Signal.register 0#8 (Signal.mux en (b - d) b)]
  { acc := projN! st 2 0, dif := projN! st 2 1, top := (projN! st 2 0) === 255#8 }

/-- the two register outputs exchanged between the fields (same widths) -/
def ssThreeSwap (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) : S3 defaultDomain :=
  let st := Signal.loop fun state =>
    let a := projN! state 2 0
    let b := projN! state 2 1
    bundleAll! [Signal.register 0#8 (Signal.mux en (a + d) a), Signal.register 0#8 (Signal.mux en (b - d) b)]
  { acc := projN! st 2 1, dif := projN! st 2 0, top := (projN! st 2 0) === 255#8 }

/-- the two registers' updates exchanged -/
def ssThreeRegs (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) : S3 defaultDomain :=
  let st := Signal.loop fun state =>
    let a := projN! state 2 0
    let b := projN! state 2 1
    bundleAll! [Signal.register 0#8 (Signal.mux en (b - d) b), Signal.register 0#8 (Signal.mux en (a + d) a)]
  { acc := projN! st 2 0, dif := projN! st 2 1, top := (projN! st 2 0) === 255#8 }

/-- ONE output altered (the combinational one) -/
def ssThreeOut (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) : S3 defaultDomain :=
  let st := Signal.loop fun state =>
    let a := projN! state 2 0
    let b := projN! state 2 1
    bundleAll! [Signal.register 0#8 (Signal.mux en (a + d) a), Signal.register 0#8 (Signal.mux en (b - d) b)]
  { acc := projN! st 2 0, dif := projN! st 2 1, top := (projN! st 2 0) === 254#8 }

/-- control targets: never run through the entry themselves -/
def ssTwoCtl (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) : S2 defaultDomain := ssTwo en d
def ssThreeCtl (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) : S3 defaultDomain := ssThree en d

/-- plain (non-loop) registers under a structure: refused before any proof -/
def ssPlain (a : Signal defaultDomain (BitVec 8)) : S2 defaultDomain :=
  { cnt := Signal.register 0#8 a, hit := (fun w => w == 0) <$> a }

/-! ## Positives -/

deriving instance Lean.ToExpr for Contract

def modOf (decl : Name) : TermElabM Sparkle.IR.AST.Module := do
  return (← Sparkle.Compiler.Elab.synthesizeCombinational decl).1

/-- the statement term, the port names, the clock/reset and the registers' initial values are written out by
hand (`inits`: one value per register, in body order; the register NAMES are the module's). -/
def checkStructSeq (decl : Name) (stmtStx : Term) (ports : List String) (inits : List Int) :
    CommandElabM Unit := liftTermElabM do
  let (m, _, thm) ← vedU1Entry decl
  let nm := Names.ofBase decl
  unless m.outputs.map (·.name) == ports do throwError "{decl}: ports {m.outputs.map (·.name)}"
  let stmt ← instantiateMVars (← Term.elabTerm stmtStx none)
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not the expected U1Stmt\n{ti.type}\n{expected}"
  -- the module the entry returned is the one the theorem is about
  let some (.defnInfo mi) := (← getEnv).find? nm.mod | throwError "no module constant"
  unless mi.value == toExpr m do throwError "{decl}: ved_mod is not the returned module"
  -- the contract, by hand
  let some (.defnInfo ci) := (← getEnv).find? nm.contract | throwError "no contract"
  -- the table of the hand-written statement; its binder names are the declaration's (`en`, `d`), not the
  -- hygienic ones of the quotation
  let tbl0 ← readTableOfType decl (← inferType stmt)
  let tbl := { tbl0 with binders := ["en", "d"] }
  let regNames := (regsOf m.body).map (·.1)
  unless regNames.length == inits.length do throwError "{decl}: {regNames.length} registers"
  let hand : Contract :=
    { modName := m.name, clkRst := some ("clk", "rst"), table := tbl,
      inNames := tbl.binders.map ("_gen_" ++ ·), outNames := ports, wires := m.wires,
      inits := regNames.zip inits }
  -- the stored contract is `contractOf` of the table, the ports, the clock/reset and the returned module ...
  let viaOf := mkAppN (Lean.mkConst ``contractOf)
    #[toExpr tbl, toExpr ports, toExpr (some ("clk", "rst") : Option (String × String)), Lean.mkConst nm.mod]
  unless ← isDefEq ci.value viaOf do throwError "{decl}: the contract is not `contractOf` of the returned module"
  -- ... and that is the hand-written contract (register initial values: literals of this file)
  unless decide (contractOf tbl ports (some ("clk", "rst")) m = hand) do
    throwError "{decl}: the contract is not the hand-written one"
  -- every port of the module is a port of the contract, in order
  let some (.defnInfo oi) := (← getEnv).find? nm.outs | throwError "no outs"
  unless oi.value == toExpr m.outputs do throwError "{decl}: ved_outs is not m.outputs"
  let r ← Tools.VedStrictAudit.strictAudit thm
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) && r.axioms.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  logInfo m!"struct+registers OK {thm} {ports} {inits}"

/-- info: struct+registers OK Tests.Ved.U1StructSeqCheck.ssOne.ved_u1 [cnt, sum] [0] -/
#guard_msgs in
run_cmd do
  checkStructSeq ``ssOne (← `(fun en d => bundle2 (ssOne en d).cnt (ssOne en d).sum)) ["cnt", "sum"] [0]

/-- info: struct+registers OK Tests.Ved.U1StructSeqCheck.ssTwo.ved_u1 [cnt, hit] [0, 0] -/
#guard_msgs in
run_cmd do
  checkStructSeq ``ssTwo (← `(fun en d => bundle2 (ssTwo en d).cnt (ssTwo en d).hit)) ["cnt", "hit"] [0, 0]

-- a non-zero initial value is part of the contract, as the hand-written one says
/-- info: struct+registers OK Tests.Ved.U1StructSeqCheck.ssTwoInit.ved_u1 [cnt, hit] [1, 0] -/
#guard_msgs in
run_cmd do
  checkStructSeq ``ssTwoInit (← `(fun en d => bundle2 (ssTwoInit en d).cnt (ssTwoInit en d).hit))
    ["cnt", "hit"] [1, 0]

/-- info: struct+registers OK Tests.Ved.U1StructSeqCheck.ssThree.ved_u1 [acc, dif, top] [0, 0] -/
#guard_msgs in
run_cmd do
  checkStructSeq ``ssThree
    (← `(fun en d => bundle2 (ssThree en d).acc (bundle2 (ssThree en d).dif (ssThree en d).top)))
    ["acc", "dif", "top"] [0, 0]

/-! ## Controls: refused, no `ved_*` constant registered by the checker left -/

def checkerNames (base : Name) : List Name :=
  [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1].map (base ++ ·)

def expectRefused (stage : String) (base : Name) (act : TermElabM Unit) :
    CommandElabM Unit := liftTermElabM do
  let accepted ← try act; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith "VED U1 REFUSED" && (s.splitOn s!"[{stage}]").length > 1 do throw e
    pure false
  if accepted then throwError "control ACCEPTED (expected a refusal at [{stage}])"
  for n in checkerNames base do
    if (← getEnv).contains n then throwError "left behind: {n}"
  logInfo m!"refused [{stage}], clean"

/-- the standard checker on `decl` (its own statement and ports) with a substituted module -/
def onModule (decl : Name) (m : Sparkle.IR.AST.Module) : TermElabM Unit := do
  let (stmt, nDom, names) ← stmtOf decl
  discard <| vedU1EntryOn decl stmt nDom names m

-- the module of another declaration: fields exchanged / a register's update exchanged / one output altered
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``ssThreeCtl do onModule ``ssThreeCtl (← modOf ``ssThreeSwap)

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``ssThreeCtl do onModule ``ssThreeCtl (← modOf ``ssThreeRegs)

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``ssThreeCtl do onModule ``ssThreeCtl (← modOf ``ssThreeOut)

-- a register update altered (read through the other output only)
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``ssTwoCtl do onModule ``ssTwoCtl (← modOf ``ssTwoFlag)

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``ssTwoCtl do onModule ``ssTwoCtl (← modOf ``ssTwoUpd)

-- a wrong initial value: the module of the declaration with another one
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``ssTwoCtl do onModule ``ssTwoCtl (← modOf ``ssTwoInit)

-- the returned module itself changed: a register initial value
def mutInit (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .register o c r d _ => .register o c r d 7
      | s => s }

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``ssTwoCtl do onModule ``ssTwoCtl (mutInit (← modOf ``ssTwo))

-- the output ports exchanged inside the module (same widths)
def mutSwap (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .assign "acc" e => .assign "dif" e
      | .assign "dif" e => .assign "acc" e
      | s => s }

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``ssThreeCtl do onModule ``ssThreeCtl (mutSwap (← modOf ``ssThree))

-- the statement with exchanged projections (same widths): the kernel's correspondence
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``ssThreeCtl do
  let stmt ← instantiateMVars (← Term.elabTerm
    (← `(fun en d => bundle2 (ssThreeCtl en d).dif (bundle2 (ssThreeCtl en d).acc (ssThreeCtl en d).top))) none)
  discard <| checkU1E ``ssThreeCtl ``ssThreeCtl stmt (← modOf ``ssThree) .generated ["acc", "dif", "top"]

-- plain registers under a structure
/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd expectRefused "multi-output" ``ssPlain (discard <| vedU1Entry ``ssPlain)

end Tests.Ved.U1StructSeqCheck

import Tools.VedU1StructOut

/-!
# Checks for structure results in the U1 entry (`#ved_u1_struct`, register-free)

A result that is a structure of `Signal defaultDomain _` fields (or a `×` of such,
or a structure of structures) is read as the tuple of its fields in constructor
order; the statement is `U1Stmt c m (fun xs => bundle2 (D xs).f₁ (bundle2 (D xs).f₂ …))`
over the ORIGINAL declaration `D`, and the output ports are the fields' names (the
compiler's `splitReturnLeaves` rule), required to be exactly the returned module's.
The checker is the standard one.  Positives: the theorem's stored type is the
hand-written statement, ports in order, std3 axioms.  Controls: swapped fields,
a wrong field width, a missing field, a statement whose projections are exchanged,
another domain, a non-signal field and a register body are refused; nothing is left.
-/

namespace Tests.Ved.U1StructOutCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1StructOut

/-! ## Declarations -/

structure Pa (dom : DomainConfig) where
  flag : Signal dom Bool
  data : Signal dom (BitVec 8)

/-- the minimal example: Bool + BitVec 8 -/
def mini (x : Signal defaultDomain (BitVec 8)) (v : Signal defaultDomain Bool) : Pa defaultDomain :=
  { flag := v, data := x &&& x }

structure Pb (dom : DomainConfig) where
  x : Signal dom (BitVec 8)
  y : Signal dom (BitVec 8)

def pb (a b : Signal defaultDomain (BitVec 8)) : Pb defaultDomain := { x := a &&& b, y := a ||| b }
def pbSwapped (a b : Signal defaultDomain (BitVec 8)) : Pb defaultDomain := { x := a ||| b, y := a &&& b }
def pbVal (a b : Signal defaultDomain (BitVec 8)) : Pb defaultDomain := { x := a &&& b, y := a ^^^ b }
/-- control target (never run through the entry itself) -/
def pbCtl (a b : Signal defaultDomain (BitVec 8)) : Pb defaultDomain := { x := a &&& b, y := a ||| b }

/-- a narrower `data` field than `Pa` -/
structure PaNarrow (dom : DomainConfig) where
  flag : Signal dom Bool
  data : Signal dom (BitVec 4)
def miniNarrow (x : Signal defaultDomain (BitVec 8)) (v : Signal defaultDomain Bool) : PaNarrow defaultDomain :=
  { flag := v, data := (fun w => w.extractLsb' 0 4) <$> x }
def miniCtl (x : Signal defaultDomain (BitVec 8)) (v : Signal defaultDomain Bool) : Pa defaultDomain :=
  { flag := v, data := x &&& x }
/-- through the standard entry -/
def miniStd (x : Signal defaultDomain (BitVec 8)) (v : Signal defaultDomain Bool) : Pa defaultDomain :=
  { flag := v, data := x &&& x }

/-- three fields, a polymorphic domain -/
structure P3 (dom : DomainConfig) where
  lo : Signal dom (BitVec 4)
  hi : Signal dom (BitVec 4)
  eq : Signal dom Bool

def p3 {dom : DomainConfig} (a : Signal dom (BitVec 8)) (b : Signal dom Bool) : P3 dom :=
  { lo := (fun w => w.extractLsb' 0 4) <$> a, hi := (fun w => w.extractLsb' 4 4) <$> a, eq := b }

/-- a structure inside a structure -/
structure Outer (dom : DomainConfig) where
  inner : Pa dom
  tail : Signal dom (BitVec 8)
def outer (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain Bool) : Outer defaultDomain :=
  { inner := { flag := b, data := ~~~a }, tail := a }

/-- a product with a structure inside -/
def prodS (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain Bool) :
    Pa defaultDomain × Signal defaultDomain (BitVec 8) :=
  ({ flag := b, data := ~~~a }, a)

def otherDom : DomainConfig := { defaultDomain with period := 20001 }
def pOther (a : Signal otherDom (BitVec 8)) : Pa otherDom := { flag := (fun w => w == 0) <$> a, data := a }

structure PNat (dom : DomainConfig) where
  n : Nat
  s : Signal dom (BitVec 8)
def pNat (a : Signal defaultDomain (BitVec 8)) : PNat defaultDomain := { n := 3, s := a }

def pReg (a : Signal defaultDomain (BitVec 8)) : Pa defaultDomain :=
  { flag := (fun w => w == 0) <$> a, data := Signal.register 0#8 a }

/-! ## Positives -/

def modOf (decl : Name) : TermElabM Sparkle.IR.AST.Module := do
  return (← Sparkle.Compiler.Elab.synthesizeCombinational decl).1

def checkStruct (decl : Name) (stmtStx : Term) (ports : List String) : CommandElabM Unit := liftTermElabM do
  let (m, _, thm, nDom) ← vedU1EntryStruct decl
  let nm := Names.ofBase decl
  unless m.outputs.map (·.name) == ports do throwError "{decl}: ports {m.outputs.map (·.name)}"
  let stmt ← instantiateMVars (← Term.elabTerm stmtStx none)
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not the expected U1Stmt\n{ti.type}\n{expected}"
  let some (.defnInfo ci) := (← getEnv).find? nm.outs | throwError "no outs"
  unless ci.value == toExpr (m.outputs) do throwError "{decl}: ved_outs is not m.outputs"
  let r ← Tools.VedStrictAudit.strictAudit thm
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) && r.axioms.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  logInfo m!"struct OK {thm} {m.outputs.map (·.name)} {nDom}"

/-- info: struct OK Tests.Ved.U1StructOutCheck.mini.ved_u1 [flag, data] 0 -/
#guard_msgs in
run_cmd checkStruct ``mini (← `(fun x v => bundle2 (mini x v).flag (mini x v).data)) ["flag", "data"]

/-- info: struct OK Tests.Ved.U1StructOutCheck.pb.ved_u1 [x, y] 0 -/
#guard_msgs in
run_cmd checkStruct ``pb (← `(fun a b => bundle2 (pb a b).x (pb a b).y)) ["x", "y"]

/-- info: struct OK Tests.Ved.U1StructOutCheck.p3.ved_u1 [lo, hi, eq] 1 -/
#guard_msgs in
run_cmd do
  checkStruct ``p3
    (← `(fun (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain Bool) =>
      bundle2 (p3 a b).lo (bundle2 (p3 a b).hi (p3 a b).eq))) ["lo", "hi", "eq"]

/-- info: struct OK Tests.Ved.U1StructOutCheck.outer.ved_u1 [inner_flag, inner_data, tail] 0 -/
#guard_msgs in
run_cmd do
  checkStruct ``outer
    (← `(fun a b => bundle2 (bundle2 (outer a b).inner.flag (outer a b).inner.data) (outer a b).tail))
    ["inner_flag", "inner_data", "tail"]

/-- info: struct OK Tests.Ved.U1StructOutCheck.prodS.ved_u1 [out_0_flag, out_0_data, out_1] 0 -/
#guard_msgs in
run_cmd do
  checkStruct ``prodS
    (← `(fun a b => bundle2 (bundle2 (prodS a b).1.flag (prodS a b).1.data) (prodS a b).2))
    ["out_0_flag", "out_0_data", "out_1"]

/-! ## Controls: refused, no `ved_*` constant left -/

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

/-- the struct entry's checker on `decl` with a substituted module -/
def onModule (decl : Name) (m : Sparkle.IR.AST.Module) : TermElabM Unit := do
  let (stmt, nDom, names) ← stmtOfStruct decl
  discard <| vedU1EntryOn decl stmt nDom names m

def expectEntry (stage : String) (decl : Name) : CommandElabM Unit :=
  expectRefused stage decl (discard <| vedU1EntryStruct decl)

-- the standard entry takes the structure path (it refused a structure at `[table]` before
-- `Tools/VedU1StructSeq.lean`): the same theorem type as `#ved_u1_struct`
def checkStd (decl : Name) (stmtStx : Term) (ports : List String) : CommandElabM Unit := liftTermElabM do
  let (m, _, thm) ← vedU1Entry decl
  let nm := Names.ofBase decl
  unless m.outputs.map (·.name) == ports do throwError "{decl}: ports {m.outputs.map (·.name)}"
  let stmt ← instantiateMVars (← Term.elabTerm stmtStx none)
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not the expected U1Stmt"
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  logInfo m!"std struct OK {thm} {m.outputs.map (·.name)}"

/-- info: std struct OK Tests.Ved.U1StructOutCheck.miniStd.ved_u1 [flag, data] -/
#guard_msgs in
run_cmd checkStd ``miniStd (← `(fun x v => bundle2 (miniStd x v).flag (miniStd x v).data)) ["flag", "data"]

-- the exchanged drivers: the module of the field-swapped declaration
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``pbCtl do onModule ``pbCtl (← modOf ``pbSwapped)

def mutSwap (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .assign "x" e => .assign "y" e
      | .assign "y" e => .assign "x" e
      | s => s }

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``pbCtl do onModule ``pbCtl (mutSwap (← modOf ``pb))

-- another value of one field
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``pbCtl do onModule ``pbCtl (← modOf ``pbVal)

-- the statement with exchanged projections (same widths): the kernel's correspondence
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``pbCtl do
  let stmt ← instantiateMVars (← Term.elabTerm (← `(fun a b => bundle2 (pbCtl a b).y (pbCtl a b).x)) none)
  discard <| checkU1E ``pbCtl ``pbCtl stmt (← modOf ``pb) .generated ["x", "y"]

-- a wrong field width: the module of the narrower declaration
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``miniCtl do onModule ``miniCtl (← modOf ``miniNarrow)

-- a missing field (port and its assignment dropped)
def mutDrop (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with outputs := m.outputs.dropLast
           body := m.body.filter fun s => match s with
             | .assign "data" _ => false
             | _ => true }

/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd expectRefused "multi-output" ``miniCtl do onModule ``miniCtl (mutDrop (← modOf ``mini))

-- a renamed field port
def mutRename (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with outputs := m.outputs.map fun p => if p.name == "data" then { p with name := "dat" } else p
           body := m.body.map fun s => match s with
             | .assign "data" e => .assign "dat" e
             | s => s }

/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd expectRefused "multi-output" ``miniCtl do onModule ``miniCtl (mutRename (← modOf ``mini))

-- another structure's module (other port list)
/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd expectRefused "multi-output" ``miniCtl do onModule ``miniCtl (← modOf ``pb)

-- another domain, a non-signal field, a register body
/-- info: refused [table], clean -/
#guard_msgs in
run_cmd expectEntry "table" ``pOther

/-- info: refused [table], clean -/
#guard_msgs in
run_cmd expectEntry "table" ``pNat

/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd expectEntry "multi-output" ``pReg

end Tests.Ved.U1StructOutCheck

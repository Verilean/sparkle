import Tools.VedU1PackedEntry

/-!
# Checks for the packed-port U1 entry (`#ved_u1_packed`, a `Signal d (A × B)` result)

A product result is ONE port `out` of width `Σ wᵢ`, the first leaf in the HIGH bits
(docs/VED-U1-PACKED.md §1).  The entry fixes the slice map `projection ↦ (offset, width)` from the
declaration's type and proves `PackedStmt c m decl`: the ordinary `U1Stmt` of the packed value
(`BitVec.append`, first part high) and, on every run, every slice of `out` equals the declaration's own
projection.

Positives: the registered theorem has EXACTLY the type `PackedStmt <ved_contract> <ved_mod> <decl>`;
the contract's slice map equals one written out by hand here (so the bit order is stated
independently of `OTy.slices`); the axioms are the standard three.
Negatives (each refused, no `ved_*` constant left): slices swapped, wrong offset, wrong width,
overlapping slices, a missing slice, a changed field value, a field swapped inside the module, another
declaration's module, and `#ved_u1` itself on a packed declaration (still `[multi-output]`).
-/

namespace Tests.Ved.U1PackedCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Packed Tools.VedU1PackedEntry

/-! ## Declarations -/

/-- two components of different widths (field 0 = 8 bits high, field 1 = 4 bits low) -/
def p2 (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b

/-- nested right, a `Bool` leaf -/
def p3r (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain Bool)
    (c : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × (Bool × BitVec 4)) := bundle2 a (bundle2 b c)

/-- nested left, auto-bound domain -/
def p3l {dom : DomainConfig} (a b : Signal dom (BitVec 8)) (c : Signal dom (BitVec 4)) :
    Signal dom ((BitVec 8 × BitVec 8) × BitVec 4) := bundle2 (bundle2 (a &&& b) (a ||| b)) c

/-- same widths in both fields, and variants of it -/
def pw (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8 × BitVec 8) := bundle2 a b
def pwSwap (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8 × BitVec 8) := bundle2 b a
def pwVal (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8 × BitVec 8) :=
  bundle2 (a &&& b) b

/-- control targets: never run through the entry themselves -/
def pwCtl (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8 × BitVec 8) := bundle2 a b
def p2Ctl (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b

/-- a result that is not packed (one leaf) -/
def one (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := ~~~a

/-! ## Positives -/

def modOf (decl : Name) : TermElabM Sparkle.IR.AST.Module := do
  return (← Sparkle.Compiler.Elab.synthesizeCombinational decl).1

/-- `slices`: the slice map written out by hand; `stmtStx`: the statement term written out by hand
(`decl` or `@decl defaultDomain`). -/
def checkPacked (decl : Name) (stmtStx : Term) (slices : List (Nat × Nat)) (W : Nat) :
    CommandElabM Unit := liftTermElabM do
  let (m, thm, nDom) ← vedU1PackedS decl
  let nm := Names.ofBase decl
  unless m.outputs == [⟨"out", .bitVector W⟩] do throwError "{decl}: outputs {repr m.outputs}"
  let stmt ← instantiateMVars (← Term.elabTerm stmtStx none)
  let expected := mkAppN (Lean.mkConst ``PackedStmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not the expected PackedStmt\n{ti.type}\n{expected}"
  -- the contract's slice map is the hand-written one
  let some (.defnInfo ci) := (← getEnv).find? nm.contract | throwError "no contract"
  let hand : PContract :=
    { modName := m.name, tbl := (← readTableOfType decl (← inferType stmt)), port := "out", slices,
      inNames := (← readTableOfType decl (← inferType stmt)).binders.map ("_gen_" ++ ·), wires := m.wires }
  unless ci.value == toExpr hand do throwError "{decl}: slice map is not the hand-written one {slices}"
  let r ← Tools.VedStrictAudit.strictAudit thm
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) && r.axioms.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  logInfo m!"packed OK {thm} {slices} {nDom}"

/-- info: packed OK Tests.Ved.U1PackedCheck.p2.ved_u1 [(4, 8), (0, 4)] 0 -/
#guard_msgs in
run_cmd checkPacked ``p2 (← `(p2)) [(4, 8), (0, 4)] 12

/-- info: packed OK Tests.Ved.U1PackedCheck.pw.ved_u1 [(8, 8), (0, 8)] 0 -/
#guard_msgs in
run_cmd checkPacked ``pw (← `(pw)) [(8, 8), (0, 8)] 16

/-- info: packed OK Tests.Ved.U1PackedCheck.p3r.ved_u1 [(5, 8), (4, 1), (0, 4)] 0 -/
#guard_msgs in
run_cmd checkPacked ``p3r (← `(p3r)) [(5, 8), (4, 1), (0, 4)] 13

/-- info: packed OK Tests.Ved.U1PackedCheck.p3l.ved_u1 [(12, 8), (4, 8), (0, 4)] 1 -/
#guard_msgs in
run_cmd checkPacked ``p3l (← `(@p3l defaultDomain)) [(12, 8), (4, 8), (0, 4)] 20

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

/-- the checker on `decl` (its own statement and table) with a substituted slice map / module -/
def onMap (decl : Name) (slices : List (Nat × Nat)) (m : Sparkle.IR.AST.Module) : TermElabM Unit := do
  let (stmt, _, tbl) ← packedStmtOf decl
  discard <| checkPackedE decl stmt tbl slices m .generated

-- the right map is accepted by the same helper (so the refusals below are due to the map)
/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``pwCtl do onMap ``pwCtl [(0, 8), (8, 8)] (← modOf ``pw)  -- slices swapped

/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``p2Ctl do onMap ``p2Ctl [(0, 4), (4, 8)] (← modOf ``p2)  -- fields' slices exchanged (widths too)

/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``p2Ctl do onMap ``p2Ctl [(5, 8), (0, 4)] (← modOf ``p2)  -- wrong offset

/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``p2Ctl do onMap ``p2Ctl [(4, 7), (0, 4)] (← modOf ``p2)  -- wrong width

/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``p2Ctl do onMap ``p2Ctl [(2, 8), (0, 4)] (← modOf ``p2)  -- overlapping

/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``p2Ctl do onMap ``p2Ctl [(4, 8)] (← modOf ``p2)  -- missing slice

/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``p2Ctl do onMap ``p2Ctl [(4, 8), (0, 4), (0, 4)] (← modOf ``p2)  -- extra slice

/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``p2Ctl do onMap ``p2Ctl [(8, 8), (0, 4)] (← modOf ``p2)  -- a gap (bits 4..7 uncovered)

-- one field's value changed (same widths): `a & b` instead of `a`
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``pwCtl do onMap ``pwCtl [(8, 8), (0, 8)] (← modOf ``pwVal)

-- the other field order inside the module (same widths): `concat [b, a]`
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``pwCtl do onMap ``pwCtl [(8, 8), (0, 8)] (← modOf ``pwSwap)

-- another declaration's module (other port width)
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``pwCtl do onMap ``pwCtl [(8, 8), (0, 8)] (← modOf ``p2)

-- a module whose port is not the one packed `out`
def mutPort (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with outputs := m.outputs.map fun p => { p with name := "out_x" } }

/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``pwCtl do onMap ``pwCtl [(8, 8), (0, 8)] (mutPort (← modOf ``pw))

-- `#ved_u1_packed` on a result that is not a product, and `#ved_u1` on a packed result
/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``one (discard <| vedU1PackedS ``one)

/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd expectRefused "multi-output" ``pwCtl (discard <| vedU1Entry ``pwCtl)

end Tests.Ved.U1PackedCheck

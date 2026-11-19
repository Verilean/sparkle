import Tools.VedU1HierEntry

/-!
# Checks for the hierarchical U1 entry, H1 (`Tools/VedU1HierEntry.lean`)

The small examples here are NOT part of the 327 inventory rows.

* ENTRY RUNS: `#ved_u1_hier` on a combinational parent that calls the same combinational child
  twice with different inputs, with a dependency between children, and with ASYMMETRIC children
  (`x - y`, `(x ^^^ y) - y`), so that a miswiring changes the value.  The theorem's exact type
  is rebuilt and compared, the axioms are the standard three, and the closed hierarchical run
  (`stepH`) is evaluated on concrete values and compared with the declaration's value.
* CONTROLS: the checker `checkU1H` (the entry's own checker) is run on the returned `(m, d)` with
  ONE piece altered; each must be refused at a named stage and leave NO constant of its base.
* KERNEL-LEVEL CONTROLS: a theorem about another Design, another declaration or another module's
  child does not typecheck against the statement.
-/

namespace Tests.Ved.U1HierCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry

/-! ## Declarations -/

/-- Asymmetric: `x - y`. -/
@[hardware_module] def hcA (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x - y

/-- Asymmetric: `(x ^^^ y) - y`. -/
@[hardware_module] def hcB (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  (x ^^^ y) - y

/-- Combinational parent: `hcA` called twice with different inputs, `hcB` depending on both. -/
def hpar (a b c : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := hcA a b
  let q := hcA b c
  hcB p q

/-- A chain of the same child: the second call reads the first call's output. -/
def hchain (a b c : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  hcA (hcA a b) c

/-- A PRIVATE parent (its constants live under `_private.<module>.0`, a name
the generated proof text cannot spell; the text uses the user-facing name). -/
private def hpriv (a b c : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  hcA (hcA a b) c

/-- Same shape as `hpar`, used by the controls (so nothing clashes with the entry runs). -/
def hctl (a b c : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := hcA a b
  let q := hcA b c
  hcB p q

/-- Another parent with other children (for the "another Design" control). -/
@[hardware_module] def hcC (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + y

def hother (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := hcC a b

/-- One parent with two outputs (refused before synthesis). -/
def hpair (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8 × BitVec 8) :=
  (fun x => (x, x)) <$> hcA a b

/-! ## Helpers -/

/-- The checker's exact expected statement for `decl`. -/
def expectedOf (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``U1HStmt)
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

/-- The entry run, the exact type, the standard axioms. -/
def checkOk (decl : Name) : CommandElabM Unit := liftTermElabM do
  let (_, d, thm, nDom, _) ← vedU1HierEntry decl
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U1HStmt c m d decl"
  let r ← Tools.VedStrictAudit.strictAudit thm
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) && r.axioms.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  logInfo m!"hier OK {thm} children {d.modules.map (·.name)}"

/-- info: hier OK Tests.Ved.U1HierCheck.hpar.ved_u1 children [Tests.Ved.U1HierCheck.hcA, Tests.Ved.U1HierCheck.hcB] -/
#guard_msgs in
run_cmd checkOk ``hpar

/-- info: hier OK Tests.Ved.U1HierCheck.hchain.ved_u1 children [Tests.Ved.U1HierCheck.hcA] -/
#guard_msgs in
run_cmd checkOk ``hchain

/-- The private parent: exact type and standard axioms, as `checkOk`
(the message avoids the module-dependent private prefix). -/
def checkOkPriv : CommandElabM Unit := liftTermElabM do
  let decl := ``hpriv
  unless isPrivateName decl do throwError "{decl} is not private"
  let (_, _, thm, nDom, _) ← vedU1HierEntry decl
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U1HStmt c m d decl"
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  logInfo m!"hier OK private parent {(privateToUserName? thm).getD thm}"

/-- info: hier OK private parent Tests.Ved.U1HierCheck.hpriv.ved_u1 -/
#guard_msgs in
run_cmd checkOkPriv

/-! ## The closed run on concrete values (miswiring is observable) -/

/-- Arrangements: the checked order for the top, the leaf order for every child. -/
def arrOf (d : Design) (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module → List Stmt :=
  fun x => if x == m then orderBodyH d x.body else Tools.VedU1Entry.orderBody x.body

/-- One closed cycle on concrete inputs; the value of the output port. -/
def stepOut (d : Design) (m : Sparkle.IR.AST.Module) (a b c : Nat) : Option Nat :=
  let env0 : Env := fun n =>
    if n == "_gen_a" then a else if n == "_gen_b" then b else if n == "_gen_c" then c else 0
  (stepH d (arrOf d m) m env0).map fun r => r.1 "out"

def swapConns : Stmt → Stmt
  | .inst mn i [(p1, e1), (p2, e2), o] => .inst mn i [(p1, e2), (p2, e1), o]
  | s => s

def synthOf (decl : Name) : CommandElabM (Sparkle.IR.AST.Module × Design) := liftTermElabM do
  Sparkle.Compiler.Elab.synthesizeCombinational decl

/- `hpar 9 3 7`: p = 6, q = 3 - 7 = 252, out = (6 ^^^ 252) - 252 = 254; swapping the first call's
connections gives p = 3 - 9 = 250 and out = (250 ^^^ 252) - 252 = 6 - 252 = 10 (mod 256). -/
run_cmd do
  let (m, d) ← synthOf ``hpar
  let a := stepOut d m 9 3 7
  let m' := { m with body := (m.body.take 1).map swapConns ++ m.body.drop 1 }
  let b := stepOut d m' 9 3 7
  unless a == some 254 do throwError "closed run of hpar: {a}"
  unless b == some 10 do throwError "closed run of the swapped hpar: {b}"
  logInfo m!"closed run: {a} vs miswired {b}"

#guard (hpar ⟨fun _ => 9#8⟩ ⟨fun _ => 3#8⟩ ⟨fun _ => 7#8⟩).val 0 == 254#8

/-! ## Controls -/

/-- The constants of this file's environment under `decl` (the parent's six
checker constants AND the `decl.ved_child.*` leaf constants). -/
def constsUnder (decl : Name) : MetaM (List Name) := do
  return (← getEnv).constants.map₂.toList.filterMap fun (n, _) =>
    if decl.isPrefixOf n then some n else none

/-- The checker with one piece altered must refuse at `stage`, and the
environment under `decl` (parent checker constants and the `ved_child`
namespace) must be exactly as before the call. -/
def expectRefused (decl : Name) (stage : String) (m : Sparkle.IR.AST.Module) (d : Design) :
    CommandElabM Unit := liftTermElabM do
  let before ← constsUnder decl
  let (stmt, nDom) ← specialiseDomain decl
  let r ← try
      discard <| checkU1H decl stmt nDom m d
      pure none
    catch e => pure (some (← e.toMessageData.toString))
  let pre := s!"VED U1 REFUSED {decl} [{stage}]"
  match r with
  | none => throwError "{decl}: expected a refusal at [{stage}], the checker ACCEPTED"
  | some msg =>
    unless msg.startsWith pre do throwError "expected {pre}, got: {msg}"
  let nm := HNames.ofBase decl
  for n in [nm.mod, nm.design, nm.contract, nm.outs, nm.body, nm.thm] do
    if (← getEnv).contains n then throwError "{n} is still in the environment after the refusal"
  let after ← constsUnder decl
  let added := after.filter (!before.contains ·)
  unless added.isEmpty do throwError "constants left under {decl} after the refusal: {added}"

/-- Replace the first statement satisfying `p` by `f s`. -/
def mapFirst (p : Stmt → Bool) (f : Stmt → Stmt) : List Stmt → List Stmt
  | [] => []
  | s :: r => if p s then f s :: r else s :: mapFirst p f r

def isInstOf (n : String) : Stmt → Bool
  | .inst mn _ _ => mn == n
  | _ => false

def hcAName : String := "Tests.Ved.U1HierCheck.hcA"
def hcBName : String := "Tests.Ved.U1HierCheck.hcB"

/-- The controls' summary line. -/
def controlsRun : CommandElabM Unit := do
  let (m, d) ← synthOf ``hctl
  let name := ``hctl
  let mut n := 0
  -- 1. conns swapped (the two inputs of the first call): the statement is false
  expectRefused name "proof" { m with body := mapFirst (isInstOf hcAName) swapConns m.body } d
  n := n + 1
  -- 2. the OUTPUT connections of the two `hcA` calls exchanged
  let swapOut : Stmt → Stmt
    | .inst mn i [a, b, (po, .ref y)] =>
      .inst mn i [a, b, (po, .ref (if y == "_gen_p" then "_gen_q" else if y == "_gen_q" then "_gen_p" else y))]
    | s => s
  expectRefused name "proof" { m with body := m.body.map swapOut } d
  n := n + 1
  -- 3. a connection missing
  let dropConn : Stmt → Stmt
    | .inst mn i (a :: r) => .inst mn i (a :: r.drop 1)
    | s => s
  expectRefused name "hier-shape" { m with body := mapFirst (isInstOf hcAName) dropConn m.body } d
  n := n + 1
  -- 4. an extra connection
  let extraConn : Stmt → Stmt
    | .inst mn i cs => .inst mn i (cs ++ [("_gen_zz", .ref "_gen_a")])
    | s => s
  expectRefused name "hier-shape" { m with body := mapFirst (isInstOf hcAName) extraConn m.body } d
  n := n + 1
  -- 5. a duplicated connection
  let dupConn : Stmt → Stmt
    | .inst mn i (a :: r) => .inst mn i (a :: a :: r)
    | s => s
  expectRefused name "hier-shape" { m with body := mapFirst (isInstOf hcAName) dupConn m.body } d
  n := n + 1
  -- 6. a wrong width: the wire `_gen_p` declared 4 bits wide
  let wires := m.wires.map fun p => if p.name == "_gen_p" then { p with ty := .bitVector 4 } else p
  expectRefused name "hier-shape" { m with wires } d
  n := n + 1
  -- 7. a non-wire connection
  let nonRef : Stmt → Stmt
    | .inst mn i ((p, _) :: r) => .inst mn i ((p, .const 1 8) :: r)
    | s => s
  expectRefused name "hier-shape" { m with body := mapFirst (isInstOf hcAName) nonRef m.body } d
  n := n + 1
  -- 8. the child's body altered (`x - y` becomes `x + y`): its leaf U1 theorem is refused
  let alter := d.modules.map fun c =>
    if c.name == hcAName then
      { c with body := c.body.map fun s => match s with
          | .assign l (.op .sub args) => .assign l (.op .add args)
          | s => s }
    else c
  expectRefused name "child" m { d with modules := alter }
  n := n + 1
  -- 9. a child missing from the design
  expectRefused name "hier-shape" m { d with modules := d.modules.filter (·.name != hcBName) }
  n := n + 1
  -- 10. duplicate child names
  expectRefused name "hier-shape" m { d with modules := d.modules ++ d.modules.take 1 }
  n := n + 1
  -- 11. a combinational cycle (the first call's output feeds its own input)
  let cyc : Stmt → Stmt
    | .inst mn i ((p1, _) :: r) => .inst mn i ((p1, .ref "_gen_p") :: r)
    | s => s
  expectRefused name "order" { m with body := mapFirst (isInstOf hcAName) cyc m.body } d
  n := n + 1
  -- 12. an undriven net (a declared wire nothing drives feeds a call)
  let und : Stmt → Stmt
    | .inst mn i ((p1, _) :: r) => .inst mn i ((p1, .ref "_gen_u") :: r)
    | s => s
  expectRefused name "order"
    { m with body := mapFirst (isInstOf hcAName) und m.body,
             wires := m.wires ++ [⟨"_gen_u", .bitVector 8⟩] } d
  n := n + 1
  -- 13. two drivers (an assignment to a wire an instance output drives)
  expectRefused name "order"
    { m with body := m.body ++ [.assign "_gen_p" (.ref "_gen_a")] } d
  n := n + 1
  -- 14. a write to a module input (an instance output on an input)
  let toIn : Stmt → Stmt
    | .inst mn i [a, b, (po, _)] => .inst mn i [a, b, (po, .ref "_gen_a")]
    | s => s
  expectRefused name "order" { m with body := mapFirst (isInstOf hcAName) toIn m.body } d
  n := n + 1
  -- 15. ANOTHER Design (the design of another parent: its modules are not this parent's children)
  let (_, d2) ← synthOf ``hother
  expectRefused name "hier-shape" m d2
  n := n + 1
  -- 16. an unused leftover module in the design (never dropped silently)
  let (_, d3) ← synthOf ``hother
  expectRefused name "hier-shape" m { d with modules := d.modules ++ d3.modules }
  n := n + 1
  -- 17. a sequential child (a register in its body): H2, refused explicitly
  let seq := d.modules.map fun c =>
    if c.name == hcAName then
      { c with body := c.body ++ [.register "r" "clk" ("rst", .synchronous) (.ref "_gen_x") 0] }
    else c
  expectRefused name "hier-shape" m { d with modules := seq }
  n := n + 1
  -- 18. a register at the top: H2, refused explicitly
  expectRefused name "hier-shape"
    { m with body := m.body ++ [.register "r" "clk" ("rst", .synchronous) (.ref "_gen_a") 0] } d
  n := n + 1
  -- 19. the top module not the design's top
  expectRefused name "hier-shape" m { d with topModule := "other" }
  n := n + 1
  -- 20. the child's module taken from ANOTHER run: same name, other module (hcA of a design whose
  --     `hcA` is the `hcC` body)
  let other := d.modules.map fun c =>
    if c.name == hcAName then { (d3.modules.headD c) with name := hcAName } else c
  expectRefused name "child" m { d with modules := other }
  n := n + 1
  -- after each refusal the environment under the controls' base (parent
  -- checker constants and its `ved_child` namespace) is unchanged
  logInfo m!"controls: {n} refused, nothing left under the base"

/-- info: controls: 20 refused, nothing left under the base -/
#guard_msgs in
run_cmd controlsRun

/-! ## A multi-output declaration is refused before synthesis -/

def multiRun : CommandElabM Unit := liftTermElabM do
  let r ← try
      discard <| vedU1HierEntry ``hpair
      pure none
    catch e => pure (some (← e.toMessageData.toString))
  match r with
  | some msg =>
    unless msg.startsWith "VED U1 REFUSED Tests.Ved.U1HierCheck.hpair [multi-output]" do
      throwError "unexpected: {msg}"
    logInfo m!"multi-output refused"
  | none => throwError "hpair accepted"

/-- info: multi-output refused -/
#guard_msgs in
run_cmd multiRun

/-! ## Type-level controls: another Design / another proof do not elaborate against the statement

These are refusals by `elabTermEnsuringType` (the elaborator's type check of
the substituted proof against the full expected type), not direct kernel
`addDecl` refusal tests. -/

def typeMismatch (what : String) (stx : Syntax) (ty : Lean.Expr) : CommandElabM Unit := liftTermElabM do
  let ok ← try
      withoutErrToSorry do
        discard <| elabTermEnsuringType stx ty
        synthesizeSyntheticMVarsNoPostponing
      pure true
    catch _ => pure false
  if ok then throwError "{what}: the substituted proof was ACCEPTED"
  logInfo m!"{what}: refused"

/-- `hchain`'s theorem about `hpar`'s statement (another declaration's proof). -/
def anotherProof : CommandElabM Unit := do
  let ty := expectedOf ``hpar 0
  typeMismatch "another declaration's proof" (← `(Tests.Ved.U1HierCheck.hchain.ved_u1)) ty

/-- `hpar`'s theorem against `hpar`'s contract and module but ANOTHER design constant. -/
def anotherDesign : CommandElabM Unit := do
  let nm := HNames.ofBase ``hpar
  let nm2 := HNames.ofBase ``hchain
  let ty := mkAppN (Lean.mkConst ``U1HStmt)
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm2.design, Lean.mkConst ``hpar]
  typeMismatch "another Design" (← `(Tests.Ved.U1HierCheck.hpar.ved_u1)) ty

/-- the leaf theorem of `hcA` is not a proof of `hcB`'s statement. -/
def anotherChild : CommandElabM Unit := do
  let hA := Names.ofBase (`Tests.Ved.U1HierCheck.hpar ++ `ved_child ++ ``hcA)
  let hB := Names.ofBase (`Tests.Ved.U1HierCheck.hpar ++ `ved_child ++ ``hcB)
  let ty := mkAppN (Lean.mkConst ``U1Stmt)
    #[Lean.mkConst hB.contract, Lean.mkConst hB.mod, Lean.mkConst ``hcB]
  typeMismatch "another child's proof" (← `(Tests.Ved.U1HierCheck.hpar.ved_child.Tests.Ved.U1HierCheck.hcA.ved_u1)) ty

/-- info: another declaration's proof: refused -/
#guard_msgs in
run_cmd anotherProof

/-- info: another Design: refused -/
#guard_msgs in
run_cmd anotherDesign

/-- info: another child's proof: refused -/
#guard_msgs in
run_cmd anotherChild

end Tests.Ved.U1HierCheck

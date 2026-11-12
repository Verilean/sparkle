import Tools.VedU1Deep
import Tools.VedU2HierRegEntry
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Nested INLINE stateful calls through the deep route (`#verify_elab_deep`, `#ved_u1_deep`, `#ved_u2_hier`)

Issue sparkle-ved-hier2-parentmix.  A parent's own `circuit do` calls a plain function (not a
`@[hardware_module]`) that has its own `circuit do` and registers.  The synthesiser inlines its
registers into the parent; on the Signal side that call is a NESTED `runCircuitH`.  DeepElab used
to drop a nested loop whose slot signature (widths, inits) equals the top's (it was taken for the
echo of the top application), so the nested value was never tied to its register block and
`_deep_trace` failed with `closers exhausted`.  Now only the top application itself (and a
specialized wrapper's head) is the echo, and the nested loop is bridged onto its register block
(candidate blocks are tried; a wrong block fails its step proof).

* POSITIVES (exact statements, standard axioms): the minimal example `nest` (`#ved_u1_deep`);
  `nest2` (a nested call that itself calls a nested stateful function: three levels, three
  registers of one signature); `parentMix` (NestedCacheCheck's declaration, parent register +
  instance + inlined call) and `parentMix2` (the same with the 2-deep inlined call) through
  `#ved_u2_hier`'s entry, type `U2HRStmt c m d decl` compared with `==`.
* REFUSALS (the real module with ONE piece of the nested call altered, against the declaration's
  own deep facts; must be refused at `[proof]` and leave nothing): the nested register's init
  changed, the nested slot swapped with the parent's (their register inputs exchanged), the
  nested register's OUTPUT replaced by its INPUT net where the parent reads it (the input net is
  the next-state expression, so this confuses state and next within one cycle; it is not a
  one-cycle delay).
-/

namespace Tests.Ved.U2HierNestedInlineCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Deep Tools.VedU1Hier Tools.VedU1HierEntry
  Tools.VedU2Hier Tools.VedU2HierEntry Tools.VedU2HierRegEntry

/-! ## Declarations -/

@[hardware_module]
def accMod (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ r + x
    return r

/-- A plain stateful function (inlined into its caller, not an instance). -/
def accInl (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ r + x
    return r

/-- A plain stateful function that itself calls `accInl`. -/
def acc2Inl (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let q ← Signal.reg 0#8
    q <~ q + accInl x
    return q

/-- The minimal example: the parent's register and one inlined stateful call. -/
def nest (o x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    p <~ o + accInl x + p
    return p

/-- Two levels of nesting. -/
def nest2 (o x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    p <~ o + acc2Inl x + p
    return p

/-- NestedCacheCheck's `parentMix`, unchanged. -/
def parentMix (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let a := accMod x
    let b := accInl x
    p <~ a + b + p
    return p

/-- `parentMix` with the 2-deep inlined call. -/
def parentMix2 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let a := accMod x
    let b := acc2Inl x
    p <~ a + b + p
    return p

/-- The declaration the hierarchical controls alter (never accepted itself). -/
def mixRef (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let a := accMod x
    let b := accInl x
    p <~ a + b + p
    return p

#guard_msgs (drop info) in
#verify_elab_deep accMod
#guard_msgs (drop info) in
#verify_elab_deep nest
#guard_msgs (drop info) in
#verify_elab_deep nest2

/-! ## Positives -/

def std3 : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def std3Only (n : Name) : CoreM Unit := do
  let axs ← collectAxioms n
  unless axs.all (std3.contains ·) do throwError "{n}: axioms outside the standard three: {axs}"

def runEntry (n : Name) : CommandElabM Unit := liftTermElabM do
  let (_, _, thm) ← vedU1DeepEntry n
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  let expected := mkAppN (mkConst ``U1Stmt)
    #[mkConst (n ++ `ved_contract), mkConst (n ++ `ved_mod), mkConst n]
  unless ti.type == expected do throwError "{thm}: type is not U1Stmt c m decl"
  let r ← Tools.VedStrictAudit.strictAudit thm
  std3Only thm
  logInfo m!"VED U1 OK {thm}: {Tools.VedStrictAudit.showNames r.axioms}"

/-- info: VED U1 OK Tests.Ved.U2HierNestedInlineCheck.nest.ved_u1: [Classical.choice, Quot.sound, propext] -/
#guard_msgs in
run_cmd runEntry ``nest

/-- info: VED U1 OK Tests.Ved.U2HierNestedInlineCheck.nest2.ved_u1: [Classical.choice, Quot.sound, propext] -/
#guard_msgs in
run_cmd runEntry ``nest2

def expectedOf (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``U2HRStmt)
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

/-- The entry run, the exact type (`==`), the strict audit, the standard axioms. -/
def checkOk (decl : Name) : CommandElabM Unit := do
  let (m, d, thm, nDom, _) ← vedU2HierEntryR decl
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U2HRStmt c m d decl"
    discard <| Tools.VedStrictAudit.strictAudit thm
    std3Only thm
    for n in [decl ++ Name.mkSimple ("ved_open_" ++ "_".intercalate (decl.components.map toString) ++ "_eq")] do
      let some (.thmInfo _) := (← getEnv).find? n | throwError "{n} is not a theorem"
      std3Only n
    logInfo m!"u2 hier reg OK {thm}: {(regsOf m.body).length} parent registers, children {d.modules.map (·.name)}"

/-- info: u2 hier reg OK Tests.Ved.U2HierNestedInlineCheck.parentMix.ved_u1: 2 parent registers, children [Tests.Ved.U2HierNestedInlineCheck.accMod] -/
#guard_msgs in
run_cmd checkOk ``parentMix

/-- info: u2 hier reg OK Tests.Ved.U2HierNestedInlineCheck.parentMix2.ved_u1: 3 parent registers, children [Tests.Ved.U2HierNestedInlineCheck.accMod] -/
#guard_msgs in
run_cmd checkOk ``parentMix2

/-! ## Refusals: the nested call altered in the module, the declaration's own deep facts -/

def modOf (base : Name) : TermElabM Sparkle.IR.AST.Module := do
  let some v := (← getConstInfo (base ++ `ved_mod)).value? | throwError "no value"
  evalModule v

def checkerNames (base : Name) : List Name :=
  [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1].map (base ++ ·) ++ auxNames base

def assertClean (absent : List Name) : TermElabM Unit := do
  let env ← getEnv
  for n in absent do
    if env.contains n then throwError "left behind: {n}"

def expectRefused (stage : String) (absent : List Name) (act : TermElabM Unit) :
    CommandElabM Unit := liftTermElabM do
  let accepted ← try act; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith "VED U1 REFUSED" && (s.splitOn s!"[{stage}]").length > 1 do throw e
    pure false
  if accepted then throwError "control ACCEPTED (expected a refusal at [{stage}])"
  assertClean absent
  logInfo m!"refused [{stage}], clean"

def deepSrc (stmt deep : Name) : TermElabM ProofSrc := do
  let tbl ← readTable stmt
  pure (.built (buildDeepWith stmt deep tbl))

def setInit (o : String) (v : Int) (b : List Stmt) : List Stmt :=
  b.map fun s => match s with
    | .register o' c r e _ => if o' == o then .register o' c r e v else s
    | s => s

/-- Exchange the input nets of two registers. -/
def swapInputs (o1 o2 : String) (b : List Stmt) : List Stmt :=
  let inOf (o : String) : Option Sparkle.IR.AST.Expr := b.findSome? fun s => match s with
    | .register o' _ _ e _ => if o' == o then some e else none
    | _ => none
  match inOf o1, inOf o2 with
  | some e1, some e2 => b.map fun s => match s with
    | .register o' c r e i => if o' == o1 then .register o' c r e2 i
        else if o' == o2 then .register o' c r e1 i else .register o' c r e i
    | s => s
  | _, _ => b

def setAssign (n : String) (e : Sparkle.IR.AST.Expr) (b : List Stmt) : List Stmt :=
  b.map fun s => match s with
    | .assign l _ => if l == n then .assign l e else s
    | s => s

def add (a b : String) : Sparkle.IR.AST.Expr := .op .add [.ref a, .ref b]

def mutated (m : Sparkle.IR.AST.Module) (f : List Stmt → List Stmt) : Sparkle.IR.AST.Module :=
  { m with body := f m.body }

def u1Ctl (decl : Name) (tag : Name) (f : List Stmt → List Stmt) : CommandElabM Unit :=
  expectRefused "proof" (checkerNames tag) do
    let m ← modOf decl
    if decide (mutated m f = m) then throwError "the mutation is the identity"
    discard <| checkU1 decl tag decl (mutated m f) (← deepSrc decl decl)

/- `nest` (module): nested register `_tmp_a_5` (input `_tmp_reg_input_4`, output read by `_tmp_arg1_3`),
parent register `_tmp_a_11` (input `_tmp_reg_input_10`), `_tmp_arg1_1 = o + _tmp_arg1_3`. -/

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd u1Ctl ``nest `ctlNestInit (setInit "_tmp_a_5" 1)

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd u1Ctl ``nest `ctlNestSwap (swapInputs "_tmp_a_5" "_tmp_a_11")

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd u1Ctl ``nest `ctlNestNextNet (setAssign "_tmp_arg1_1" (add "_gen_o" "_tmp_reg_input_4"))

/- `nest2`: innermost `_tmp_a_7`, middle `_tmp_a_12`, parent `_tmp_a_18`. -/

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd u1Ctl ``nest2 `ctlNest2Init (setInit "_tmp_a_7" 1)

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd u1Ctl ``nest2 `ctlNest2Swap (swapInputs "_tmp_a_7" "_tmp_a_12")

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd u1Ctl ``nest2 `ctlNest2NextNet (setAssign "_tmp_arg1_1" (add "_gen_o" "_tmp_reg_input_11"))

/-! Hierarchical: `mixRef`'s module has the instance `accMod`, the nested register `_tmp_a_7`
(input `_tmp_reg_input_6`, read by `_tmp_arg1_5`) and the parent register `_tmp_a_13`;
`_tmp_arg1_1 = instance output + _tmp_arg1_5`. -/

def localConsts : CommandElabM NameSet := do
  return (← getEnv).constants.map₂.toList.foldl (fun s (n, _) => s.insert n) {}

def synthOf (decl : Name) : CommandElabM (Sparkle.IR.AST.Module × Design) := liftTermElabM do
  Sparkle.Compiler.Elab.synthesizeCombinational decl

/-- The hierarchical checker with one piece altered refuses at `[proof]`, leaving nothing. -/
def hierCtl (decl : Name) (needle : String) (f : List Stmt → List Stmt) : CommandElabM Unit := do
  let (m, d) ← synthOf decl
  let before ← localConsts
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  let m' := mutated m f
  if decide (m' = m) then throwError "the mutation is the identity"
  let r ← try
      discard <| checkU2HR decl stmt nDom m' d none
      pure none
    catch e => pure (some (← liftTermElabM (e.toMessageData.toString)))
  match r with
  | none => throwError "{decl}: the checker ACCEPTED the altered module"
  | some msg =>
    unless msg.startsWith s!"VED U1 REFUSED {decl} [proof]" do throwError "expected a [proof] refusal, got: {msg}"
    unless (msg.splitOn needle).length > 1 do throwError "the refusal does not name `{needle}`: {msg.take 300}"
    logInfo m!"refused [proof] ({needle}), clean"
  let added := (← localConsts).toList.filter (!before.contains ·)
  unless added.isEmpty do throwError "constants left after the refusal: {added}"

/-- info: refused [proof] (unsolved goals), clean -/
#guard_msgs in
run_cmd hierCtl ``mixRef "unsolved goals" (setInit "_tmp_a_7" 1)

/-- info: refused [proof] (omega could not prove the goal), clean -/
#guard_msgs in
run_cmd hierCtl ``mixRef "omega could not prove the goal" (swapInputs "_tmp_a_7" "_tmp_a_13")

/-- info: refused [proof] (omega could not prove the goal), clean -/
#guard_msgs in
run_cmd do
  hierCtl ``mixRef "omega could not prove the goal"
    (setAssign "_tmp_arg1_1" (add "_tmp_op_a_2" "_tmp_reg_input_6"))

end Tests.Ved.U2HierNestedInlineCheck

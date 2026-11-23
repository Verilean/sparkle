import Tools.VedU2HierRegEntry
import Tools.VedU2HierRecEntry
import Tools.VedU2HierRecOr
import Tests.Ved.ComposeCheckUtil
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# The nested toy through the entry (CANDIDATE; Tools/VedU2HierRec*.lean; observed, single runs)

NOT a ledger row.  A depth-2 design through `#ved_u2_hier` with `ved.compose.nested` ON:

* `leafs` (one register, `r' = r + x`) <- `mids` (one register of its own, `r' = r + leafs(x) + y`, output `r`) <- `tops`
  (a register-free parent, `out = mids(a, b)`).  The middle module is SCALAR (one output): the middle module as a
  multi-output hierarchical parent (a struct middle module with registers) has no entry yet (probe at the end).
* the stored type is `U2HRStmtR contract mod design decl`, the artifact is the declaration's own synthesis, the axioms are
  the standard three, the middle module's theorem constant occurs in the proof, and the grandchild's constants do not occur in
  the proof's DIRECT constants (not a closure audit);
* the closed run `runHSR` of the parent's real design is evaluated and compared with a hand-written reference;
* CONTROLS through the checker (`checkU2HN`) on edited `(m, d)`: the middle module's output not the parent's output, the
  instance output wire swapped, a same-NAME but different middle module (the stored theorem is refused by the cache check),
  a duplicate instance name (wrong instance path), and the option OFF (the old refusal text, exactly).
-/

namespace Tests.Ved.RecEntry

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil
open Tools.VedU1HierEntry Tools.VedU2HierRec

/-- a sequential leaf (one register) -/
@[hardware_module] def leafs (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let r ← Signal.reg 0#4
    r <~ r + x
    return r

#verify_elab_deep leafs

/-- the middle module: one register of its own, one instance of `leafs` on its data input -/
@[hardware_module] def mids (x y : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let r ← Signal.reg 0#4
    let c := leafs x
    r <~ r + c + y
    return r

/-- the top: register-free, one instance of the middle module on its data inputs -/
def tops (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) := mids a b
/-- the same parent with the wires crossed (a second parent over the SAME middle module) -/
def tops3 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) := mids b a
-- copies for the controls (each control needs its own constants)
def topsC1 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) := mids a b
def topsC2 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) := mids a b
def topsC3 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) := mids a b
def topsC4 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) := mids a b
def topsC5 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) := mids a b
def topsC7 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := mids a b
    acc <~ (accS + c : Signal defaultDomain (BitVec 4))
    return accS
def topsOff (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) := mids a b

/-- a parent WITH a register over the middle module (data inputs) -/
def topr1 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := mids a b
    acc <~ (accS + c : Signal defaultDomain (BitVec 4))
    return accS

/-- a second middle module over the SAME leaf (the grandchild `leafs` is shared by both middle modules) -/
@[hardware_module] def midsB (x y : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let r ← Signal.reg 0#4
    let c := leafs y
    r <~ r + c + x
    return r

/-- TWO distinct middle modules (sharing the grandchild) and a register-free parent -/
def topm (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) := mids a b + midsB b a

/-- the same with a register in the parent -/
def topmr (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := mids a b
    let e := midsB b a
    acc <~ (accS + c + e : Signal defaultDomain (BitVec 4))
    return accS

/-- DEPTH 3: a middle module over a middle module (one register of its own, one instance of `mids`) -/
@[hardware_module] def mids2 (x y : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let r ← Signal.reg 0#4
    let c := mids x y
    r <~ r + c
    return r

/-- depth 3, register-free parent -/
def tops2 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) := mids2 a b

/-- depth 3, a parent WITH a register -/
def topr2 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := mids2 a b
    acc <~ (accS + c : Signal defaultDomain (BitVec 4))
    return accS

def topsC6 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) := mids2 a b

def expectedR (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``U2HRStmtR) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

-- the nested entry, option ON
set_option ved.compose.nested true in
#ved_u2_hier tops

-- the nested entry for a parent WITH registers (the register route; the middle module's theorem is already stored by `tops`)
set_option ved.compose.nested true in
#ved_u2_hier topr1

-- DEPTH 3 through the entry, the same code: the register-free parent first (the middle module `mids2` is itself a register
-- parent over the non-leaf `mids`: its own entry is the nested register route), then the parent with a register
set_option ved.compose.nested true in
#ved_u2_hier tops2

set_option ved.compose.nested true in
#ved_u2_hier topr2

-- TWO distinct middle modules sharing one grandchild
set_option ved.compose.nested true in
#ved_u2_hier topm

set_option ved.compose.nested true in
#ved_u2_hier topmr

/-- the accepted theorem, read independently of the entry -/
def acceptedN (decl midThm : Name) (hit : Bool) : CommandElabM Unit := do
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
    let used := ti.value.getUsedConstants
    unless used.contains midThm do throwError "{nm.thm}: the middle module's theorem {midThm} does not occur"
    -- the grandchild is not unfolded: none of its constants is a DIRECT constant of the proof
    let gc := used.filter fun n => (n.toString.splitOn "RecEntry.leafs").length > 1
    unless gc.isEmpty do throwError "{nm.thm}: grandchild constants occur directly: {gc}"
    discard <| Tools.VedStrictAudit.strictAudit nm.thm
    logInfo m!"ACCEPTED {decl}: U2HRStmtR type ==, same artifact, std3, kernel, {midThm} occurs ({if hit then "stored, checked" else "built"}), no grandchild constant among the {used.size} direct constants (NOT a closure audit)"

#eval acceptedN ``tops `Tests.Ved.RecEntry.mids.ved_u2r false

#eval acceptedN ``topr1 `Tests.Ved.RecEntry.mids.ved_u2r true

#eval acceptedN ``tops2 `Tests.Ved.RecEntry.mids2.ved_u1 false
#eval acceptedN ``topr2 `Tests.Ved.RecEntry.mids2.ved_u1 true

#eval acceptedN ``topm `Tests.Ved.RecEntry.midsB.ved_u2r false
#eval acceptedN ``topmr `Tests.Ved.RecEntry.midsB.ved_u2r true

def withNested {α : Type} (act : CommandElabM α) : CommandElabM α :=
  withScope (fun sc => { sc with opts := sc.opts.setBool `ved.compose.nested true }) act

-- a second parent over the SAME middle module: the stored theorem is reused (checked); nothing of the middle module is rebuilt
#eval show CommandElabM Unit from do
  let before ← localConsts
  discard <| withNested (vedU2HierEntryR ``tops3)
  let after ← localConsts
  let added := after.toList.filter (!before.contains ·)
  let mid := added.filter fun n => (n.toString.splitOn "RecEntry.mids").length > 1
  unless mid.isEmpty do throwError "the middle module's constants were rebuilt: {mid}"
  unless added.any (· == (HNames.ofBase ``tops3).thm) do throwError "tops3's theorem was not added"
  acceptedN ``tops3 `Tests.Ved.RecEntry.mids.ved_u2r true

-- the closed run of the parent's real design, evaluated, against a hand-written reference
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``tops
  let arr : Sparkle.IR.AST.Module → List Stmt := fun c => orderBodyH d c.body
  let K := 6
  let a := [3, 1, 4, 1, 5, 9]
  let b := [2, 7, 1, 8, 2, 8]
  let ins : Nat → String → Nat := fun t n =>
    if n == "_gen_a" then a.getD t 0 else if n == "_gen_b" then b.getD t 0 else 0
  match runHSR d arr m (seedFwd m K ins) K (st0HR d m) with
  | none => throwError "the closed run of the nested design failed"
  | some envs =>
    let outs := envs.map (fun e => e "out")
    let rec refRun : Nat → Nat → Nat → List Nat
      | 0, _, _ => []
      | k + 1, rl, rm =>
        let t := K - (k + 1)
        rm :: refRun k ((rl + a.getD t 0) % 16) ((rm + rl + b.getD t 0) % 16)
    let ref := refRun K 0 0
    unless outs == ref do throwError "run {outs} differs from the reference {ref}"
    logInfo m!"RUN tops (depth 2, runHSR on the real design): out = {outs} = reference {ref}"

-- the closed run at DEPTH 3, evaluated, against a hand-written reference
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``tops2
  let arr : Sparkle.IR.AST.Module → List Stmt := fun c => orderBodyH d c.body
  let K := 6
  let a := [3, 1, 4, 1, 5, 9]
  let b := [2, 7, 1, 8, 2, 8]
  let ins : Nat → String → Nat := fun t n =>
    if n == "_gen_a" then a.getD t 0 else if n == "_gen_b" then b.getD t 0 else 0
  match runHSR d arr m (seedFwd m K ins) K (st0HR d m) with
  | none => throwError "the closed run of the depth-3 design failed"
  | some envs =>
    let outs := envs.map (fun e => e "out")
    let rec refRun : Nat → Nat → Nat → Nat → List Nat
      | 0, _, _, _ => []
      | k + 1, rl, rm, r2 =>
        let t := K - (k + 1)
        r2 :: refRun k ((rl + a.getD t 0) % 16) ((rm + rl + b.getD t 0) % 16) ((r2 + rm) % 16)
    let ref := refRun K 0 0 0
    unless outs == ref do throwError "run {outs} differs from the reference {ref}"
    logInfo m!"RUN tops2 (depth 3, runHSR on the real design): out = {outs} = reference {ref}"

/-! ## Controls through the checker on edited `(m, d)` (option-independent: `checkU2HN` itself) -/

def ctlN (what : String) (decl : Name) (stage : String) (needle : String) (m : Sparkle.IR.AST.Module) (d : Design) :
    CommandElabM Unit := do
  let before ← localConsts
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  let r ← try
      discard <| Tools.VedU2HierRecEntry.checkU2HN midEntryN decl stmt nDom m d none
      pure none
    catch e => pure (some (← liftTermElabM (e.toMessageData.toString)))
  match r with
  | none => throwError "{what}: expected a refusal, the checker ACCEPTED"
  | some msg =>
    unless msg.startsWith s!"VED U1 REFUSED {decl} [{stage}]" do
      throwError "{what}: expected a refusal at [{stage}], got: {msg.take 400}"
    unless needle == "" || (msg.splitOn needle).length > 1 do throwError "{what}: the refusal does not name `{needle}`: {msg.take 400}"
    let added := (← localConsts).toList.filter (!before.contains ·)
    unless added.isEmpty do throwError "{what}: constants left after the refusal: {added}"
    logInfo m!"CONTROL {what}: {msg.take 300}"

def midName : String := "Tests.Ved.RecEntry.mids"

-- (a) the top's output is NOT the middle module's output
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topsC1
  let b := m.body.map fun s => match s with
    | .assign "out" _ => .assign "out" (.ref "_gen_a")
    | s => s
  ctlN "(a) output of the parent is not the middle module's output" ``topsC1 "proof" "" { m with body := b } d

-- (b) the two data inputs of the middle module swapped in the parent (same widths: the shape passes, only the proof refuses)
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topsC2
  let b := setConnAt 0 "_gen_y" (.ref "_gen_a") (setConnAt 0 "_gen_x" (.ref "_gen_b") m.body)
  ctlN "(b) middle module's inputs swapped in the parent" ``topsC2 "open" "no call of" { m with body := b } d

-- (c) a SAME-NAME but different middle module (its register's initial value): the stored theorem must not be used
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topsC3
  let mods := d.modules.map fun x =>
    if x.name == midName then
      { x with body := x.body.map fun s => match s with
          | .register o c r e _ => .register o c r e 1
          | s => s }
    else x
  ctlN "(c) same-name different middle module (stored theorem refused)" ``topsC3 "child" "same name, different module"
    m { d with modules := mods }

-- (d) a wrong instance path: two instances with the same name
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topsC4
  let inst := m.body.filter fun s => match s with | .inst .. => true | _ => false
  ctlN "(d) duplicate instance name" ``topsC4 "hier-shape" "HierShapeR" { m with body := m.body ++ inst } d

-- (f) the GRANDCHILD edited (same name, other register initial value): the middle module's stored design no longer
-- lies in the parent's design (by value); the stored theorem is refused
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topsC5
  let mods := d.modules.map fun x =>
    if x.name == "Tests.Ved.RecEntry.leafs" then
      { x with body := x.body.map fun s => match s with
          | .register o c r e _ => .register o c r e 1
          | s => s }
    else x
  ctlN "(f) same-name different GRANDCHILD (stored theorem refused)" ``topsC5 "child" "not a module of the parent's design"
    m { d with modules := mods }

-- (g) depth 3: the middle module of the middle module edited (same name): refused the same way
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topsC6
  let mods := d.modules.map fun x =>
    if x.name == midName then
      { x with body := x.body.map fun s => match s with
          | .register o c r e _ => .register o c r e 1
          | s => s }
    else x
  ctlN "(g) depth 3: same-name different inner middle module" ``topsC6 "child" "not a module of the parent's design"
    m { d with modules := mods }

-- (h) a parent WITH a register, option on: the register's next-state expression changed (add -> sub): refused at [proof]
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topsC7
  let (stmt, nDom) ← liftTermElabM (specialiseDomain ``topsC7)
  let before ← localConsts
  let b := m.body.map fun s => match s with
    | .assign l (.op .add args) => .assign l (.op .sub args)
    | s => s
  let r ← try
      discard <| withNested (checkU2HR ``topsC7 stmt nDom { m with body := b } d none)
      pure none
    catch e => pure (some (← liftTermElabM (e.toMessageData.toString)))
  match r with
  | none => throwError "(h): expected a refusal, the checker ACCEPTED"
  | some msg =>
    unless msg.startsWith "VED U1 REFUSED Tests.Ved.RecEntry.topsC7 [" do throwError "(h): unexpected: {msg.take 300}"
    let added := (← localConsts).toList.filter (!before.contains ·)
    unless added.isEmpty do throwError "(h): constants left: {added}"
    logInfo m!"CONTROL (h) register parent, next-state expression changed: {msg.take 200}"

-- (e) option OFF: the old refusal, text unchanged
#eval show CommandElabM Unit from do
  let before ← localConsts
  let r ← try
      discard <| vedU2HierEntryR ``topsOff
      pure "ACCEPTED"
    catch e => liftTermElabM (e.toMessageData.toString)
  let exp := "VED U1 REFUSED Tests.Ved.RecEntry.topsOff [hier-shape]: instance _tmp_inst_Tests.Ved.RecEntry.mids_0: child Tests.Ved.RecEntry.mids is not a leaf (memory or instance in its body: depth 1 only)"
  unless r == exp do throwError "option off: the refusal changed: {r}"
  let added := (← localConsts).toList.filter (!before.contains ·)
  unless added.isEmpty do throwError "constants left: {added}"
  logInfo m!"CONTROL (e) option off: {r}"

/-! ## Probe: a STRUCT middle module (multi-output hierarchical parent) is not supported by the entry -/

structure Pn (dom : DomainConfig) where
  s : Signal dom (BitVec 4)
  d : Signal dom (BitVec 4)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (Pn dom) dom := ⟨⟩

@[hardware_module] def midq (x y : Signal defaultDomain (BitVec 4)) : Pn defaultDomain :=
  circuit do
    let r ← Signal.reg 0#4
    let c := leafs x
    r <~ r + c + y
    return ({ s := r, d := c } : Pn defaultDomain)

def topq (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  let c := midq a b
  c.s - c.d

#eval show CommandElabM Unit from do
  let r ← try
      discard <| withNested (vedU2HierEntryR ``topq)
      pure "ACCEPTED"
    catch e => liftTermElabM (e.toMessageData.toString)
  logInfo m!"PROBE struct middle module under the option: {r.take 500}"

-- the struct middle module as a PARENT of its own entry (multiOut on): the first refusal
#eval show CommandElabM Unit from do
  let r ← try
      discard <| withScope (fun sc => { sc with opts := sc.opts.setBool `ved.compose.multiOut true }) (vedU2HierEntryR ``midq)
      pure "ACCEPTED"
    catch e => liftTermElabM (e.toMessageData.toString)
  logInfo m!"PROBE struct middle module as a parent, multiOut on: {r.take 500}"

end Tests.Ved.RecEntry

-- axioms of the new theorems (observed)
#print axioms Tools.VedU2HierRec.runHSR_exists
#print axioms Tools.VedU2HierRec.succF_of_step
#print axioms Tools.VedU2HierRec.outputsOnHSR_of_stepRKH
#print axioms Tools.VedU2HierRec.outputsOnHSR_of_oracle
#print axioms Tools.VedU2HierRec.exists_arrHR
#print axioms Tools.VedU2HierRec.succF_of_theoremR
#print axioms Tools.VedU2HierRec.kid_inst_R
#print axioms Tools.VedU2HierRec.U2HRStmtR_of_S
#print axioms Tests.Ved.RecEntry.tops.ved_u1
#print axioms Tests.Ved.RecEntry.mids.ved_u2r

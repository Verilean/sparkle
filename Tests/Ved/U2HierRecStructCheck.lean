import Tools.VedU2HierRegEntry
import Tools.VedU2HierRecEntry
import Tools.VedU2HierRecCausal
import Tests.Ved.ComposeCheckUtil
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# The STRUCT middle module through the nested entry (CANDIDATE; Tools/VedU2HierRec*.lean; observed, single runs)

NOT a ledger row.  A depth-2 design through `#ved_u2_hier` with `ved.compose.multiOut` and `ved.compose.nested` ON:

* `leafs` (one register, `r' = r + x`) <- `midq` (a STRUCT result `{ s := r, d := leafs x }`: two output ports, a register of its
  own, an instance of `leafs`) <- `topqr` (a parent WITH a register, `acc' = acc + (c.s - c.d)`, the middle module's data input
  `x` is the parent's REGISTER `acc`).
* the middle module's own entry runs first (the multi-output hierarchical PARENT entry: the struct result read through
  `stmtOfStruct`, contract outputs `["s", "d"]`, per-port deep facts), its stored theorem `midq.ved_u1` is `U2HRStmtK` over the
  sub-design `[leafs]` and is turned into `U2HRStmtR` (`U2HRStmtR_iff_K`); the parent consumes it through the register-fed
  instance route (`kid_seq_R`, `outputsOnHSR_of_stepRKH`), port by port;
* the stored type is `U2HRStmtR contract mod design decl`, the artifact is the declaration's own synthesis, the axioms are the
  standard three, the middle module's theorem constant occurs in the proof, and the grandchild's constants do not occur in the
  proof's DIRECT constants (not a closure audit);
* CONTROLS through the checker (`checkU2HR`) on edited `(m, d)`, both options on: the two outputs of `midq` swapped in the
  parent (the observation is the asymmetric `s - d`), a wrong port fed to one consumer, a same-NAME but different middle module
  (the stored theorem is refused by the cache check), the option OFF (the old refusal text).
-/

namespace Tests.Ved.RecStruct

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

structure Pn (dom : DomainConfig) where
  s : Signal dom (BitVec 4)
  d : Signal dom (BitVec 4)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (Pn dom) dom := ⟨⟩

/-- the STRUCT middle module: two outputs, a register of its own, an instance of `leafs` -/
@[hardware_module] def midq (x y : Signal defaultDomain (BitVec 4)) : Pn defaultDomain :=
  circuit do
    let r ← Signal.reg 0#4
    let c := leafs x
    r <~ r + c + y
    return ({ s := r, d := c } : Pn defaultDomain)

/-- the parent: a register, the middle module fed from the parent's register `acc` and a data input, the ASYMMETRIC observation `s - d` -/
def topqr (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := midq accS b
    acc <~ (accS + (c.s - c.d) : Signal defaultDomain (BitVec 4))
    return accS

-- copies for the controls (each control needs its own constants)
def topqC1 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := midq accS b
    acc <~ (accS + (c.s - c.d) : Signal defaultDomain (BitVec 4))
    return accS
def topqC2 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := midq accS b
    acc <~ (accS + (c.s - c.d) : Signal defaultDomain (BitVec 4))
    return accS
def topqC3 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := midq accS b
    acc <~ (accS + (c.s - c.d) : Signal defaultDomain (BitVec 4))
    return accS
def topqC4 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := midq accS b
    acc <~ (accS + (c.s - c.d) : Signal defaultDomain (BitVec 4))
    return accS

def withBoth {α : Type} (act : CommandElabM α) : CommandElabM α :=
  withScope (fun sc => { sc with opts := (sc.opts.setBool `ved.compose.nested true).setBool `ved.compose.multiOut true }) act

def expectedR (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``U2HRStmtR) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

-- the nested entry, both options ON
set_option ved.compose.multiOut true in
set_option ved.compose.nested true in
#ved_u2_hier topqr

/-- the accepted theorem, read independently of the entry -/
def acceptedS (decl midThm : Name) : CommandElabM Unit := do
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
    -- (`leafs.match_1` is a Lean MATCHER, shared by every `circuit do` of this file through the matcher cache: not the grandchild's body)
    let env ← getEnv
    let gc := used.filter fun n => (n.toString.splitOn "RecStruct.leafs").length > 1 && !(Lean.Meta.isMatcherCore env n)
    unless gc.isEmpty do throwError "{nm.thm}: grandchild constants occur directly: {gc}"
    discard <| Tools.VedStrictAudit.strictAudit nm.thm
    logInfo m!"ACCEPTED {decl}: U2HRStmtR type ==, same artifact, std3, kernel, {midThm} occurs, no grandchild constant among the {used.size} direct constants (NOT a closure audit)"

#eval acceptedS ``topqr `Tests.Ved.RecStruct.midq.ved_u2r

-- the middle module's OWN theorem: the struct result read as two ports, `U2HRStmtR` over the sub-design `[leafs]`
#eval show CommandElabM Unit from do
  -- the middle module's own entry ran on the module VALUE of the PARENT's design and its sub-design (the standalone synthesis of
  -- `midq` names its temporaries by a different counter)
  let (_, dTop) ← synthOf ``topqr
  let some mq := dTop.modules.find? (·.name == "Tests.Ved.RecStruct.midq") | throwError "no midq in the parent's design"
  let dq := Tools.VedU2HierRecEntry.subDesignOf dTop mq
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? `Tests.Ved.RecStruct.midq.ved_u2r | throwError "no midq.ved_u2r"
    unless ti.type.getAppFn.isConstOf ``U2HRStmtR do throwError "midq.ved_u2r is not U2HRStmtR"
    let some (.thmInfo tk) := (← getEnv).find? `Tests.Ved.RecStruct.midq.ved_u1 | throwError "no midq.ved_u1"
    unless tk.type.getAppFn.isConstOf ``U2HRStmtK do throwError "midq.ved_u1 is not U2HRStmtK"
    let some ci := (← getEnv).find? `Tests.Ved.RecStruct.midq.ved_mod | throwError "midq.ved_mod missing"
    unless ci.value! == toExpr mq do throwError "midq.ved_mod is not the parent's module value of midq"
    let some di := (← getEnv).find? `Tests.Ved.RecStruct.midq.ved_design | throwError "midq.ved_design missing"
    unless di.value! == toExpr dq do throwError "midq.ved_design is not the sub-design of midq in the parent's design"
    unless mq.outputs.map (·.name) == ["s", "d"] do throwError "midq's output ports are {mq.outputs.map (·.name)}"
    std3Only `Tests.Ved.RecStruct.midq.ved_u2r
    logInfo m!"MIDQ: ved_u1 : U2HRStmtK, ved_u2r : U2HRStmtR over {dq.modules.map (·.name)}, ports {mq.outputs.map (·.name)}, the module is the parent's by value, the design its sub-design, std3"

-- the closed run of the parent's real design (the nested semantics), evaluated, against a hand-written reference
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topqr
  let arr : Sparkle.IR.AST.Module → List Stmt := fun c => orderBodyH d c.body
  let K := 7
  let b := [2, 7, 1, 8, 2, 8, 3]
  let ins : Nat → String → Nat := fun t n => if n == "_gen_b" then b.getD t 0 else 0
  match runHSR d arr m (seedFwd m K ins) K (st0HR d m) with
  | none => throwError "the closed run of the nested design failed"
  | some envs =>
    let outs := envs.map (fun e => e "out")
    -- state (acc, r, lr): out = acc; s = r; d = lr; acc' = acc + (r - lr); r' = r + lr + b; lr' = lr + acc
    let rec refRun : Nat → Nat → Nat → Nat → List Nat
      | 0, _, _, _ => []
      | k + 1, acc, r, lr =>
        let t := K - (k + 1)
        acc :: refRun k ((acc + (r + 16 - lr)) % 16) ((r + lr + b.getD t 0) % 16) ((lr + acc) % 16)
    let ref := refRun K 0 0 0
    unless outs == ref do throwError "run {outs} differs from the reference {ref}"
    logInfo m!"RUN topqr (depth 2, struct middle module, runHSR on the real design): out = {outs} = reference {ref}"

/-! ## Controls through the entry's checker `checkU2HR` on edited `(m, d)` -/

def ctlS (what : String) (decl : Name) (stage : String) (needle : String) (m : Sparkle.IR.AST.Module) (d : Design)
    (both : Bool := true) : CommandElabM Unit := do
  let before ← localConsts
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  let r ← try
      discard <| (if both then withBoth else id) (checkU2HR decl stmt nDom m d none)
      pure none
    catch e => pure (some (← liftTermElabM (e.toMessageData.toString)))
  match r with
  | none => throwError "{what}: expected a refusal, the checker ACCEPTED"
  | some msg =>
    unless msg.startsWith s!"VED U1 REFUSED {decl} [{stage}]" do
      throwError "{what}: expected a refusal at [{stage}], got: {msg.take 500}"
    unless needle == "" || (msg.splitOn needle).length > 1 do throwError "{what}: the refusal does not name `{needle}`: {msg.take 500}"
    let added := (← localConsts).toList.filter (!before.contains ·)
    unless added.isEmpty do throwError "{what}: constants left after the refusal: {added}"
    logInfo m!"CONTROL {what}: {msg.take 300}"

/-- swap two wires in the connections of the instances of `midq` -/
def swapPorts (b : List Stmt) : List Stmt :=
  b.map fun s => match s with
    | .inst mn i cs => .inst mn i (cs.map fun q =>
        if q.1 == "s" then ("s", q.2) else q)
    | s => s

-- (a) the two OUTPUTS of `midq` swapped in the parent: the instance's `s` port is read as the `d` wire and vice versa
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topqC1
  let b := m.body.map fun s => match s with
    | .inst mn i cs =>
      let ws := cs.lookup "s"
      let wd := cs.lookup "d"
      .inst mn i (cs.map fun q =>
        if q.1 == "s" then ("s", wd.getD q.2) else if q.1 == "d" then ("d", ws.getD q.2) else q)
    | s => s
  ctlS "(a) the two outputs of midq swapped in the parent" ``topqC1 "proof" "" { m with body := b } d

-- (b) a WRONG PORT fed to one consumer: `s - d` reads `s` twice
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topqC2
  let sw := (m.body.filterMap fun s => match s with
    | .inst _ _ cs => cs.lookup "s"
    | _ => none).head!
  let b := m.body.map fun s => match s with
    | .assign l (.op .sub [x, _]) => .assign l (.op .sub [x, x])
    | s => s
  let _ := sw
  ctlS "(b) a wrong port fed to one consumer (s - s)" ``topqC2 "proof" "" { m with body := b } d

-- (c) a SAME-NAME but different middle module (its register's initial value): the stored theorem must not be used
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topqC3
  let mods := d.modules.map fun x =>
    if x.name == "Tests.Ved.RecStruct.midq" then
      { x with body := x.body.map fun s => match s with
          | .register o c r e _ => .register o c r e 1
          | s => s }
    else x
  ctlS "(c) same-name different middle module (stored theorem refused)" ``topqC3 "child" "same name, different module"
    m { d with modules := mods }

-- (d) the option OFF: the old refusal, exactly (the struct middle module is not read)
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topqC4
  ctlS "(d) both options OFF" ``topqC4 "hier-shape" "" m d (both := false)

def topqC5 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := midq accS b
    acc <~ (accS + (c.s - c.d) : Signal defaultDomain (BitVec 4))
    return accS

/-- the entry's refusal text of `decl` under the given scope options (nothing may be left behind) -/
def refusalOf (decl : Name) (opts : Lean.Options → Lean.Options) : CommandElabM String := do
  let before ← localConsts
  let r ← try
      discard <| withScope (fun sc => { sc with opts := opts sc.opts }) (vedU2HierEntryR decl)
      pure "ACCEPTED"
    catch e => liftTermElabM (e.toMessageData.toString)
  let added := (← localConsts).toList.filter (!before.contains ·)
  unless added.isEmpty do throwError "{decl}: constants left after the refusal: {added}"
  return r

-- (e) the struct middle module as a PARENT of its own entry, both options OFF: the old `[table]` text, exactly
#eval show CommandElabM Unit from do
  let r ← refusalOf ``midq id
  let want := "VED U1 REFUSED Tests.Ved.RecStruct.midq [table]: ved_table%: Tests.Ved.RecStruct.Pn\n  Sparkle.Core.Domain.defaultDomain is not a Signal defaultDomain _ (v1: Signal binders only)"
  unless r == want do throwError "(e) the refusal text changed: {r}"
  logInfo m!"CONTROL (e) midq as a parent, options off: the old [table] text, exactly"

-- (f) `ved.compose.nested` ON, `ved.compose.multiOut` OFF: the old `[child]` refusal of the struct middle module
#eval show CommandElabM Unit from do
  let r ← refusalOf ``topqC5 (fun o => o.setBool `ved.compose.nested true)
  unless r.startsWith "VED U1 REFUSED Tests.Ved.RecStruct.topqC5 [child]: middle module Tests.Ved.RecStruct.midq: ved_table%: Tests.Ved.RecStruct.Pn" do
    throwError "(f) unexpected: {r.take 400}"
  logInfo m!"CONTROL (f) nested on, multiOut off: {r.take 260}"

end Tests.Ved.RecStruct

#print axioms Tools.VedU2HierRec.runHSR_congr_seed
#print axioms Tools.VedU2HierRec.srcOf_prefix_R
#print axioms Tools.VedU2HierRec.call_causal_R
#print axioms Tools.VedU2HierRec.bundle_causal_agree_R
#print axioms Tests.Ved.RecStruct.topqr.ved_u1
#print axioms Tests.Ved.RecStruct.midq.ved_u2r

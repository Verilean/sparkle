import Tools.VedU2HierRegEntry
import Tools.VedU2HierRecEntry
import Tools.VedU2HierRecLeaf
import Tests.Ved.ComposeCheckUtil
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# A LEAF direct child next to a STRUCT middle module (CANDIDATE; Tools/VedU2HierRecLeaf.lean; observed, single runs)

NOT a ledger row.  The R163 SHAPE: a parent with a register whose instances are a struct middle module AND a leaf that is also the
middle module's own grandchild, through `#ved_u2_hier` with `ved.compose.multiOut` and `ved.compose.nested` ON.

* `cl` (combinational leaf, `x + 3`) <- `midc` (STRUCT `{ s := r, d := cl x }`, one register) <- `topc` (a register `acc`,
  `acc' = acc + (c.s - c.d) + cl b`: the middle module is fed from the parent's REGISTER, the leaf directly from the data input);
  `topc2` feeds the direct leaf from the register too (`cl (acc + b)`);
* `leafs` (sequential leaf, one register) <- `midq` (struct) <- `topls` (`acc' = acc + (c.s - c.d) + leafs b`).
* the leaf direct child's theorem is its own `U1Stmt` (the ordinary child stage of the entry), the parent consumes it through
  `kid_seq_RL` (state path `i :: p` = the child's own state at `p`), its success through `succF_of_leaf`; the middle module's theorem
  is its own `U2HRStmtR` over its sub-design.
* CONTROLS (checker on edited `(m, d)`; nothing left behind): the leaf's output wire swapped with the middle module's port wire, a
  same-NAME different leaf (edited in the design), the options OFF (old text).
-/

namespace Tests.Ved.RecLeaf

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil
open Tools.VedU1HierEntry Tools.VedU2HierRec

/-- a COMBINATIONAL leaf -/
@[hardware_module] def cl (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  (x + (Signal.pure 3#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))

/-- a SEQUENTIAL leaf -/
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

/-- the STRUCT middle module over the combinational leaf -/
@[hardware_module] def midc (x y : Signal defaultDomain (BitVec 4)) : Pn defaultDomain :=
  circuit do
    let r ← Signal.reg 0#4
    let c := cl x
    r <~ r + c + y
    return ({ s := r, d := c } : Pn defaultDomain)

/-- the STRUCT middle module over the sequential leaf -/
@[hardware_module] def midq (x y : Signal defaultDomain (BitVec 4)) : Pn defaultDomain :=
  circuit do
    let r ← Signal.reg 0#4
    let c := leafs x
    r <~ r + c + y
    return ({ s := r, d := c } : Pn defaultDomain)

/-- R163 shape, combinational leaf: the leaf `cl` is a direct child (fed from the data input) AND the middle module's grandchild -/
def topc (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := midc accS b
    let e := cl b
    acc <~ (accS + (c.s - c.d) + e : Signal defaultDomain (BitVec 4))
    return accS

/-- the direct leaf fed from the parent's REGISTER -/
def topc2 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := midc accS b
    let e := cl (accS + b : Signal defaultDomain (BitVec 4))
    acc <~ (accS + (c.s - c.d) + e : Signal defaultDomain (BitVec 4))
    return accS

/-- the SEQUENTIAL leaf variant -/
def topls (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := midq accS b
    let e := leafs b
    acc <~ (accS + (c.s - c.d) + e : Signal defaultDomain (BitVec 4))
    return accS

-- copies for the controls (each control needs its own constants)
/-- (the observation `(s - d) - e` is NOT symmetric in `s` and `e`: swapping the leaf's output with the middle module's `s` changes it) -/
def topcC1 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := midc accS b
    let e := cl b
    acc <~ (accS + (c.s - c.d) - e : Signal defaultDomain (BitVec 4))
    return accS
def topcC2 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := midc accS b
    let e := cl b
    acc <~ (accS + (c.s - c.d) + e : Signal defaultDomain (BitVec 4))
    return accS
def topcC3 (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := midc accS b
    let e := cl b
    acc <~ (accS + (c.s - c.d) + e : Signal defaultDomain (BitVec 4))
    return accS

def withBoth {α : Type} (act : CommandElabM α) : CommandElabM α :=
  withScope (fun sc => { sc with opts := (sc.opts.setBool `ved.compose.nested true).setBool `ved.compose.multiOut true }) act

def expectedR (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``U2HRStmtR) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

set_option ved.compose.multiOut true in
set_option ved.compose.nested true in
#ved_u2_hier topc

set_option ved.compose.multiOut true in
set_option ved.compose.nested true in
#ved_u2_hier topc2

set_option ved.compose.multiOut true in
set_option ved.compose.nested true in
#ved_u2_hier topls

/-- the accepted theorem, read independently of the entry: the type, the artifact, std3, kernel, the middle module's theorem occurs, the
leaf's own theorem (`<decl>.ved_child.<leaf>.ved_u1`) occurs -/
def acceptedL (decl midThm leafThm : Name) (leafName : String) : CommandElabM Unit := do
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
    unless used.contains leafThm do throwError "{nm.thm}: the leaf child's theorem {leafThm} does not occur"
    unless used.contains ``Tools.VedU2HierRec.kid_seq_RL || used.contains ``Tools.VedU2HierRec.kid_inst_RL do
      throwError "{nm.thm}: neither kid_seq_RL nor kid_inst_RL occurs"
    discard <| Tools.VedStrictAudit.strictAudit nm.thm
    -- the leaf's own theorem is about THE leaf module of the parent's real design (by value), through the module the design resolves
    let some (.thmInfo tl) := (← getEnv).find? leafThm | throwError "{leafThm} is not a theorem"
    unless tl.type.getAppFn.isConstOf ``U1Stmt do throwError "{leafThm} is not a U1Stmt"
    let largs := tl.type.getAppArgs
    let some lmC := largs[1]? | throwError "{leafThm}: unexpected arity"
    let some lmI := (← getEnv).find? lmC.constName! | throwError "{lmC} missing"
    let some lmod := d.modules.find? (·.name == leafName) | throwError "no module {leafName} in the parent's design"
    unless lmI.value! == toExpr lmod do throwError "{lmC} is not the leaf module of the parent's design (by value)"
    unless (findMod d leafName).isSome && (findMod d leafName) == some lmod do throwError "findMod d {leafName} is not the leaf module"
    logInfo m!"ACCEPTED {decl}: U2HRStmtR type ==, same artifact, std3, kernel, {midThm} and {leafThm} occur, kid_seq_RL used ({used.size} direct constants); {leafThm} is a U1Stmt over the leaf module of the real design (by value, findMod agrees)"

#eval acceptedL ``topc `Tests.Ved.RecLeaf.midc.ved_u2r `Tests.Ved.RecLeaf.topc.ved_child.Tests.Ved.RecLeaf.cl.ved_u1 "Tests.Ved.RecLeaf.cl"
#eval acceptedL ``topc2 `Tests.Ved.RecLeaf.midc.ved_u2r `Tests.Ved.RecLeaf.topc2.ved_child.Tests.Ved.RecLeaf.cl.ved_u1 "Tests.Ved.RecLeaf.cl"
#eval acceptedL ``topls `Tests.Ved.RecLeaf.midq.ved_u2r `Tests.Ved.RecLeaf.topls.ved_child.Tests.Ved.RecLeaf.leafs.ved_u1 "Tests.Ved.RecLeaf.leafs"

-- the closed run of the parent's real design (the nested semantics), against a hand-written reference
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topc
  let arr : Sparkle.IR.AST.Module → List Stmt := fun c => orderBodyH d c.body
  let K := 7
  let b := [2, 7, 1, 8, 2, 8, 3]
  let ins : Nat → String → Nat := fun t n => if n == "_gen_b" then b.getD t 0 else 0
  match runHSR d arr m (seedFwd m K ins) K (st0HR d m) with
  | none => throwError "the closed run of the leaf-next-to-middle design failed"
  | some envs =>
    let outs := envs.map (fun e => e "out")
    -- state (acc, r); out = acc; cl x = x + 3; midc: s = r, d = acc + 3, r' = r + (acc + 3) + b; acc' = acc + (s - d) + (b + 3)
    let rec refRun : Nat → Nat → Nat → List Nat
      | 0, _, _ => []
      | k + 1, acc, r =>
        let t := K - (k + 1)
        let y := b.getD t 0
        let dd := (acc + 3) % 16
        acc :: refRun k ((acc + (r + 16 - dd) + (y + 3)) % 16) ((r + dd + y) % 16)
    let ref := refRun K 0 0
    unless outs == ref do throwError "run {outs} differs from the reference {ref}"
    logInfo m!"RUN topc (leaf next to a struct middle module, runHSR on the real design): out = {outs} = reference {ref}"

-- the sequential-leaf variant: the leaf's OWN state lives at the path `[leafInstance]` of the parent's state (state: acc, r, lr, le)
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topls
  let arr : Sparkle.IR.AST.Module → List Stmt := fun c => orderBodyH d c.body
  let K := 7
  let b := [2, 7, 1, 8, 2, 8, 3]
  let ins : Nat → String → Nat := fun t n => if n == "_gen_b" then b.getD t 0 else 0
  match runHSR d arr m (seedFwd m K ins) K (st0HR d m) with
  | none => throwError "the closed run of the sequential-leaf design failed"
  | some envs =>
    let outs := envs.map (fun e => e "out")
    -- midq: lr' = lr + acc, r' = r + lr + b, s = r, d = lr; the direct leaf: le' = le + b, e = le; acc' = acc + (s - d) + e
    let rec refRun : Nat → Nat → Nat → Nat → Nat → List Nat
      | 0, _, _, _, _ => []
      | k + 1, acc, r, lr, le =>
        let t := K - (k + 1)
        let y := b.getD t 0
        acc :: refRun k ((acc + (r + 16 - lr) + le) % 16) ((r + lr + y) % 16) ((lr + acc) % 16) ((le + y) % 16)
    let ref := refRun K 0 0 0 0
    unless outs == ref do throwError "run {outs} differs from the reference {ref}"
    logInfo m!"RUN topls (sequential leaf next to a struct middle module, runHSR on the real design): out = {outs} = reference {ref}"

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

/-- rewrite every sub-expression bottom-up -/
partial def mapE (f : Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr) : Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr
  | .op o args => f (.op o (args.map (mapE f)))
  | .concat args => f (.concat (args.map (mapE f)))
  | .slice e hi lo => f (.slice (mapE f e) hi lo)
  | e => f e

-- (a) the leaf's output and the middle module's `s` port SWAPPED in the parent's consumers: every read of the leaf's output wire reads
-- the middle module's port wire and vice versa (the asymmetric observation `s - d + e` changes)
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topcC1
  let outW (mn : String) (p : String) : Option String := m.body.findSome? fun s => match s with
    | .inst mn' _ cs => if mn' == mn then (match cs.lookup p with | some (.ref x) => some x | _ => none) else none
    | _ => none
  let some wl := outW "Tests.Ved.RecLeaf.cl" "out" | throwError "no leaf output wire"
  let some ws := outW "Tests.Ved.RecLeaf.midc" "s" | throwError "no middle module s wire"
  let sw : Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr := fun e => match e with
    | .ref x => if x == wl then .ref ws else if x == ws then .ref wl else e
    | e => e
  let b := m.body.map fun s => match s with
    | .assign l r => .assign l (mapE sw r)
    | s => s
  ctlS "(a) the leaf's output swapped with the middle module's" ``topcC1 "proof" "" { m with body := b } d

-- (b) a SAME-NAME but different leaf (edited in the design: every constant `3` of `cl` becomes `5`): the leaf's own theorem and the
-- middle module's theorem are about the declaration, so nothing may be accepted
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topcC2
  let c5 : Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr := fun e => match e with
    | .const 3 w => .const 5 w
    | e => e
  let mods := d.modules.map fun x =>
    if x.name == "Tests.Ved.RecLeaf.cl" then
      { x with body := x.body.map fun s => match s with
          | .assign l r => .assign l (mapE c5 r)
          | s => s }
    else x
  if mods == d.modules then throwError "(b) the edit changed nothing"
  ctlS "(b) same-name different leaf" ``topcC2 "child" "" m { d with modules := mods }

-- (c) the options OFF: the old refusal (`hier-shape`), nothing left behind
#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topcC3
  ctlS "(c) both options OFF" ``topcC3 "hier-shape" "" m d (both := false)

end Tests.Ved.RecLeaf

#print axioms Tools.VedU2HierRec.runIn_leaf
#print axioms Tools.VedU2HierRec.WOH_of_WO_leaf
#print axioms Tools.VedU2HierRec.succF_of_leaf
#print axioms Tools.VedU2HierRec.kid_seq_RL
#print axioms Tools.VedU2HierRec.kid_inst_RL
#print axioms Tests.Ved.RecLeaf.topc.ved_u1
#print axioms Tests.Ved.RecLeaf.topls.ved_u1

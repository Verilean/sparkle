import Tools.VedU2HierRegEntry
import Tools.VedU2HierRecEntry
import Tools.VedU2HierRecLeaf
import Tools.VedU2HierRecLeafCache
import Tests.Ved.ComposeCheckUtil
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# The ports of one open parent share the register bundle; the leaf cache by value (CANDIDATE; observed, single runs)

NOT a ledger row.

**`sparkle.deepShareRegs` (Tools/DeepElab.lean, default off)**.  A struct middle module with four registers and three ports goes
through `#ved_u2_hier` (`ved.compose.multiOut` + `ved.compose.nested`) with the option ON: the middle module's own entry runs the deep
run of its open parent, whose ports after the first reuse the first port's register arms (`_deep` = `⟨inits, next of port 0, own out⟩`),
the first port's `_deep_next` / `_deep_inits` statements (constant renamed), the first port's readers (aliases) and their `_zero` /
`_succ` lemmas.  Read back here: the accepted theorem (type `U2HRStmtR`, same artifact, std3, kernel, strict audit), the port theorems
`_deep_trace` of the open parent exist for every port, the later ports' `_deep_next` type IS the first port's with the Cdo constant
renamed, and the later ports' `_deep_rd<i>_succ` proofs are the first port's constants.

**`ved.compose.leafCache` (Tools/VedU2HierRecLeafCache.lean, default off)**.  The R163 shape (the leaf `cl` is a direct child of the
parent AND the middle module's grandchild): with the option ON the parent's direct-leaf child reuses the theorem the middle module's
entry produced under `<mid>.ved_child.<leaf>` (no `<top>.ved_child.<leaf>` theorem is produced; the accepted theorem uses the stored
one).  The finder is checked by value: the same module and statement hit; the same-NAME different leaf (a constant edited), and a
different statement, do not.
-/

namespace Tests.Ved.RecShare

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil
open Tools.VedU1HierEntry Tools.VedU2HierRec

@[hardware_module] def cl (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  (x + (Signal.pure 3#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))

@[hardware_module] def leafs (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let r ← Signal.reg 0#4
    r <~ r + x
    return r

#verify_elab_deep leafs

structure Q3 (dom : DomainConfig) where
  s0 : Signal dom (BitVec 4)
  s1 : Signal dom (BitVec 4)
  s2 : Signal dom (BitVec 4)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (Q3 dom) dom := ⟨⟩

/-- four registers, three ports (the registers on the left of every sum), one leaf instance -/
@[hardware_module] def midq (x y : Signal defaultDomain (BitVec 4)) : Q3 defaultDomain :=
  circuit do
    let r0 ← Signal.reg 0#4
    let r1 ← Signal.reg 0#4
    let r2 ← Signal.reg 0#4
    let r3 ← Signal.reg 0#4
    let c := leafs x
    r0 <~ r0 + r3 + c
    r1 <~ r1 + r0 + y
    r2 <~ r2 + r1 + y
    r3 <~ r3 + r2 + y
    return ({ s0 := r0, s1 := r1, s2 := r2 } : Q3 defaultDomain)

def topq (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := midq accS b
    acc <~ (accS + c.s0 + c.s1 + c.s2 : Signal defaultDomain (BitVec 4))
    return accS

structure Pn (dom : DomainConfig) where
  s : Signal dom (BitVec 4)
  d : Signal dom (BitVec 4)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (Pn dom) dom := ⟨⟩

/-- the middle module over the combinational leaf `cl` (also a direct child of `topc`) -/
@[hardware_module] def midc (x y : Signal defaultDomain (BitVec 4)) : Pn defaultDomain :=
  circuit do
    let r ← Signal.reg 0#4
    let c := cl x
    r <~ r + c + y
    return ({ s := r, d := c } : Pn defaultDomain)

def topc (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := midc accS b
    let e := cl b
    acc <~ (accS + (c.s - c.d) + e : Signal defaultDomain (BitVec 4))
    return accS

def expectedR (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``U2HRStmtR) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

/-- the accepted theorem, read independently of the entry (type, artifact, std3, kernel, strict audit; the named constants occur) -/
def accepted (decl : Name) (mustUse : List Name) : CommandElabM Unit := do
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
    for c in mustUse do
      unless used.contains c do throwError "{nm.thm}: {c} does not occur"
    discard <| Tools.VedStrictAudit.strictAudit nm.thm
    logInfo m!"ACCEPTED {decl}: U2HRStmtR type ==, same artifact, std3, kernel, strict audit; {mustUse} occur"

/-! ## the register bundle shared across the ports -/

set_option ved.compose.multiOut true in
set_option ved.compose.nested true in
set_option sparkle.deepShareRegs true in
#ved_u2_hier topq

#eval accepted ``topq [`Tests.Ved.RecShare.midq.ved_u2r]

-- the middle module's open parent: the port theorems exist for every port; the later ports reuse the first port's bundle
#eval show CommandElabM Unit from do
  liftTermElabM do
    let env ← getEnv
    let op := `Tests.Ved.RecShare.midq
    let pre (p : String) := op ++ Name.mkSimple s!"ved_open_Tests_Ved_RecShare_midq_{p}_deep"
    -- the open parent's constants are declared by the deep run of the middle module's entry: find them by their suffix
    let names := env.constants.map₂.foldl (fun (acc : List Name) n _ => n :: acc) []
    let find (suffix : String) : Option Name := names.find? fun n => match n with
      | .str _ s => s == suffix
      | _ => false
    let some t0 := find "ved_open_Tests_Ved_RecShare_midq_s0_deep_trace" | throwError "no s0 trace theorem"
    let some t1 := find "ved_open_Tests_Ved_RecShare_midq_s1_deep_trace" | throwError "no s1 trace theorem"
    let some t2 := find "ved_open_Tests_Ved_RecShare_midq_s2_deep_trace" | throwError "no s2 trace theorem"
    let some n0 := find "ved_open_Tests_Ved_RecShare_midq_s0_deep_next" | throwError "no s0 next"
    let some n1 := find "ved_open_Tests_Ved_RecShare_midq_s1_deep_next" | throwError "no s1 next"
    let some d0 := find "ved_open_Tests_Ved_RecShare_midq_s0_deep" | throwError "no s0 deep"
    let some d1 := find "ved_open_Tests_Ved_RecShare_midq_s1_deep" | throwError "no s1 deep"
    let some u0 := find "ved_open_Tests_Ved_RecShare_midq_s0_deep_rd0_succ" | throwError "no s0 rd0_succ"
    let some u1 := find "ved_open_Tests_Ved_RecShare_midq_s1_deep_rd0_succ" | throwError "no s1 rd0_succ"
    let some (.thmInfo tn0) := env.find? n0 | throwError "s0 next is not a theorem"
    let some (.thmInfo tn1) := env.find? n1 | throwError "s1 next is not a theorem"
    -- `_deep_next` of port 1 = port 0's statement with the Cdo constant renamed
    let rn := tn0.type.replace fun e => if e.isConstOf d0 then some (Lean.mkConst d1) else none
    unless rn == tn1.type do throwError "{n1}: its type is not the first port's statement with {d0} renamed to {d1}"
    -- the step lemma of port 1 is the first port's (a constant: no re-elaboration)
    let some (.thmInfo tu1) := env.find? u1 | throwError "s1 rd0_succ is not a theorem"
    unless tu1.value == Lean.mkConst u0 do throwError "{u1}: its proof is not the first port's {u0}"
    -- every port's capstone is a theorem proved (no sorry)
    for t in [t0, t1, t2] do
      let axs ← collectAxioms t
      if axs.contains ``sorryAx then throwError "{t}: sorryAx"
    logInfo m!"SHARE midq: ports s0 s1 s2 each have a trace theorem (no sorry); {n1} = {n0} with {d0} -> {d1}; {u1} := {u0}"

/-! ## the leaf cache by value -/

set_option ved.compose.multiOut true in
set_option ved.compose.nested true in
set_option ved.compose.leafCache true in
#ved_u2_hier topc

-- the parent uses the middle module's stored leaf theorem; its own `ved_child.cl` theorem is not produced
#eval show CommandElabM Unit from do
  let stored := `Tests.Ved.RecShare.midc.ved_child.Tests.Ved.RecShare.cl.ved_u1
  let own := `Tests.Ved.RecShare.topc.ved_child.Tests.Ved.RecShare.cl.ved_u1
  unless (← getEnv).contains stored do throwError "{stored} (the middle module's leaf theorem) is missing"
  if (← getEnv).contains own then throwError "{own} exists: the leaf was proved twice"
  accepted ``topc [`Tests.Ved.RecShare.midc.ved_u2r, stored]

-- the finder: module VALUE and statement; the name alone never hits
#eval show CommandElabM Unit from do
  let stored := `Tests.Ved.RecShare.midc.ved_child.Tests.Ved.RecShare.cl.ved_u1
  let (m, d) ← synthOf ``topc
  let some lmod := d.modules.find? (·.name == "Tests.Ved.RecShare.cl") | throwError "no leaf module"
  liftTermElabM do
    let env ← getEnv
    let some (.thmInfo ti) := env.find? stored | throwError "no stored theorem"
    let stmt := ti.type.getAppArgs[2]!
    let tbl ← readTableOfType `Tests.Ved.RecShare.cl (← inferType stmt)
    let hit ← Tools.VedU2HierRecLeafCache.findStoredLeaf `Tests.Ved.RecShare.cl stmt lmod tbl ["out"] false
    unless hit == some `Tests.Ved.RecShare.midc.ved_child.Tests.Ved.RecShare.cl do throwError "same leaf, same statement: expected a hit, got {hit}"
    -- same NAME, different leaf (the constant 3 becomes 5)
    let c5 : Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr := fun e => match e with
      | .const 3 w => .const 5 w
      | e => e
    let rec mapE (f : Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr) : Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr
      | .op o args => f (.op o (args.map (mapE f)))
      | .concat args => f (.concat (args.map (mapE f)))
      | .slice e hi lo => f (.slice (mapE f e) hi lo)
      | e => f e
    let lmod' := { lmod with body := lmod.body.map fun s => match s with
      | .assign l r => .assign l (mapE c5 r)
      | s => s }
    if lmod' == lmod then throwError "the edit changed nothing"
    let miss ← Tools.VedU2HierRecLeafCache.findStoredLeaf `Tests.Ved.RecShare.cl stmt lmod' tbl ["out"] false
    unless miss.isNone do throwError "same name, different leaf: expected no hit, got {miss}"
    -- a different statement (the sequential leaf's) under the same module
    let miss2 ← Tools.VedU2HierRecLeafCache.findStoredLeaf `Tests.Ved.RecShare.cl (Lean.mkConst `Tests.Ved.RecShare.leafs) lmod tbl ["out"] false
    unless miss2.isNone do throwError "different statement: expected no hit, got {miss2}"
    logInfo m!"LEAF CACHE: hit {hit} (module value + statement); same-name different leaf: no hit; different statement: no hit"

end Tests.Ved.RecShare

#print axioms Tests.Ved.RecShare.topq.ved_u1
#print axioms Tests.Ved.RecShare.topc.ved_u1

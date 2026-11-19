import Tools.VedU2HierRegEntry
import Tools.VedH3ChildTblEntry
import Tools.VedH3ChildEntry
import IP.Net.IPv4
import Tests.Ved.U1EqLutCheck
import Tests.Ved.U2HierWireCheck
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import Sparkle.Core.Lut

/-!
# Checks for the named constant-table leaf route (issue sparkle-ved-hier3-child)

`Tools/VedH3ChildTbl.lean` / `Tools/VedH3ChildTblEntry.lean`: a register-free one-input leaf whose body is
straight-line `const` / alias / `eq`-against-the-input / `mux` statements that the position-skeleton table
route (`tblDataOf?`) does not take, proved from the module's own statements (names, forms, one packed row
per input value, all checked by the kernel) and `decide +kernel` over the input domain against the
declaration's own value.  The hierarchical entries pick it for a combinational child (`childProofSrc`).

The small examples are NOT rows of the 327 inventory.

* POSITIVES, the two shapes of the real rows at the smallest size:
  `ntResp` is `httpRespByte`'s shape (hand-written `Signal.mux (cnt === k) bₖ …` over `let`-bound constants,
  indices starting at 1, constants shared by value, `_gen_b` operand wires, two statements per index),
  `ntLut` is `respByteMux`'s shape (a `kLut!` table with repeated entries: the compiler shares equal
  constants, so the body has fewer statements than the skeleton `4t + 2` of `tblDataOf?`).
  Each is first checked NOT to be taken by `tblDataOf?` and to be read by `ntblDataOf?`; after the entry the
  stored type of the theorem is, as an `Expr` compared with `==`, `U1Stmt c m (@decl defaultDomain)`, its
  axioms are within `propext`, `Classical.choice`, `Quot.sound`, and `<decl>.ved_ntbl` is the data the
  kernel checked.  `ntEmit` is a parent with a counter register whose output is the child's input
  (`#ved_u2_hier`: the child is proved once and its theorem composed with the parent).
* CONTROLS: the checker is run on the REAL module of the positive declaration with ONE piece altered (a
  table constant, two constants exchanged, an index constant, the then/else operands of one `mux`, one
  constant's width); each must be refused at `[proof]` and leave no `ved_*` constant.

## Add-stage chains (`Tools/VedH3ChildChain.lean`, `Tools/VedH3ChildChainEntry.lean`)

`ckSum` is the shape of `tcpHeaderChecksumSig` at the smallest size that exercises every part of the route: a
prelude (two slices of a 32-bit input, a constant word), three `Sparkle.IP.Net.IPv4.onesAdd16Sig` stages (the first with the
shared constants between its halves, two chained stages: the induction step), `~~~` of the last sum, and a
16-bit input read directly as a word.  The leaf is proved by the stage lemmas composed by induction (a stage
uses its sum twice: the generated script's term grows as `2^stages`); the theorem has exactly the type
`U1Stmt c m (@decl defaultDomain)`, standard axioms, and `<decl>.ved_chain` is the data the kernel checked.
`ckParent` is a parent whose instance is the chain leaf (`#ved_u2_hier`).  Controls (one piece of the real
module altered, refused at `[proof]`, no `ved_*` constant left): a constant word changed, a slice reading the
wrong half, a slice narrowed by one bit, the chained operand replaced by a word (the chain is broken),
the final `~~~` dropped, and the module of another chain against this statement.
-/

namespace Tests.Ved.H3ChildCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedH3ChildTblEntry Tests.Ved.U1EqLutCheck
open Tests.Ved.U2HierWireCheck (expectedOf std3Only)

/-! ## Declarations -/

@[inline] def eqN {dom : DomainConfig} (cnt : Signal dom (BitVec 3)) (k : Nat) : Signal dom Bool :=
  cnt === (Signal.pure (BitVec.ofNat 3 k) : Signal dom (BitVec 3))

/-- `httpRespByte`'s shape: five bytes, indices 1..4, the third byte equals the first (shared constant) -/
@[hardware_module] def ntResp {dom : DomainConfig} (cnt : Signal dom (BitVec 3)) : Signal dom (BitVec 8) :=
  let b0 := (Signal.pure 0x48#8 : Signal dom (BitVec 8))
  let b1 := (Signal.pure 0xAB#8 : Signal dom (BitVec 8))
  let b2 := (Signal.pure 0x48#8 : Signal dom (BitVec 8))
  let b3 := (Signal.pure 0x21#8 : Signal dom (BitVec 8))
  let b4 := (Signal.pure 0x7E#8 : Signal dom (BitVec 8))
  Signal.mux (eqN cnt 1) b0
    (Signal.mux (eqN cnt 2) b1
      (Signal.mux (eqN cnt 3) b2
        (Signal.mux (eqN cnt 4) b3 b4)))

/-- `respByteMux`'s shape: a `kLut!` table with repeated entries (shared constants) -/
@[hardware_module] def ntLut {dom : DomainConfig} (i : Signal dom (BitVec 3)) : Signal dom (BitVec 8) :=
  kLut! i [
    Signal.pure 0x45#8, Signal.pure 0x00#8, Signal.pure 0x00#8, Signal.pure 0xC0#8,
    Signal.pure 0x00#8, Signal.pure 0x45#8
  ]

/-- a parent with a counter register: the child's input is the register's output -/
def ntEmit (trigger : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let cnt ← Signal.reg (0#3)
    let cs := (cnt : Signal defaultDomain (BitVec 3))
    cnt <~ Signal.mux trigger (cs + 1#3) cs
    return ntResp cs

/-! ## Positives -/

def specOf (decl : Name) : Lean.Expr := mkApp (Lean.mkConst decl) (Lean.mkConst ``defaultDomain)

/-- the leaf entry with the named-table proof source; the shape is first pinned: read by `ntblDataOf?`,
not taken by `tblDataOf?` -/
def runNT (decl : Name) (base : Name) (m : Sparkle.IR.AST.Module) : TermElabM Name := do
  let (stmt, nDom) ← specialiseDomain decl
  let inp := ((dataPortsOf m (clkRstOf m)).map fun p => p.name).headD ""
  unless (tblDataOf? m inp).isNone do throwError "{decl}: taken by the skeleton table route"
  unless (ntblDataOf? m inp).isSome do throwError "{decl}: not read as a named table"
  checkU1E decl base stmt m (childProofSrc decl nDom m)

def checkPos (decl : Name) (entries : Nat) : CommandElabM Unit := liftTermElabM do
  let (m, _) ← Sparkle.Compiler.Elab.synthesizeCombinational decl
  let thm ← runNT decl decl m
  let nm := Names.ofBase decl
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, specOf decl]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not U1Stmt c m (@{decl} defaultDomain)"
  let r ← Tools.VedStrictAudit.strictAudit thm
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) && r.axioms.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  -- the named-table route: the registered data is the one the kernel checked
  let some (.defnInfo di) := (← getEnv).find? (decl ++ `ved_ntbl) | throwError "{decl}: no named-table data"
  let some D ← (unsafe Meta.evalExpr (Option Tools.VedH3ChildTbl.NData)
      (mkApp (Lean.mkConst ``Option [Level.zero]) (Lean.mkConst ``Tools.VedH3ChildTbl.NData))
      (mkApp2 (Lean.mkConst ``Option.some [Level.zero]) (Lean.mkConst ``Tools.VedH3ChildTbl.NData) di.value) : MetaM _)
    | throwError "{decl}: data not evaluable"
  unless D.ok = true && D.rowsOk = true && D.rows.length == 2 ^ D.iw do throwError "{decl}: data rejected"
  let nConst := D.Fl.filter (fun f => match f with | .const _ w => w == D.w | _ => false) |>.length
  unless nConst == entries do throwError "{decl}: {nConst} distinct output constants, expected {entries}"
  logInfo m!"OK {decl}: exact type, axioms {ax.size}, named table, {nConst} output constants"

/-- info: OK Tests.Ved.H3ChildCheck.ntResp: exact type, axioms 3, named table, 4 output constants -/
#guard_msgs in
run_cmd checkPos ``ntResp 4
/-- info: OK Tests.Ved.H3ChildCheck.ntLut: exact type, axioms 3, named table, 3 output constants -/
#guard_msgs in
run_cmd checkPos ``ntLut 3

/-- the parent through `#ved_u2_hier`: the child proved once, its theorem composed with the parent -/
def checkHier (decl : Name) : CommandElabM Unit := do
  let (m, d, thm, nDom, _) ← Tools.VedU2HierRegEntry.vedU2HierEntryR decl
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U2HRStmt c m d decl"
    unless !(regsOf m.body).isEmpty do throwError "{decl}: the parent has no register"
    discard <| Tools.VedStrictAudit.strictAudit thm
    std3Only thm
    let kid := (decl ++ `ved_child) ++ ``ntResp
    unless (← getEnv).contains (kid ++ `ved_ntbl) do throwError "the child did not take the named-table route"
    logInfo m!"u2 hier OK: {(regsOf m.body).length} parent register, children {", ".intercalate (d.modules.map (·.name))}"

/-- info: u2 hier OK: 1 parent register, children Tests.Ved.H3ChildCheck.ntResp -/
#guard_msgs in
run_cmd checkHier ``ntEmit

/-! ## Controls: ONE piece altered, refused at `[proof]`, no `ved_*` constant left -/

def ctlNames (base : Name) : List Name := checkerNames base ++ [base ++ `ved_ntbl]

def expectRefusedNT (stage : String) (base : Name) (act : TermElabM Unit) : CommandElabM Unit := liftTermElabM do
  let accepted ← try act; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith "VED U1 REFUSED" && (s.splitOn s!"[{stage}]").length > 1 do throw e
    pure false
  if accepted then throwError "control ACCEPTED (expected a refusal at [{stage}])"
  for n in ctlNames base do
    if (← getEnv).contains n then throwError "left behind: {n}"
  logInfo m!"refused [{stage}], clean"

/-- the checker with the named-table source on `m` (read again from the altered module) against `decl` -/
def ctlNT (base decl : Name) (m : Sparkle.IR.AST.Module) : CommandElabM Unit := do
  expectRefusedNT "proof" base do
    let (stmt, nDom) ← specialiseDomain decl
    let inp := ((dataPortsOf m (clkRstOf m)).map fun p => p.name).headD ""
    unless (ntblDataOf? m inp).isSome do throwError "{base}: the altered module is not read as a named table"
    discard <| checkU1E decl base stmt m (childProofSrc decl nDom m)

def realMod (decl : Name) : CommandElabM Sparkle.IR.AST.Module := liftTermElabM do
  return (← Sparkle.Compiler.Elab.synthesizeCombinational decl).1

open Sparkle.IR.AST in
/-- the `n`-th `mux` has its then / else operands exchanged -/
def swapMuxArms (n : Nat) (m : Sparkle.IR.AST.Module) : Except String Sparkle.IR.AST.Module :=
  mutNth n (fun s => match s with
    | .assign o (.op .mux [c, t, f]) => some (.assign o (.op .mux [c, f, t]))
    | _ => none) m

open Sparkle.IR.AST in
/-- the `n`-th constant of width `w` is declared with width `w - 1` -/
def narrowConst (w n : Nat) (m : Sparkle.IR.AST.Module) : Except String Sparkle.IR.AST.Module :=
  mutNth n (fun s => match s with
    | .assign o (.const v w') => if w' == w then some (.assign o (.const v (w - 1))) else none
    | _ => none) m

def ctlMutNT (base decl : Name) (mutant : Sparkle.IR.AST.Module → Except String Sparkle.IR.AST.Module) :
    CommandElabM Unit := do
  let o ← realMod decl
  match mutant o with
  | .error e => throwError "{base}: mutator failed: {e}"
  | .ok m =>
    if m.body == o.body then throwError "{base}: the mutant is the original"
    ctlNT base decl m

-- a table constant of `ntResp` changed (the 8-bit constants are the entries)
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMutNT `ctlRespConst ``ntResp (bumpConst 8 1)

-- two entries exchanged
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMutNT `ctlRespSwap ``ntResp (swapConsts 8 0 1)

-- an index constant (3-bit) changed
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMutNT `ctlRespIndex ``ntResp (bumpConst 3 1)

-- the then / else operands of the first mux exchanged
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMutNT `ctlRespArms ``ntResp (swapMuxArms 0)

-- one constant declared one bit narrower (0xAB does not fit in 7 bits)
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMutNT `ctlRespWidth ``ntResp (narrowConst 8 1)

-- the `kLut!` table: a constant changed, two entries exchanged
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMutNT `ctlLutConst ``ntLut (bumpConst 8 2)

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMutNT `ctlLutSwap ``ntLut (swapConsts 8 0 2)

-- the module of `ntResp` against the statement of `ntLut` (the same ports, another function)
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do ctlNT `ctlOtherDecl ``ntLut (← realMod ``ntResp)

/-! ## Add-stage chains -/

/-- three stages: `ones(hi, lo)`, `ones(·, b)`, `ones(·, const)`, inverted -/
@[hardware_module] def ckSum {dom : DomainConfig} (a : Signal dom (BitVec 32)) (b : Signal dom (BitVec 16)) :
    Signal dom (BitVec 16) :=
  let hi : Signal dom (BitVec 16) := a.map (BitVec.extractLsb' 16 16 ·)
  let lo : Signal dom (BitVec 16) := a.map (BitVec.extractLsb' 0 16 ·)
  let k : Signal dom (BitVec 16) := Signal.pure 0x1234#16
  let s := Sparkle.IP.Net.IPv4.onesAdd16Sig hi lo
  let s := Sparkle.IP.Net.IPv4.onesAdd16Sig s b
  let s := Sparkle.IP.Net.IPv4.onesAdd16Sig s k
  s.map (BitVec.not ·)

/-- another chain (two stages), for the control that exchanges modules -/
@[hardware_module] def ckSum2 {dom : DomainConfig} (a : Signal dom (BitVec 32)) (b : Signal dom (BitVec 16)) :
    Signal dom (BitVec 16) :=
  let hi : Signal dom (BitVec 16) := a.map (BitVec.extractLsb' 16 16 ·)
  let lo : Signal dom (BitVec 16) := a.map (BitVec.extractLsb' 0 16 ·)
  let s := Sparkle.IP.Net.IPv4.onesAdd16Sig hi b
  let s := Sparkle.IP.Net.IPv4.onesAdd16Sig s lo
  s.map (BitVec.not ·)

/-- a parent whose instance is the chain leaf -/
def ckParent (a : Signal defaultDomain (BitVec 32)) (b : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain (BitVec 16) :=
  ckSum a b

open Tools.VedH3ChildChainEntry in
def runCh (decl : Name) (base : Name) (m : Sparkle.IR.AST.Module) : TermElabM Name := do
  let (stmt, nDom) ← specialiseDomain decl
  unless (chainDataOf? m).isSome do throwError "{decl}: not read as a chain"
  unless (Tools.VedH3ChildTblEntry.ntblDataOf? m "_gen_a").isNone do throwError "{decl}: read as a named table"
  checkU1E decl base stmt m (.built (buildChain decl nDom))

open Tools.VedH3ChildChainEntry in
def checkChain (decl : Name) (stages : Nat) : CommandElabM Unit := liftTermElabM do
  let (m, _) ← Sparkle.Compiler.Elab.synthesizeCombinational decl
  let thm ← runCh decl decl m
  let nm := Names.ofBase decl
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, specOf decl]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not U1Stmt c m (@{decl} defaultDomain)"
  let r ← Tools.VedStrictAudit.strictAudit thm
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) && r.axioms.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  let some (.defnInfo di) := (← getEnv).find? (decl ++ `ved_chain) | throwError "{decl}: no chain data"
  let some D ← (unsafe Meta.evalExpr (Option Tools.VedH3ChildChain.CData)
      (mkApp (Lean.mkConst ``Option [Level.zero]) (Lean.mkConst ``Tools.VedH3ChildChain.CData))
      (mkApp2 (Lean.mkConst ``Option.some [Level.zero]) (Lean.mkConst ``Tools.VedH3ChildChain.CData) di.value) : MetaM _)
    | throwError "{decl}: data not evaluable"
  unless D.stages.length == stages do throwError "{decl}: {D.stages.length} stages, expected {stages}"
  logInfo m!"OK {decl}: exact type, axioms {ax.size}, chain of {D.stages.length} stages"

/-- info: OK Tests.Ved.H3ChildCheck.ckSum: exact type, axioms 3, chain of 3 stages -/
#guard_msgs in
run_cmd checkChain ``ckSum 3
/-- info: OK Tests.Ved.H3ChildCheck.ckSum2: exact type, axioms 3, chain of 2 stages -/
#guard_msgs in
run_cmd checkChain ``ckSum2 2

/-- the exact statement of a register-free parent (`U2HStmt`, as in `Tests/Ved/U2HierCheck.lean`) -/
def expectedH2a (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := Tools.VedU1HierEntry.HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``Tools.VedU2Hier.U2HStmt)
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

/-- the parent through `#ved_u2_hier`: the chain leaf proved once, composed with the parent -/
def checkHierCk (decl : Name) : CommandElabM Unit := liftTermElabM do
  let (_, d, thm, nDom, _) ← Tools.VedU2HierEntry.vedU2HierEntry decl
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expectedH2a decl nDom do throwError "{thm}: type is not U2HStmt c m d decl"
  discard <| Tools.VedStrictAudit.strictAudit thm
  std3Only thm
  unless (← getEnv).contains (((decl ++ `ved_child) ++ ``ckSum) ++ `ved_chain) do
    throwError "the child did not take the chain route"
  logInfo m!"u2 hier OK: children {", ".intercalate (d.modules.map (·.name))}"

/-- info: u2 hier OK: children Tests.Ved.H3ChildCheck.ckSum -/
#guard_msgs in
run_cmd checkHierCk ``ckParent

/-- the chain controls: the checker with the chain source on the altered module of `ckSum` -/
def ctlCk (base decl : Name) (m : Sparkle.IR.AST.Module) : CommandElabM Unit :=
  expectRefusedNT "proof" base do
    discard <| runCh' decl base m
where
  runCh' (decl base : Name) (m : Sparkle.IR.AST.Module) : TermElabM Name := do
    let (stmt, nDom) ← specialiseDomain decl
    checkU1E decl base stmt m (.built (Tools.VedH3ChildChainEntry.buildChain decl nDom))

def ctlNames' (base : Name) : List Name := ctlNames base ++ [base ++ `ved_chain, base ++ `ved_ports]

open Sparkle.IR.AST in
/-- the first slice reading bits `hi..lo` of its source is changed by `f` -/
def mutSlice (n : Nat) (f : Nat → Nat → Nat × Nat) (m : Sparkle.IR.AST.Module) : Except String Sparkle.IR.AST.Module :=
  mutNth n (fun s => match s with
    | .assign o (.slice e hi lo) => let (h, l) := f hi lo; some (.assign o (.slice e h l))
    | _ => none) m

open Sparkle.IR.AST in
/-- the `n`-th statement `x := concat [hi0, A]` reads the word `W` instead of its operand -/
def mutOperand (n : Nat) (m : Sparkle.IR.AST.Module) : Except String Sparkle.IR.AST.Module :=
  mutNth n (fun s => match s with
    | .assign o (.concat [.ref h, .ref _]) => some (.assign o (.concat [.ref h, .ref "_gen_hi"]))
    | _ => none) m

open Sparkle.IR.AST in
/-- the last `not` of the body becomes the identity (a `ref` of its operand) -/
def dropNot (m : Sparkle.IR.AST.Module) : Except String Sparkle.IR.AST.Module :=
  mutNth 0 (fun s => match s with
    | .assign o (.op .not [x]) => some (.assign o x)
    | _ => none) m

def ctlMutCk (base decl : Name) (mutant : Sparkle.IR.AST.Module → Except String Sparkle.IR.AST.Module) :
    CommandElabM Unit := do
  let o ← realMod decl
  match mutant o with
  | .error e => throwError "{base}: mutator failed: {e}"
  | .ok m =>
    if m.body == o.body then throwError "{base}: the mutant is the original"
    expectRefusedNT "proof" base do
      discard <| ctlCk.runCh' decl base m
    -- (the left-behind names of the chain route)
    for n in ctlNames' base do
      if (← getEnv).contains n then throwError "left behind: {n}"

-- a constant word changed (0x1234 -> 0x1235): the read data is still a chain, the values differ
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMutCk `ctlCkConst ``ckSum (bumpConst 16 0)

-- a slice reads the wrong half of its input
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMutCk `ctlCkSlice ``ckSum (mutSlice 0 fun _ _ => (15, 0))

-- a slice narrowed by one bit (bits 31..17 instead of 31..16)
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMutCk `ctlCkNarrow ``ckSum (mutSlice 0 fun hi _ => (hi, 17))

-- the chained operand of the second stage replaced by a word (the chain is broken)
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMutCk `ctlCkBroken ``ckSum (mutOperand 3)

-- the final `~~~` dropped
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd ctlMutCk `ctlCkNoNot ``ckSum dropNot

-- the module of the two-stage chain against the three-stage statement
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do
  let m ← realMod ``ckSum2
  expectRefusedNT "proof" `ctlCkOther do
    discard <| ctlCk.runCh' ``ckSum `ctlCkOther m
  for n in ctlNames' `ctlCkOther do
    if (← getEnv).contains n then throwError "left behind: {n}"

end Tests.Ved.H3ChildCheck

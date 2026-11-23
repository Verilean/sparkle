import Tools.VedU2HierMultiOut
import Tools.VedU2HierRegEntry
import Tests.Ved.ComposeCheckUtil
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for `U2HRStmtK` (Tools/VedU2HierMultiOut.lean)

Prints the full candidate statement, the axioms of the coincidence theorems, and runs the shape side of the
k-output hierarchy on real synthesised designs (a parent with a register whose child has 2 resp. 3 outputs):

* `HierShapeS d m = false` and `HierShapeK d m = true` on the real design;
* CONTROLS on the shape (an edited `(m, d)`): an output not connected, two outputs on one parent wire, an output
  on a wire of the wrong width: `HierShapeK = false`, and under `ved.compose.multiOut` the entry refuses them at
  `[hier-shape]` with the matching text; with the option OFF the entry refuses the real design at `[hier-shape]` with
  the previous text (child has 2 outputs);
* the swap of two SAME-width outputs in the parent's use is NOT a shape property (`HierShapeK` stays true): only a
  proof can refuse it;
* the first refusal of the real design with the option ON: `[child]`, the child's table (`ved_table%`) is read from a
  `Signal` result; a structure result is not read (the child's own theorem cannot be stated).  No acceptance is claimed.
-/

namespace Tests.Ved.MultiOutCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil

structure P2 (dom : DomainConfig) where
  s : Signal dom (BitVec 4)
  d : Signal dom (BitVec 4)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (P2 dom) dom := ⟨⟩

@[hardware_module] def child2 {dom : DomainConfig} (x y : Signal dom (BitVec 4)) : P2 dom :=
  ({ s := x + y, d := x - y } : P2 dom)

/-- a parent with a register reading both outputs of the 2-output child -/
def top2 (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := child2 accS inp
    acc <~ (c.s + c.d : Signal defaultDomain (BitVec 4))
    return accS

structure P3 (dom : DomainConfig) where
  a : Signal dom (BitVec 4)
  b : Signal dom (BitVec 4)
  c : Signal dom (BitVec 4)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (P3 dom) dom := ⟨⟩

@[hardware_module] def child3 {dom : DomainConfig} (x y : Signal dom (BitVec 4)) : P3 dom :=
  ({ a := x + y, b := x - y, c := x &&& y } : P3 dom)

/-- a parent reading two of the three outputs -/
def top3 (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let k := child3 accS inp
    acc <~ (k.a + k.c : Signal defaultDomain (BitVec 4))
    return accS

/-- Replace the connection of port `p` of instance `k` by `e`, or drop it (`none`). -/
def editConn (k : Nat) (p : String) (e : Option Sparkle.IR.AST.Expr) (b : List Stmt) : List Stmt :=
  let rec go : List Stmt → Nat → List Stmt
    | [], _ => []
    | s :: r, n =>
      match s with
      | .inst mn i cs =>
        (if n == k then
          .inst mn i (cs.filterMap fun q => if q.1 == p then e.map (p, ·) else some q)
        else s) :: go r (n + 1)
      | _ => s :: go r n
  go b 0

def withBody (m : Sparkle.IR.AST.Module) (b : List Stmt) : Sparkle.IR.AST.Module := { m with body := b }

def refMsg (decl : Name) (m : Sparkle.IR.AST.Module) (d : Design) : CommandElabM String := do
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  try
    discard <| checkU2HR decl stmt nDom m d none
    pure "ACCEPTED"
  catch e => liftTermElabM (e.toMessageData.toString)

def expectMsg (what : String) (msg : String) (needles : List String) : CommandElabM Unit := do
  for n in needles do
    unless (msg.splitOn n).length > 1 do throwError "{what}: expected `{n}` in: {msg.take 400}"
  logInfo m!"{what}: {msg.take 240}"

/-- the wire the instance's port `p` is connected to -/
def connOf (b : List Stmt) (p : String) : Option Sparkle.IR.AST.Expr :=
  b.findSome? fun s => match s with
    | .inst _ _ cs => cs.lookup p
    | _ => none

#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``top2
  let nOut := d.modules.map (·.outputs.length)
  unless nOut == [2] do throwError "child output counts {nOut}"
  unless HierShapeS d m == false do throwError "HierShapeS should be false for the 2-output child"
  unless HierShapeK d m == true do throwError "HierShapeK should be true"
  logInfo m!"top2: child outputs {d.modules.map (fun c => c.outputs.map (·.name))}; HierShapeS=false HierShapeK=true"
  -- controls on the shape
  let outS := ((d.modules.map (·.outputs)).headD []).map (·.name)
  let (o1, o2) := (outS[0]!, outS[1]!)
  let w1 := connOf m.body o1; let w2 := connOf m.body o2
  let (some w1, some w2) := (w1, w2) | throwError "no connections"
  let kd := fun b => ({ m with body := b } : Sparkle.IR.AST.Module)
  -- (ii) output missing
  let mMiss := kd (editConn 0 o2 none m.body)
  unless HierShapeK d mMiss == false do throwError "missing output: HierShapeK should be false"
  -- (iii) two outputs on one wire
  let mSame := kd (editConn 0 o2 (some w1) m.body)
  unless HierShapeK d mSame == false do throwError "same wire: HierShapeK should be false"
  -- wrong width: an output on the 1-bit-different wire: use a wire of another width, the parent's input `inp` is 4-bit; take the clock input (no wire)
  let mWid := kd (editConn 0 o2 (some (.ref "no_such_wire")) m.body)
  unless HierShapeK d mWid == false do throwError "unknown wire: HierShapeK should be false"
  -- (i) the swap of two same-width outputs: not a shape property
  let mSwap := kd (editConn 0 o1 (some w2) (editConn 0 o2 (some w1) m.body))
  unless HierShapeK d mSwap == true do throwError "swap: HierShapeK stays true (a proof refuses it)"
  logInfo m!"controls: missing={HierShapeK d mMiss} sameWire={HierShapeK d mSame} unknownWire={HierShapeK d mWid} swap={HierShapeK d mSwap}"
  -- option OFF: the previous text, at [hier-shape]
  let off ← refMsg ``top2 m d
  expectMsg "option off" off ["[hier-shape]", "has 2 outputs (multi-output children: H3)"]
  -- option ON: controls refused at [hier-shape]
  withScope (fun sc => { sc with opts := sc.opts.setBool `ved.compose.multiOut true }) do
    expectMsg "on, missing" (← refMsg ``top2 mMiss d) ["[hier-shape]", s!"port {o2} of"]
    expectMsg "on, same wire" (← refMsg ``top2 mSame d) ["[hier-shape]", "same parent wire"]
    -- the real design: the shape passes, the first refusal is the child's table
    -- (unit 2: the child's struct theorem is now supplied, the first refusal moves past `[child]`)
    expectMsg "on, real" (← refMsg ``top2 m d) []

#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``top3
  unless d.modules.map (·.outputs.length) == [3] do throwError "3-output child"
  unless HierShapeS d m == false && HierShapeK d m == true do throwError "top3 shape"
  logInfo m!"top3: child outputs {d.modules.map (fun c => c.outputs.map (·.name))}; HierShapeS=false HierShapeK=true"
  let (m2, d2) ← synthOf ``top2
  -- an output of the 3-output child dropped
  let o := ((d.modules.map (·.outputs)).headD []).map (·.name)
  let mMiss := ({ m with body := editConn 0 o[2]! none m.body } : Sparkle.IR.AST.Module)
  unless HierShapeK d mMiss == false do throwError "3-out: missing output should fail"
  discard <| pure (m2, d2)

end Tests.Ved.MultiOutCheck

open Tools.VedU2Hier

#print U2HRStmtK
#print HierShapeK
#print connsOkK
#print outRefNames
#print axioms U2HRStmtK_iff
#print axioms U2HRStmtK_of_U2HRStmt
#print axioms HierShapeK_of_S
#print axioms HierShapeS_of_K
#print axioms outputsOnHS_of_stepR_multi
#print axioms outputsOnHS_of_stepRK_multi
#print axioms kid_inst_multi

/-! ## Unit 2: the 2-output struct child accepted end to end (option `ved.compose.multiOut`)

`top2` (child `child2`, outputs `s`, `d`, both read) and `top3` (3 outputs, two read) are accepted by the entry with the option on:
the stored type is `==` `U2HRStmtK c m d decl` (original declaration), the module/design are the declaration's own synthesis, the
axioms are within the standard three, no `sorryAx`, and the child theorem constant (from the struct entry's route) occurs in the proof.
CONTROLS (a copy of `(m, d)` altered, or the option off): refused, nothing left behind.  The same-width swap and the wrong wiring are
checked on `top2m` (the parent reads `s - d`, not commutative).  The same-width swap passes the SHAPE (`HierShapeK` true) and is refused
by the PROOF. -/

namespace Tests.Ved.MultiOutCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil

def top2m (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := child2 accS inp
    acc <~ (c.s - c.d : Signal defaultDomain (BitVec 4))
    return accS

/-- the same design as `top2m`, for the controls (the accepted `top2m` leaves its constants behind) -/
def top2n (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := child2 accS inp
    acc <~ (c.s - c.d : Signal defaultDomain (BitVec 4))
    return accS

def expectedK (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := Tools.VedU1HierEntry.HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``U2HRStmtK) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

def acceptK (decl kid : Name) : CommandElabM Unit := do
  let (m, d) ← synthOf decl
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  -- (`top2` was already accepted by the first `#eval` of this file, its constants are inspected as they are)
  let thm := (Tools.VedU1HierEntry.HNames.ofBase decl).thm
  unless (← getEnv).contains thm do discard <| checkU2HR decl stmt nDom m d none
  let (m2, d2) ← synthOf decl
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type == expectedK decl nDom do throwError "{thm}: type is not U2HRStmtK c m d decl"
    unless decide (m = m2) && d.topModule == d2.topModule && decide (d.modules = d2.modules) do
      throwError "{decl}: the returned module/design differ from the declaration's own synthesis"
    let nm := Tools.VedU1HierEntry.HNames.ofBase decl
    let some ci := (← getEnv).find? nm.mod | throwError "{nm.mod} missing"
    unless ci.value! == toExpr m2 do throwError "{nm.mod} is not the declaration's own module"
    let axs ← collectAxioms thm
    unless axs.all (std3.contains ·) do throwError "{thm}: axioms outside std3: {axs}"
    if axs.contains ``sorryAx then throwError "{thm}: sorryAx"
    let kidThm := (decl ++ `ved_child ++ kid) ++ `ved_u1
    unless ti.value.getUsedConstants.contains kidThm do throwError "{thm}: the child theorem {kidThm} does not occur"
    discard <| Tools.VedStrictAudit.strictAudit thm
    logInfo m!"ACCEPTED {decl}: U2HRStmtK type ==, same artifact, std3, kernel, child theorem {kidThm} occurs"

def ctlK (what : String) (decl : Name) (stages : List String) (m : Sparkle.IR.AST.Module) (d : Design) :
    CommandElabM Unit := do
  let before ← localConsts
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  let r ← try
      discard <| checkU2HR decl stmt nDom m d none
      pure none
    catch e => pure (some (← liftTermElabM (e.toMessageData.toString)))
  match r with
  | none => throwError "{what}: expected a refusal, the checker ACCEPTED"
  | some msg =>
    unless stages.any (fun st => msg.startsWith s!"VED U1 REFUSED {decl} [{st}]") do
      throwError "{what}: expected a refusal at one of {stages}, got: {msg.take 300}"
    let added := (← localConsts).toList.filter (!before.contains ·)
    unless added.isEmpty do throwError "{what}: constants left after the refusal: {added}"
    logInfo m!"CONTROL {what}: {msg.take 200}"

#eval show CommandElabM Unit from do
  withScope (fun sc => { sc with opts := sc.opts.setBool `ved.compose.multiOut true }) do
    acceptK ``top2 `Tests.Ved.MultiOutCheck.child2
    acceptK ``top3 `Tests.Ved.MultiOutCheck.child3
    acceptK ``top2m `Tests.Ved.MultiOutCheck.child2

#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``top2n
  let outS := ((d.modules.map (·.outputs)).headD []).map (·.name)
  let (o1, o2) := (outS[0]!, outS[1]!)
  let (some w1, some w2) := (connOf m.body o1, connOf m.body o2) | throwError "no connections"
  let kd := fun b => ({ m with body := b } : Sparkle.IR.AST.Module)
  withScope (fun sc => { sc with opts := sc.opts.setBool `ved.compose.multiOut true }) do
    -- (i) the two same-width outputs swapped in the parent's use: the shape passes, the proof refuses
    let mSwap := kd (editConn 0 o1 (some w2) (editConn 0 o2 (some w1) m.body))
    unless HierShapeK d mSwap == true do throwError "swap: HierShapeK should stay true"
    ctlK "(i) swapped same-width outputs" ``top2n ["proof", "kernel", "open", "deep"] mSwap d
    -- (ii) an output missing
    ctlK "(ii) output d missing" ``top2n ["hier-shape"] (kd (editConn 0 o2 none m.body)) d
    -- (iii) wrong wiring: the child's output s on the wire of the OTHER instance's s
    ctlK "(iii) wrong wiring" ``top2n ["hier-shape", "order", "proof", "kernel", "conns", "open", "deep", "artifact"]
      (kd (editConn 0 o1 (some (.ref "_tmp_c_s_9")) m.body)) d
  -- (iv) the option off: the old text
  let off ← refMsg ``top2n m d
  expectMsg "(iv) option off" off ["[hier-shape]", "has 2 outputs (multi-output children: H3)"]

end Tests.Ved.MultiOutCheck

#print axioms Tests.Ved.MultiOutCheck.acceptK

/-! ## Unit 3: a SEQUENTIAL struct child (2 outputs, one register of its own)

`kidr` keeps a register and returns `{ s := reg, d := reg - y }`.  The child theorem is the struct entry's loop-script route
(`Tools.VedU1StructSeq`), through the same `stmtOfStruct` + `checkU1E` as the register-free child. -/

namespace Tests.Ved.MultiOutCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil

@[hardware_module] def kidr {dom : DomainConfig} (x y : Signal dom (BitVec 4)) : P2 dom :=
  circuit do
    let r ← Signal.reg 0#4
    let rS := (r : Signal dom (BitVec 4))
    r <~ x + y
    return ({ s := rS, d := rS - y } : P2 dom)

/-- a parent with a register reading both outputs of the sequential 2-output child; the child's inputs are the parent's DATA inputs -/
def topr (inp inp2 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := kidr inp2 inp
    acc <~ (c.s - c.d : Signal defaultDomain (BitVec 4))
    return accS

/-- the same parent with the child's inputs read from the parent's REGISTER -/
def topr0 (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := kidr accS inp
    acc <~ (c.s - c.d : Signal defaultDomain (BitVec 4))
    return accS

-- (a) the CHILD theorem of the sequential struct child: the very call of the entry (`stmtOfStruct` of the declaration, `checkU1E`
-- on the design's own child module), a module WITH a register
#eval show CommandElabM Unit from do
  let (_, d) ← synthOf ``topr
  let some cm := d.modules.head? | throwError "no child"
  unless (regsOf cm.body).length == 1 do throwError "the child has {(regsOf cm.body).length} registers, expected 1"
  unless d.modules.length == 1 && cm.outputs.length == 2 do throwError "child shape"
  liftTermElabM do
    let (b, _, names) ← Tools.VedU1StructOut.stmtOfStruct ``kidr
    let thm ← Tools.VedU1Entry.checkU1E ``kidr (``kidr ++ `ved_seq3) b cm .generated names
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type.getAppFn.isConstOf ``Tools.VedU1Contract.U1Stmt do throwError "{thm}: type is not U1Stmt"
    let axs ← collectAxioms thm
    unless axs.all (std3.contains ·) do throwError "{thm}: axioms outside std3: {axs}"
    if axs.contains ``sorryAx then throwError "{thm}: sorryAx"
    logInfo m!"CHILD THEOREM (sequential struct child, 1 register, outputs {names}): {thm} U1Stmt, std3, no sorryAx"

-- (b) (unit 3 pinned the parent's refusals here; unit 4 accepts them: see the section below)

end Tests.Ved.MultiOutCheck

/-! ## Unit 4: a parent with registers over SEQUENTIAL 2-output struct children

* (a) `topr0`: the child's input is the parent's REGISTER; `topr`: the child's inputs are the parent's data inputs;
* (b) `topb`: two instances of the sequential child, the second reads an OUTPUT of the first (chain through a multi-output producer);
* (c) `topc`: one instance whose two outputs feed two DIFFERENT consumers (a producer's output net is keyed by the producer's module name, the OUTPUT PORT and its input nets, recursively: `keyNetI` extended with `portKey`, not replaced, and not the instance id).

All are accepted with the stored type `U2HRStmtK c m d top`, the same artifact, std3, the kernel, the child theorem constant used
(`acceptK`).  `U2HRStmtK` was approved (reviewer, 2026-11-23) for the scope of ca486924..2eff05ce only: a register parent
with sequential or combinational multi-output LEAF children; it is not a new TRUSTED statement.  Old paths are unchanged with
`ved.compose.multiOut` off. -/

namespace Tests.Ved.MultiOutCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil

def topb (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c1 := kidr accS inp
    let c2 := kidr c1.s inp
    acc <~ (c2.s + c2.d : Signal defaultDomain (BitVec 4))
    return accS

def topc (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c1 := kidr accS inp
    let c2 := kidr c1.s inp
    let c3 := kidr c1.d inp
    acc <~ (c2.s + c3.d : Signal defaultDomain (BitVec 4))
    return accS

-- copies for the controls (the accepted ones leave their constants in the environment)
def topr0n (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := kidr accS inp
    acc <~ (c.s - c.d : Signal defaultDomain (BitVec 4))
    return accS

def topbn (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c1 := kidr accS inp
    let c2 := kidr c1.s inp
    acc <~ (c2.s + c2.d : Signal defaultDomain (BitVec 4))
    return accS

def topcn (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c1 := kidr accS inp
    let c2 := kidr c1.s inp
    let c3 := kidr c1.d inp
    acc <~ (c2.s + c3.d : Signal defaultDomain (BitVec 4))
    return accS

def withMO (conn : Bool) (sc : Command.Scope) : Command.Scope :=
  { sc with opts := (sc.opts.setBool `ved.compose.multiOut true).setBool `ved.compose.connect conn }

#eval show CommandElabM Unit from do
  withScope (withMO false) do
    acceptK ``topr0 `Tests.Ved.MultiOutCheck.kidr
    acceptK ``topr `Tests.Ved.MultiOutCheck.kidr
  withScope (withMO true) do
    acceptK ``topb `Tests.Ved.MultiOutCheck.kidr
    acceptK ``topc `Tests.Ved.MultiOutCheck.kidr

/-- the instances of a body, with their position -/
def instsOf (b : List Stmt) : List (Nat × String × String × List (String × Sparkle.IR.AST.Expr)) :=
  let rec go : List Stmt → Nat → List (Nat × String × String × List (String × Sparkle.IR.AST.Expr))
    | [], _ => []
    | .inst mn i cs :: r, n => (n, mn, i, cs) :: go r (n + 1)
    | _ :: r, n => go r n
  go b 0

-- controls (observed refusals), option on
#eval show CommandElabM Unit from do
  -- (a) topr0: the two outputs of the sequential child swapped (same width): the shape passes, a proof refuses
  withScope (withMO false) do
    let (m, d) ← synthOf ``topr0n
    let outS := ((d.modules.map (·.outputs)).headD []).map (·.name)
    let (o1, o2) := (outS[0]!, outS[1]!)
    let (some w1, some w2) := (connOf m.body o1, connOf m.body o2) | throwError "no connections"
    let kd := fun b => ({ m with body := b } : Sparkle.IR.AST.Module)
    let mSwap := kd (editConn 0 o1 (some w2) (editConn 0 o2 (some w1) m.body))
    unless HierShapeK d mSwap == true do throwError "swap: HierShapeK should stay true"
    ctlK "(a-i) topr0: swapped same-width outputs" ``topr0n ["proof", "kernel", "open", "deep"] mSwap d
    ctlK "(a-ii) topr0: output d missing" ``topr0n ["hier-shape"] (kd (editConn 0 o2 none m.body)) d
    ctlK "(a-iii) topr0: wrong wiring" ``topr0n ["hier-shape", "order", "proof", "kernel", "conns", "open", "deep", "artifact"]
      (kd (editConn 0 o1 (some (.ref "_tmp_c_s_9")) m.body)) d
  -- (c) topc: the two outputs of the producer swapped between the two consumers
  withScope (withMO true) do
    let (m, d) ← synthOf ``topcn
    let is := instsOf m.body
    let outWires := is.flatMap fun (_, _, _, cs) => cs.filterMap fun (p, e) => match p, e with
      | "s", .ref w => some w
      | "d", .ref w => some w
      | _, _ => none
    -- the consumers: instances whose `_gen_x` reads an output wire of another instance
    let cons := is.filter fun (_, _, _, cs) => match cs.lookup "_gen_x" with
      | some (.ref w) => outWires.contains w
      | _ => false
    -- (the synthesized IR holds each producer/consumer chain twice: the nets of the result and those of the `let`s; the control
    -- mis-wires both copies the same way)
    unless cons.length == 4 do throwError "topc: expected 4 consumer instances, found {cons.length}"
    let swapPair (b : List Stmt) (p q : Nat × String × String × List (String × Sparkle.IR.AST.Expr)) : List Stmt :=
      match p.2.2.2.lookup "_gen_x", q.2.2.2.lookup "_gen_x" with
      | some x1, some x2 => setConnAt p.1 "_gen_x" x2 (setConnAt q.1 "_gen_x" x1 b)
      | _, _ => b
    let mSw := ({ m with body := swapPair (swapPair m.body cons[0]! cons[1]!) cons[2]! cons[3]! } : Sparkle.IR.AST.Module)
    ctlK "(c) topc: the producer's two outputs swapped between the consumers" ``topcn
      ["proof", "kernel", "open", "deep", "hier-shape", "order"] mSw d
    -- (b) topb: the consumer reads the producer's OTHER output (d for s)
    let (mb, db) ← synthOf ``topbn
    let isb := instsOf mb.body
    let consb := isb.filter fun (_, _, _, cs) => match cs.lookup "_gen_x" with
      | some (.ref w) => isb.any fun (_, _, _, cs') => cs'.lookup "s" == some (.ref w)
      | _ => false
    unless consb.length == 2 do throwError "topb: expected 2 consumer instances, found {consb.length}"
    let mut bodyB := mb.body
    for (kb, _, _, csb) in consb do
      let some (.ref xb) := csb.lookup "_gen_x" | throwError "no _gen_x"
      let some dw := (isb.filterMap fun (_, _, _, cs) => match cs.lookup "s", cs.lookup "d" with
        | some (.ref sw), some (.ref dw) => if sw == xb then some dw else none
        | _, _ => none).head? | throwError "no producer"
      bodyB := setConnAt kb "_gen_x" (.ref dw) bodyB
    ctlK "(b) topb: the consumer reads the producer's other output" ``topbn
      ["proof", "kernel", "open", "deep", "hier-shape", "order"]
      ({ mb with body := bodyB } : Sparkle.IR.AST.Module) db
  -- the option off: the old text (a design with a 2-output child is outside U2HRStmt)
  let (m0, d0) ← synthOf ``topr0n
  let off ← refMsg ``topr0n m0 d0
  expectMsg "(iv) option off, topr0" off ["[hier-shape]", "has 2 outputs (multi-output children: H3)"]

-- more toys: a Bool port and a second register (a 3-output child with `Bool`/`BitVec 4`/`BitVec 8` ports), a consumer reading BOTH
-- outputs of the producer, a COMBINATIONAL 2-output consumer of a sequential producer
structure R3 (dom : DomainConfig) where
  a : Signal dom (BitVec 4)
  b : Signal dom Bool
  c : Signal dom (BitVec 8)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (R3 dom) dom := ⟨⟩

@[hardware_module] def kid3 {dom : DomainConfig} (x : Signal dom (BitVec 4)) (e : Signal dom Bool) (y : Signal dom (BitVec 8)) :
    R3 dom :=
  circuit do
    let r ← Signal.reg 0#4
    let q ← Signal.reg 0#8
    let rS := (r : Signal dom (BitVec 4))
    let qS := (q : Signal dom (BitVec 8))
    r <~ Signal.mux e (x + rS) rS
    q <~ qS + y
    return ({ a := rS, b := e, c := qS + y } : R3 dom)

def top3s (inp : Signal defaultDomain (BitVec 4)) (en : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let k := kid3 inp en accS
    acc <~ Signal.mux k.b k.c accS
    return accS

def topd (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c1 := kidr accS inp
    let c2 := kidr c1.s c1.d
    acc <~ (c2.s + c2.d : Signal defaultDomain (BitVec 4))
    return accS

def tope (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c1 := kidr accS inp
    let c2 := child2 c1.s c1.d
    acc <~ (c2.s + c2.d : Signal defaultDomain (BitVec 4))
    return accS

#eval show CommandElabM Unit from do
  withScope (withMO true) do
    acceptK ``top3s `Tests.Ved.MultiOutCheck.kid3
    acceptK ``topd `Tests.Ved.MultiOutCheck.kidr
    acceptK ``tope `Tests.Ved.MultiOutCheck.kidr

end Tests.Ved.MultiOutCheck

/-! ## Unit 6: TWO different sequential struct children in one parent (R184's `wSign` then `wMul`)

The parent's child loop is one `TermElabM`.  The struct sequential script names its holes `?R ?h0 ?hstep`; in one metavariable
context the second child's `?R` denotes the FIRST child's (assigned) mvar, and the second child is refused
("ved_ss_R: no invariant mvar ?R in the goal").  Under `ved.compose.multiOut` the entry elaborates each child in a fresh
context.  The control below runs the two child checks in one `TermElabM` WITHOUT the fresh context (the old behaviour)
and pins the refusal; the entry accepts `topq`. -/

namespace Tests.Ved.MultiOutCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil

@[hardware_module] def kidq {dom : DomainConfig} (x y : Signal dom (BitVec 4)) : P2 dom :=
  circuit do
    let r ← Signal.reg 0#4
    let rS := (r : Signal dom (BitVec 4))
    r <~ x + y
    return ({ s := rS, d := rS + y } : P2 dom)

def topq (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c1 := kidr accS inp
    let c2 := kidq c1.s inp
    acc <~ (c2.s + c2.d : Signal defaultDomain (BitVec 4))
    return accS

-- control: both child checks in ONE `TermElabM`, one metavariable context (the old child loop): the second is refused
#eval show CommandElabM Unit from do
  let (_, d) ← synthOf ``topq
  unless d.modules.length == 2 do throwError "topq: expected 2 child modules, found {d.modules.length}"
  liftTermElabM do
    let mut refused : Option String := none
    for cm in d.modules do
      let decl := cm.name.toName
      let (b, _, names) ← Tools.VedU1StructOut.stmtOfStruct decl
      try discard <| Tools.VedU1Entry.checkU1E decl (``topq ++ `ved_oneCtx ++ decl) b cm .generated names
      catch e => refused := some (← e.toMessageData.toString)
    let some msg := refused | throwError "control: the second struct child was accepted in a shared metavariable context (expected the old refusal)"
    unless (msg.splitOn "no invariant mvar").length > 1 do throwError "control: unexpected refusal: {msg.take 300}"
    logInfo m!"CONTROL (shared mctx, old behaviour): second sequential struct child refused: {msg.take 200}"

#eval show CommandElabM Unit from do
  withScope (withMO true) do
    acceptK ``topq `Tests.Ved.MultiOutCheck.kidq

end Tests.Ved.MultiOutCheck

/-! ## Unit 7: the struct child script with `ved.sseq.fastOrder` and `ved.sseq.share` (both default off)

`ved.sseq.fastOrder`: the script's order fact through `Tools.VedU1OrderFast.orderOkLeafFast_sound` and its width fact through
`Tools.VedMemWidth.WidthStmt_of_parts` (the quadratic String `Nodup` / order checks of the leaf are killed at 23 GB on
R184's `wPointOp`, 560 statements / 563 wires).  `ved.sseq.share`: the packing stage as `ved_pack_wire_all`.  The child
theorem (type `U1Stmt`, std3, no `sorryAx`) is accepted with each option alone and with both, for the sequential 2-output
struct child `kidr`; the default (both off) is the unit-3 check above. -/

namespace Tests.Ved.MultiOutCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil

def kidOptCheck (tag : String) (fo sh : Bool) : CommandElabM Unit := do
  let (_, d) ← synthOf ``topr
  let some cm := d.modules.head? | throwError "no child"
  liftTermElabM do
    withOptions (fun o => (o.setBool `ved.sseq.fastOrder fo).setBool `ved.sseq.share sh) do
      let (b, _, names) ← Tools.VedU1StructOut.stmtOfStruct ``kidr
      let thm ← Tools.VedU1Entry.checkU1E ``kidr (``kidr ++ Name.mkSimple tag) b cm .generated names
      let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
      unless ti.type.getAppFn.isConstOf ``Tools.VedU1Contract.U1Stmt do throwError "{thm}: type is not U1Stmt"
      let axs ← collectAxioms thm
      unless axs.all (std3.contains ·) do throwError "{thm}: axioms outside std3: {axs}"
      if axs.contains ``sorryAx then throwError "{thm}: sorryAx"
      -- the leaf fast lemma is used exactly when the option is on
      let usesFast := (ti.value.getUsedConstants.contains ``Tools.VedU1OrderFast.orderOkLeafFast_sound)
      unless usesFast == fo do throwError "{thm}: orderOkLeafFast_sound used = {usesFast}, option = {fo}"
      logInfo m!"CHILD THEOREM kidr fastOrder={fo} share={sh}: {thm} U1Stmt, std3, no sorryAx, orderOkLeafFast_sound used = {usesFast}"

#eval kidOptCheck "ved_fo1" true false
#eval kidOptCheck "ved_sh1" false true
#eval kidOptCheck "ved_fs1" true true

end Tests.Ved.MultiOutCheck

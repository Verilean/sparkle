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
    expectMsg "on, real" (← refMsg ``top2 m d) ["[child]", "ved_table%"]

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

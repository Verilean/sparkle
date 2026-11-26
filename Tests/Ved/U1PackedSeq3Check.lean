import Tools.VedU1PackedEntry

/-!
# Checks for the size gate of the per-statement first attempt (`sparkle-ved-packed-seq3`)

`#ved_u1_packed` on a `Signal.loop` body first runs the per-statement script (`Tools/VedU1PackedSeq2.lean`) only when the
summed expanded size of the body's assignments (`Tools.VedU1PackedSeq3.substStats`) is within `ved.packedseq3.maxExp`
(default 20000); a larger body goes straight to the flat loop script.  R23 (`mmuTopSignal`, sum 44568) otherwise ran the first
attempt to the whole proof budget (8·10^9 heartbeats, 520 s) before the fallback.  The contract and the statement are unchanged.

* `substStats` on hand-written bodies (sum / maximum of the expanded sizes; a shared wire counts at every use) and on the
  modules of the positives below (all far below the default bound).
* The gate decision: a doubling chain of 30 assignments (expanded size 2^30) is skipped and costs nothing
  (`firstAttemptOk` is a size computation on the body, no tactic runs); the positives are within the bound.
* Positives, default option: the proof still comes from the per-statement script (`step_seq` in the proof), type `==` the
  expected `PackedStmt`, standard axioms, the hand-written contract.
* Gate engaged (`ved.packedseq3.maxExp 0`): the same declaration is still accepted (flat loop script), the stored type is the
  same, the proof does NOT use `step_seq` (the first attempt did not run).
* Refusals are unchanged with the gate engaged: one control kind, a module whose OUTPUT is altered by a constant, is refused
  at `[proof]` and nothing is left behind (no altered-register-update control here).
-/

namespace Tests.Ved.U1PackedSeq3Check

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.AST
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Packed Tools.VedU1PackedEntry Tools.VedU1PackedSeq3

/-! ## `substStats` -/

def ref (n : String) : Sparkle.IR.AST.Expr := .ref n
def add (a b : Sparkle.IR.AST.Expr) : Sparkle.IR.AST.Expr := .op .add [a, b]

/-- a := 5, b := a + a, c := b + a, d := slice c: expanded sizes 1, 3, 5, 6 (a shared wire counts at every use) -/
def chain : List Stmt :=
  [.assign "a" (.const 5 8), .assign "b" (add (ref "a") (ref "a")), .assign "c" (add (ref "b") (ref "a")),
   .assign "d" (.slice (ref "c") 3 0)]

#guard (substStats chain).nAssign == 4
#guard (substStats chain).sumExp == 1 + 3 + 5 + 6
#guard (substStats chain).maxExp == 6
#guard (substStats chain).own == 1 + 3 + 3 + 2
#guard (substStats chain).nRegs == 0

-- inputs and registers (names no assignment defines) count 1 each
#guard (substStats [.assign "x" (add (ref "in") (ref "reg"))]).sumExp == 3

/-- a doubling chain: every wire is used twice by the next one -/
def doubling (n : Nat) : List Stmt :=
  (.assign "w0" (.const 1 8)) :: (List.range n).map fun i => .assign s!"w{i+1}" (add (ref s!"w{i}") (ref s!"w{i}"))

#guard (substStats (doubling 10)).maxExp == 2 ^ 11 - 1

-- the gate: a small body runs the first attempt, the doubling chain does not
/-- info: [true, false] -/
#guard_msgs in
run_cmd do
  let a ← liftCoreM (firstAttemptOk chain)
  let b ← liftCoreM (firstAttemptOk (doubling 30))
  logInfo m!"{[a, b]}"

/-! ## Declarations (the shapes of `Tests/Ved/U1PackedSeq2Check.lean`, own copies: the entry leaves constants behind) -/

def gCnt (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    let cNext := Signal.mux en (c + d) c
    let fNext := Signal.mux (c === 255#8) (Signal.pure true) f
    bundleAll! [Signal.register 0#8 cNext, Signal.register false fNext]
  bundle2 (projN! st 2 0) (projN! st 2 1)

def gFsm (go done : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 3 × Bool × Bool) :=
  let st := Signal.loop fun state =>
    let s := projN! state 3 0
    let a := projN! state 3 1
    let b := projN! state 3 2
    let sNext := Signal.mux (go &&& (s === 0#3)) (Signal.pure 1#3)
      (Signal.mux (done &&& (s === 1#3)) (Signal.pure 2#3)
        (Signal.mux (s === 2#3) (Signal.pure 0#3) s))
    let aNext := Signal.mux (s === 1#3) (Signal.pure true) (Signal.mux (s === 2#3) (Signal.pure false) a)
    let bNext := (a &&& go) ||| b
    bundleAll! [Signal.register 0#3 sNext, Signal.register false aNext, Signal.register false bNext]
  bundle2 (projN! st 3 0) (bundle2 (projN! st 3 1) (projN! st 3 2))

/-- the gate-engaged copies -/
def gCntOff (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) := gCnt en d
def gFsmOff (go done : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 3 × Bool × Bool) := gFsm go done

/-- control module: the output altered by a constant -/
def gCntConst (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    let cNext := Signal.mux en (c + d) c
    let fNext := Signal.mux (c === 255#8) (Signal.pure true) f
    bundleAll! [Signal.register 0#8 cNext, Signal.register false fNext]
  bundle2 (projN! st 2 0 + 1#8) (projN! st 2 1)

def gCntCtl (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) := gCnt en d

/-! ## The checker -/

def modOf (decl : Name) : TermElabM Sparkle.IR.AST.Module := do
  return (← Sparkle.Compiler.Elab.synthesizeCombinational decl).1

def usesStepSeq (thm : Name) : CoreM Bool := do
  let env ← getEnv
  let mut todo := [thm]
  let mut seen : Std.HashSet Name := {}
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      if n == ``Tools.VedU1ScriptSeq.step_seq then return true
      if let some (.thmInfo ti) := env.find? n then
        todo := ti.value.getUsedConstants.toList ++ todo
  return false

/-- accept `decl` through the entry; the stored type is the expected `PackedStmt`, the axioms are the three standard ones,
`seq` says whether the proof comes from the per-statement script; also `substStats` is within the default bound -/
def checkG (decl : Name) (stmtStx : Term) (seq : Bool) (bounded : Bool) : CommandElabM Unit := liftTermElabM do
  let (m, thm, _) ← vedU1PackedS decl
  let nm := Names.ofBase decl
  let stmt ← instantiateMVars (← Term.elabTerm stmtStx none)
  let expected := mkAppN (Lean.mkConst ``PackedStmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not the expected PackedStmt"
  let r ← Tools.VedStrictAudit.strictAudit thm
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) && r.axioms.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  unless (← usesStepSeq thm) == seq do throwError "{thm}: step_seq in the proof is {!seq}, expected {seq}"
  let st := substStats (orderBody m.body)
  unless (decide (st.sumExp ≤ 20000)) == bounded do throwError "{decl}: substStats {repr st}"
  logInfo m!"packed seq3 OK {thm} step_seq={seq} sumExp={st.sumExp}"

/-! ## Positives: the gate lets the per-statement script run -/

/-- info: packed seq3 OK Tests.Ved.U1PackedSeq3Check.gCnt.ved_u1 step_seq=true sumExp=78 -/
#guard_msgs in
run_cmd checkG ``gCnt (← `(gCnt)) true true

/-- info: packed seq3 OK Tests.Ved.U1PackedSeq3Check.gFsm.ved_u1 step_seq=true sumExp=327 -/
#guard_msgs in
run_cmd checkG ``gFsm (← `(gFsm)) true true

/-! ## Gate engaged: skipped at once, same statement, flat loop script -/

/-- info: packed seq3 OK Tests.Ved.U1PackedSeq3Check.gCntOff.ved_u1 step_seq=false sumExp=78 -/
#guard_msgs in
set_option ved.packedseq3.maxExp 0 in
run_cmd checkG ``gCntOff (← `(gCntOff)) false true

/-- info: packed seq3 OK Tests.Ved.U1PackedSeq3Check.gFsmOff.ved_u1 step_seq=false sumExp=327 -/
#guard_msgs in
set_option ved.packedseq3.maxExp 0 in
run_cmd checkG ``gFsmOff (← `(gFsmOff)) false true

/-! ## Controls: refusals unchanged with the gate engaged -/

def checkerNames (base : Name) : List Name :=
  [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1].map (base ++ ·)

def expectRefused (stage : String) (base : Name) (act : TermElabM Unit) : CommandElabM Unit := liftTermElabM do
  let accepted ← try act; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith "VED U1 REFUSED" && (s.splitOn s!"[{stage}]").length > 1 do throw e
    pure false
  if accepted then throwError "control ACCEPTED (expected a refusal at [{stage}])"
  for n in checkerNames base do
    if (← getEnv).contains n then throwError "left behind: {n}"
  logInfo m!"refused [{stage}], clean"

def onMap (decl : Name) (slices : List (Nat × Nat)) (m : Sparkle.IR.AST.Module) : TermElabM Unit := do
  let (stmt, _, tbl) ← packedStmtOf decl
  discard <| checkPackedE decl stmt tbl slices m .generated

/-- info: refused [proof], clean -/
#guard_msgs in
set_option ved.packedseq3.maxExp 0 in
run_cmd expectRefused "proof" ``gCntCtl do onMap ``gCntCtl [(1, 8), (0, 1)] (← modOf ``gCntConst)

-- the same refusal with the default gate (the first attempt runs and fails)
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``gCntCtl do onMap ``gCntCtl [(1, 8), (0, 1)] (← modOf ``gCntConst)

end Tests.Ved.U1PackedSeq3Check

import Tools.VedU2HierRegEntry
import Tests.Ved.U2HierWireCheck
import Tests.Ved.U2HierStateCallCheck
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for the partial generation of the open parent's deep facts (H2c-state)

`checkU2HR` runs `#verify_elab_deep` on the open parent, whose ports are proved one by one.  A failure of a port
the proof does not use is tolerated, but RECORDED (`VED U2 HIER PARTIAL-DEEP …` info lines: the open parent, the
used port, the failing ports, the number of errors and the first error per failing port); every other error
(an error of the used port, one tied to no port, a missing state theorem the proof needs) is refused at `[deep]`,
and a `sorry` or a non-standard axiom in a used fact is refused by the strict audit of the final theorem.

`stPortX` is a parent with three registers and TWO ports (`x`: the child `diff2` on the registers `a`, `b`; `y`: the
register `c`); the proof uses port `x`.  No real parent of the corpus has a port that fails and another that
exports the loop state in a small module, so the controls simulate the deep run's outcome with the checker's
test hook `tamper` (it runs right after the deep command, on the real `Phase1` and the real messages):
* `failPort p` removes port `p`'s `PROVEN` line and logs an error, as a port block that aborted does;
* `twin` copies every deep constant of the open parent under a twin name (the same types, the same values) and
  continues with the twin, optionally with ONE used fact replaced by a `sorry` proof or by a local `axiom`, or
  with the state theorems left out.
The final check, the proof and the audit are the real ones.
-/

namespace Tests.Ved.U2HierPartialDeepCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU2Hier Tools.VedU2HierEntry Tools.VedU2HierRegEntry Tests.Ved.U2HierWireCheck
  Tests.Ved.U2HierStateCallCheck

structure StOut where
  x : Signal defaultDomain (BitVec 4)
  y : Signal defaultDomain (BitVec 4)

instance : Sparkle.Core.HasDomain StOut defaultDomain := ⟨⟩

def stPorts (trigger : Signal defaultDomain Bool) : StOut :=
  circuit do
    let a ← Signal.reg 0#4
    let b ← Signal.reg 0#4
    let c ← Signal.reg 1#4
    let aS := (a : Signal defaultDomain (BitVec 4))
    let cS := (c : Signal defaultDomain (BitVec 4))
    a <~ Signal.mux trigger (aS + cS) aS
    b <~ aS
    c <~ cS + 1#4
    return { x := diff2 aS (b : Signal defaultDomain (BitVec 4)), y := cS }

/-- The clean positive. -/
def stPortX (trigger : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) := (stPorts trigger).x

/-- The untouched twin (accepted). -/
def stPortT (trigger : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) := (stPorts trigger).x

/-- The partial generation (accepted, recorded). -/
def stPortF (trigger : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) := (stPorts trigger).x

/-- The declaration the refusal controls run on (never accepted, so nothing is left under its name). -/
def stPortR (trigger : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) := (stPorts trigger).x


/-! ## The tamper hooks -/

/-- Remove the `PROVEN` line of port `p` and log an error, as a block that failed does. -/
def failPort (p : String) (msg : String := "simulated failure") : Phase1 → CommandElabM Phase1 := fun p1 => do
  let mut kept := []
  for m in (← get).messages.toList do
    let isP := m.severity == MessageSeverity.information &&
      ((← m.data.toString).splitOn s!".{p}: PROVEN via").length > 1
    unless isP do kept := kept ++ [m]
  let mut log : MessageLog := {}
  for m in kept do log := log.add m
  modify fun s => { s with messages := log }
  logError msg
  pure p1

/-- An error that belongs to no port: logged after every port has its `PROVEN` line. -/
def strayError : Phase1 → CommandElabM Phase1 := fun p1 => do
  logError "simulated stray error"
  pure p1

inductive Twist | none | sorryOf (suffix : String) | axiomOf (suffix : String) | noState

/-- Continue with a twin of the open parent's deep constants: every constant whose name lies under the open
parent's name stem (the open parent itself, `_deep`, `_nm`, `_deep_state`, … and their auxiliary lemmas) is copied
under the stem `…Tw`, types and values with the names renamed, so the copy is a complete, independent set of facts.
`tw` changes ONE theorem (by its suffix) to a `sorry` proof or to a proof by a local axiom, or leaves the state
theorems out. -/
def twin (tw : Twist) : Phase1 → CommandElabM Phase1 := fun p1 => do
  let open_ := p1.opn.openName
  let l := open_.getString!
  let pre := open_.getPrefix
  let env ← getEnv
  -- the stem a constant lies under (`pre ++ l…`), if any, and the suffix after the stem
  let rootOf (n : Name) : Option Name :=
    let rec go (m : Name) : Option Name :=
      match m with
      | .str q s' => if q == pre && s'.startsWith l then some m else go q
      | .num q _ => go q
      | .anonymous => none
    go n
  let tnRoot (r : Name) : Name := .str pre (l ++ "Tw" ++ ((r.getString!.drop l.length).toString))
  -- the axioms `native_decide` declares (`…._native.…`) stand for COMPILED code of the original and are not copied
  let ren (n : Name) : Option Name :=
    if (n.components.any (·.toString == "_native")) then none
    else (rootOf n).map fun r => n.replacePrefix r (tnRoot r)
  let valOf (ci : ConstantInfo) : Lean.Expr := match ci with
    | .defnInfo d => d.value
    | .thmInfo t => t.value
    | _ => Lean.mkConst ``True
  let seed := env.constants.map₂.toList.filterMap fun (n, ci) => (ren n).map fun n' => (n, n', ci)
  -- constants realised on demand (equation lemmas, …) are not in `map₂`: add whatever a copied constant mentions
  let mut todo := seed
  let mut seen : NameSet := seed.foldl (fun acc (n, _, _) => acc.insert n) {}
  let mut work := seed
  while !work.isEmpty do
    let mut more := []
    for (_, _, ci) in work do
      for c in ci.type.getUsedConstants ++ (valOf ci).getUsedConstants do
        if (ren c).isSome && !seen.contains c then
          seen := seen.insert c
          if let some cic := env.find? c then more := more ++ [(c, (ren c).get!, cic)]
    todo := todo ++ more
    work := more
  let rename (e : Lean.Expr) : Lean.Expr :=
    e.replace fun x => match x with
      | .const c lv => (ren c).map fun c' => Lean.mkConst c' lv
      | _ => none
  let isStateThm (n : Name) : Bool := match n with | .str _ s' => s'.endsWith "_deep_state" | _ => false
  let sufOf (n : Name) : String := match rootOf n with | some r => (r.getString!.drop l.length).toString | none => ""
  liftCoreM <| withOptions (fun o => o.setBool `Elab.async false) do
    let mut pending := todo.filter fun (n, _, _) => !(match tw with | .noState => isStateThm n | _ => false)
    let mut added : NameSet := {}
    let mut fuel := pending.length + 1
    while !pending.isEmpty && fuel > 0 do
      fuel := fuel - 1
      let mut next := []
      for (n, n', ci) in pending do
        let deps := (ci.type.getUsedConstants ++ (valOf ci).getUsedConstants).filter fun c => (ren c).isSome && c != n
        if deps.all fun c => added.contains c then
          match ci with
          | .defnInfo d =>
            addDecl (.defnDecl { d with name := n', type := rename d.type, value := rename d.value, hints := .abbrev })
          | .thmInfo t =>
            let ty := rename t.type
            let value ← match tw with
              | .sorryOf suf =>
                if sufOf n == suf then pure (mkApp2 (Lean.mkConst ``sorryAx [Level.zero]) ty (Lean.mkConst ``Bool.false))
                else pure (rename t.value)
              | .axiomOf suf =>
                if sufOf n == suf then
                  let ax := n'.appendAfter "_ax"
                  addDecl (.axiomDecl { name := ax, levelParams := t.levelParams, type := ty, isUnsafe := false })
                  pure (Lean.mkConst ax (t.levelParams.map mkLevelParam))
                else pure (rename t.value)
              | _ => pure (rename t.value)
            addDecl (.thmDecl { t with name := n', type := ty, value })
          | .axiomInfo a => addDecl (.axiomDecl { a with name := n', type := rename a.type })
          | _ => throwError "twin: {n} is neither a definition, a theorem nor an axiom"
          enableRealizationsForConst n'
          added := added.insert n
        else next := next ++ [(n, n', ci)]
      pending := next
    unless pending.isEmpty do throwError "twin: {pending.length} constants could not be copied (dependency cycle or a missing one)"
  pure { p1 with opn := { p1.opn with openName := tnRoot open_ } }

/-! ## Runs -/

def prep (decl : Name) : CommandElabM (Lean.Expr × Nat × Sparkle.IR.AST.Module × Design) := do
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  let (m, d) ← synthOf decl
  pure (stmt, nDom, m, d)

/-- The checker must ACCEPT; the stored theorem has the exact statement and standard axioms. -/
def expectAcc (decl : Name) (tamper : Phase1 → CommandElabM Phase1) : CommandElabM Unit := do
  let (stmt, nDom, m, d) ← prep decl
  let (thm, _, _) ← checkU2HR decl stmt nDom m d none tamper
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U2HRStmt c m d decl"
    discard <| Tools.VedStrictAudit.strictAudit thm
    std3Only thm

/-- The checker must REFUSE at `stage`, the message names `needle`, nothing is left behind. -/
def expectRef (decl : Name) (stage needle : String) (tamper : Phase1 → CommandElabM Phase1) : CommandElabM Unit := do
  let before ← localConsts
  let (stmt, nDom, m, d) ← prep decl
  let r ← try
      discard <| checkU2HR decl stmt nDom m d none tamper
      pure none
    catch e => pure (some (← liftTermElabM (e.toMessageData.toString)))
  let pre := s!"VED U1 REFUSED {decl} [{stage}]"
  match r with
  | none => throwError "{decl}: expected a refusal at [{stage}], the checker ACCEPTED"
  | some msg =>
    unless msg.startsWith pre do throwError "expected {pre}, got: {msg.take 600}"
    unless (msg.splitOn needle).length > 1 do throwError "the refusal does not name `{needle}`: {msg.take 600}"
  let after ← localConsts
  let added := after.toList.filter (!before.contains ·)
  unless added.isEmpty do throwError "constants left after the refusal: {added}"
  unless (← get).messages.toList.all (·.severity != MessageSeverity.error) do
    throwError "errors left in the message log after the refusal"

set_option maxRecDepth 100000

/-! ## A clean positive: no PARTIAL-DEEP line (the log is exactly the checker's own, so `#guard_msgs` sees none) -/

#guard_msgs in
run_cmd expectAcc ``stPortX pure

/-! ## The twin machinery itself: the untouched twin is accepted (so a refusal below is due to the one change) -/

#guard_msgs in
run_cmd expectAcc ``stPortT (twin .none)

/-! ## ACCEPTED: an unused port fails, the used port's facts exist -> accepted AND recorded -/

/--
info: VED U2 HIER PARTIAL-DEEP Tests.Ved.U2HierPartialDeepCheck.stPortF: open parent Tests.Ved.U2HierPartialDeepCheck.stPortF.ved_open_Tests_Ved_U2HierPartialDeepCheck_stPortF, used port x, failed ports [y], 1 errors tolerated (ports the proof does not use)
---
info: VED U2 HIER PARTIAL-DEEP Tests.Ved.U2HierPartialDeepCheck.stPortF: port y, 1 errors, first: simulated failure
-/
#guard_msgs in
run_cmd expectAcc ``stPortF (failPort "y")

/-! ## The decision itself (`attributeDeepErrors`, `deepVerdict`) on message lists -/

private def okMsg (p : String) : Bool × String := (false, s!"#verify_elab_deep o.{p}: PROVEN via Cdo.elab_general — t")
private def errMsg (t : String) : Bool × String := (true, t)

-- errors before a `PROVEN` line belong to that port; the trailing ones to the first port without one
#guard attributeDeepErrors ["x", "y", "z"] [okMsg "x", errMsg "e1", okMsg "y", errMsg "e2"] ==
  ([], [("y", ["e1"]), ("z", ["e2"])])
#guard attributeDeepErrors ["x"] [okMsg "x", errMsg "e"] == (["e"], [])
-- an error of an unused port, the used port `x` exported its state: tolerated, with the counts
#guard (deepVerdict true ["x", "y"] (· == "x") [okMsg "x", errMsg "boom"]).toOption == some (some ("x", [("y", 1, "boom")]))
-- no error: nothing to record
#guard (deepVerdict true ["x", "y"] (· == "x") [okMsg "x", okMsg "y"]).toOption == some none
-- an error of the used port, one tied to no port, no exported state, no port, no call on the state: refused
#guard (deepVerdict true ["x", "y"] (· == "x") [errMsg "boom"]).toOption.isNone
#guard (deepVerdict true ["x", "y"] (· == "x") [okMsg "x", okMsg "y", errMsg "boom"]).toOption.isNone
#guard (deepVerdict true ["x", "y"] (fun _ => false) [okMsg "x", errMsg "boom"]).toOption.isNone
#guard (deepVerdict true [] (fun _ => false) [errMsg "boom"]).toOption.isNone
#guard (deepVerdict false ["x", "y"] (· == "x") [okMsg "x", errMsg "boom"]).toOption.isNone

/-! ## REFUSED -/

/- an error of the USED port (its `PROVEN` line is gone, the error is tied to it) -/
run_cmd expectRef ``stPortR "deep" "an error of the port x, which the proof uses" (failPort "x")

/- an error tied to NO port (every port proved, an error is logged anyway) -/
run_cmd expectRef ``stPortR "deep" "an error is tied to no port" strayError

/- the needed state theorem missing (no port exported the loop state) -/
run_cmd expectRef ``stPortR "deep" "no port of the open parent exported its loop state" (twin .noState)

/- a `sorry` in a used deep fact (the state theorem of the used port) -/
run_cmd expectRef ``stPortR "audit" "sorryAx" (twin (.sorryOf "_x_deep_state"))

/- a non-standard axiom in a used deep fact (a local `axiom` the state theorem is made of) -/
run_cmd expectRef ``stPortR "audit" "_x_deep_state_ax" (twin (.axiomOf "_x_deep_state"))

/-- info: partial-deep controls: 1 accepted and recorded (stPortF), 5 refused (used-port error, stray error, state theorem missing, sorry, local axiom), clean positives print no PARTIAL-DEEP line -/
#guard_msgs in
run_cmd logInfo m!"partial-deep controls: 1 accepted and recorded (stPortF), 5 refused (used-port error, stray error, state theorem missing, sorry, local axiom), clean positives print no PARTIAL-DEEP line"

end Tests.Ved.U2HierPartialDeepCheck

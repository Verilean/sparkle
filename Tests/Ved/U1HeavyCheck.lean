import Tools.VedU1Entry
import Tools.VedStrictAudit
import Sparkle
import Sparkle.Compiler.Elab
import IP.YOLOv8.Primitives.MaxPool
import IP.YOLOv8.Primitives.Requantize

set_option maxRecDepth 4096

/-!
# `#ved_u1` on signed select trees and on a signed product with a shift and a clamp (sparkle-ved-u1-heavy)

The real rows `Sparkle.IP.YOLOv8.Primitives.MaxPool.maxPool2x2` (four signed INT8 inputs, a `max` tree of
`slt`) and `Sparkle.IP.YOLOv8.Primitives.Requantize.requantize` (INT32 accumulator times a sign-extended
unsigned 16-bit scale, arithmetic shift by a 5-bit selector, clamp to INT8) were refused at `[proof]`
(heartbeats): the wide path of the flat script opens every signed value into a case split on its sign bit,
once per case of the selector.  `Tools/VedU1Heavy.lean` is a capped first try inside the flat script of a
combinational module with wide data inputs and a signed comparison or arithmetic shift
(`scriptFor … (heavy := 1)`): both sides brought to one form with `toSigned` kept whole
(`ved_heavy_norm`), the wrap-around product and the shifted value named by variables with their ranges
(`ved_gen_atoms`, `ved_gen_shifts`), one case split per distinct condition (`ved_heavy_close`).  When the
try fails (error, heartbeat cap, more than 24 cases) the flat tactics run as before from the same state.

What is fixed here, at the smallest sizes that exercise each shape and on the two real rows:
1. `#ved_u1` accepts `smax3` (three 6-bit inputs: a select tree, 18 bits), `smax4` (four 8-bit: the
   `maxPool2x2` shape), `qreq` (10 + 4 + 3 bits: product, shift, clamp), and the two real rows;
   the stored type of `<decl>.ved_u1` compared with `==` against `U1Stmt <decl>.ved_contract
   <decl>.ved_mod (@decl defaultDomain)`, axioms within std3;
2. the heavy tactics ALONE (`heavy := 2`: under the cap of the try, no flat fallback) accepts `smax3` and `qreq`;
3. refusals (`expectRefused`, stage `[proof]`, no `ved_*` constant left) of the heavy tactics alone on the
   module with one change each: the signed compare read as unsigned (select tree and clamp), the operands of
   the compare exchanged (both), the arithmetic shift read as logical, a clamp bound changed (7 becomes 6), the
   sign-extension constant of the scale (63 becomes 31);
4. the failure path of `first | ved_heavy_try (HEAVY) | FLAT` (section 5): the fallback runs from the original
   goal and context after a try that changed them; a heartbeat cap and a recursion limit inside the try are
   ordinary errors; the try stops at what is left of the caller's heartbeat limit (a fix: it used to get the
   caller's whole limit again); at entry level a capped try falls back to the flat tactics, and a small caller
   limit refuses `smax3` at `[proof]`, clean.
-/

namespace Tests.Ved.U1HeavyCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry

/-! ## 1. Shapes -/

def smax2 {dom : DomainConfig} {n : Nat} (a b : Signal dom (BitVec n)) : Signal dom (BitVec n) :=
  Signal.mux (Signal.slt b a) a b

def smax3 {dom : DomainConfig} (a b c : Signal dom (BitVec 6)) : Signal dom (BitVec 6) :=
  smax2 (smax2 a b) c

def smax4 {dom : DomainConfig} (a b c d : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  smax2 (smax2 a b) (smax2 c d)

def qMul {dom : DomainConfig} (acc : Signal dom (BitVec 10)) (scale : Signal dom (BitVec 4)) :
    Signal dom (BitVec 10) :=
  let sIsNeg := (scale.map (BitVec.extractLsb' 3 1 ·)) === 1#1
  let scaleExt := Signal.mux sIsNeg (BitVec.ofNat 6 0x3F ++ scale) (0#6 ++ scale)
  acc * scaleExt

def qShift {dom : DomainConfig} (val : Signal dom (BitVec 10)) (shift : Signal dom (BitVec 3)) :
    Signal dom (BitVec 10) :=
  Signal.ashr val (0#7 ++ shift)

def qClamp {dom : DomainConfig} (val : Signal dom (BitVec 10)) : Signal dom (BitVec 4) :=
  let over := Signal.slt (Signal.pure (BitVec.ofNat 10 7)) val
  let under := Signal.slt val (Signal.pure (BitVec.ofInt 10 (-8)))
  Signal.mux over (Signal.pure 7#4)
    (Signal.mux under (Signal.pure (BitVec.ofInt 4 (-8))) (val.map (BitVec.extractLsb' 0 4 ·)))

def qreq {dom : DomainConfig} (acc : Signal dom (BitVec 10)) (scale : Signal dom (BitVec 4))
    (shift : Signal dom (BitVec 3)) : Signal dom (BitVec 4) :=
  qClamp (qShift (qMul acc scale) shift)


def smax2w {dom : DomainConfig} (a b : Signal dom (BitVec 9)) : Signal dom (BitVec 9) :=
  smax2 a b

/-! ## 2. Positive -/

#guard_msgs (drop info) in
#ved_u1 smax3

#guard_msgs (drop info) in
#ved_u1 smax4

#guard_msgs (drop info) in
#ved_u1 qreq

#guard_msgs (drop info) in
#ved_u1 Sparkle.IP.YOLOv8.Primitives.MaxPool.maxPool2x2

#guard_msgs (drop info) in
#ved_u1 Sparkle.IP.YOLOv8.Primitives.Requantize.requantize

/-- the stored type is `U1Stmt c m (@decl defaultDomain)` (`==`), axioms within std3 -/
def checkRow (decl : Name) : CoreM Unit := do
  let nm := Names.ofBase decl
  let thm := decl ++ `ved_u1
  let stmt := mkApp (Lean.mkConst decl) (Lean.mkConst ``Sparkle.Core.Domain.defaultDomain)
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not U1Stmt c m ({decl} defaultDomain)"
  let ax ← collectAxioms thm
  unless ax.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do throwError "{thm}: axioms {ax}"

/-- info: OK 5 rows: stored type = U1Stmt c m F, axioms within std3 -/
#guard_msgs in
run_cmd liftCoreM do
  checkRow ``smax3
  checkRow ``smax4
  checkRow ``qreq
  checkRow ``Sparkle.IP.YOLOv8.Primitives.MaxPool.maxPool2x2
  checkRow ``Sparkle.IP.YOLOv8.Primitives.Requantize.requantize
  logInfo "OK 5 rows: stored type = U1Stmt c m F, axioms within std3"

/-! ## 3. The heavy script alone -/

def checkerNames (base : Name) : List Name :=
  [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1].map (base ++ ·)

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

/-- the heavy script as the proof source: `heavy := 2` alone (under the cap of `ved_heavy_try`, no flat
fallback: the flat script on a false statement runs for minutes by design, so the refusals below test the
heavy script itself), `heavy := 1` the script of the entry (the capped heavy try, then the flat tactics) -/
def heavyProof (decl : Name) (nDom : Nat) (heavy : Nat := 2) : ProofSrc :=
  .built fun nm m => do
    let clkRst := clkRstOf m
    let inNames := (dataPortsOf m clkRst).map fun p => p.name
    let widths := m.inputs.filter (fun p => match clkRst with | some (k, r) => p.name != k && p.name != r | none => true) |>.map fun p => match p.ty with | .bitVector w => w | .bit => 1 | _ => 100
    scriptFor nm decl nDom (regShape m) inNames (bodyHasEq m.body) none (← helperConsts decl) widths none (heavy := heavy)

def modOfDecl (decl : Name) : TermElabM Sparkle.IR.AST.Module := do
  let (m, _) ← Sparkle.Compiler.Elab.synthesizeCombinational decl
  return m

abbrev IRExpr := Sparkle.IR.AST.Expr

/-- rewrite every top-level assignment expression -/
def mapAssign (f : IRExpr → IRExpr) (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .assign n e => .assign n (f e)
      | s => s }

/-- signed compare read as unsigned (wrong sign) -/
def sgnU : IRExpr → IRExpr
  | .op .lt_s args => .op .lt_u args
  | e => e

/-- operands of the signed compare exchanged -/
def swapLt : IRExpr → IRExpr
  | .op .lt_s [a, b] => .op .lt_s [b, a]
  | e => e

/-- arithmetic shift read as logical (wrong sign) -/
def asrToShr : IRExpr → IRExpr
  | .op .asr args => .op .shr args
  | e => e

/-- a clamp bound changed: the constant 7 (the largest 4-bit signed value) becomes 6 -/
def constOff : IRExpr → IRExpr
  | .const 7 w => .const 6 w
  | e => e

/-- the sign-extension constant of the scale loses a bit -/
def padOff : IRExpr → IRExpr
  | .const 63 6 => .const 31 6
  | e => e

def differs (f : IRExpr → IRExpr) (m : Sparkle.IR.AST.Module) : Bool := !(decide (mapAssign f m = m))


/-- info: heavy script alone accepts, stored type = U1Stmt c m F, axioms within std3 -/
#guard_msgs in
run_cmd do
  liftTermElabM do
    for (d, tag) in [(``smax3, `ctlHeavyS3), (``qreq, `ctlHeavyQ)] do
      let (stmt, _, names) ← stmtOf d
      let thm ← checkU1E d tag stmt (← modOfDecl d) (heavyProof d 1) names
      let nm := Names.ofBase tag
      let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
      let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
      unless ti.type == expected do throwError "{thm}: stored type differs"
      let ax ← collectAxioms thm
      unless ax.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do throwError "{thm}: axioms {ax}"
  logInfo "heavy script alone accepts, stored type = U1Stmt c m F, axioms within std3"

/-! ## 4. Refusals -/

/-- info: mutations differ from the original -/
#guard_msgs in
run_cmd liftTermElabM do
  let m2 ← modOfDecl ``smax2w
  let mq ← modOfDecl ``qreq
  unless differs sgnU m2 && differs swapLt m2 && differs sgnU mq && differs swapLt mq && differs asrToShr mq
      && differs constOff mq && differs padOff mq do
    throwError "a mutation is the identity"
  logInfo "mutations differ from the original"

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlS2Sign) do
  let (stmt, _, names) ← stmtOf ``smax2w
  discard <| checkU1E ``smax2w `ctlS2Sign stmt (mapAssign sgnU (← modOfDecl ``smax2w)) (heavyProof ``smax2w 1) names

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlS2Swap) do
  let (stmt, _, names) ← stmtOf ``smax2w
  discard <| checkU1E ``smax2w `ctlS2Swap stmt (mapAssign swapLt (← modOfDecl ``smax2w)) (heavyProof ``smax2w 1) names

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlQSign) do
  let (stmt, _, names) ← stmtOf ``qreq
  discard <| checkU1E ``qreq `ctlQSign stmt (mapAssign sgnU (← modOfDecl ``qreq)) (heavyProof ``qreq 1) names

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlQSwap) do
  let (stmt, _, names) ← stmtOf ``qreq
  discard <| checkU1E ``qreq `ctlQSwap stmt (mapAssign swapLt (← modOfDecl ``qreq)) (heavyProof ``qreq 1) names

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlQAsr) do
  let (stmt, _, names) ← stmtOf ``qreq
  discard <| checkU1E ``qreq `ctlQAsr stmt (mapAssign asrToShr (← modOfDecl ``qreq)) (heavyProof ``qreq 1) names

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlQConst) do
  let (stmt, _, names) ← stmtOf ``qreq
  discard <| checkU1E ``qreq `ctlQConst stmt (mapAssign constOff (← modOfDecl ``qreq)) (heavyProof ``qreq 1) names

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlQPad) do
  let (stmt, _, names) ← stmtOf ``qreq
  discard <| checkU1E ``qreq `ctlQPad stmt (mapAssign padOff (← modOfDecl ``qreq)) (heavyProof ``qreq 1) names


/-! ## 5. The fallback and the budget of the heavy try

`scriptFor … (heavy := 1)` ends with `first | ved_heavy_try (HEAVY) | FLAT`.  Tactic level (small goals):
1. the try changes the goal and the context and then fails: `FLAT` runs from the original goal and context;
2. a heartbeat cap and a recursion limit inside the try are ordinary errors, the fallback is reached;
3. the try never runs past what is left of the caller's heartbeat limit.
Entry level: the fallback is reached and accepted on a small signed module (the try capped by the test hook
`ved.u1.heavyHeartbeatsForTest`, default 0 = off: the same module is refused by the heavy tactics alone),
and a small caller limit refuses `smax3` at `[proof]`, clean. -/

open Tools.VedU1Heavy

open Lean Meta Elab Tactic in
/-- TEST: `expect_err "s" (seq)`: `seq` fails with a message containing `s`; the state is put back -/
elab "expect_err " s:str "(" seq:tacticSeq ")" : tactic => do
  let saved ← saveState
  let r ← try evalTactic seq; pure none catch e => pure (some (← e.toMessageData.toString))
  saved.restore
  match r with
  | none => throwError "expect_err: no error"
  | some m => unless (m.splitOn s.getString).length > 1 do throwError "expect_err: unexpected message {m}"

open Lean Meta Elab Tactic in
/-- TEST: `with_rec_depth n (seq)`: `seq` with a recursion limit `n` levels above the current depth -/
elab "with_rec_depth " n:num "(" seq:tacticSeq ")" : tactic =>
  withTheReader Core.Context (fun c => { c with maxRecDepth := c.currRecDepth + n.getNat }) (evalTactic seq)

open Lean Meta Elab Tactic in
/-- TEST: `caller_hb used limit bound (seq)`: `seq` as a caller that has used `used` thousand heartbeats of a
limit of `limit` thousand; it fails with a heartbeat error and has used less than `bound` thousand since the call -/
elab "caller_hb " used:num limit:num bound:num "(" seq:tacticSeq ")" : tactic => do
  let saved ← saveState
  let hb0 ← IO.getNumHeartbeats
  unless hb0 ≥ used.getNat * 1000 do throwError "caller_hb: too few heartbeats counted yet"
  let r ← try
      withTheReader Core.Context
        (fun c => { c with initHeartbeats := hb0 - used.getNat * 1000, maxHeartbeats := limit.getNat * 1000 })
        (evalTactic seq)
      pure none
    catch e => pure (some (← e.toMessageData.toString))
  let hb1 ← IO.getNumHeartbeats
  saved.restore
  let some m := r | throwError "caller_hb: no error"
  unless (m.splitOn "heartbeats").length > 1 do throwError "caller_hb: unexpected message {m}"
  unless (hb1 - hb0) / 1000 < bound.getNat do throwError "caller_hb: the try used {(hb1 - hb0) / 1000}k"

open Lean Meta Elab Tactic in
/-- TEST: the local context holds exactly `n` hypotheses and none is a `ved_*` name -/
elab "ctx_is " n:num : tactic => withMainContext do
  let l := (← getLCtx).foldl (fun a d => if d.isImplementationDetail then a else a.push d) #[]
  unless l.size == n.getNat do throwError "ctx_is: {l.size} hypotheses, expected {n.getNat}"
  for d in l do
    if (d.userName.toString.splitOn "ved_").length > 1 then throwError "ctx_is: leaked {d.userName}"

set_option linter.unusedVariables false

theorem toSigned_lt (x : Nat) (hx : x < 1024) : toSigned 10 (x * 5 % 1024) < 512 := by
  have := toSigned_range 10 (x * 5 % 1024) (by omega) (by omega)
  simp only [Nat.reduceSub, Nat.reducePow] at this
  omega

/-- the heavy tactics on a small goal: `ved_heavy_norm` swaps the branches of `ite (¬ c)`, `ved_gen_atoms`
names the wrap-around argument of `toSigned` (a variable with its range) -/
theorem heavyChanges (x : Nat) (hx : x < 1024) :
    (if ¬ x < 3 then toSigned 10 (x * 5 % 1024) else 0) < 512 := by
  ved_heavy_norm
  ved_gen_atoms
  guard_hyp ved_p0 : Nat
  have := toSigned_range 10 ved_p0 (by omega) (by omega)
  simp only [Nat.reduceSub, Nat.reducePow] at this
  split <;> omega

/-- 1. the try changes the goal and the context (as in `heavyChanges`) and then fails: `first` goes on from the
ORIGINAL goal and context (the goal is the original one, two hypotheses, no `ved_*` name) -/
theorem heavyFallsBack (x : Nat) (hx : x < 1024) :
    (if ¬ x < 3 then toSigned 10 (x * 5 % 1024) else 0) < 512 := by
  first
  | ved_heavy_try (ved_heavy_norm; ved_gen_atoms; guard_hyp ved_p0 : Nat; fail "late failure")
  | (guard_target =ₛ (if ¬ x < 3 then toSigned 10 (x * 5 % 1024) else 0) < 512
     ctx_is 2
     have := toSigned_lt x hx
     split <;> omega)

set_option ved.u1.heavyHeartbeatsForTest 1 in
/-- 2a. a heartbeat cap inside the try is an ordinary error, the fallback is reached -/
theorem heavyHbFallsBack (x : Nat) (hx : x < 1024) :
    (if ¬ x < 3 then toSigned 10 (x * 5 % 1024) else 0) < 512 := by
  expect_err "heartbeats" (ved_heavy_try (ved_heavy_norm; ved_gen_atoms))
  first
  | ved_heavy_try (ved_heavy_norm; ved_gen_atoms; guard_hyp ved_p0 : Nat; split <;> omega)
  | (ctx_is 2; have := toSigned_lt x hx; split <;> omega)

/-- 2b. the recursion limit inside the try is an ordinary error, the fallback is reached -/
theorem heavyRecFallsBack (x : Nat) (hx : x < 1024) :
    (if ¬ x < 3 then toSigned 10 (x * 5 % 1024) else 0) < 512 := by
  expect_err "recursion" (ved_heavy_try (with_rec_depth 2 (ved_heavy_norm; ved_gen_atoms)))
  first
  | ved_heavy_try (with_rec_depth 2 (ved_heavy_norm; ved_gen_atoms; guard_hyp ved_p0 : Nat; split <;> omega))
  | (ctx_is 2; have := toSigned_lt x hx; split <;> omega)

/-- 3. a caller that has used 100k of 150k: the try (a `decide` of about 840k heartbeats, far above both the
cap and the caller's limit) stops with what is left (about 50k), not with the caller's whole limit -/
theorem heavyCallerBudget (x : Nat) (hx : x < 1024) : x < 1024 := by
  caller_hb 100 150 100
    (ved_heavy_try (have _ := (by decide : (List.range 1000).foldl (· + ·) 0 = 499500)))
  exact hx

set_option ved.u1.heavyHeartbeatsForTest 1 in
/-- an unlimited caller (limit 0): the cap of the try applies (here the test hook: 1 thousand) -/
theorem heavyUnlimitedCaller (x : Nat) (hx : x < 1024) : x < 1024 := by
  caller_hb 0 0 100
    (ved_heavy_try (have _ := (by decide : (List.range 1000).foldl (· + ·) 0 = 499500)))
  exact hx

/-! entry level -/

/-- a wide unsigned module (the entry does not use the heavy try on it; the controls force `heavy := 1` / `2`):
closed by the flat tactics, and by the heavy tactics alone when the try is not capped -/
def umin12 {dom : DomainConfig} (a b : Signal dom (BitVec 12)) : Signal dom (BitVec 12) :=
  Signal.mux (Signal.ult a b) a b

def withLocal (cap : Nat) (act : TermElabM α) : TermElabM α :=
  withOptions (·.set `ved.u1.heavyHeartbeatsForTest cap) act

/-- the stored type is `U1Stmt c m (@decl defaultDomain)`, axioms within std3 (`checkRow` for a tag) -/
def checkStored (decl tag : Name) (stmt : Lean.Expr) (thm : Name) : CoreM Unit := do
  let nm := Names.ofBase tag
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: stored type differs"
  let ax ← collectAxioms thm
  unless ax.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do throwError "{thm}: axioms {ax}"

-- the heavy tactics alone under a cap of 1 thousand heartbeats: refused at `[proof]` (no fallback), clean
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlUmin12Alone) do
  let (stmt, _, names) ← stmtOf ``umin12
  discard <| withLocal 1 <| checkU1E ``umin12 `ctlUmin12Alone stmt (← modOfDecl ``umin12) (heavyProof ``umin12 1 (heavy := 2)) names

-- the same module and cap with the script of the entry (`heavy := 1`): the try fails, the flat tactics close it
/-- info: capped try, flat fallback accepts; stored type = U1Stmt c m F, axioms within std3 -/
#guard_msgs in
run_cmd do
  liftTermElabM do
    let (stmt, _, names) ← stmtOf ``umin12
    let thm ← withLocal 1 <| checkU1E ``umin12 `ctlUmin12Fall stmt (← modOfDecl ``umin12) (heavyProof ``umin12 1 (heavy := 1)) names
    checkStored ``umin12 `ctlUmin12Fall stmt thm
  logInfo "capped try, flat fallback accepts; stored type = U1Stmt c m F, axioms within std3"

/-- 3. a small caller limit with `ved.u1.proofHeartbeats 0` (pattern of `U1StageCheck`): `smax3` with the
script of the entry (`heavy := 1`, the try uncapped by the test hook) is refused at `[proof]`, clean, and the
command has used about the caller's limit (not more than 10% above it) -/
def withCallerLimit (n : Nat) (act : TermElabM α) : TermElabM α :=
  withOptions (fun o => (o.set `ved.u1.proofRecDepth (0 : Nat)).set `ved.u1.proofHeartbeats (0 : Nat)) <|
    Core.withCurrHeartbeats <|
      withTheReader Core.Context (fun c => { c with maxHeartbeats := n * 1000 }) act

/-- the command has used about the caller's limit (at most 110% of it) and is refused at `[proof]`, clean -/
def budgetRefused (n : Nat) : CommandElabM Unit := do
  let tag := Name.mkSimple s!"ctlBud{n}"
  let (stmt, _, names) ← liftTermElabM (stmtOf ``smax3)
  let hb0 ← IO.getNumHeartbeats
  expectRefused "proof" (checkerNames tag) do
    discard <| withCallerLimit n <| checkU1E ``smax3 tag stmt (← modOfDecl ``smax3) (heavyProof ``smax3 1 (heavy := 1)) names
  let used := ((← IO.getNumHeartbeats) - hb0) / 1000
  unless used ≤ n * 11 / 10 do throwError "limit {n}k: used {used}k"

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd budgetRefused 3000

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd budgetRefused 6000

end Tests.Ved.U1HeavyCheck

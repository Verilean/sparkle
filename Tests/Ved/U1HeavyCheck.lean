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
once per case of the selector.  `Tools/VedU1Heavy.lean` is the first attempt the entry now makes for a
combinational module with wide data inputs (`scriptFor … (heavy := true)`): both sides brought to one
form with `toSigned` kept whole (`ved_heavy_norm`), the wrap-around product and the shifted value named
by variables with their ranges (`ved_gen_atoms`, `ved_gen_shifts`), one case split per distinct
condition (`ved_heavy_close`).  When it fails the flat script runs as before.

What is fixed here, at the smallest sizes that exercise each shape and on the two real rows:
1. `#ved_u1` accepts `smax3` (three 6-bit inputs: a select tree, 18 bits), `smax4` (four 8-bit: the
   `maxPool2x2` shape), `qreq` (10 + 4 + 3 bits: product, shift, clamp), and the two real rows;
   the stored type of `<decl>.ved_u1` compared with `==` against `U1Stmt <decl>.ved_contract
   <decl>.ved_mod (@decl defaultDomain)`, axioms within std3;
2. the heavy script ALONE (no flat fallback) accepts `smax3` and `qreq`;
3. refusals (`expectRefused`, stage `[proof]`, no `ved_*` constant left) of the heavy script alone on the
   module with one change each: the signed compare read as unsigned (select tree and clamp), the operands of
   the compare exchanged (both), the arithmetic shift read as logical, a clamp bound changed (7 becomes 6), the
   sign-extension constant of the scale (63 becomes 31).
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

/-- the heavy script ALONE as the proof source: no first-attempt cap, no flat fallback (the flat script on a
false statement runs for minutes by design, so the refusals below test the heavy script itself) -/
def heavyProof (decl : Name) (nDom : Nat) : ProofSrc :=
  .built fun nm m => do
    let clkRst := clkRstOf m
    let inNames := (dataPortsOf m clkRst).map fun p => p.name
    let widths := m.inputs.filter (fun p => match clkRst with | some (k, r) => p.name != k && p.name != r | none => true) |>.map fun p => match p.ty with | .bitVector w => w | .bit => 1 | _ => 100
    scriptFor nm decl nDom (regShape m) inNames (bodyHasEq m.body) none (← helperConsts decl) widths none (heavy := true)

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

end Tests.Ved.U1HeavyCheck

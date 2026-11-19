import Tools.VedU2HierRegEntry
import Tools.VedU2HierBudget
import Tools.DeepFinArms
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import IP.Net.ICMP

/-!
# Checks for H2e, part 2: the unfolded nested loop, and the budget of the register-parent route

Issue sparkle-ved-hier2-h2e (`docs/VED-HIER-H2E.md`; part 1 is `U2HierOpenDeep2Check`).

* `reqW` is R228's shape at a small scale: the receive parser of the ICMP library (a nested stateful circuit of five
  registers) is applied outside the parent's `circuit do`; its `done` and `ident` are read by the next state of the parent's
  `okR`, and the child's argument is the complement of a sum of the parent's registers (`~~~(idReg + identIn)`).  The
  declaration's term holds the nested loop UNFOLDED inside the parent's loop (`Signal.loop fun live => packRegister …`), which
  is not the syntactic form of the exported state theorems; `ved_rw_loops` matches it by unfolding.
  POSITIVE: type `U2HRStmt c m d decl` compared with `==`, axioms within `propext`, `Classical.choice`, `Quot.sound` (strict
  audit), the state theorem of the loop and the nested state theorem exist.  REFUSALS (the real module with ONE piece altered
  against the declaration's own deep facts, `[proof]`, nothing left behind): the next-state nets of two nested registers
  exchanged.
* BUDGET.  `ved.u2.hierRecDepth`, `ved.u2.hierHeartbeats` (the register-parent check as a whole) and `ved.u2.nestedRecDepth`,
  `ved.u2.nestedHeartbeats` (the export of the nested loops' state theorems, `Tools/DeepElab.lean`) are lower bounds on the
  limits, `0` = no extra floor (the caller's limit applies as it is); the defaults are the former fixed constants (100000,
  8000000, 65536, 1600000).  (1) the helper `withNestedBudget` raises a lower caller limit to the floor, leaves a higher one
  alone, changes nothing for `0`; (2) the defaults accept `reqW` under a SMALL caller limit (they raise it); (3) with the floors
  at `0` the same small caller limit is respected: refused at `[proof]`, nothing left behind; likewise a small `maxRecDepth`;
  (4) the floors given explicitly accept it again.
-/

namespace Tests.Ved.U2HierOpenDeep3Check

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Net.ICMP
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
  Tools.VedU2HierEntry Tools.VedU2HierRegEntry

/-! ## Declarations -/

@[hardware_module] def hdr16 {dom : DomainConfig} (a : Signal dom (BitVec 16)) (b : Signal dom (BitVec 16)) :
    Signal dom (BitVec 16) := a + b

structure OR (dom : DomainConfig) where
  out : Signal dom (BitVec 16)
  ok : Signal dom Bool

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (OR dom) dom := ⟨⟩

/-- The receive parser of the ICMP library read by the parent's next state; the child's argument is the complement of a sum
of the parent's registers. -/
def reqG {dom : DomainConfig} (trigger : Signal dom Bool) (identIn : Signal dom (BitVec 16))
    (byte : Signal dom (BitVec 8)) (valid sop : Signal dom Bool) : OR dom :=
  let parsed := icmpRxParser byte valid sop
  circuit do
    let idReg ← Signal.reg (0#16)
    let okR ← Signal.reg false
    let idSig := (idReg : Signal dom (BitVec 16))
    let okSig := (okR : Signal dom Bool)
    idReg <~ Signal.mux trigger identIn idSig
    okR <~ Signal.mux trigger (Signal.pure false)
      (Signal.mux (parsed.done &&& (parsed.ident === idSig)) (Signal.pure true) okSig)
    return ({ out := hdr16 (~~~(idSig + identIn)) idSig, ok := okSig } : OR dom)

def reqW (trigger : Signal defaultDomain Bool) (identIn : Signal defaultDomain (BitVec 16))
    (byte : Signal defaultDomain (BitVec 8)) (valid sop : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 16) :=
  (reqG trigger identIn byte valid sop).out

/-- The declaration the CONTROLS alter (never accepted itself). -/
def reqRef (trigger : Signal defaultDomain Bool) (identIn : Signal defaultDomain (BitVec 16))
    (byte : Signal defaultDomain (BitVec 8)) (valid sop : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 16) :=
  (reqG trigger identIn byte valid sop).out

/-- The declaration the BUDGET runs check (its constants are not left by an accepted `reqW`). -/
def reqB (trigger : Signal defaultDomain Bool) (identIn : Signal defaultDomain (BitVec 16))
    (byte : Signal defaultDomain (BitVec 8)) (valid sop : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 16) :=
  (reqG trigger identIn byte valid sop).out

/-! ## Helpers -/

def std3 : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def std3Only (n : Name) : CoreM Unit := do
  let axs ← collectAxioms n
  unless axs.all (std3.contains ·) do throwError "{n}: axioms outside the standard three: {axs}"

def expectedOf (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``U2HRStmt)
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

def localConsts : CommandElabM NameSet := do
  return (← getEnv).constants.map₂.toList.foldl (fun s (n, _) => s.insert n) {}

def synthOf (decl : Name) : CommandElabM (Sparkle.IR.AST.Module × Design) := liftTermElabM do
  Sparkle.Compiler.Elab.synthesizeCombinational decl

/-! ## The unfolded nested loop: positive -/

/-- The entry run, the exact type (`==`), the strict audit, the standard axioms, the loop's state theorem (the port that reads
it: one of `ports`) and the nested one. -/
def checkOk (decl : Name) (ports : List String) : CommandElabM Unit := do
  let saved := (← get).messages
  let (m, d, thm, nDom, _) ← vedU2HierEntryR decl
  -- (the entry reports the ports of the deep run the proof does not use; they are not what is checked here)
  modify fun s => { s with messages := saved }
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U2HRStmt c m d decl"
    discard <| Tools.VedStrictAudit.strictAudit thm
    std3Only thm
    let openSuf := "ved_open_" ++ "_".intercalate (decl.components.map toString)
    let mut top : Option Name := none
    let mut nest : Option Name := none
    for suf in ("" :: ports.map ("_" ++ ·)) do
      let n := decl ++ Name.mkSimple (openSuf ++ suf ++ "_deep_state")
      if let some (.thmInfo _) := (← getEnv).find? n then
        std3Only n
        top := some n
      let nn := decl ++ Name.mkSimple (openSuf ++ suf ++ "_deep_state_n0")
      if let some (.thmInfo _) := (← getEnv).find? nn then
        std3Only nn
        nest := some nn
    unless top.isSome do throwError "{decl}: no port of {ports} exported the loop state"
    unless nest.isSome do throwError "{decl}: no nested state theorem"
    logInfo m!"u2 hier open-deep3 OK {thm}: {(regsOf m.body).length} registers, children {d.modules.map (·.name)}"

/-- info: u2 hier open-deep3 OK Tests.Ved.U2HierOpenDeep3Check.reqW.ved_u1: 7 registers, children [Tests.Ved.U2HierOpenDeep3Check.hdr16] -/
#guard_msgs in
run_cmd checkOk ``reqW ["out", "ok"]

/-! ## Refusals: the real module with ONE piece altered, the declaration's own deep facts -/

def setInit (o : String) (v : Int) (b : List Stmt) : List Stmt :=
  b.map fun s => match s with
    | .register o' c r e _ => if o' == o then .register o' c r e v else s
    | s => s

/-- Exchange the input nets of two registers. -/
def swapInputs (o1 o2 : String) (b : List Stmt) : List Stmt :=
  let inOf (o : String) : Option Sparkle.IR.AST.Expr := b.findSome? fun s => match s with
    | .register o' _ _ e _ => if o' == o then some e else none
    | _ => none
  match inOf o1, inOf o2 with
  | some e1, some e2 => b.map fun s => match s with
    | .register o' c r e i => if o' == o1 then .register o' c r e2 i
        else if o' == o2 then .register o' c r e1 i else .register o' c r e i
    | s => s
  | _, _ => b

def setAssign (n : String) (e : Sparkle.IR.AST.Expr) (b : List Stmt) : List Stmt :=
  b.map fun s => match s with
    | .assign l _ => if l == n then .assign l e else s
    | s => s

/-- The hierarchical checker on the altered module refuses at the named stage, leaving nothing. -/
def hierCtl (decl : Name) (stage : String) (f : List Stmt → List Stmt) : CommandElabM Unit := do
  let (m, d) ← synthOf decl
  let before ← localConsts
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  let m' := { m with body := f m.body }
  if decide (m' = m) then throwError "the mutation is the identity"
  let r ← try
      discard <| checkU2HR decl stmt nDom m' d none
      pure none
    catch e => pure (some (← liftTermElabM (e.toMessageData.toString)))
  match r with
  | none => throwError "{decl}: the checker ACCEPTED the altered module"
  | some msg =>
    unless msg.startsWith s!"VED U1 REFUSED {decl} [{stage}]" do throwError "expected a [{stage}] refusal, got: {msg.take 400}"
    logInfo m!"refused [{stage}], clean"
  let added := (← localConsts).toList.filter (!before.contains ·)
  unless added.isEmpty do throwError "constants left after the refusal: {added}"

/- `reqRef` (module): the parent's registers `_tmp_a_4` (`idReg`) and `_tmp_a_66` (`okR`); the nested parser's registers
`_tmp_a_13` (cnt), `_tmp_a_17` (type), `_tmp_a_32` (ident), `_tmp_a_45` (seq), `_tmp_a_47` (done); `_tmp_arg0_71 =
~~~_tmp_arg1_0` (`idReg + identIn`) is the child's first argument. -/

-- The next-state nets of the parser's identifier and sequence registers exchanged (same width).
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd hierCtl ``reqRef "proof" (swapInputs "_tmp_a_32" "_tmp_a_45")

-- (the wrong-constant and wrong-initial-value refusals of this shape cost about a minute each; `compRef` in
-- `U2HierOpenDeep2Check` covers those mutations in seconds)

/-! ## The budget -/

section Budget
open Tools.VedU2HierBudget

/-- The limits `withNestedBudget` hands on, for a caller context with the given limits and options `o`. -/
def nestedLimits (o : Options) (callerRec callerHb : Nat) : CoreM (Nat × Nat) :=
  withReader (fun (c : Core.Context) => { c with options := o, maxRecDepth := callerRec, maxHeartbeats := callerHb }) do
    withNestedBudget (do let c ← read; pure (c.maxRecDepth, c.maxHeartbeats))

def nestedOpts (r h : Nat) : Options :=
  (({} : Options).set `ved.u2.nestedRecDepth r).set `ved.u2.nestedHeartbeats h

-- the defaults (65536, 1600000 thousand) raise a small caller limit, and leave a larger one alone
/-- info: ok -/
#guard_msgs in
run_cmd do
  let a ← liftCoreM (nestedLimits {} 512 200000000)
  unless a == (65536, 1600000000) do throwError "defaults, small caller: {a}"
  let b ← liftCoreM (nestedLimits {} 1000000 9000000000)
  unless b == (1000000, 9000000000) do throwError "defaults, large caller: {b}"
  logInfo "ok"

-- `0` is no floor: the caller's limit applies as it is
/-- info: ok -/
#guard_msgs in
run_cmd do
  let a ← liftCoreM (nestedLimits (nestedOpts 0 0) 512 200000000)
  unless a == (512, 200000000) do throwError "zero floors, small caller: {a}"
  logInfo "ok"

-- an explicit floor is honoured: above the caller's limit it raises it, below it changes nothing
/-- info: ok -/
#guard_msgs in
run_cmd do
  let a ← liftCoreM (nestedLimits (nestedOpts 2000 5000000) 512 200000000)
  unless a == (2000, 5000000000) do throwError "explicit floors, small caller: {a}"
  let b ← liftCoreM (nestedLimits (nestedOpts 2000 5) 512 200000000)
  unless b == (2000, 200000000) do throwError "explicit low heartbeat floor: {b}"
  logInfo "ok"

def zeroFloors (o : Options) : Options :=
  (((o.set `ved.u2.hierRecDepth (0 : Nat)).set `ved.u2.hierHeartbeats (0 : Nat)).set `ved.u2.nestedRecDepth (0 : Nat)).set
    `ved.u2.nestedHeartbeats (0 : Nat)

def explicitFloors (o : Options) : Options :=
  (((o.set `ved.u2.hierRecDepth (100000 : Nat)).set `ved.u2.hierHeartbeats (8000000 : Nat)).set
    `ved.u2.nestedRecDepth (65536 : Nat)).set `ved.u2.nestedHeartbeats (1600000 : Nat)

/-- The checker (on the unaltered module) under the options `f o`, the environment restored afterwards: `none` when it
accepted, the refusal's text otherwise; the constants a refusal left behind are counted. -/
def runWith (decl : Name) (f : Options → Options) : CommandElabM (Option String × Nat) := do
  let (m, d) ← synthOf decl
  let before ← localConsts
  let saved ← get
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  let r ← try
      withScope (fun sc => { sc with opts := f sc.opts }) (discard <| checkU2HR decl stmt nDom m d none)
      pure none
    catch e => pure (some (← liftTermElabM (e.toMessageData.toString)))
  let added := (← localConsts).toList.filter (!before.contains ·)
  set saved
  return (r, added.length)

def expectAccepted (decl : Name) (f : Options → Options) : CommandElabM Unit := do
  let (r, _) ← runWith decl f
  match r with
  | none => logInfo "accepted"
  | some msg => throwError "expected acceptance, refused: {msg.take 300}"

def expectRefused (decl : Name) (stage : String) (f : Options → Options) : CommandElabM Unit := do
  let (r, left) ← runWith decl f
  match r with
  | none => throwError "{decl}: accepted under a low budget"
  | some msg =>
    unless msg.startsWith s!"VED U1 REFUSED {decl} [{stage}]" do throwError "expected a [{stage}] refusal, got: {msg.take 300}"
    unless left == 0 do throwError "{left} constants left after the refusal"
    logInfo s!"refused [{stage}], clean"

-- DEFAULTS under a small caller limit (100000 thousand heartbeats): the floors raise it, accepted
/-- info: accepted -/
#guard_msgs in
run_cmd expectAccepted ``reqB (fun o => o.set `maxHeartbeats (100000 : Nat))

-- the floors at 0: the small limit is the limit, refused at [proof], nothing left behind
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused ``reqB "proof" (fun o =>
  (((o.set `ved.u2.hierHeartbeats (0 : Nat)).set `ved.u2.nestedHeartbeats (0 : Nat)).set `maxHeartbeats (100000 : Nat)))

-- a small recursion limit with the floors at 0 is respected too
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused ``reqB "proof" (fun o =>
  (zeroFloors o).set `maxRecDepth (64 : Nat))

-- the floors given EXPLICITLY, above the small caller limit: accepted again
/-- info: accepted -/
#guard_msgs in
run_cmd expectAccepted ``reqB (fun o => (explicitFloors o).set `maxHeartbeats (100000 : Nat))

end Budget

end Tests.Ved.U2HierOpenDeep3Check

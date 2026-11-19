import Tools.VedU2HierRegEntry
import Tools.VedU2HierBudget
import Tools.DeepFinArms
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for H2e: derived child arguments over register state on real-IP-shaped circuits; the nested export's budget

Issue sparkle-ved-hier2-h2e.  Real IP rows R228 (`synth_icmpRequesterByte`) and R210 (`synth_arpResponderByte`) stopped in
the register-step proof of the open parent.  What stood between a parent whose child reads `~~~(sum of register state)`
and acceptance (`docs/VED-HIER-H2E.md`):

* `omega` does not read `x ^^^ 65535`: the complement of a bounded value is rewritten (`Tools/VedU2HierXor.lean`, one lemma
  per width) inside `ved_hier_close`;
* the concatenations of the one's-complement adder (`0#1 ++ x : BitVec 17`) were left as `(0#1 ++ x).toNat`: the core lemma
  has the width `m + n` on its left side and simp's unifier cannot solve `?m + ?n =?= 17`
  (`Tools/VedU2HierBvAppend.lean`: `ved_toNat_append`, `ved_sigval_append`);
* the state theorem reads the registers through `rd<i> <arguments> t`, whose arguments contain the same loop again, so the
  rewritten goal grew with every use and no fact matched it: the loops of the goal are rewritten to
  `BitVec.ofNat w (irS …)` by definitional matching (`ved_rw_loops`, `Tools/VedU2HierLoopRw.lean`);
* the goal was then closed by `omega` with thirty net equations in the context: every `if` of every fact was split
  (10 GB); `ved_port_ctx` clears what the goal does not speak of.

The shapes below are those minimal reproductions: `compW` (8-bit complement of a sum of two registers), `onesW` (the
checksum of R228: two chained 16-bit one's-complement adds, `~~~`, concatenations, a derived argument over three
registers).  The unfolded nested loop and the budget are in `U2HierOpenDeep3Check`.

* POSITIVES: type `U2HRStmt c m d decl` compared with `==`, axioms within `propext`, `Classical.choice`, `Quot.sound`
  (strict audit), the state theorem of the port that reads the loop exists (`nestW`: also the nested one).
* REFUSALS (the real module with ONE piece altered against the declaration's own deep facts, `[proof]`, nothing left behind):
  a wrong constant, the next-state nets of two registers exchanged, a wrong initial value, for `compW`; the exchange for `onesW`.
* BUDGET (`ved.u2.hierRecDepth`, `ved.u2.hierHeartbeats`, `ved.u2.nestedRecDepth`, `ved.u2.nestedHeartbeats`: floors, `0` =
  the caller's limit as it is; defaults 100000 / 8000000 / 65536 / 1600000, the former constants): the helper that sets
  the nested export's limits raises a lower caller limit to the floor, leaves a higher one alone, and with `0` changes
  nothing; a run with the floors at `0` under a small caller `maxHeartbeats` is refused and leaves nothing, the same run
  with the floors given explicitly is accepted.
-/

namespace Tests.Ved.U2HierOpenDeep2Check

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
  Tools.VedU2HierEntry Tools.VedU2HierRegEntry

/-! ## Declarations -/

@[hardware_module] def addc {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := a + b

structure O2 (dom : DomainConfig) where
  out : Signal dom (BitVec 8)
  seen : Signal dom Bool

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (O2 dom) dom := ⟨⟩

/-- Two 8-bit registers; the child's first argument is the complement of a computed value (`~~~(a + b)`). -/
def compG {dom : DomainConfig} (trig : Signal dom Bool) (x : Signal dom (BitVec 8)) : O2 dom :=
  circuit do
    let a ← Signal.reg (0#8)
    let b ← Signal.reg (0#8)
    let aS := (a : Signal dom (BitVec 8))
    let bS := (b : Signal dom (BitVec 8))
    a <~ Signal.mux trig x aS
    b <~ bS + aS
    return ({ out := addc (~~~(aS + bS)) (Signal.mux trig x bS)
            , seen := (aS === bS) } : O2 dom)

def compW (trig : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  (compG trig x).out

/-- The declaration the CONTROLS alter (never accepted itself). -/
def compRef (trig : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  (compG trig x).out

@[hardware_module] def hdrL {dom : DomainConfig}
    (chk : Signal dom (BitVec 16)) (cnt : Signal dom (BitVec 4)) : Signal dom (BitVec 8) :=
  let b2 : Signal dom (BitVec 8) := chk.map (BitVec.extractLsb' 8 8 ·)
  let b3 : Signal dom (BitVec 8) := chk.map (BitVec.extractLsb' 0 8 ·)
  Signal.mux (cnt === (Signal.pure 3#4 : Signal dom (BitVec 4))) b2 b3

/-- One's-complement add of two 16-bit words (the carry folded back), as the checksums of the IP library build it. -/
@[inline] def onesAddL {dom : DomainConfig} (a b : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let a17 : Signal dom (BitVec 17) := (Signal.pure (0#1 : BitVec 1) : Signal dom (BitVec 1)) ++ a
  let b17 : Signal dom (BitVec 17) := (Signal.pure (0#1 : BitVec 1) : Signal dom (BitVec 1)) ++ b
  let s17 : Signal dom (BitVec 17) := a17 + b17
  let low : Signal dom (BitVec 16) := s17.map (BitVec.extractLsb' 0 16 ·)
  let carBit : Signal dom (BitVec 1) := s17.map (BitVec.extractLsb' 16 1 ·)
  let car16 : Signal dom (BitVec 16) := (Signal.pure (0#15 : BitVec 15) : Signal dom (BitVec 15)) ++ carBit
  low + car16

structure OL (dom : DomainConfig) where
  txByte : Signal dom (BitVec 8)
  txValid : Signal dom Bool

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (OL dom) dom := ⟨⟩

/-- The checksum of the ICMP requester: the child reads `~~~(onesAdd (onesAdd w0 ident) seq)` over the latched registers. -/
def onesG {dom : DomainConfig} (trigger : Signal dom Bool) (identIn seqIn : Signal dom (BitVec 16)) : OL dom :=
  circuit do
    let txCnt ← Signal.reg (0#4)
    let idReg ← Signal.reg (0#16)
    let seqReg ← Signal.reg (0#16)
    let txCntSig := (txCnt : Signal dom (BitVec 4))
    let idSig := (idReg : Signal dom (BitVec 16))
    let seqSig := (seqReg : Signal dom (BitVec 16))
    let idNow := Signal.mux trigger identIn idSig
    let seqNow := Signal.mux trigger seqIn seqSig
    let typ := (Signal.pure 8#8 : Signal dom (BitVec 8))
    let w0 := (typ ++ (Signal.pure (0#8 : BitVec 8) : Signal dom (BitVec 8)) : Signal dom (BitVec 16))
    let chk := (onesAddL (onesAddL w0 idNow) seqNow).map (BitVec.not ·)
    txCnt <~ Signal.mux trigger (Signal.pure 1#4) (txCntSig + (Signal.pure 1#4 : Signal dom (BitVec 4)))
    idReg <~ idNow
    seqReg <~ seqNow
    return ({ txByte := hdrL chk txCntSig
            , txValid := ~~~(txCntSig === (Signal.pure 0#4 : Signal dom (BitVec 4))) } : OL dom)

def onesW (trigger : Signal defaultDomain Bool) (identIn seqIn : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain (BitVec 8) := (onesG trigger identIn seqIn).txByte

/-- The declaration the CONTROLS alter (never accepted itself). -/
def onesRef (trigger : Signal defaultDomain Bool) (identIn seqIn : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain (BitVec 8) := (onesG trigger identIn seqIn).txByte

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

/-! ## Positives -/

/-- The entry run, the exact type (`==`), the strict audit, the standard axioms, the state theorem of one of `ports` (and
the nested one when `nested`). -/
def checkOk (decl : Name) (ports : List String) (nested : Bool) : CommandElabM Unit := do
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
    let mut found : Option Name := none
    for suf in ("" :: ports.map ("_" ++ ·)) do
      let n := decl ++ Name.mkSimple (openSuf ++ suf ++ "_deep_state")
      if let some (.thmInfo _) := (← getEnv).find? n then
        std3Only n
        found := some n
    unless found.isSome do throwError "{decl}: no port of {ports} exported the loop state"
    if nested then
      let n := decl ++ Name.mkSimple (openSuf ++ "_deep_state_n0")
      let some (.thmInfo _) := (← getEnv).find? n | throwError "{n} is not a theorem"
      std3Only n
    logInfo m!"u2 hier open-deep2 OK {thm}: {(regsOf m.body).length} parent registers, children {d.modules.map (·.name)}"

/-- info: u2 hier open-deep2 OK Tests.Ved.U2HierOpenDeep2Check.compW.ved_u1: 2 parent registers, children [Tests.Ved.U2HierOpenDeep2Check.addc] -/
#guard_msgs in
run_cmd checkOk ``compW ["out", "seen"] false

/-- info: u2 hier open-deep2 OK Tests.Ved.U2HierOpenDeep2Check.onesW.ved_u1: 3 parent registers, children [Tests.Ved.U2HierOpenDeep2Check.hdrL] -/
#guard_msgs in
run_cmd checkOk ``onesW ["txByte", "txValid"] false

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

/- `compRef` (module): registers `_tmp_a_4` (a), `_tmp_a_8` (b); `_tmp_arg1_0 = a + b`, `_tmp_arg0_15 = ~~~_tmp_arg1_0` is the
child's first argument. -/

-- A WRONG CONSTANT: the complement taken with the mask 254 instead of 255.
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd hierCtl ``compRef "proof" (setAssign "_tmp_arg0_15" (.op .xor [.ref "_tmp_arg1_0", .const 254 8]))

-- The next-state nets of the two registers exchanged.
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd hierCtl ``compRef "proof" (swapInputs "_tmp_a_4" "_tmp_a_8")

-- A wrong initial value.
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd hierCtl ``compRef "proof" (setInit "_tmp_a_8" 1)

/- `onesRef` (module): registers `_tmp_a_9` (txCnt), `_tmp_a_13` (ident), `_tmp_a_17` (seq); the message type byte is
`_tmp_concat_hi_2`; `_tmp_arg0_31 = ~~~_tmp_s_30` is the child's checksum argument. -/

-- The next-state nets of the identifier and the sequence registers exchanged (same width).
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd hierCtl ``onesRef "proof" (swapInputs "_tmp_a_13" "_tmp_a_17")

-- Not here (measured): a wrong constant or initial value on `onesRef` makes the refused proof search run
-- for minutes (a wrong constant: over 12 GB, killed after 579 s); the same two mutations on `compRef` above refuse in seconds.

end Tests.Ved.U2HierOpenDeep2Check

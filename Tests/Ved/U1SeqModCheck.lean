import Tests.Ved.U1MultiLoopRow
import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# `#ved_u1` on a packed loop word read through chained truncations (sparkle-ved-crypto-simp)

`Tools/VedU1ScriptSeqGen.lean` (`seqLoopScript`) normalises every assignment of a `Signal.loop` module on its own.  On a
module with many wide registers the packed loop word is read back field by field, each statement slicing the previous
one (`s_k = s_{k-1} % 2^w`); before `Nat.mod_mod_of_dvd` was applied to the normalised statement, `omega` in
`ved_seq_unpack` met up to ten nested `% 2^k` layers over a 2822-bit word, doubled in cost every few statements and the
first attempt hit its heartbeat cap (the flat fallback then ran out of simp steps: the real row R171, `synth_ecdsaR`,
was refused at `[proof]`).

The body here has that shape: a copy of the ECDSA sign orchestrator FSM (`IP.Crypto.P256ECDSAHW.signHW`: a 5-bit step
register, eleven 256-bit registers, one 1-bit register, 257-bit conditional subtracts), written out so the Check needs
no proof library.

What is fixed here:
1. the declaration `ecdsaR` is accepted by `#ved_u1`, the stored type of `ecdsaR.ved_u1` is `==`
   `U1Stmt ecdsaR.ved_contract ecdsaR.ved_mod ecdsaR`, the axioms are within std3;
2. the proof comes from the per-statement first attempt (it uses `step_seq`): at 95c26529 (without the collapse) the
   first attempt hit its cap, the flat script followed and the declaration was refused, so this is the line that
   distinguishes the two heads;
3. refusal control (one kind: the output altered by a constant) stays refused at `[proof]`, nothing left behind; it runs
   on a small three-register body of the same kind (accepted unaltered), because the refusal of the heavy body would cost
   the whole first attempt plus the flat script.
-/

namespace Tests.Ved.U1SeqModCheck

open Sparkle.Core.Domain Sparkle.Core.Signal
def pNat : Nat := 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
def nNat : Nat := 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

def pBv257 : BitVec 257 := BitVec.ofNat 257 pNat

def nBv257 : BitVec 257 := BitVec.ofNat 257 nNat

def condSubN {dom : DomainConfig}
    (a : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  let aw := (a.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let nP := (Signal.pure nBv257 : Signal dom (BitVec 257))
  let ge := ((BitVec.ule · ·) <$> nP <*> aw : Signal dom Bool)
  let red := (Signal.mux ge (aw - nP) aw : Signal dom (BitVec 257))
  ((BitVec.extractLsb' 0 256 ·) <$> red : Signal dom (BitVec 256))

def addModN {dom : DomainConfig}
    (a b : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  let aw := (a.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let bw := (b.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let s  := (aw + bw : Signal dom (BitVec 257))
  let nP := (Signal.pure nBv257 : Signal dom (BitVec 257))
  let ge := ((BitVec.ule · ·) <$> nP <*> s : Signal dom Bool)
  let red := (Signal.mux ge (s - nP) s : Signal dom (BitVec 257))
  ((BitVec.extractLsb' 0 256 ·) <$> red : Signal dom (BitVec 256))

structure SignOut (dom : DomainConfig) where
    rOut : Signal dom (BitVec 256)
    sOut : Signal dom (BitVec 256)
    done : Signal dom Bool
    smStart : Signal dom Bool
    smK : Signal dom (BitVec 256)
    pInvStart : Signal dom Bool
    pMulStart : Signal dom Bool
    pA : Signal dom (BitVec 256)
    pB : Signal dom (BitVec 256)
    pExp : Signal dom (BitVec 256)
    nInvStart : Signal dom Bool
    nMulStart : Signal dom Bool
    nA : Signal dom (BitVec 256)
    nB : Signal dom (BitVec 256)
    nExp : Signal dom (BitVec 256)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (SignOut dom) dom := ⟨⟩

@[inline] def stepEq {dom : DomainConfig}
    (stSig : Signal dom (BitVec 5)) (kk : Nat) : Signal dom Bool :=
  (stSig === (Signal.pure (BitVec.ofNat 5 kk) : Signal dom (BitVec 5)))

@[inline] def or2 {dom : DomainConfig}
    (a b : Signal dom Bool) : Signal dom Bool :=
  (a ||| b)

def signHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (d k z : Signal dom (BitVec 256))
    (smX smY smZ : Signal dom (BitVec 256))
    (smDone : Signal dom Bool)
    (pRes : Signal dom (BitVec 256))
    (pDone : Signal dom Bool)
    (nRes : Signal dom (BitVec 256))
    (nDone : Signal dom Bool) :
    SignOut dom :=
  circuit do
    let stR ← Signal.reg (0#5)
    let dR ← Signal.reg (0#256)
    let kR ← Signal.reg (0#256)
    let zR ← Signal.reg (0#256)
    let xR ← Signal.reg (0#256)     -- k·G Jacobian X
    let zjR ← Signal.reg (0#256)    -- k·G Jacobian Z
    let zinvR ← Signal.reg (0#256)  -- Z^(p-2) mod p
    let zinv2R ← Signal.reg (0#256) -- Zinv² mod p
    let rR ← Signal.reg (0#256)     -- signature r
    let kinvR ← Signal.reg (0#256)  -- k^(n-2) mod n
    let rdR ← Signal.reg (0#256)    -- r·d mod n
    let sR ← Signal.reg (0#256)     -- signature s
    let doneR ← Signal.reg false

    let stSig := (stR : Signal dom (BitVec 5))
    let dSig := (dR : Signal dom (BitVec 256))
    let kSig := (kR : Signal dom (BitVec 256))
    let zSig := (zR : Signal dom (BitVec 256))
    let xSig := (xR : Signal dom (BitVec 256))
    let zjSig := (zjR : Signal dom (BitVec 256))
    let zinvSig := (zinvR : Signal dom (BitVec 256))
    let zinv2Sig := (zinv2R : Signal dom (BitVec 256))
    let rSig := (rR : Signal dom (BitVec 256))
    let kinvSig := (kinvR : Signal dom (BitVec 256))
    let rdSig := (rdR : Signal dom (BitVec 256))
    let sSig := (sR : Signal dom (BitVec 256))

    let isSmIssue  := stepEq stSig 1
    let isSmWait   := stepEq stSig 2
    let isZiIssue  := stepEq stSig 3
    let isZiWait   := stepEq stSig 4
    let isZi2Issue := stepEq stSig 5
    let isZi2Wait  := stepEq stSig 6
    let isX1Issue  := stepEq stSig 7
    let isX1Wait   := stepEq stSig 8
    let isKiIssue  := stepEq stSig 9
    let isKiWait   := stepEq stSig 10
    let isRdIssue  := stepEq stSig 11
    let isRdWait   := stepEq stSig 12
    let isSIssue   := stepEq stSig 13
    let isSWait    := stepEq stSig 14

    let smAck := (isSmWait &&& smDone : Signal dom Bool)
    let ziAck := (isZiWait &&& pDone : Signal dom Bool)
    let zi2Ack := (isZi2Wait &&& pDone : Signal dom Bool)
    let x1Ack := (isX1Wait &&& pDone : Signal dom Bool)
    let kiAck := (isKiWait &&& nDone : Signal dom Bool)
    let rdAck := (isRdWait &&& nDone : Signal dom Bool)
    let sAck := (isSWait &&& nDone : Signal dom Bool)

    let zrdComb := addModN zSig rdSig

    let pInvStart := isZiIssue
    let pMulStart := (isZi2Issue ||| isX1Issue : Signal dom Bool)
    let pA := (Signal.mux isZiIssue zjSig
                (Signal.mux isZi2Issue zinvSig xSig) : Signal dom (BitVec 256))
    let pB := (Signal.mux isZi2Issue zinvSig zinv2Sig : Signal dom (BitVec 256))
    let pExp := (Signal.pure (BitVec.ofNat 256 (pNat - 2)) : Signal dom (BitVec 256))

    let nInvStart := isKiIssue
    let nMulStart := (isRdIssue ||| isSIssue : Signal dom Bool)
    let nA := (Signal.mux isKiIssue kSig
                (Signal.mux isRdIssue rSig kinvSig) : Signal dom (BitVec 256))
    let nB := (Signal.mux isRdIssue dSig zrdComb : Signal dom (BitVec 256))
    let nExp := (Signal.pure (BitVec.ofNat 256 (nNat - 2)) : Signal dom (BitVec 256))

    dR <~ Signal.mux start d dSig
    kR <~ Signal.mux start k kSig
    zR <~ Signal.mux start z zSig

    xR <~ Signal.mux start (Signal.pure 0#256 : Signal dom (BitVec 256))
            (Signal.mux smAck smX
              (Signal.mux x1Ack pRes xSig))   -- x1 overwrites X at the X·Zinv² ack
    zjR <~ Signal.mux smAck smZ zjSig

    zinvR <~ Signal.mux ziAck pRes zinvSig
    zinv2R <~ Signal.mux zi2Ack pRes zinv2Sig
    let x1AtAck := condSubN pRes
    rR <~ Signal.mux x1Ack x1AtAck rSig
    kinvR <~ Signal.mux kiAck nRes kinvSig
    rdR <~ Signal.mux rdAck nRes rdSig
    sR <~ Signal.mux sAck nRes sSig

    let advanceIssue :=  -- issue phases always advance to their wait next cycle
      or2 isSmIssue (or2 isZiIssue (or2 isZi2Issue (or2 isX1Issue
        (or2 isKiIssue (or2 isRdIssue isSIssue)))))
    let anyAck :=
      or2 smAck (or2 ziAck (or2 zi2Ack (or2 x1Ack
        (or2 kiAck (or2 rdAck sAck)))))
    let stInc := (stSig + (Signal.pure 1#5 : Signal dom (BitVec 5)) : Signal dom (BitVec 5))
    let advance := (advanceIssue ||| anyAck : Signal dom Bool)
    stR <~ Signal.mux start (Signal.pure 1#5 : Signal dom (BitVec 5))
             (Signal.mux advance stInc stSig)

    doneR <~ sAck

    return ({ rOut := rSig
            , sOut := sSig
            , done := (doneR : Signal dom Bool)
            , smStart := isSmIssue
            , smK := kSig
            , pInvStart := pInvStart
            , pMulStart := pMulStart
            , pA := pA
            , pB := pB
            , pExp := pExp
            , nInvStart := nInvStart
            , nMulStart := nMulStart
            , nA := nA
            , nB := nB
            , nExp := nExp
            } : SignOut dom)


open Lean Elab Command Term Meta
open Tools.VedU1Contract Tools.VedU1Entry
open Tests.Ved.U1MultiLoopRow

/-- the sign orchestrator at the default domain, one 256-bit output -/
def ecdsaR
    (start : Signal defaultDomain Bool)
    (d k z : Signal defaultDomain (BitVec 256))
    (smX smY smZ : Signal defaultDomain (BitVec 256))
    (smDone : Signal defaultDomain Bool)
    (pRes : Signal defaultDomain (BitVec 256))
    (pDone : Signal defaultDomain Bool)
    (nRes : Signal defaultDomain (BitVec 256))
    (nDone : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 256) :=
  (signHW start d k z smX smY smZ smDone pRes pDone nRes nDone).rOut

#guard_msgs (drop info) in
#synthesizeVerilog ecdsaR

/-! ## 1. Positive -/

set_option Elab.async false in
#ved_u1_pub Tests.Ved.U1SeqModCheck.ecdsaR

/-! ## 2. Stored type, axioms, route -/

/-- info: OK 1 rows: stored type = U1Stmt c m F, axioms within std3 -/
#guard_msgs in
run_cmd checkRows [(.anonymous, ``ecdsaR)]

/-- does the proof term (through its theorem dependencies) use `step_seq`, the lemma of the per-statement script? -/
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

/-- info: the proof comes from the per-statement first attempt -/
#guard_msgs in
run_cmd liftCoreM do
  unless (← usesStepSeq (``ecdsaR ++ `ved_u1)) do throwError "the flat script proved it (first attempt did not succeed)"
  logInfo "the proof comes from the per-statement first attempt"

/-! ## 3. Refusal control -/

def modOf (base : Name) : TermElabM Sparkle.IR.AST.Module := do
  let some v := (← getConstInfo (base ++ `ved_mod)).value? | throwError "no value"
  evalModule v

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

/-- the output port gets `+ 1` -/
def mutOut (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .assign "out" e => .assign "out" (.op .add [e, .const 1 256])
      | s => s }

/-- The control runs on a small body of the same kind (three registers, a 9-bit sum cut back to 8 bits), so the refusal is
cheap: the heavy body above would need the whole first attempt and the flat script to fail before the refusal. -/
def small (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    let b ← Signal.reg 0#8
    let c ← Signal.reg 0#8
    let aS := (a : Signal defaultDomain (BitVec 8))
    let bS := (b : Signal defaultDomain (BitVec 8))
    let cS := (c : Signal defaultDomain (BitVec 8))
    a <~ aS + x
    b <~ bS + aS
    let w := (aS.map (fun v => BitVec.append (0#1) v) : Signal defaultDomain (BitVec 9))
    let w2 := (bS.map (fun v => BitVec.append (0#1) v) : Signal defaultDomain (BitVec 9))
    let sum := (w + w2 : Signal defaultDomain (BitVec 9))
    c <~ ((BitVec.extractLsb' 0 8 ·) <$> sum : Signal defaultDomain (BitVec 8))
    return aS + bS + cS

#guard_msgs (drop info) in
#synthesizeVerilog small

/-- info: small body accepted, stored type `==` U1Stmt, std3 -/
#guard_msgs in
run_cmd liftTermElabM do
  let (m, _) ← Sparkle.Compiler.Elab.synthesizeCombinational ``small
  let thm ← checkU1 ``small `smallOk ``small m .generated
  let nm := Names.ofBase `smallOk
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst ``small]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "stored type differs"
  let ax ← collectAxioms thm
  unless ax.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do throwError "axioms {ax}"
  logInfo "small body accepted, stored type `==` U1Stmt, std3"

/-- info: mutation differs from the original -/
#guard_msgs in
run_cmd liftTermElabM do
  let (m, _) ← Sparkle.Compiler.Elab.synthesizeCombinational ``small
  if decide (mutOut m = m) then throwError "the mutation is the identity"
  logInfo "mutation differs from the original"

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlOut) do
  let (m, _) ← Sparkle.Compiler.Elab.synthesizeCombinational ``small
  discard <| checkU1 ``small `ctlOut ``small (mutOut m) .generated

end Tests.Ved.U1SeqModCheck

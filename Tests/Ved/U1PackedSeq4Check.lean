import Tools.VedU1PackedEntry

/-!
# Checks for the packed-seq4 script of a packed result with registers (`sparkle-ved-packed-seq4`)

`#ved_u1_packed` on a `Signal.loop` body runs `Tools.VedU1PackedSeq4.packedSeqScript4` (the per-statement script of
`Tools/VedU1PackedSeq2.lean` with three changes of the proof, none of the statement):

* the register fields are read back out of the packed loop word by three closed lemmas (`pk4_div`, `pk4_mod`, `pk4_lt`;
  `ved_pk4_unpack`) instead of `omega` over the whole word;
* the kernel evaluation of `OrderOk` (and of `woCheck`, the `Nodup` of the wire names) tests a natural-number key of the
  two names before it compares the strings (`Tools/VedU1PackedSeq4Fast.lean`: `OrderOk_eq_K`, `woCheckK_eq`, `nodupK_iff`);
* the `declWidth` facts and the membership facts of the environment are proved in one kernel evaluation each.

* Lemma level: `ved_pk4_unpack` turns a hypothesis over a wrapped packed word into the bare field (two fields of a
  three-field word); a wrong-modulus word is left as it is.  `OrderOkK = OrderOk`, `woCheckK = woCheck`, `nodupK` on the
  modules of the positives (accepted bodies) and on a REVERSED body (both false).
* Positives (stored type `==` the expected `PackedStmt`, the standard axioms, the hand-written contract, the proof uses
  `step_seq`, `OrderOk_eq_K`, and for the multi-field words `pk4_div`): a two-register counter, an eight-register word of
  mixed widths (`BitVec 32`, `3`, `Bool`, `20`, `2`, `22`, `Bool`, `8`).
* default options (`ved.packedseq4.on` false; the packed-seq4 script runs only above the packed-seq3 size gate and only with the
  option on, the positives set `ved.packedseq3.maxExp 0`): a body below the gate goes through the packed-seq2 script (no
  `OrderOk_eq_K` in the proof).
* Control: a module with the output altered by a constant is refused at `[proof]` and nothing is left behind.
-/

namespace Tests.Ved.U1PackedSeq4Check

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.AST Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Packed Tools.VedU1PackedEntry Tools.VedU1PackedSeq4

/-! ## `ved_pk4_unpack` -/

example (E : String → Nat) (X : BitVec 3 × Bool × BitVec 8)
    (h : E "g" = ((((X.1.toNat % 8 * 512 + (X.2.1.toNat % 2 * 256 + X.2.2.toNat % 256) % 512) % 4096 % 2 ^ (11 + 1))
      / 512) % 2 ^ (2 + 1))) : E "g" = X.1.toNat := by
  ved_pk4_unpack at h
  exact h

example (E : String → Nat) (X : BitVec 3 × Bool × BitVec 8)
    (h : E "g" = ((((X.1.toNat % 8 * 512 + (X.2.1.toNat % 2 * 256 + X.2.2.toNat % 256) % 512) % 4096 % 2 ^ (11 + 1))
      % 512) / 256 % 2)) : E "g" = X.2.1.toNat := by
  ved_pk4_unpack at h
  exact h

example (E : String → Nat) (X : BitVec 3 × Bool × BitVec 8)
    (h : E "g" = ((((X.1.toNat % 8 * 512 + (X.2.1.toNat % 2 * 256 + X.2.2.toNat % 256) % 512) % 4096 % 2 ^ (11 + 1))
      % 512) % 256)) : E "g" = X.2.2.toNat := by
  ved_pk4_unpack at h
  exact h

-- a term of another shape is not changed: no field of a word, a quotient by a literal that is not a field boundary
example (E : String → Nat) (X : BitVec 3 × Bool × BitVec 8)
    (h : E "g" = X.2.2.toNat / 100 % 2) : E "g" = X.2.2.toNat / 100 % 2 := by
  ved_pk4_unpack at h
  exact h

/-! ## Declarations -/

def qCnt (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    let cNext := Signal.mux en (c + d) c
    let fNext := Signal.mux (c === 255#8) (Signal.pure true) f
    bundleAll! [Signal.register 0#8 cNext, Signal.register false fNext]
  bundle2 (projN! st 2 0) (projN! st 2 1)

def qCntOff (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) := qCnt en d

set_option maxRecDepth 4096 in
/-- eight registers of mixed widths in one loop word -/
def q8 (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 32)) (k : Signal defaultDomain (BitVec 3)) :
    Signal defaultDomain (BitVec 32 × BitVec 3 × Bool × BitVec 20 × BitVec 2 × BitVec 22 × Bool × BitVec 8) :=
  let st := Signal.loop fun state =>
    let a := projN! state 8 0
    let b := projN! state 8 1
    let c := projN! state 8 2
    let e := projN! state 8 3
    let f := projN! state 8 4
    let g := projN! state 8 5
    let h := projN! state 8 6
    let i := projN! state 8 7
    bundleAll! [Signal.register 0#32 (Signal.mux en (a + d) a),
      Signal.register 0#3 (Signal.mux (c &&& en) k b),
      Signal.register false (Signal.mux (b === 3#3) (Signal.pure true) c),
      Signal.register 0#20 (Signal.mux en (e + 1#20) e),
      Signal.register 0#2 (Signal.mux h (f + 1#2) f),
      Signal.register 0#22 (Signal.mux c (g + 3#22) g),
      Signal.register false (Signal.mux (f === 3#2) (Signal.pure false) h),
      Signal.register 0#8 (Signal.mux en (i + 1#8) i)]
  bundleAll! [projN! st 8 0, projN! st 8 1, projN! st 8 2, projN! st 8 3, projN! st 8 4, projN! st 8 5,
    projN! st 8 6, projN! st 8 7]

/-- control module: the output altered by a constant -/
def qCntConst (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    let cNext := Signal.mux en (c + d) c
    let fNext := Signal.mux (c === 255#8) (Signal.pure true) f
    bundleAll! [Signal.register 0#8 cNext, Signal.register false fNext]
  bundle2 (projN! st 2 0 + 1#8) (projN! st 2 1)

def qCntCtl (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) := qCnt en d

/-! ## The checker -/

def modOf (decl : Name) : TermElabM Sparkle.IR.AST.Module := do
  return (← Sparkle.Compiler.Elab.synthesizeCombinational decl).1

/-- the proof term, looked through the auxiliary theorems, mentions the constant `c` -/
def usesConst (thm c : Name) : CoreM Bool := do
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
      if n == c then return true
      if let some (.thmInfo ti) := env.find? n then
        todo := ti.value.getUsedConstants.toList ++ todo
  return false

/-- accept `decl` through the entry: type `==` the expected `PackedStmt`, standard axioms, `step_seq` in the proof,
`OrderOk_eq_K` in the proof iff `seq4`, `pk4_div` in the proof iff `unpack` -/
def check4 (decl : Name) (stmtStx : Term) (seq4 unpack : Bool) : CommandElabM Unit := liftTermElabM do
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
  unless ← usesConst thm ``Tools.VedU1ScriptSeq.step_seq do throwError "{thm}: no step_seq (not the per-statement script)"
  unless (← usesConst thm ``OrderOk_eq_K) == seq4 do throwError "{thm}: OrderOk_eq_K in the proof is {!seq4}"
  unless (← usesConst thm ``pk4_div) == unpack do throwError "{thm}: pk4_div in the proof is {!unpack}"
  -- the key-tested checks agree with the definitions on the accepted body, and on a reversed one
  let b0 := orderBody m.body
  unless decide (OrderOkK m b0 = OrderOk m b0) && OrderOk m b0 do throwError "{decl}: OrderOkK differs on the body"
  unless decide (OrderOkK m b0.reverse = OrderOk m b0.reverse) do throwError "{decl}: OrderOkK differs on the reversed body"
  unless decide (woCheckK [] b0 = true) && decide (woCheckK [] b0.reverse = woCheck [] b0.reverse) do
    throwError "{decl}: woCheckK differs"
  unless decide (nodupK (m.wires.map (·.name)) = true) do throwError "{decl}: nodupK"
  logInfo m!"packed seq4 OK {thm} seq4={seq4} unpack={unpack}"

/-! ## Positives -/

/-- info: packed seq4 OK Tests.Ved.U1PackedSeq4Check.qCnt.ved_u1 seq4=true unpack=true -/
#guard_msgs in
set_option ved.packedseq3.maxExp 0 in
set_option ved.packedseq4.on true in
run_cmd check4 ``qCnt (← `(qCnt)) true true

/-- info: packed seq4 OK Tests.Ved.U1PackedSeq4Check.q8.ved_u1 seq4=true unpack=true -/
#guard_msgs in
set_option maxHeartbeats 1600000 in
set_option ved.packedseq3.maxExp 0 in
set_option ved.packedseq4.on true in
run_cmd check4 ``q8 (← `(q8)) true true

/-! ## The packed-seq2 script (option off): same statement, no packed-seq4 lemma in the proof -/

/-- info: packed seq4 OK Tests.Ved.U1PackedSeq4Check.qCntOff.ved_u1 seq4=false unpack=false -/
#guard_msgs in
run_cmd check4 ``qCntOff (← `(qCntOff)) false false

/-! ## Control -/

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
run_cmd expectRefused "proof" ``qCntCtl do onMap ``qCntCtl [(1, 8), (0, 1)] (← modOf ``qCntConst)

end Tests.Ved.U1PackedSeq4Check

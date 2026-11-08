import Tools.VedU1Deep
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# U1 entry with the DeepElab generator: accepted examples and controls

Issue sparkle-ved-gen1.  Design: docs/VERIFY-ELAB-DEEP-U0U1-DESIGN-2026-11-08.md
§11.  First example `accK9`, second `natInit5`: the shapes of
`Tests/Verification/ValueParamInitRepro.lean`, re-declared here (that file is
not a library target; one register whose current value is the output).

What is fixed here (`#guard_msgs`):
1. `#verify_elab_deep` then the entry, for both examples: `VED U1 OK`, with the
   strict audit (standard three axioms only).
2. The complete type: the registered theorem's type is exactly
   `U1Stmt f.ved_contract f.ved_mod f`, with the declaration constant itself.
3. The constant-dependency closure of the accepted theorem contains
   `{f}_deep_trace` and NO `native_decide` auxiliary and NO theorem of the
   native-dependent DeepElab families (`_deep_coneEval_*`, `_deep_regstep`,
   `_deep_signal_run`, …), although those exist in the environment.
4. Refusals (all through `expectRefused`, which also checks that none of the
   checker's constants, auxiliaries included, is left): mutated modules
   (init, constant), another declaration's DeepElab facts (different
   meaning), another declaration's accepted proof, a `native_decide`-carrying
   proof and a proof that drags in DeepElab's native replay theorem (strict
   audit), and a declaration `#verify_elab_deep` never ran on.
5. Kernel: the init-mutated module does not implement `accK9`
   (`¬ U1Stmt`, a cycle-0 witness).
-/

namespace Tests.Ved.U1DeepCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Deep

def accK (k : BitVec 8) (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg (0#8)
    let a := (acc : Signal defaultDomain (BitVec 8))
    acc <~ a + d + (Signal.pure k : Signal defaultDomain (BitVec 8))
    return a

def accK9 (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := accK 9#8 d

/-- Same shape as `accK9`, a different constant (a different meaning). -/
def accK10 (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := accK 10#8 d

/-- `#verify_elab_deep` is never run on this one. -/
def accK11 (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := accK 11#8 d

def natInit (n : Nat) (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (BitVec.ofNat 8 n)
    let a := (r : Signal defaultDomain (BitVec 8))
    r <~ a + d
    return a

def natInit5 (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := natInit 5 d

#guard_msgs (drop info) in
#verify_elab_deep accK9
#guard_msgs (drop info) in
#verify_elab_deep accK10
#guard_msgs (drop info) in
#verify_elab_deep natInit5

/-! ## 1. The entry accepts both examples -/

def runEntry (n : Name) : CommandElabM Unit := liftTermElabM do
  let (_, _, thm) ← vedU1DeepEntry n
  let r ← Tools.VedStrictAudit.strictAudit thm
  logInfo m!"VED U1 OK {thm}: {Tools.VedStrictAudit.showNames r.axioms}"

/-- info: VED U1 OK Tests.Ved.U1DeepCheck.accK9.ved_u1: [Classical.choice, Quot.sound, propext] -/
#guard_msgs in
run_cmd runEntry ``accK9

/-- info: VED U1 OK Tests.Ved.U1DeepCheck.natInit5.ved_u1: [Classical.choice, Quot.sound, propext] -/
#guard_msgs in
run_cmd runEntry ``natInit5

/-! ## 2. The complete type -/

example : U1Stmt accK9.ved_contract accK9.ved_mod accK9 := accK9.ved_u1
example : U1Stmt natInit5.ved_contract natInit5.ved_mod natInit5 := natInit5.ved_u1

/-- info: complete type: accK9.ved_u1, natInit5.ved_u1 -/
#guard_msgs in
run_cmd liftTermElabM do
  for n in [``accK9, ``natInit5] do
    let ti ← getConstInfo (n ++ `ved_u1)
    let expected := mkAppN (mkConst ``U1Stmt)
      #[mkConst (n ++ `ved_contract), mkConst (n ++ `ved_mod), mkConst n]
    unless ti.type == expected do throwError "type of {n}.ved_u1 is not the expected statement"
  logInfo "complete type: accK9.ved_u1, natInit5.ved_u1"

/-! ## 3. Constant-dependency closure (separately from `collectAxioms`) -/

/-- Every constant reachable from `n` through types and values. -/
partial def constClosure (n : Name) : CoreM NameSet := do
  let rec go (todo : List Name) (seen : NameSet) : CoreM NameSet := do
    match todo with
    | [] => pure seen
    | c :: rest =>
      if seen.contains c then go rest seen else
      let seen := seen.insert c
      let some ci := (← getEnv).find? c | go rest seen
      let cs := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      go (cs.toList ++ rest) seen
  go [n] {}

/-- A `native_decide` auxiliary, or a theorem of the DeepElab families whose
proofs use `native_decide`. -/
def nativeFamily (c : Name) : Bool :=
  let s := c.toString
  (s.splitOn "_native").length > 1 ||
  ["_deep_coneEval", "_deep_regstep", "_deep_seed_bounded", "_deep_step_", "_deep_signalM",
   "_deep_signal_fold", "_deep_signal_run", "_deep_state_trace"].any (fun p => (s.splitOn p).length > 1)

/-- info: closure of accK9.ved_u1: has accK9_deep_trace, no native family (environment has accK9_deep_signal_run) -/
#guard_msgs in
run_cmd liftTermElabM do
  let cl ← constClosure ``accK9.ved_u1
  unless cl.contains ``accK9_deep_trace do throwError "accK9_deep_trace not used (vacuous)"
  for c in cl.toList do
    if nativeFamily c then throwError "closure contains {c}"
  unless (← getEnv).contains ``accK9_deep_signal_run do throwError "control premise: no native theorem in env"
  logInfo "closure of accK9.ved_u1: has accK9_deep_trace, no native family (environment has accK9_deep_signal_run)"

/-! ## 4. Refusals -/

def modOf (base : Name) : TermElabM Sparkle.IR.AST.Module := do
  let some v := (← getConstInfo (base ++ `ved_mod)).value? | throwError "no value"
  evalModule v

/-- The checker's constants for `base`, the builder's auxiliaries included. -/
def checkerNames (base : Name) : List Name :=
  [`ved_mod, `ved_contract, `ved_outs, `ved_u1].map (base ++ ·) ++ auxNames base

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

def deepSrc (stmt deep : Name) : TermElabM ProofSrc := do
  let tbl ← readTable stmt
  pure (.built (buildDeepWith stmt deep tbl))

/-- The register init changed to 5. -/
def mutInit (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .register o c r i _ => .register o c r i 5
      | s => s }

/-- The constant 9 changed to 10. -/
def mutConst (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .assign n (.const 9 w) => .assign n (.const 10 w)
      | s => s }

/-- info: mutations differ from the original -/
#guard_msgs in
run_cmd liftTermElabM do
  let m ← modOf ``accK9
  if decide (mutInit m = m) || decide (mutConst m = m) then throwError "a mutation is the identity"
  logInfo "mutations differ from the original"

-- mutated modules against the real declaration and its own DeepElab facts
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlInit) do
  discard <| checkU1 ``accK9 `ctlInit ``accK9 (mutInit (← modOf ``accK9)) (← deepSrc ``accK9 ``accK9)

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlConst) do
  discard <| checkU1 ``accK9 `ctlConst ``accK9 (mutConst (← modOf ``accK9)) (← deepSrc ``accK9 ``accK9)

-- another declaration's DeepElab facts (a different meaning: constant 10)
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlFacts10) do
  discard <| checkU1 ``accK9 `ctlFacts10 ``accK9 (← modOf ``accK9) (← deepSrc ``accK9 ``accK10)

-- … and the second example's facts for the first example
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlFactsNat) do
  discard <| checkU1 ``accK9 `ctlFactsNat ``accK9 (← modOf ``accK9) (← deepSrc ``accK9 ``natInit5)

-- another declaration's accepted proof
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlProofNat) do
  discard <| checkU1 ``accK9 `ctlProofNat ``accK9 (← modOf ``accK9) (.term (mkCIdent ``natInit5.ved_u1))

-- a correct proof carrying a `native_decide` fact (strict audit)
/-- info: refused [audit], clean -/
#guard_msgs in
run_cmd expectRefused "audit" (checkerNames `ctlNative) do
  let stx ← `((fun (_ : (2 : Nat) + 2 = 4) => accK9.ved_u1) (by native_decide))
  discard <| checkU1 ``accK9 `ctlNative ``accK9 (← modOf ``accK9) (.term stx)

-- a correct proof that drags in DeepElab's native IR replay theorem (strict audit)
/-- info: refused [audit], clean -/
#guard_msgs in
run_cmd expectRefused "audit" (checkerNames `ctlReplay) do
  let stx ← `((fun (_ : True) => accK9.ved_u1) (by have := @accK9_deep_signal_run; trivial))
  discard <| checkU1 ``accK9 `ctlReplay ``accK9 (← modOf ``accK9) (.term stx)

-- no `#verify_elab_deep` for this declaration: the builder refuses
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames ``accK11) do
  discard <| vedU1DeepEntry ``accK11

/-! ## 5. Kernel: the init-5 module does not implement `accK9` -/

def mAcc5 : Sparkle.IR.AST.Module := mutInit accK9.ved_mod

def cAcc5 : Contract := contractOf (ved_table% accK9) ["out"] (some ("clk", "rst")) mAcc5

def zeros : Nat → String → Nat := fun _ _ => 0

theorem zeros_ok : InputsOk cAcc5 mAcc5 zeros :=
  ⟨fun _ _ _ => Nat.two_pow_pos _, fun _ _ _ => rfl⟩

theorem out_mem (c : Contract) (h : c.outputs = [⟨"out", .bitVector 8⟩]) :
    (⟨"out", .bitVector 8⟩ : Port) ∈ c.outputs := by
  rw [h]; exact List.mem_singleton_self _

/-- The declaration's output at cycle 0 is 0 (from DeepElab's trace and init). -/
theorem src0 : srcOf cAcc5 accK9 zeros "out" 0 = 0 := by
  simp [srcOf, cAcc5, contractOf, applyIns, OTy.obs, PTy.obs]
  rw [accK9_deep_trace]
  simp only [CExpr.compile, accK9_deep_out, Cdo.irState, accK9_deep_inits]
  simp [Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalExpr.go,
    Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalOp, envOfC, weOfC, chainMap, List.finRange,
    accK9_nm, natJoin, widthOf, mask, Nat.shiftRight_eq_div_pow, accK9_inp, PTy.sig, zeros]

theorem acc5_not_accK9 : ¬ U1Stmt cAcc5 mAcc5 accK9 :=
  not_u1_of_not_outputs <|
    not_outputs_of_witness _ _ _ zeros zeros_ok 1 0 (by decide) ⟨"out", .bitVector 8⟩
      (out_mem _ (by decide))
      _ rfl _ rfl (by show _ ≠ srcOf cAcc5 accK9 zeros "out" 0; rw [src0]; decide)

end Tests.Ved.U1DeepCheck

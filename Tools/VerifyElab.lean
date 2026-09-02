/-
  `#verify_elab f` — kernel-checked proof that the IR the elaborator
  produces for a `circuit do` definition computes the same cycle trace
  as the definition's own Signal semantics.

  This is the link the other verifiers do not touch: `#verify_emit`
  and `#verify_dsl_roundtrip` are IR↔IR congruences, while user proofs
  live on the Signal side.  The generated theorem is

      f_elab_trace : ∀ inputs t,
        f_irTrace inputs t = ((f inputs).val t).toNat

  where `f_irTrace` is the register-state recurrence the PROVEN IR
  semantics (`Sparkle.IR.Semantics.evalExpr`) induces on the elaborated
  module — so the statement lands on the same semantics the M0–M4
  certified-roundtrip stack starts from, giving (per instance)

      Signal semantics ≡ IR semantics ≡ emitted SystemVerilog.

  Prototype and tactic-recipe validation:
  `Tests/Verification/ElabTracePrototype.lean`.

  v1 scope: single module, exactly ONE register, output = that
  register, all inputs `BitVec`-typed signals.  Same interactive-run
  caveat as `#verify_eq` (docs/KnownIssues.md Issue 2).
-/

import Lean
import Sparkle.Compiler.Elab
import Sparkle.IR.Semantics
import Tools.SVParser.VerifyEmit

namespace Tools.VerifyElab

open Lean Elab Command
open Sparkle.IR.AST
open Sparkle.Core Sparkle.Core.Signal
open Sparkle.IR.Optimize (buildDefMap)
open Tools.SVParser.VerifyEmit (inlineCone widthTable denote varIdent)

deriving instance ToExpr for Sparkle.IR.Type.DimExpr
deriving instance ToExpr for Sparkle.IR.AST.Operator
deriving instance ToExpr for Sparkle.IR.AST.Expr

/-- Collect the module's single register: (name, inputExpr, init). -/
def theRegister (m : Sparkle.IR.AST.Module) :
    Except String (String × Sparkle.IR.AST.Expr × Int) := do
  let regs := m.body.filterMap fun st => match st with
    | .register out _ _ input init => some (out, input, init)
    | _ => none
  match regs with
  | [r] => .ok r
  | [] => .error "#verify_elab: no register in the module"
  | _ => .error "#verify_elab v1: exactly one register supported"

/-- Non-clock, non-reset inputs, elaborator order. -/
def dataInputs (m : Sparkle.IR.AST.Module) : List (String × Nat) :=
  m.inputs.filterMap fun p =>
    if p.name == "clk" || p.name == "rst" then none
    else some (p.name, p.ty.bitWidth)

elab "#verify_elab" id:ident : command => do
  let declName ← liftTermElabM <|
    Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
  let design ← liftTermElabM
    (Sparkle.Compiler.Elab.synthesizeHierarchical declName)
  let m ← match design.modules with
    | [m] => pure m
    | _ => throwError "#verify_elab v1: single-module designs only"
  let (regName, regInput, regInit) ← match theRegister m with
    | .ok r => pure r
    | .error e => throwError e
  let ins := dataInputs m
  -- widths: register + inputs
  let wt := (widthTable m)
  let regW := wt.getD regName 0
  -- inline the register's next-state cone over {register} ∪ inputs
  let stopAt : Std.HashMap String Bool :=
    (ins.foldl (fun (h : Std.HashMap String Bool) (n, _) =>
      h.insert n true) {}).insert regName true
  let dm := buildDefMap m.body
  let cone ← match inlineCone dm stopAt 10000 regInput with
    | .ok c => pure c
    | .error e => throwError "#verify_elab: {e}"
  -- the DSL's parameter names, from `_gen_<param>` input names
  let paramOf (n : String) : String :=
    match n.dropPrefix? "_gen_" with
    | some sub => sub.toString
    | none => n
  let base := declName.componentsRev.headD (Name.mkSimple "x")
    |>.toString
  let mkI (s : String) : Ident := mkIdent (Name.mkSimple s)
  let weId := mkI s!"{base}_weM"
  let envId := mkI s!"{base}_envAt"
  let trId := mkI s!"{base}_irTrace"
  let thId := mkI s!"{base}_elab_trace"
  -- binders for the DSL inputs
  let paramIds : Array Ident :=
    (ins.map fun (n, _) => mkI (paramOf n)).toArray
  let paramBinders ← ins.toArray.mapM fun (n, w) => do
    let pid := mkI (paramOf n)
    `(Lean.Parser.Term.bracketedBinderF| ($pid :
      Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain
        (BitVec $(quote w))))
  -- weM : widths of register and inputs
  let weBody ← do
    let mut acc ← `((0 : Nat))
    for (n, w) in ((regName, regW) :: ins).reverse do
      acc ← `(if n == $(quote n) then $(quote w) else $acc)
    pure acc
  elabCommand (← `(def $weId : Sparkle.IR.Semantics.WEnv :=
    fun n => $weBody))
  -- envAt : register ↦ s, each input ↦ (x.val t).toNat
  let envBody ← do
    let mut acc ← `((0 : Nat))
    for (n, _) in ins.reverse do
      let pid := mkI (paramOf n)
      acc ← `(if n == $(quote n) then (($pid).val t).toNat else $acc)
    `(if n == $(quote regName) then s else $acc)
  elabCommand (← `(def $envId $paramBinders* (s t : Nat) :
      Sparkle.IR.Semantics.Env := fun n => $envBody))
  -- the inlined cone, declared directly as a constant (ToExpr gives a
  -- closed value; addDecl avoids the syntax round-trip)
  let coneId := mkI s!"{base}_cone"
  liftCoreM <| addAndCompile <| .defnDecl {
    name := coneId.getId
    levelParams := []
    type := mkConst ``Sparkle.IR.AST.Expr
    value := toExpr cone
    hints := .abbrev
    safety := .safe }
  -- without this, `simp only [f_cone]` in generated (or user) proofs
  -- dies with "enableRealizationsForConst must be called first"
  liftCoreM <| Lean.enableRealizationsForConst coneId.getId
  let coneT : Term := ⟨coneId.raw⟩
  let appArgs : Array Term := paramIds.map fun p => ⟨p.raw⟩
  elabCommand (← `(def $trId $paramBinders* : Nat → Nat
    | 0 => $(quote regInit.toNat)
    | t+1 => (Sparkle.IR.Semantics.evalExpr $weId
        ($envId $appArgs* ($trId $appArgs* t) t) $coneT).getD 0))
  -- ---- stage 2: the theorems --------------------------------------
  -- the step form: VerifyEmit's reflector over the cone, refs as v_*
  -- idents, beta-bound register-first-then-inputs
  let stepBody ← denote wt cone
  let vBinders ← ((regName, regW) :: ins).toArray.mapM fun (n, w) => do
    `(Lean.Parser.Term.funBinder|
      ($(varIdent n) : BitVec $(quote w)))
  let fApp ← `(($(id) $appArgs*))
  let stepArgs ← ((regName, regW) :: ins).toArray.mapM fun (n, _) => do
    if n == regName then `((($fApp).val n))
    else `((($(mkI (paramOf n))).val n))
  let stepId := mkI s!"{base}_step'"
  let zeroId := mkI s!"{base}_zero'"
  let traceThId := mkI s!"{base}_elab_trace"
  -- the tactic recipes, validated in Tests/Verification (prototype)
  -- and scratch velab8 (fully generic form)
  let recipeHead ← `(tactic|
    (simp only [$id:ident, runCircuitH, Signal.loop, Signal.map];
     rw [Signal.loopGo_eq];
     simp [packRegister, Signal.register, Signal.mux, Signal.map,
       bundle2, Signal.pure, Functor.map, Seq.seq, Signal.ap,
       Signal.seq, Nat.lt_succ_iff]))
  elabCommand (← `(private theorem $zeroId $paramBinders* :
      ($fApp).val 0 = BitVec.ofNat $(quote regW) $(quote regInit.toNat)
      := by $recipeHead:tactic))
  elabCommand (← `(private theorem $stepId $paramBinders* (n : Nat) :
      ($fApp).val (n+1)
      = (fun $vBinders* => $stepBody) $stepArgs* := by
    $recipeHead:tactic
    simp only [HAdd.hAdd, HSub.hSub, HMul.hMul, HAnd.hAnd, HOr.hOr,
      HXor.hXor, Functor.map, Seq.seq, Signal.ap, Signal.seq,
      Signal.map]
    repeat' split
    all_goals (try simp_all)
    all_goals (first | rfl | bv_decide)))
  elabCommand (← `(theorem $traceThId $paramBinders* (t : Nat) :
      $trId $appArgs* t = (($fApp).val t).toNat := by
    induction t with
    | zero => simp [$trId:ident, $zeroId:ident]
    | succ n ih =>
      rw [$trId:ident, ih]
      unfold $envId:ident
      simp only [$coneId:ident]
      simp [Sparkle.IR.Semantics.evalExpr,
        Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalOp,
        Sparkle.IR.Semantics.evalExpr.go, Sparkle.IR.Semantics.mask,
        $weId:ident, Sparkle.IR.Semantics.widthOf]
      rw [$stepId:ident]
      simp only []
      repeat' split
      all_goals (try simp_all [BitVec.toNat_eq,
        BitVec.extractLsb'_eq_extractLsb, BitVec.toNat_add])
      all_goals (first | rfl | bv_omega)))
  -- the generated proofs recover failed tactics as `sorry`, so a
  -- success log without an axiom check would lie — it did once, on the
  -- first `sub` circuit, before this check existed
  let axioms ← liftCoreM <| Lean.collectAxioms traceThId.getId
  if axioms.contains ``sorryAx then
    throwError "#verify_elab {id.getId}: a generated proof FAILED (the theorem depends on sorryAx) — see the errors above"
  logInfo m!"#verify_elab {id.getId}: PROVEN — {traceThId.getId} (register {regName}, {ins.length} inputs; axioms clean)"

end Tools.VerifyElab

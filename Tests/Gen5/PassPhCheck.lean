import Tools.PassPh.Pass
import Tests.Gen3.ExpectedType
set_option autoImplicit false
set_option linter.unusedVariables false
-- NOT BUILT (Check for Tools/PassPh/Pass.lean, freeze rev2 + rev3). No sorry / axiom / native_decide in source. Conditional result: pass_ph holds under the hypotheses BetaNonTargetAgrees (T1 +1 candidate), ExprEqvLaws (T1 +1 candidate), HeadBetaAgreesL (replaces T1L-74), RecRulePhU (hypothesis definition); none accepted. Clean build is the coder's.

/-! # RT pass_ph checks (Tools/PassPh/*.lean, Tools/Assume/ExprEqvGL.lean)

TYPE: `pass_ph` and `PassPh'` are compared by `checkExpected` against `ExpPassPh` written here (own spelling), independently of the freeze text; `example := pass_ph`.
MUTANT: well-typed single changes of `ExpPassPh` (a hypothesis dropped), rejected by signature / defeq (NOT semantic counterexamples).
AXIOMS: standard only. CLOSURE: no sorryAx / ofReduceBool / trustCompiler in the closure of the targets. -/

namespace Tests.Gen5.PassPhCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tests.Gen3.ExpectedType Tools.Assume.AbbrevExtern Tools.PassPh

section Expected

def ExpPassPh : Prop := ∀ (natLit? : Lean.Expr → Option Nat) (env : Lean.Environment),
  Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env → ReplaceAgrees → Tools.ShippingLetsReaderInv.Inst1Agrees →
  HeadBetaAgreesL → BetaNonTargetAgrees → Tools.Assume.ExprEqvGL.ExprEqvLaws →
  ∀ (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
    Sparkle.Compiler.MachRecUnfold.pass env natLit? isUser e = .ok r → NoPh r = true ∧ BvarLt 0 r = true

-- mutants: one hypothesis dropped (the statement becomes stronger / different, so the proof's type differs)
def MutNoEq : Prop := ∀ (natLit? : Lean.Expr → Option Nat) (env : Lean.Environment),
  Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env → ReplaceAgrees → Tools.ShippingLetsReaderInv.Inst1Agrees →
  HeadBetaAgreesL → BetaNonTargetAgrees →
  ∀ (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
    Sparkle.Compiler.MachRecUnfold.pass env natLit? isUser e = .ok r → NoPh r = true ∧ BvarLt 0 r = true
def MutNoHH : Prop := ∀ (natLit? : Lean.Expr → Option Nat) (env : Lean.Environment),
  Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env → ReplaceAgrees → Tools.ShippingLetsReaderInv.Inst1Agrees →
  BetaNonTargetAgrees → Tools.Assume.ExprEqvGL.ExprEqvLaws →
  ∀ (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
    Sparkle.Compiler.MachRecUnfold.pass env natLit? isUser e = .ok r → NoPh r = true ∧ BvarLt 0 r = true
def MutNoRec : Prop := ∀ (natLit? : Lean.Expr → Option Nat) (env : Lean.Environment),
  Tools.Assume.EnvDeclValue.DeclValuePh env → ReplaceAgrees → Tools.ShippingLetsReaderInv.Inst1Agrees →
  HeadBetaAgreesL → BetaNonTargetAgrees → Tools.Assume.ExprEqvGL.ExprEqvLaws →
  ∀ (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
    Sparkle.Compiler.MachRecUnfold.pass env natLit? isUser e = .ok r → NoPh r = true ∧ BvarLt 0 r = true
def MutNoBeta : Prop := ∀ (natLit? : Lean.Expr → Option Nat) (env : Lean.Environment),
  Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env → ReplaceAgrees → Tools.ShippingLetsReaderInv.Inst1Agrees →
  HeadBetaAgreesL → Tools.Assume.ExprEqvGL.ExprEqvLaws →
  ∀ (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
    Sparkle.Compiler.MachRecUnfold.pass env natLit? isUser e = .ok r → NoPh r = true ∧ BvarLt 0 r = true

end Expected

example : ExpPassPh := fun natLit? => pass_ph natLit?
example : PassPh' := pass_ph
example : ExpPassPh = PassPh' := rfl
-- the three components of `ExprEqvLaws` are exactly the facts the memo needs (no global instance)
example (h : Tools.Assume.ExprEqvGL.ExprEqvLaws) : EquivBEq Lean.Expr := h.equiv
example (h : Tools.Assume.ExprEqvGL.ExprEqvLaws) : LawfulHashable Lean.Expr := h.lawfulHash
example (h : Tools.Assume.ExprEqvGL.ExprEqvLaws) : ∀ a b : Lean.Expr, (a == b) = true → ∀ L, GL L a → GL L b := h.pres

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``pass_ph ``ExpPassPh
  checkExpected ``PassPh' ``ExpPassPh
  logInfo m!"RT PASSPHCHECK TYPE 2 declarations compared (pass_ph, PassPh')"
  checkMutant ``pass_ph ``MutNoEq
  checkMutant ``pass_ph ``MutNoHH
  checkMutant ``pass_ph ``MutNoRec
  checkMutant ``pass_ph ``MutNoBeta
  logInfo m!"RT PASSPHCHECK MUTANT 4 statement mutants rejected (hEq / HeadBetaAgreesL / RecRulePhU / BetaNonTargetAgrees dropped; signature/defeq rejection, not semantic counterexamples)"

def targets : List Name := [``pass_ph, ``passWith_ph, ``passM_goodL, ``passStep_goodL, ``passSpine_goodL, ``passJoint,
  ``memoGoodL_insert, ``memoGoodL_hit, ``memoGoodL_empty, ``passPh']

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in targets do checkAxioms n
  logInfo m!"RT PASSPHCHECK AXIOMS {targets.length} declarations checked (standard axioms only)"

/-! ## Closure audit -/

def valueOfCI : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

partial def closureOf (env : Environment) (root : Name) : StateT (NameSet × NameSet) MetaM Unit := do
  if (← get).1.contains root then return
  modify fun (s, u) => (s.insert root, u)
  match env.find? root with
  | none => modify fun (s, u) => (s, u.insert root)
  | some ci =>
    for c in ci.type.getUsedConstants do closureOf env c
    match valueOfCI ci with
    | some v => for c in v.getUsedConstants do closureOf env c
    | none => pure ()
    match ci with
    | .inductInfo v => for c in v.ctors do closureOf env c
    | _ => pure ()

def forbiddenConsts : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler]

def closureHits (env : Environment) (roots : List Name) : MetaM (NameSet × NameSet × List Name) := do
  let (_, (seen, unk)) ← (roots.forM (closureOf env)).run ({}, {})
  pure (seen, unk, forbiddenConsts.filter seen.contains)

-- negative control (built in memory): a `sorryAx`-based theorem must be detected, a clean one not
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let bad := mkApp2 (mkConst ``sorryAx [Level.zero]) tru (mkConst ``Bool.false)
    addDecl (.thmDecl { name := `PassPhCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.thmDecl { name := `PassPhCheck.clean1, levelParams := [], type := tru, value := mkConst ``True.intro })
    let env ← getEnv
    let (_, _, hits) ← closureHits env [`PassPhCheck.direct]
    if hits.isEmpty then throwError "RT PASSPHCHECK CLOSURE CONTROL FAILED: sorry-based control not detected"
    let (_, _, hits2) ← closureHits env [`PassPhCheck.clean1]
    unless hits2.isEmpty do throwError "RT PASSPHCHECK CLOSURE CONTROL FAILED: clean control flagged"
    logInfo m!"RT PASSPHCHECK CLOSURE CONTROLS OK: 1 negative detected, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env targets
  for n in targets do
    unless seen.contains n do throwError "RT PASSPHCHECK CLOSURE FAILED: target {n} not in the closure seen set"
  unless hits.isEmpty do throwError "RT PASSPHCHECK CLOSURE FAILED: forbidden constants {hits}"
  unless unk.isEmpty do throwError "RT PASSPHCHECK CLOSURE FAILED: unknown constants {unk.toList}"
  logInfo m!"RT PASSPHCHECK CLOSURE OK: {seen.toList.length} constants from {targets.length} roots; no sorryAx / ofReduceBool / trustCompiler"

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo m!"RT PASSPHCHECK COUNTS: TYPE 2 / MUTANT 4 / AXIOMS {targets.length} / CLOSURE OK / CONTROLS 1+1 (conditional on BetaNonTargetAgrees, ExprEqvLaws, HeadBetaAgreesL, RecRulePhU; none accepted)"

end Tests.Gen5.PassPhCheck

import Tools.ShippingGen5ReaderTraceInlineCompose
import Tests.Gen3.ExpectedType
set_option autoImplicit false
set_option linter.unusedVariables false
-- Built in Pod (kjob lake build Tests.Gen5.ReaderTraceInlineComposeCheck, exit 0; TYPE 3 / MUTANT 2 (signature/defeq rejections, not semantic counterexamples) / AXIOMS 8 standard only / no sorryAx) on the tree of 2a6af8f053b88b44dbe1681b0dbaa93ec9e7b1b9 (Lean content identical; header comment-only). Clean build is the coder's. If a `sorry` returns to the source, the AXIOMS check fails with sorryAx.

/-! # RT inline compose checks

TYPE: the main theorems are compared by `checkExpected` against `Exp…` statements written here (own spelling), independently of the freeze `#check` text.
MUTANT: well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples).
AXIOMS: reports every axiom of each theorem; `sorryAx` is reported as a failure, so while sorries remain this check logs them instead of passing silently.
Hypotheses `DeclValuePh`, `RecRulePhU`, `PassPh`, `ReplaceAgrees`, `HeadBetaAgrees0` are theorem hypotheses only; none is claimed true for accepted sources. -/

namespace Tests.Gen5.ReaderTraceInlineComposeCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tests.Gen3.ExpectedType Tools.Assume.AbbrevExtern

section Expected

def ExpUserInliner : Prop := ∀ (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
  (hrr : RecRulePhU env) (hp : PassPh env) (hr : ReplaceAgrees) (hb : HeadBetaAgrees0)
  (e : Lean.Expr) (hn : NoPh e = true) (hbl : BvarLt 0 e = true),
    NoPh (Sparkle.Compiler.Elab.userInliner env e) = true ∧ BvarLt 0 (Sparkle.Compiler.Elab.userInliner env e) = true
def ExpRounds : Prop := ∀ (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
  (hrr : RecRulePhU env) (hp : PassPh env) (inl : Lean.Expr → Lean.Expr) (isRec : Lean.Name → Bool)
  (hinl : ∀ e : Lean.Expr, NoPh e = true → BvarLt 0 e = true → NoPh (inl e) = true ∧ BvarLt 0 (inl e) = true)
  (k : Nat) (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      NoPh (Sparkle.Compiler.Elab.userInliner.rounds env inl isRec k e) = true ∧
        BvarLt 0 (Sparkle.Compiler.Elab.userInliner.rounds env inl isRec k e) = true
def ExpInlinedConst : Prop := ∀ (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
  (hrr : RecRulePhU env) (hp : PassPh env) (hr : ReplaceAgrees) (hb : HeadBetaAgrees0)
  (c : Lean.Name) (ci0 : Lean.ConstantInfo) (hc : env.find? c = some ci0) (d : Lean.DefinitionVal)
  (hd : Sparkle.Compiler.Elab.inlinedConst (Sparkle.Compiler.Elab.userInliner env) ci0 = .defnInfo d),
    NoPh d.value = true ∧ BvarLt 0 d.value = true

-- mutants
def MutUserInlinerNoPass : Prop := ∀ (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
  (hr : ReplaceAgrees) (hb : HeadBetaAgrees0)
  (e : Lean.Expr) (hn : NoPh e = true) (hbl : BvarLt 0 e = true),
    NoPh (Sparkle.Compiler.Elab.userInliner env e) = true ∧ BvarLt 0 (Sparkle.Compiler.Elab.userInliner env e) = true
def MutUserInlinerL1 : Prop := ∀ (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
  (hrr : RecRulePhU env) (hp : PassPh env) (hr : ReplaceAgrees) (hb : HeadBetaAgrees0)
  (e : Lean.Expr) (hn : NoPh e = true) (hbl : BvarLt 1 e = true),
    NoPh (Sparkle.Compiler.Elab.userInliner env e) = true ∧ BvarLt 0 (Sparkle.Compiler.Elab.userInliner env e) = true

end Expected

-- Decoy: same suffix as the real hypothesis, different namespace. Used only as a negative control.
namespace Decoy
def RecRulePhU (_env : Lean.Environment) : Prop := True
theorem userInliner_ph_decoy (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hrr : RecRulePhU env) (hp : PassPh env) (hr : ReplaceAgrees) (hb : HeadBetaAgrees0) : True := trivial
end Decoy

/-- Fully qualified names of the Prop-typed, non-equation hypotheses (binder types) of `thm`. -/
def hypHeads (thm : Name) : MetaM (List Name) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    let mut out : Array Name := #[]
    for x in xs do
      let t ← inferType x
      if (← isProp t) then
        match t.getAppFn with
        | .const n _ => unless n == ``Eq do out := out.push n
        | _ => pure ()
    return out.toList

def checkHyps (thm : Name) (expected : List Name) : MetaM Unit := do
  let got ← hypHeads thm
  unless got.toArray.qsort Name.lt == expected.toArray.qsort Name.lt do
    throwError "RT INLINECOMPOSECHECK HYPS {thm}: got {got}, expected {expected}"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``userInliner_ph ``ExpUserInliner
  checkExpected ``rounds_ph ``ExpRounds
  checkExpected ``inlinedConst_defn_ph ``ExpInlinedConst
  for m in [``MutUserInlinerNoPass, ``MutUserInlinerL1] do
    let r ← try checkExpected ``userInliner_ph m; pure true catch _ => pure false
    if r then throwError "RT INLINECOMPOSECHECK MUTANT {m} was accepted"
  let hyps := [``Tools.Assume.EnvDeclValue.DeclValuePh, ``Tools.ShippingGen5ReaderTrace.RecRulePhU,
    ``Tools.ShippingGen5ReaderTrace.PassPh, ``Tools.Assume.AbbrevExtern.ReplaceAgrees, ``Tools.Assume.AbbrevExtern.HeadBetaAgrees0]
  checkHyps ``userInliner_ph hyps
  checkHyps ``inlinedConst_defn_ph hyps
  -- negative control: same-suffix decoy in another namespace must not match the qualified list
  let r ← try checkHyps ``Decoy.userInliner_ph_decoy hyps; pure true catch _ => pure false
  if r then throwError "RT INLINECOMPOSECHECK HYPS decoy RecRulePhU was accepted"
  logInfo m!"RT INLINECOMPOSECHECK HYPS 5 qualified hypotheses matched; decoy rejected"
  logInfo m!"RT INLINECOMPOSECHECK TYPE 3 / MUTANT 2 rejected by signature/defeq (not semantic counterexamples)"

def thms : List Name := [``inl_step_ph, ``rounds_ph, ``abbrev_fold_ph, ``userInliner_ph, ``inlinedConst_defn_ph,
  ``shapeInputs_of_decl', ``shapeInputs_of_inline', ``shapeInputs_of_entryConst']

run_cmd Lean.Elab.Command.liftTermElabM do
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array Name := #[]
  for n in thms do
    let ax ← Lean.collectAxioms n
    let extra := ax.filter (fun a => !std.contains a)
    unless extra.isEmpty do
      logInfo m!"RT INLINECOMPOSECHECK AXIOMS {n}: non-standard {extra.toList}"
      bad := bad.push n
  if bad.isEmpty then
    logInfo m!"RT INLINECOMPOSECHECK AXIOMS {thms.length} declarations checked (standard axioms only); CLOSURE: no sorryAx"
  else
    throwError "RT INLINECOMPOSECHECK AXIOMS/CLOSURE: sorryAx or other axioms in {bad.toList}"

end Tests.Gen5.ReaderTraceInlineComposeCheck

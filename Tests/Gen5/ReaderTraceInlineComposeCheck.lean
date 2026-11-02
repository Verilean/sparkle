import Tools.ShippingGen5ReaderTraceInlineCompose
import Tests.Gen3.ExpectedType
set_option autoImplicit false
set_option linter.unusedVariables false
-- NOT BUILT. Check for Tools/ShippingGen5ReaderTraceInlineCompose.lean (scripts/gen5/RT_INLINE_COMPOSE_FREEZE.md). If any `sorry` returns to the source, the AXIOMS line below reports `sorryAx` (that is the intended signal while sorries remain).

/-! # RT inline compose checks

TYPE: the main theorems are compared by `checkExpected` against `Exp…` statements written here (own spelling), independently of the freeze `#check` text.
MUTANT: well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples).
AXIOMS: reports every axiom of each theorem; `sorryAx` is reported as a failure, so while sorries remain this check logs them instead of passing silently.
Hypotheses `DeclValuePh`, `RecRulePh`, `PassPh`, `ReplaceAgrees`, `HeadBetaAgrees0` are theorem hypotheses only; none is claimed true for accepted sources. -/

namespace Tests.Gen5.ReaderTraceInlineComposeCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tests.Gen3.ExpectedType Tools.Assume.AbbrevExtern

section Expected

def ExpUserInliner : Prop := ∀ (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
  (hrr : RecRulePh env) (hp : PassPh env) (hr : ReplaceAgrees) (hb : HeadBetaAgrees0)
  (e : Lean.Expr) (hn : NoPh e = true) (hbl : BvarLt 0 e = true),
    NoPh (Sparkle.Compiler.Elab.userInliner env e) = true ∧ BvarLt 0 (Sparkle.Compiler.Elab.userInliner env e) = true
def ExpRounds : Prop := ∀ (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
  (hrr : RecRulePh env) (hp : PassPh env) (inl : Lean.Expr → Lean.Expr) (isRec : Lean.Name → Bool)
  (hinl : ∀ e : Lean.Expr, NoPh e = true → BvarLt 0 e = true → NoPh (inl e) = true ∧ BvarLt 0 (inl e) = true)
  (k : Nat) (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      NoPh (Sparkle.Compiler.Elab.userInliner.rounds env inl isRec k e) = true ∧
        BvarLt 0 (Sparkle.Compiler.Elab.userInliner.rounds env inl isRec k e) = true
def ExpInlinedConst : Prop := ∀ (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
  (hrr : RecRulePh env) (hp : PassPh env) (hr : ReplaceAgrees) (hb : HeadBetaAgrees0)
  (c : Lean.Name) (ci0 : Lean.ConstantInfo) (hc : env.find? c = some ci0) (d : Lean.DefinitionVal)
  (hd : Sparkle.Compiler.Elab.inlinedConst (Sparkle.Compiler.Elab.userInliner env) ci0 = .defnInfo d),
    NoPh d.value = true ∧ BvarLt 0 d.value = true

-- mutants
def MutUserInlinerNoPass : Prop := ∀ (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
  (hr : ReplaceAgrees) (hb : HeadBetaAgrees0)
  (e : Lean.Expr) (hn : NoPh e = true) (hbl : BvarLt 0 e = true),
    NoPh (Sparkle.Compiler.Elab.userInliner env e) = true ∧ BvarLt 0 (Sparkle.Compiler.Elab.userInliner env e) = true
def MutUserInlinerL1 : Prop := ∀ (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
  (hrr : RecRulePh env) (hp : PassPh env) (hr : ReplaceAgrees) (hb : HeadBetaAgrees0)
  (e : Lean.Expr) (hn : NoPh e = true) (hbl : BvarLt 1 e = true),
    NoPh (Sparkle.Compiler.Elab.userInliner env e) = true ∧ BvarLt 0 (Sparkle.Compiler.Elab.userInliner env e) = true

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``userInliner_ph ``ExpUserInliner
  checkExpected ``rounds_ph ``ExpRounds
  checkExpected ``inlinedConst_defn_ph ``ExpInlinedConst
  for m in [``MutUserInlinerNoPass, ``MutUserInlinerL1] do
    let r ← try checkExpected ``userInliner_ph m; pure true catch _ => pure false
    if r then throwError "RT INLINECOMPOSECHECK MUTANT {m} was accepted"
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

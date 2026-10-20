import Lean

/-! # Name-agnostic unfolding of a goal's auxiliary case analyses

WRITTEN, NOT BUILT (branch `fix/reader-p3`). Meta code only: two tactics, no
theorem, no axiom.

Lean v4.32.1 does not generate the equation lemmas / splitter of a `match`
with name-literal and array-literal patterns ("failed to generate equality
theorems for `match` expression", measured on `rawNode.match_15` and on the
copy `stepOldP.match_1`), so such a matcher is reasoned about from its
definition: `unfold` the matcher, split the scrutinees into constructors,
then unfold the sparse case analyses (`X._sparseCasesOn_k`) so that the
`dite`s on the string components / the array size become visible to `split`
(technique of `Tools.ShippingReaderRawNodeArm.match15_three`).

The names of those auxiliaries are generated (`mkAuxDeclName` under the name
of the first definition of the module that needed the same sparse case
analysis; the cache is per module) and change when an unrelated definition
of the same module changes (the `prodMatcherArity?` switch removes `go`'s
auxiliaries, which `rawNode.match_15` reused). These tactics read them off
the goal instead of naming them:

* `dsimp_sparse_aux` — `dsimp only [X₁, …, Xₖ]` over every sparse case
  analysis occurring in the goal (tagged `isSparseCasesOn`, or named
  `_sparseCasesOn…`); fails when there is none (use under `try`/`first`);
* `unfold_matchers_aux` — `unfold M₁ … Mₖ` over every matcher (`isMatcherCore`)
  occurring in the goal. -/
namespace Tools.ShippingSparseCasesTac
open Lean Elab Tactic

/-- The constants of the main goal's target that satisfy `p`. -/
def goalConsts (p : Environment → Name → Bool) : TacticM (Array Name) := withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let env ← getEnv
  return t.getUsedConstants.filter (p env)

/-- A sparse case analysis (`X._sparseCasesOn_k`). -/
def isSparseAux (env : Environment) (n : Name) : Bool :=
  isSparseCasesOn env n ||
    (match n with
     | .str _ s => s.startsWith "_sparseCasesOn"
     | _ => false)

/-- A matcher (`X.match_k`). -/
def isMatcherAux (env : Environment) (n : Name) : Bool :=
  Meta.isMatcherCore env n

/-- The constant as identifier text, from the root. -/
def idText (n : Name) : String :=
  "_root_." ++ n.toString

/-- Parse a tactic from text and run it on the main goal. -/
def runText (s : String) : TacticM Unit := do
  match Parser.runParserCategory (← getEnv) `tactic s with
  | .ok stx => evalTactic stx
  | .error msg => throwError "internal tactic text did not parse: {msg}\n{s}"

/-- `dsimp only [X₁, …, Xₖ]` over every sparse case analysis of the goal. -/
elab "dsimp_sparse_aux" : tactic => do
  let ns ← goalConsts isSparseAux
  if ns.isEmpty then
    throwError "dsimp_sparse_aux: no sparse case analysis in the goal"
  runText ("dsimp only [" ++ ", ".intercalate (ns.toList.map idText) ++ "]")

/-- `unfold M₁ … Mₖ` over every matcher of the goal. -/
elab "unfold_matchers_aux" : tactic => do
  let ns ← goalConsts isMatcherAux
  if ns.isEmpty then
    throwError "unfold_matchers_aux: no matcher in the goal"
  runText ("unfold " ++ " ".intercalate (ns.toList.map idText))

end Tools.ShippingSparseCasesTac

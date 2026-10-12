import Sparkle
import Tools.ShippingReaderNodes2

/-! # A WELL-TYPED body the old recogniser accepts and the strict reader refuses (G3)

`Tests/Compiler/ReaderWildcardTest.lean` showed the recognisers accept
ill-typed expressions. This file asks the question that matters: is there a
declaration the Lean kernel ACCEPTS whose value the recogniser accepts and
that is not a quotation?

`wtMux` below is a real declaration. Its nodes mention the domain as two
different terms — `defaultDomain` and `altDomain`, a definition that unfolds
to it — so every node is well typed (the types agree by unfolding
`altDomain`), while no single `dom` makes `quote dom … t` equal to the body
syntactically.

Logs only (compiled code), prefixed `WTWILD`; no assertion:
the recognisers on the declaration's value, the certified shape, whether the
entry takes the declaration as it is, the strict reader at either domain
term, and whether the real compile succeeds. Expected from reading the
definitions: recognisers `true`, shape found, strict reader `none` at both. -/
namespace Tests.Compiler.ReaderWellTypedWildcardTest
open Lean Meta
open Sparkle.Core.Domain Sparkle.Core.Signal

/-- A second name for the default domain: definitionally `defaultDomain`. -/
def altDomain : DomainConfig := defaultDomain

/-- Well typed: each node's domain is `defaultDomain` up to unfolding
`altDomain`; syntactically the nodes disagree. -/
def wtMux : Signal defaultDomain Bool :=
  @Signal.mux altDomain Bool (@Signal.pure defaultDomain Bool true)
    (@Signal.pure altDomain Bool false) (@Signal.pure defaultDomain Bool true)

open Sparkle.Compiler.Elab Tools.ShippingReaderTerm Tools.ShippingReaderInputs
  Tools.ShippingReaderNodes2 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let ci ← getConstInfo ``wtMux
  let some body := ci.value? | throwError "wtMux has no value"
  IO.println s!"WTWILD value = {← ppExpr body}"
  IO.println s!"WTWILD unifiedGateBoolBody = {unifiedGateBoolBody #[] body}"
  IO.println s!"WTWILD mixedGateBoolBody = {mixedGateBoolBody #[] body}"
  IO.println s!"WTWILD mixedCertifiedShape? isSome = {(mixedCertifiedShape? false [] ci).isSome}"
  let entry := entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)
  IO.println s!"WTWILD entry constant keeps the value = {entry.value?.map (· == body)}"
  let domA : Lean.Expr := .const ``Sparkle.Core.Domain.defaultDomain []
  let domB : Lean.Expr := .const ``altDomain []
  IO.println s!"WTWILD strict reader at defaultDomain = {(readTerm2 (kindsCfg domA (isExpr domA) []) body).isSome}"
  IO.println s!"WTWILD strict reader at altDomain = {(readTerm2 (kindsCfg domB (isExpr domB) []) body).isSome}"
  try
    let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational ``wtMux
    IO.println s!"WTWILD real compile: succeeded, {b.body.length} statements"
  catch ex =>
    IO.println s!"WTWILD real compile: failed ({← ex.toMessageData.toString})"

end Tests.Compiler.ReaderWellTypedWildcardTest

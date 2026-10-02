import Tools.ShippingInlineSoundness
import Tests.Compiler.ShippingMixedExecutionTest

/-! Two-level Bool lifts at the real entry.

`(fun x y => x && !y) <$> a <*> b`, `!x && y` and `!(x || y)` are how the IP
library writes "set and not cleared" and "neither" on control signals. The
legacy lowering puts the inner application on a wire of its own and the
result on a second one; the inner or outer operator is the unary NOT, which
is a right-hand-side shape of the back half as of this unit (simple shape,
typed expression, printed text `(w'(x ^ w'dM))`, grammar, name binding). The
tests check byte parity with the legacy compile and prove the busy flag of a
bit-serial engine — "neither idle nor finishing" — end to end. -/
namespace Sparkle.Tests.Compiler.ShippingBoolLiftSoundnessTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingUnifiedSource
open Tools.ShippingMixedSourceBridge Tools.ShippingMixedExecutionSoundness
open Tools.ShippingInlineSoundness
open Tools.ShippingMuxLoweringSoundness (encodeBool)

/-! ## Shapes -/

section
variable {dom : DomainConfig}
def bAndNot (s l : Signal dom Bool) : Signal dom Bool :=
  (fun s l => s && !l) <$> s <*> l
def bNotAnd (s l : Signal dom Bool) : Signal dom Bool :=
  (fun s l => !s && l) <$> s <*> l
def bNor (i f : Signal dom Bool) : Signal dom Bool :=
  (fun i f => !(i || f)) <$> i <*> f
def bCone (a b c d : Signal dom (BitVec 8)) : Signal dom Bool :=
  (fun s l => s && !l) <$> (Signal.beq a b) <*> (Signal.beq c d)
def bMux (a b c d x y : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.mux ((fun s l => !s && l) <$> (Signal.beq a b) <*> (Signal.beq c d)) x y
/-- The same lift twice: the second is a cache hit. -/
def bShare (s l : Signal dom Bool) (x y : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.mux ((fun s l => s && !l) <$> s <*> l)
    (Signal.mux ((fun s l => s && !l) <$> s <*> l) x y) y
/-- The busy flag of a bit-serial engine: neither idle (count 0) nor
finishing (count 65). -/
def bBusy (cnt : Signal dom (BitVec 7)) : Signal dom Bool :=
  (fun i f => !(i || f)) <$> (Signal.beq cnt (Signal.pure 0#7)) <*>
    (Signal.beq cnt (Signal.pure 65#7))
/-- A three-level body is not one of the canonical bodies: legacy route. -/
def bDeep (a b : Signal dom Bool) : Signal dom Bool :=
  (fun x y => !(x && !y)) <$> a <*> b
end
def bConcrete (s l : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  (fun s l => s && !l) <$> s <*> l

/-! ## The busy flag, end to end -/

def bBusyTerm : Term .bool :=
  .appBool2 .nor (.compare .eq (.bitsInput 7 0) (.bitsLit 7 0))
    (.compare .eq (.bitsInput 7 0) (.bitsLit 7 65))

theorem bBusyTerm_wf : bBusyTerm.WF 0 1 (fun _ => 7) := by
  simp [bBusyTerm, Term.WF]

theorem bBusy_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    denote bi vi bBusyTerm = bBusy (vi 0 7) := rfl

#def_entry_value bBusyEntry of bBusy
def bBusyBinders : List (Name × MixedGateBinder) := [(`dom, .domain), (`cnt, .bits 7)]
theorem bBusy_peel : mixedGatePeel bBusyEntry = some (bBusyBinders,
    quote (.bvar 1) (fun _ => inputExpr bBusyBinders.length 1)
      (fun j => inputExpr bBusyBinders.length (j + 1)) bBusyTerm) := rfl

/-- **Source-to-RTL execution of a two-level Bool lift.** -/
theorem bBusy_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``bBusy) mctx mref cctx cref w (m, design) w')
    (entry : EntryDefines mctx mref cctx cref ``bBusy bBusyEntry) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bBusyBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``bBusy bBusyBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems (encodeBool ((bBusy (bits 1 7)).val tick)) := by
  apply execution_source_of_entry (kb := 0) (kv := 1) (vw := fun _ => 7)
    (bpos := fun _ => 1) (vpos := fun j => j + 1) hr entry
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) bBusy_peel bBusyTerm_wf
  · intro j hj; omega
  · intro j hj
    have h : j = 0 := by omega
    subst h
    exact ⟨`cnt, rfl⟩

/-! ## Runtime gates on the real compiler -/

run_cmd liftTermElabM do
  let env ← getEnv
  let pred := instancePredicate env
  let inl := userInliner env
  let translate : TranslateFn := fun e h t n => translateExprToWire e h t n
  let mut count := 0
  for name in [``bAndNot, ``bNotAnd, ``bNor, ``bCone, ``bMux, ``bShare, ``bBusy,
      ``bConcrete] do
    let ci ← getConstInfo name
    let ec := entryConst true false [] ci pred inl (userProjection? env)
    unless (mixedCertifiedShape? false [] ec pred).isSome do
      throwError "{name}: no gate accepts the lift"
    let (mc, dc) ← synthesizeCombinationalCore name [] false
    let (ml, dl) ← synthesizeCombinationalCoreWith translate name [] false
      (certifiedFrontEnd := false)
    unless mc.body == ml.body && mc.inputs == ml.inputs && mc.outputs == ml.outputs &&
        mc.wires == ml.wires && mc.name == ml.name && dc.modules == dl.modules do
      throwError "{name}: the certified compile departed from the legacy compile\n{repr mc.body}\n{repr ml.body}"
    -- The NOT is a shape the optimizer check does not normalise: the shipped
    -- module is the proved one.
    let (mf, _) ← synthesizeCombinational name
    unless Sparkle.IR.OptCheck.checkedOptimize mf == mf do
      throwError "{name}: the shipped module is not the retained one"
    count := count + 1
  unless count == 8 do throwError "bool-lift case count mismatch: {count}"
  logInfo m!"BOOL LIFT FRONT END: {count} declarations, certified == legacy bytes, shipped module retained"

run_cmd liftTermElabM do
  let env ← getEnv
  let pred := instancePredicate env
  let inl := userInliner env
  for (name, valueName) in [(``bBusy, ``bBusyEntry)] do
    let some v := (entryConst true false [] (← getConstInfo name) pred inl (userProjection? env)).value?
      | throwError "{name} has no entry value"
    let .ok r := Tools.ShippingEntrySoundness.reflExpr v
      | throwError "{name}: entry value is not reflectable"
    unless (← getConstInfo valueName).value? == some r do
      throwError "{valueName} is not the entry constant of {name}"
  let ci ← getConstInfo ``bDeep
  unless (mixedCertifiedShape? false [] (entryConst true false [] ci pred inl (userProjection? env)) pred).isNone do
    throwError "a three-level body passed the gate"

run_cmd do
  if (← get).messages.hasErrors then throwError "bool-lift regression failed"
  for name in [``Tools.ShippingUnifiedRecursion.appBool2_contract,
      ``Tools.ShippingUnifiedMeaning.view_appBool2,
      ``Tools.ShippingTypedExprSoundness.typedExpr_printed,
      ``Tools.ShippingPrintSoundness.emitExpr_render_all,
      ``Tools.ShippingUnifiedProtection.fuel_orders,
      ``bBusy_library, ``bBusy_execution] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected bool-lift axiom: {name}: {ax}"
  logInfo "BOOL LIFT ENDPOINTS: unary NOT through the typed, printed and grammar layers; the busy flag of a bit-serial engine source to RTL; standard axioms only"

end Sparkle.Tests.Compiler.ShippingBoolLiftSoundnessTest

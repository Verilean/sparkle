import Tools.ShippingInlineSoundness
import Tests.Compiler.ShippingMixedExecutionTest

/-! Two map idioms of the IP library at the real entry.

`a.map (fun v => BitVec.append (0#k) v)` — zero-extension by a literal prefix
— lowers exactly like the zero-extending width cast, `{k'd0, a}`. A slice
written `f <$> a` lowers like the slice map, under the legacy `Functor.map`
handler's child hint. The front end also folds a literal `Nat` difference, so
`BitVec.extractLsb' (32 - 8) 8` is the slice at start 24. The tests check byte
parity with the legacy compile and prove widen-add-narrow — both idioms and an
adder between them — end to end. -/
namespace Sparkle.Tests.Compiler.ShippingMapFormsSoundnessTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingUnifiedSource
open Tools.ShippingMixedSourceBridge Tools.ShippingMixedExecutionSoundness
open Tools.ShippingInlineSoundness

/-! ## Shapes -/

section
variable {dom : DomainConfig}
def zPad (a : Signal dom (BitVec 8)) : Signal dom (BitVec 10) :=
  a.map (fun v => BitVec.append (0#2) v)
def zCone (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 12) :=
  (a + b).map (fun v => BitVec.append (0#4) v)
def zSum (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 9) :=
  a.map (fun v => BitVec.append (0#1) v) + b.map (fun v => BitVec.append (0#1) v)
def fLow (a : Signal dom (BitVec 8)) : Signal dom (BitVec 4) :=
  (fun x => BitVec.extractLsb' 0 4 x) <$> a
def fDot (a : Signal dom (BitVec 8)) : Signal dom (BitVec 4) :=
  (BitVec.extractLsb' 4 4 ·) <$> a
def fCone (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 4) :=
  (BitVec.extractLsb' 2 4 ·) <$> (a + b)
/-- The start written as a difference: the front end folds it to 24. -/
def sSub (a : Signal dom (BitVec 32)) : Signal dom (BitVec 8) :=
  a.map (BitVec.extractLsb' (32 - 8) 8 ·)
/-- Widen, add, narrow: the carry-free sum of two bytes through nine bits. -/
def zNarrow (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun x => BitVec.extractLsb' 0 8 x) <$>
    (a.map (fun v => BitVec.append (0#1) v) + b.map (fun v => BitVec.append (0#1) v))
/-- A non-zero literal prefix is not a zero-extension: legacy route. -/
def zOnes (a : Signal dom (BitVec 8)) : Signal dom (BitVec 10) :=
  a.map (fun v => BitVec.append (3#2) v)
end
def zConcrete (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 10) :=
  a.map (fun v => BitVec.append (0#2) v)

/-! ## Widen, add, narrow — end to end -/

def zNarrowTerm : Term (.bits 8) :=
  .sliceF `x 0 8 (.binary .add (.zextMap `v 1 (.bitsInput 8 0)) (.zextMap `v 1 (.bitsInput 8 1)))

theorem zNarrowTerm_wf : zNarrowTerm.WF 0 2 (fun _ => 8) := by
  refine ⟨⟨⟨⟨by omega, rfl, by omega⟩, by omega⟩, ⟨⟨by omega, rfl, by omega⟩, by omega⟩⟩,
    by omega, by omega⟩

theorem zNarrow_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    denote bi vi zNarrowTerm = zNarrow (vi 0 8) (vi 1 8) := rfl

#def_entry_value zNarrowEntry of zNarrow
def zNarrowBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`a, .bits 8), (`b, .bits 8)]
theorem zNarrow_peel : mixedGatePeel zNarrowEntry = some (zNarrowBinders,
    quote (.bvar 2) (fun _ => inputExpr zNarrowBinders.length 1)
      (fun j => inputExpr zNarrowBinders.length (j + 1)) zNarrowTerm) := rfl

/-- **Source-to-RTL execution of widen-add-narrow.** -/
theorem zNarrow_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``zNarrow) mctx mref cctx cref w (m, design) w')
    (entry : EntryDefines mctx mref cctx cref ``zNarrow zNarrowEntry) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = zNarrowBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``zNarrow zNarrowBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems ((zNarrow (bits 1 8) (bits 2 8)).val tick).toNat := by
  apply execution_source_of_entry (kb := 0) (kv := 2) (vw := fun _ => 8)
    (bpos := fun _ => 1) (vpos := fun j => j + 1) hr entry
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) zNarrow_peel zNarrowTerm_wf
  · intro j hj; omega
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩

/-! ## Runtime gates on the real compiler -/

run_cmd liftTermElabM do
  let env ← getEnv
  let pred := instancePredicate env
  let inl := userInliner env
  let translate : TranslateFn := fun e h t n => translateExprToWire e h t n
  let mut count := 0
  for name in [``zPad, ``zCone, ``zSum, ``fLow, ``fDot, ``fCone, ``sSub, ``zNarrow,
      ``zConcrete] do
    let ci ← getConstInfo name
    let ec := entryConst true false [] ci pred inl (userProjection? env)
    unless (mixedCertifiedShape? false [] ec pred).isSome do
      throwError "{name}: no gate accepts the declaration"
    let (mc, dc) ← synthesizeCombinationalCore name [] false
    let (ml, dl) ← synthesizeCombinationalCoreWith translate name [] false
      (certifiedFrontEnd := false)
    unless mc.body == ml.body && mc.inputs == ml.inputs && mc.outputs == ml.outputs &&
        mc.wires == ml.wires && mc.name == ml.name && dc.modules == dl.modules do
      throwError "{name}: the certified compile departed from the legacy compile\n{repr mc.body}\n{repr ml.body}"
    count := count + 1
  unless count == 9 do throwError "map-form case count mismatch: {count}"
  logInfo m!"MAP FORMS FRONT END: {count} declarations, certified == legacy bytes"

run_cmd liftTermElabM do
  let env ← getEnv
  let pred := instancePredicate env
  let inl := userInliner env
  for (name, valueName) in [(``zNarrow, ``zNarrowEntry)] do
    let some v := (entryConst true false [] (← getConstInfo name) pred inl (userProjection? env)).value?
      | throwError "{name} has no entry value"
    let .ok r := Tools.ShippingEntrySoundness.reflExpr v
      | throwError "{name}: entry value is not reflectable"
    unless (← getConstInfo valueName).value? == some r do
      throwError "{valueName} is not the entry constant of {name}"
  -- A non-zero prefix is not the zero-extension; it keeps the legacy route.
  let ci ← getConstInfo ``zOnes
  unless (mixedCertifiedShape? false [] (entryConst true false [] ci pred inl (userProjection? env)) pred).isNone do
    throwError "a non-zero literal prefix passed the gate"

run_cmd do
  if (← get).messages.hasErrors then throwError "map-form regression failed"
  for name in [``Tools.ShippingUnifiedRecursion.zextMap_contract,
      ``Tools.ShippingUnifiedRecursion.sliceF_contract,
      ``Tools.ShippingUnifiedMeaning.view_zextMap, ``Tools.ShippingUnifiedMeaning.view_sliceF,
      ``Tools.ShippingUnifiedProtection.fuel_orders,
      ``zNarrow_library, ``zNarrow_execution] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected map-form axiom: {name}: {ax}"
  logInfo "MAP FORMS ENDPOINTS: the literal-prefix zero-extension and the `<$>` slice; widen-add-narrow source to RTL; standard axioms only"

end Sparkle.Tests.Compiler.ShippingMapFormsSoundnessTest

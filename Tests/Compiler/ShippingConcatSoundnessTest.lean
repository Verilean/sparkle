import Tools.ShippingInlineSoundness
import Tests.Compiler.ShippingMixedExecutionTest

/-! Concatenation at the real entry.

`a ++ b` of two Signals lowers to ONE assignment `{hi, lo}`, with the result
wire allocated before the operands as the legacy handler does. A literal
operand (`v#k ++ b`, `a ++ v#k`) lowers the same way with the literal on a
constant wire of its own, allocated where the operand would be lowered. The IR
concatenation of two references is a right-hand-side shape of the whole back
half and a constructor of the unified source `Term`.

The result type of `a ++ b` is `BitVec (m + n)`: the elaborator writes the
SUM, and every parent's type arguments then carry it. The front end folds
literal `Nat` sums (`inlFoldNat`), so the entry constant has literal widths
everywhere. The tests check byte parity with the legacy compile of the
declaration AS WRITTEN, that the shipped module is the proved one, and prove a
nibble swap — two slices concatenated — end to end. -/
namespace Sparkle.Tests.Compiler.ShippingConcatSoundnessTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingUnifiedSource
open Tools.ShippingMixedSourceBridge Tools.ShippingMixedExecutionSoundness
open Tools.ShippingInlineSoundness
open Tools.ShippingMuxLoweringSoundness (encodeBool)

/-! ## Shapes -/

section
variable {dom : DomainConfig}
def cPair (a : Signal dom (BitVec 8)) (b : Signal dom (BitVec 4)) : Signal dom (BitVec 12) :=
  a ++ b
/-- No ascription: the declared result type itself is `BitVec (8 + 4)`. -/
def cInferred (a : Signal dom (BitVec 8)) (b : Signal dom (BitVec 4)) := a ++ b
/-- A parent of the concatenation: its operator instance is at width `8 + 8`. -/
def cSum (a b : Signal dom (BitVec 8)) (c : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  (a ++ b) + c
/-- Nested: the inner width `8 + 8` is an operand width of the outer one. -/
def cTriple (a b c : Signal dom (BitVec 8)) : Signal dom (BitVec 24) :=
  a ++ b ++ c
def cSlice (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (a ++ b).map (BitVec.extractLsb' 4 8 ·)
def cCmp (a b : Signal dom (BitVec 8)) (c : Signal dom (BitVec 16)) : Signal dom Bool :=
  Signal.beq (a ++ b) c
def cCone (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 16) :=
  (a + b) ++ (a ^^^ b)
/-- The same concatenation twice: the second is a cache hit. -/
def cShare (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 32) :=
  (a ++ b) ++ (a ++ b)
def cMux (s : Signal dom Bool) (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 16) :=
  Signal.mux s (a ++ b) (b ++ a)
/-- Two slices concatenated: the nibbles of a byte, swapped. -/
def cSwap (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  a.map (fun x => BitVec.extractLsb' 0 4 x) ++ a.map (fun x => BitVec.extractLsb' 4 4 x)
/-- Zero-extension by a literal prefix: the widening idiom of the IP library.
The lowering puts the literal on a `concat_const` wire of its own. -/
def cZext (a : Signal dom (BitVec 8)) : Signal dom (BitVec 12) :=
  (0#4 : BitVec 4) ++ a
/-- A literal suffix: a left shift by a constant. -/
def cShl (a : Signal dom (BitVec 8)) : Signal dom (BitVec 12) :=
  a ++ 3#4
def cPad (a : Signal dom (BitVec 8)) : Signal dom (BitVec 20) :=
  0#4 ++ a ++ 0#8
/-- The same literal prefix twice: two constant wires, as the legacy emits. -/
def cWide (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 9) :=
  (0#1 ++ a) + (0#1 ++ b)
/-- A numeral literal operand is not the canonical `v#k`: legacy route. -/
def cNumeral (a : Signal dom (BitVec 8)) : Signal dom (BitVec 12) :=
  (5 : BitVec 4) ++ a
end
def cConcrete (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 16) :=
  a ++ b

/-! ## The nibble swap, end to end -/

def cSwapTerm : Term (.bits 8) :=
  .concat (.slice `x 0 4 (.bitsInput 8 0)) (.slice `x 4 4 (.bitsInput 8 0))

theorem cSwapTerm_wf : cSwapTerm.WF 0 1 (fun _ => 8) := by
  refine ⟨⟨⟨by omega, rfl, by omega⟩, by omega, by omega⟩, ⟨⟨by omega, rfl, by omega⟩, by omega, by omega⟩⟩

/-- The kernel's own reading of `++` on Signals: the declaration IS the
denotation of the term. -/
theorem cSwap_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    denote bi vi cSwapTerm = cSwap (vi 0 8) := rfl

#def_entry_value cSwapEntry of cSwap
def cSwapBinders : List (Name × MixedGateBinder) := [(`dom, .domain), (`a, .bits 8)]
theorem cSwap_peel : mixedGatePeel cSwapEntry = some (cSwapBinders,
    quote (.bvar 1) (fun _ => inputExpr cSwapBinders.length 1)
      (fun j => inputExpr cSwapBinders.length (j + 1)) cSwapTerm) := rfl

/-- **Source-to-RTL execution of a concatenation of slices.** -/
theorem cSwap_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``cSwap) mctx mref cctx cref w (m, design) w')
    (entry : EntryDefines mctx mref cctx cref ``cSwap cSwapEntry) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = cSwapBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``cSwap cSwapBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems ((cSwap (bits 1 8)).val tick).toNat := by
  apply execution_source_of_entry (kb := 0) (kv := 1) (vw := fun _ => 8)
    (bpos := fun _ => 1) (vpos := fun j => j + 1) hr entry
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) cSwap_peel cSwapTerm_wf
  · intro j hj; omega
  · intro j hj
    have h : j = 0 := by omega
    subst h
    exact ⟨`a, rfl⟩

/-! ## A widened sum, end to end

`(0#1 ++ a) + (0#1 ++ b)`: the nine-bit sum of two bytes, the carry kept —
the first step of the LIN checksum of the IP library. -/

def cWideTerm : Term (.bits 9) :=
  .binary .add (.concatLitHi 1 0 (.bitsInput 8 0)) (.concatLitHi 1 0 (.bitsInput 8 1))

theorem cWideTerm_wf : cWideTerm.WF 0 2 (fun _ => 8) := by
  refine ⟨⟨⟨by omega, rfl, by omega⟩, by omega, by decide⟩,
    ⟨⟨by omega, rfl, by omega⟩, by omega, by decide⟩⟩

theorem cWide_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    denote bi vi cWideTerm = cWide (vi 0 8) (vi 1 8) := rfl

#def_entry_value cWideEntry of cWide
def cWideBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`a, .bits 8), (`b, .bits 8)]
theorem cWide_peel : mixedGatePeel cWideEntry = some (cWideBinders,
    quote (.bvar 2) (fun _ => inputExpr cWideBinders.length 1)
      (fun j => inputExpr cWideBinders.length (j + 1)) cWideTerm) := rfl

/-- **Source-to-RTL execution of a sum over literal-prefixed operands.** -/
theorem cWide_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``cWide) mctx mref cctx cref w (m, design) w')
    (entry : EntryDefines mctx mref cctx cref ``cWide cWideEntry) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = cWideBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``cWide cWideBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems ((cWide (bits 1 8) (bits 2 8)).val tick).toNat := by
  apply execution_source_of_entry (kb := 0) (kv := 2) (vw := fun _ => 8)
    (bpos := fun _ => 1) (vpos := fun j => j + 1) hr entry
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) cWide_peel cWideTerm_wf
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
  for name in [``cPair, ``cInferred, ``cSum, ``cTriple, ``cSlice, ``cCmp, ``cCone, ``cShare, ``cMux,
      ``cSwap, ``cZext, ``cShl, ``cPad, ``cWide, ``cConcrete] do
    let ci ← getConstInfo name
    -- As written the result width is the sum `m + n`: no gate reads it.
    unless (mixedCertifiedShape? false [] ci pred).isNone do
      throwError "{name}: the declaration as written already passes a gate"
    let ec := entryConst true false [] ci pred inl (userProjection? env)
    unless (mixedCertifiedShape? false [] ec pred).isSome do
      throwError "{name}: no gate accepts the concatenation after folding"
    let (mc, dc) ← synthesizeCombinationalCore name [] false
    let (ml, dl) ← synthesizeCombinationalCoreWith translate name [] false
      (certifiedFrontEnd := false)
    unless mc.body == ml.body && mc.inputs == ml.inputs && mc.outputs == ml.outputs &&
        mc.wires == ml.wires && mc.name == ml.name && dc.modules == dl.modules do
      throwError "{name}: the certified compile departed from the legacy compile\n{repr mc.body}\n{repr ml.body}"
    let (mf, _) ← synthesizeCombinational name
    unless Sparkle.IR.OptCheck.checkedOptimize mf == mf do
      throwError "{name}: the shipped module is not the retained one"
    count := count + 1
  unless count == 15 do throwError "concat case count mismatch: {count}"
  logInfo m!"CONCAT FRONT END: {count} declarations, certified == legacy bytes, shipped module retained"

run_cmd liftTermElabM do
  let env ← getEnv
  let pred := instancePredicate env
  let inl := userInliner env
  for (name, valueName) in [(``cSwap, ``cSwapEntry), (``cWide, ``cWideEntry)] do
    let some v := (entryConst true false [] (← getConstInfo name) pred inl (userProjection? env)).value?
      | throwError "{name} has no entry value"
    let .ok r := Tools.ShippingEntrySoundness.reflExpr v
      | throwError "{name}: entry value is not reflectable"
    unless (← getConstInfo valueName).value? == some r do
      throwError "{valueName} is not the entry constant of {name}"
  -- A numeral literal operand keeps the legacy mixed handler.
  let ci ← getConstInfo ``cNumeral
  unless (mixedCertifiedShape? false [] (entryConst true false [] ci pred inl (userProjection? env)) pred).isNone do
    throwError "a numeral-operand concatenation passed the gate"

run_cmd do
  if (← get).messages.hasErrors then throwError "concat regression failed"
  for name in [``Tools.ShippingUnifiedRecursion.concat_contract,
      ``Tools.ShippingUnifiedMeaning.view_concat,
      ``Tools.ShippingTypedExprSoundness.typedExpr_printed,
      ``Tools.ShippingPrintSoundness.emitExpr_render_all,
      ``Tools.ShippingUnifiedProtection.fuel_orders,
      ``Tools.ShippingUnifiedRecursion.concatLitHi_contract,
      ``Tools.ShippingUnifiedRecursion.concatLitLo_contract,
      ``cSwap_library, ``cSwap_execution, ``cWide_library, ``cWide_execution] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected concat axiom: {name}: {ax}"
  logInfo "CONCAT ENDPOINTS: `{a, b}` through the typed, printed and grammar layers; a nibble swap (two slices concatenated) and a sum over literal-prefixed operands source to RTL; standard axioms only"

end Sparkle.Tests.Compiler.ShippingConcatSoundnessTest

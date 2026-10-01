import Tools.ShippingInlineSoundness
import Tests.Compiler.ShippingMixedExecutionTest
import IP.Bus.CANopenHW

/-! Slices at the real entry.

`a.map (BitVec.extractLsb' start len ·)` lowers to ONE part-select assignment
`x[hi:lo]`. The part-select is a new right-hand-side shape for the whole back
half — simple shape, typed expression, printed text, concrete grammar, name
binding — and a new constructor of the unified source `Term`. The tests check
byte parity with the legacy compile on the real compiler, that the shipped
module of a slice design is the proved one, and prove two outputs of the
CANopen COB-ID demultiplexer of the IP library end to end. -/
namespace Sparkle.Tests.Compiler.ShippingSliceSoundnessTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingUnifiedSource
open Tools.ShippingMixedSourceBridge Tools.ShippingMixedExecutionSoundness
open Tools.ShippingInlineSoundness
open Tools.ShippingMuxLoweringSoundness (encodeBool)

/-! ## Shapes -/

section
variable {dom : DomainConfig}
def sField (a : Signal dom (BitVec 11)) : Signal dom (BitVec 4) :=
  a.map (BitVec.extractLsb' 7 4 ·)
/-- One bit: the result wire is a scalar `logic`. -/
def sBit (a : Signal dom (BitVec 11)) : Signal dom (BitVec 1) :=
  a.map (BitVec.extractLsb' 10 1 ·)
/-- The whole width: printed as the wire itself. -/
def sFull (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  a.map (BitVec.extractLsb' 0 8 ·)
def sCone (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 4) :=
  (a + b).map (BitVec.extractLsb' 2 4 ·)
def sTwice (a : Signal dom (BitVec 8)) : Signal dom (BitVec 4) :=
  a.map (BitVec.extractLsb' 0 4 ·) + a.map (BitVec.extractLsb' 4 4 ·)
def sCmp (a : Signal dom (BitVec 8)) : Signal dom Bool :=
  Signal.beq (a.map (BitVec.extractLsb' 4 4 ·)) (Signal.pure 3#4)
def sNested (a : Signal dom (BitVec 8)) : Signal dom (BitVec 2) :=
  (a.map (BitVec.extractLsb' 2 4 ·)).map (BitVec.extractLsb' 1 2 ·)
/-- A plain binder name. -/
def sNamed (a : Signal dom (BitVec 8)) : Signal dom (BitVec 4) :=
  a.map (fun x => BitVec.extractLsb' 4 4 x)
/-- Reaching past the source width is NOT the canonical slice: legacy route. -/
def sOver (a : Signal dom (BitVec 8)) : Signal dom (BitVec 4) :=
  a.map (BitVec.extractLsb' 6 4 ·)
end
def sConcrete (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 4) :=
  a.map (BitVec.extractLsb' 4 4 ·)

/-! ## The plain-binder slice, end to end -/

def sNamedTerm : Term (.bits 4) := .slice `x 4 4 (.bitsInput 8 0)

theorem sNamedTerm_wf : sNamedTerm.WF 0 1 (fun _ => 8) := by simp [sNamedTerm, Term.WF]

theorem sNamed_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    denote bi vi sNamedTerm = sNamed (vi 0 8) := rfl

#def_entry_value sNamedEntry of sNamed
def sNamedBinders : List (Name × MixedGateBinder) := [(`dom, .domain), (`a, .bits 8)]
theorem sNamed_peel : mixedGatePeel sNamedEntry = some (sNamedBinders,
    quote (.bvar 1) (fun _ => inputExpr sNamedBinders.length 1)
      (fun j => inputExpr sNamedBinders.length (j + 1)) sNamedTerm) := rfl

/-- **Source-to-RTL execution of a slice.** -/
theorem sNamed_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``sNamed) mctx mref cctx cref w (m, design) w')
    (entry : EntryDefines mctx mref cctx cref ``sNamed sNamedEntry) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = sNamedBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``sNamed sNamedBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems ((sNamed (bits 1 8)).val tick).toNat := by
  apply execution_source_of_entry (kb := 0) (kv := 1) (vw := fun _ => 8)
    (bpos := fun _ => 1) (vpos := fun j => j + 1) hr entry
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) sNamed_peel sNamedTerm_wf
  · intro j hj; omega
  · intro j hj
    have h : j = 0 := by omega
    subst h
    exact ⟨`a, rfl⟩

/-! ## A real IP module: the CANopen COB-ID demultiplexer -/

/-- The 4-bit function code of a COB-ID (`IP/Bus/CANopenHW.lean`). -/
def fcTop (cobId : Signal defaultDomain (BitVec 11)) : Signal defaultDomain (BitVec 4) :=
  (Sparkle.IP.Bus.CANopenHW.cobIdDemuxHW cobId).fc

/-- "This COB-ID is an NMT command": the function code is zero. -/
def isNmtTop (cobId : Signal defaultDomain (BitVec 11)) : Signal defaultDomain Bool :=
  (Sparkle.IP.Bus.CANopenHW.cobIdDemuxHW cobId).isNmt

#def_entry_value fcEntry of fcTop
#def_entry_lam_names fcNames of fcTop
#def_entry_value isNmtEntry of isNmtTop
#def_entry_lam_names isNmtNames of isNmtTop

/-- The slice's binder is a hygienic macro name of the IP source file; it is
read from the entry constant (`fcNames` lists the `fun` binders in order:
the input, then the slice lambda). The terms are proof data only, hence
`noncomputable` (compiling a definition over the reflected name list trips a
code-generator bug of this Lean version). -/
noncomputable def fcTerm : Term (.bits 4) :=
  .slice (fcNames.getD 1 .anonymous) 7 4 (.bitsInput 11 0)
noncomputable def isNmtTerm : Term .bool :=
  .compare .eq (.slice (isNmtNames.getD 1 .anonymous) 7 4 (.bitsInput 11 0)) (.bitsLit 4 0)

theorem fcTerm_wf : fcTerm.WF 0 1 (fun _ => 11) := by simp [fcTerm, Term.WF]
theorem isNmtTerm_wf : isNmtTerm.WF 0 1 (fun _ => 11) := by simp [isNmtTerm, Term.WF]

theorem fc_library (bi : Nat → Signal defaultDomain Bool)
    (vi : (j : Nat) → (w : Nat) → Signal defaultDomain (BitVec w)) :
    denote bi vi fcTerm = fcTop (vi 0 11) := rfl
theorem isNmt_library (bi : Nat → Signal defaultDomain Bool)
    (vi : (j : Nat) → (w : Nat) → Signal defaultDomain (BitVec w)) :
    denote bi vi isNmtTerm = isNmtTop (vi 0 11) := rfl

def demuxBinders : List (Name × MixedGateBinder) := [(`cobId, .bits 11)]
theorem fc_peel : mixedGatePeel fcEntry = some (demuxBinders,
    quote (.const ``Sparkle.Core.Domain.defaultDomain []) (fun _ => inputExpr demuxBinders.length 0)
      (fun j => inputExpr demuxBinders.length j) fcTerm) := rfl
theorem isNmt_peel : mixedGatePeel isNmtEntry = some (demuxBinders,
    quote (.const ``Sparkle.Core.Domain.defaultDomain []) (fun _ => inputExpr demuxBinders.length 0)
      (fun j => inputExpr demuxBinders.length j) isNmtTerm) := rfl

/-- **The CANopen function-code field, source to RTL.** -/
theorem fc_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``fcTop) mctx mref cctx cref w (m, design) w')
    (entry : EntryDefines mctx mref cctx cref ``fcTop fcEntry) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = demuxBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ (bools : Nat → Signal defaultDomain Bool)
        (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``fcTop demuxBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems ((fcTop (bits 0 11)).val tick).toNat := by
  obtain ⟨ids, nd, len, cache, H⟩ := execution_source_of_entry (kb := 0) (kv := 1)
    (vw := fun _ => 11) (bpos := fun _ => 0) (vpos := fun j => j) hr entry
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) fc_peel fcTerm_wf
    (by intro j hj; omega)
    (by
      intro j hj
      have h : j = 0 := by omega
      subst h
      exact ⟨`cobId, rfl⟩)
  exact ⟨ids, nd, len, cache, fun bools bits tick initial mems h =>
    H (D := defaultDomain) bools bits tick initial mems h⟩

/-- **The CANopen NMT decode, source to RTL.** -/
theorem isNmt_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``isNmtTop) mctx mref cctx cref w (m, design) w')
    (entry : EntryDefines mctx mref cctx cref ``isNmtTop isNmtEntry) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = demuxBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ (bools : Nat → Signal defaultDomain Bool)
        (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``isNmtTop demuxBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems (encodeBool ((isNmtTop (bits 0 11)).val tick)) := by
  obtain ⟨ids, nd, len, cache, H⟩ := execution_source_of_entry (kb := 0) (kv := 1)
    (vw := fun _ => 11) (bpos := fun _ => 0) (vpos := fun j => j) hr entry
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) isNmt_peel isNmtTerm_wf
    (by intro j hj; omega)
    (by
      intro j hj
      have h : j = 0 := by omega
      subst h
      exact ⟨`cobId, rfl⟩)
  exact ⟨ids, nd, len, cache, fun bools bits tick initial mems h =>
    H (D := defaultDomain) bools bits tick initial mems h⟩

/-! ## Runtime gates on the real compiler -/

run_cmd liftTermElabM do
  let env ← getEnv
  let pred := instancePredicate env
  let inl := userInliner env
  let translate : TranslateFn := fun e h t n => translateExprToWire e h t n
  let mut count := 0
  for name in [``sField, ``sBit, ``sFull, ``sCone, ``sTwice, ``sCmp, ``sNested, ``sNamed,
      ``sConcrete, ``fcTop, ``isNmtTop] do
    let ci ← getConstInfo name
    let ec := entryConst true false [] ci pred inl
    unless (mixedCertifiedShape? false [] ec pred).isSome do
      throwError "{name}: no gate accepts the slice declaration"
    let (mc, dc) ← synthesizeCombinationalCore name [] false
    let (ml, dl) ← synthesizeCombinationalCoreWith translate name [] false
      (certifiedFrontEnd := false)
    unless mc.body == ml.body && mc.inputs == ml.inputs && mc.outputs == ml.outputs &&
        mc.wires == ml.wires && mc.name == ml.name && dc.modules == dl.modules do
      throwError "{name}: the certified compile departed from the legacy compile"
    -- The shipped module of a slice design is the proved one: the optimizer's
    -- proposal is not validated on part-selects, so the module is retained.
    let (mf, _) ← synthesizeCombinational name
    unless Sparkle.IR.OptCheck.checkedOptimize mf == mf do
      throwError "{name}: the shipped module is not the retained one"
    count := count + 1
  unless count == 11 do throwError "slice case count mismatch: {count}"
  logInfo m!"SLICE FRONT END: {count} declarations, certified == legacy bytes, shipped module retained"

run_cmd liftTermElabM do
  let env ← getEnv
  let pred := instancePredicate env
  let inl := userInliner env
  for (name, valueName) in [(``sNamed, ``sNamedEntry), (``fcTop, ``fcEntry),
      (``isNmtTop, ``isNmtEntry)] do
    let some v := (entryConst true false [] (← getConstInfo name) pred inl).value?
      | throwError "{name} has no entry value"
    let .ok r := Tools.ShippingEntrySoundness.reflExpr v
      | throwError "{name}: entry value is not reflectable"
    unless (← getConstInfo valueName).value? == some r do
      throwError "{valueName} is not the entry constant of {name}"
  -- An out-of-range slice is not the canonical shape; it keeps the legacy route.
  let ci ← getConstInfo ``sOver
  unless (mixedCertifiedShape? false [] ci pred).isNone do
    throwError "an out-of-range slice passed the gate"

run_cmd do
  if (← get).messages.hasErrors then throwError "slice regression failed"
  for name in [``Tools.ShippingUnifiedRecursion.slice_contract,
      ``Tools.ShippingUnifiedMeaning.view_slice,
      ``Tools.ShippingTypedExprSoundness.typedExpr_printed,
      ``Tools.ShippingPrintSoundness.emitExpr_render_all,
      ``Tools.ShippingUnifiedProtection.fuel_orders,
      ``sNamed_library, ``sNamed_execution, ``fc_library, ``fc_execution,
      ``isNmt_library, ``isNmt_execution] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected slice axiom: {name}: {ax}"
  logInfo "SLICE ENDPOINTS: part-selects through the typed, printed and grammar layers; the CANopen COB-ID function code and NMT decode of the IP library; standard axioms only"

end Sparkle.Tests.Compiler.ShippingSliceSoundnessTest

import Tools.ShippingInlineSoundness
import Tests.Compiler.ShippingMixedExecutionTest
import Sparkle.Core.Lut
import IP.Crypto.AESHW

/-! Applicative-lifted Bool-result operators at the real entry.

`(BitVec.ule · ·) <$> a <*> b`, `(· == ·) <$> a <*> b`, `(· && ·) <$> a <*> b`
and the `kLut!` table mux built from them are the idiom of the IP library.
The front end normalises them to `Signal.ap (Signal.map f a) b`; the Bool
control arm lowers that form with the legacy applicative lowering's hints.
The tests check, on the real compiler, that the certified compile is
byte-identical to the legacy compile, and prove two declarations end to end:
a range check built from lifted comparisons, and the AES round-constant
table of the IP library. -/
namespace Sparkle.Tests.Compiler.ShippingApplicativeSoundnessTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingUnifiedSource
open Tools.ShippingMixedSourceBridge Tools.ShippingMixedExecutionSoundness
open Tools.ShippingInlineSoundness
open Tools.ShippingMuxLoweringSoundness (encodeBool)

/-! ## Shapes -/

section
variable {dom : DomainConfig}
def aEq (a b : Signal dom (BitVec 8)) : Signal dom Bool := (· == ·) <$> a <*> b
def aUle (a b : Signal dom (BitVec 8)) : Signal dom Bool := (BitVec.ule · ·) <$> a <*> b
def aUlt (a b : Signal dom (BitVec 8)) : Signal dom Bool := (BitVec.ult · ·) <$> a <*> b
def aSlt (a b : Signal dom (BitVec 8)) : Signal dom Bool := (BitVec.slt · ·) <$> a <*> b
def aSle (a b : Signal dom (BitVec 8)) : Signal dom Bool := (BitVec.sle · ·) <$> a <*> b
def aAnd (a b : Signal dom Bool) : Signal dom Bool := (· && ·) <$> a <*> b
def aOr (a b : Signal dom Bool) : Signal dom Bool := (· || ·) <$> a <*> b
def aXor (a b : Signal dom Bool) : Signal dom Bool := (· ^^ ·) <$> a <*> b
/-- A literal operand. -/
def aLit (a : Signal dom (BitVec 8)) : Signal dom Bool := (· == ·) <$> a <*> Signal.pure 3
/-- Cone operands. -/
def aCone (a b c : Signal dom (BitVec 8)) : Signal dom Bool :=
  (BitVec.ule · ·) <$> (a + b) <*> (b - c)
/-- Lifted operators as each other's operands. -/
def aNest (a b c : Signal dom (BitVec 8)) : Signal dom Bool :=
  (· && ·) <$> ((BitVec.ule · ·) <$> (a + b) <*> c) <*> ((· == ·) <$> a <*> Signal.pure 3)
/-- The table mux macro. -/
def aLut (i : Signal dom (BitVec 2)) : Signal dom (BitVec 8) :=
  kLut! i [Signal.pure 1#8, Signal.pure 2#8, Signal.pure 4#8, Signal.pure 8#8]
/-- The same lifted comparison twice: shared, as on the legacy route. -/
def aShare (a b c : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.mux ((BitVec.ule · ·) <$> a <*> b) (a + c)
    (Signal.mux ((BitVec.ule · ·) <$> a <*> b) c b)
def aShareBool (a b : Signal dom Bool) : Signal dom Bool :=
  (· || ·) <$> ((· && ·) <$> a <*> b) <*> ((· && ·) <$> a <*> b)
/-- NOT in the certified vocabulary (a three-level lambda body): stays legacy.
(The two-level bodies `s && !l`, `!s && l`, `!(s || l)` are certified — see
`ShippingBoolLiftSoundnessTest`.) -/
def aAndNot (a b : Signal dom Bool) : Signal dom Bool :=
  (fun s l => !(s && !l)) <$> a <*> b
end
def aConcrete (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain Bool :=
  (BitVec.ule · ·) <$> a <*> b

/-! ## A range check, end to end -/

/-- `lo ≤ x < hi`, written with lifted comparisons and a lifted conjunction. -/
def inRange {dom : DomainConfig} (lo hi x : Signal dom (BitVec 8)) : Signal dom Bool :=
  (· && ·) <$> ((BitVec.ule · ·) <$> lo <*> x) <*> ((BitVec.ult · ·) <$> x <*> hi)

def inRangeTerm : Term .bool :=
  .appBool .band (.appCompare .ule (.bitsInput 8 0) (.bitsInput 8 2))
    (.appCompare .ult (.bitsInput 8 2) (.bitsInput 8 1))

theorem inRangeTerm_wf : inRangeTerm.WF 0 3 (fun _ => 8) := by simp [inRangeTerm, Term.WF]

/-- The kernel's own unfolding of `<$>` / `<*>`: the declaration IS the
denotation of the term. -/
theorem inRange_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    denote bi vi inRangeTerm = inRange (vi 0 8) (vi 1 8) (vi 2 8) := rfl

#def_entry_value inRangeEntry of inRange
def inRangeBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`lo, .bits 8), (`hi, .bits 8), (`x, .bits 8)]
theorem inRange_peel : mixedGatePeel inRangeEntry = some (inRangeBinders,
    quote (.bvar 3) (fun _ => inputExpr inRangeBinders.length 1)
      (fun j => inputExpr inRangeBinders.length (j + 1)) inRangeTerm) := rfl

/-- **Source-to-RTL execution of applicative-lifted comparisons.** -/
theorem inRange_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``inRange) mctx mref cctx cref w (m, design) w')
    (entry : EntryDefines mctx mref cctx cref ``inRange inRangeEntry) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = inRangeBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``inRange inRangeBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems
        (encodeBool ((inRange (bits 1 8) (bits 2 8) (bits 3 8)).val tick)) := by
  apply execution_source_of_entry (kb := 0) (kv := 3) (vw := fun _ => 8)
    (bpos := fun _ => 1) (vpos := fun j => j + 1) hr entry
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) inRange_peel inRangeTerm_wf
  · intro j hj; omega
  · intro j hj
    have h : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases h with rfl | rfl | rfl
    · exact ⟨`lo, rfl⟩
    · exact ⟨`hi, rfl⟩
    · exact ⟨`x, rfl⟩

/-! ## A real IP module: the AES round-constant table -/

/-- The mux chain `kLut!` unrolls a table into: entry `k` is selected by the
lifted comparison `sel == k`; the last entry is the default. -/
def lutTerm : Nat → List Nat → Term (.bits 8)
  | _, [] => .bitsLit 8 0
  | _, [v] => .bitsLit 8 v
  | k, v :: rest =>
    .mux (.appCompare .eq (.bitsInput 4 0) (.bitsNum 4 k)) (.bitsLit 8 v) (lutTerm (k + 1) rest)

/-- The table of `Sparkle.IP.Crypto.AESHW.rconHW` (`IP/Crypto/AESHW.lean`). -/
def rconTable : List Nat :=
  [0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36, 0x00, 0x00, 0x00, 0x00, 0x00]

def rconTerm : Term (.bits 8) := lutTerm 0 rconTable

theorem rconTerm_wf : rconTerm.WF 0 1 (fun _ => 4) := by
  simp [rconTerm, rconTable, lutTerm, Term.WF]

/-- The IP definition IS the denotation of the table term (kernel `rfl`
through the `kLut!` expansion). -/
theorem rcon_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    denote bi vi rconTerm = Sparkle.IP.Crypto.AESHW.rconHW (vi 0 4) := rfl

#def_entry_value rconEntry of Sparkle.IP.Crypto.AESHW.rconHW
def rconBinders : List (Name × MixedGateBinder) := [(`dom, .domain), (`i, .bits 4)]
theorem rcon_peel : mixedGatePeel rconEntry = some (rconBinders,
    quote (.bvar 1) (fun _ => inputExpr rconBinders.length 1)
      (fun j => inputExpr rconBinders.length (j + 1)) rconTerm) := rfl

/-- **The AES round-constant table, source to RTL.** The module compiled
from the IP library's `rconHW` computes `rconHW`'s own output stream. -/
theorem rcon_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``Sparkle.IP.Crypto.AESHW.rconHW) mctx mref cctx cref w
      (m, design) w')
    (entry : EntryDefines mctx mref cctx cref ``Sparkle.IP.Crypto.AESHW.rconHW rconEntry) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = rconBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``Sparkle.IP.Crypto.AESHW.rconHW rconBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems
        ((Sparkle.IP.Crypto.AESHW.rconHW (bits 1 4)).val tick).toNat := by
  apply execution_source_of_entry (kb := 0) (kv := 1) (vw := fun _ => 4)
    (bpos := fun _ => 1) (vpos := fun j => j + 1) hr entry
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) rcon_peel rconTerm_wf
  · intro j hj; omega
  · intro j hj
    have h : j = 0 := by omega
    subst h
    exact ⟨`i, rfl⟩

/-! ## Runtime gates on the real compiler -/

run_cmd liftTermElabM do
  let env ← getEnv
  let pred := instancePredicate env
  let inl := userInliner env
  let translate : TranslateFn := fun e h t n => translateExprToWire e h t n
  let mut count := 0
  for name in [``aEq, ``aUle, ``aUlt, ``aSlt, ``aSle, ``aAnd, ``aOr, ``aXor, ``aLit, ``aCone,
      ``aNest, ``aLut, ``aShare, ``aShareBool, ``aConcrete, ``inRange,
      ``Sparkle.IP.Crypto.AESHW.rconHW, ``Sparkle.IP.Crypto.AESHW.sboxHW] do
    let ci ← getConstInfo name
    unless (certifiedShape? false [] ci).isNone && (mixedCertifiedShape? false [] ci pred).isNone do
      throwError "{name}: an applicative declaration passed a gate as written"
    let ec := entryConst true false [] ci pred inl (structEnv env)
    unless ec.value? != ci.value? do throwError "{name}: the entry constant is the original"
    unless (mixedCertifiedShape? false [] ec pred).isSome do
      throwError "{name}: no gate accepts the normalised declaration"
    let (mc, dc) ← synthesizeCombinationalCore name [] false
    let (ml, dl) ← synthesizeCombinationalCoreWith translate name [] false
      (certifiedFrontEnd := false)
    unless mc.body == ml.body && mc.inputs == ml.inputs && mc.outputs == ml.outputs &&
        mc.wires == ml.wires && mc.name == ml.name && dc.modules == dl.modules do
      throwError "{name}: the certified compile departed from the legacy compile"
    count := count + 1
  unless count == 18 do throwError "applicative case count mismatch: {count}"
  logInfo m!"APPLICATIVE FRONT END: {count} declarations normalised, certified == legacy bytes"

run_cmd liftTermElabM do
  let env ← getEnv
  let pred := instancePredicate env
  let inl := userInliner env
  for (name, valueName) in [(``inRange, ``inRangeEntry),
      (``Sparkle.IP.Crypto.AESHW.rconHW, ``rconEntry)] do
    let some v := (entryConst true false [] (← getConstInfo name) pred inl (structEnv env)).value?
      | throwError "{name} has no entry value"
    let .ok r := Tools.ShippingEntrySoundness.reflExpr v
      | throwError "{name}: entry value is not reflectable"
    unless (← getConstInfo valueName).value? == some r do
      throwError "{valueName} is not the entry constant of {name}"
  -- A lambda body outside the certified vocabulary keeps the legacy route.
  let ci ← getConstInfo ``aAndNot
  unless (entryConst true false [] ci pred inl (structEnv env)).value? == ci.value? do
    throwError "aAndNot was rewritten"
  let (m, _) ← synthesizeCombinationalCore ``aAndNot [] false
  let (ml, _) ← synthesizeCombinationalCoreWith
    (fun e h t n => translateExprToWire e h t n) ``aAndNot [] false (certifiedFrontEnd := false)
  unless m.body == ml.body && m.wires == ml.wires do
    throwError "aAndNot: default and legacy compiles differ"

run_cmd do
  if (← get).messages.hasErrors then throwError "applicative regression failed"
  for name in [``Tools.ShippingUnifiedRecursion.appCompare_contract,
      ``Tools.ShippingUnifiedRecursion.appBool_contract,
      ``Tools.ShippingUnifiedMeaning.view_appCompare,
      ``Tools.ShippingUnifiedMeaning.view_appBool,
      ``Tools.ShippingUnifiedProtection.fuel_orders,
      ``Tools.ShippingInlineSoundness.execution_source_of_entry,
      ``inRange_library, ``inRange_execution, ``rcon_library, ``rcon_execution] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected applicative axiom: {name}: {ax}"
  logInfo "APPLICATIVE ENDPOINTS: lifted comparisons and Bool operators, and the AES round-constant table of the IP library; standard axioms only"

end Sparkle.Tests.Compiler.ShippingApplicativeSoundnessTest

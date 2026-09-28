import Tools.ShippingUnifiedExecutionSoundness
import Tests.Compiler.ShippingMixedExecutionTest

/-! Source/cache foundation tests. Compilation comparisons below are regression
witnesses for existing success paths, NOT new source-to-RTL theorems. -/
namespace Sparkle.Tests.Compiler.ShippingUnifiedSourceTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingBoolSourceSoundness
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMixedSourceBridge Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMixedExecutionSoundness Tools.ShippingUnifiedExecutionSoundness

-- All of these already compile on the existing fallback path.
def arithmetic1 {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 1)) := Signal.mux c a b + a
def arithmetic8 {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) := Signal.mux c a b + a
def arithmetic65 {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 65)) := Signal.mux c a b + a
def comparison {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.ult (Signal.mux c a b + a) (Signal.mux c b a)
def nested {dom : DomainConfig} (c d : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.mux (Signal.beq (Signal.mux c a b) (a + b))
    (Signal.mux (Signal.ult (Signal.mux d a b + a) b) (a * b) b)
    (Signal.mux c a b - Signal.mux d b a)

def arithmeticTerm (w : Nat) : Term (.bits w) := .binary .add
  (.mux (.boolInput 0) (.bitsInput w 0) (.bitsInput w 1)) (.bitsInput w 0)
def comparisonTerm (w : Nat) : Term .bool := .compare .ult (arithmeticTerm w)
  (.mux (.boolInput 0) (.bitsInput w 1) (.bitsInput w 0))
def nestedTerm (w : Nat) : Term (.bits w) := .mux
  (.compare .eq (.mux (.boolInput 0) (.bitsInput w 0) (.bitsInput w 1))
    (.binary .add (.bitsInput w 0) (.bitsInput w 1)))
  (.mux (.compare .ult
    (.binary .add (.mux (.boolInput 1) (.bitsInput w 0) (.bitsInput w 1)) (.bitsInput w 0))
    (.bitsInput w 1)) (.binary .mul (.bitsInput w 0) (.bitsInput w 1)) (.bitsInput w 1))
  (.binary .sub (.mux (.boolInput 0) (.bitsInput w 0) (.bitsInput w 1))
    (.mux (.boolInput 1) (.bitsInput w 1) (.bitsInput w 0)))

theorem nested_wf (w : Nat) (hw : 0 < w) : (nestedTerm w).WF 2 2 (fun _ => w) := by
  simp [nestedTerm, Term.WF, hw]

theorem arithmetic_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    denote bi vi (arithmeticTerm 8) = arithmetic8 (bi 0) (vi 0 8) (vi 1 8) := rfl
theorem comparison_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    denote bi vi (comparisonTerm 8) = comparison (bi 0) (vi 0 8) (vi 1 8) := rfl
theorem nested_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    denote bi vi (nestedTerm 8) = nested (bi 0) (bi 1) (vi 0 8) (vi 1 8) := rfl

#def_decl_value nestedValue of nested
def binders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`d, .bool), (`a, .bits 8), (`b, .bits 8)]
theorem nested_peel : mixedGatePeel nestedValue = some (binders,
    quote (.bvar 4) (fun j => inputExpr binders.length (j + 1))
      (fun j => inputExpr binders.length (j + 3)) (nestedTerm 8)) := rfl

/-- Quoted real source, at arbitrary Signal observations, has the unified
meaning required by the new cache invariant. No compiler run is claimed here. -/
theorem nested_meaning {inputs : FVarId → Option Value} {dom : Lean.Expr}
    {bi vi : Nat → FVarId} {D : DomainConfig}
    (bools : Nat → Signal D Bool) (bits : (j : Nat) → (w : Nat) → Signal D (BitVec w)) (tick : Nat)
    (hb : ∀ j, j < 2 → inputs (bi j) = some (.bool ((bools j).val tick)))
    (hv : ∀ j, j < 2 → inputs (vi j) = some (.bits 8 ((bits j 8).val tick))) :
    Meaning inputs (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) (nestedTerm 8))
      (.bits 8 ((nested (bools 0) (bools 1) (bits 0 8) (bits 1 8)).val tick)) := by
  have meaning := meaning_quote (dom := dom) (vw := fun _ => 8)
    (bits := fun j w => (bits j w).val tick) hb hv (nestedTerm 8) (nested_wf 8 (by decide))
  rw [← denote_val bools (fun j w => bits j w) tick, nested_library] at meaning
  exact meaning

#def_decl_value comparisonValue of comparison
def comparisonBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`a, .bits 8), (`b, .bits 8)]
theorem comparison_peel : mixedGatePeel comparisonValue = some (comparisonBinders,
    quote (.bvar 3) (fun _ => inputExpr comparisonBinders.length 1)
      (fun j => inputExpr comparisonBinders.length (j + 2)) (comparisonTerm 8)) := rfl

#def_decl_value arithmetic65Value of arithmetic65
def arithmetic65Binders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`a, .bits 65), (`b, .bits 65)]
theorem arithmetic65_peel : mixedGatePeel arithmetic65Value = some (arithmetic65Binders,
    quote (.bvar 3) (fun _ => inputExpr arithmetic65Binders.length 1)
      (fun j => inputExpr arithmetic65Binders.length (j + 2)) (arithmeticTerm 65)) := rfl

/-- The general unified endpoint instantiates on the real declaration whose
mux trees sit under arithmetic, comparison and mux conditions at once. -/
theorem nested_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``nested) mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref ``nested nestedValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = binders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``nested binders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems
        ((nested (bools 1) (bools 2) (bits 3 8) (bits 4 8)).val tick).toNat := by
  apply Tools.ShippingUnifiedExecutionSoundness.execution_source_of_env hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) nested_peel (nested_wf 8 (by decide))
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`c, rfl⟩
    · exact ⟨`d, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩

/-- Bool-result composition through the same endpoint: a comparison whose
operands contain vector muxes. -/
theorem comparison_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``comparison) mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref ``comparison comparisonValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = comparisonBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``comparison comparisonBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems
        (encodeBool ((comparison (bools 1) (bits 2 8) (bits 3 8)).val tick)) := by
  apply Tools.ShippingUnifiedExecutionSoundness.execution_source_of_env (kb := 1) (kv := 2)
    (vw := fun _ => 8) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) comparison_peel
    (by simp [comparisonTerm, arithmeticTerm, Term.WF])
  · intro j hj
    have h : j = 0 := by omega
    subst h
    exact ⟨`c, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩

/-- Arithmetic root above a vector mux at a nonuniform width. -/
theorem arithmetic65_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``arithmetic65) mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref ``arithmetic65 arithmetic65Value) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = arithmetic65Binders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``arithmetic65 arithmetic65Binders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems
        ((arithmetic65 (bools 1) (bits 2 65) (bits 3 65)).val tick).toNat := by
  apply Tools.ShippingUnifiedExecutionSoundness.execution_source_of_env (kb := 1) (kv := 2)
    (vw := fun _ => 65) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) arithmetic65_peel
    (by simp [arithmeticTerm, Term.WF])
  · intro j hj
    have h : j = 0 := by omega
    subst h
    exact ⟨`c, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩

-- A genuinely mixed-width source: an 8-bit comparison controls a 65-bit mux
-- whose branches are 65-bit arithmetic and another mux.
def mixedWidth {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8))
    (x y : Signal dom (BitVec 65)) :=
  Signal.mux ((Signal.ult a b) &&& c) (x + y) (Signal.mux c y x)
#def_decl_value mixedWidthValue of mixedWidth
def mixedWidthBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`a, .bits 8), (`b, .bits 8), (`x, .bits 65), (`y, .bits 65)]
def mixedVW : Nat → Nat := fun j => if j < 2 then 8 else 65
def mixedWidthTerm : Term (.bits 65) := .mux
  (.boolBinary .band (.compare .ult (.bitsInput 8 0) (.bitsInput 8 1)) (.boolInput 0))
  (.binary .add (.bitsInput 65 2) (.bitsInput 65 3))
  (.mux (.boolInput 0) (.bitsInput 65 3) (.bitsInput 65 2))
theorem mixedWidth_wf : mixedWidthTerm.WF 1 4 mixedVW := by
  simp [mixedWidthTerm, Term.WF, mixedVW]
theorem mixedWidth_peel : mixedGatePeel mixedWidthValue = some (mixedWidthBinders,
    quote (.bvar 5) (fun _ => inputExpr mixedWidthBinders.length 1)
      (fun j => inputExpr mixedWidthBinders.length (j + 2)) mixedWidthTerm) := rfl
theorem mixedWidth_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    denote bi vi mixedWidthTerm = mixedWidth (bi 0) (vi 0 8) (vi 1 8) (vi 2 65) (vi 3 65) := rfl

/-- The unified endpoint on a real declaration whose subtrees use different
positive widths: the 65-bit result is controlled by an 8-bit comparison. -/
theorem mixedWidth_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``mixedWidth) mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref ``mixedWidth mixedWidthValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = mixedWidthBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``mixedWidth mixedWidthBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems
        ((mixedWidth (bools 1) (bits 2 8) (bits 3 8) (bits 4 65) (bits 5 65)).val tick).toNat := by
  apply Tools.ShippingUnifiedExecutionSoundness.execution_source_of_env (kb := 1) (kv := 4)
    (vw := mixedVW) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) mixedWidth_peel mixedWidth_wf
  · intro j hj
    have h : j = 0 := by omega
    subst h
    exact ⟨`c, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩
    · exact ⟨`x, rfl⟩
    · exact ⟨`y, rfl⟩

-- Width-changing sources through the canonical `Signal.map (BitVec.setWidth w)`
-- form: zero-extension, truncation, an equal-width cast, and a widened operand
-- under an arithmetic parent.
def widen {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.map (BitVec.setWidth 16) (Signal.mux c a b + a)
def narrow {dom : DomainConfig} (c : Signal dom Bool) (x y : Signal dom (BitVec 65)) :=
  Signal.map (BitVec.setWidth 8) (Signal.mux c x y + x)
def rewidth {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.map (BitVec.setWidth 8) (Signal.mux c a b)
def widenAdd {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8))
    (x : Signal dom (BitVec 16)) :=
  Signal.map (BitVec.setWidth 16) (Signal.mux c a b) + x

def widenTerm : Term (.bits 16) := .setw 16 (.binary .add
  (.mux (.boolInput 0) (.bitsInput 8 0) (.bitsInput 8 1)) (.bitsInput 8 0))
def narrowTerm : Term (.bits 8) := .setw 8 (.binary .add
  (.mux (.boolInput 0) (.bitsInput 65 0) (.bitsInput 65 1)) (.bitsInput 65 0))
def rewidthTerm : Term (.bits 8) := .setw 8
  (.mux (.boolInput 0) (.bitsInput 8 0) (.bitsInput 8 1))
def widenAddVW : Nat → Nat := fun j => if j < 2 then 8 else 16
def widenAddTerm : Term (.bits 16) := .binary .add
  (.setw 16 (.mux (.boolInput 0) (.bitsInput 8 0) (.bitsInput 8 1))) (.bitsInput 16 2)

theorem widen_wf : widenTerm.WF 1 2 (fun _ => 8) := by simp [widenTerm, Term.WF]
theorem narrow_wf : narrowTerm.WF 1 2 (fun _ => 65) := by simp [narrowTerm, Term.WF]
theorem widenAdd_wf : widenAddTerm.WF 1 3 widenAddVW := by
  simp [widenAddTerm, Term.WF, widenAddVW]

theorem widen_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    denote bi vi widenTerm = widen (bi 0) (vi 0 8) (vi 1 8) := rfl
theorem narrow_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    denote bi vi narrowTerm = narrow (bi 0) (vi 0 65) (vi 1 65) := rfl
theorem widenAdd_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    denote bi vi widenAddTerm = widenAdd (bi 0) (vi 0 8) (vi 1 8) (vi 2 16) := rfl

#def_decl_value widenValue of widen
def widenBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`a, .bits 8), (`b, .bits 8)]
theorem widen_peel : mixedGatePeel widenValue = some (widenBinders,
    quote (.bvar 3) (fun _ => inputExpr widenBinders.length 1)
      (fun j => inputExpr widenBinders.length (j + 2)) widenTerm) := rfl

#def_decl_value narrowValue of narrow
def narrowBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`x, .bits 65), (`y, .bits 65)]
theorem narrow_peel : mixedGatePeel narrowValue = some (narrowBinders,
    quote (.bvar 3) (fun _ => inputExpr narrowBinders.length 1)
      (fun j => inputExpr narrowBinders.length (j + 2)) narrowTerm) := rfl

#def_decl_value widenAddValue of widenAdd
def widenAddBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`a, .bits 8), (`b, .bits 8), (`x, .bits 16)]
theorem widenAdd_peel : mixedGatePeel widenAddValue = some (widenAddBinders,
    quote (.bvar 4) (fun _ => inputExpr widenAddBinders.length 1)
      (fun j => inputExpr widenAddBinders.length (j + 2)) widenAddTerm) := rfl

/-- The unified endpoint on a real zero-extension root: a 16-bit result from
8-bit mux/arithmetic children. -/
theorem widen_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``widen) mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref ``widen widenValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = widenBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``widen widenBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems
        ((widen (bools 1) (bits 2 8) (bits 3 8)).val tick).toNat := by
  apply Tools.ShippingUnifiedExecutionSoundness.execution_source_of_env (kb := 1) (kv := 2)
    (vw := fun _ => 8) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) widen_peel widen_wf
  · intro j hj
    have h : j = 0 := by omega
    subst h
    exact ⟨`c, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩

/-- The unified endpoint on a real truncation root: an 8-bit result from
65-bit mux/arithmetic children. -/
theorem narrow_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``narrow) mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref ``narrow narrowValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = narrowBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``narrow narrowBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems
        ((narrow (bools 1) (bits 2 65) (bits 3 65)).val tick).toNat := by
  apply Tools.ShippingUnifiedExecutionSoundness.execution_source_of_env (kb := 1) (kv := 2)
    (vw := fun _ => 65) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) narrow_peel narrow_wf
  · intro j hj
    have h : j = 0 := by omega
    subst h
    exact ⟨`c, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`x, rfl⟩
    · exact ⟨`y, rfl⟩

/-- The unified endpoint with a widened operand under an arithmetic parent
at mixed widths. -/
theorem widenAdd_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``widenAdd) mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref ``widenAdd widenAddValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = widenAddBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``widenAdd widenAddBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems
        ((widenAdd (bools 1) (bits 2 8) (bits 3 8) (bits 4 16)).val tick).toNat := by
  apply Tools.ShippingUnifiedExecutionSoundness.execution_source_of_env (kb := 1) (kv := 3)
    (vw := widenAddVW) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) widenAdd_peel widenAdd_wf
  · intro j hj
    have h : j = 0 := by omega
    subst h
    exact ⟨`c, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases h with rfl | rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩
    · exact ⟨`x, rfl⟩

open Sparkle.IR.OptCheck Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup
open Tools.SVParser.AST Tools.SVParser.EmitSem Tools.SVParser.EmitAst
open Tools.ShippingDeclWidths Tools.ShippingModulePrintSoundness Tools.ShippingSVBridge
open ShippingMixedExecutionTest in
run_cmd liftTermElabM do
  let mut count := 0
  for name in [``arithmetic1, ``arithmetic8, ``arithmetic65, ``comparison, ``nested] do
    let ci ← getConstInfo name
    unless (mixedCertifiedShape? false [] ci).isSome do
      throwError "Unified-source test missed the extended mutual gate"
    let (raw, _) ← synthesizeCombinationalCore name [] false
    let (legacy, _) ← synthesizeCombinationalCoreWith
      (translateFuelFix (fun rec e h t named =>
        Rec.translateExprToWireCached rec e h t named) translateFuelLimit) name [] false false
    let (actual, _) ← synthesizeCombinational name
    let n := if name == ``arithmetic1 then 1 else if name == ``arithmetic65 then 65 else 8
    let samples := if n == 1 then [0, 1] else [0, 1, 2^(n-1)-1, 2^(n-1), 2^n-1]
    for post in [dropZeroWidthModule raw, mergeDuplicates (dropZeroWidthModule raw), actual] do
      let m := checkedOptimize post
      unless Tools.ShippingSVBridge.forwardCheck m && assignmentOrderCheck m.body do
        throwError "Mutual mux semantic/order checks failed: {name}"
      let some sv := emitAstModule m | throwError "Mutual mux AST emission failed"
      let some pairs := combItems sv.items | throwError "Mutual mux body extraction failed"
      let widths := astWidths sv
      let names := (declarationTable sv).map Prod.fst
      for flags in List.range (if name == ``nested then 4 else 2) do
        for x in samples do
          for y in samples do
            let bs := fun j => if j == 0 then flags % 2 == 1 else flags / 2 == 1
            let vs := fun j (w : Nat) => BitVec.ofNat w (if j == 0 then x else y)
            let values := if name == ``nested then [flags % 2, flags / 2, x, y] else [flags % 2, x, y]
            let expected := if name == ``comparison then encodeBool (eval bs vs (comparisonTerm n))
              else (eval bs vs (if name == ``nested then nestedTerm n else arithmeticTerm n)).toNat
            let legacyInit := fun w =>
              (((legacy.inputs.map (·.name)).zip values).find? (fun p => p.1 == w)).map Prod.snd |>.getD 0
            unless (evalAssigns (Tools.ShippingEntrySoundness.weOf legacy) (fun _ _ => 0)
                legacy.body legacyInit).map (· "out") == some expected do
              throwError "Mutual mux legacy/source mismatch: {name}, {values}"
            for seed in [0, 1, 2^n-1] do
              let initial := fun w =>
                match (((m.inputs.map (·.name)).zip values).find? (fun p => p.1 == w)) with
                | some (_, v) => v
                | none => mask ((widths w).getD 0) seed
              let some stable := evalAssignsSV widths (fun _ _ => 0) pairs initial |
                throwError "Mutual mux SV evaluation failed"
              let mut current := initial
              for _ in [:pairs.length] do
                let some next := parallelRound widths pairs current | throwError "Mutual mux delta failed"
                current := next
              let some extra := parallelRound widths pairs current | throwError "Mutual mux stable round failed"
              unless observeUnsignedOutput sv current "out" == some expected &&
                  names.all (fun x => current x == stable x && extra x == stable x) do
                throwError "Mutual mux source/SV/delta mismatch: {name}, {values}"
              count := count + 1
  unless count == 2322 do throwError "Mutual mux case count mismatch: {count}"
  -- Mixed-width regression: 8-bit comparison controlling a 65-bit mux.
  let ciM ← getConstInfo ``mixedWidth
  unless (mixedCertifiedShape? false [] ciM).isSome do
    throwError "mixed-width source missed the extended gate"
  let (rawM, _) ← synthesizeCombinationalCore ``mixedWidth [] false
  let (actualM, _) ← synthesizeCombinational ``mixedWidth
  let mut mcount : Nat := 0
  for post in [dropZeroWidthModule rawM, mergeDuplicates (dropZeroWidthModule rawM), actualM] do
    let m := checkedOptimize post
    unless Tools.ShippingSVBridge.forwardCheck m && assignmentOrderCheck m.body do
      throwError "mixed-width semantic/order checks failed"
    let some sv := emitAstModule m | throwError "mixed-width AST emission failed"
    let some pairs := combItems sv.items | throwError "mixed-width body extraction failed"
    let widths := astWidths sv
    for flag in [0, 1] do
      for p8 in [(0, 1), (5, 5), (255, 254)] do
        for p65 in [(0, 1), (2^64, 2^65 - 1), (12345, 2^64 + 7)] do
          let bs := fun _ => flag == 1
          let vsv := fun j (w : Nat) => BitVec.ofNat w
            (if j == 0 then p8.1 else if j == 1 then p8.2 else if j == 2 then p65.1 else p65.2)
          let values := [flag, p8.1, p8.2, p65.1, p65.2]
          let expected := (eval bs vsv mixedWidthTerm).toNat
          let initialM := fun w =>
            match (((m.inputs.map (·.name)).zip values).find? (fun p => p.1 == w)) with
            | some (_, v) => v
            | none => 0
          let some stable := evalAssignsSV widths (fun _ _ => 0) pairs initialM |
            throwError "mixed-width SV evaluation failed"
          unless observeUnsignedOutput sv stable "out" == some expected do
            throwError "mixed-width source/SV mismatch: {values}"
          mcount := mcount + 1
  unless mcount == 54 do throwError "mixed-width case count mismatch: {mcount}"
  -- Width-changing regression: zero-extension, truncation, equal-width cast,
  -- and a widened operand under an arithmetic parent.
  let mut scount : Nat := 0
  for name in [``widen, ``narrow, ``rewidth, ``widenAdd] do
    let ci ← getConstInfo name
    unless (mixedCertifiedShape? false [] ci).isSome do
      throwError "width-changing source missed the extended gate: {name}"
    let (raw, _) ← synthesizeCombinationalCore name [] false
    let (actual, _) ← synthesizeCombinational name
    for post in [dropZeroWidthModule raw, mergeDuplicates (dropZeroWidthModule raw), actual] do
      let m := checkedOptimize post
      unless Tools.ShippingSVBridge.forwardCheck m && assignmentOrderCheck m.body do
        throwError "width-changing semantic/order checks failed: {name}"
      let some sv := emitAstModule m | throwError "width-changing AST emission failed: {name}"
      let some pairs := combItems sv.items |
        throwError "width-changing body extraction failed: {name}"
      let widths := astWidths sv
      for flag in [0, 1] do
        for p in [(0, 1, 3), (5, 255, 12345), (254, 255, 65535)] do
          let bs := fun (_ : Nat) => flag == 1
          let (expected, values) :=
            if name == ``widen then
              ((eval bs (fun j w => BitVec.ofNat w (if j == 0 then p.1 else p.2.1))
                widenTerm).toNat, [flag, p.1, p.2.1])
            else if name == ``narrow then
              ((eval bs (fun j w => BitVec.ofNat w
                  (if j == 0 then p.1 * 2 ^ 40 + p.2.2 else p.2.1 * 2 ^ 30 + 77))
                narrowTerm).toNat, [flag, p.1 * 2 ^ 40 + p.2.2, p.2.1 * 2 ^ 30 + 77])
            else if name == ``rewidth then
              ((eval bs (fun j w => BitVec.ofNat w (if j == 0 then p.1 else p.2.1))
                rewidthTerm).toNat, [flag, p.1, p.2.1])
            else
              ((eval bs (fun j w => BitVec.ofNat w
                  (if j == 0 then p.1 else if j == 1 then p.2.1 else p.2.2))
                widenAddTerm).toNat, [flag, p.1, p.2.1, p.2.2])
          let initial := fun w =>
            match (((m.inputs.map (·.name)).zip values).find? (fun q => q.1 == w)) with
            | some (_, v) => v
            | none => 0
          let some stable := evalAssignsSV widths (fun _ _ => 0) pairs initial |
            throwError "width-changing SV evaluation failed: {name}"
          unless observeUnsignedOutput sv stable "out" == some expected do
            throwError "width-changing source/SV mismatch: {name}, {values}"
          scount := scount + 1
  unless scount == 72 do throwError "width-changing case count mismatch: {scount}"
  logInfo m!"UNIFIED SOURCE REGRESSION: {count} uniform + 54 mixed-width + {scount} width-changing source/SV cases through the extended certified gate"

-- The source view must not reinterpret a user instance as a library operation.
example : view (mkApp6 (.const ``HAdd.hAdd [.zero, .zero, .zero])
    (sigT (.bvar 0) 8) (sigT (.bvar 0) 8) (sigT (.bvar 0) 8)
    (.const `UserAdd []) (.bvar 1) (.bvar 2)) = none := rfl
example : view (mkApp5 (.const ``Signal.beq []) (.const ``Bool []) (.bvar 0)
    (.const `UserBEq []) (.bvar 1) (.bvar 2)) = none := rfl

run_cmd do
  if (← get).messages.hasErrors then throwError "Unified source/cache regression failed"
  for name in [``denote_val, ``meaning_quote, ``meaning_quote_mixed, ``Meaning.deterministic,
      ``mixedWidth_execution,
      ``nested_meaning,
      ``Tools.ShippingUnifiedCache.validated_hit, ``Tools.ShippingUnifiedCache.record_preserves,
      ``Tools.ShippingUnifiedCache.cached_action, ``Tools.ShippingUnifiedInvariant.cached_outcome,
      ``Tools.ShippingUnifiedInvariant.Inv.emit_reserved,
      ``Tools.ShippingUnifiedInvariant.Inputs.of_mixed,
      ``Tools.ShippingUnifiedRecursion.fuel_contract,
      ``Tools.ShippingUnifiedRecursion.translateExprToWire_contract,
      ``Tools.ShippingUnifiedProtection.fuel_protects,
      ``Tools.ShippingUnifiedProtection.fuel_orders,
      ``Tools.ShippingUnifiedExecutionSoundness.execution_source_of_env,
      ``nested_execution, ``comparison_execution, ``arithmetic65_execution,
      ``widen_execution, ``narrow_execution, ``widenAdd_execution] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected unified source/cache axiom: {name}: {ax}"
  logInfo "UNIFIED MUTUAL RECURSION ENDPOINT: standard axioms only; general source-to-RTL theorem connected"

end Sparkle.Tests.Compiler.ShippingUnifiedSourceTest

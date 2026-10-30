import Tools.ShippingGen4FbTailInv
import Tools.ShippingMemoInv
import Tests.Gen4.FbInvCheck
-- BUILT (unit FB-4) at f8470c1c: kjob lake build Tests.Gen4.FbTailInvCheck exit 0 (Pod build; clean build is the coder's): TYPE OK x3 (extraction via logged isDefEq), MUTANT REJECTED x8 (signature/defeq), AXIOMS OK x8, closure audit (no Tools.ShippingMemo.*) with 4 controls.
set_option autoImplicit false
-- NOT BUILT (unit FB-4). Checks: TYPE (independent Expected typed again from FALLBACK_SUPPLY_FREEZE.md §12 and the
-- R4RunInv text of f07f4bf2), MUTANT (signature/defeq rejections, NOT semantic counterexamples), projections as
-- theorems, AXIOMS, and an explicit value-closure audit (type and body of every reached constant) with controls.
namespace Tests.Gen4.FbTailInvFixture
/-- helper 1 (uses the memo-law structure `RefLawsM`/`memoInv_hit`) -/
theorem helperA : True := (fun _ => trivial) @Tools.ShippingMemo.memoInv_hit
end Tests.Gen4.FbTailInvFixture

namespace Tests.Gen4.FbTailInvFixtureB
/-- helper 2 (uses helper 1, other namespace) -/
theorem helperB : True := Tests.Gen4.FbTailInvFixture.helperA
end Tests.Gen4.FbTailInvFixtureB

namespace Tests.Gen4.FbTailInvFixtureC
/-- closure-detector control: direct use of `memoInv_hit` -/
theorem badDirect : True := (fun _ => trivial) @Tools.ShippingMemo.memoInv_hit
/-- closure-detector control: through two helpers in other namespaces -/
theorem badIndirect : True := Tests.Gen4.FbTailInvFixtureB.helperB
/-- closure-detector control: unrelated (must NOT be flagged) -/
theorem goodUnrelated : True := trivial
/-- clean control: a built FB-3 theorem (must NOT be flagged) -/
theorem goodFb3 : True := (fun _ => trivial) @Tools.ShippingGen4FbInv.a4_inv_machine_or_R4RunInv
end Tests.Gen4.FbTailInvFixtureC

namespace Tests.Gen4.FbTailInvCheck
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Sparkle.IR.Builder
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingMachineOutcomeA Tools.ShippingMachineOutcomeA3 Tools.ShippingMachineOutcomeA4
open Tools.ShippingGen4FbR4
open Tools.ShippingGen2 Tools.ShippingGen4FbInv Tools.ShippingGen4FbTailInv
open Tests.Gen3.ExpectedType

def ExpR4RunInvT {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    InvAt L P Reach (D + 1) w₄ ∧ InvAt L P Reach (D + 1) w₆ ∧ InvAt L P Reach (D + 1) w₅ ∧
    RunsTo (getConstInfo declName) mctx mref cctx cref w₁ ci w₂ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₂ tenv w₃ ∧
    JQC L.O (D + 1) w₃ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₃ envR' w₄ ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate tenv)
      (userInliner tenv) (structEnv tenv)) (structEnv envR') = some shape ∧
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName shape) mctx mref cctx cref w₄ none w₆ ∧
    JQC L.O (D + 1) w₄ ∧ JQC L.O (D + 1) w₆ ∧
    (∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
      (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
      (sg : Std.HashMap String String),
      RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w₅ () w' ∧
      FinallyRestores (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) D sf sw sl sp sc ss sg w₅ w' ∧
      (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
      (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        declName pb D w sf sw sl sp sc ss sg)) ∧
    JQC L.O D w' ∧
    RunsTo (legacyTail
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName [] false
      (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv)
        (structEnv tenv))) mctx mref cctx cref w₆ (m, d) w₅ ∧
    ∃ (t : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design) (w₇ : Void IO.RealWorld),
      RunsTo (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName shape.binders shape.body) mctx mref cctx cref w₄ (t, d₀) w₇ ∧
      JQC L.O (D + 1) w₇ ∧
      ((Sparkle.IR.Machine.closeLets shape.layout.lets t = none ∧ w₆ = w₇) ∨
       (∃ t', Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧ shape.insts ≠ [] ∧
         ((shape.instFields.isEmpty = true ∧
            RunsTo (closeInstsM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆) ∨
          (shape.instFields.isEmpty = false ∧
            RunsTo (closeInstsGM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆))))

/-- mutant: signature-level change. -/
def MutR4RunInvTNoW5 {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    InvAt L P Reach (D + 1) w₄ ∧ InvAt L P Reach (D + 1) w₆ ∧
    RunsTo (getConstInfo declName) mctx mref cctx cref w₁ ci w₂ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₂ tenv w₃ ∧
    JQC L.O (D + 1) w₃ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₃ envR' w₄ ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate tenv)
      (userInliner tenv) (structEnv tenv)) (structEnv envR') = some shape ∧
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName shape) mctx mref cctx cref w₄ none w₆ ∧
    JQC L.O (D + 1) w₄ ∧ JQC L.O (D + 1) w₆ ∧
    (∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
      (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
      (sg : Std.HashMap String String),
      RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w₅ () w' ∧
      FinallyRestores (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) D sf sw sl sp sc ss sg w₅ w' ∧
      (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
      (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        declName pb D w sf sw sl sp sc ss sg)) ∧
    JQC L.O D w' ∧
    RunsTo (legacyTail
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName [] false
      (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv)
        (structEnv tenv))) mctx mref cctx cref w₆ (m, d) w₅ ∧
    ∃ (t : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design) (w₇ : Void IO.RealWorld),
      RunsTo (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName shape.binders shape.body) mctx mref cctx cref w₄ (t, d₀) w₇ ∧
      JQC L.O (D + 1) w₇ ∧
      ((Sparkle.IR.Machine.closeLets shape.layout.lets t = none ∧ w₆ = w₇) ∨
       (∃ t', Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧ shape.insts ≠ [] ∧
         ((shape.instFields.isEmpty = true ∧
            RunsTo (closeInstsM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆) ∨
          (shape.instFields.isEmpty = false ∧
            RunsTo (closeInstsGM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆))))

/-- mutant: signature-level change. -/
def MutR4RunInvTJQCW5 {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    InvAt L P Reach (D + 1) w₄ ∧ InvAt L P Reach (D + 1) w₆ ∧ JQC L.O (D + 1) w₅ ∧
    RunsTo (getConstInfo declName) mctx mref cctx cref w₁ ci w₂ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₂ tenv w₃ ∧
    JQC L.O (D + 1) w₃ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₃ envR' w₄ ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate tenv)
      (userInliner tenv) (structEnv tenv)) (structEnv envR') = some shape ∧
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName shape) mctx mref cctx cref w₄ none w₆ ∧
    JQC L.O (D + 1) w₄ ∧ JQC L.O (D + 1) w₆ ∧
    (∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
      (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
      (sg : Std.HashMap String String),
      RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w₅ () w' ∧
      FinallyRestores (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) D sf sw sl sp sc ss sg w₅ w' ∧
      (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
      (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        declName pb D w sf sw sl sp sc ss sg)) ∧
    JQC L.O D w' ∧
    RunsTo (legacyTail
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName [] false
      (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv)
        (structEnv tenv))) mctx mref cctx cref w₆ (m, d) w₅ ∧
    ∃ (t : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design) (w₇ : Void IO.RealWorld),
      RunsTo (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName shape.binders shape.body) mctx mref cctx cref w₄ (t, d₀) w₇ ∧
      JQC L.O (D + 1) w₇ ∧
      ((Sparkle.IR.Machine.closeLets shape.layout.lets t = none ∧ w₆ = w₇) ∨
       (∃ t', Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧ shape.insts ≠ [] ∧
         ((shape.instFields.isEmpty = true ∧
            RunsTo (closeInstsM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆) ∨
          (shape.instFields.isEmpty = false ∧
            RunsTo (closeInstsGM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆))))

/-- mutant: signature-level change. -/
def MutR4RunInvTDepthD {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    InvAt L P Reach (D + 1) w₄ ∧ InvAt L P Reach (D + 1) w₆ ∧ InvAt L P Reach D w₅ ∧
    RunsTo (getConstInfo declName) mctx mref cctx cref w₁ ci w₂ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₂ tenv w₃ ∧
    JQC L.O (D + 1) w₃ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₃ envR' w₄ ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate tenv)
      (userInliner tenv) (structEnv tenv)) (structEnv envR') = some shape ∧
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName shape) mctx mref cctx cref w₄ none w₆ ∧
    JQC L.O (D + 1) w₄ ∧ JQC L.O (D + 1) w₆ ∧
    (∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
      (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
      (sg : Std.HashMap String String),
      RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w₅ () w' ∧
      FinallyRestores (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) D sf sw sl sp sc ss sg w₅ w' ∧
      (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
      (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        declName pb D w sf sw sl sp sc ss sg)) ∧
    JQC L.O D w' ∧
    RunsTo (legacyTail
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName [] false
      (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv)
        (structEnv tenv))) mctx mref cctx cref w₆ (m, d) w₅ ∧
    ∃ (t : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design) (w₇ : Void IO.RealWorld),
      RunsTo (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName shape.binders shape.body) mctx mref cctx cref w₄ (t, d₀) w₇ ∧
      JQC L.O (D + 1) w₇ ∧
      ((Sparkle.IR.Machine.closeLets shape.layout.lets t = none ∧ w₆ = w₇) ∨
       (∃ t', Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧ shape.insts ≠ [] ∧
         ((shape.instFields.isEmpty = true ∧
            RunsTo (closeInstsM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆) ∨
          (shape.instFields.isEmpty = false ∧
            RunsTo (closeInstsGM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆))))

/-- mutant: signature-level change. -/
def MutR4RunInvTW6Again {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    InvAt L P Reach (D + 1) w₄ ∧ InvAt L P Reach (D + 1) w₆ ∧ InvAt L P Reach (D + 1) w₆ ∧
    RunsTo (getConstInfo declName) mctx mref cctx cref w₁ ci w₂ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₂ tenv w₃ ∧
    JQC L.O (D + 1) w₃ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₃ envR' w₄ ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate tenv)
      (userInliner tenv) (structEnv tenv)) (structEnv envR') = some shape ∧
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName shape) mctx mref cctx cref w₄ none w₆ ∧
    JQC L.O (D + 1) w₄ ∧ JQC L.O (D + 1) w₆ ∧
    (∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
      (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
      (sg : Std.HashMap String String),
      RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w₅ () w' ∧
      FinallyRestores (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) D sf sw sl sp sc ss sg w₅ w' ∧
      (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
      (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        declName pb D w sf sw sl sp sc ss sg)) ∧
    JQC L.O D w' ∧
    RunsTo (legacyTail
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName [] false
      (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv)
        (structEnv tenv))) mctx mref cctx cref w₆ (m, d) w₅ ∧
    ∃ (t : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design) (w₇ : Void IO.RealWorld),
      RunsTo (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName shape.binders shape.body) mctx mref cctx cref w₄ (t, d₀) w₇ ∧
      JQC L.O (D + 1) w₇ ∧
      ((Sparkle.IR.Machine.closeLets shape.layout.lets t = none ∧ w₆ = w₇) ∨
       (∃ t', Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧ shape.insts ≠ [] ∧
         ((shape.instFields.isEmpty = true ∧
            RunsTo (closeInstsM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆) ∨
          (shape.instFields.isEmpty = false ∧
            RunsTo (closeInstsGM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆))))

/-- projection to FB-3's `R4RunInv` (drop the `w₅` conjunct): a theorem, not a defeq. -/
theorem r4RunInvT_to_R4RunInv {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld)
    (h : R4RunInvT L P Reach mctx cctx D declName shape m d w w') :
    R4RunInv L P Reach mctx cctx D declName shape m d w w' := by
  obtain ⟨tenv, pb, ci, envR', w₁, w₂, w₃, w₄, w₅, w₆, h4, h6, _, h⟩ := h
  exact ⟨tenv, pb, ci, envR', w₁, w₂, w₃, w₄, w₅, w₆, h4, h6, h⟩

/-- projection to FB-2's `R4Run`. -/
theorem r4RunInvT_to_R4Run {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld)
    (h : R4RunInvT L P Reach mctx cctx D declName shape m d w w') :
    R4Run L.O mctx cctx D declName shape m d w w' :=
  Tests.Gen4.FbInvCheck.r4RunInv_to_R4Run L P Reach mctx cctx D declName shape m d w w'
    (r4RunInvT_to_R4RunInv L P Reach mctx cctx D declName shape m d w w' h)

/-- the extraction projected to FB-3's `a4_inv_machine_or_R4RunInv` statement. -/
theorem a4_tail_projects_to_a4_inv {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
      R4RunInv L P Reach mctx cctx D declName shape m d w w' :=
  (a4_inv_tail_machine_or_R4RunInvT L P Reach hA hI hC hr entry).imp id
    (r4RunInvT_to_R4RunInv L P Reach mctx cctx D declName shape m d w w')

/-- ... and to FB-2's `a4_machine_or_R4Run` statement (`A4MachineSideA ∨ R4Run`). -/
theorem a4_tail_projects_to_a4_machine_or_R4Run {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨ R4Run L.O mctx cctx D declName shape m d w w' :=
  (a4_inv_tail_machine_or_R4RunInvT L P Reach hA hI hC hr entry).imp id
    (r4RunInvT_to_R4Run L P Reach mctx cctx D declName shape m d w w')

def ExpLegacyTailKeepsInv : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat)
    (hC : ChildKeepsInv L P Reach (D + 1))
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    (tenv : Lean.Environment) (pb : Bool) (declName : Name) (ci : ConstantInfo),
    Keeps mctx mref cctx cref (InvAt L P Reach (D + 1))
      (legacyTail (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName [] false ci)

def ExpA4InvTailMachineOrR4RunInvT : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
      ExpR4RunInvT L P Reach mctx cctx D declName shape m d w w'

/-! mutants of the statements (signature level) -/
def MutTailKeepsAtD : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat)
    (hC : ChildKeepsInv L P Reach (D + 1))
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    (tenv : Lean.Environment) (pb : Bool) (declName : Name) (ci : ConstantInfo),
    Keeps mctx mref cctx cref (InvAt L P Reach D)
      (legacyTail (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName [] false ci)

def MutTailKeepsNoHC : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    (tenv : Lean.Environment) (pb : Bool) (declName : Name) (ci : ConstantInfo),
    Keeps mctx mref cctx cref (InvAt L P Reach (D + 1))
      (legacyTail (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName [] false ci)

def MutExtractNoHC : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
      R4RunInvT L P Reach mctx cctx D declName shape m d w w'

def MutExtractJQHyp : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : JQ L.O.quiet D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
      R4RunInvT L P Reach mctx cctx D declName shape m d w w'

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``R4RunInvT ``ExpR4RunInvT
  checkExpected ``legacyTail_keepsInv ``ExpLegacyTailKeepsInv
  checkExpected ``a4_inv_tail_machine_or_R4RunInvT ``ExpA4InvTailMachineOrR4RunInvT
  checkMutant ``R4RunInvT ``MutR4RunInvTNoW5
  checkMutant ``R4RunInvT ``MutR4RunInvTJQCW5
  checkMutant ``R4RunInvT ``MutR4RunInvTDepthD
  checkMutant ``R4RunInvT ``MutR4RunInvTW6Again
  checkMutant ``legacyTail_keepsInv ``MutTailKeepsAtD
  checkMutant ``legacyTail_keepsInv ``MutTailKeepsNoHC
  checkMutant ``a4_inv_tail_machine_or_R4RunInvT ``MutExtractNoHC
  checkMutant ``a4_inv_tail_machine_or_R4RunInvT ``MutExtractJQHyp

/-! ## Value-closure audit
The new declarations must not reach the memo-law structure `RefLawsM` or `Tools.ShippingMemo.*` (no `LM`, no
`memoInv_hit`) through their type or their EXPLICIT body (every reached constant, every namespace, including the
structure name of a raw `Expr.proj`). Opaque/partial implementations are not kernel terms and are not followed. -/

def fbNew : List Name :=
  [``legacyTail_keeps_generic, ``legacyTail_keepsInv, ``R4RunInvT, ``a4_inv_tail_machine_or_R4RunInvT,
   ``r4RunInvT_to_R4RunInv, ``r4RunInvT_to_R4Run, ``a4_tail_projects_to_a4_inv,
   ``a4_tail_projects_to_a4_machine_or_R4Run]

def fbForbidden (n : Name) : Bool := (`Tools.ShippingMemo).isPrefixOf n

def fbBody? : ConstantInfo → Option Lean.Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

/-- constants of `e`, plus the structure name of every raw `Expr.proj` node (`getUsedConstants` skips that). -/
partial def fbConsts (e : Lean.Expr) : Array Name :=
  let rec go (e : Lean.Expr) (seen : Std.HashSet Lean.Expr) (acc : Array Name) :
      Std.HashSet Lean.Expr × Array Name :=
    if seen.contains e then (seen, acc) else
    let seen := seen.insert e
    match e with
    | .const c _ => (seen, acc.push c)
    | .proj s _ b => go b seen (acc.push s)
    | .app f a => let (s, r) := go f seen acc; go a s r
    | .lam _ t b _ => let (s, r) := go t seen acc; go b s r
    | .forallE _ t b _ => let (s, r) := go t seen acc; go b s r
    | .letE _ t v b _ => let (s, r) := go t seen acc; let (s, r) := go v s r; go b s r
    | .mdata _ b => go b seen acc
    | _ => (seen, acc)
  (go e {} #[]).2

structure FbReach where
  hit : Option (List Name) := none
  visited : Nat := 0
  noBody : Nat := 0
  opaques : Array Name := #[]
  deriving Inhabited

def fbReach (root : Name) (cap : Nat := 3000000) : MetaM FbReach := do
  let env ← getEnv
  let mut out : FbReach := {}
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then
      throwError "FB4 AUDIT INCOMPLETE at {root}: more than {cap} constants; non-reference NOT established"
    let some ci := env.find? c | continue
    let body := fbBody? ci
    if body.isNone then out := { out with noBody := out.noBody + 1 }
    if ci matches .opaqueInfo _ then out := { out with opaques := out.opaques.push c }
    let used := fbConsts ci.type ++ (body.map fbConsts).getD #[]
    for u in used do
      if fbForbidden u then
        return { out with hit := some (path ++ [u]) }
      unless seen.contains u do
        seen := seen.insert u
        queue := queue.push (u, path ++ [u])
  return out

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- raw-projection control on a bare expression (the structure name of an `Expr.proj` is seen)
  let rawProj := Lean.Expr.proj ``Tools.ShippingMemo.RefLawsM 0 (Lean.mkBVar 0)
  unless (fbConsts rawProj).any fbForbidden do
    throwError "FB4 AUDIT FAILED: the detector misses a raw Expr.proj of RefLawsM"
  logInfo m!"FB4 REACH CONTROL raw proj: flagged"
  for (c, bad) in [(``Tests.Gen4.FbTailInvFixtureC.badDirect, true), (``Tests.Gen4.FbTailInvFixtureC.badIndirect, true),
      (``Tests.Gen4.FbTailInvFixtureC.goodUnrelated, false), (``Tests.Gen4.FbTailInvFixtureC.goodFb3, false)] do
    let r ← fbReach c
    if bad && r.hit.isNone then throwError "FB4 AUDIT FAILED: the closure detector misses {c}"
    if !bad && r.hit.isSome then throwError "FB4 AUDIT FAILED: the closure detector flags {c}: {toString r.hit}"
    logInfo m!"FB4 REACH CONTROL {c}: {toString r.hit}"
  for c in fbNew do
    let r ← fbReach c
    if let some p := r.hit then
      throwError "FB4 AUDIT FAILED {c}: reaches Tools.ShippingMemo.* via {p}"
    logInfo m!"FB4 REACH {c}: no Tools.ShippingMemo.* in the closure (visited {r.visited}, no-body {r.noBody}, opaque {r.opaques.size})"
  for c in fbNew do
    checkAxioms c

end Tests.Gen4.FbTailInvCheck

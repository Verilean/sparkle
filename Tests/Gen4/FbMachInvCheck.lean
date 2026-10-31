import Tools.ShippingGen4FbMachInv
import Tools.ShippingMemoInv
import Tools.ShippingLegacySemMemoWalk
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT (unit FB-13). Text = scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §21.4/§21.5 (rev12, scoped approved at a02dc304).
-- Expected definitions are typed again here: `ExpSideInv` = the body of `A4MachineSideA` (ShippingGen4FbR4.lean:71-98, `O := L.O`)
-- with the three leading `InvAt (D+1)` conjuncts; `ExpR4RunInvT5` = a retyped copy of the `R4RunInvT` body.
-- Checks: TYPE (definition VALUE and TYPE, three theorems), MUTANT (well-typed single changes; signature/defeq rejections,
-- NOT semantic counterexamples), projections (theorems), value-closure audit with `missing` failing when non-zero, controls, AXIOMS.

namespace Tests.Gen4.FbMachInvFixture
theorem helperA : True := (fun _ => trivial) @Tools.ShippingMemo.memoInv_hit
end Tests.Gen4.FbMachInvFixture
namespace Tests.Gen4.FbMachInvFixtureB
theorem helperB : True := Tests.Gen4.FbMachInvFixture.helperA
end Tests.Gen4.FbMachInvFixtureB
namespace Tests.Gen4.FbMachInvFixtureC
theorem badDirect : True := (fun _ => trivial) @Tools.ShippingMemo.memoInv_hit
theorem badOuterMiss : True := (fun _ => trivial) @Tools.ShippingLegacySem.outer_miss
theorem badIndirect : True := Tests.Gen4.FbMachInvFixtureB.helperB
theorem goodUnrelated : True := trivial
theorem goodFb3 : True := (fun _ => trivial) @Tools.ShippingGen4FbInv.a4_inv_machine_or_R4RunInv
end Tests.Gen4.FbMachInvFixtureC

namespace Tests.Gen4.FbMachInvCheck
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
open Tools.ShippingGen2 Tools.ShippingGen4FbInv Tools.ShippingGen4FbTailInv Tools.ShippingGen4FbFin0 Tools.ShippingGen4FbMachInv
open Tests.Gen3.ExpectedType



def ExpSideInv {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
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
      declName shape) mctx mref cctx cref w₄ (some (m, d)) w₆ ∧
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
    ∃ wl : Void IO.RealWorld,
      RunsTo (show MetaM Unit from profLogIO pb
        s!"[profile] synthesizeCombinational {declName} machine certified front end")
        mctx mref cctx cref w₆ () wl ∧
      RunsTo (sparkleSubModuleCache.modify (·.insert declName (m, d)) : MetaM Unit)
        mctx mref cctx cref wl () w₅

def MutDefNo5 {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
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
      declName shape) mctx mref cctx cref w₄ (some (m, d)) w₆ ∧
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
    ∃ wl : Void IO.RealWorld,
      RunsTo (show MetaM Unit from profLogIO pb
        s!"[profile] synthesizeCombinational {declName} machine certified front end")
        mctx mref cctx cref w₆ () wl ∧
      RunsTo (sparkleSubModuleCache.modify (·.insert declName (m, d)) : MetaM Unit)
        mctx mref cctx cref wl () w₅

def MutDefJQC5 {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
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
      declName shape) mctx mref cctx cref w₄ (some (m, d)) w₆ ∧
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
    ∃ wl : Void IO.RealWorld,
      RunsTo (show MetaM Unit from profLogIO pb
        s!"[profile] synthesizeCombinational {declName} machine certified front end")
        mctx mref cctx cref w₆ () wl ∧
      RunsTo (sparkleSubModuleCache.modify (·.insert declName (m, d)) : MetaM Unit)
        mctx mref cctx cref wl () w₅

def MutDefDepthD {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
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
      declName shape) mctx mref cctx cref w₄ (some (m, d)) w₆ ∧
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
    ∃ wl : Void IO.RealWorld,
      RunsTo (show MetaM Unit from profLogIO pb
        s!"[profile] synthesizeCombinational {declName} machine certified front end")
        mctx mref cctx cref w₆ () wl ∧
      RunsTo (sparkleSubModuleCache.modify (·.insert declName (m, d)) : MetaM Unit)
        mctx mref cctx cref wl () w₅

def MutDefW6Twice {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
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
      declName shape) mctx mref cctx cref w₄ (some (m, d)) w₆ ∧
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
    ∃ wl : Void IO.RealWorld,
      RunsTo (show MetaM Unit from profLogIO pb
        s!"[profile] synthesizeCombinational {declName} machine certified front end")
        mctx mref cctx cref w₆ () wl ∧
      RunsTo (sparkleSubModuleCache.modify (·.insert declName (m, d)) : MetaM Unit)
        mctx mref cctx cref wl () w₅

def ExpR4RunInvT5 {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
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

def ExpFin0Side : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : ExpSideInv L P Reach mctx cctx 0 declName shape m d w w'),
    InvAt L P Reach 0 w'

def MutT1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : ExpSideInv L P Reach mctx cctx 0 declName shape m d w w'),
    InvAt L P Reach 1 w'

def MutT2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : ExpSideInv L P Reach mctx cctx 0 declName shape m d w w'),
    InvAt L P Reach 0 w

def MutT3 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : ExpSideInv L P Reach mctx cctx 0 declName shape m d w w'),
    JQC L.O 0 w'

def MutT4 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : ExpSideInv L P Reach mctx cctx 1 declName shape m d w w'),
    InvAt L P Reach 0 w'

def MutT5 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} 
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : ExpSideInv L P Reach mctx cctx 0 declName shape m d w w'),
    InvAt L P Reach 0 w'

def ExpExtract : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    ExpSideInv L P Reach mctx cctx D declName shape m d w w' ∨
      ExpR4RunInvT5 L P Reach mctx cctx D declName shape m d w w'

def MutS1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    ExpSideInv L P Reach mctx cctx D declName shape m d w w' ∨
      ExpR4RunInvT5 L P Reach mctx cctx D declName shape m d w w'

def MutS2 : Prop :=
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
      ExpR4RunInvT5 L P Reach mctx cctx D declName shape m d w w'

def MutS3 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    ExpSideInv L P Reach mctx cctx D declName shape m d w w' ∨
      R4RunInv L P Reach mctx cctx D declName shape m d w w'

def ExpBoth : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach 0 w) (hC : ChildKeepsInv L P Reach 1)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    (ExpSideInv L P Reach mctx cctx 0 declName shape m d w w' ∨
      ExpR4RunInvT5 L P Reach mctx cctx 0 declName shape m d w w') ∧ InvAt L P Reach 0 w'

def MutB1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach 0 w) (hC : ChildKeepsInv L P Reach 1)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    ExpSideInv L P Reach mctx cctx 0 declName shape m d w w' ∨
      ExpR4RunInvT5 L P Reach mctx cctx 0 declName shape m d w w'

def MutB2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach 0 w) (hC : ChildKeepsInv L P Reach 1)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    ExpSideInv L P Reach mctx cctx 0 declName shape m d w w' ∨
      (ExpR4RunInvT5 L P Reach mctx cctx 0 declName shape m d w w' ∧ InvAt L P Reach 0 w')

def MutB3 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach 0 w) (hC : ChildKeepsInv L P Reach 0)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    (ExpSideInv L P Reach mctx cctx 0 declName shape m d w w' ∨
      ExpR4RunInvT5 L P Reach mctx cctx 0 declName shape m d w w') ∧ InvAt L P Reach 0 w'

def MutB4 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach 0 w) (hC : ChildKeepsInv L P Reach 1)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    (A4MachineSideA L.O mctx cctx 0 declName shape m d w w' ∨
      ExpR4RunInvT5 L P Reach mctx cctx 0 declName shape m d w w') ∧ InvAt L P Reach 0 w'

/-- projection: `A4MachineSideInv → A4MachineSideA L.O` (drop the three leading `InvAt` conjuncts). -/
theorem sideInv_to_sideA {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} {D : Nat}
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : A4MachineSideInv L P Reach mctx cctx D declName shape m d w w') :
    A4MachineSideA L.O mctx cctx D declName shape m d w w' := by
  obtain ⟨tenv, pb, ci, envR', w₁, w₂, w₃, w₄, w₅, w₆, _, _, _, rest⟩ := h
  exact ⟨tenv, pb, ci, envR', w₁, w₂, w₃, w₄, w₅, w₆, rest⟩

/-- projection: the extraction projects to `a4_inv_tail_machine_or_R4RunInvT`'s conclusion. -/
theorem extract_to_fb4 {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
      R4RunInvT L P Reach mctx cctx D declName shape m d w w' := by
  rcases a4_inv_side_or_tail L P Reach hA hI hC hr entry with h | h
  · exact Or.inl (sideInv_to_sideA L P Reach h)
  · exact Or.inr h

def checkDefType (thm exp : Name) : MetaM Unit := do
  let a := (← getConstInfo thm).type
  let e := (← getConstInfo exp).type
  cmpTele s!"{thm} (definition TYPE)" a e
  logInfo m!"GEN3 TYPE OK (definition type) {thm} against {exp}"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``A4MachineSideInv ``ExpSideInv
  checkDefType ``A4MachineSideInv ``ExpSideInv
  checkExpected ``tFin0_of_a4MachineSideInv ``ExpFin0Side
  checkExpected ``a4_inv_side_or_tail ``ExpExtract
  checkExpected ``a4_inv_tail_fin0_both ``ExpBoth
  -- definition-value mutants (each a well-typed single change to the Expected body)
  checkMutant ``A4MachineSideInv ``MutDefNo5
  checkMutant ``A4MachineSideInv ``MutDefJQC5
  checkMutant ``A4MachineSideInv ``MutDefDepthD
  checkMutant ``A4MachineSideInv ``MutDefW6Twice
  -- theorem mutants
  checkMutant ``tFin0_of_a4MachineSideInv ``MutT1
  checkMutant ``tFin0_of_a4MachineSideInv ``MutT2
  checkMutant ``tFin0_of_a4MachineSideInv ``MutT3
  checkMutant ``tFin0_of_a4MachineSideInv ``MutT4
  checkMutant ``tFin0_of_a4MachineSideInv ``MutT5
  checkMutant ``a4_inv_side_or_tail ``MutS1
  checkMutant ``a4_inv_side_or_tail ``MutS2
  checkMutant ``a4_inv_side_or_tail ``MutS3
  checkMutant ``a4_inv_tail_fin0_both ``MutB1
  checkMutant ``a4_inv_tail_fin0_both ``MutB2
  checkMutant ``a4_inv_tail_fin0_both ``MutB3
  checkMutant ``a4_inv_tail_fin0_both ``MutB4

/-! ## Value-closure audit (§14.4): `missing` constants make the audit FAIL ("not established") -/
def fbNew : List Name :=
  [``A4MachineSideInv, ``a4_inv_side_or_tail, ``tFin0_of_a4MachineSideInv, ``a4_inv_tail_fin0_both, ``sideInv_to_sideA, ``extract_to_fb4]
def fbForbidden (n : Name) : Bool := (`Tools.ShippingMemo).isPrefixOf n
def fbBody? : ConstantInfo → Option Lean.Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none
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
  missing : Array Name := #[]
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
      throwError "FB13 AUDIT INCOMPLETE at {root}: more than {cap} constants; non-reference NOT established"
    let some ci := env.find? c | do
      out := { out with missing := out.missing.push c }
      continue
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
  -- control (a): a root that is not in the environment is reported as missing, and the audit assertion fails
  let r0 ← fbReach `Tests.Gen4.FbMachInvFixtureC.doesNotExist
  if r0.missing.isEmpty then throwError "FB13 AUDIT FAILED: the detector does not report an absent root as missing"
  let failed ← try
      (if r0.missing.size != 0 then throwError "FB13 missing constants: {r0.missing}" else pure false)
    catch _ => pure true
  unless failed do throwError "FB13 AUDIT FAILED: the missing-assertion did not fail on an absent root"
  logInfo m!"FB13 REACH CONTROL absent root: missing {r0.missing.size}, assertion failed as expected"
  -- control (b): raw proj and fixtures
  let rawProj := Lean.Expr.proj ``Tools.ShippingMemo.RefLawsM 0 (Lean.mkBVar 0)
  unless (fbConsts rawProj).any fbForbidden do
    throwError "FB13 AUDIT FAILED: the detector misses a raw Expr.proj of RefLawsM"
  logInfo m!"FB13 REACH CONTROL raw proj: flagged"
  for (c, bad) in [(``Tests.Gen4.FbMachInvFixtureC.badDirect, true), (``Tests.Gen4.FbMachInvFixtureC.badOuterMiss, true), (``Tests.Gen4.FbMachInvFixtureC.badIndirect, true),
      (``Tests.Gen4.FbMachInvFixtureC.goodUnrelated, false), (``Tests.Gen4.FbMachInvFixtureC.goodFb3, false), (``Tools.ShippingGen4FbFin.a4_inv_tail_fin, false), (``Tools.ShippingGen4FbFin0.a4_inv_tail_fin0, false)] do
    let r ← fbReach c
    if bad && r.hit.isNone then throwError "FB13 AUDIT FAILED: the closure detector misses {c}"
    if !bad && r.hit.isSome then throwError "FB13 AUDIT FAILED: the closure detector flags {c}: {toString r.hit}"
    if !bad && !r.missing.isEmpty then throwError "FB13 AUDIT FAILED: control {c} has missing constants {r.missing}"
    logInfo m!"FB13 REACH CONTROL {c}: {toString r.hit} (missing {r.missing.size})"
  for c in fbNew do
    let r ← fbReach c
    if let some p := r.hit then
      throwError "FB13 AUDIT FAILED {c}: reaches Tools.ShippingMemo.* via {p}"
    unless r.missing.isEmpty do
      throwError "FB13 AUDIT NOT ESTABLISHED {c}: {r.missing.size} reached constants not in the environment: {r.missing}"
    logInfo m!"FB13 REACH {c}: no Tools.ShippingMemo.* in the closure (visited {r.visited}, missing {r.missing.size}, no-body {r.noBody}, opaque {r.opaques.size})"
  for c in fbNew do
    checkAxioms c

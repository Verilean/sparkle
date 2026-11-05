import Tools.ShippingGen5Flow1Tie
import Tests.Gen5.ClosingRun2Check
set_option autoImplicit false
set_option linter.unusedVariables false
-- NOT BUILT as a clean issue-linked build yet (build is the coder's). No sorry / axiom / native_decide.

/-! # FG flow 1 U1 checks (Tools/ShippingGen5Flow1Tie.lean; scripts/gen5/FLOW1_FREEZE.md section 2)

Expected statements are written from the frozen types of FLOW1_FREEZE.md section 2, not derived from the implementation's
signature. ONE comparator (`Tests.Gen5.ClosingRun2Check.cmpTeleR`: binder-by-binder, macro scopes erased, binder info, types by `==`
with a REDUCIBLE `isDefEq` fallback) accepts them. Mutants are one-point, well-typed variants of an Expected statement; they are
rejected by this comparator (rejection by signature / defeq of a changed statement, NOT a semantic counterexample).
Negative control: the `hsh : ClosingShared` form (`callTie_of_closingShared_*`) is not accepted as the run-side form.
Closure: value + type walk; the ROOT itself is judged; unresolved names fail (value-side and type-side negative controls).
Not claimed: `hord`/`hGen`/`hIH`/`hKI`, non-vacuity, depth-0 `stop`, `hDG_SEM`/`hOW`/`hkidW`, T1/FG. -/

namespace Tests.Gen5.Flow1TieFixture
theorem helperV : True := trivial
theorem useV : True := helperV
theorem helperT : True := trivial
theorem useT : helperT = helperT := rfl
theorem rootBad : True := (fun _ => trivial) @Tools.ShippingGen2.core_reads_invAt0
end Tests.Gen5.Flow1TieFixture

namespace Tests.Gen5.Flow1TieCheck
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.IR.Builder
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids
open Tools.ShippingGen2 Tools.ShippingGen5RunReads Tools.ShippingGen5ClosingRun
open Tools.ShippingGen5Flow1Tie
open Tests.Gen3.ExpectedType
open Tests.Gen5.ClosingRun2Check (cmpTeleR forbidConsts badProj reachWith AReach)

/-! ## 1. Independent Expected values and one-point mutants -/

def ExpOne : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def ExpGroup : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneNoHs : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneNoHd0 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneHsW1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w') (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneHd0W1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w' = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneHIH2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 2) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneHKI2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 2)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneHordNoBound : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneHordFieldsNe : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields ≠ [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneGenSwap : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR' envR)
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneGenWSwap : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w' w raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneNoGenHyp : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneHRunW : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w' (raw, D) w)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneHRunNoCore : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] true) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneHNoneNe : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? ≠ none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneNoPq : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, CallTie p q k hk

def MutOneHRPX : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneH1Ne : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneNoOW : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutOneNoDGSEM : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpNoHs : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpNoHd0 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpHsW1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w') (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpHd0W1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w' = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpHIH2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 2) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpHKI2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 2)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpHordNoBound : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpHordFieldsNe : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields ≠ [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpGenSwap : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR' envR)
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpGenWSwap : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w' w raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpNoGenHyp : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpHRunW : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w' (raw, D) w)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpHRunNoCore : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] true) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpHNoneNe : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? ≠ none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpNoPq : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, CallTie p q k hk

def MutGrpHRPX : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpHGEq : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpNoKidW : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutGrpNoDGSEM : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk


/-! ## 2. Checker -/

def checkExp (thm exp : Name) : MetaM Unit := do
  let ciT ← getConstInfo thm
  let ciE ← getConstInfo exp
  unless ciT.levelParams.length == ciE.levelParams.length do throwError "FLOW1 CHECK FAILED {thm}: universe parameters"
  let a ← stmtOf thm
  let e ← stmtOf exp
  let e := e.instantiateLevelParams ciE.levelParams (ciT.levelParams.map mkLevelParam)
  cmpTeleR s!"{thm}" a e

def rejected (thm mt : Name) : MetaM Bool := do
  let a ← stmtOf thm
  let e ← stmtOf mt
  withoutModifyingState do
    try
      cmpTeleR s!"{thm} vs {mt}" a e
      pure false
    catch _ => pure true

/-! ## 3. Closure audit -/

/-- Judge the ROOT itself, then its value+type closure; unresolved names are a failure. Returns visited count. -/
def auditRoot (resolve : Name → Option ConstantInfo) (root : Name) (req : List Name) : MetaM Nat := do
  if forbidConsts.contains root then throwError "FLOW1 AUDIT FAILED: root {root} is itself forbidden"
  let r ← reachWith resolve root
  if let some p := r.hit then throwError "FLOW1 AUDIT FAILED {root}: forbidden use via {p}"
  if r.unknown != 0 then throwError "FLOW1 AUDIT FAILED {root}: {r.unknown} unresolved name(s), first via {toString r.unknownFirst}"
  for t in req do
    unless r.seen.contains t do throwError "FLOW1 AUDIT FAILED {root}: {t} not reached"
  return r.visited

def auditFails (resolve : Name → Option ConstantInfo) (root : Name) : MetaM Bool := do
  try
    let _ ← auditRoot resolve root []
    pure false
  catch _ => pure true

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let mutOne : List Name := [``MutOneNoHs, ``MutOneNoHd0, ``MutOneHsW1, ``MutOneHd0W1, ``MutOneHIH2, ``MutOneHKI2, ``MutOneHordNoBound, ``MutOneHordFieldsNe, ``MutOneGenSwap, ``MutOneGenWSwap, ``MutOneNoGenHyp, ``MutOneHRunW, ``MutOneHRunNoCore, ``MutOneHNoneNe, ``MutOneNoPq, ``MutOneHRPX, ``MutOneH1Ne, ``MutOneNoOW, ``MutOneNoDGSEM]
  let mutGrp : List Name := [``MutGrpNoHs, ``MutGrpNoHd0, ``MutGrpHsW1, ``MutGrpHd0W1, ``MutGrpHIH2, ``MutGrpHKI2, ``MutGrpHordNoBound, ``MutGrpHordFieldsNe, ``MutGrpGenSwap, ``MutGrpGenWSwap, ``MutGrpNoGenHyp, ``MutGrpHRunW, ``MutGrpHRunNoCore, ``MutGrpHNoneNe, ``MutGrpNoPq, ``MutGrpHRPX, ``MutGrpHGEq, ``MutGrpNoKidW, ``MutGrpNoDGSEM]
  -- TYPE: Expected accepted
  checkExp ``callTie_of_run_one_ex ``ExpOne
  checkExp ``callTie_of_run_group_kidW ``ExpGroup
  -- MUTANT: each one-point variant rejected; the hsh-form (old) statements are rejected as the run-side form
  let mut nMut : Nat := 0
  for m in mutOne do
    unless ← rejected ``callTie_of_run_one_ex m do throwError "FLOW1 MUTANT ACCEPTED: {m}"
    nMut := nMut + 1
  for m in mutGrp do
    unless ← rejected ``callTie_of_run_group_kidW m do throwError "FLOW1 MUTANT ACCEPTED: {m}"
    nMut := nMut + 1
  let mut nNeg : Nat := 0
  for (t, o) in [(``callTie_of_run_one_ex, ``Tools.ShippingGen5T2TieCR2.callTie_of_closingShared_one_ex),
      (``callTie_of_run_group_kidW, ``Tools.ShippingGen5T2TieCR2.callTie_of_closingShared_group_kidW),
      (``callTie_of_run_one_ex, ``Tools.ShippingGen5ClosingRun2.closingRun0_of_run)] do
    unless ← rejected t o do throwError "FLOW1 NEGATIVE CONTROL ACCEPTED: {o} matched {t}"
    nNeg := nNeg + 1
  -- CONTROL: detector controls (root itself, raw bad uses, value-side / type-side unresolved)
  let env ← getEnv
  let F := `Tests.Gen5.Flow1TieFixture
  let mut nCtl : Nat := 0
  unless ← auditFails env.find? ``Tools.ShippingGen2.core_reads_invAt0 do throwError "FLOW1 CONTROL FAILED: root itself not judged"
  nCtl := nCtl + 1
  unless ← auditFails env.find? (F ++ `rootBad) do throwError "FLOW1 CONTROL FAILED: bad use not flagged"
  nCtl := nCtl + 1
  if ← auditFails env.find? (F ++ `useV) then throwError "FLOW1 CONTROL FAILED: clean fixture useV fails"
  if ← auditFails env.find? (F ++ `useT) then throwError "FLOW1 CONTROL FAILED: clean fixture useT fails"
  nCtl := nCtl + 1
  let hideV := fun n => if n == F ++ `helperV then none else env.find? n
  let hideT := fun n => if n == F ++ `helperT then none else env.find? n
  unless ← auditFails hideV (F ++ `useV) do throwError "FLOW1 CONTROL FAILED: unknown helper VALUE skipped"
  nCtl := nCtl + 1
  unless ← auditFails hideT (F ++ `useT) do throwError "FLOW1 CONTROL FAILED: unknown helper TYPE skipped"
  nCtl := nCtl + 1
  -- REACH: the real roots
  let common := [``Tools.ShippingGen5ClosingRun2.closingRun0_of_run, ``Tools.ShippingGen5RunReads.runReads_of_run,
      ``Tools.ShippingGen5ClosingRun2.closingShared_of_run, ``Tools.ShippingGen5T2TieCR2.calleePkg_of_t1ND]
  let v1 ← auditRoot env.find? ``callTie_of_run_one_ex
    (common ++ [``Tools.ShippingGen5T2TieCR2.callTie_of_closingShared_one_ex, ``Tools.ShippingGen5T2TieCR.servedCall_of_closingShared_one])
  let v2 ← auditRoot env.find? ``callTie_of_run_group_kidW
    (common ++ [``Tools.ShippingGen5T2TieCR2.callTie_of_closingShared_group_kidW, ``Tools.ShippingGen5T2TieCR2.servedCall_of_closingShared_group])
  -- AXIOMS
  let mut nAx : Nat := 0
  for n in [``callTie_of_run_one_ex, ``callTie_of_run_group_kidW] do
    checkAxioms n
    nAx := nAx + 1
  logInfo m!"FLOW1 TIE SUMMARY: TYPE 2, MUTANT {nMut} (one 19, group 19) + NEGATIVE {nNeg}, CONTROL {nCtl}, REACH 2 (visited {v1}, {v2}), AXIOMS {nAx} standard-only"

end Tests.Gen5.Flow1TieCheck

import Tools.ShippingGen5T2TieCR2
import Tests.Gen5.T2TieCRCheck
import Tests.Gen5.ClosingRun2Check
import Tests.Gen5.T2TieCheck
import Tests.Gen3.ExpectedType
import Tools.ShippingGen5ClosingRun
set_option autoImplicit false
-- NOT BUILT as a clean issue-linked build. No sorry / axiom / native_decide.

/-! # T2-TIE next-unit checks (Tools/ShippingGen5T2TieCR2.lean; scripts/gen5/T2TIE_NEXT_FREEZE_R0.md §3-§4)

`ExpA`-`ExpC2` are written from the Lean text of freeze §3 (not from the implementation's signature), compared with the SAME
reducible comparator as `Tests.Gen5.ClosingRun2Check` (`checkExpectedR`/`checkMutantR`/`reachWith`). Positive controls: the built
`servedCall_of_closingShared_one` and `callTie_of_served_oneOut_t1ND` pass the same comparator. Mutants N1-N12 are well-typed
one-place differences, rejected by signature/defeq only; they are NOT semantic counterexamples. Closure walker: unknown names fail;
named/raw projection and recursor detection and the `stop_of_run` prohibition are kept.

Not claimed: supply of `hDG_SEM`, `OneOutWidth`, `hkidW`, `hrow`/`hord`, `hGen`, non-vacuity, depth-0 `stop`, T1/FG. -/

namespace Tests.Gen5.T2TieCR2Check
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingGen2 Tools.ShippingGen5ClosingRun2 Tools.ShippingGen5T2TieCR2
open Tests.Gen3.ExpectedType Tests.Gen5.ClosingRun2Check

def ExpCtlOneOut : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L P Reach DataOk) (hRp : Reach p.decl) (hPp : P p.decl = some p)
    (hord : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (h1 : p.d.shape.instFields = []) (hOW : OneOutWidth P p k),
    CallTie p q k hk

def ExpA : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ q.decl = (p.d.shape.insts[k]'hk).1 ∧ DataOk q

def ExpB : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none),
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1

def ExpC1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk) (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def ExpC2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth) ,
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutN1A : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    (k : Nat) (hk : k < p.d.shape.insts.length),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ q.decl = (p.d.shape.insts[k]'hk).1 ∧ DataOk q

def MutN2A : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ q.decl = X ∧ DataOk q

def MutN3A : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ q.decl = (p.d.shape.insts[k]'hk).1

def MutN4B : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (hG : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none),
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1

def MutN5B : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none),
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p (k + 1) r.1

def MutN6B : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none),
    ∃ (dsn : Sparkle.IR.AST.Design) (r : Tools.ShippingChildInv.Res),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1

def MutN7C1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk) ,
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutN8C1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk) (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p p k hk

def MutN8C2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth) ,
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p p k hk

def MutN9C1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p p k hk) (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutN9C2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p p k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth) ,
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutN10C2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k + 1]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth) ,
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutN11C2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O p.decl y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth) ,
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

def MutN12C1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk) (hOW : OneOutWidth P p k),
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk

run_cmd Lean.Elab.Command.liftTermElabM do
  -- positive controls: built statements, same comparator
  checkExpectedR ``Tools.ShippingGen5T2TieCR.servedCall_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.ExpT1
  checkExpectedR ``Tools.ShippingGen2.callTie_of_served_oneOut_t1ND ``Tests.Gen5.T2TieCR2Check.ExpCtlOneOut
  -- new statements against the independent Expected
  checkExpectedR ``calleePkg_of_t1ND ``Tests.Gen5.T2TieCR2Check.ExpA
  checkExpectedR ``servedCall_of_closingShared_group ``Tests.Gen5.T2TieCR2Check.ExpB
  checkExpectedR ``callTie_of_closingShared_one_ex ``Tests.Gen5.T2TieCR2Check.ExpC1
  checkExpectedR ``callTie_of_closingShared_group_kidW ``Tests.Gen5.T2TieCR2Check.ExpC2
  checkMutantR ``calleePkg_of_t1ND ``Tests.Gen5.T2TieCR2Check.MutN1A
  checkMutantR ``calleePkg_of_t1ND ``Tests.Gen5.T2TieCR2Check.MutN2A
  checkMutantR ``calleePkg_of_t1ND ``Tests.Gen5.T2TieCR2Check.MutN3A
  checkMutantR ``servedCall_of_closingShared_group ``Tests.Gen5.T2TieCR2Check.MutN4B
  checkMutantR ``servedCall_of_closingShared_group ``Tests.Gen5.T2TieCR2Check.MutN5B
  checkMutantR ``servedCall_of_closingShared_group ``Tests.Gen5.T2TieCR2Check.MutN6B
  checkMutantR ``callTie_of_closingShared_one_ex ``Tests.Gen5.T2TieCR2Check.MutN7C1
  checkMutantR ``callTie_of_closingShared_one_ex ``Tests.Gen5.T2TieCR2Check.MutN8C1
  checkMutantR ``callTie_of_closingShared_group_kidW ``Tests.Gen5.T2TieCR2Check.MutN8C2
  checkMutantR ``callTie_of_closingShared_one_ex ``Tests.Gen5.T2TieCR2Check.MutN9C1
  checkMutantR ``callTie_of_closingShared_group_kidW ``Tests.Gen5.T2TieCR2Check.MutN9C2
  checkMutantR ``callTie_of_closingShared_group_kidW ``Tests.Gen5.T2TieCR2Check.MutN10C2
  checkMutantR ``callTie_of_closingShared_group_kidW ``Tests.Gen5.T2TieCR2Check.MutN11C2
  checkMutantR ``callTie_of_closingShared_one_ex ``Tests.Gen5.T2TieCR2Check.MutN12C1

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let F := `Tests.Gen5.ClosingRun2Fixture
  for (c, bad) in [(F ++ `badDec, true), (F ++ `badCoreReads, true), (F ++ `unrelated, false), (F ++ `cleanND, false)] do
    let r ← reach c
    if bad && r.hit.isNone then throwError "CR2 AUDIT FAILED: detector misses {c}"
    if !bad && r.hit.isSome then throwError "CR2 AUDIT FAILED: detector flags {c}"
  let envU ← getEnv
  let hideB := fun n => if n == `Tests.Gen5.ClosingRun2Helper.helperA then none else envU.find? n
  let rU ← reachWith hideB (F ++ `badCoreReadsHelper)
  if rU.unknown == 0 then throwError "CR2 AUDIT FAILED: unresolved name was skipped, not counted"
  let stopN := ``Tools.ShippingGen5ClosingRun.stop_of_run
  for (c, bad) in [(`Tests.Gen5.T2TieCRStopFixture.badStopDirect, true),
      (`Tests.Gen5.T2TieCRStopFixture.badStopHelper, true),
      (`Tests.Gen5.T2TieCRStopFixture.cleanStop, false)] do
    let r ← reach c
    if r.unknown != 0 then throwError "CR2 STOP AUDIT FAILED: fixture {c} has unresolved names"
    if bad && !r.seen.contains stopN then throwError "CR2 STOP AUDIT FAILED: stop_of_run detector misses {c}"
    if !bad && r.seen.contains stopN then throwError "CR2 STOP AUDIT FAILED: stop_of_run detector flags {c}"
  logInfo m!"CR2 STOP controls OK: direct and helper fixtures detected, clean fixture not flagged"
  for (c, req) in [(``calleePkg_of_t1ND, [``Tools.ShippingGen2.T1HypND.pkg, ``Tools.ShippingGen2.T1HypND.closed]),
      (``servedCall_of_closingShared_group,
        [``Tools.ShippingMachineInstG.closeInstsG_calls, ``Tools.ShippingMachineInstG.closeInstsG_names,
         ``Tools.ShippingGen2.T1HypND.closed]),
      (``callTie_of_closingShared_one_ex,
        [``calleePkg_of_t1ND, ``Tools.ShippingGen5T2TieCR.servedCall_of_closingShared_one,
         ``Tools.ShippingGen2.houtTy_of_closingND, ``Tools.ShippingGen2.callTie_of_served_oneOut]),
      (``callTie_of_closingShared_group_kidW,
        [``calleePkg_of_t1ND, ``servedCall_of_closingShared_group, ``Tools.ShippingGen2.houtTy_of_closingND,
         ``Tools.ShippingGen2.callTie_of_served_kidW_closing])] do
    let r ← reach c
    if let some p := r.hit then throwError "CR2 AUDIT FAILED {c}: forbidden use via {p}"
    if r.unknown != 0 then throwError "CR2 AUDIT FAILED {c}: {r.unknown} unresolved name(s), first via {toString r.unknownFirst}"
    if r.seen.contains stopN then throwError "CR2 AUDIT FAILED {c}: stop_of_run reached"
    for t in req do
      unless r.seen.contains t do throwError "CR2 AUDIT FAILED {c}: {t} not reached"
    logInfo m!"CR2 REACH {c}: no forbidden root (T1Hyp.dec / T1Hyp fields / raw proj / recursor / BodyStepC / core_reads_invAt0 / soundX_ships_ran / servedShips0_proved / TopShips / ofReduceBool); reaches {req} (visited {r.visited}, unknown 0); stop_of_run not reached"

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``calleePkg_of_t1ND, ``servedCall_of_closingShared_group, ``callTie_of_closingShared_one_ex,
      ``callTie_of_closingShared_group_kidW] do
    checkAxioms n

end Tests.Gen5.T2TieCR2Check

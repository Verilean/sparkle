import Tools.ShippingGen5T2Conn
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- §7.7 part built in g5tc-f72cedf6 (clean, exit 0, 740 jobs; TYPE 4, MUTANT 9, AXIOMS 4); §7.8 additions NOT BUILT.
-- No sorry / axiom / native_decide.

/-! # T2-TIE connection checks (Tools/ShippingGen5T2Conn.lean; DGEN_FREEZE.md §7.7)

Expected types written independently and compared mechanically (`checkExpected`); mutants that must be rejected
(`checkMutant`; a rejection is a signature / defeq rejection, not a semantic counterexample); axioms. CONDITIONAL:
`houtTy`, `CallOutWidthAt` inputs (`OneOutWidth` / `hy`,`hout`,`hkidW`), T2-FIELD, `hDG_CLOSINGRUN` and DG-SEM stay
unsupplied inputs. Not T2-TIE supply, not M5/FG completion. -/

namespace Tests.Gen5.T2ConnCheck
open Tools.ShippingGen2
open Tests.Gen3.ExpectedType
open Sparkle.Core.Domain
open Sparkle.Core Sparkle.Core.Signal

/-- §7.3/§7.7 (a) -/
def ExpectedDgenWidths : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hT2_FIELD : ∀ i : ι,
      ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hW : CallOutWidthAt p q k),
    CallTie p q k hk

/-- Mutant: without the callee row `houtTy`. -/
def MutDgenWidthsNoOutTy : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hT2_FIELD : ∀ i : ι,
      ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o)
    (hDG_SEM : GenExtAtCall p q k hk)
    (hW : CallOutWidthAt p q k),
    CallTie p q k hk

/-- Mutant: `houtTy` weakened to `≤`. -/
def MutDgenWidthsLeOutTy : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hT2_FIELD : ∀ i : ι,
      ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.width ≤ o.ty.bitWidth)
    (hW : CallOutWidthAt p q k),
    CallTie p q k hk

/-- Mutant: without DG-SEM's `GenExtAtCall`. -/
def MutDgenWidthsNoSem : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hT2_FIELD : ∀ i : ι,
      ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hW : CallOutWidthAt p q k),
    CallTie p q k hk

/-- §7.7 (b) -/
def ExpectedServedWidths : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hW : CallOutWidthAt p q k),
    CallTie p q k hk

/-- Mutant: without `hDG_CLOSINGRUN`. -/
def MutServedWidthsNoClosing : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hW : CallOutWidthAt p q k),
    CallTie p q k hk

/-- §7.7 (c) one-output parents -/
def ExpectedServedOneOut : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (h1 : p.d.shape.instFields = []) (hOW : OneOutWidth P p k),
    CallTie p q k hk

/-- Mutant: without `instFields = []`. -/
def MutServedOneOutNoH1 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hOW : OneOutWidth P p k),
    CallTie p q k hk

/-- Mutant: without G-ONEOUT-WID's `OneOutWidth`. -/
def MutServedOneOutNoOW : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (h1 : p.d.shape.instFields = []),
    CallTie p q k hk

/-- §7.7 (d) group parents -/
def ExpectedServedKidW : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref)
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hG : p.d.shape.instFields ≠ []) {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y)
    (hout : y.1.outputs = q.d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)))
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    CallTie p q k hk

/-- Mutant: without `hout`. -/
def MutServedKidWNoHout : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref)
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hG : p.d.shape.instFields ≠ []) {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    CallTie p q k hk

/-- Mutant: without `hy` (no served child of call `k`). -/
def MutServedKidWNoHy : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref)
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hG : p.d.shape.instFields ≠ []) {y : Tools.ShippingChildInv.Res}
    (hout : y.1.outputs = q.d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)))
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    CallTie p q k hk

/-- Mutant: without `instFields ≠ []`. -/
def MutServedKidWNoHG : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref)
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y)
    (hout : y.1.outputs = q.d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)))
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    CallTie p q k hk

/-- §7.8 group range row from the closing witness -/
def ExpectedClosingKidWRange : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hG : p.d.shape.instFields ≠ [])
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    CallOutRange p q k hk

/-- Mutant: without `houtTy`. -/
def MutClosingKidWRangeNoOutTy : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hG : p.d.shape.instFields ≠ [])
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    CallOutRange p q k hk

/-- Mutant: without `instFields ≠ []`. -/
def MutClosingKidWRangeNoHG : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    CallOutRange p q k hk

/-- Mutant: `hkidW` with a trivial conclusion. -/
def MutClosingKidWRangeTrivKidW : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hG : p.d.shape.instFields ≠ [])
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        True),
    CallOutRange p q k hk

/-- §7.8 group CallTie, closing form -/
def ExpectedServedKidWClosing : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hG : p.d.shape.instFields ≠ [])
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    CallTie p q k hk

/-- Mutant: without DG-SEM's `GenExtAtCall`. -/
def MutServedKidWClosingNoSem : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hG : p.d.shape.instFields ≠ [])
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    CallTie p q k hk

/-- Mutant: without `hDG_CLOSINGRUN`. -/
def MutServedKidWClosingNoClosing : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hG : p.d.shape.instFields ≠ [])
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    CallTie p q k hk

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``callTie_of_dgen_widths ``ExpectedDgenWidths
  checkExpected ``callTie_of_served_widths ``ExpectedServedWidths
  checkExpected ``callTie_of_served_oneOut ``ExpectedServedOneOut
  checkExpected ``callTie_of_served_kidW ``ExpectedServedKidW
  checkExpected ``callOutRange_of_closing_kidW ``ExpectedClosingKidWRange
  checkExpected ``callTie_of_served_kidW_closing ``ExpectedServedKidWClosing
  checkMutant ``callTie_of_dgen_widths ``MutDgenWidthsNoOutTy
  checkMutant ``callTie_of_dgen_widths ``MutDgenWidthsLeOutTy
  checkMutant ``callTie_of_dgen_widths ``MutDgenWidthsNoSem
  checkMutant ``callTie_of_served_widths ``MutServedWidthsNoClosing
  checkMutant ``callTie_of_served_oneOut ``MutServedOneOutNoH1
  checkMutant ``callTie_of_served_oneOut ``MutServedOneOutNoOW
  checkMutant ``callTie_of_served_kidW ``MutServedKidWNoHout
  checkMutant ``callTie_of_served_kidW ``MutServedKidWNoHy
  checkMutant ``callTie_of_served_kidW ``MutServedKidWNoHG
  checkMutant ``callOutRange_of_closing_kidW ``MutClosingKidWRangeNoOutTy
  checkMutant ``callOutRange_of_closing_kidW ``MutClosingKidWRangeNoHG
  checkMutant ``callOutRange_of_closing_kidW ``MutClosingKidWRangeTrivKidW
  checkMutant ``callTie_of_served_kidW_closing ``MutServedKidWClosingNoSem
  checkMutant ``callTie_of_served_kidW_closing ``MutServedKidWClosingNoClosing

/-! ## Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``callTie_of_dgen_widths, ``callTie_of_served_widths, ``callTie_of_served_oneOut, ``callTie_of_served_kidW, ``callOutRange_of_closing_kidW,
      ``callTie_of_served_kidW_closing] do
    checkAxioms n

end Tests.Gen5.T2ConnCheck

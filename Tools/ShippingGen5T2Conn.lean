import Tools.ShippingGen5T2Range
set_option autoImplicit false
-- NOT BUILT: written without running Lean. No sorry / axiom / native_decide.

/-! # T2-TIE connection to the range supplier (DGEN_FREEZE.md §7.3 / §7.7)

`callTie_of_dgen` / `callTie_of_served` (Tools/ShippingGen5T2Tie.lean) take the range row `hDG_SEM_range :
CallOutRange p q k hk` as a hypothesis. Here it is replaced by `callOutRange_of_widths`'s inputs: the callee row
`houtTy` and `CallOutWidthAt p q k`, which in turn is taken from

* one-output parents (`instFields = []`): G-ONEOUT-WID's `OneOutWidth P p k` (`callOutWidthAt_of_oneOut`);
* group parents (`instFields ≠ []`): the SAME child's `hy` / `hout` and the group premise `hkidW`
  (`callOutWidthAt_of_kidW`).

CONDITIONAL. Nothing here supplies `houtTy` (callee coverage OPEN), `OneOutWidth`, `hy`/`hout`/`hkidW`, the
T2-FIELD selection, `hDG_CLOSINGRUN` or `GenExtAtCall` (DG-SEM). No FG premise, no `Nonempty ι`, no change of
`T1Hyp`/`GenWF`; T2-TIE stays conditional on DG-SEM. Not M5 or FG completion. -/
namespace Tools.ShippingGen2
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

variable {ι : Type} {dom : ι → DomainConfig}

/-- `callTie_of_dgen` with the range row from `houtTy` + `CallOutWidthAt`. -/
theorem callTie_of_dgen_widths (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hT2_FIELD : ∀ i : ι,
      ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hW : CallOutWidthAt p q k) :
    CallTie p q k hk :=
  callTie_of_dgen p q k hk hT2_FIELD hDG_SEM (callOutRange_of_widths p q k hk houtTy hW)

/-- `callTie_of_served` with the range row from `houtTy` + `CallOutWidthAt`. -/
theorem callTie_of_served_widths {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hW : CallOutWidthAt p q k) :
    CallTie p q k hk :=
  callTie_of_served L P p q k hk hDG_GENP hDG_CLOSINGRUN hDG_SEM (callOutRange_of_widths p q k hk houtTy hW)

/-- **One-output parents**: the range row from `houtTy` + G-ONEOUT-WID's `OneOutWidth P p k`. -/
theorem callTie_of_served_oneOut {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (h1 : p.d.shape.instFields = []) (hOW : OneOutWidth P p k) :
    CallTie p q k hk :=
  callTie_of_served_widths L P p q k hk hDG_GENP hDG_CLOSINGRUN hDG_SEM houtTy
    (callOutWidthAt_of_oneOut P p q k hk hDG_GENP h1 hOW)

/-- **Group parents**: the range row from `houtTy` + the same child's `hy`/`hout` + `hkidW`. `hy`/`hout` are explicit
inputs (their supply for the served child is OPEN). -/
theorem callTie_of_served_kidW {mref cref} (L : Laws mref cref)
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
          some pt.ty.bitWidth) :
    CallTie p q k hk :=
  callTie_of_served_widths L P p q k hk hDG_GENP hDG_CLOSINGRUN hDG_SEM houtTy
    (callOutWidthAt_of_kidW O p q k hk hG hy hout hkidW)

end Tools.ShippingGen2

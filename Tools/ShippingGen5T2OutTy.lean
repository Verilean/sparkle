import Tools.ShippingGen5T2Conn
import Tools.ShippingReaderOutsInv
import Tools.ShippingPostSoundness
set_option autoImplicit false
-- NOT BUILT: written without running Lean. No sorry / axiom / native_decide.

/-! # T2-OUTTY: the callee's `houtTy` row (scripts/gen5/DGEN_FREEZE.md §7.9, rev2.5, par/gen5-t2 505f3392)

(H1) one real-entry result of a reached callee gives `∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width`:
`RealChildA.run` → `synthesizeCombinational_reads` (core run in the SAME admissible context) → `outTy_of_core` with
`T1Hyp.defines`. (H2) the callee of an ORDINARY call of a reached parent is reached (`T1Hyp.closed`). (H3) the row from
the closing witness `r`. (H4) the §7.7 (c) / §7.8 roots with `houtTy` replaced by T1's own hypotheses and the
ordinary-call branch condition `hord`.

Uses `T1Hyp.defines` (H1, H3) and `T1Hyp.closed` (H2) ONLY; never `T1Hyp.dec`, `pkg` or `closes` (closure audit in
Tests/Gen5/T2OutTyCheck.lean). `DataOk` stays abstract. CONDITIONAL: `hDG_CLOSINGRUN`, DG-SEM, `OneOutWidth` /
`hkidW` remain inputs. Not M5 or FG completion. -/
namespace Tools.ShippingGen2
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

variable {ι : Type} {dom : ι → DomainConfig}

/-- **(H1)** The `houtTy` row of a reached callee from ONE real-entry result. -/
theorem houtTy_of_realChild {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1Hyp L P Reach DataOk) {c : Lean.Name} {q : Pkg ι dom}
    {r : Tools.ShippingChildInv.Res} (hR : Reach c) (hq : P c = some q)
    (hy : Tools.ShippingChildCacheA.RealChildA L.O c r) :
    ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width :=
  match hy with
  | .run mctx cctx _ _ adm _ _ _ hr => by
    obtain ⟨_, _, _, core, -⟩ := Tools.ShippingPostSoundness.synthesizeCombinational_reads hr
    exact Tools.ShippingReaderOutsInv.outTy_of_core core (H.defines c hR q hq mctx cctx adm)

/-- **(H2)** The callee of an ordinary call of a reached parent is reached. -/
theorem reach_callee_of_t1 {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1Hyp L P Reach DataOk) (p : Pkg ι dom) (hRp : Reach p.decl)
    (hPp : P p.decl = some p) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hord : (p.d.shape.instOrigins.getD k .ord).child? = none) :
    Reach (p.d.shape.insts[k]'hk).1 :=
  H.closed p.decl hRp p hPp k hk hord

/-- **(H3)** The `houtTy` row from the closing witness of `hDG_CLOSINGRUN`. -/
theorem houtTy_of_closing {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1Hyp L P Reach DataOk) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hRc : Reach (p.d.shape.insts[k]'hk).1)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1) :
    ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width := by
  obtain ⟨r, _, hS, -⟩ := hDG_CLOSINGRUN
  exact houtTy_of_realChild L P H hRc hDG_GENP hS.1

/-- **(H4) one-output parents**: §7.7 (c) without `houtTy`. -/
theorem callTie_of_served_oneOut_t1 {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (hRp : Reach p.decl) (hPp : P p.decl = some p)
    (hord : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (h1 : p.d.shape.instFields = []) (hOW : OneOutWidth P p k) :
    CallTie p q k hk :=
  callTie_of_served_oneOut L P p q k hk hDG_GENP hDG_CLOSINGRUN hDG_SEM
    (houtTy_of_closing L P H p q k hk (reach_callee_of_t1 L P H p hRp hPp k hk hord) hDG_GENP hDG_CLOSINGRUN)
    h1 hOW

/-- **(H4) group parents**: §7.8 without `houtTy`. -/
theorem callTie_of_served_kidW_closing_t1 {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (hRp : Reach p.decl) (hPp : P p.decl = some p)
    (hord : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (hG : p.d.shape.instFields ≠ [])
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth) :
    CallTie p q k hk :=
  callTie_of_served_kidW_closing L P p q k hk hDG_GENP hDG_CLOSINGRUN hDG_SEM
    (houtTy_of_closing L P H p q k hk (reach_callee_of_t1 L P H p hRp hPp k hk hord) hDG_GENP hDG_CLOSINGRUN)
    hG hkidW

end Tools.ShippingGen2

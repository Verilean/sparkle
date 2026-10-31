import Tools.ShippingGen5T2TieCR
import Tools.ShippingGen5T1ND
import Tools.ShippingMachineInstG
import Tools.ShippingChildServe
set_option autoImplicit false
-- Built in ttcr6-456699fc (clean issue-linked build, exit 0, 776 jobs; scoped approved at 456699fc).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # T2-TIE next unit (scripts/gen5/T2TIE_NEXT_FREEZE_R0.md, approved f13820c9)

CONDITIONAL compositions. Not a supply of `hDG_SEM` (`GenExtAtCall`), `OneOutWidth`, `hkidW`, `hrow`/`hord`, `hGen`,
non-vacuity, the depth-0 `stop`, or the general FG; they remain named premises. -/

namespace Tools.ShippingGen5T2TieCR2
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

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

theorem calleePkg_of_t1ND
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) :
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ q.decl = (p.d.shape.insts[k]'hk).1 ∧ DataOk q := by
  obtain ⟨q, hq, hd, hok⟩ := hT.pkg _ (hT.closed X hR p hP k hk hnone)
  exact ⟨q, hq, hd, hok⟩

theorem servedCall_of_closingShared_group
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D)
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) :
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1 := by
  obtain ⟨-, -, -, -, -, -, t, t', d₀, children, -, -, -, -, hcl', hbr, -⟩ := hsh
  rcases hbr with ⟨hi, -⟩ | ⟨-, hcc, hch⟩
  · rw [hi] at hk
    exact absurd hk (Nat.not_lt_zero _)
  · rcases hcc with ⟨h1, -⟩ | ⟨-, hci, -⟩
    · exact absurd h1 hG
    · obtain ⟨st, -, args, outs, child, mc, hst, hmc, hout, -, hchild⟩ :=
        Tools.ShippingMachineInstG.closeInstsG_calls hci k (by simpa using hk)
      obtain ⟨-, -, -, hnames⟩ := Tools.ShippingMachineInstG.closeInstsG_names hci
      obtain ⟨y, hy, hdisj⟩ := hch.2 k hk
      rw [hy] at hchild
      simp only [Option.map_some, Option.some.injEq] at hchild
      have hmem : y ∈ children := List.mem_of_getElem? hy
      have hyn := hnames y hmem
      have hmc' : mc = y.1 := by
        rw [hchild, hmc] at hyn
        exact Option.some.inj hyn.1.symm ▸ rfl
      rcases hdisj with hc | ⟨-, hS⟩
      · rw [hnone] at hc
        cases hc
      · have hReach := hT.closed X hR p hP k hk hnone
        refine ⟨y, D, hS hReach, hyn.2, hyn.1, ?_⟩
        unfold FieldRowAt
        rw [if_neg hG]
        obtain ⟨-, -, -, -, -, -, -, hall, -⟩ := hst
        have hf := List.all_eq_true.mp hall _ (List.mem_map.mpr ⟨_, hout, rfl⟩)
        obtain ⟨o, ho, hon⟩ := List.any_eq_true.mp hf
        subst hmc'
        exact List.mem_map.mpr ⟨o, ho, by simpa using hon⟩

theorem callTie_of_closingShared_one_ex
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D)
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k) :
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk := by
  obtain ⟨q, hq, -, -⟩ := calleePkg_of_t1ND hT hR hP k hk hnone
  have hclosing := Tools.ShippingGen5T2TieCR.servedCall_of_closingShared_one hT hR hP hsh h1 k hk hnone
  exact ⟨q, hq, callTie_of_served_oneOut L P p q k hk hq hclosing (hDG_SEM q hq)
    (houtTy_of_closingND L P hT p q k hk (hT.closed X hR p hP k hk hnone) hq hclosing) h1 hOW⟩

theorem callTie_of_closingShared_group_kidW
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D)
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth) :
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk := by
  obtain ⟨q, hq, -, -⟩ := calleePkg_of_t1ND hT hR hP k hk hnone
  have hclosing := servedCall_of_closingShared_group hT hR hP hsh hG k hk hnone
  exact ⟨q, hq, callTie_of_served_kidW_closing L P p q k hk hq hclosing (hDG_SEM q hq)
    (houtTy_of_closingND L P hT p q k hk (hT.closed X hR p hP k hk hnone) hq hclosing) hG hkidW⟩

end Tools.ShippingGen5T2TieCR2

#print axioms Tools.ShippingGen5T2TieCR2.calleePkg_of_t1ND
#print axioms Tools.ShippingGen5T2TieCR2.servedCall_of_closingShared_group
#print axioms Tools.ShippingGen5T2TieCR2.callTie_of_closingShared_one_ex
#print axioms Tools.ShippingGen5T2TieCR2.callTie_of_closingShared_group_kidW

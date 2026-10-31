import Tools.ShippingGen5ClosingRun2
import Tools.ShippingGen5T2Tie
import Tools.ShippingChildServe
set_option autoImplicit false
-- NOT BUILT: new unit (freeze r1 95671524); clean build is run by the coder.
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # T2-TIE x DG-CLOSINGRUN: one-output connection (scripts/gen5/T2TIE_CR_FREEZE_R1.md)

Supplies, for a ONE-OUTPUT parent (`instFields = []`) and an ordinary call `k` (`child? = none`), the four conjuncts C1-C4 of
the named hypothesis `hDG_CLOSINGRUN` of `callTie_of_served` from a `ClosingShared` / `ClosingRun0`, and composes them with the
built `callTie_of_served`. Scope: this is a conditional one-output connection. It is NOT a supply of `hDG_GENP`, `hDG_SEM`,
`hDG_SEM_range`, the group field row, `hord`/`hrow`, `hGen`, non-vacuity of `ClosingShared`, the depth-0 `stop`, or the general FG,
and it does not complete the Issue. -/

namespace Tools.ShippingGen5T2TieCR
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

theorem servedCall_of_closingShared_one
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D)
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) :
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1 := by
  obtain ⟨-, -, -, -, -, -, t, t', d₀, children, -, -, -, -, hcl', hbr, -⟩ := hsh
  rcases hbr with ⟨hi, -⟩ | ⟨-, hcc, hch⟩
  · rw [hi] at hk
    exact absurd hk (Nat.not_lt_zero _)
  · rcases hcc with ⟨-, hci⟩ | ⟨hne, -⟩
    · obtain ⟨args, child, mc, hargs, hchild, hmc, st, -, hst⟩ :=
        Tools.ShippingMachineInst.closeInsts_calls hci k (by simpa using hk)
      obtain ⟨-, hnames⟩ := Tools.ShippingChildServe.closeInsts_names hci
      have hmem : child ∈ children := List.mem_of_getElem? hchild
      have hmc' : mc = child.1 := by
        have h2 := hnames child hmem
        rw [hmc] at h2
        exact Option.some.inj h2
      obtain ⟨y, hy, hdisj⟩ := hch.2 k hk
      have hyc : y = child := Option.some.inj (hy.symm.trans hchild)
      subst hyc
      rcases hdisj with hc | ⟨-, hS⟩
      · rw [hnone] at hc
        cases hc
      · have hReach := hT.closed X hR p hP k hk hnone
        have hacy := Tools.ShippingChildServe.closeInsts_acyclic hci
        refine ⟨y, D, hS hReach, ?_, ?_, ?_⟩
        · intro g hg
          exact hacy.2.2.2 y hmem g hg
        · exact hnames y hmem
        · subst hmc'
          exact fieldRow_one_of_callStmt p k h1 hst
    · exact absurd h1 hne

theorem callTie_of_closingShared_one
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D)
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk) :
    CallTie p q k hk :=
  callTie_of_served L P p q k hk hDG_GENP
    (servedCall_of_closingShared_one hT hR hP hsh h1 k hk hnone) hDG_SEM hDG_SEM_range

theorem callTie_of_closingRun0_one
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : Tools.ShippingGen5ClosingRun2.ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D)
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk) :
    CallTie p q k hk :=
  callTie_of_closingShared_one hT hR hP h.shared h1 k hk hnone q hDG_GENP hDG_SEM hDG_SEM_range

end Tools.ShippingGen5T2TieCR

#print axioms Tools.ShippingGen5T2TieCR.servedCall_of_closingShared_one
#print axioms Tools.ShippingGen5T2TieCR.callTie_of_closingShared_one
#print axioms Tools.ShippingGen5T2TieCR.callTie_of_closingRun0_one

import Tools.ShippingGen5AuditE3B3Run
import Tools.ShippingGen5T1ND
set_option autoImplicit false
-- A.P-17 re-threading (Issue sparkle-ledger-ap17): `auditE3B3_of_t1hyp_run` with `H : T1HypND` (no `dec`). No sorry / axiom / native_decide.

/-! # D.E-3 / B3 from `T1HypND`

`machPrem3R_of_t1hyp` and `auditE3B3_of_t1hyp_run` (Tools/ShippingGen5AuditE3B3Run.lean) use only `H.pkg`, `H.defines`, `H.closes`,
`H.closed`, which `T1HypND` (Tools/ShippingGen5T1ND.lean) has verbatim. The copies below are the same text with `H : T1HypND`;
nothing else changes. -/

namespace Tools.ShippingGen5AuditE3B3
open Lean Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5FG
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingSrm7Rank (CallGraph callees declRank InClass kidModName)
open Tools.ShippingSrm15Graph (graphOf FirstOcc)
open Tools.ShippingMemCloses (memKey)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingGen5NameKids2 (MemTagsNamed kidNameAt)
open Tools.ShippingGen5NameKids3 (GraphAgrees ReachSpans OrdPath OrdEdge ReachClosed)
open Tools.ShippingEntrySoundness (RunsTo)
open Sparkle.IR.ModuleName (ofDecl)
open Tools.ShippingGen5AuditCarrier (SOf)
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry Tools.ShippingEntrySoundness
open Tools.ShippingSrm7Rank
open Tools.ShippingGen5NameKids3
open Tools.ShippingSrm12Corr
open Tools.ShippingChildInv (Res)
open Tools.ShippingKidsChildIface (synthesizeCombinational_designL)
open Tools.ShippingChildVCA
open Tools.ShippingChildBndCore (dv cv)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry Tools.ShippingEntrySoundness
open Tools.ShippingCacheCoherentRun (IsMem)
open Tools.ShippingChildInv (Res)
open Sparkle.IR.AST (Stmt)

open Sparkle.IR.AST (Stmt)

section ND
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}

theorem machPrem3R_of_t1hypND {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L P Reach DataOk) (R : DataRes3R DataOk) (hA : AdmCtx L.O.quiet mctx cctx) :
    ∀ c, Reach c → ∀ sp, SOf P c = some sp → MachPrem3R (mctx := mctx) (cctx := cctx) L.O c sp := by
  intro c hc sp hS
  obtain ⟨q, hq, hdecl, hdo⟩ := H.pkg c hc
  subst hdecl
  simp only [SOf, hq, Option.map_some, Option.some.injEq] at hS
  subst hS
  refine ⟨q.d, rfl, q.ok, q.body_eq, R.outTy q hdo, ?_, ?_⟩
  · exact H.defines _ hc q hq mctx cctx hA
  · by_cases hno : q.d.shape.insts = []
    · refine Or.inl ⟨hno, fun mctx' cctx' => ?_⟩
      exact leafCloses_of_data _ q.d q.ok q.body_eq hno (R.leafAlias q hdo hno) mctx' cctx'
    · obtain ⟨hC, hsl, hdom⟩ := R.callsRows q hdo hno
      have hcl : ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context), AdmCtx L.O.quiet mctx' cctx' →
          MachineClosesAtA (mref := mref) (cref := cref) L.O mctx' cctx' q.decl q.d.shape :=
        fun mctx' cctx' hA' => H.closes _ hc q hq mctx' cctx' hA'
      by_cases hf : q.d.shape.instFields = []
      · exact Or.inr (Or.inr ⟨q.kD, hC, hsl, hdom, hno, hf, hcl⟩)
      · exact Or.inr (Or.inl ⟨q.kD, hC, hsl, hdom, hno, hf, hcl⟩)

theorem auditE3B3_of_t1hypND_run {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L P Reach DataOk)
    (hMemRow : ∀ q : Pkg ι dom, DataOk q → MemParentDataOk q ∧ ExtInS q)
    (hLeafAlias : ∀ q : Pkg ι dom, DataOk q → q.d.shape.insts = [] → q.d.letsAliasOk = true)
    (hA : AdmCtx L.O.quiet mctx cctx)
    {g : CallGraph} {B : Nat} {top : Name}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) (hg : GraphAgrees g Reach (SOf P)) :
    AuditE3 P Reach L ∧ AuditB3 L P Reach := by
  have R : DataRes3R DataOk :=
    { callsRows := fun q hq _ => by
        obtain ⟨-, hc, hs, -, hd⟩ := MemParentDataOk.rows (hMemRow q hq).1
        exact ⟨hc, hs, hd⟩
      outTy := fun q hq => by
        obtain ⟨-, -, -, ho, -⟩ := MemParentDataOk.rows (hMemRow q hq).1
        exact ho
      leafAlias := hLeafAlias }
  have hS : ∀ c, Reach c → ∃ sp, SOf P c = some sp := by
    intro c hc
    obtain ⟨q, hq, -, -⟩ := H.pkg c hc
    exact ⟨q.d.shape, by simp [SOf, hq]⟩
  have hcl : ReachClosed Reach (SOf P) := by
    intro c hc sp hSc k hk hch
    obtain ⟨q, hq, -, -⟩ := H.pkg c hc
    simp only [SOf, hq, Option.map_some, Option.some.injEq] at hSc
    subst hSc
    exact H.closed c hc q hq k hk hch
  have Q := q_induct3R L.O L.T hin hsp hg hS (machPrem3R_of_t1hypND H R hA) hcl
  refine ⟨auditE3_of_q hcl Q, ?_⟩
  intro c hc sp hSc k hk y hkid ns
  have K := kidOK_of_kidTA hg hcl Q hc hSc hk hkid
  refine ⟨fun a ha => List.mem_map.mpr ⟨a, List.mem_cons_of_mem _ ha, rfl⟩, ?_, ?_⟩
  · intro a ha mn i cs hm
    obtain ⟨g', hg', rfl⟩ := K.2 a ha mn i cs hm
    exact List.mem_map.mpr ⟨g', List.mem_cons_of_mem _ hg', rfl⟩
  · intro hmem
    obtain ⟨a, ha, e⟩ := List.mem_map.mp hmem
    exact kidOK_hsep hin hsp hc K a ha e

end ND

end Tools.ShippingGen5AuditE3B3

#print axioms Tools.ShippingGen5AuditE3B3.machPrem3R_of_t1hypND
#print axioms Tools.ShippingGen5AuditE3B3.auditE3B3_of_t1hypND_run

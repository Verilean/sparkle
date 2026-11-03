import Tools.ShippingGen5AuditE3B3
import Tools.ShippingGen3HrowGate
import Tools.ShippingGen5RunReads
set_option autoImplicit false
-- NOT BUILT (written in the rt136 Pod; the build is pending).
-- U-A4 hrow (T1L-04) from the run: hrow-free version of auditE3B3_of_t1hyp (scripts/gen5/AUD_UA4_HROW.md).
-- The origin-only row (instFields = [] -> every tag is a non-memory origin) is obtained INSIDE q_induct3R from the run `RealChildA O c y`:
-- runReads_of_run (RR3) gives `shapeEq : machineShape? .. = some d.shape`, `machineShape?_noMemRow` (L2) gives `noMemRowS`.
-- Copies (verbatim except marked): MachPrem3 -> MachPrem3R (third disjunct asks `instFields = []` instead of the origin row),
-- q_induct3 -> q_induct3R (one use), machPrem3_of_t1hyp -> machPrem3R_of_t1hyp, DataRes3 -> DataRes3R (no noMemRow field).
-- No existing file, statement or definition is changed. No sorry / axiom / native_decide.

variable {tenv : Lean.Environment}

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

section HrowRun
open Tools.ShippingChildInv (Res)
open Tools.ShippingKidsChildIface (synthesizeCombinational_designL)
open Tools.ShippingChildVCA
open Tools.ShippingChildBndCore (dv cv)
variable {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **hrow from a run.** If the child `c` has a real run `RealChildA O c y`, the machine shape `sh` of `c`
(`MachineDefines`) is the one `machineShape?` returned in that run (RR3 `shapeEq`), so it passes the final gate of
`machineShape?` (L2), and with `instFields = []` every instance tag is a non-memory origin. -/
theorem nomemO_of_real (O : RefLawsAOps MkRefd mref cref) {c : Name} {sh : MachineShape}
    (entry : MachineDefines mctx mref cctx cref c sh)
    (closes : ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c sh)
    (hf : sh.instFields = []) {y : Res} (h : RealChildA O c y) :
    ∀ x ∈ sh.instTagged, x.2.child?.isNone = true := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    obtain ⟨M, D, w1, hcore, hpost, hdesL⟩ := synthesizeCombinational_designL hr
    have hw : JQ O.quiet (dv w) w := ⟨quiet, synth, rfl⟩
    have hc : CacheInvA O (cv w) := fun c r h => cache c r h
    obtain ⟨_, _, _, _, _, _, hRR, -⟩ := Tools.ShippingGen5RunReads.runReads_of_run O adm hw (Or.inr hc) hcore
      (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx' adm)
    have hrow : Tools.ShippingGen2DataBridge.noMemRowS sh = true :=
      Tools.ShippingGen3HrowGate.machineShape?_noMemRow hRR.shapeEq
    unfold Tools.ShippingGen2DataBridge.noMemRowS at hrow
    rw [hf] at hrow
    have hall : sh.instTagged.all (fun x => x.2.child?.isNone) = true := by simpa using hrow
    intro x hx
    exact List.all_eq_true.mp hall x hx
#print axioms nomemO_of_real
end HrowRun

section Q
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry Tools.ShippingEntrySoundness
open Tools.ShippingCacheCoherentRun (IsMem)
open Tools.ShippingChildInv (Res)
open Sparkle.IR.AST (Stmt)
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
def MachPrem3R {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    (O : RefLawsAOps MkRefd mref cref) (c : Name) (sp : MachineShape) : Prop :=
  ∃ d : MachineData, d.shape = sp ∧ d.ok = true ∧
    d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    (∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width) ∧
    MachineDefines mctx mref cctx cref c d.shape ∧
    ((d.shape.insts = [] ∧ ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context),
        MachineCloses mctx' mref cctx' cref c d.shape) ∨
     (∃ nDecl : Nat, d.callsOk nDecl = true ∧ d.ss.length = d.shape.layout.slots.length ∧
        (∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain) ∧ d.shape.insts ≠ [] ∧ d.shape.instFields ≠ [] ∧
        ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context), AdmCtx O.quiet mctx' cctx' →
          Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape) ∨
     (∃ nDecl : Nat, d.callsOk nDecl = true ∧ d.ss.length = d.shape.layout.slots.length ∧
        (∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain) ∧ d.shape.insts ≠ [] ∧
        d.shape.instFields = [] ∧
        ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context), AdmCtx O.quiet mctx' cctx' →
          Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape))

set_option maxHeartbeats 4000000 in
theorem q_induct3R {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) (hg : GraphAgrees g Reach S)
    (hS : ∀ c, Reach c → ∃ sp, S c = some sp)
    (hprem : ∀ c, Reach c → ∀ sp, S c = some sp → MachPrem3R (mctx := mctx) (cctx := cctx) O c sp)
    (hcl : ReachClosed Reach S) :
    ∀ c, Reach c → ∀ y, RealChildA O c y → QY g c y := by
  obtain ⟨r0, h0, -, -⟩ := Tools.ShippingSrm7Rank.inClass_rank hin
  have key : ∀ r c, Reach c → declRank g B c = some r → ∀ y, RealChildA O c y → QY g c y := by
    intro r
    induction r using Nat.strongRecOn with
    | _ r ih =>
      intro c hc hr y hy
      obtain ⟨sp, hSc⟩ := hS c hc
      -- kids
      have kids : ∀ (k : Nat) (hk : k < sp.insts.length) (y' : Res),
          Tools.ShippingCallsMemA.KidTA O (originAt sp k) (sp.insts[k]'hk).1 y' → KidOK g c y' := by
        intro k hk y' hkid
        rcases hkid with h1 | ⟨hch, hrc⟩
        · obtain ⟨cb, aw, dw, hmo⟩ : ∃ cb aw dw, originAt sp k = .mem cb aw dw := by
            cases ho : originAt sp k with
            | ord => rw [ho] at h1; simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?] at h1
            | field i => rw [ho] at h1; simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?] at h1
            | mem cb aw dw => exact ⟨cb, aw, dw, rfl⟩
          rw [hmo] at h1
          simp only [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?, Option.some.injEq] at h1
          subst h1
          exact memModule_kidOK g c cb aw dw
        · have he := ordEdge_of_idx hg hc hSc hk hch
          obtain ⟨r1, h1, hlt⟩ := rank_of_ordEdge hr he
          have hc' : Reach (sp.insts[k]'hk).1 := hcl c hc sp hSc k hk (by simpa using hch)
          obtain ⟨hn, hd, ho⟩ := ih r1 hlt _ hc' h1 y' hrc
          refine ⟨?_, ho⟩
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact Or.inr ⟨_, strictDesc_of_edge he, hn⟩
          · rcases hd a ha with hm | ⟨c'', hs, hnm⟩
            · exact Or.inl hm
            · exact Or.inr ⟨c'', strictDesc_of_edge_left he hs, hnm⟩
      obtain ⟨d, hdS, ok, hbody, outTy, entry, hcase⟩ := hprem c hc sp hSc
      subst hdS
      rcases hcase with ⟨hno, closes⟩ | ⟨nDecl, hC, hslots, hdomB, hins, hfne, closes⟩ | ⟨nDecl, hC, hslots, hdomB, hins, hfe, closes⟩
      · have I := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O d ok hbody hno outTy entry closes hy
        refine ⟨I.name, ?_, ?_⟩
        · intro a ha; rw [I.design] at ha; simp at ha
        · intro a ha mn i cs hm
          rw [I.design] at ha
          have : a = y.1 := by simpa using ha
          subst this
          have := List.all_eq_true.mp I.seqOk _ hm
          simp [Sparkle.IR.OptCheck.seqStmtOk] at this
      · have hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
            Tools.ShippingCallsMemA.KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y' →
            ∀ a ∈ y'.1 :: y'.2.modules, a.name ≠ ofDecl c :=
          fun k hk y' hkid => kidOK_hsep hin hsp hc (kids k hk y' hkid)
        obtain ⟨-, -, -, -, M, D, -, -, -, -, hpost, hdes, hMn, hb, -, hinst, hreal, -⟩ :=
          Tools.ShippingSrm4Core5.deepChild_ifaceA'M O T d ok hbody hC hslots hdomB hins hfne outTy hsep entry closes hy
        have hname : y.1.name = ofDecl c := by
          rcases hpost with e | e
          · rw [e, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
          · rw [e, Tools.ShippingMachineDepthRun.mergeChecked_name, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
        refine ⟨hname, ?_, ?_⟩
        · intro a ha
          rw [hdes] at ha
          obtain ⟨k, hk, y', hkid, hor, -⟩ := hreal a ha
          have K := kids k hk y' hkid
          refine K.1 a ?_
          rcases hor with rfl | h
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ h
        · intro a ha mn i cs hm
          rcases List.mem_cons.mp ha with rfl | ha
          · rw [hb] at hm
            obtain ⟨mc, hmc⟩ := hinst mn i cs hm
            obtain ⟨hmem, hnm⟩ := moduleByName_spec hmc
            exact ⟨mc, by rw [hdes]; exact hmem, hnm⟩
          · rw [hdes] at ha
            obtain ⟨k, hk, y', hkid, hor, hcov⟩ := hreal a ha
            have K := kids k hk y' hkid
            have ha' : a ∈ y'.1 :: y'.2.modules := by
              rcases hor with rfl | h
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ h
            obtain ⟨g2, hg2, hn2⟩ := K.2 a ha' mn i cs hm
            obtain ⟨g', hg', hn'⟩ := hcov g2 (List.mem_cons_of_mem _ hg2)
            exact ⟨g', by rw [hdes]; exact hg', hn'.trans hn2⟩
      · have hnomemO : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true :=
          nomemO_of_real O entry closes hfe hy
        have hch : ∀ (k : Nat) (hk : k < d.shape.insts.length), (originAt d.shape k).child? = none := by
          intro k hk
          exact Tools.ShippingChildInv.notag_at hnomemO hk
        have hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
            RealChildA O (d.shape.insts[k]).1 y' →
            ∀ a ∈ y'.1 :: y'.2.modules, a.name ≠ ofDecl c :=
          fun k hk y' hrc => kidOK_hsep hin hsp hc (kids k hk y' (Or.inr ⟨hch k hk, hrc⟩))
        obtain ⟨-, -, -, -, M, D, -, -, -, -, hpost, hdes, hMn, hb, -, hinst, hreal, -⟩ :=
          deepChild_ifaceAO O T d ok hbody hC hslots hdomB hins outTy hnomemO hsep entry closes hy
        have hname : y.1.name = ofDecl c := by
          rcases hpost with e | e
          · rw [e, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
          · rw [e, Tools.ShippingMachineDepthRun.mergeChecked_name, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
        refine ⟨hname, ?_, ?_⟩
        · intro a ha
          rw [hdes] at ha
          obtain ⟨k, hk, y', hrc, hor, -⟩ := hreal a ha
          have K := kids k hk y' (Or.inr ⟨hch k hk, hrc⟩)
          refine K.1 a ?_
          rcases hor with rfl | h
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ h
        · intro a ha mn i cs hm
          rcases List.mem_cons.mp ha with rfl | ha
          · rw [hb] at hm
            obtain ⟨mc, hmc⟩ := hinst mn i cs hm
            obtain ⟨hmem, hnm⟩ := moduleByName_spec hmc
            exact ⟨mc, by rw [hdes]; exact hmem, hnm⟩
          · rw [hdes] at ha
            obtain ⟨k, hk, y', hrc, hor, hcov⟩ := hreal a ha
            have K := kids k hk y' (Or.inr ⟨hch k hk, hrc⟩)
            have ha' : a ∈ y'.1 :: y'.2.modules := by
              rcases hor with rfl | h
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ h
            obtain ⟨g2, hg2, hn2⟩ := K.2 a ha' mn i cs hm
            obtain ⟨g', hg', hn'⟩ := hcov g2 (List.mem_cons_of_mem _ hg2)
            exact ⟨g', by rw [hdes]; exact hg', hn'.trans hn2⟩
  intro c hc y hy
  obtain ⟨r, hr, -⟩ := rank_of_reach h0 (hsp c hc)
  exact key r c hc hr y hy

#print axioms q_induct3R
end Q
section S6R
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}

/-- `DataRes3` (this directory) without the `noMemRow` field. -/
structure DataRes3R (DataOk : Pkg ι dom → Prop) : Prop where
  callsRows : ∀ q, DataOk q → q.d.shape.insts ≠ [] →
    q.d.callsOk q.kD = true ∧ q.d.ss.length = q.d.shape.layout.slots.length ∧
      (∀ b ∈ q.d.shape.binders.drop q.kD, b.2 ≠ .domain)
  outTy : ∀ q, DataOk q → ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width
  leafAlias : ∀ q, DataOk q → q.d.shape.insts = [] → q.d.letsAliasOk = true

theorem machPrem3R_of_t1hyp {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (R : DataRes3R DataOk) (hA : AdmCtx L.O.quiet mctx cctx) :
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
#print axioms machPrem3R_of_t1hyp
end S6R

section FinalR
open Tools.ShippingChildInv (Res)
open Sparkle.IR.AST (Stmt)
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}

/-- E-3 and the B3 part from `T1Hyp`, the existing row T1L-12 (`hMemRow`), the row `hLeafAlias`, `AdmCtx` and the E-5
carriers: `auditE3B3_of_t1hyp` WITHOUT `hrow` (T1L-04), which `nomemO_of_real` takes from the run. -/
theorem auditE3B3_of_t1hyp_run {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk)
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
  have Q := q_induct3R L.O L.T hin hsp hg hS (machPrem3R_of_t1hyp H R hA) hcl
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
#print axioms auditE3B3_of_t1hyp_run
end FinalR

end Tools.ShippingGen5AuditE3B3

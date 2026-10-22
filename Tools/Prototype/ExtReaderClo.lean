import Tools.Prototype.ExtReaderDefs

/-! # Unit EXT2 (3/N): the closedness invariant `Clo` of the reader block with the operations `O` (copy of LCQ2's arm proofs)

STATUS: see REPORT-EXT2.md for the build log. The arm proofs are LCQ2's (`Tools/ShippingCloInv.lean`) with the call sites of the operations
turned into `O`. NO premise about `O` is used (the operations act on INPUT subterms the reader reads again), so the theorems hold for an
ARBITRARY `O : ExtOps`. The combinators / helpers that do not mention the operations are LCQ2's, not copied. No sorry / axiom / native_decide. -/

namespace Tools.Prototype.ExtReader
open Lean Sparkle.Compiler.Elab
open Tools.ShippingLetsAliasInv Tools.ShippingReaderFuel Tools.ShippingReaderLenOk
open Tools.ShippingCloInv
open Tools.ShippingLetsReaderInv (SatP satp_pure satp_okO satp_failO satp_optK satp_bindO satp_bind
  satp_ite satp_domGuard satp_pure_ite satp_mono satp_foldO satp_findSomeO)

section Folds
variable {h : Hs}

theorem instArg_cloX (O : ExtOps) (hG : CGood h) (env : List MachVal) (k : Nat) (hE : EnvClo env) :
    ∀ (s : List Nat × MachRead) (a : MixedGateBinder × Lean.Expr), CloSt s.2 →
      SatP h (fun p : List Nat × MachRead => CloSt p.2) (instArgX O env k s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ (hA : CloSt st)
  refine satp_bindO (csat_cConv hG hA hE) ?_
  rintro ⟨v', st1⟩ ⟨(h1 : CloSt st1), (hv' : Clo 0 v' = true)⟩
  refine satp_pure ?_
  intro r hr
  cases kind with
  | domain =>
    try dsimp only at hr
    split at hr
    · split at hr
      · cases hr
      · injection hr with hr
        subst hr
        exact h1
    · injection hr with hr
      subst hr
      exact cloSt_dom h1 (by rfl) (by rfl) (by rfl) hv'
  | bits w =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact cloSt_lets h1 (machLetIndex_clo h1.1 hv') (by rfl) (by rfl)
  | bool =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact cloSt_lets h1 (machLetIndex_clo h1.1 hv') (by rfl) (by rfl)


theorem instSArg_cloX (O : ExtOps) (hG : CGood h) (env : List MachVal) (hE : EnvClo env) :
    ∀ (s : List Nat × MachRead) (a : MixedGateBinder × Lean.Expr), CloSt s.2 →
      SatP h (fun p : List Nat × MachRead => CloSt p.2) (instSArgX O env s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ (hA : CloSt st)
  refine satp_bindO (csat_cConv hG hA hE) ?_
  rintro ⟨v', st1⟩ ⟨(h1 : CloSt st1), (hv' : Clo 0 v' = true)⟩
  refine satp_pure ?_
  intro r hr
  cases kind with
  | domain =>
    try dsimp only at hr
    split at hr
    · split at hr
      · cases hr
      · injection hr with hr
        subst hr
        exact h1
    · injection hr with hr
      subst hr
      exact cloSt_dom h1 (by rfl) (by rfl) (by rfl) hv'
  | bits w =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact cloSt_lets h1 (machLetIndex_clo h1.1 hv') (by rfl) (by rfl)
  | bool =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact cloSt_lets h1 (machLetIndex_clo h1.1 hv') (by rfl) (by rfl)


theorem nestedProbe_cloX (O : ExtOps) (hG : CGood h) (env : List MachVal) (dom' αs initsE body : Lean.Expr)
    (st1 : MachRead) (hr1 : CloSt st1) (hE : EnvClo env) :
    ∀ a, a ∈ st1.nested.toList →
      SatP h (ConvC 0) (nestedProbeX O env dom' αs initsE body st1 a) := by
  rintro ⟨base, d, a, ini, ws, v⟩ hmem
  have hv : Clo 0 v = true := hr1.2.1 _ hmem
  refine satp_ite ?_ satp_failO
  refine satp_bind ?_
  intro r hr
  rcases r with _ | ⟨ws', v', st'⟩
  · exact satp_failO
  · have hc : ChainC (ws', v', st') :=
      csat_cChain hG hr1 (envClo_cons hE (fun w hw => by cases hw)) (ws', v', st') hr
    refine satp_pure_ite ?_
    exact ⟨hc.1, hv⟩

theorem loopProbe_cloX (O : ExtOps) (hG : CGood h) (env : List MachVal) (body : Lean.Expr) (n : Nat)
    (st1 : MachRead) (hr1 : CloSt st1) (hE : EnvClo env) :
    ∀ a, SatP h (fun p : Nat × MachRead => CloSt p.2) (loopProbeX O env body n st1 a) := by
  rintro ⟨b0, n0, ws0⟩
  refine satp_ite satp_failO ?_
  refine satp_bind ?_
  intro r hr
  rcases r with _ | st'
  · exact satp_failO
  · have hz : CloSt { st1 with ws := #[] } := cloSt_congr hr1 (by rfl) (by rfl) (by rfl)
    have hc : CloSt st' :=
      csat_cLoopBody hG hz (envClo_cons hE (fun w hw => by cases hw)) st' hr
    refine satp_pure_ite ?_
    exact cloSt_congr hc (by rfl) (by rfl) (by rfl)

end Folds

section Arms
variable {h : Hs}

/-- `machConv`'s `.app` arm. -/
theorem cconv_app_satX (O : ExtOps) (senv : StructEnv) (hG : CGood h) (env : List MachVal)
    (d : Nat) (f a : Lean.Expr) (st : MachRead) (hst : CloSt st) (hE : EnvClo env) :
    SatP h (ConvC d) (convStepX O senv env d (.app f a) st) := by
  first
    | simp only [convStepX]
    | (unfold convStepX; dsimp only)
  split
  · -- a bare `Signal.register`
    rename_i dom α init x hreg
    refine satp_ite satp_failO ?_
    split
    · exact satp_okO ⟨hst, clo_slot _ _⟩
    · refine satp_optK ?_
      intro kind _
      refine satp_optK ?_
      intro initN _
      refine satp_bindO (csat_cConv hG hst hE) ?_
      rintro ⟨dom', st1⟩ ⟨(h1 : CloSt st1), (hd' : Clo 0 dom' = true)⟩
      refine satp_domGuardX O ?_
      refine satp_bindO (csat_cConv hG (cloSt_dom h1 (by rfl) (by rfl) (by rfl) hd') hE) ?_
      rintro ⟨x', st2⟩ ⟨(h2 : CloSt st2), hx'⟩
      refine satp_okO ⟨?_, clo_slot _ _⟩
      exact cloSt_congr h2 (by rfl) (by rfl) (by rfl)
  · split
    · -- a loop read
      exact satp_pure_ite ⟨hst, clo_slot _ _⟩
    · split
      · -- a nested machine
        exact satp_ite satp_failO (satp_mono (fun p hp => convC_mono hp) (csat_cNested hG hst hE))
      · split
        · -- an instance
          exact satp_ite satp_failO
            (satp_mono (fun p hp => convC_mono hp) (csat_cInst hG hst hE))
        · split
          · -- a structure instance
            exact satp_ite satp_failO
              (satp_mono (fun p hp => convC_mono hp) (csat_cInstS hG hst hE))
          · split
            · -- a memory
              refine satp_ite satp_failO (satp_bindO (csat_cInst hG hst hE) ?_)
              rintro ⟨v, st1⟩ ⟨(h1 : CloSt st1), (hv : Clo 0 v = true)⟩
              exact satp_okO ⟨cloSt_congr h1 (by rfl) (by rfl) (by rfl), clo_zero hv⟩
            · split
              · -- a state read
                exact satp_pure_ite ⟨hst, clo_slot _ _⟩
              · -- an application
                refine satp_bindO (csat_cConv hG hst hE) ?_
                rintro ⟨f', st1⟩ ⟨(h1 : CloSt st1), (hf' : Clo d f' = true)⟩
                refine satp_bindO (csat_cConv hG h1 hE) ?_
                rintro ⟨a', st2⟩ ⟨(h2 : CloSt st2), (ha' : Clo d a' = true)⟩
                exact satp_okO ⟨h2, bundleIota_clo _ _ (projIota_clo _ _ _ (clo_pair hf' ha'))⟩

/-- `machConv`'s `.letE` arm. -/
theorem cconv_letE_satX (O : ExtOps) (senv : StructEnv) (hG : CGood h) (env : List MachVal)
    (d : Nat) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead) (hst : CloSt st)
    (hE : EnvClo env) :
    SatP h (ConvC d) (convStepX O senv env d (.letE nm ty v b nd) st) := by
  refine satp_ite satp_failO ?_
  split
  · exact satp_mono (fun p hp => convC_mono hp) (csat_cConv hG hst hE)
  · refine satp_ite ?_ ?_
    · refine satp_bindO (csat_cLoopRoot hG hst hE) ?_
      rintro ⟨mv, st1⟩ ⟨(h1 : CloSt st1), (hmv : MvClo mv)⟩
      have hEv : EnvClo (mv :: env) := envClo_cons hE (fun w hw => by subst hw; exact hmv)
      exact satp_mono (fun p hp => convC_mono hp) (csat_cConv hG h1 hEv)
    · split
      · exact satp_mono (fun p hp => convC_mono hp)
          (csat_cConv hG hst (envClo_cons hE (fun w hw => by cases hw)))
      · split
        · exact satp_mono (fun p hp => convC_mono hp)
            (csat_cConv hG hst (envClo_cons hE (fun w hw => by cases hw)))
        · refine satp_bindO (csat_cConv hG hst hE) ?_
          rintro ⟨v', st1⟩ ⟨(h1 : CloSt st1), (hv' : Clo 0 v' = true)⟩
          have hB := machBindLet_clo (nm := nm) (ty := ty) h1.1 hv'
          dsimp only
          generalize machBindLet nm ty v' st1.lets = bl at hB ⊢
          obtain ⟨x, lets'⟩ := bl
          have hA : CloSt { st1 with lets := lets' } := cloSt_lets h1 hB.1 (by rfl) (by rfl)
          have hEv : EnvClo (MachVal.val x :: env) :=
            envClo_cons hE (fun w hw => by injection hw with hw; subst hw; exact hB.2)
          show SatP h (ConvC d) (cConv (MachVal.val x :: env) 0 b { st1 with lets := lets' })
          exact satp_mono (fun p hp => convC_mono hp) (csat_cConv hG hA hEv)

/-- `machConv`. -/
theorem cconv_satX (O : ExtOps) (senv : StructEnv) (hG : CGood h) (env : List MachVal)
    (d : Nat) (e : Lean.Expr) (st : MachRead) (hst : CloSt st) (hE : EnvClo env) :
    SatP h (ConvC d) (convStepX O senv env d e st) := by
  cases e
  case bvar j =>
    refine satp_pure ?_
    intro r hr
    obtain ⟨hs, hv⟩ := convBvar_clo hst.2.2 hE hr
    show CloSt r.2 ∧ Clo d r.1 = true
    rw [hs]
    exact ⟨hst, hv⟩
  case app f a => exact cconv_app_satX O senv hG env d f a st hst hE
  case letE nm ty v b nd => exact cconv_letE_satX O senv hG env d nm ty v b nd st hst hE
  case lam nm t b bi =>
    refine satp_bindO (csat_cConv hG hst hE) ?_
    rintro ⟨t', st1⟩ ⟨(h1 : CloSt st1), (ht' : Clo d t' = true)⟩
    refine satp_bindO (csat_cConv hG h1 hE) ?_
    rintro ⟨b', st2⟩ ⟨(h2 : CloSt st2), (hb' : Clo (d + 1) b' = true)⟩
    refine satp_okO ⟨h2, ?_⟩
    show Clo d (.lam nm t' b' bi) = true
    simp only [Clo, Bool.and_eq_true]
    exact ⟨ht', hb'⟩
  case forallE nm t b bi =>
    refine satp_bindO (csat_cConv hG hst hE) ?_
    rintro ⟨t', st1⟩ ⟨(h1 : CloSt st1), (ht' : Clo d t' = true)⟩
    refine satp_bindO (csat_cConv hG h1 hE) ?_
    rintro ⟨b', st2⟩ ⟨(h2 : CloSt st2), (hb' : Clo (d + 1) b' = true)⟩
    refine satp_okO ⟨h2, ?_⟩
    show Clo d (.forallE nm t' b' bi) = true
    simp only [Clo, Bool.and_eq_true]
    exact ⟨ht', hb'⟩
  all_goals first
    | (refine satp_okO ⟨hst, ?_⟩; rfl)
    | exact satp_failO

/-- `machNested`. -/
theorem cnested_satX (O : ExtOps) (senv : StructEnv) (hG : CGood h) (env : List MachVal)
    (dom αs initsE body : Lean.Expr) (st : MachRead) (hst : CloSt st) (hE : EnvClo env) :
    SatP h (ConvC 0) (nestedStepX O senv env dom αs initsE body st) := by
  refine satp_ite satp_failO ?_
  refine satp_bindO (csat_cConv hG hst hE) ?_
  rintro ⟨dom', st1⟩ ⟨(h1 : CloSt st1), (hd' : Clo 0 dom' = true)⟩
  refine satp_bind ?_
  intro shared hsh
  rcases shared with _ | r
  · refine satp_optK ?_
    rintro ⟨base, st2⟩ hres
    obtain ⟨kinds, inits, _, _, _, hst2, _⟩ := machReserveX_some hres
    subst hst2
    have h2 : CloSt (reserved st1 dom' body kinds inits) :=
      cloSt_dom h1 (by rfl) (by rfl) (by rfl) hd'
    refine satp_bindO (csat_cChain hG
      (cloSt_congr h2 (by rfl) (by rfl) (by rfl))
      (envClo_cons hE (fun w hw => by cases hw))) ?_
    rintro ⟨ws, v, st3⟩ ⟨(h3 : CloSt st3), (hv3 : Clo 0 v = true)⟩
    refine satp_okO ⟨?_, hv3⟩
    exact cloSt_nested (e := (base, dom', αs, initsE, ws, v)) h3 (by rfl) (by rfl) (by rfl) hv3
  · have := satp_findSomeO (P := ConvC 0) st1.nested.toList
      (fun a ha => nestedProbe_cloX O hG env dom' αs initsE body st1 h1 hE a ha) r hsh
    exact satp_okO this

/-- `machInstance`. -/
theorem cinst_satX (O : ExtOps) (hG : CGood h) (env : List MachVal) (c : Name)
    (org : Sparkle.Compiler.MachInstOrigin.InstOrigin) (kinds : List MixedGateBinder)
    (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead) (hst : CloSt st)
    (hE : EnvClo env) :
    SatP h (ConvC 0) (instStepX O env c org kinds res args st) := by
  refine satp_optK ?_
  intro st1 hst1
  have h1 : CloSt st1 := instEntry_clo hst hst1
  refine satp_bindO (satp_foldO (P := fun p : List Nat × MachRead => CloSt p.2)
    (kinds.zip args) ([], st1) ?_ h1) ?_
  · intro s a _ hs
    exact instArg_cloX O hG env st1.insts.size hE s a hs
  rintro ⟨js, st2⟩ (h2 : CloSt st2)
  refine satp_pure ?_
  intro r hr
  split at hr
  all_goals first
    | (injection hr with hq; subst hq; exact ⟨h2, clo_inst _ _⟩)
    | (injection hr with hq; subst hq
       exact ⟨cloSt_congr h2 (by rfl) (by rfl) (by rfl), clo_inst _ _⟩)

/-- `machInstanceS`. -/
theorem cinstS_satX (O : ExtOps) (senv : StructEnv) (hG : CGood h) (env : List MachVal)
    (c : Name) (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr)
    (st : MachRead) (hst : CloSt st) (hE : EnvClo env) :
    SatP h (ConvC 0) (instSStepX O senv env c kinds ty args st) := by
  refine satp_ite satp_failO ?_
  refine satp_optK ?_
  intro resTy hres
  refine satp_optK ?_
  intro r _
  obtain ⟨oc, fields⟩ := r
  cases oc with
  | none => exact satp_failO
  | some ctor =>
    refine satp_ite satp_failO ?_
    refine satp_bindO (satp_foldO (P := fun p : List Nat × MachRead => CloSt p.2)
      (kinds.zip args) ([], st) ?_ hst) ?_
    · intro s a _ hs
      exact instSArg_cloX O hG env hE s a hs
    rintro ⟨js, st1⟩ (h1 : CloSt st1)
    refine satp_bindO (satp_foldO
      (P := fun p : List Lean.Expr × MachRead => CloSt p.2 ∧ ∀ q ∈ p.1, Clo 0 q = true)
      resTy.getAppArgs.toList ([], st1) ?_ ⟨h1, by simp⟩) ?_
    · intro s a _ hs
      exact instSParam_sat hG env hE s a hs
    rintro ⟨params, st2⟩ ⟨(h2 : CloSt st2), (hps : ∀ q ∈ params, Clo 0 q = true)⟩
    try dsimp only
    split
    · exact satp_okO ⟨h2, clo_ctorApp _ _ params hps _ _⟩
    · exact satp_okO ⟨cloSt_congr h2 (by rfl) (by rfl) (by rfl), clo_ctorApp _ _ params hps _ _⟩

/-- `machChain`. -/
theorem cchain_satX (O : ExtOps) (senv : StructEnv) (hG : CGood h) (env : List MachVal)
    (e : Lean.Expr) (st : MachRead) (hst : CloSt st) (hE : EnvClo env) :
    SatP h ChainC (chainStepX O senv env e st) := by
  unfold chainStepX
  split
  · refine satp_bindO (csat_cConv hG hst hE) ?_
    rintro ⟨v', st1⟩ ⟨h1, hv'⟩
    exact satp_okO ⟨h1, hv'⟩
  · refine satp_bind ?_
    intro r hr
    have hr' : ∀ a b, r = some (a, b) → ConvC 0 (a, b) := by
      intro a b he
      subst he
      exact csat_cConv hG hst hE (a, b) hr
    revert hr'
    split
    · intro hr'
      have h1 := hr' _ _ rfl
      have h1' : CloSt _ := h1.1
      refine satp_ite ?_ satp_failO
      refine satp_bindO (csat_cChain hG h1'
        (envClo_cons hE (fun w hw => by cases hw))) ?_
      rintro ⟨ws, v, st3⟩ ⟨h2, hv⟩
      exact satp_okO ⟨h2, hv⟩
    · intro _
      exact satp_failO
  · rename_i nm ty v b nd
    split
    · exact csat_cChain hG hst hE
    · refine satp_ite ?_ ?_
      · refine satp_bindO (csat_cLoopRoot hG hst hE) ?_
        rintro ⟨mv, st1⟩ ⟨(h1 : CloSt st1), (hmv : MvClo mv)⟩
        exact csat_cChain hG h1 (envClo_cons hE (fun w hw => by subst hw; exact hmv))
      · split
        · exact csat_cChain hG hst (envClo_cons hE (fun w hw => by cases hw))
        · split
          · exact csat_cChain hG hst (envClo_cons hE (fun w hw => by cases hw))
          · refine satp_bindO (csat_cConv hG hst hE) ?_
            rintro ⟨v', st1⟩ ⟨(h1 : CloSt st1), (hv' : Clo 0 v' = true)⟩
            have hB := machBindLet_clo (nm := nm) (ty := ty) h1.1 hv'
            dsimp only
            generalize machBindLet nm ty v' st1.lets = bl at hB ⊢
            obtain ⟨x, lets'⟩ := bl
            have hA : CloSt { st1 with lets := lets' } := cloSt_lets h1 hB.1 (by rfl) (by rfl)
            have hEv : EnvClo (MachVal.val x :: env) :=
              envClo_cons hE (fun w hw => by injection hw with hw; subst hw; exact hB.2)
            show SatP h ChainC (cChain (MachVal.val x :: env) b { st1 with lets := lets' })
            exact csat_cChain hG hA hEv
  · exact satp_failO

/-- `machLoopRoot`. -/
theorem cloopRoot_satX (O : ExtOps) (senv : StructEnv) (hG : CGood h) (env : List MachVal)
    (e : Lean.Expr) (st : MachRead) (hst : CloSt st) (hE : EnvClo env) :
    SatP h RootC (loopRootStepX O senv env e st) := by
  unfold loopRootStepX
  split
  · rename_i dom body hview
    refine satp_ite satp_failO ?_
    refine satp_optK ?_
    intro regs _
    refine satp_ite satp_failO ?_
    refine satp_optK ?_
    intro kinds _
    refine satp_optK ?_
    intro inits _
    refine satp_bindO (csat_cConv hG hst hE) ?_
    rintro ⟨dom', st1⟩ ⟨(h1 : CloSt st1), (hd' : Clo 0 dom' = true)⟩
    refine satp_domGuardX O ?_
    refine satp_bind ?_
    intro shared hsh
    rcases shared with _ | ⟨b0, st2⟩
    · refine satp_bindO (csat_cLoopBody hG
        (cloSt_dom h1 (by rfl) (by rfl) (by rfl) hd')
        (envClo_cons hE (fun w hw => by cases hw))) ?_
      rintro st3 (h3 : CloSt st3)
      exact satp_okO ⟨cloSt_congr h3 (by rfl) (by rfl) (by rfl), trivial⟩
    · have := satp_findSomeO (P := fun p : Nat × MachRead => CloSt p.2) st1.loopWs.toList
        (fun a _ => loopProbe_cloX O hG env body _ st1 h1 hE a)
        (b0, st2) hsh
      exact satp_okO ⟨this, trivial⟩
  · exact satp_failO

end Arms

/-! ## One step, and the fuel induction -/

/-- **One step keeps the closedness invariant.** -/
theorem cstep_goodX (O : ExtOps) (senv : StructEnv) {h : Hs} (hG : CGood h) :
    CGood (fun c => (stepX O senv c).run h) := by
  intro c hpre v hv
  cases c with
  | conv env d e st =>
    obtain ⟨pa, pb⟩ := hpre
    exact cconv_satX O senv hG env d e st pa pb v hv
  | nested env dom αs initsE body st =>
    obtain ⟨pa, pb⟩ := hpre
    exact cnested_satX O senv hG env dom αs initsE body st pa pb v hv
  | inst env c org kinds res args st =>
    obtain ⟨pa, pb⟩ := hpre
    exact cinst_satX O hG env c org kinds res args st pa pb v hv
  | instS env c kinds ty args st =>
    obtain ⟨pa, pb⟩ := hpre
    exact cinstS_satX O senv hG env c kinds ty args st pa pb v hv
  | chain env e st =>
    obtain ⟨pa, pb⟩ := hpre
    exact cchain_satX O senv hG env e st pa pb v hv
  | loopBody base env e st =>
    obtain ⟨pa, pb⟩ := hpre
    exact cloopBody_sat senv hG base env e st pa pb v hv
  | loopRoot env e st =>
    obtain ⟨pa, pb⟩ := hpre
    exact cloopRoot_satX O senv hG env e st pa pb v hv

/-- **The closedness invariant of the fuel reader, for ALL fuels** (induction on the fuel). -/
theorem readF_cloX (O : ExtOps) (senv : StructEnv) : ∀ n, CGood (readFX O senv n)
  | 0 => fun c _ v hv => by
    have hv' : (none : Option (RB c)) = some (some v) := hv
    cases hv'
  | n + 1 => cstep_goodX O senv (readF_cloX O senv n)

#print axioms readF_cloX

end Tools.Prototype.ExtReader

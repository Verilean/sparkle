import Tools.Prototype.ExtReaderDefs

/-! # Unit EXT2 (2/N): the `LetOk` / `RdOk` invariant of the reader block with the operations `O` (copy of LC3's arm proofs)

STATUS: see REPORT-EXT2.md for the build log. The arm proofs are LC3's (`Tools/ShippingLetsReaderInv.lean`, lines 335–1042) with the
call sites of the operations turned into `O` (`convStepX O`, …); the combinators (`SatP`, `Good`, `ConvOut`, …) and the helper lemmas
that do not mention the operations (`instSParam_sat`, `loopNext_sat`, `convBvar_ok`, `machBindLet_*`, …) are LC3's, not copied.
PREMISES: `PureFactsX O senv`: three operation ranges (`rootFloat`, `lift`, `inst1`, here HYPOTHESES for an arbitrary `O`, PROVED for
`modelOps` by `OpsOk`), `SigTyRange` (INPUT condition) and the PROVED extractor lemmas. No sorry / axiom / native_decide. -/

namespace Tools.Prototype.ExtReader
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
open Tools.ShippingReaderFuelR1 Tools.ShippingReaderLenOk
open Tools.Prototype.ExtModelLetOk

/-- LC3's `PureFacts` with the operation fields stated for `O`. -/
structure PureFactsX (O : ExtOps) (senv : StructEnv) : Prop where
  rootFloat : ∀ v, LetOk 0 v = true → LetOk 0 (O.rootFloat v) = true
  lift : ∀ e, LetOk 0 e = true →
    LetOk 0 (O.lift e 0 1) = true ∧ LetOk 0 (O.lift e 1 1) = true
  inst1 : ∀ n b a, LetOk n b = true → LetOk n a = true → LetOk n (O.inst1 b a) = true
  sigTy : ∀ c kinds ty, senv.instS c = some (kinds, ty) → ∀ n, LetOk n ty = true
  bundleIota : ∀ n e, LetOk n e = true →
    LetOk n (Sparkle.Compiler.MachRawSurface.bundleIota e) = true
  projIota : ∀ n e, LetOk n e = true → LetOk n (machProjIota senv.proj e) = true
  regView : ∀ n fn args d α i x, (∀ a ∈ args, LetOk n a = true) →
    regView? fn args = some (d, α, i, x) → LetOk n d = true ∧ LetOk n x = true
  runApp : ∀ n e dom αs inits body, LetOk n e = true →
    machRunApp? e = some (dom, αs, inits, body) → LetOk n dom = true ∧ LetOk n body = true
  instCall : ∀ n e c kinds res args, LetOk n e = true →
    machInstCall? senv e = some (c, kinds, res, args) → ∀ a ∈ args, LetOk n a = true
  instCallS : ∀ n e c kinds ty args, LetOk n e = true →
    machInstCallS? senv e = some (c, kinds, ty, args) → ∀ a ∈ args, LetOk n a = true
  memCall : ∀ n e combo aw dw dom ops, LetOk n e = true →
    Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) e =
      some (combo, aw, dw, dom, ops) → LetOk n dom = true ∧ ∀ o ∈ ops, LetOk n o = true
  loopView : ∀ n e dom body, LetOk n e = true → loopView? e = some (dom, body) →
    LetOk n dom = true ∧ LetOk n body = true
  letTail : ∀ n e, LetOk n e = true → LetOk n (machLetTail e) = true
  loopRegs : ∀ n e regs, LetOk n e = true → machLoopRegs e = some regs →
    ∀ r ∈ regs, LetOk n r.2.2 = true

/-- The record from the operation ranges and `SigTyRange` (the extractor facts are LC3's PROVED lemmas). -/
theorem pureFactsX_of {O : ExtOps} {senv : StructEnv} (hO : OpsOk O) (hsig : SigTyRange senv) :
    PureFactsX O senv where
  rootFloat := hO.rootFloat
  lift := fun e he => ⟨hO.lift e 0 1 he, hO.lift e 1 1 he⟩
  inst1 := hO.inst1
  sigTy := hsig
  bundleIota := Tools.ShippingLetsReaderInv.bundleIotaRange
  projIota := fun n e he => projIota_ok senv.proj n e he
  regView := fun n fn args d α i x hall h => regView_ok n fn args d α i x hall h
  runApp := fun n e dom αs inits body he h => runApp_ok n e dom αs inits body he h
  instCall := fun n e c kinds res args he h => instCall_ok senv n e c kinds res args he h
  instCallS := fun n e c kinds ty args he h => instCallS_ok senv n e c kinds ty args he h
  memCall := fun n e combo aw dw dom ops he h => memCall_ok _ n e combo aw dw dom ops he h
  loopView := fun n e dom body he h => loopView_ok n e dom body he h
  letTail := fun n e he => letTail_ok n e he
  loopRegs := fun n e regs he h => loopRegs_ok n e regs he h

theorem instRes_okX (O : ExtOps) {senv : StructEnv} (F : PureFactsX O senv) {n : Nat} :
    ∀ (args : List Lean.Expr) (ty r : Lean.Expr), LetOk n ty = true →
      (∀ a ∈ args, LetOk n a = true) → instResX O ty args = some r → LetOk n r = true
  | [], ty, r, ht, _, h => by
    simp only [instResX, Option.some.injEq] at h
    subst h
    exact ht
  | a :: as, ty, r, ht, ha, h => by
    cases ty with
    | forallE nm t b bi =>
      simp only [instResX] at h
      simp only [LetOk, Bool.and_eq_true] at ht
      exact instRes_okX O F as _ r (F.inst1 n b a ht.2 (ha a List.mem_cons_self))
        (fun x hx => ha x (List.mem_cons_of_mem _ hx)) h
    | _ => simp [instResX] at h

section Folds
variable {h : Hs}

/-- `machInstance`'s `foldlM` function (one argument). -/
theorem instArg_satX (O : ExtOps) (hG : Good h) (env : List MachVal) (k : Nat) {s0 : MachRead}
    (hE : EnvOk s0.lets.size env) (args : List Lean.Expr)
    (hargs : ∀ x ∈ args, LetOk 0 x = true) (kinds : List MixedGateBinder) :
    ∀ s a, a ∈ kinds.zip args → Adv s0 s.2 →
      SatP h (fun p : List Nat × MachRead => Adv s0 p.2) (instArgX O env k s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ hmem (hA : Adv s0 st)
  have harg : LetOk 0 arg = true := hargs arg (List.of_mem_zip hmem).2
  refine satp_bindO (sat_cConv hG hA.1 (envOk_mono hA.2 hE) harg) ?_
  rintro ⟨v', st1⟩ ⟨h1, hv'⟩
  have h1' : Adv st st1 := h1
  have hv'' : LetOk st1.lets.size v' = true := hv'
  have hA1 : Adv s0 st1 := adv_trans hA h1'
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
        exact hA1
    · injection hr with hr
      subst hr
      exact adv_dom hA1 (by rfl) (by rfl) (by rfl) hv''
  | bits w =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact adv_lets hA1 (machLetIndex_noAlias hA1.1.1) machLetIndex_size (by rfl) (by rfl)
  | bool =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact adv_lets hA1 (machLetIndex_noAlias hA1.1.1) machLetIndex_size (by rfl) (by rfl)

/-- `machInstanceS`'s first `foldlM` function (one argument). -/
theorem instSArg_satX (O : ExtOps) (hG : Good h) (env : List MachVal) {s0 : MachRead}
    (hE : EnvOk s0.lets.size env) (args : List Lean.Expr)
    (hargs : ∀ x ∈ args, LetOk 0 x = true) (kinds : List MixedGateBinder) :
    ∀ s a, a ∈ kinds.zip args → Adv s0 s.2 →
      SatP h (fun p : List Nat × MachRead => Adv s0 p.2) (instSArgX O env s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ hmem (hA : Adv s0 st)
  have harg : LetOk 0 arg = true := hargs arg (List.of_mem_zip hmem).2
  refine satp_bindO (sat_cConv hG hA.1 (envOk_mono hA.2 hE) harg) ?_
  rintro ⟨v', st1⟩ ⟨h1, hv'⟩
  have h1' : Adv st st1 := h1
  have hv'' : LetOk st1.lets.size v' = true := hv'
  have hA1 : Adv s0 st1 := adv_trans hA h1'
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
        exact hA1
    · injection hr with hr
      subst hr
      exact adv_dom hA1 (by rfl) (by rfl) (by rfl) hv''
  | bits w =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact adv_lets hA1 (machLetIndex_noAlias hA1.1.1) machLetIndex_size (by rfl) (by rfl)
  | bool =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact adv_lets hA1 (machLetIndex_noAlias hA1.1.1) machLetIndex_size (by rfl) (by rfl)

/-- `machNested`'s sharing probe. -/
theorem nestedProbe_satX (O : ExtOps) (hG : Good h) (env : List MachVal) (dom' αs initsE body : Lean.Expr)
    (st1 : MachRead) (hr1 : RdOk st1) (hE : EnvOk st1.lets.size env)
    (hb : LetOk 0 body = true) :
    ∀ a, a ∈ st1.nested.toList →
      SatP h (ConvOut st1) (nestedProbeX O env dom' αs initsE body st1 a) := by
  rintro ⟨base, d, a, ini, ws, v⟩ hmem
  have hv : LetOk st1.lets.size v = true := hr1.2.1 _ hmem
  refine satp_ite ?_ satp_failO
  refine satp_bind ?_
  intro r hr
  rcases r with _ | ⟨ws', v', st'⟩
  · exact satp_failO
  · have hc : ChainOut st1 (ws', v', st') :=
      sat_cChain hG hr1 (envOk_cons hE (fun w hw => by cases hw)) hb (ws', v', st') hr
    refine satp_pure_ite ?_
    exact ⟨hc.1, letOk_mono hc.1.2 _ hv⟩

/-- `machLoopRoot`'s sharing probe. -/
theorem loopProbe_satX (O : ExtOps) (hG : Good h) (env : List MachVal) (body : Lean.Expr) (n : Nat)
    (st1 : MachRead) (hr1 : RdOk st1) (hE : EnvOk st1.lets.size env)
    (hb : LetOk 0 body = true) :
    ∀ a, SatP h (fun p : Nat × MachRead => Adv st1 p.2) (loopProbeX O env body n st1 a) := by
  rintro ⟨b0, n0, ws0⟩
  refine satp_ite satp_failO ?_
  refine satp_bind ?_
  intro r hr
  rcases r with _ | st'
  · exact satp_failO
  · have hz : Adv st1 { st1 with ws := #[] } := adv_congr (adv_refl hr1) (by rfl) (by rfl) (by rfl)
    have hc : Adv { st1 with ws := #[] } st' :=
      sat_cLoopBody hG hz.1 (envOk_cons hE (fun w hw => by cases hw)) hb st' hr
    refine satp_pure_ite ?_
    exact adv_congr (adv_trans hz hc) (by rfl) (by rfl) (by rfl)

end Folds

section Arms
variable {h : Hs}

/-- `machConv`'s `.app` arm. -/
theorem conv_app_satX (O : ExtOps) (senv : StructEnv) (F : PureFactsX O senv) (hG : Good h) (env : List MachVal)
    (d : Nat) (f a : Lean.Expr) (st : MachRead) (hst : RdOk st) (hE : EnvOk st.lets.size env)
    (hl : LetOk 0 (.app f a) = true) :
    SatP h (ConvOut st) (convStepX O senv env d (.app f a) st) := by
  have hfa : LetOk 0 f = true ∧ LetOk 0 a = true := letOk_app.mp hl
  first
    | simp only [convStepX]
    | (unfold convStepX; dsimp only)
  split
  · -- a bare `Signal.register`
    rename_i dom α init x hreg
    have hdx := F.regView 0 _ _ dom α init x (ok_getAppArgs hl) hreg
    refine satp_ite satp_failO ?_
    split
    · exact satp_okO ⟨adv_refl hst, letOk_slot _ _⟩
    · refine satp_optK ?_
      intro kind _
      refine satp_optK ?_
      intro initN _
      refine satp_bindO (sat_cConv hG hst hE hdx.1) ?_
      rintro ⟨dom', st1⟩ ⟨h1, hd'⟩
      have h1' : Adv st st1 := h1
      have hd'' : LetOk st1.lets.size dom' = true := hd'
      refine satp_domGuardX O ?_
      refine satp_bindO (sat_cConv hG
        (rdOk_dom h1'.1 (by rfl) (by rfl) (by rfl) hd'') (envOk_mono h1'.2 hE) hdx.2) ?_
      rintro ⟨x', st2⟩ ⟨h2, hx'⟩
      refine satp_okO ⟨?_, letOk_slot _ _⟩
      exact adv_congr (adv_trans (adv_dom h1' (by rfl) (by rfl) (by rfl) hd'') h2)
        (by rfl) (by rfl) (by rfl)
  · split
    · -- a loop read
      exact satp_pure_ite ⟨adv_refl hst, letOk_slot _ _⟩
    · split
      · -- a nested machine
        rename_i dom αs initsE body hrun
        have hdb := F.runApp 0 _ dom αs initsE body hl hrun
        exact satp_ite satp_failO (sat_cNested hG hst hE hdb.1 hdb.2)
      · split
        · -- an instance
          rename_i c kinds res args hic
          exact satp_ite satp_failO (sat_cInst hG hst hE (F.instCall 0 _ c kinds res args hl hic))
        · split
          · -- a structure instance
            rename_i c kinds ty args hic
            exact satp_ite satp_failO (sat_cInstS hG hst hE
              (F.instCallS 0 _ c kinds ty args hl hic)
              (F.sigTy c kinds ty (machInstCallS?_instS hic) 0))
          · split
            · -- a memory
              rename_i combo aw dw dom ops hmem
              have hm := F.memCall 0 _ combo aw dw dom ops hl hmem
              refine satp_ite satp_failO (satp_bindO (sat_cInst hG hst hE ?_) ?_)
              · intro x hx
                rcases List.mem_cons.mp hx with rfl | hx
                · exact hm.1
                · exact hm.2 x hx
              · rintro ⟨v, st1⟩ ⟨h1, hv⟩
                exact satp_okO ⟨adv_congr h1 (by rfl) (by rfl) (by rfl), hv⟩
            · split
              · -- a state read
                exact satp_pure_ite ⟨adv_refl hst, letOk_slot _ _⟩
              · -- an application
                refine satp_bindO (sat_cConv hG hst hE hfa.1) ?_
                rintro ⟨f', st1⟩ ⟨h1, hf'⟩
                have h1' : Adv st st1 := h1
                refine satp_bindO (sat_cConv hG h1'.1 (envOk_mono h1'.2 hE) hfa.2) ?_
                rintro ⟨a', st2⟩ ⟨h2, ha'⟩
                have h2' : Adv st1 st2 := h2
                refine satp_okO ⟨adv_trans h1' h2', ?_⟩
                have hf'' : LetOk st1.lets.size f' = true := hf'
                have ha'' : LetOk st2.lets.size a' = true := ha'
                exact F.bundleIota _ _ (F.projIota _ _
                  (letOk_pair (letOk_mono h2'.2 _ hf'') ha''))

/-- `machConv`'s `.letE` arm. -/
theorem conv_letE_satX (O : ExtOps) (senv : StructEnv) (F : PureFactsX O senv) (hG : Good h) (env : List MachVal)
    (d : Nat) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead) (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 (.letE nm ty v b nd) = true) :
    SatP h (ConvOut st) (convStepX O senv env d (.letE nm ty v b nd) st) := by
  have hl' : (LetOk 0 ty = true ∧ LetOk 0 v = true) ∧ LetOk 0 b = true := by
    simpa [LetOk] using hl
  refine satp_ite satp_failO ?_
  split
  · rename_i n2 t2 v2 w nd2 heq
    have hrf := F.rootFloat v hl'.1.2
    rw [heq] at hrf
    simp only [LetOk, Bool.and_eq_true] at hrf
    have hc : LetOk 0 (.letE n2 t2 v2 (.letE nm (O.lift ty 0 1) w (O.lift b 1 1) nd)
        nd2) = true := by
      simp only [LetOk, Bool.and_eq_true]
      exact ⟨⟨hrf.1.1, hrf.1.2⟩, ⟨⟨(F.lift ty hl'.1.1).1, hrf.2⟩, (F.lift b hl'.2).2⟩⟩
    exact sat_cConv hG hst hE hc
  · have hvv : LetOk 0 (O.rootFloat v) = true :=
      F.rootFloat v hl'.1.2
    refine satp_ite ?_ ?_
    · refine satp_bindO (sat_cLoopRoot hG hst hE hvv) ?_
      rintro ⟨mv, st1⟩ ⟨h1, hmv⟩
      have h1' : Adv st st1 := h1
      have hEv : EnvOk st1.lets.size (mv :: env) :=
        envOk_cons (envOk_mono h1'.2 hE) (fun w hw => by subst hw; exact hmv)
      exact satp_mono (fun p hp => convOut_trans h1' hp) (sat_cConv hG h1'.1 hEv hl'.2)
    · split
      · exact sat_cConv hG hst (envOk_cons hE (fun w hw => by cases hw)) hl'.2
      · split
        · exact sat_cConv hG hst (envOk_cons hE (fun w hw => by cases hw)) hl'.2
        · refine satp_bindO (sat_cConv hG hst hE hvv) ?_
          rintro ⟨v', st1⟩ ⟨h1, hv'⟩
          have h1' : Adv st st1 := h1
          have hv'' : LetOk st1.lets.size v' = true := hv'
          have hN := machBindLet_noAlias (nm := nm) (ty := ty) (v' := v') h1'.1.1
          have hR := machBindLet_range (nm := nm) (ty := ty) (v' := v') hv''
          dsimp only
          generalize machBindLet nm ty v' st1.lets = bl at hN hR ⊢
          obtain ⟨x, lets'⟩ := bl
          have hA : Adv st { st1 with lets := lets' } := adv_lets h1' hN hR.1 (by rfl) (by rfl)
          have hEv : EnvOk (({ st1 with lets := lets' } : MachRead).lets.size) (MachVal.val x :: env) :=
            envOk_cons (envOk_mono (Nat.le_trans h1'.2 hR.1) hE)
              (fun w hw => by injection hw with hw; subst hw; exact hR.2)
          show SatP h (ConvOut st) (cConv (MachVal.val x :: env) 0 b { st1 with lets := lets' })
          exact satp_mono (fun p hp => convOut_trans hA hp) (sat_cConv hG hA.1 hEv hl'.2)

/-- `machConv`. -/
theorem conv_satX (O : ExtOps) (senv : StructEnv) (F : PureFactsX O senv) (hG : Good h) (env : List MachVal)
    (d : Nat) (e : Lean.Expr) (st : MachRead) (hst : RdOk st) (hE : EnvOk st.lets.size env)
    (hl : LetOk 0 e = true) : SatP h (ConvOut st) (convStepX O senv env d e st) := by
  cases e
  case bvar j =>
    refine satp_pure ?_
    intro r hr
    obtain ⟨hs, hv⟩ := convBvar_ok hst.2.2 hE hr
    show Adv st r.2 ∧ LetOk r.2.lets.size r.1 = true
    rw [hs]
    exact ⟨adv_refl hst, hv⟩
  case app f a => exact conv_app_satX O senv F hG env d f a st hst hE hl
  case letE nm ty v b nd => exact conv_letE_satX O senv F hG env d nm ty v b nd st hst hE hl
  case lam nm t b bi =>
    have hl' : LetOk 0 t = true ∧ LetOk 0 b = true := by simpa [LetOk] using hl
    refine satp_bindO (sat_cConv hG hst hE hl'.1) ?_
    rintro ⟨t', st1⟩ ⟨h1, ht'⟩
    have h1' : Adv st st1 := h1
    have ht'' : LetOk st1.lets.size t' = true := ht'
    refine satp_bindO (sat_cConv hG h1'.1 (envOk_mono h1'.2 hE) hl'.2) ?_
    rintro ⟨b', st2⟩ ⟨h2, hb'⟩
    have h2' : Adv st1 st2 := h2
    have hb'' : LetOk st2.lets.size b' = true := hb'
    refine satp_okO ⟨adv_trans h1' h2', ?_⟩
    show LetOk st2.lets.size (.lam nm t' b' bi) = true
    simp only [LetOk, Bool.and_eq_true]
    exact ⟨letOk_mono h2'.2 _ ht'', hb''⟩
  case forallE nm t b bi =>
    have hl' : LetOk 0 t = true ∧ LetOk 0 b = true := by simpa [LetOk] using hl
    refine satp_bindO (sat_cConv hG hst hE hl'.1) ?_
    rintro ⟨t', st1⟩ ⟨h1, ht'⟩
    have h1' : Adv st st1 := h1
    have ht'' : LetOk st1.lets.size t' = true := ht'
    refine satp_bindO (sat_cConv hG h1'.1 (envOk_mono h1'.2 hE) hl'.2) ?_
    rintro ⟨b', st2⟩ ⟨h2, hb'⟩
    have h2' : Adv st1 st2 := h2
    have hb'' : LetOk st2.lets.size b' = true := hb'
    refine satp_okO ⟨adv_trans h1' h2', ?_⟩
    show LetOk st2.lets.size (.forallE nm t' b' bi) = true
    simp only [LetOk, Bool.and_eq_true]
    exact ⟨letOk_mono h2'.2 _ ht'', hb''⟩
  all_goals first
    | (refine satp_okO ⟨adv_refl hst, letOk_zero hl⟩)
    | exact satp_failO

/-- `machNested`. -/
theorem nested_satX (O : ExtOps) (senv : StructEnv) (hG : Good h) (env : List MachVal)
    (dom αs initsE body : Lean.Expr) (st : MachRead) (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hd : LetOk 0 dom = true) (hb : LetOk 0 body = true) :
    SatP h (ConvOut st) (nestedStepX O senv env dom αs initsE body st) := by
  refine satp_ite satp_failO ?_
  refine satp_bindO (sat_cConv hG hst hE hd) ?_
  rintro ⟨dom', st1⟩ ⟨h1, hd'⟩
  have h1' : Adv st st1 := h1
  have hd'' : LetOk st1.lets.size dom' = true := hd'
  refine satp_bind ?_
  intro shared hsh
  rcases shared with _ | r
  · refine satp_optK ?_
    rintro ⟨base, st2⟩ hres
    obtain ⟨kinds, inits, _, _, _, hst2, _⟩ := machReserveX_some hres
    subst hst2
    have h2 : Adv st1 (reserved st1 dom' body kinds inits) :=
      adv_dom (adv_refl h1'.1) (by rfl) (by rfl) (by rfl) hd''
    refine satp_bindO (sat_cChain hG
      (rdOk_congr h2.1 (by rfl) (by rfl) (by rfl))
      (envOk_cons (envOk_mono h1'.2 hE) (fun w hw => by cases hw)) hb) ?_
    rintro ⟨ws, v, st3⟩ ⟨h3, hv3⟩
    have h3' : Adv st1 st3 := adv_trans (adv_congr h2 (by rfl) (by rfl) (by rfl)) h3
    have hst3 : Adv st st3 := adv_trans h1' h3'
    have hv3' : LetOk st3.lets.size v = true := hv3
    refine satp_okO ⟨?_, hv3'⟩
    exact adv_nested (e := (base, dom', αs, initsE, ws, v)) hst3 (by rfl) (by rfl) (by rfl) hv3'
  · have := satp_findSomeO (P := ConvOut st1) st1.nested.toList
      (fun a ha => nestedProbe_satX O hG env dom' αs initsE body st1 h1'.1
        (envOk_mono h1'.2 hE) hb a ha) r hsh
    exact satp_okO (convOut_trans h1' this)

/-- `machInstance`. -/
theorem inst_satX (O : ExtOps) (hG : Good h) (env : List MachVal) (c : Name)
    (org : Sparkle.Compiler.MachInstOrigin.InstOrigin) (kinds : List MixedGateBinder)
    (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead) (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (ha : ∀ a ∈ args, LetOk 0 a = true) :
    SatP h (ConvOut st) (instStepX O env c org kinds res args st) := by
  refine satp_optK ?_
  intro st1 hst1
  have h1 : Adv st st1 := instEntry_adv (adv_refl hst) hst1
  refine satp_bindO (satp_foldO (P := fun p : List Nat × MachRead => Adv st p.2)
    (kinds.zip args) ([], st1) ?_ h1) ?_
  · intro s a hmem hs
    exact instArg_satX O hG env st1.insts.size hE args ha kinds s a hmem hs
  rintro ⟨js, st2⟩ (h2 : Adv st st2)
  refine satp_pure ?_
  intro r hr
  split at hr
  all_goals first
    | (injection hr with hq; subst hq; exact ⟨h2, letOk_inst _ _⟩)
    | (injection hr with hq; subst hq
       exact ⟨adv_congr h2 (by rfl) (by rfl) (by rfl), letOk_inst _ _⟩)

/-- `machInstanceS`. -/
theorem instS_satX (O : ExtOps) (senv : StructEnv) (F : PureFactsX O senv) (hG : Good h) (env : List MachVal)
    (c : Name) (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr)
    (st : MachRead) (hst : RdOk st) (hE : EnvOk st.lets.size env)
    (ha : ∀ a ∈ args, LetOk 0 a = true) (ht : LetOk 0 ty = true) :
    SatP h (ConvOut st) (instSStepX O senv env c kinds ty args st) := by
  refine satp_ite satp_failO ?_
  refine satp_optK ?_
  intro resTy hres
  have hres0 : LetOk 0 resTy = true := instRes_okX O F args ty resTy ht ha hres
  refine satp_optK ?_
  intro r _
  obtain ⟨oc, fields⟩ := r
  cases oc with
  | none => exact satp_failO
  | some ctor =>
    refine satp_ite satp_failO ?_
    refine satp_bindO (satp_foldO (P := fun p : List Nat × MachRead => Adv st p.2)
      (kinds.zip args) ([], st) ?_ (adv_refl hst)) ?_
    · intro s a hmem hs
      exact instSArg_satX O hG env hE args ha kinds s a hmem hs
    rintro ⟨js, st1⟩ (h1 : Adv st st1)
    refine satp_bindO (satp_foldO
      (P := fun p : List Lean.Expr × MachRead =>
        Adv st p.2 ∧ ∀ q ∈ p.1, LetOk p.2.lets.size q = true)
      resTy.getAppArgs.toList ([], st1) ?_ ⟨h1, by simp⟩) ?_
    · intro s a hmem hs
      exact instSParam_sat hG env hE resTy.getAppArgs.toList
        (fun q hq => ok_getAppArgs hres0 q (Array.mem_toList_iff.mp hq)) s a hmem hs
    rintro ⟨params, st2⟩ ⟨(h2 : Adv st st2), (hps : ∀ q ∈ params, LetOk st2.lets.size q = true)⟩
    try dsimp only
    split
    · exact satp_okO ⟨h2, ok_ctorApp _ _ params hps _ _⟩
    · exact satp_okO ⟨adv_congr h2 (by rfl) (by rfl) (by rfl), ok_ctorApp _ _ params hps _ _⟩

/-- `machChain`. -/
theorem chain_satX (O : ExtOps) (senv : StructEnv) (F : PureFactsX O senv) (hG : Good h) (env : List MachVal)
    (e : Lean.Expr) (st : MachRead) (hst : RdOk st) (hE : EnvOk st.lets.size env)
    (hl : LetOk 0 e = true) : SatP h (ChainOut st) (chainStepX O senv env e st) := by
  revert hl
  unfold chainStepX
  split
  · intro hl
    simp only [LetOk, Bool.and_eq_true] at hl
    refine satp_bindO (sat_cConv hG hst hE (by okh)) ?_
    rintro ⟨v', st1⟩ ⟨h1, hv'⟩
    exact satp_okO ⟨h1, hv'⟩
  · intro hl
    simp only [LetOk, Bool.and_eq_true] at hl
    refine satp_bind ?_
    intro r hr
    have hr' : ∀ a b, r = some (a, b) → ConvOut st (a, b) := by
      intro a b he
      subst he
      exact sat_cConv hG hst hE (by okh) (a, b) hr
    revert hr'
    split
    · intro hr'
      have h1 := hr' _ _ rfl
      have h1' : Adv st _ := h1.1
      refine satp_ite ?_ satp_failO
      refine satp_bindO (sat_cChain hG h1'.1 (envOk_cons (envOk_mono h1'.2 hE)
        (fun w hw => by cases hw)) (by okh)) ?_
      rintro ⟨ws, v, st3⟩ ⟨h2, hv⟩
      exact satp_okO ⟨adv_trans h1' h2, hv⟩
    · intro _
      exact satp_failO
  · intro hl
    rename_i nm ty v b nd
    have hl' : (LetOk 0 ty = true ∧ LetOk 0 v = true) ∧ LetOk 0 b = true := by
      simpa [LetOk] using hl
    split
    · rename_i n2 t2 v2 w nd2 heq
      have hrf := F.rootFloat v hl'.1.2
      rw [heq] at hrf
      simp only [LetOk, Bool.and_eq_true] at hrf
      have hc : LetOk 0 (.letE n2 t2 v2 (.letE nm (O.lift ty 0 1) w (O.lift b 1 1) nd)
          nd2) = true := by
        simp only [LetOk, Bool.and_eq_true]
        exact ⟨⟨hrf.1.1, hrf.1.2⟩, ⟨⟨(F.lift ty hl'.1.1).1, hrf.2⟩, (F.lift b hl'.2).2⟩⟩
      exact sat_cChain hG hst hE hc
    · have hvv : LetOk 0 (O.rootFloat v) = true :=
        F.rootFloat v hl'.1.2
      refine satp_ite ?_ ?_
      · refine satp_bindO (sat_cLoopRoot hG hst hE hvv) ?_
        rintro ⟨mv, st1⟩ ⟨h1, hmv⟩
        have h1' : Adv st st1 := h1
        have hEv : EnvOk st1.lets.size (mv :: env) :=
          envOk_cons (envOk_mono h1'.2 hE) (fun w hw => by subst hw; exact hmv)
        exact satp_mono (fun p hp => chainOut_trans h1' hp) (sat_cChain hG h1'.1 hEv hl'.2)
      · split
        · exact sat_cChain hG hst (envOk_cons hE (fun w hw => by cases hw)) hl'.2
        · split
          · exact sat_cChain hG hst (envOk_cons hE (fun w hw => by cases hw)) hl'.2
          · refine satp_bindO (sat_cConv hG hst hE hvv) ?_
            rintro ⟨v', st1⟩ ⟨h1, hv'⟩
            have h1' : Adv st st1 := h1
            have hv'' : LetOk st1.lets.size v' = true := hv'
            have hN := machBindLet_noAlias (nm := nm) (ty := ty) (v' := v') h1'.1.1
            have hR := machBindLet_range (nm := nm) (ty := ty) (v' := v') hv''
            dsimp only
            generalize machBindLet nm ty v' st1.lets = bl at hN hR ⊢
            obtain ⟨x, lets'⟩ := bl
            have hA : Adv st { st1 with lets := lets' } := adv_lets h1' hN hR.1 (by rfl) (by rfl)
            have hEv : EnvOk (({ st1 with lets := lets' } : MachRead).lets.size)
                (MachVal.val x :: env) :=
              envOk_cons (envOk_mono (Nat.le_trans h1'.2 hR.1) hE)
                (fun w hw => by injection hw with hw; subst hw; exact hR.2)
            show SatP h (ChainOut st) (cChain (MachVal.val x :: env) b { st1 with lets := lets' })
            exact satp_mono (fun p hp => chainOut_trans hA hp) (sat_cChain hG hA.1 hEv hl'.2)
  · intro _
    exact satp_failO

/-- `machLoopBody`. -/
theorem loopBody_satX (O : ExtOps) (senv : StructEnv) (F : PureFactsX O senv) (hG : Good h) (base : Nat)
    (env : List MachVal) (e : Lean.Expr) (st : MachRead) (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true) :
    SatP h (BodyOut st) (loopBodyStep base env e st) := by
  cases e
  case letE nm ty v b nd =>
    have hl' : (LetOk 0 ty = true ∧ LetOk 0 v = true) ∧ LetOk 0 b = true := by
      simpa [LetOk] using hl
    refine satp_bindO (sat_cConv hG hst hE hl'.1.2) ?_
    rintro ⟨v', st1⟩ ⟨h1, hv'⟩
    have h1' : Adv st st1 := h1
    have hv'' : LetOk st1.lets.size v' = true := hv'
    have hF := loopLet_facts (nm := nm) (ty := ty) (v' := v') h1'.1.1 hv''
    dsimp only
    generalize (if machIsSlot v' then machBindLetNamed nm ty v' st1.lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' st1.lets
      else machBindLet nm ty v' st1.lets) = bl at hF ⊢
    obtain ⟨x, lets'⟩ := bl
    have hA : Adv st { st1 with lets := lets' } := adv_lets h1' hF.1 hF.2.1 (by rfl) (by rfl)
    have hEv : EnvOk (({ st1 with lets := lets' } : MachRead).lets.size) (MachVal.val x :: env) :=
      envOk_cons (envOk_mono (Nat.le_trans h1'.2 hF.2.1) hE)
        (fun w hw => by injection hw with hw; subst hw; exact hF.2.2)
    show SatP h (BodyOut st) (cLoopBody base (MachVal.val x :: env) b { st1 with lets := lets' })
    exact satp_mono (fun p hp => adv_trans hA hp) (sat_cLoopBody hG hA.1 hEv hl'.2)
  all_goals
    unfold loopBodyStep
    try dsimp only
    refine satp_optK ?_
    intro regs hregs
    have hr := F.loopRegs 0 _ regs hl hregs
    refine satp_bindO (satp_foldO (P := fun p : List (Nat × Lean.Expr) × MachRead => Adv st p.2)
      regs ([], st) ?_ (adv_refl hst)) ?_
    · intro s a hmem hs
      exact loopNext_sat hG env base hE regs hr s a hmem hs
    rintro ⟨ws, st1⟩ (h1 : Adv st st1)
    exact satp_okO (adv_congr h1 (by rfl) (by rfl) (by rfl))

/-- `machLoopRoot`. -/
theorem loopRoot_satX (O : ExtOps) (senv : StructEnv) (F : PureFactsX O senv) (hG : Good h) (env : List MachVal)
    (e : Lean.Expr) (st : MachRead) (hst : RdOk st) (hE : EnvOk st.lets.size env)
    (hl : LetOk 0 e = true) : SatP h (RootOut st) (loopRootStepX O senv env e st) := by
  unfold loopRootStepX
  split
  · rename_i dom body hview
    have hdb := F.loopView 0 e dom body hl hview
    refine satp_ite satp_failO ?_
    refine satp_optK ?_
    intro regs _
    refine satp_ite satp_failO ?_
    refine satp_optK ?_
    intro kinds _
    refine satp_optK ?_
    intro inits _
    refine satp_bindO (sat_cConv hG hst hE hdb.1) ?_
    rintro ⟨dom', st1⟩ ⟨h1, hd'⟩
    have h1' : Adv st st1 := h1
    have hd'' : LetOk st1.lets.size dom' = true := hd'
    refine satp_domGuardX O ?_
    refine satp_bind ?_
    intro shared hsh
    rcases shared with _ | ⟨b0, st2⟩
    · have h2 : Adv st1 { st1 with
          kinds := st1.kinds ++ kinds.toArray
          inits := st1.inits ++ inits.toArray
          names := st1.names ++ ((List.range kinds.length).map fun i =>
            Name.mkSimple s!"loop{st1.loops.size}_r{i}").toArray
          dom := some dom'
          loops := st1.loops.push (st1.kinds.size, kinds.length)
          nestedLoops := if st1.loopDepth ≥ 1 then st1.nestedLoops + 1 else st1.nestedLoops
          loopDepth := st1.loopDepth + 1 } :=
        adv_dom (adv_refl h1'.1) (by rfl) (by rfl) (by rfl) hd''
      refine satp_bindO (sat_cLoopBody hG h2.1
        (envOk_cons (envOk_mono h1'.2 hE) (fun w hw => by cases hw)) hdb.2) ?_
      rintro st3 (h3 : Adv _ st3)
      exact satp_okO ⟨adv_congr (adv_trans h1' (adv_trans h2 h3)) (by rfl) (by rfl) (by rfl),
        trivial⟩
    · have := satp_findSomeO (P := fun p : Nat × MachRead => Adv st1 p.2) st1.loopWs.toList
        (fun a _ => loopProbe_satX O hG env body _ st1 h1'.1 (envOk_mono h1'.2 hE) hdb.2 a)
        (b0, st2) hsh
      exact satp_okO ⟨adv_trans h1' this, trivial⟩
  · exact satp_failO

end Arms

/-! ## One step, and the fuel induction -/

/-- **One step keeps the joint invariant**: if the table keeps it, the body run against the table keeps it. -/
theorem step_goodX (O : ExtOps) (senv : StructEnv) (F : PureFactsX O senv) {h : Hs} (hG : Good h) :
    Good (fun c => (stepX O senv c).run h) := by
  intro c hpre v hv
  cases c with
  | conv env d e st =>
    obtain ⟨pa, pb, pc⟩ := hpre
    exact conv_satX O senv F hG env d e st pa pb pc v hv
  | nested env dom αs initsE body st =>
    obtain ⟨pa, pb, pc, pd⟩ := hpre
    exact nested_satX O senv hG env dom αs initsE body st pa pb pc pd v hv
  | inst env c org kinds res args st =>
    obtain ⟨pa, pb, pc⟩ := hpre
    exact inst_satX O hG env c org kinds res args st pa pb pc v hv
  | instS env c kinds ty args st =>
    obtain ⟨pa, pb, pc, pd⟩ := hpre
    exact instS_satX O senv F hG env c kinds ty args st pa pb pc pd v hv
  | chain env e st =>
    obtain ⟨pa, pb, pc⟩ := hpre
    exact chain_satX O senv F hG env e st pa pb pc v hv
  | loopBody base env e st =>
    obtain ⟨pa, pb, pc⟩ := hpre
    exact loopBody_satX O senv F hG base env e st pa pb pc v hv
  | loopRoot env e st =>
    obtain ⟨pa, pb, pc⟩ := hpre
    exact loopRoot_satX O senv F hG env e st pa pb pc v hv

/-- **The joint invariant of the fuel reader, for ALL fuels** (induction on the fuel). -/
theorem readF_goodX (O : ExtOps) (senv : StructEnv) (F : PureFactsX O senv) : ∀ n, Good (readFX O senv n)
  | 0 => fun c _ v hv => by
    have hv' : (none : Option (RB c)) = some (some v) := hv
    cases hv'
  | n + 1 => step_goodX O senv F (readF_goodX O senv F n)


#print axioms readF_goodX

end Tools.Prototype.ExtReader

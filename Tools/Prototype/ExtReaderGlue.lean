import Tools.Prototype.ExtReaderLetOk
import Tools.Prototype.ExtReaderClo
import Tools.Prototype.ExtReaderDom
import Tools.Prototype.ExtReaderRaw

/-! # Unit EXT2 (6/N): the wrapper-level facts of the reader with the operations `O` (copies of LC12 / LCC / LCQ2 glue)

STATUS: see REPORT-EXT2.md for the build log. Block-only call table `btabX O senv n`. Copies, with `wtab` ↦ `btabX O`, `machXxxF` ↦
`readFX O senv n (Call.xxx …)`, `PureFacts` ↦ `PureFactsX O`, of: `shapeStart_ok`, `shapeRootLet_ok`, `rootLets_ok`, `shapeBody_ok`,
`shapeMid_wrap_ok`, `shapeMid_ok`, `shapeStart_clo`, `shapeRootLet_clo`, `rootLets_clo`, `shapeBody_clo`, and of the normaliser's
`LetOk 0` proof (`normStepP_ok` …) for `normStepX O`. No sorry / axiom / native_decide. -/

namespace Tools.Prototype.ExtReader
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
  Tools.Prototype.NormNodeModelLetOk Tools.Prototype.ReaderLfp Lean.Order
open Tools.ShippingReaderFuelShapeR5 Tools.ShippingReaderLenOk
open Tools.ShippingCloInv
open Tools.Prototype.ReaderClosed Tools.Prototype.ReaderTyped
open Tools.Prototype.NormStepModel Tools.Prototype.ExtModelLetOk
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMixedSourceBridge

/-! ## the posts of the block for the operations `O` -/

section Posts
variable {O : ExtOps} {senv : StructEnv} (F : PureFactsX O senv)
include F

theorem machConvFX_post {n : Nat} {env : List MachVal} {d : Nat} {e : Lean.Expr} {st st' : MachRead} {r : Lean.Expr}
    (hst : RdOk st) (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : readFX O senv n (Call.conv env d e st) = some (some (r, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size r = true := by
  have := readF_goodX O senv F n (Call.conv env d e st) ⟨hst, hE, hl⟩ (r, st') h
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem machChainFX_post {n : Nat} {env : List MachVal} {e : Lean.Expr}
    {st st' : MachRead} {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : readFX O senv n (Call.chain env e st) = some (some (ws, v, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size v = true := by
  have := readF_goodX O senv F n (Call.chain env e st) ⟨hst, hE, hl⟩ (ws, v, st') h
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem machLoopRootFX_post {n : Nat} {env : List MachVal} {e : Lean.Expr}
    {st st' : MachRead} {mv : MachVal} (hst : RdOk st) (hE : EnvOk st.lets.size env)
    (hl : LetOk 0 e = true) (h : readFX O senv n (Call.loopRoot env e st) = some (some (mv, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ MvOk st'.lets.size mv := by
  have := readF_goodX O senv F n (Call.loopRoot env e st) ⟨hst, hE, hl⟩ (mv, st') h
  exact ⟨this.1.1, this.1.2, this.2⟩

/-! ## the phases of the wrapper keep `RdOk` (LC12) -/

omit F in
theorem shapeStart_okX {n : Nat} {m : ShapeMid} {st0 : MachRead}
    (hs : ∀ dom αs initsE body dom' stc, m.run? = some (dom, αs, initsE, body) →
      readFX O senv n (Call.conv (m.rootLets.map fun _ => MachVal.unit) 0 dom ({} : MachRead)) =
        some (some (dom', stc)) → LetOk 0 dom' = true)
    (hr : (shapeStart senv m).run (btabX O senv n) = some (some st0)) : RdOk st0 := by
  rcases shapeStart_invT hr with ⟨_, h0⟩ | ⟨dom, αs, initsE, body, dom', stc, base, hm, hc, hres⟩
  · rw [h0]; exact rdOk_init
  · obtain ⟨kinds, inits, _, _, _, hst⟩ := machReserve_some hres
    subst hst
    exact rdOk_dom (rdOk_init) (by rfl) (by rfl) (d := dom') (by rfl)
      (letOk_zero (hs dom αs initsE body dom' stc hm hc))

theorem shapeRootLet_okX {n : Nat} (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr)
    (s' : List MachVal × MachRead) (hs : RdOk s.2 ∧ EnvOk s.2.lets.size s.1)
    (ha : LetOk 0 a.2.2 = true)
    (hr : (shapeRootLet senv s a).run (btabX O senv n) = some (some s')) :
    RdOk s'.2 ∧ EnvOk s'.2.lets.size s'.1 ∧ s.2.lets.size ≤ s'.2.lets.size := by
  obtain ⟨env, st⟩ := s
  obtain ⟨nm, ty, v⟩ := a
  obtain ⟨hst, hE⟩ := hs
  have hl : LetOk 0 v = true := ha
  first
    | (simp only [shapeRootLet] at hr)
    | (unfold shapeRootLet at hr; try dsimp only at hr)
  split at hr
  · obtain ⟨⟨mv, st2⟩, hl2, hr⟩ := bindO_some_inv hr
    have hp := machLoopRootFX_post F hst hE hl hl2
    try dsimp only at hr
    have e := okO_run_inv hr
    subst e
    exact ⟨hp.1, envOk_cons (envOk_mono hp.2.1 hE) (fun w hw => by subst hw; exact hp.2.2), hp.2.1⟩
  · split at hr
    · obtain ⟨⟨v', st2⟩, hc, hr⟩ := bindO_some_inv hr
      have hp := machConvFX_post F hst hE hl hc
      try dsimp only at hr
      have e := okO_run_inv hr
      subst e
      have hv'' : LetOk st2.lets.size v' = true := hp.2.2
      have hF := rootBind_facts (nm := nm) (ty := ty) (c := (!st2.loops.isEmpty && machIsSlot v'))
        hp.1.1 hv'' (fun h => by
          have := (Bool.and_eq_true _ _).mp h
          exact this.2)
      generalize (if (!st2.loops.isEmpty && machIsSlot v') = true then machBindLetNamed nm ty v' st2.lets
        else machBindLet nm ty v' st2.lets) = bl at hF ⊢
      obtain ⟨x, lets'⟩ := bl
      have hA : RdOk { st2 with lets := lets' } := rdOk_lets hp.1 hF.1 hF.2.1 (by rfl) (by rfl)
      refine ⟨hA, ?_, Nat.le_trans hp.2.1 hF.2.1⟩
      exact envOk_cons (envOk_mono (Nat.le_trans hp.2.1 hF.2.1) hE)
        (fun w hw => by injection hw with hw; subst hw; exact hF.2.2)
    · exact (failO_run_inv hr).elim

theorem rootLets_okX {n : Nat} {l : List (Name × Lean.Expr × Lean.Expr)} {env env' : List MachVal}
    {st0 st1 : MachRead} (hl : ∀ x ∈ l, LetOk 0 x.2.2 = true) (h0 : RdOk st0)
    (hr : (foldO (shapeRootLet senv) (env, st0) l).run (btabX O senv n) = some (some (env', st1)))
    (hE : EnvOk st0.lets.size env) : RdOk st1 ∧ EnvOk st1.lets.size env' := by
  have := foldO_inv_mem (h := btabX O senv n) (fun s : List MachVal × MachRead =>
      RdOk s.2 ∧ EnvOk s.2.lets.size s.1) (fun a : Name × Lean.Expr × Lean.Expr => LetOk 0 a.2.2 = true)
    (f := shapeRootLet senv)
    (fun s a s' ha hs hr => by
      have := shapeRootLet_okX F s a s' hs ha hr
      exact ⟨this.1, this.2.1⟩) l (env, st0) (env', st1) hl ⟨h0, hE⟩ hr
  exact this

theorem shapeBody_okX {n : Nat} {m : ShapeMid} {env : List MachVal} {st1 st : MachRead}
    {v : Lean.Expr} (hs : RdOk st1) (hE : EnvOk st1.lets.size env)
    (hr0 : LetOk 0 m.root = true)
    (hbody : ∀ dom αs initsE body, m.run? = some (dom, αs, initsE, body) → LetOk 0 body = true)
    (hwrap : ∀ c params, m.wrap? = some (c, params) →
      LetOk 0 c = true ∧ ∀ x ∈ params, LetOk 0 x = true)
    (hr : (shapeBody m env st1).run (btabX O senv n) = some (some (st, v))) :
    RdOk st ∧ st1.lets.size ≤ st.lets.size ∧ LetOk st.lets.size v = true := by
  unfold shapeBody at hr
  rcases hm : m.run? with _ | ⟨dom, αs, initsE, body⟩
  · rw [hm] at hr
    try dsimp only at hr
    obtain ⟨⟨v0, st2⟩, hc, hr⟩ := bindO_some_inv hr
    try dsimp only at hr
    have e := okO_run_inv hr
    injection e with e1 e2
    subst e1
    subst e2
    exact machConvFX_post F hs hE hr0 hc
  · rw [hm] at hr
    try dsimp only at hr
    obtain ⟨⟨ws, v0, st2⟩, hc, hr⟩ := bindO_some_inv hr
    try dsimp only at hr
    have e := okO_run_inv hr
    injection e with e1 e2
    have hp := machChainFX_post F hs
      (envOk_cons hE (fun w hw => by cases hw)) (hbody dom αs initsE body hm) hc
    subst e1
    refine ⟨rdOk_congr hp.1 (by rfl) (by rfl) (by rfl), hp.2.1, ?_⟩
    rw [← e2]
    cases hw : m.wrap? with
    | none => exact hp.2.2
    | some cp =>
      obtain ⟨c, params⟩ := cp
      obtain ⟨hc0, hps⟩ := hwrap c params hw
      show LetOk st2.lets.size (mkAppN c (params.push v0)) = true
      refine ok_mkAppN (letOk_zero hc0) ?_
      intro a ha
      rcases Array.mem_push.mp ha with ha | ha
      · exact letOk_zero (hps a ha)
      · rw [ha]; exact hp.2.2

end Posts

/-! ## the closedness phases (LCQ2) -/

section CloPosts
variable {O : ExtOps} {senv : StructEnv}

theorem machConvFX_clo {n : Nat} {env : List MachVal} {d : Nat} {e : Lean.Expr} {st st' : MachRead}
    {r : Lean.Expr} (hst : CloSt st) (hE : EnvClo env)
    (h : readFX O senv n (Call.conv env d e st) = some (some (r, st'))) : CloSt st' ∧ Clo d r = true :=
  readF_cloX O senv n (Call.conv env d e st) ⟨hst, hE⟩ (r, st') h

theorem machChainFX_clo {n : Nat} {env : List MachVal} {e : Lean.Expr} {st st' : MachRead}
    {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} (hst : CloSt st) (hE : EnvClo env)
    (h : readFX O senv n (Call.chain env e st) = some (some (ws, v, st'))) : CloSt st' ∧ Clo 0 v = true :=
  readF_cloX O senv n (Call.chain env e st) ⟨hst, hE⟩ (ws, v, st') h

theorem machLoopRootFX_clo {n : Nat} {env : List MachVal} {e : Lean.Expr} {st st' : MachRead}
    {mv : MachVal} (hst : CloSt st) (hE : EnvClo env)
    (h : readFX O senv n (Call.loopRoot env e st) = some (some (mv, st'))) : CloSt st' ∧ MvClo mv :=
  readF_cloX O senv n (Call.loopRoot env e st) ⟨hst, hE⟩ (mv, st') h

theorem shapeStart_cloX {n : Nat} {m : ShapeMid} {st0 : MachRead}
    (hr : (shapeStart senv m).run (btabX O senv n) = some (some st0)) : CloSt st0 := by
  rcases shapeStart_invT hr with ⟨_, h0⟩ | ⟨dom, αs, initsE, body, dom', stc, base, hm, hc, hres⟩
  · rw [h0]; exact cloSt_init
  · obtain ⟨kinds, inits, _, _, _, hst⟩ := machReserve_some hres
    subst hst
    have hd := (machConvFX_clo (O := O) cloSt_init (envClo_units m.rootLets) hc).2
    exact cloSt_dom cloSt_init (by rfl) (by rfl) (d := dom') (by rfl) hd

theorem shapeRootLet_cloX {n : Nat} (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr)
    (s' : List MachVal × MachRead) (hs : CloSt s.2 ∧ EnvClo s.1)
    (hr : (shapeRootLet senv s a).run (btabX O senv n) = some (some s')) :
    CloSt s'.2 ∧ EnvClo s'.1 := by
  obtain ⟨env, st⟩ := s
  obtain ⟨nm, ty, v⟩ := a
  obtain ⟨hst, hE⟩ := hs
  first
    | (simp only [shapeRootLet] at hr)
    | (unfold shapeRootLet at hr; try dsimp only at hr)
  split at hr
  · obtain ⟨⟨mv, st2⟩, hl2, hr⟩ := bindO_some_inv hr
    have hp := machLoopRootFX_clo hst hE hl2
    try dsimp only at hr
    have e := okO_run_inv hr
    subst e
    exact ⟨hp.1, envClo_cons hE (fun w hw => by subst hw; exact hp.2)⟩
  · split at hr
    · obtain ⟨⟨v', st2⟩, hc, hr⟩ := bindO_some_inv hr
      have hp := machConvFX_clo hst hE hc
      try dsimp only at hr
      have e := okO_run_inv hr
      subst e
      have hF := rootBind_clo (nm := nm) (ty := ty) (c := (!st2.loops.isEmpty && machIsSlot v'))
        hp.1.1 hp.2
      generalize (if (!st2.loops.isEmpty && machIsSlot v') = true then machBindLetNamed nm ty v' st2.lets
        else machBindLet nm ty v' st2.lets) = bl at hF ⊢
      obtain ⟨x, lets'⟩ := bl
      exact ⟨cloSt_lets hp.1 hF.1 (by rfl) (by rfl),
        envClo_cons hE (fun w hw => by injection hw with hw; subst hw; exact hF.2)⟩
    · exact (failO_run_inv hr).elim

theorem rootLets_cloX {n : Nat} {l : List (Name × Lean.Expr × Lean.Expr)} {env env' : List MachVal}
    {st0 st1 : MachRead} (h0 : CloSt st0) (hE : EnvClo env)
    (hr : (foldO (shapeRootLet senv) (env, st0) l).run (btabX O senv n) = some (some (env', st1))) :
    CloSt st1 ∧ EnvClo env' := by
  exact foldO_inv_mem (h := btabX O senv n) (fun s : List MachVal × MachRead => CloSt s.2 ∧ EnvClo s.1)
    (fun _ : Name × Lean.Expr × Lean.Expr => True) (f := shapeRootLet senv)
    (fun s a s' _ hs hr => shapeRootLet_cloX s a s' hs hr) l (env, st0) (env', st1)
    (fun _ _ => trivial) ⟨h0, hE⟩ hr

theorem shapeBody_cloX {n : Nat} {m : ShapeMid} {env : List MachVal} {st1 st : MachRead}
    {v : Lean.Expr} (hs : CloSt st1) (hE : EnvClo env)
    (hr : (shapeBody m env st1).run (btabX O senv n) = some (some (st, v))) : CloSt st := by
  unfold shapeBody at hr
  rcases hm : m.run? with _ | ⟨dom, αs, initsE, body⟩
  · rw [hm] at hr
    try dsimp only at hr
    obtain ⟨⟨v0, st2⟩, hc, hr⟩ := bindO_some_inv hr
    try dsimp only at hr
    have e := okO_run_inv hr
    injection e with e1 e2
    subst e1
    exact (machConvFX_clo hs hE hc).1
  · rw [hm] at hr
    try dsimp only at hr
    obtain ⟨⟨ws, v0, st2⟩, hc, hr⟩ := bindO_some_inv hr
    try dsimp only at hr
    have e := okO_run_inv hr
    injection e with e1 e2
    have hp := machChainFX_clo hs (envClo_cons hE (fun w hw => by cases hw)) hc
    subst e1
    exact cloSt_congr hp.1 (by rfl) (by rfl) (by rfl)

end CloPosts

/-! ## the normaliser (NMI) for the operations `O` -/

theorem normStepX_ok (O : ExtOps) (hO : OpsOk O) (node : StructEnv → Lean.Expr → Lean.Expr) {senv : StructEnv}
    (hraw : RawNodeRangeX O senv) (hnode : ∀ e, LetOk 0 e = true → LetOk 0 (node senv e) = true)
    {tab : (c : Lean.Expr) → Option Lean.Expr} (ht : TabOk tab) :
    ∀ (e r : Lean.Expr), LetOk 0 e = true → (normStepX O node senv e).run tab = some r → LetOk 0 r = true := by
  intro e r he hr
  cases e with
  | app f a =>
    simp only [normStepX] at hr
    split at hr
    · rename_i dom nE x y hav
      obtain ⟨hd, hx, hy⟩ := ashrView_ok (ok_getAppArgs he) hav
      split at hr
      · rename_i n hn
        split at hr
        · exact (Option.some.inj hr) ▸ he
        · simp only [FM.bind, FM.call, FM.pure, Option.bind_eq_some_iff, Option.some.injEq] at hr
          obtain ⟨x', hx', y', hy', rfl⟩ := hr
          exact ashrE_ok _ _ (fun k => letOk_natLit 0 k)
            (fun m a b ha hb => machSigBin_ok hd _ _ _ ha hb) hd (ht _ _ hx hx') (ht _ _ hy hy') n
      · exact (Option.some.inj hr) ▸ he
    · split at hr
      · rename_i e' hraw'
        exact ht _ _ (hraw _ _ he hraw') hr
      · simp only [LetOk, Bool.and_eq_true] at he
        simp only [FM.bind, FM.call, FM.pure, Option.bind_eq_some_iff, Option.some.injEq] at hr
        obtain ⟨f', hf', a', ha', rfl⟩ := hr
        exact hnode _ (by simp only [LetOk, Bool.and_eq_true]; exact ⟨ht _ _ he.1 hf', ht _ _ he.2 ha'⟩)
  | lam nm t b bi =>
    simp only [normStepX] at hr
    simp only [LetOk, Bool.and_eq_true] at he
    simp only [FM.bind, FM.call, FM.pure, Option.bind_eq_some_iff, Option.some.injEq] at hr
    obtain ⟨b', hb', rfl⟩ := hr
    simp only [LetOk, Bool.and_eq_true]
    exact ⟨he.1, ht _ _ he.2 hb'⟩
  | letE nm t v b nd =>
    simp only [normStepX] at hr
    simp only [LetOk, Bool.and_eq_true] at he
    split at hr
    · exact ht _ _ (hO.inst1 0 b v he.2 he.1.2) hr
    · split at hr
      · exact ht _ _ (hO.inst1 0 b v he.2 he.1.2) hr
      · simp only [FM.bind, FM.call, FM.pure, Option.bind_eq_some_iff, Option.some.injEq] at hr
        obtain ⟨v', hv', b', hb', rfl⟩ := hr
        simp only [LetOk, Bool.and_eq_true]
        exact ⟨⟨he.1.1, ht _ _ he.1.2 hv'⟩, ht _ _ he.2 hb'⟩
  | bvar _ => exact (Option.some.inj hr) ▸ he
  | fvar _ => exact (Option.some.inj hr) ▸ he
  | mvar _ => exact (Option.some.inj hr) ▸ he
  | sort _ => exact (Option.some.inj hr) ▸ he
  | const _ _ => exact (Option.some.inj hr) ▸ he
  | lit _ => exact (Option.some.inj hr) ▸ he
  | forallE _ _ _ _ => exact (Option.some.inj hr) ▸ he
  | mdata _ _ => exact (Option.some.inj hr) ▸ he
  | proj _ _ _ => exact (Option.some.inj hr) ▸ he

theorem tabOk_fuelX (O : ExtOps) (hO : OpsOk O) (node : StructEnv → Lean.Expr → Lean.Expr) {senv : StructEnv}
    (hraw : RawNodeRangeX O senv) (hnode : ∀ e, LetOk 0 e = true → LetOk 0 (node senv e) = true) :
    ∀ n, TabOk (machNormFX O node n senv)
  | 0 => fun e r _ h => by
    have : machNormFX O node 0 senv e = none := rfl
    rw [this] at h; cases h
  | n + 1 => fun e r he h =>
    normStepX_ok O hO node hraw hnode (tabOk_fuelX O hO node hraw hnode n) e r he h

theorem normRangeX (O : ExtOps) (hO : OpsOk O) (node : StructEnv → Lean.Expr → Lean.Expr) {senv : StructEnv}
    (hraw : RawNodeRangeX O senv) (hnode : ∀ e, LetOk 0 e = true → LetOk 0 (node senv e) = true) :
    ∀ e en, LetOk 0 e = true → execNormX O node senv e = some en → LetOk 0 en = true := by
  intro e en he h
  obtain ⟨n, hn⟩ := (execNormX_iff O node senv).mp h
  exact tabOk_fuelX O hO node hraw hnode n e en he hn

/-- **PROVED, no correspondence premise**: the normaliser of the reader with the operations `O` keeps `LetOk 0` (the node rewriter is the
LC19 model `machNormNodeM`). -/
theorem normRangeXM (O : ExtOps) (hO : OpsOk O) {senv : StructEnv} :
    ∀ e en, LetOk 0 e = true → execNormX O machNormNodeM senv e = some en → LetOk 0 en = true :=
  normRangeX O hO machNormNodeM (rawNodeRangeX_of hO) (fun _ he => machNormNodeM_ok senv he)

/-! ## the preprocessing (LC13) for the operations `O` -/

theorem shapeMidX_ok (O : ExtOps) (hO : OpsOk O) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr)
    (hen : LetOk 0 en = true) :
    (∀ x ∈ (shapeMidX O senv p en).rootLets, LetOk 0 x.2.2 = true) ∧ LetOk 0 (shapeMidX O senv p en).root = true ∧
      ∀ dom αs initsE body, (shapeMidX O senv p en).run? = some (dom, αs, initsE, body) → LetOk 0 body = true := by
  have he := machLoopAsLet_ok 0 _ (hO.rootFloat _ (hO.zeroLit 0 _ (inlFoldNat_ok 0 _ hen)))
  have hr := machRoot_ok 0 senv.proj _ [] he (by simp)
  unfold shapeMidX
  dsimp only
  generalize machRoot senv.proj (machLoopAsLet (O.rootFloat (O.zeroLit (inlFoldNat en)))) [] = r at hr ⊢
  obtain ⟨rl, sel, run?, root⟩ := r
  obtain ⟨h1, h2, h3⟩ := hr
  refine ⟨h1, h2, ?_⟩
  intro dom αs initsE body h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, hq, hm⟩ := h
  have hqok : LetOk 0 q = true := by
    split at hq
    · exact ok_getAppArgs h2 q (Array.mem_of_back? hq)
    · exact h3 q hq
  exact (runApp_ok 0 q dom αs initsE body hqok hm).2

theorem shapeMidX_wrap_ok (O : ExtOps) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr)
    (hr : LetOk 0 (shapeMidX O senv p en).root = true) :
    ∀ c params, (shapeMidX O senv p en).wrap? = some (c, params) →
      LetOk 0 c = true ∧ ∀ x ∈ params, LetOk 0 x = true := by
  intro c params h
  unfold shapeMidX at hr h
  dsimp only at hr h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  all_goals
    have e := Option.some.inj h
    injection e with e1 e2
    subst e1
    subst e2
    exact ⟨ok_getAppFn hr, fun x hx => ok_getAppArgs hr x (array_mem_of_mem_pop hx)⟩

/-! ## the composed corollary for the operations `O` (analogue of `machineShapeNM_typed_all_rawNode'`) -/

open Tools.Prototype.ReaderComposed in
/-- **Corollary** (PROVED from `hO : OpsOk O`, `hsig`, `hpe`): for ANY operations `O` satisfying the `LetOk` ranges, a successful run of
`machineShapeX O` has the let-table / closedness / typed conclusion of `machineShapeNM_typed_all_rawNode'`, with `execNorm` ↦
`execNormX O machNormNodeM` and `shapeMid` ↦ `shapeMidX O`. -/
theorem machineShapeX_typed_all {O : ExtOps} (hO : OpsOk O) {senv : StructEnv} (hsig : SigTyRange senv)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hpe : ∀ p : ShapePre, shapePre sm ps ci senv = some p → LetOk 0 p.e = true)
    (h : machineShapeX O sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNormX O machNormNodeM senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMidX O senv p en) st v = some sp ∧
      (∀ (d : MachineData), d.shape = sp → d.ok = true →
        d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
          (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed →
        d.letsAliasOk = true ∧
        ∀ {declName : Name} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
          (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State),
          Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape) := by
  have F : PureFactsX O senv := pureFactsX_of hO hsig
  obtain ⟨n, p, en, st0, env, st1, st, v, hp, hex, h0, h1, h2, h3⟩ := machineShapeX_steps h
  obtain ⟨hrl, hrt, hrb⟩ := shapeMidX_ok O hO senv p en (normRangeXM O hO _ _ (hpe p hp) hex)
  have r0 : RdOk st0 := shapeStart_okX (n := n) (Dom.startDom_succ_w' hO.eqv h0 h1 h2 h3) h0
  have r1 := rootLets_okX F hrl r0 h1 (fun v hv => by cases hv)
  have r2 := shapeBody_okX F r1.1 r1.2 hrt hrb (shapeMidX_wrap_ok O senv p en hrt) h2
  have c0 : CloSt st0 := shapeStart_cloX h0
  have c1 := rootLets_cloX c0 (fun v hv => by cases hv) h1
  have c2 : CloSt st := shapeBody_cloX c1.1 c1.2 h2
  have hnb : NoLetBvar st.lets := letsClo_noLetBvar c2.1
  have hna : NoLetAlias st.lets := r2.1.1
  refine ⟨p, en, st, v, hp, hex, r2.1, hna, r2.2.2, h3, ?_⟩
  intro d hs hok hbody
  have halias := typed_letsAlias (shapePre_outs_ne hp) h3 hna hnb d hs hok hbody
  exact ⟨halias, fun mctx mref cctx cref => letsClose_of_data d hok hbody halias mctx mref cctx cref⟩

#print axioms machineShapeX_typed_all

end Tools.Prototype.ExtReader

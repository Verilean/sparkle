import Tools.ShippingGen5ReaderTraceDispatch
import Tools.ShippingGen5Cover5
import Tools.ShippingReaderFuelShapeR5
import Tools.ShippingReaderLenOkReserve
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceShape, exit 0, 771 jobs) on the tree of 389c4097 (Lean content identical; this header is comment-only). Written against freeze rev14 `scripts/gen5/DG_READERTRACE_FREEZE_REV14.md` §2.1 / §2.2 with the §10 plan A (`DomAtomic` restored). Clean build is the coder's. No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R12a / U-R12b: `DomAtomic`, `MidInputs`, `ShapeInputs`, `ShapeCarry`, `shapeStart_trace`, `shapeRootLet_trace`, `rootLets_trace`, `shapeBody_trace`, `machineShapeF_reach` (+ `_of_premises`, `machineShapeF_ranges`)

Statements are those of rev14 §2.1 / §2.2 with `DomAtomic dom` restored in the `MidInputs` run clause (rev14 §10, plan A, approved by the reviewer; rev0 §3.3 / F4). `hT : TraceGood senv nDecl (readF senv n)` and `hIn : ShapeInputs` are theorem hypotheses; no new premise.
`shapeStart` reserves into the EMPTY state `{}` with the converted domain `dom'`, discarding the conversion state; `DomAtomic dom` (bvar or const) gives, by a one-step unfolding of the `readF` conv arm, that the discarded state is `{}`, so `hT` supplies the range of `dom'` in the reserved state.
Conditional (intermediate) result: it does not claim that `ShapeInputs` (including `DomAtomic dom` for accepted sources) or any named hypothesis behind `hT` holds. Not supplied: the supply of `ShapeInputs` (U-R12c), C-QWIT, `d'.ok`, real run, FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover5 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingReaderFuelShapeR5 Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv Tools.ShippingReaderLenOk

/-- rev0 §3.3 (F4): the domain of the enclosing machine is a bound variable or a constant. `shapeStart` discards the state of the `dom` conversion, so this is the input condition that gives the range of the converted domain in the reserved (empty) state. A named input condition (rev14 §10, plan A); its supply from accepted sources is not proved here. -/
def DomAtomic (e : Lean.Expr) : Prop := (∃ j, e = .bvar j) ∨ (∃ c ls, e = .const c ls)

/-- rev0 §5 `MidInputs`, with `DomAtomic dom` restored (rev14 §10, plan A). -/
def MidInputs (nDecl : Nat) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  p.bs.length ≤ nDecl ∧
  (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), (shapeMid senv p en).rootLets[k]? = some x →
      NoPh x.2.2 = true ∧ BvarLt (k + nDecl) x.2.2 = true) ∧
  (∀ (dom αs ie b : Lean.Expr), (shapeMid senv p en).run? = some (dom, αs, ie, b) →
      NoPh dom = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + nDecl) dom = true ∧ DomAtomic dom ∧
      NoPh b = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + 1 + nDecl) b = true) ∧
  ((shapeMid senv p en).run? = none →
      NoPh (shapeMid senv p en).root = true ∧
      BvarLt ((shapeMid senv p en).rootLets.length + nDecl) (shapeMid senv p en).root = true)

def ShapeInputs (nDecl : Nat) (senv : StructEnv) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (n : Nat) : Prop :=
  ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p → machNormF n senv p.e = some en →
    MidInputs nDecl senv p en

/-- the invariant carried between the three reader stages: the old side (`RdOk`, `EnvOk`) and the new side (`TrInv`, `EnvPh`). -/
def ShapeCarry (senv : StructEnv) (nDecl : Nat) (env : List MachVal) (st : MachRead) : Prop :=
  RdOk st ∧ EnvOk st.lets.size env ∧ TrInv senv nDecl st ∧ EnvPh nDecl st env

theorem shapeCarry_empty (senv : StructEnv) (nDecl : Nat) : ShapeCarry senv nDecl [] ({} : MachRead) :=
  ⟨rdOk_init, fun v hv => absurd hv (by simp), trInv_empty,
    ⟨fun v hv => absurd hv (by simp), fun b n hbn => absurd hbn (by simp)⟩⟩

theorem readF_conv_bvar {senv : StructEnv} {n : Nat} {env : List MachVal} {d j : Nat} {st : MachRead}
    {r : Lean.Expr × MachRead} (h : readF senv n (Call.conv env d (.bvar j) st) = some (some r)) :
    convBvar env d j st = some r := by
  cases n with
  | zero => exact absurd h (by simp [readF, fuel])
  | succ n =>
    have h' : (some (convBvar env d j st) : Option (Option (Lean.Expr × MachRead))) = some (some r) := h
    exact Option.some.inj h'

theorem readF_conv_const {senv : StructEnv} {n : Nat} {env : List MachVal} {d : Nat} {c : Name} {ls : List Level}
    {st : MachRead} {r : Lean.Expr × MachRead} (h : readF senv n (Call.conv env d (.const c ls) st) = some (some r)) :
    r = (.const c ls, st) := by
  cases n with
  | zero => exact absurd h (by simp [readF, fuel])
  | succ n =>
    have h' : (some (some (Lean.Expr.const c ls, st)) : Option (Option (Lean.Expr × MachRead))) = some (some r) := h
    exact (Option.some.inj (Option.some.inj h')).symm

theorem shapeStart_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (m : ShapeMid)
    (hdom : ∀ dom αs ie b, m.run? = some (dom, αs, ie, b) →
        NoPh dom = true ∧ BvarLt (m.rootLets.length + nDecl) dom = true ∧ DomAtomic dom)
    {st0 : MachRead} (hr : (shapeStart senv m).run (wtab senv n) = some (some st0)) :
    FReachC nDecl ({} : MachRead) st0 ∧ ShapeCarry senv nDecl [] st0 := by
  rcases shapeStart_inv hr with ⟨_, e⟩ | ⟨dom, αs, initsE, body, dom', stc, base, hm, hc, hres⟩
  · subst e
    exact ⟨FReachC.refl _, shapeCarry_empty senv nDecl⟩
  · obtain ⟨hn, hb, hat⟩ := hdom dom αs initsE body hm
    have hUnits : EnvPh nDecl ({} : MachRead) (m.rootLets.map fun _ => MachVal.unit) :=
      ⟨fun v hv => by simp at hv, fun b n hbn => by simp at hbn⟩
    have hb' : BvarLt (0 + (m.rootLets.map fun _ => MachVal.unit).length + nDecl) dom = true := by
      rw [List.length_map, Nat.zero_add]; exact hb
    have hpre : TracePre senv nDecl (Call.conv (m.rootLets.map fun _ => MachVal.unit) 0 dom ({} : MachRead)) :=
      ⟨⟨rdOk_init, fun v hv => by simp at hv, noPh_letOk 0 dom hn⟩, ⟨trInv_empty, hUnits, hn, hb'⟩⟩
    have hc' : readF senv n (Call.conv (m.rootLets.map fun _ => MachVal.unit) 0 dom ({} : MachRead)) =
        some (some (dom', stc)) := hc
    -- the state of the discarded conversion is `{}` (one-step unfolding of the bvar / const arm)
    have hstc : stc = ({} : MachRead) := by
      rcases hat with ⟨j, rfl⟩ | ⟨c, ls, rfl⟩
      · have hcb := readF_conv_bvar hc'
        exact (convBvar_trace (nDecl := nDecl) hUnits (fun d hd => by cases hd) hb' hcb).1
      · have := readF_conv_const hc'
        exact (Prod.mk.inj this).2
    subst hstc
    obtain ⟨hP, _, hX⟩ := hT _ hpre (dom', ({} : MachRead)) hc'
    obtain ⟨kinds, inits, _, _, _, hst⟩ := machReserve_some hres
    subst hst
    obtain ⟨hR, hTr⟩ := trInv_reserved hX.1 hX.2.1 hX.2.2 body kinds inits
    refine ⟨hR, ?_, ?_, hTr, ?_⟩
    · exact (adv_dom (st' := reserved ({} : MachRead) dom' body kinds inits) (adv_refl rdOk_init) rfl rfl (d := dom') rfl hP.2).1
    · exact fun v hv => absurd hv (by simp [reserved])
    · exact ⟨fun v hv => absurd hv (by simp), fun b n hbn => absurd hbn (by simp)⟩

theorem shapeRootLet_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr)
    (hs : ShapeCarry senv nDecl s.1 s.2)
    (hn : NoPh a.2.2 = true) (hb : BvarLt (s.1.length + nDecl) a.2.2 = true)
    {s' : List MachVal × MachRead} (hr : (shapeRootLet senv s a).run (wtab senv n) = some (some s')) :
    FReachC nDecl s.2 s'.2 ∧ ShapeCarry senv nDecl s'.1 s'.2 ∧ s'.1.length = s.1.length + 1 := by
  obtain ⟨env, st⟩ := s
  obtain ⟨nm, ty, v⟩ := a
  obtain ⟨hRd, hEo, hTr, hEp⟩ := hs
  simp only at hn hb hRd hEo hTr hEp
  simp only [shapeRootLet] at hr
  split at hr
  · -- a `Signal.loop` root
    obtain ⟨⟨mv, s1⟩, hl, hr⟩ := bindO_some_inv hr
    have hh := hT (Call.loopRoot env v st) ⟨⟨hRd, hEo, noPh_letOk 0 v hn⟩, ⟨hTr, hEp, hn, hb⟩⟩ (mv, s1) hl
    obtain ⟨hP1, hR1, hX1⟩ := hh
    have hAdv : Adv st s1 := hP1.1
    have hEv : EnvOk s1.lets.size (mv :: env) :=
      envOk_cons (envOk_mono hAdv.2 hEo) (fun w hw => by subst hw; exact hP1.2)
    have e := okO_run_inv hr
    subst e
    exact ⟨hR1, ⟨hAdv.1, hEv, hX1.1, envPh_cons_root (envPh_mono hEp hR1) hX1.2.1 hX1.2.2⟩, rfl⟩
  · split at hr
    · -- an ordinary root `let`
      obtain ⟨⟨v', s1⟩, hc, hr⟩ := bindO_some_inv hr
      have hh := hT (Call.conv env 0 v st) ⟨⟨hRd, hEo, noPh_letOk 0 v hn⟩, ⟨hTr, hEp, hn, by rw [Nat.zero_add]; exact hb⟩⟩ (v', s1) hc
      obtain ⟨hP1, hR1, hX1⟩ := hh
      have hA1 : Adv st s1 := hP1.1
      have hv'' : LetOk s1.lets.size v' = true := hP1.2
      have e := okO_run_inv hr
      subst e
      by_cases hsl : (!s1.loops.isEmpty && machIsSlot v') = true
      · have hsl' : machIsSlot v' = true := by simpa using (Bool.and_eq_true_iff.mp hsl).2
        simp only [hsl, if_true]
        have hbr := bindLetNamed_reach (nm := nm) (ty := ty) hX1.2.1 hX1.2.2
        have hN := machBindLetNamed_noAlias (nm := nm) (ty := ty) (v' := v') hA1.1.1 (slot_not_letVar hsl')
        have hRg := machBindLetNamed_range (nm := nm) (ty := ty) (v' := v') hv''
        have hA : Adv st { s1 with lets := (machBindLetNamed nm ty v' s1.lets).2 } :=
          adv_lets hA1 hN hRg.1 (by rfl) (by rfl)
        refine ⟨reachC_trans hR1 hbr.1, ⟨hA.1, ?_, trInv_bindLetNamed hX1.1 hX1.2.1 hX1.2.2, ?_⟩, rfl⟩
        · exact envOk_cons (envOk_mono (Nat.le_trans hA1.2 hRg.1) hEo)
            (fun w hw => by injection hw with hw; subst hw; exact hRg.2)
        · exact envPh_cons_val (envPh_mono hEp (reachC_trans hR1 hbr.1)) hbr.2.1 hbr.2.2
      · simp only [hsl, if_false]
        have hbr := bindLet_reach (nm := nm) (ty := ty) hX1.2.1 hX1.2.2
        have hN := machBindLet_noAlias (nm := nm) (ty := ty) (v' := v') hA1.1.1
        have hRg := machBindLet_range (nm := nm) (ty := ty) (v' := v') hv''
        have hA : Adv st { s1 with lets := (machBindLet nm ty v' s1.lets).2 } :=
          adv_lets hA1 hN hRg.1 (by rfl) (by rfl)
        refine ⟨reachC_trans hR1 hbr.1, ⟨hA.1, ?_, trInv_bindLet hX1.1 hX1.2.1 hX1.2.2, ?_⟩, rfl⟩
        · exact envOk_cons (envOk_mono (Nat.le_trans hA1.2 hRg.1) hEo)
            (fun w hw => by injection hw with hw; subst hw; exact hRg.2)
        · exact envPh_cons_val (envPh_mono hEp (reachC_trans hR1 hbr.1)) hbr.2.1 hbr.2.2
    · exact (failO_run_inv hr).elim

theorem rootLets_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n)) :
    ∀ (l : List (Name × Lean.Expr × Lean.Expr)) (env : List MachVal) (st : MachRead),
    ShapeCarry senv nDecl env st →
    (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), l[k]? = some x →
        NoPh x.2.2 = true ∧ BvarLt (env.length + k + nDecl) x.2.2 = true) →
    ∀ {env' : List MachVal} {st' : MachRead},
    (foldO (shapeRootLet senv) (env, st) l).run (wtab senv n) = some (some (env', st')) →
    FReachC nDecl st st' ∧ ShapeCarry senv nDecl env' st' ∧ env'.length = env.length + l.length
  | [], env, st, hs, _, env', st', hr => by
    have hr' : (okO (env, st) : FM WCall WCall.Res (Option (List MachVal × MachRead))).run (wtab senv n) =
        some (some (env', st')) := hr
    have e := okO_run_inv hr'
    injection e with e1 e2
    subst e1
    subst e2
    exact ⟨FReachC.refl _, hs, rfl⟩
  | a :: l, env, st, hs, hl, env', st', hr => by
    have hr' : (bindO (shapeRootLet senv (env, st) a) fun s1 => foldO (shapeRootLet senv) s1 l).run (wtab senv n) =
        some (some (env', st')) := hr
    obtain ⟨s1, h1, h2⟩ := bindO_some_inv hr'
    have ha := hl 0 a rfl
    obtain ⟨hR1, hS1, hlen1⟩ := shapeRootLet_trace senv nDecl n hT (env, st) a hs ha.1
      (by simpa using ha.2) h1
    obtain ⟨hR2, hS2, hlen2⟩ := rootLets_trace senv nDecl n hT l s1.1 s1.2 hS1
      (fun k x hx => by
        have := hl (k + 1) x hx
        have hh : env.length + (k + 1) + nDecl = s1.1.length + k + nDecl := by simp only at hlen1; omega
        rw [hh] at this
        exact this) h2
    refine ⟨reachC_trans hR1 hR2, hS2, ?_⟩
    simp only at hlen1 hlen2 ⊢
    simp only [List.length_cons]
    omega

theorem shapeBody_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (m : ShapeMid) (env : List MachVal) (st1 : MachRead)
    (hs : ShapeCarry senv nDecl env st1) (hlen : env.length = m.rootLets.length)
    (hrun : ∀ dom αs ie b, m.run? = some (dom, αs, ie, b) →
        NoPh b = true ∧ BvarLt (m.rootLets.length + 1 + nDecl) b = true)
    (hroot : m.run? = none → NoPh m.root = true ∧ BvarLt (m.rootLets.length + nDecl) m.root = true)
    {st : MachRead} {v : Lean.Expr} (hr : (shapeBody m env st1).run (wtab senv n) = some (some (st, v))) :
    FReachC nDecl st1 st ∧ TrInv senv nDecl st ∧
    (m.wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v) := by
  obtain ⟨hRd, hEo, hTr, hEp⟩ := hs
  unfold shapeBody at hr
  rcases hm : m.run? with _ | ⟨dom, αs, initsE, body⟩
  · rw [hm] at hr
    dsimp only at hr
    obtain ⟨⟨v0, st2⟩, hc, hr⟩ := bindO_some_inv hr
    dsimp only at hr
    have hrt := hroot hm
    have hh := hT (Call.conv env 0 m.root st1) ⟨⟨hRd, hEo, noPh_letOk 0 _ hrt.1⟩,
      ⟨hTr, hEp, hrt.1, by rw [Nat.zero_add, hlen]; exact hrt.2⟩⟩ (v0, st2) hc
    have e := okO_run_inv hr
    injection e with e1 e2
    subst e1
    subst e2
    exact ⟨hh.2.1, hh.2.2.1, fun _ => ⟨hh.2.2.2.1, hh.2.2.2.2⟩⟩
  · rw [hm] at hr
    dsimp only at hr
    obtain ⟨⟨ws, v0, st2⟩, hc, hr⟩ := bindO_some_inv hr
    dsimp only at hr
    have hrn := hrun dom αs initsE body hm
    have hh := hT (Call.chain (MachVal.regs 0 :: env) body st1)
      ⟨⟨hRd, envOk_cons hEo (fun w hw => by cases hw), noPh_letOk 0 _ hrn.1⟩,
       ⟨hTr, envPh_cons_regs hEp 0, hrn.1, by
          simp only [List.length_cons]
          rw [hlen]
          exact hrn.2⟩⟩ (ws, v0, st2) hc
    obtain ⟨hP, hR, hX⟩ := hh
    have hws : ∀ w ∈ st2.ws ++ ws.toArray, w.1 < st2.kinds.size ∧ InRange nDecl st2 st2.lets.size w.2 := by
      intro w hw
      rcases Array.mem_append.mp hw with hw | hw
      · exact hX.1.1.2.1.2 w hw
      · exact hX.2.1 w (List.mem_toArray.mp hw)
    have hwsR : FReachC nDecl st2 { st2 with ws := st2.ws ++ ws.toArray } := reachC_ws st2 _ hws
    have e := okO_run_inv hr
    injection e with e1 e2
    subst e1
    refine ⟨reachC_trans hR hwsR, ⟨fullInv_reachC hX.1.1 hwsR, hX.1.2⟩, fun hw => ?_⟩
    rw [← e2]
    simp only [hw]
    exact ⟨hX.2.2.1, hX.2.2.2⟩

theorem machineShapeF_reach {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape} {nDecl : Nat}
    (hT : TraceGood senv nDecl (readF senv n))
    (h : machineShapeF n sm ps ci senv ai = some (some sp))
    (hIn : ShapeInputs nDecl senv sm ps ci n) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size ∧
      FReachC nDecl ({} : MachRead) st0 ∧ FReachC nDecl st0 st1 ∧ FReachC nDecl st1 st ∧
      TrInv senv nDecl st ∧
      ((shapeMid senv p en).wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v) := by
  obtain ⟨p, en, st0, env, st1, st, v, hp, hen, h0, h1, h2, h3, l2, i1, i2, i3, i4⟩ := machineShapeF_state_side h
  obtain ⟨_, hrl, hrun, hroot⟩ := hIn p en hp hen
  obtain ⟨R0, C0⟩ := shapeStart_trace senv nDecl n hT (shapeMid senv p en)
    (fun dom αs ie b hm => ⟨(hrun dom αs ie b hm).1, (hrun dom αs ie b hm).2.1, (hrun dom αs ie b hm).2.2.1⟩) h0
  obtain ⟨R1, C1, hl1⟩ := rootLets_trace senv nDecl n hT _ [] st0 C0
    (fun k x hk => by
      have := hrl k x hk
      rw [List.length_nil, Nat.zero_add]
      exact this) h1
  obtain ⟨R2, Tr, hv⟩ := shapeBody_trace senv nDecl n hT _ env st1 C1 (by simpa using hl1)
    (fun dom αs ie b hm => ⟨(hrun dom αs ie b hm).2.2.2.1, (hrun dom αs ie b hm).2.2.2.2⟩) hroot h2
  exact ⟨p, en, st0, env, st1, st, v, hp, hen, h0, h1, h2, h3, l2, i1, i2, i3, i4, R0, R1, R2, Tr, hv⟩

theorem machineShapeF_reach_of_premises (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hi1 : Inst1Agrees) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env)) {n : Nat} {sm : Bool}
    {ps : List (String × Nat)} {ci : ConstantInfo} {ai : Bool} {sp : MachineShape} {nDecl : Nat}
    (h : machineShapeF n sm ps ci (structEnv env) ai = some (some sp))
    (hIn : ShapeInputs nDecl (structEnv env) sm ps ci n) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (envs : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci (structEnv env) = some p ∧
      machNormF n (structEnv env) p.e = some en ∧
      (shapeStart (structEnv env) (shapeMid (structEnv env) p en)).run (wtab (structEnv env) n) = some (some st0) ∧
      (foldO (shapeRootLet (structEnv env)) (([] : List MachVal), st0) (shapeMid (structEnv env) p en).rootLets).run
        (wtab (structEnv env) n) = some (some (envs, st1)) ∧
      (shapeBody (shapeMid (structEnv env) p en) envs st1).run (wtab (structEnv env) n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid (structEnv env) p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size ∧
      FReachC nDecl ({} : MachRead) st0 ∧ FReachC nDecl st0 st1 ∧ FReachC nDecl st1 st ∧
      TrInv (structEnv env) nDecl st ∧
      ((shapeMid (structEnv env) p en).wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v) :=
  machineShapeF_reach (readF_traceGood_of_premises env hK hC hla hrf hi1 hD nDecl n) h hIn

theorem machineShapeF_ranges {nDecl : Nat} {senv : StructEnv} {st : MachRead} (hTr : TrInv senv nDecl st) :
    (∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) →
        InRange nDecl st j v ∧ NoLoose 0 v) ∧
    (∀ w ∈ st.ws, w.1 < st.kinds.size ∧ InRange nDecl st st.lets.size w.2) ∧
    (∀ d, st.dom = some d → InRange nDecl st st.lets.size d ∧ NoLoose 0 d) :=
  ⟨fun j nm kd v hj => ⟨hTr.1.2.1.1 j nm kd v hj, hTr.2.2.2.2.2.1 j nm kd v hj⟩, hTr.1.2.1.2, hTr.2.2.2.2.1⟩

end Tools.ShippingGen5ReaderTrace

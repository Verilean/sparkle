import Tools.ShippingGen5ReaderTraceDispatch
import Tools.ShippingGen5Cover5
import Tools.ShippingReaderFuelShapeR5
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceShape, exit 0, 771 jobs) on the tree of 8ba8bf09 (Lean content identical; this header is comment-only). Written against freeze rev14 `scripts/gen5/DG_READERTRACE_FREEZE_REV14.md` §2.1; see its §10 addendum for the part not implemented. Clean build is the coder's. No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R12a (part): `MidInputs`, `ShapeInputs`, `ShapeCarry`, `shapeRootLet_trace`, `rootLets_trace`, `shapeBody_trace`

Statements are those of rev14 §2.1. `hT : TraceGood senv nDecl (readF senv n)` and the `MidInputs`-shaped range hypotheses are theorem hypotheses; no new premise.
NOT implemented here: `shapeStart_trace` and `machineShapeF_reach` (see the addendum of rev14: `shapeStart` reserves into the EMPTY state `{}` with the converted domain `dom'`, whose `InRange` is
relative to the discarded conversion state `stc`, so `DomPh` of the reserved state is not supplied by `hT` alone).
Conditional (intermediate) result: it does not claim that `ShapeInputs` or any named hypothesis behind `hT` holds. Not supplied: C-QWIT, `d'.ok`, real run, FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover5 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingReaderFuelShapeR5 Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv

/-- rev0 §5 `MidInputs` without `DomAtomic dom` (rev14 §0 point 4: a weakening). -/
def MidInputs (nDecl : Nat) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  p.bs.length ≤ nDecl ∧
  (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), (shapeMid senv p en).rootLets[k]? = some x →
      NoPh x.2.2 = true ∧ BvarLt (k + nDecl) x.2.2 = true) ∧
  (∀ (dom αs ie b : Lean.Expr), (shapeMid senv p en).run? = some (dom, αs, ie, b) →
      NoPh dom = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + nDecl) dom = true ∧
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

end Tools.ShippingGen5ReaderTrace

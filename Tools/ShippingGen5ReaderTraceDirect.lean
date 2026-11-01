import Tools.ShippingGen5ReaderTraceShapeIn
import Tools.PartialTotal.Agree
import Tools.Prototype.NormRangeLetOk
set_option autoImplicit false
-- NOT BUILT: first draft, not yet built.

/-! # DG-READERTRACE: `shapeInputs_of_direct` (freeze rev19 `scripts/gen5/DG_READERTRACE_FREEZE_REV19.md` §2-§3)

The conditions N1-a (`DeclValuePh`), N2-b (`PackTupleInputsBridge`, twin `lamDepth` / `packTupleInputsF`), N3-b (`RawNodePh` / `NormNodePh`)
and `CiDirect` are defined here exactly as in rev19 §2 and are theorem hypotheses only: they are NOT registered in `Tools/Assume/` and not
claimed true for accepted sources (a later freeze decides registration). `RootFloatAgrees` is obtained from `rootFloatAgrees` (par/ptot-m4)
and `LiftAgrees`. Proved here: `packTupleInputsF_ph` (from `LiftAgrees`, `Inst1Agrees`), `machNormF_ph` (from `Inst1Agrees`, `RawNodePh`,
`NormNodePh`), `shapeInputs_of_direct`. Conditional (intermediate) result: no hypothesis is shown to hold for accepted sources. -/

namespace Tools.Assume.EnvDeclValue
open Lean Tools.ShippingGen5ReaderTrace
def DeclValuePh (env : Lean.Environment) : Prop :=
  ∀ (n : Lean.Name) (d : Lean.DefinitionVal),
    env.find? n = some (.defnInfo d) → NoPh d.value = true ∧ BvarLt 0 d.value = true
end Tools.Assume.EnvDeclValue

namespace Tools.ShippingGen5ReaderTracePack
open Lean Sparkle.Compiler.MachTupleIn Tools.ShippingGen5ReaderTrace
def lamDepth : Lean.Expr → Nat
  | .lam _ _ b _ => lamDepth b + 1
  | _ => 0
def packTupleInputsF : Nat → Lean.Expr → Lean.Expr
  | k + 1, .lam nm ty b bi =>
    match tupleInput? ty with
    | some (dom, ws) =>
      let n := ws.foldl (· + ·) 0
      let ty' := mkApp2 (.const ``Sparkle.Core.Signal.Signal [.zero]) dom (mkApp (.const ``BitVec []) (natE n))
      let b' := (b.liftLooseBVars 1 1).instantiate1 (unpackE (dom.liftLooseBVars 0 1) ws (.bvar 0))
      .lam nm ty' (packTupleInputsF k b') bi
    | none => .lam nm ty (packTupleInputsF k b) bi
  | _, e => e
end Tools.ShippingGen5ReaderTracePack

namespace Tools.Assume.PackTupleBridge
open Lean Tools.ShippingGen5ReaderTrace
def PackTupleInputsBridge : Prop :=
  ∀ e : Lean.Expr, NoPh e = true → BvarLt 0 e = true →
    Sparkle.Compiler.MachTupleIn.packTupleInputs e = Tools.ShippingGen5ReaderTracePack.packTupleInputsF (Tools.ShippingGen5ReaderTracePack.lamDepth e) e
end Tools.Assume.PackTupleBridge

namespace Tools.Assume.NormNodePh
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5ReaderTrace
def RawNodePh (senv : StructEnv) : Prop :=
  ∀ (L : Nat) (f a e' : Lean.Expr),
    NoPh f = true → NoPh a = true → BvarLt L f = true → BvarLt L a = true →
    Sparkle.Compiler.MachRawSurface.rawNode senv.prodMatch (.app f a) = some e' →
    NoPh e' = true ∧ BvarLt L e' = true
def NormNodePh (senv : StructEnv) : Prop :=
  ∀ (L : Nat) (f a : Lean.Expr),
    NoPh f = true → NoPh a = true → BvarLt L f = true → BvarLt L a = true →
    NoPh (machNormNode senv (.app f a)) = true ∧ BvarLt L (machNormNode senv (.app f a)) = true
end Tools.Assume.NormNodePh

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.ShippingReaderFuel
open Sparkle.Compiler.MachTupleIn Tools.ShippingGen5ReaderTracePack Tools.ShippingReaderFuelShapeR5

/-! ## `packTupleInputsF` -/

theorem unpackE_ph {L : Nat} (dom x : Lean.Expr) (ws : List Nat)
    (hdn : NoPh dom = true) (hdb : BvarLt L dom = true) (hxn : NoPh x = true) (hxb : BvarLt L x = true) :
    NoPh (unpackE dom ws x) = true ∧ BvarLt L (unpackE dom ws x) = true := by
  unfold unpackE
  split
  · simp [sliceMapE, natE, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, NoPh, BvarLt, hdn, hdb, hxn, hxb]
  · simp [sliceMapE, natE, mkApp7, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, NoPh, BvarLt, hdn, hdb, hxn, hxb]
  · exact ⟨hxn, hxb⟩

theorem tupleInput?_dom {ty dom : Lean.Expr} {ws : List Nat} (h : tupleInput? ty = some (dom, ws)) :
    ∃ (ls : List Level) (t : Lean.Expr), ty = .app (.app (.const ``Sparkle.Core.Signal.Signal ls) dom) t := by
  unfold tupleInput? at h
  split at h
  · rename_i ls d t
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨ws', _, hq⟩ := h
    simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, _⟩ := hq
    exact ⟨ls, t, rfl⟩
  · simp at h

theorem packTupleInputsF_ph (hla : LiftAgrees) (hi1 : Inst1Agrees) :
    ∀ (k L : Nat) (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
      NoPh (packTupleInputsF k e) = true ∧ BvarLt L (packTupleInputsF k e) = true := by
  intro k
  induction k with
  | zero => intro L e hn hb; exact ⟨hn, hb⟩
  | succ k ih =>
    intro L e hn hb
    cases e with
    | lam nm ty b bi =>
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
      simp only [packTupleInputsF]
      cases ht : tupleInput? ty with
      | none =>
        simp only [ht]
        have := ih (L + 1) b hn.2 hb.2
        simp only [NoPh, BvarLt, Bool.and_eq_true]
        exact ⟨⟨hn.1, this.1⟩, hb.1, this.2⟩
      | some p =>
        obtain ⟨dom, ws⟩ := p
        obtain ⟨ls, t, hty⟩ := tupleInput?_dom ht
        subst hty
        simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
        have hdn : NoPh dom = true := hn.1.1.2
        have hdb : BvarLt L dom = true := hb.1.1.2
        simp only [ht]
        have hl0 := (hla dom (noPh_letOk 0 dom hdn)).1
        have hl1 := (hla b (noPh_letOk 0 b hn.2)).2
        rw [hl0, hl1, hi1]
        have hdn' := liftSpec_noPh dom 0 1 hdn
        have hdb' : BvarLt (L + 1) (liftSpec dom 0 1) = true := liftSpec_bvarLt dom 0 1 L hdb
        have hu := unpackE_ph (L := L + 1) (liftSpec dom 0 1) (.bvar 0) ws hdn' hdb' rfl (by simp [BvarLt])
        have hbn := inst1Spec_noPh (liftSpec b 1 1) _ 0 (liftSpec_noPh b 1 1 hn.2) hu.1
        have hbb := inst1Spec_bvarLt (liftSpec b 1 1) (unpackE (liftSpec dom 0 1) ws (.bvar 0)) 0 (L + 1) (L + 1)
          (liftSpec_bvarLt b 1 1 (L + 1) hb.2) hu.2 (Nat.le_refl _)
        have := ih (L + 1) _ hbn hbb
        simp only [NoPh, BvarLt, Bool.and_eq_true]
        refine ⟨⟨?_, this.1⟩, ?_, this.2⟩
        · simp [natE, mkApp2, mkApp, NoPh, hdn]
        · simp [natE, mkApp2, mkApp, BvarLt, hdb]
    | _ => exact ⟨hn, hb⟩


/-! ## `machNormF` -/

theorem ashrE_ph {L : Nat} (dom x y : Lean.Expr) (n : Nat)
    (hdn : NoPh dom = true) (hdb : BvarLt L dom = true) (hxn : NoPh x = true) (hxb : BvarLt L x = true)
    (hyn : NoPh y = true) (hyb : BvarLt L y = true) :
    NoPh (Sparkle.Compiler.MachSignOps.ashrE inlNatLit
      (fun m a b => machSigBin m ((machSigInst m).getD .anonymous) dom n a b) dom n x y) = true ∧
    BvarLt L (Sparkle.Compiler.MachSignOps.ashrE inlNatLit
      (fun m a b => machSigBin m ((machSigInst m).getD .anonymous) dom n a b) dom n x y) = true := by
  simp [Sparkle.Compiler.MachSignOps.ashrE, Sparkle.Compiler.MachSignOps.fillE, Sparkle.Compiler.MachSignOps.msbE,
    Sparkle.Compiler.MachSignOps.bvT, machSigBin, machSigT, inlNatLit, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkApp,
    NoPh, BvarLt, hdn, hdb, hxn, hxb, hyn, hyb]

theorem machNormF_ph (hi1 : Inst1Agrees) (senv : StructEnv)
    (hraw : Tools.Assume.NormNodePh.RawNodePh senv) (hnode : Tools.Assume.NormNodePh.NormNodePh senv) :
    ∀ (n L : Nat) (e en : Lean.Expr), NoPh e = true → BvarLt L e = true → machNormF n senv e = some en →
      NoPh en = true ∧ BvarLt L en = true := by
  intro n
  induction n with
  | zero => intro L e en _ _ h; simp [machNormF, fuel] at h
  | succ n ih =>
    intro L e en hn hb h
    have h' : (normStep senv e).run (fuel (normStep senv) n) = some en := h
    have hc : ∀ (L' : Nat) (c r : Lean.Expr), NoPh c = true → BvarLt L' c = true →
        fuel (normStep senv) n c = some r → NoPh r = true ∧ BvarLt L' r = true :=
      fun L' c r hn' hb' hr => ih L' c r hn' hb' hr
    cases e with
    | app f a =>
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
      simp only [normStep] at h'
      split at h'
      · rename_i dom nE x y hview
        have hargs := Tools.Prototype.NormRangeLetOk.ashrView_args _ _ _ _ _ _ hview
        have hall := phArgs_getAppArgs (L := L) (e := .app f a) (by simp [NoPh, hn]) (by simp [BvarLt, hb])
        rw [hargs] at hall
        have hdom := hall dom (by simp)
        have hx := hall x (by simp)
        have hy := hall y (by simp)
        split at h'
        · rename_i k hk
          split at h'
          · simp only [FM.pure, Option.some.injEq] at h'
            subst h'
            simp only [NoPh, BvarLt, Bool.and_eq_true]
            exact ⟨hn, hb⟩
          · simp only [FM.bind, FM.call, FM.pure, Option.bind_eq_some_iff] at h'
            obtain ⟨x', hx', y', hy', hen⟩ := h'
            simp only [Option.some.injEq] at hen
            subst hen
            have h1 := hc L x x' hx.1 hx.2 hx'
            have h2 := hc L y y' hy.1 hy.2 hy'
            exact ashrE_ph dom x' y' k hdom.1 hdom.2 h1.1 h1.2 h2.1 h2.2
        · simp only [FM.pure, Option.some.injEq] at h'
          subst h'
          simp only [NoPh, BvarLt, Bool.and_eq_true]
          exact ⟨hn, hb⟩
      · split at h'
        · rename_i e' hraw'
          have hr := hraw L f a e' hn.1 hn.2 hb.1 hb.2 hraw'
          exact hc L e' en hr.1 hr.2 h'
        · simp only [FM.bind, FM.call, FM.pure, Option.bind_eq_some_iff] at h'
          obtain ⟨f', hf', a', ha', hen⟩ := h'
          simp only [Option.some.injEq] at hen
          subst hen
          have h1 := hc L f f' hn.1 hb.1 hf'
          have h2 := hc L a a' hn.2 hb.2 ha'
          exact hnode L f' a' h1.1 h2.1 h1.2 h2.2
    | lam nm t b bi =>
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
      simp only [normStep, FM.bind, FM.call, FM.pure, Option.bind_eq_some_iff] at h'
      obtain ⟨b', hb', hen⟩ := h'
      simp only [Option.some.injEq] at hen
      subst hen
      have h1 := hc (L + 1) b b' hn.2 hb.2 hb'
      simp only [NoPh, BvarLt, Bool.and_eq_true]
      exact ⟨⟨hn.1, h1.1⟩, hb.1, h1.2⟩
    | letE nm t v b nd =>
      simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
      have hinst : NoPh (b.instantiate1 v) = true ∧ BvarLt L (b.instantiate1 v) = true := by
        rw [hi1]
        refine ⟨inst1Spec_noPh b v 0 hn.2 hn.1.2, ?_⟩
        exact inst1Spec_bvarLt b v 0 L L (by simpa using hb.2) hb.1.2 (Nat.le_refl _)
      simp only [normStep] at h'
      split at h'
      · exact hc L _ en hinst.1 hinst.2 h'
      · split at h'
        · exact hc L _ en hinst.1 hinst.2 h'
        · simp only [FM.bind, FM.call, FM.pure, Option.bind_eq_some_iff] at h'
          obtain ⟨v', hv', b', hb', hen⟩ := h'
          simp only [Option.some.injEq] at hen
          subst hen
          have h1 := hc L v v' hn.1.2 hb.1.2 hv'
          have h2 := hc (L + 1) b b' hn.2 hb.2 hb'
          simp only [NoPh, BvarLt, Bool.and_eq_true]
          exact ⟨⟨⟨hn.1.1, h1.1⟩, h2.1⟩, ⟨hb.1.1, h1.2⟩, h2.2⟩
    | _ =>
      simp only [normStep, FM.pure, Option.some.injEq] at h'
      subst h'
      exact ⟨hn, hb⟩

/-! ## `shapeInputs_of_direct` -/

def CiDirect (env : Lean.Environment) (ci : Lean.ConstantInfo) : Prop :=
  ∃ c : Lean.Name, env.find? c = some ci

theorem shapeInputs_of_direct
    (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    {ci : Lean.ConstantInfo} (hci : CiDirect env ci)
    (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env))
    (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    {nDecl : Nat} {sm : Bool} {ps : List (String × Nat)} {n : Nat}
    (hdom : ∀ (p : ShapePre) (en : Lean.Expr),
      shapePre sm ps ci (structEnv env) = some p → machNormF n (structEnv env) p.e = some en →
      ∀ (dom αs ie b : Lean.Expr), (shapeMid (structEnv env) p en).run? = some (dom, αs, ie, b) → DomAtomic dom)
    (hbs : ∀ p : ShapePre, shapePre sm ps ci (structEnv env) = some p → p.bs.length ≤ nDecl) :
    ShapeInputs nDecl (structEnv env) sm ps ci n := by
  have hrf : RootFloatAgrees := Tools.PartialTotal.Agree.rootFloatAgrees hla
  have hdecl : ∀ d, ci = ConstantInfo.defnInfo d → NoPh d.value = true ∧ BvarLt 0 d.value = true := by
    intro d hd
    obtain ⟨c, hc⟩ := hci
    rw [hd] at hc
    exact hv c d hc
  intro p en hp hen
  obtain ⟨hci', hpeel, -⟩ := shapePre_facts hp
  have hd := hdecl p.d hci'
  have h1 : NoPh (Sparkle.Compiler.MachTupleIn.packTupleInputs p.d.value) = true ∧
      BvarLt 0 (Sparkle.Compiler.MachTupleIn.packTupleInputs p.d.value) = true := by
    rw [hbr _ hd.1 hd.2]
    exact packTupleInputsF_ph hla hi1 _ 0 _ hd.1 hd.2
  have h2 := mixedGatePeel_ph (L := 0) _ p.bs p.e hpeel h1.1 h1.2
  rw [Nat.zero_add] at h2
  have h3 := machNormF_ph hi1 (structEnv env) hraw hnode n p.bs.length p.e en h2.1 h2.2 hen
  have hm := shapeMid_ph hz hrf (structEnv env) p h3.1 h3.2
  have hle := hbs p hp
  refine ⟨hle, ?_, ?_, ?_⟩
  · intro k x hx
    have := hm.1 k x hx
    exact ⟨this.1, bvarLt_mono (by omega) this.2⟩
  · intro dom αs ie b hr
    have := hm.2.1 dom αs ie b hr
    exact ⟨this.1, bvarLt_mono (by omega) this.2.1, hdom p en hp hen dom αs ie b hr, this.2.2.1,
      bvarLt_mono (by omega) this.2.2.2⟩
  · intro hr
    have := hm.2.2 hr
    exact ⟨this.1, bvarLt_mono (by omega) this.2⟩

end Tools.ShippingGen5ReaderTrace

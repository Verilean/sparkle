import Tools.Prototype.NormStepModel

/-! # Unit EXT (1/2): kernel-visible MODELS of the extern / partial operations of the model reader, with `LetOk` proved for the models

BUILT (unit EXT): e1 exit 1 (3 proof errors), e2 exit 1 (missing `open`s), e3 exit 0 (first full file); Tests.Compiler.ExtModelAgreeTest
t4 exit 0 after the `lowerM` guard (t1 exit 1 / t2 exit 1 / t3 exit 1 = test-file errors and the probe that found the guard); the `lowerM` change was
built through t4, which compiles this file. No sorry / axiom / native_decide. `#print axioms` below: only [propext] / [propext, Quot.sound]
for the model lemmas.

EVERY Prop premise of `machineShapeNM_typed_all_rawNode'` and its kind (before this unit):
* `hroot : RootFloatRange` — `partial def rootFloat` (MachRawSurface.lean:198; calls the extern `liftLooseBVars`).
* `hinst1 : Inst1Range` — extern `Expr.instantiate1`.
* `hsig : SigTyRange senv` — INPUT condition on the environment (`senv.instS` result types mention no `_machLet`).
* `hz : ZeroLitAgrees` — extern `Expr.replace` ↔ structural `replaceNoCache` (already a correspondence; its range is `zeroLit_ok`, proved).
* `hll : LiftLooseRange` — extern `liftLooseBVars`.   * `hlo : LowerLooseRange` — extern `lowerLooseBVars`.
* `hbeta : BetaRange` — `partial def betaRev` behind `Expr.beta`.   * `hE : EqvLetOk0` — extern `Expr.eqv`.
* `hpe` — INPUT condition (the preprocessed term of `shapePre` has `LetOk 0`; a generation-time fact about the user's term, not derived).
After this unit the six operation premises (`hroot hinst1 hll hlo hbeta hE`) are replaced, in `machineShapeNM_typed_all_rawNode_corr`, by one
correspondence premise per operation. The `LetOk` part is PROVED for the models. `hsig`, `hz`, `hpe` are unchanged.
What was NOT done: the reader copies still call the shipped operations (`rootFloat` at Elab.lean:3990/4155/5088, `instantiate1` at
4095/4989/4992, `liftLooseBVars` in `rootFloat`/`rawNode`); no reader variant that calls the models exists. A correspondence premise is
extensional agreement of an extern with a model, NOT a discharge; it is evidence-tested only.

Scope. Models of the operations behind the premises of `machineShapeNM_typed_all_rawNode'`, each by structural recursion on `Expr`
(`rootFloat`: fuel recursion): `liftM` (`Expr.liftLooseBVars`, extern), `lowerM` (`lowerLooseBVars`, extern), `inst1M`
(`instantiate1`, extern), `betaM` (`Expr.beta #[a]`, `partial def betaRev`), `eqvM` (`Expr.eqv`, extern), `rootFloatN`
(`rootFloat`, `partial def`). PROVED here (no premise): `LetOk` behaviour of every model. The model ↔ shipped operation agreement is NOT proved
(the shipped operations are extern / partial); it is the named premise per operation (`LiftCorr`, `LowerCorr`, `Inst1Corr`, `BetaCorr`,
`EqvCorr`, `RootFloatCorr`). Agreement on a finite grid (Tests/Compiler/ExtModelAgreeTest.lean) is EVIDENCE, not a proof. -/

namespace Tools.Prototype.ExtModelLetOk
open Lean Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv Tools.Prototype.RawNodeRangeLetOk Tools.Prototype.StartDomOk
open Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
  Tools.Prototype.NormNodeModelLetOk Tools.Prototype.ReaderLfp Lean.Order
open Tools.ShippingReaderFuelShapeR5 Tools.ShippingReaderLenOk Tools.ShippingCloInv
open Tools.Prototype.ReaderTyped Tools.Prototype.StartDomOk Tools.Prototype.ReaderClosed
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMixedSourceBridge
open Tools.Prototype.RawNodeRangeLetOk Tools.Prototype.ReaderComposed Tools.Prototype.NormStepModel

/-! ## the models -/

/-- Model of `Expr.liftLooseBVars e s d`: loose `bvar i` with `i ≥ s` (shifted by the binders passed) becomes `bvar (i + d)`. -/
def liftM : Lean.Expr → Nat → Nat → Lean.Expr
  | .bvar i, s, d => if s ≤ i then .bvar (i + d) else .bvar i
  | .app f a, s, d => .app (liftM f s d) (liftM a s d)
  | .lam n t b bi, s, d => .lam n (liftM t s d) (liftM b (s + 1) d) bi
  | .forallE n t b bi, s, d => .forallE n (liftM t s d) (liftM b (s + 1) d) bi
  | .letE n t v b nd, s, d => .letE n (liftM t s d) (liftM v s d) (liftM b (s + 1) d) nd
  | .mdata m e, s, d => .mdata m (liftM e s d)
  | .proj sn i e, s, d => .proj sn i (liftM e s d)
  | e, _, _ => e

/-- Structural part of the `lowerLooseBVars` model: loose `bvar i` with `i ≥ s` becomes `bvar (i - d)`. -/
def lowerCore : Lean.Expr → Nat → Nat → Lean.Expr
  | .bvar i, s, d => if s ≤ i then .bvar (i - d) else .bvar i
  | .app f a, s, d => .app (lowerCore f s d) (lowerCore a s d)
  | .lam n t b bi, s, d => .lam n (lowerCore t s d) (lowerCore b (s + 1) d) bi
  | .forallE n t b bi, s, d => .forallE n (lowerCore t s d) (lowerCore b (s + 1) d) bi
  | .letE n t v b nd, s, d => .letE n (lowerCore t s d) (lowerCore v s d) (lowerCore b (s + 1) d) nd
  | .mdata m e, s, d => .mdata m (lowerCore e s d)
  | .proj sn i e, s, d => .proj sn i (lowerCore e s d)
  | e, _, _ => e

/-- Model of `Expr.lowerLooseBVars e s d`. The executed probe (Tests/Compiler/ExtModelAgreeTest.lean) shows the shipped extern returns
`e` unchanged when `s < d` (the precondition `d ≤ s` of the C++ is not met), so the model has that guard. -/
def lowerM (e : Lean.Expr) (s d : Nat) : Lean.Expr := if s < d then e else lowerCore e s d

/-- Model of `instantiate1 b a` under `off` binders: `bvar off` is `a` lifted by `off`, deeper loose variables drop by one. -/
def inst1M : Lean.Expr → Lean.Expr → Nat → Lean.Expr
  | .bvar i, a, off => if i < off then .bvar i else if i == off then liftM a 0 off else .bvar (i - 1)
  | .app f x, a, off => .app (inst1M f a off) (inst1M x a off)
  | .lam n t b bi, a, off => .lam n (inst1M t a off) (inst1M b a (off + 1)) bi
  | .forallE n t b bi, a, off => .forallE n (inst1M t a off) (inst1M b a (off + 1)) bi
  | .letE n t v b nd, a, off => .letE n (inst1M t a off) (inst1M v a off) (inst1M b a (off + 1)) nd
  | .mdata m e, a, off => .mdata m (inst1M e a off)
  | .proj sn i e, a, off => .proj sn i (inst1M e a off)
  | e, _, _ => e

/-- Model of `f.beta #[a]` (`betaRev` with one argument, `useZeta := false`, `preserveMData := false`). -/
def betaM : Lean.Expr → Lean.Expr → Lean.Expr
  | .lam _ _ b _, a => inst1M b a 0
  | .mdata _ b, a => betaM b a
  | f, a => .app f a

/-- Model of `Expr.eqv` for the `LetOk` direction: same shape, binder names / binder infos / `mdata` payloads ignored. -/
def eqvM : Lean.Expr → Lean.Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar a, .fvar b => a.name == b.name
  | .app f a, .app f' a' => eqvM f f' && eqvM a a'
  | .lam _ t b _, .lam _ t' b' _ => eqvM t t' && eqvM b b'
  | .forallE _ t b _, .forallE _ t' b' _ => eqvM t t' && eqvM b b'
  | .letE _ t v b _, .letE _ t' v' b' _ => eqvM t t' && eqvM v v' && eqvM b b'
  | .mdata _ e, .mdata _ e' => eqvM e e'
  | .proj _ i e, .proj _ i' e' => i == i' && eqvM e e'
  | .mvar _, .mvar _ => true
  | .sort _, .sort _ => true
  | .const _ _, .const _ _ => true
  | .lit _, .lit _ => true
  | _, _ => false

/-- Fuel model of `rootFloat` (`none`: fuel exhausted). The text of `MachRawSurface.rootFloat` with `liftLooseBVars` ↦ `liftM`. -/
def rootFloatN : Nat → Lean.Expr → Option Lean.Expr
  | 0, _ => none
  | k + 1, .letE n t v b nd =>
    match v with
    | .letE n2 t2 v2 w nd2 => rootFloatN k (.letE n2 t2 v2 (.letE n (liftM t 0 1) w (liftM b 1 1) nd) nd2)
    | _ => (rootFloatN k b).map fun r => .letE n t v r nd
  | k + 1, .app f a =>
    match a with
    | .letE n t v b nd => (rootFloatN k (.app (liftM f 0 1) b)).map fun r => .letE n t v r nd
    | _ => some (.app f a)
  | _ + 1, e => some e

/-! ## `LetOk` of the models (PROVED, no premise) -/

theorem letOk_liftM (k : Nat) : ∀ (e : Lean.Expr) (s d : Nat), LetOk k (liftM e s d) = LetOk k e := by
  intro e
  induction e with
  | bvar i => intro s d; unfold liftM; split <;> rfl
  | app f a ihf iha => intro s d; simp only [liftM, LetOk, ihf, iha]
  | lam n t b bi iht ihb => intro s d; simp only [liftM, LetOk, iht, ihb]
  | forallE n t b bi iht ihb => intro s d; simp only [liftM, LetOk, iht, ihb]
  | letE n t v b nd iht ihv ihb => intro s d; simp only [liftM, LetOk, iht, ihv, ihb]
  | mdata m e ih => intro s d; simp only [liftM, LetOk, ih]
  | proj sn i e ih => intro s d; simp only [liftM, LetOk, ih]
  | _ => intro s d; simp [liftM, LetOk]

theorem letOk_lowerCore (k : Nat) : ∀ (e : Lean.Expr) (s d : Nat), LetOk k (lowerCore e s d) = LetOk k e := by
  intro e
  induction e with
  | bvar i => intro s d; unfold lowerCore; split <;> rfl
  | app f a ihf iha => intro s d; simp only [lowerCore, LetOk, ihf, iha]
  | lam n t b bi iht ihb => intro s d; simp only [lowerCore, LetOk, iht, ihb]
  | forallE n t b bi iht ihb => intro s d; simp only [lowerCore, LetOk, iht, ihb]
  | letE n t v b nd iht ihv ihb => intro s d; simp only [lowerCore, LetOk, iht, ihv, ihb]
  | mdata m e ih => intro s d; simp only [lowerCore, LetOk, ih]
  | proj sn i e ih => intro s d; simp only [lowerCore, LetOk, ih]
  | _ => intro s d; simp [lowerCore, LetOk]

theorem letOk_lowerM (k : Nat) (e : Lean.Expr) (s d : Nat) : LetOk k (lowerM e s d) = LetOk k e := by
  unfold lowerM
  split
  · rfl
  · exact letOk_lowerCore k e s d

theorem letOk_inst1M (k : Nat) {a : Lean.Expr} (ha : LetOk k a = true) :
    ∀ (b : Lean.Expr) (off : Nat), LetOk k b = true → LetOk k (inst1M b a off) = true := by
  intro b
  induction b with
  | bvar i =>
    intro off _
    unfold inst1M
    split
    · rfl
    · split
      · rw [letOk_liftM]; exact ha
      · rfl
  | app f x ihf ihx =>
    intro off h
    simp only [LetOk, Bool.and_eq_true] at h
    simp only [inst1M, LetOk, Bool.and_eq_true]
    exact ⟨ihf off h.1, ihx off h.2⟩
  | lam n t b bi iht ihb =>
    intro off h
    simp only [LetOk, Bool.and_eq_true] at h
    simp only [inst1M, LetOk, Bool.and_eq_true]
    exact ⟨iht off h.1, ihb (off + 1) h.2⟩
  | forallE n t b bi iht ihb =>
    intro off h
    simp only [LetOk, Bool.and_eq_true] at h
    simp only [inst1M, LetOk, Bool.and_eq_true]
    exact ⟨iht off h.1, ihb (off + 1) h.2⟩
  | letE n t v b nd iht ihv ihb =>
    intro off h
    simp only [LetOk, Bool.and_eq_true] at h
    simp only [inst1M, LetOk, Bool.and_eq_true]
    exact ⟨⟨iht off h.1.1, ihv off h.1.2⟩, ihb (off + 1) h.2⟩
  | mdata m e ih => intro off h; simp only [LetOk] at h; simp only [inst1M, LetOk]; exact ih off h
  | proj sn i e ih => intro off h; simp only [LetOk] at h; simp only [inst1M, LetOk]; exact ih off h
  | _ => intro off h; simpa [inst1M] using h

theorem letOk_betaM (k : Nat) : ∀ (f a : Lean.Expr), LetOk k f = true → LetOk k a = true →
    LetOk k (betaM f a) = true := by
  intro f
  induction f with
  | lam n t b bi _ _ =>
    intro a hf ha
    simp only [LetOk, Bool.and_eq_true] at hf
    exact letOk_inst1M k ha b 0 hf.2
  | mdata m e ih => intro a hf ha; simp only [LetOk] at hf; simp only [betaM]; exact ih a hf ha
  | _ =>
    intro a hf ha
    simp only [betaM, LetOk, Bool.and_eq_true] <;> simp_all [LetOk]

theorem letOk_eqvM (k : Nat) : ∀ (a b : Lean.Expr), eqvM a b = true → LetOk k b = true → LetOk k a = true := by
  intro a
  induction a with
  | fvar x =>
    intro b h hb
    cases b <;> simp only [eqvM] at h <;> try contradiction
    rename_i y
    have : x.name = y.name := eq_of_beq h
    have hxy : x = y := by cases x; cases y; simp_all
    subst hxy; exact hb
  | app f x ihf ihx =>
    intro b h hb
    cases b <;> simp only [eqvM] at h <;> try contradiction
    simp only [Bool.and_eq_true] at h
    simp only [LetOk, Bool.and_eq_true] at hb ⊢
    exact ⟨ihf _ h.1 hb.1, ihx _ h.2 hb.2⟩
  | lam n t b bi iht ihb =>
    intro c h hc
    cases c <;> simp only [eqvM] at h <;> try contradiction
    simp only [Bool.and_eq_true] at h
    simp only [LetOk, Bool.and_eq_true] at hc ⊢
    exact ⟨iht _ h.1 hc.1, ihb _ h.2 hc.2⟩
  | forallE n t b bi iht ihb =>
    intro c h hc
    cases c <;> simp only [eqvM] at h <;> try contradiction
    simp only [Bool.and_eq_true] at h
    simp only [LetOk, Bool.and_eq_true] at hc ⊢
    exact ⟨iht _ h.1 hc.1, ihb _ h.2 hc.2⟩
  | letE n t v b nd iht ihv ihb =>
    intro c h hc
    cases c <;> simp only [eqvM] at h <;> try contradiction
    simp only [Bool.and_eq_true] at h
    simp only [LetOk, Bool.and_eq_true] at hc ⊢
    exact ⟨⟨iht _ h.1.1 hc.1.1, ihv _ h.1.2 hc.1.2⟩, ihb _ h.2 hc.2⟩
  | mdata m e ih =>
    intro c h hc
    cases c <;> simp only [eqvM] at h <;> try contradiction
    simp only [LetOk] at hc ⊢
    exact ih _ h hc
  | proj sn i e ih =>
    intro c h hc
    cases c <;> simp only [eqvM] at h <;> try contradiction
    simp only [Bool.and_eq_true] at h
    simp only [LetOk] at hc ⊢
    exact ih _ h.2 hc
  | _ => intro c h hc; simp [LetOk]

theorem letOk_rootFloatN (k : Nat) : ∀ (fuel : Nat) (e r : Lean.Expr), rootFloatN fuel e = some r →
    LetOk k e = true → LetOk k r = true := by
  intro fuel
  induction fuel with
  | zero => intro e r h; simp [rootFloatN] at h
  | succ m ih =>
    intro e r h he
    cases e with
    | letE n t v b nd =>
      cases v with
      | letE n2 t2 v2 w nd2 =>
        simp only [rootFloatN] at h
        simp only [LetOk, Bool.and_eq_true] at he
        refine ih _ _ h ?_
        simp only [LetOk, Bool.and_eq_true, letOk_liftM]
        exact ⟨⟨he.1.2.1.1, he.1.2.1.2⟩, ⟨⟨he.1.1, he.1.2.2⟩, he.2⟩⟩
      | _ =>
        simp only [rootFloatN] at h
        obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [LetOk, Bool.and_eq_true] at he ⊢
        exact ⟨he.1, ih _ _ hr' he.2⟩
    | app f a =>
      cases a with
      | letE n t v b nd =>
        simp only [rootFloatN] at h
        obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [LetOk, Bool.and_eq_true] at he ⊢
        refine ⟨he.2.1, ih _ _ hr' ?_⟩
        simp only [LetOk, Bool.and_eq_true, letOk_liftM]
        exact ⟨he.1, he.2.2⟩
      | _ =>
        simp only [rootFloatN] at h
        have := Option.some.inj h
        subst this; exact he
    | _ =>
      simp only [rootFloatN] at h
      have := Option.some.inj h
      subst this; exact he

/-! ## the correspondence premises (one per operation; NOT proved) and the derived shipped-shape premises -/

/-- PREMISE (NOT proved; extern): `Expr.liftLooseBVars` is `liftM`. -/
def LiftCorr : Prop := ∀ (e : Lean.Expr) (s d : Nat), e.liftLooseBVars s d = liftM e s d
/-- PREMISE (NOT proved; extern): `Expr.lowerLooseBVars` is `lowerM`. -/
def LowerCorr : Prop := ∀ (e : Lean.Expr) (s d : Nat), e.lowerLooseBVars s d = lowerM e s d
/-- PREMISE (NOT proved; extern): `Expr.instantiate1` is `inst1M · · 0`. -/
def Inst1Corr : Prop := ∀ b a : Lean.Expr, b.instantiate1 a = inst1M b a 0
/-- PREMISE (NOT proved; `partial def betaRev`): `f.beta #[a]` is `betaM f a`. -/
def BetaCorr : Prop := ∀ f a : Lean.Expr, f.beta #[a] = betaM f a
/-- PREMISE (NOT proved; extern): `a == b` implies `eqvM a b`. -/
def EqvCorr : Prop := ∀ a b : Lean.Expr, (a == b) = true → eqvM a b = true
/-- PREMISE (NOT proved; `partial def rootFloat`, which itself calls the extern `liftLooseBVars`): the shipped answer is some fuel's
`rootFloatN` answer. -/
def RootFloatCorr : Prop :=
  ∀ v : Lean.Expr, LetOk 0 v = true → ∃ fuel, rootFloatN fuel v = some (Sparkle.Compiler.MachRawSurface.rootFloat v)

theorem liftLooseRange_of (h : LiftCorr) : LiftLooseRange := by
  intro e s d he; rw [h, letOk_liftM]; exact he

theorem lowerLooseRange_of (h : LowerCorr) : LowerLooseRange := by
  intro e s d he; rw [h, letOk_lowerM]; exact he

theorem inst1Range_of (h : Inst1Corr) : Inst1Range := by
  intro n b a hb ha; rw [h]; exact letOk_inst1M n ha b 0 hb

theorem betaRange_of (h : BetaCorr) : BetaRange := by
  intro f a hf ha; rw [h]; exact letOk_betaM 0 f a hf ha

theorem eqvLetOk0_of (h : EqvCorr) : EqvLetOk0 := by
  intro a b hab hb; exact letOk_eqvM 0 a b (h a b hab) hb

theorem rootFloatRange_of (h : RootFloatCorr) : RootFloatRange := by
  intro v hv
  obtain ⟨fuel, hf⟩ := h v hv
  exact letOk_rootFloatN 0 fuel v _ hf hv

/-! ## the composed corollary with the extern ranges replaced by the correspondence premises -/

/-- **Corollary** of `machineShapeNM_typed_all_rawNode'`, the MODEL reader `machineShapeNM`: the six `Range`/`LetOk` premises of
the extern / partial operations `rootFloat`, `instantiate1`, `liftLooseBVars`, `lowerLooseBVars`, `Expr.beta`, `Expr.eqv`
(`RootFloatRange`, `Inst1Range`, `LiftLooseRange`, `LowerLooseRange`, `BetaRange`, `EqvLetOk0`) are replaced by ONE correspondence premise
per operation (`RootFloatCorr`, `Inst1Corr`, `LiftCorr`, `LowerCorr`, `BetaCorr`, `EqvCorr`); the `LetOk 0` behaviour of the kernel-visible
MODELS is PROVED above. `ZeroLitAgrees` (already a correspondence extern `replace` ↔ structural `replaceNoCache`, whose range is
proved in `zeroLit_ok`), `SigTyRange senv` and `hpe` (input conditions) are unchanged. The shipped extern ↔ model agreement is NOT proved.
Same conclusion as the previous corollary. Not a statement about the shipped reader. -/
theorem machineShapeNM_typed_all_rawNode_corr {senv : StructEnv}
    (hroot : RootFloatCorr) (hinst1 : Inst1Corr) (hsig : SigTyRange senv)
    (hz : ZeroLitAgrees) (hll : LiftCorr) (hlo : LowerCorr) (hbeta : BetaCorr)
    (hE : EqvCorr)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hpe : ∀ p : ShapePre, shapePre sm ps ci senv = some p → LetOk 0 p.e = true)
    (h : machineShapeNM sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNormM senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      (∀ (d : MachineData), d.shape = sp → d.ok = true →
        d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
          (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed →
        d.letsAliasOk = true ∧
        ∀ {declName : Name} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
          (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State),
          Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape) :=
  machineShapeNM_typed_all_rawNode' (rootFloatRange_of hroot) (inst1Range_of hinst1) hsig hz
    (liftLooseRange_of hll) (lowerLooseRange_of hlo) (betaRange_of hbeta) (eqvLetOk0_of hE) hpe h

#print axioms letOk_liftM
#print axioms letOk_lowerM
#print axioms letOk_inst1M
#print axioms letOk_betaM
#print axioms letOk_eqvM
#print axioms letOk_rootFloatN
#print axioms machineShapeNM_typed_all_rawNode_corr

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeNM_typed_all_rawNode_corr
  ["RootFloatCorr", "Inst1Corr", "SigTyRange", "ZeroLitAgrees", "LiftCorr", "LowerCorr",
    "BetaCorr", "EqvCorr", "Eq", "Eq"])

/- THROWING: (1) none of the six replaced `Range` constants occurs in the new type; (2) the new conclusion is `isDefEq` to the previous
corollary's conclusion; the binders `sm ps ci ai sp senv hsig hz hpe h` are shared fvars (types `isDefEq`), the six replaced binders are
skipped (fresh mvars in the old type). Mutations: (1) the old conclusion with `execNormM` ↦ `execNorm`; (2) the shared binder `hpe`
dropped from the matching. Both must be rejected. -/
open Meta in
def checkExt (mutate : Nat) : MetaM Unit := do
  let newI ← getConstInfo ``machineShapeNM_typed_all_rawNode_corr
  let oldI ← getConstInfo ``machineShapeNM_typed_all_rawNode'
  let replaced : List Name := [`hroot, `hinst1, `hll, `hlo, `hbeta, `hE]
  for c in [``RootFloatRange, ``Inst1Range, ``LiftLooseRange, ``LowerLooseRange, ``BetaRange, ``EqvLetOk0] do
    if newI.type.getUsedConstants.contains c then throwError "{c} occurs in the new type"
  let rep (e : Expr) : Expr :=
    e.replace fun x => if mutate == 1 && x.isConstOf ``execNormM then some (.const ``execNorm []) else none
  forallTelescope newI.type fun xs nb => do
    let mut oty := oldI.type
    let mut j := 0
    let mut nrep := 0
    for _ in [0:xs.size + 8] do
      match oty with
      | .forallE n d b _ =>
        if replaced.contains n then
          unless j < xs.size && (← xs[j]!.fvarId!.getUserName) == n do throwError "replaced binder {n} not aligned"
          j := j + 1
          nrep := nrep + 1
          oty := b.instantiate1 (← mkFreshExprMVar d)
        else if mutate == 2 && n == `hpe then
          oty := b.instantiate1 (← mkFreshExprMVar d)
        else
          unless j < xs.size do throwError "old type has more binders than new"
          unless (← xs[j]!.fvarId!.getUserName) == n do throwError "binder name mismatch at {j}: {n}"
          unless (← isDefEq d (← xs[j]!.fvarId!.getType)) do throwError "binder type mismatch at {n}"
          oty := b.instantiate1 xs[j]!
          j := j + 1
      | _ => break
    unless nrep == 6 && j == xs.size do throwError "binder bookkeeping failed ({nrep}, {j}, {xs.size})"
    unless (← isDefEq (rep oty) nb) do throwError "conclusions are not defeq"
    logInfo m!"EXT check (mutate={mutate}): conclusion defeq, {xs.size - 6} shared binders, 6 replaced"

run_meta checkExt 0
run_meta (do
  for m in [1, 2] do
    let ok ← (do checkExt m; pure true : MetaM Bool) <|> pure false
    if ok then throwError "mutation {m} was NOT rejected"
  logInfo m!"EXT check: mutations 1,2 rejected")

end Tools.Prototype.ExtModelLetOk

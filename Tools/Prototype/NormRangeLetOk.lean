import Tools.Prototype.PreprocLetOk

/-! # Unit LC14: `NormRange senv` (LetOk 0 preserved by `execNorm`) from per-helper range premises

BUILT (unit LC14): a1 exit 1 (base `run_meta` parse error in ReaderFixpointSpec, fixed by parenthesising), a2 exit 1 (this file), a3 exit 0. No sorry / axiom / native_decide.

**`NormRange` is REPLACED by the premises `RawNodeRange` and `NormNodeRange` (not proved), NOT unconditionally discharged.**

PROVED (this file, conditional on those premises): the step lemma `normStep_ok` (every arm of `normStep` keeps `LetOk 0`, given a table that does),
the fuel induction `tabOk_fuel`, and `normRange_of : NormRange senv` from the premises below.
The `normStep` arms that BUILD terms are proved here: `ashr` (through `ashrE`/`machSigBin`, structural), `.lam`,
`.letE`, and the two `instantiate1` arms (through `Inst1Range`, the existing PREMISE).
PREMISES (correspondence/range NOT proved; each names the ONE call it covers):
* `RawNodeRange senv`: `Sparkle.Compiler.MachRawSurface.rawNode senv.prodMatch` (uses `liftLooseBVars 0 n`, `beta`, `peel`).
* `NormNodeRange senv`: `machNormNode senv` (the node rewriter, ~40 arms calling machNormPure/Ap/ApLift/Map).
`LiftRange` (offsets 0/1 only) does not cover the arbitrary `liftLooseBVars 0 n` / `beta` of `rawNode`, so no existing premise covers either call.
No counterexample was found for either (no arm of the shipped text creates an `fvar`); that is NOT a proof. -/
namespace Tools.Prototype.NormRangeLetOk
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk

/-- PREMISE (not proved): the raw-surface node rewriter invents no `_machLet j` placeholder. -/
def RawNodeRange (senv : StructEnv) : Prop :=
  ∀ e e', LetOk 0 e = true → Sparkle.Compiler.MachRawSurface.rawNode senv.prodMatch e = some e' →
    LetOk 0 e' = true

/-- PREMISE (not proved): the node normaliser `machNormNode` invents no `_machLet j` placeholder. -/
def NormNodeRange (senv : StructEnv) : Prop :=
  ∀ e, LetOk 0 e = true → LetOk 0 (machNormNode senv e) = true

theorem machSigBin_ok {n : Nat} {dom : Lean.Expr} (hd : LetOk n dom = true) (m inst : Name) (w : Nat)
    {a b : Lean.Expr} (ha : LetOk n a = true) (hb : LetOk n b = true) :
    LetOk n (machSigBin m inst dom w a b) = true := by
  simp [machSigBin, machSigT, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB, LetOk, letOk_natLit, hd, ha, hb]

theorem ashrE_ok {n : Nat} (natE : Nat → Lean.Expr) (binE : Name → Lean.Expr → Lean.Expr → Lean.Expr)
    (hnat : ∀ k, LetOk n (natE k) = true)
    (hbin : ∀ m a b, LetOk n a = true → LetOk n b = true → LetOk n (binE m a b) = true)
    {dom x y : Lean.Expr} (hd : LetOk n dom = true) (hx : LetOk n x = true) (hy : LetOk n y = true) (w : Nat) :
    LetOk n (Sparkle.Compiler.MachSignOps.ashrE natE binE dom w x y) = true := by
  have hm : LetOk n (Sparkle.Compiler.MachSignOps.fillE natE dom w
      (Sparkle.Compiler.MachSignOps.msbE natE dom w x)) = true := by
    simp [Sparkle.Compiler.MachSignOps.msbE, Sparkle.Compiler.MachSignOps.fillE,
      Sparkle.Compiler.MachSignOps.bvT, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB, LetOk, hnat, hd, hx]
  unfold Sparkle.Compiler.MachSignOps.ashrE
  exact hbin _ _ _ (hbin _ _ _ (hbin _ _ _ hx hm) hy) hm

set_option maxHeartbeats 16000000 in
/-- `ashrView?` only returns the spine's own arguments (same case split as `ashrMatch_view`). -/
theorem ashrView_args (fn : Lean.Expr) (args : Array Lean.Expr) (dom nE x y : Lean.Expr)
    (h : ashrView? fn args = some (dom, nE, x, y)) : args = #[dom, nE, x, y] := by
  revert h
  unfold ashrView?
  rcases args with ⟨L⟩
  cases fn with
  | const n us =>
    rcases n with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p5, s5⟩ | ⟨p5, i5⟩, s4⟩ | ⟨p4, i4⟩, s3⟩ |
      ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
    all_goals (try unfold_matchers_aux)
    all_goals (try dsimp_sparse_aux)
    all_goals (repeat' split)
    all_goals first
      | (intro h; cases h; rfl)
      | (intro h; cases h)
      | rfl
      | (subst_vars; intro h; cases h; rfl)
      | (subst_vars; intro h; cases h)
      | (exfalso; contradiction)
      | (rcases L with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, L'⟩⟩⟩⟩⟩ <;>
          first
            | (intro h; cases h; rfl)
            | (intro h; cases h)
            | (subst_vars; intro h; cases h; rfl)
            | (subst_vars; intro h; cases h)
            | (exfalso; contradiction)
            | (exfalso; simp at *; done)
            | (exfalso; simp at *; omega))
  | _ => intro h; cases h

theorem ashrView_ok {n : Nat} {fn : Lean.Expr} {args : Array Lean.Expr} (hargs : ∀ a ∈ args, LetOk n a = true)
    {dom nE x y : Lean.Expr} (h : ashrView? fn args = some (dom, nE, x, y)) :
    LetOk n dom = true ∧ LetOk n x = true ∧ LetOk n y = true := by
  have := ashrView_args fn args dom nE x y h
  subst this
  exact ⟨hargs _ (by simp), hargs _ (by simp), hargs _ (by simp)⟩

/-- The table `h` keeps `LetOk 0`. -/
def TabOk (h : (c : Lean.Expr) → Option Lean.Expr) : Prop :=
  ∀ e r, LetOk 0 e = true → h e = some r → LetOk 0 r = true

theorem normStep_ok {senv : StructEnv} (hraw : RawNodeRange senv) (hnode : NormNodeRange senv)
    (hinst : Inst1Range) {tab : (c : Lean.Expr) → Option Lean.Expr} (ht : TabOk tab) :
    ∀ (e r : Lean.Expr), LetOk 0 e = true → (normStep senv e).run tab = some r → LetOk 0 r = true := by
  intro e r he hr
  cases e with
  | app f a =>
    simp only [normStep] at hr
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
    simp only [normStep] at hr
    simp only [LetOk, Bool.and_eq_true] at he
    simp only [FM.bind, FM.call, FM.pure, Option.bind_eq_some_iff, Option.some.injEq] at hr
    obtain ⟨b', hb', rfl⟩ := hr
    simp only [LetOk, Bool.and_eq_true]
    exact ⟨he.1, ht _ _ he.2 hb'⟩
  | letE nm t v b nd =>
    simp only [normStep] at hr
    simp only [LetOk, Bool.and_eq_true] at he
    split at hr
    · exact ht _ _ (hinst 0 b v he.2 he.1.2) hr
    · split at hr
      · exact ht _ _ (hinst 0 b v he.2 he.1.2) hr
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

theorem tabOk_fuel {senv : StructEnv} (hraw : RawNodeRange senv) (hnode : NormNodeRange senv)
    (hinst : Inst1Range) : ∀ n, TabOk (machNormF n senv)
  | 0 => fun e r _ h => by
    have : machNormF 0 senv e = none := rfl
    rw [this] at h; cases h
  | n + 1 => fun e r he h =>
    normStep_ok hraw hnode hinst (tabOk_fuel hraw hnode hinst n) e r he h

/-- **PROVED** from `RawNodeRange`, `NormNodeRange` (PREMISES, one call each) and the existing `Inst1Range`. -/
theorem normRange_of {senv : StructEnv} (hraw : RawNodeRange senv) (hnode : NormNodeRange senv)
    (hinst : Inst1Range) : NormRange senv := by
  intro e en he h
  obtain ⟨n, hn⟩ := (execNorm_iff senv).mp h
  exact tabOk_fuel hraw hnode hinst n e en he hn

/-- `machineShapeN_lets''` WITHOUT `hnorm : NormRange senv`: it is replaced by the two named helper premises. -/
theorem machineShapeN_lets''_noNorm {senv : StructEnv} (hroot : RootFloatRange) (hlift : LiftRange)
    (hinst1 : Inst1Range) (hsig : SigTyRange senv) (hz : ZeroLitAgrees)
    (hraw : RawNodeRange senv) (hnode : NormNodeRange senv)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hpe : ∀ p : ShapePre, shapePre sm ps ci senv = some p → LetOk 0 p.e = true)
    (hstart : ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p →
      execNorm senv p.e = some en → StartDomOk senv (shapeMid senv p en))
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp :=
  machineShapeN_lets'' hroot hlift hinst1 hsig hz (normRange_of hraw hnode hinst1) hpe hstart h

#print axioms normStep_ok
#print axioms normRange_of
#print axioms machineShapeN_lets''_noNorm

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeN_lets''_noNorm
  ["RootFloatRange", "LiftRange", "Inst1Range", "SigTyRange", "ZeroLitAgrees", "RawNodeRange", "NormNodeRange", "Eq",
    "StartDomOk", "Eq"])

end Tools.Prototype.NormRangeLetOk

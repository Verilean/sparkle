import Tools.Prototype.ReaderFixpointWrapper

/-! # Unit LC11b prototype: a kernel-visible `execNorm`, and the sharpened `machNorm` premises

Review check of LC11 (c57a5350) against REVIEW-LC11: (1) the wrapper's several table reads are combined by
`ext_wtab_fuel` as `n + N` (an upper bound of the two fuels) with `wtab_mono` as the monotonicity lemma — complies;
(2) the refusal `some none` is covered (`r : Option MachineShape`, `_fail_iff`) — complies; (3) the docstrings and
ledger say outer `none` = OUT = "no result in the model" and draw no termination/divergence conclusion — complies
(wording tightened below).

NEW here (REVIEW-LC11b: priority = the premise-free executable normaliser; no new premise about the real `machNorm`).
* `execNorm senv : Expr → Option Expr` — `partial_fixpoint` of the SAME body `normStep senv` (as `execBlock`).
  PROVED (no premise): `execNorm_iff : execNorm senv e = some r ↔ ∃ n, machNormF n senv e = some r`,
  `execNorm_eq_lfp`, `execNorm_unfold`.
* `xtabE`, `machineShapeN` — a NEW wrapper against `execNorm` + `execBlock`, DISTINCT from `machineShapeX` (which uses
  the real `machNorm`).  PROVED PREMISE-FREE (relative to the fuel model): `machineShapeN_iff_fuel`, `machineShapeN_none_iff`
  (outer `none` = no finite derivation in the model; nothing about running or termination).  This does NOT discharge
  `NormSound`/`NormTotal` of `machineShapeX`.
* `ext_wtab_of_reach` — common fuel `n + N` for finitely many reached queries (monotone via `wtab_mono`).
* OPEN, not assumed anywhere: `∀ e, execNorm senv e = some (machNorm senv e)` — a STRONG SUFFICIENT condition (finite
  model derivation AND agreement on EVERY `Expr`) for discharging `NormSound`/`NormTotal` of `machineShapeX`; not shown
  to be necessary (a local transfer may restrict the inputs to the expressions the wrapper queries). Its scope is the
  normaliser replacement ONLY: `TwinCoverAt` (the seven shipped readers), shape reflection and runtime fit are unaffected.
  PROVED equivalences: `NormSound senv ↔ ∀ e r, execNorm e = some r → machNorm e = r`;
  `NormSound ∧ NormTotal ↔ ∀ e, execNorm e = some (machNorm e)`.
`TwinCoverAt` stays OPEN; production untouched; no switch.  BUILT (unit LC11b): b3 exit 0 (254 jobs), test b4 exit 0 (259 jobs). No sorry / axiom /
native_decide. -/
namespace Tools.Prototype.ReaderExec
open Lean.Order Sparkle.Compiler.Elab Tools.ShippingReaderFuel Tools.Prototype.ReaderLfp

/-- The kernel-visible normaliser: `partial_fixpoint` of the same body `normStep senv` as `machNormF`. -/
def execNorm (senv : StructEnv) (e : Lean.Expr) : Option Lean.Expr :=
  (normStep senv e).run (execNorm senv)
partial_fixpoint monotonicity by
  intro h₁ h₂ hle c
  exact Fn_mono (κ := Lean.Expr) (R := fun _ => Lean.Expr) (normStep senv) h₁ h₂ hle c

theorem execNorm_eq_lfp (senv : StructEnv) :
    execNorm senv = lfp (κ := Lean.Expr) (R := fun _ => Lean.Expr) (normStep senv) := by
  unfold Tools.Prototype.ReaderLfp.lfp
  with_unfolding_all rfl

theorem execNorm_unfold (senv : StructEnv) (e : Lean.Expr) :
    execNorm senv e = (normStep senv e).run (execNorm senv) := execNorm.eq_1 senv e

/-- **PROVED, premise-free**: `execNorm` answers exactly where some fuel of `machNormF` does. -/
theorem execNorm_iff (senv : StructEnv) {e r : Lean.Expr} :
    execNorm senv e = some r ↔ ∃ n, machNormF n senv e = some r := by
  rw [execNorm_eq_lfp]
  exact lfp_iff_fuel (κ := Lean.Expr) (R := fun _ => Lean.Expr) (compact_normStep senv)

/-- `execNorm` is sound for the fuel twin, and total on exactly its answers (restating `execNorm_iff`
with the two premises' shapes). -/
theorem normSound_iff_X (senv : StructEnv) :
    NormSound senv ↔ ∀ e r, execNorm senv e = some r → machNorm senv e = r := by
  constructor
  · intro hs e r h
    obtain ⟨n, hn⟩ := (execNorm_iff senv).mp h
    exact hs e n r hn
  · intro hx e n r h
    exact hx e r ((execNorm_iff senv).mpr ⟨n, h⟩)

theorem normSound_total_iff_X (senv : StructEnv) :
    NormSound senv ∧ NormTotal senv ↔ ∀ e, execNorm senv e = some (machNorm senv e) := by
  constructor
  · rintro ⟨hs, ht⟩ e
    obtain ⟨n, hn⟩ := ht e
    exact (execNorm_iff senv).mpr ⟨n, hn⟩
  · intro h
    refine ⟨(normSound_iff_X senv).mpr (fun e r hr => ?_), fun e => ?_⟩
    · rw [h e] at hr; exact Option.some.inj hr
    · exact (execNorm_iff senv).mp (h e)

/-- Finitely many reached queries have one common fuel (`n + N`, by `wtab_mono`). -/
theorem ext_wtab_of_reach {senv : StructEnv} :
    ∀ L : List (Sigma WCall.Res), (∀ q ∈ L, ∃ n, wtab senv n q.1 = some q.2) →
      ∃ N, Ext (wtab senv N) L := by
  intro L
  induction L with
  | nil => intro _; exact ⟨0, ext_nil _⟩
  | cons q L ih =>
    intro hL
    obtain ⟨N, hN⟩ := ih (fun p hp => hL p (List.mem_cons.mpr (Or.inr hp)))
    obtain ⟨n, hn⟩ := hL q (List.mem_cons.mpr (Or.inl rfl))
    refine ⟨n + N, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact wtab_mono senv (Nat.le_add_right n N) _ _ hn
    · exact wtab_mono senv (Nat.le_add_left N n) _ _ (hN p hp)

section Wrapper
variable {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {senv : StructEnv}
  {ai : Bool}

/-! ## The wrapper against `execNorm`: PREMISE-FREE relative to the fuel model -/

end Wrapper

/-- The wrapper's table with BOTH reads kernel-visible. -/
def xtabE (senv : StructEnv) : (c : WCall) → Option (WCall.Res c)
  | .norm e => execNorm senv e
  | .blk c => execBlock senv c

def machineShapeN (symbolicMode : Bool) (parameters : List (String × Nat)) (ci : Lean.ConstantInfo)
    (senv : StructEnv) (allowInsts : Bool := true) : Option (Option MachineShape) :=
  (shapeW symbolicMode parameters ci senv allowInsts).run (xtabE senv)

theorem wtab_le_xtabE (senv : StructEnv) (n : Nat) : HLe (wtab senv n) (xtabE senv) := by
  intro c r h
  cases c with
  | norm e => exact (execNorm_iff senv).mpr ⟨n, h⟩
  | blk c => exact (execBlock_iff senv).mpr ⟨n, h⟩

section Wrapper2
variable {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {senv : StructEnv}
  {ai : Bool}

theorem machineShapeN_fuel {r : Option MachineShape}
    (h : machineShapeN sm ps ci senv ai = some r) :
    ∃ n, machineShapeF n sm ps ci senv ai = some r := by
  have h' : (shapeW sm ps ci senv ai).run (xtabE senv) = some r := h
  obtain ⟨L, e, k⟩ := (compact_shapeW sm ps ci senv ai).ok (xtabE senv) r h'
  obtain ⟨N, hN⟩ := ext_wtab_of_reach (senv := senv) L (by
    intro q hq
    obtain ⟨c, y⟩ := q
    have hx : xtabE senv c = some y := e _ hq
    cases c with
    | norm e' => exact (execNorm_iff senv).mp hx
    | blk c' => exact (execBlock_iff senv).mp hx)
  exact ⟨N, k (wtab senv N) hN⟩

/-- **PROVED, no premise** (relative to the fuel model `machineShapeF`): success AND refusal. -/
theorem machineShapeN_iff_fuel {r : Option MachineShape} :
    machineShapeN sm ps ci senv ai = some r ↔ ∃ n, machineShapeF n sm ps ci senv ai = some r :=
  ⟨machineShapeN_fuel, fun ⟨n, h⟩ => (shapeW sm ps ci senv ai).mono _ _ (wtab_le_xtabE senv n) r h⟩

/-- Outer `none` = "no finite derivation in the model" (NOT a statement about running or termination). -/
theorem machineShapeN_none_iff :
    machineShapeN sm ps ci senv ai = none ↔ ∀ n, machineShapeF n sm ps ci senv ai = none := by
  constructor
  · intro h n
    cases hn : machineShapeF n sm ps ci senv ai with
    | none => rfl
    | some r =>
      have := machineShapeN_iff_fuel.mpr ⟨n, hn⟩
      rw [h] at this; cases this
  · intro h
    cases hx : machineShapeN sm ps ci senv ai with
    | none => rfl
    | some r =>
      obtain ⟨n, hn⟩ := machineShapeN_fuel hx
      rw [h n] at hn; cases hn

end Wrapper2

#print axioms execNorm_iff
#print axioms machineShapeN_iff_fuel
#print axioms machineShapeN_none_iff

end Tools.Prototype.ReaderExec

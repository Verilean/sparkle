import Tools.Prototype.ReaderFixpointExec
import Tools.ShippingReaderFuelShapeEval

/-! # Unit LC11 prototype: wrapper-level correspondence `machineShapeX` ↔ `machineShapeF n`

Block level (LC8/LC9): `execBlock_iff : execBlock senv c = some r ↔ ∃ n, readF senv n c = some r`.
This file lifts it to the WRAPPER `shapeW` (`machineShapeX` = `shapeW` against `xtab senv`;
`machineShapeF n` = `shapeW` against `wtab senv n`), using `compact_shapeW` (finitely many table reads) and
`wtab` monotonicity (`wtab_mono`).

Result encodings (the same on both sides, projection = identity): outer `none` = OUT (no finite
derivation / fuel too small), `some none` = ordinary refusal (old `none`), `some (some s)` = success.

* `machineShapeX_iff_fuel` : under `NormSound` + `NormTotal`,
    `machineShapeX … = some r ↔ ∃ n, machineShapeF n … = some r`   (r : Option MachineShape, so
    refusal and success alike; `_ok_iff`, `_fail_iff` are the two instances).
* `machineShapeF_le_X`     : (needs only `NormSound`) `machineShapeF n = some r → machineShapeX = some r`.
* `machineShapeX_none_iff` : `machineShapeX = none ↔ ∀ n, machineShapeF n = none`.

PREMISES (hypotheses of the theorems, NOT proved, not axioms): `xtab` answers `machNorm` with the REAL
`partial` function `machNorm`; `wtab` answers it with the fuel twin `machNormF`.  Their relation is
the `machNorm` part of the transcription question (O2) and is not proved:
* `NormSound senv`: every finished `machNormF` answer equals `machNorm senv e` (used by ← only).
* `NormTotal senv`: every `machNorm senv e` is reached by some fuel of `machNormF` (used by → only);
  it is stronger than needed (only the `e` the wrapper actually queries matter) and may well fail where
  `machNorm` diverges.
Nothing here relates the shipped `partial def` readers to anything (`TwinCoverAt` stays OPEN); production
`machineShape?` and the seven `partial def`s are untouched; no switch (A1 not done).

BUILT/UNBUILT: see REPORT-LC11.md.  No sorry / axiom / native_decide. -/
namespace Tools.Prototype.ReaderExec
open Sparkle.Compiler.Elab Tools.ShippingReaderFuel

/-- PREMISE: finished fuel answers of `machNormF` are answers of the real `machNorm`. -/
def NormSound (senv : StructEnv) : Prop :=
  ∀ (e : Lean.Expr) (n : Nat) (r : Lean.Expr), machNormF n senv e = some r → machNorm senv e = r

/-- PREMISE: the real `machNorm` answer is reached by some fuel of `machNormF`. -/
def NormTotal (senv : StructEnv) : Prop :=
  ∀ e : Lean.Expr, ∃ n, machNormF n senv e = some (machNorm senv e)

theorem wtab_le_xtab {senv : StructEnv} (hs : NormSound senv) (n : Nat) :
    HLe (wtab senv n) (xtab senv) := by
  intro c r h
  cases c with
  | norm e =>
    have h' : machNormF n senv e = some r := h
    show some (machNorm senv e) = some r
    rw [hs e n r h']
  | blk c =>
    have h' : readF senv n c = some r := h
    exact (execBlock_iff senv).mpr ⟨n, h'⟩

theorem ext_wtab_fuel {senv : StructEnv} (ht : NormTotal senv) :
    ∀ L : List (Sigma WCall.Res), Ext (xtab senv) L → ∃ N, Ext (wtab senv N) L := by
  intro L
  induction L with
  | nil => intro _; exact ⟨0, ext_nil _⟩
  | cons q L ih =>
    intro hL
    have hq : xtab senv q.1 = some q.2 := hL q (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨N, hN⟩ := ih (fun p hp => hL p (List.mem_cons.mpr (Or.inr hp)))
    obtain ⟨c, r⟩ := q
    have hn : ∃ n, wtab senv n c = some r := by
      cases c with
      | norm e =>
        have h1 : some (machNorm senv e) = some r := hq
        obtain ⟨n, hn⟩ := ht e
        refine ⟨n, ?_⟩
        show machNormF n senv e = some r
        rw [hn]; exact h1
      | blk c =>
        have h1 : execBlock senv c = some r := hq
        obtain ⟨n, hn⟩ := (execBlock_iff senv).mp h1
        exact ⟨n, hn⟩
    obtain ⟨n, hn⟩ := hn
    refine ⟨n + N, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact wtab_mono senv (Nat.le_add_right n N) _ _ hn
    · exact wtab_mono senv (Nat.le_add_left N n) _ _ (hN p hp)

section Wrapper
variable {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {senv : StructEnv}
  {ai : Bool}

/-- ← (premise `NormSound` only): a finished fuel answer is the executable answer. -/
theorem machineShapeF_le_X (hs : NormSound senv) {n : Nat} {r : Option MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some r) :
    machineShapeX sm ps ci senv ai = some r :=
  (shapeW sm ps ci senv ai).mono _ _ (wtab_le_xtab hs n) r h

/-- → (premise `NormTotal` only): an executable answer is a finished fuel answer. -/
theorem machineShapeX_fuel (ht : NormTotal senv) {r : Option MachineShape}
    (h : machineShapeX sm ps ci senv ai = some r) :
    ∃ n, machineShapeF n sm ps ci senv ai = some r := by
  have h' : (shapeW sm ps ci senv ai).run (xtab senv) = some r := h
  obtain ⟨L, e, k⟩ := (compact_shapeW sm ps ci senv ai).ok (xtab senv) r h'
  obtain ⟨N, hN⟩ := ext_wtab_fuel ht L e
  exact ⟨N, k (wtab senv N) hN⟩

/-- **Wrapper-level correspondence**, success and ordinary refusal alike (`r : Option MachineShape`;
outer `none` = OUT is the third case, `machineShapeX_none_iff`). -/
theorem machineShapeX_iff_fuel (hs : NormSound senv) (ht : NormTotal senv)
    {r : Option MachineShape} :
    machineShapeX sm ps ci senv ai = some r ↔ ∃ n, machineShapeF n sm ps ci senv ai = some r :=
  ⟨machineShapeX_fuel ht, fun ⟨_, h⟩ => machineShapeF_le_X hs h⟩

theorem machineShapeX_ok_iff (hs : NormSound senv) (ht : NormTotal senv) {s : MachineShape} :
    machineShapeX sm ps ci senv ai = some (some s) ↔
      ∃ n, machineShapeF n sm ps ci senv ai = some (some s) :=
  machineShapeX_iff_fuel hs ht

theorem machineShapeX_fail_iff (hs : NormSound senv) (ht : NormTotal senv) :
    machineShapeX sm ps ci senv ai = some none ↔
      ∃ n, machineShapeF n sm ps ci senv ai = some none :=
  machineShapeX_iff_fuel hs ht

/-- OUT: the executable wrapper has no answer iff every fuel is OUT. -/
theorem machineShapeX_none_iff (hs : NormSound senv) (ht : NormTotal senv) :
    machineShapeX sm ps ci senv ai = none ↔ ∀ n, machineShapeF n sm ps ci senv ai = none := by
  constructor
  · intro h n
    cases hn : machineShapeF n sm ps ci senv ai with
    | none => rfl
    | some r => rw [machineShapeF_le_X hs hn] at h; cases h
  · intro h
    cases hx : machineShapeX sm ps ci senv ai with
    | none => rfl
    | some r =>
      obtain ⟨n, hn⟩ := machineShapeX_fuel ht hx
      rw [h n] at hn; cases hn

end Wrapper

#print axioms machineShapeF_le_X
#print axioms machineShapeX_fuel
#print axioms machineShapeX_iff_fuel
#print axioms machineShapeX_none_iff

end Tools.Prototype.ReaderExec

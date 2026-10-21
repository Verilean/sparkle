import Tools.ShippingEnvSnapshot
-- BUILT (unit SR2i): r1 exit 0. Axioms of getEnvFrame_of_readKeeps, envFrame_set, runsTo_det: [propext, Classical.choice, Quot.sound].
open Lean in
/-! # Unit SR2i: necessary conditions for a correspondence with the real `ST.Ref`

NO correspondence with the real `ST.Ref` is established here and no law is added to any structure.  This file
states, as `Prop`s over the REAL types (`Void IO.RealWorld`, `ST.Ref.get/set`), the cell-level conditions that a
runtime/heap model would have to satisfy (`ReadKeeps`, `ReadWorld`, `SetGet`, `SetFrame`), and PROVES the
implications that hold from definitions:

* `runsTo_det`            — determinism of a run (law-free: a run is a function of the start world);
* `readOf_get`            — the value `get` returns is `readOf` (definitional);
* `ReadWorld.readKeeps`   — `ReadWorld r → ReadKeeps r`;
* `getEnvFrame_of_readKeeps` — `ReadKeeps cref → GetEnvFrame` (SR2h's single-primitive premise follows from the
  weaker cell condition that a read of the Core cell does not change what the Core cell reads);
* `envFrame_set`          — a `set` of a cell distinct from `cref` keeps `envAt`, given `SetFrame`.

All of `ReadKeeps/ReadWorld/SetGet/SetFrame` are PREMISES (statements about the opaque `ST.Ref.get/set`); none is
proved of the runtime. -/
namespace Tools.ShippingStRefCorrespondence
open Lean
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (readOf)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingEnvSnapshot (EnvFrame GetEnvFrame)

/-- The world after a `get` of `r` (the value is `readOf r w`, see `readOf_get`). -/
def getW {σ : Type} (r : IO.Ref σ) (w : Void IO.RealWorld) : Void IO.RealWorld :=
  match (ST.Ref.get r : ST IO.RealWorld σ) w with
  | .mk _ w' => w'

/-- The world after a `set` of `r`. -/
def setW {σ : Type} (r : IO.Ref σ) (v : σ) (w : Void IO.RealWorld) : Void IO.RealWorld :=
  match (ST.Ref.set r v : ST IO.RealWorld Unit) w with
  | .mk _ w' => w'

/-- C1 (read does not change what the same cell reads).  PREMISE for the real runtime. -/
def ReadKeeps {σ : Type} (r : IO.Ref σ) : Prop := ∀ w, readOf r (getW r w) = readOf r w

/-- C1' (read does not change the world at all; stronger).  PREMISE for the real runtime. -/
def ReadWorld {σ : Type} (r : IO.Ref σ) : Prop := ∀ w, getW r w = w

/-- C3 (get-after-set).  PREMISE for the real runtime. -/
def SetGet {σ : Type} (r : IO.Ref σ) : Prop := ∀ v w, readOf r (setW r v w) = v

/-- C4 (a set of one cell does not change what a different cell reads).  PREMISE for the real runtime. -/
def SetFrame {σ τ : Type} (r : IO.Ref σ) (r' : IO.Ref τ) : Prop :=
  r.ref ≠ r'.ref → ∀ v w, readOf r' (setW r v w) = readOf r' w

theorem ReadWorld.readKeeps {σ : Type} {r : IO.Ref σ} (h : ReadWorld r) : ReadKeeps r := by
  intro w; rw [h w]

/-- The value a `get` returns is `readOf r w` (definitional: `readOf` is defined by the `get`). -/
theorem readOf_get {σ : Type} (r : IO.Ref σ) (w : Void IO.RealWorld) :
    (ST.Ref.get r : ST IO.RealWorld σ) w = .mk (readOf r w) (getW r w) := by
  unfold readOf getW
  cases (ST.Ref.get r : ST IO.RealWorld σ) w <;> rfl

/-- Determinism: a run is a function of the start world, so two runs from one world agree.  Law-free; it says
nothing about the real runtime (it is a fact about the logic's function space). -/
theorem runsTo_det {α : Type} {m : MetaM α} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {a b : α}
    {w' w'' : Void IO.RealWorld}
    (h1 : RunsTo m mctx mref cctx cref w a w') (h2 : RunsTo m mctx mref cctx cref w b w'') :
    a = b ∧ w' = w'' := by
  unfold RunsTo at h1 h2
  rw [h1] at h2
  cases h2; exact ⟨rfl, rfl⟩

section real
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- SR2h's single-primitive premise `GetEnvFrame` follows from the cell condition `ReadKeeps cref`. -/
theorem getEnvFrame_of_readKeeps (hk : ReadKeeps cref) : GetEnvFrame mctx mref cctx cref := by
  intro w e w' h
  unfold Tools.ShippingEntrySoundness.RunsTo at h
  unfold envAt
  have key : (Lean.getEnv : MetaM Environment) mctx mref cctx cref w =
      (match (ST.Ref.get cref : ST IO.RealWorld Core.State) w with
        | .mk v w2 => EST.Out.ok v.env w2) := rfl
  rw [key, readOf_get] at h
  cases h
  exact congrArg Core.State.env (hk w)

/-- A `set` of a cell `r` other than `cref` keeps the Core environment, given `SetFrame r cref`. -/
theorem envFrame_set {σ : Type} (r : IO.Ref σ) (v : σ) (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref) :
    EnvFrame (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref := by
  intro w u w' h
  unfold Tools.ShippingEntrySoundness.RunsTo at h
  unfold envAt
  have key : (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref w =
      (match (ST.Ref.set r v : ST IO.RealWorld Unit) w with
        | .mk u w2 => EST.Out.ok u w2) := rfl
  rw [key] at h
  have hw : setW r v w = w' := by
    unfold setW; revert h
    cases (ST.Ref.set r v : ST IO.RealWorld Unit) w; intro h; cases h; rfl
  rw [← hw]
  exact congrArg Core.State.env (hf hne v w)

end real
end Tools.ShippingStRefCorrespondence

#print axioms Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps
#print axioms Tools.ShippingStRefCorrespondence.envFrame_set
#print axioms Tools.ShippingStRefCorrespondence.runsTo_det

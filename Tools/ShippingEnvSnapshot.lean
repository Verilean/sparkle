import Tools.ShippingEntryReadsLinked
-- BUILT (unit SR2h): s2 exit 0 (s1 exit 1: one simp-closing error, fixed). Axioms: envSnapshot_of_getConstInfo [propext, Classical.choice, Quot.sound]; Model.getConstM_frame none; Model.snapshot_model [propext].
open Lean in
/-! # Unit SR2h: `EnvSnapshot` from a ONE-operation environment frame, and a pure read-only `Core.State` model

SR2g left `EnvSnapshot cref w1 w2` (`envAt cref w2 = envAt cref w1`) as a named hypothesis.  Here:

PART 1 (real types, law-free reductions).  `EnvFrame x` : every successful run of `x` ends in a world carrying the
same `envAt cref` as its start.  PROVED: `EnvFrame` is closed under `pure` and `bind`
(`EnvFrame.pure/.bind`); `EnvFrame (getConstInfo n)` follows from `EnvFrame getEnv`
(`envFrame_getConstInfo`); hence `EnvSnapshot cref w1 w2` follows from the run of `getConstInfo` between `w1` and
`w2` plus `GetEnvFrame` (`envSnapshot_of_getConstInfo`, `ci_in_envR_of_frame`).  The premise is therefore REPLACED
by the strictly smaller, single-operation statement `GetEnvFrame := EnvFrame getEnv` (the bare `get` of the Core
state writes nothing back); it is NOT proved for the real `ST.Ref`: `ST.Ref.get` is an `@[extern] opaque`
(`Init/System/ST.lean`) and the world it returns is opaque, so the kernel cannot see that `get r w` returns `w`.
This file makes NO claim that `GetEnvFrame` holds of the runtime; it is a PREMISE (one named law about one
primitive), and `EnvSnapshot` is no longer a premise of its own.

PART 2 (a pure model).  `Tools.ShippingEnvSnapshot.Model`: a Core-state-like record `St E` (the environment and
an unrelated rest-field), actions `St E → Out`, with `getEnvM`, `getRestM`, `modifyRestM` and the WRITER `setEnvM`.
PROVED from the definitions (no law): `getEnvM`, `getRestM`, `modifyRestM` preserve the model's `env`; closure under
bind; the model analogue of `getConstInfo` (a read of `env` then a lookup) preserves it, so the model analogue of
`EnvSnapshot` holds; and `setEnvM` does NOT (`setEnvM_not_frame`), so the form discriminates.
NO CORRESPONDENCE with the real `ST.Ref`/`Core.State`/`MetaM` is established: the model is a different type
(`St E` and `Model.Out`, not `Void IO.RealWorld`/`EST`).  What a correspondence would need: a map
`Void IO.RealWorld → St Environment` (the Core state read at a world) such that the real `ST.Ref.get cref` is
sent to `getRestM`/`getEnvM`-shaped steps — i.e. a model of the runtime heap, the same OPEN "fit" as
`Tools/ShippingHeapModel.lean`.

No `sorry`, no axiom, no new law in `RefLawsAOps`. -/
namespace Tools.ShippingEnvSnapshot
open Lean
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (readOf)
open Tools.ShippingEntryReadsLinked (envAt EnvSnapshot getEnv_value getConstInfo_value)

section real
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- A successful run of `x` (in these contexts) ends in a world with the same Core environment as its start. -/
def EnvFrame {α : Type} (x : MetaM α) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  ∀ (w : Void IO.RealWorld) (a : α) (w' : Void IO.RealWorld),
    RunsTo x mctx mref cctx cref w a w' → envAt cref w' = envAt cref w

theorem EnvFrame.pure {α : Type} (a : α) : EnvFrame (Pure.pure a : MetaM α) mctx mref cctx cref := by
  intro w b w' h
  obtain ⟨-, rfl⟩ := Tools.ShippingChildInv.RunsTo.pure_world h
  rfl

theorem EnvFrame.bind {α β : Type} {m : MetaM α} {f : α → MetaM β}
    (hm : EnvFrame m mctx mref cctx cref) (hf : ∀ a, EnvFrame (f a) mctx mref cctx cref) :
    EnvFrame (m >>= f) mctx mref cctx cref := by
  intro w b w'' h
  obtain ⟨a, w1, h1, h2⟩ := Tools.ShippingEntrySoundness.RunsTo.bind h
  exact (hf a w1 b w'' h2).trans (hm w a w1 h1)

/-- **The ONE primitive premise (PREMISE, not proved):** the bare read of the Core environment leaves the Core
environment unchanged.  This is a statement about the opaque `ST.Ref.get`; see the header. -/
def GetEnvFrame (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  EnvFrame (Lean.getEnv : MetaM Environment) mctx mref cctx cref

/-- `getConstInfo` preserves the Core environment, given only that `getEnv` does (the lookup either throws —
no successful run — or returns). -/
theorem envFrame_getConstInfo (n : Name) (hg : GetEnvFrame mctx mref cctx cref) :
    EnvFrame (Lean.getConstInfo n : MetaM ConstantInfo) mctx mref cctx cref := by
  intro w ci w' h
  unfold Lean.getConstInfo at h
  obtain ⟨env, w1, he, hm⟩ := Tools.ShippingEntrySoundness.RunsTo.bind h
  have h1 := hg w env w1 he
  cases hf : env.find? n with
  | none => rw [hf] at hm; exact (Tools.ShippingReflectCtx.throwUnknownConstant_not_runs n hm).elim
  | some i =>
    rw [hf] at hm
    obtain ⟨-, rfl⟩ := Tools.ShippingChildInv.RunsTo.pure_world hm
    exact h1

/-- **`EnvSnapshot` for the `getConstInfo` run, from `GetEnvFrame`** (no `EnvSnapshot` hypothesis). -/
theorem envSnapshot_of_getConstInfo {n : Name} {w1 w2 : Void IO.RealWorld} {ci : ConstantInfo}
    (hg : GetEnvFrame mctx mref cctx cref)
    (hget : RunsTo (Lean.getConstInfo n : MetaM ConstantInfo) mctx mref cctx cref w1 ci w2) :
    EnvSnapshot cref w1 w2 :=
  envFrame_getConstInfo n hg w1 ci w2 hget

/-- The consequence SR2g wanted, with `GetEnvFrame` in place of `EnvSnapshot`. -/
theorem ci_in_envR_of_frame {n : Name} {w1 w2 w3 : Void IO.RealWorld} {ci : ConstantInfo} {envR : Environment}
    (hg : GetEnvFrame mctx mref cctx cref)
    (hget : RunsTo (Lean.getConstInfo n : MetaM ConstantInfo) mctx mref cctx cref w1 ci w2)
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3) :
    envR.find? n = some ci :=
  Tools.ShippingEntryReadsLinked.ci_in_envR hget henv (envSnapshot_of_getConstInfo hg hget)

end real

/-! ## A pure read-only `Core.State` model (NOT connected to the real runtime) -/
namespace Model

/-- A Core-state-like record: the environment and everything else. -/
structure St (E : Type) where
  env : E
  rest : Nat

inductive Out (E α : Type) where
  | ok : α → St E → Out E α
  | error : St E → Out E α

abbrev M (E α : Type) := St E → Out E α

variable {E : Type}

def pureM {α} (a : α) : M E α := fun s => .ok a s
def bindM {α β} (x : M E α) (f : α → M E β) : M E β := fun s =>
  match x s with
  | .ok a s' => f a s'
  | .error s' => .error s'
def getEnvM : M E E := fun s => .ok s.env s
def getRestM : M E Nat := fun s => .ok s.rest s
def modifyRestM (f : Nat → Nat) : M E Unit := fun s => .ok () { s with rest := f s.rest }
/-- The only WRITER of the environment in the model (`setEnv`/`modifyEnv`/`addDecl`'s effect). -/
def setEnvM (e : E) : M E Unit := fun s => .ok () { s with env := e }
/-- Model of `getConstInfo`: read the environment, then look the name up (throw if absent). -/
def getConstM (find : E → Option Nat) : M E Nat :=
  bindM getEnvM fun e => match find e with
    | some c => pureM c
    | none => fun s => .error s

def RunsTo {α} (x : M E α) (s : St E) (a : α) (s' : St E) : Prop := x s = .ok a s'

/-- The model analogue of `EnvFrame`. -/
def Frame {α} (x : M E α) : Prop := ∀ s a s', RunsTo x s a s' → s'.env = s.env

theorem Frame.pure {α} (a : α) : Frame (pureM a : M E α) := by
  intro s b s' h; cases h; rfl

theorem Frame.bind {α β} {x : M E α} {f : α → M E β} (hx : Frame x) (hf : ∀ a, Frame (f a)) :
    Frame (bindM x f) := by
  intro s b s'' h
  unfold RunsTo bindM at h
  cases h1 : x s with
  | error s1 => rw [h1] at h; cases h
  | ok a s1 =>
    rw [h1] at h
    exact (hf a s1 b s'' h).trans (hx s a s1 h1)

/-- **PROVED from the definitions, no law:** the bare read of the environment writes nothing back. -/
theorem getEnvM_frame : Frame (getEnvM : M E E) := by
  intro s a s' h; cases h; rfl

theorem getRestM_frame : Frame (getRestM : M E Nat) := by
  intro s a s' h; cases h; rfl

theorem modifyRestM_frame (f : Nat → Nat) : Frame (modifyRestM f : M E Unit) := by
  intro s a s' h; cases h; rfl

theorem getConstM_frame (find : E → Option Nat) : Frame (getConstM find) := by
  unfold getConstM
  refine getEnvM_frame.bind fun e => ?_
  cases find e with
  | some c => exact Frame.pure c
  | none => intro s a s' h; cases h

/-- Model analogue of `EnvSnapshot` for a `getConstInfo` run followed by anything that only reads/modifies the
rest-field: the environment at the start of a later `getEnv` equals that at the start of the lookup. -/
theorem snapshot_model (find : E → Option Nat) {s1 s2 : St E} {c : Nat} {s3 : St E} {e : E}
    (h1 : RunsTo (getConstM find) s1 c s2) (h2 : RunsTo (getEnvM : M E E) s2 e s3) :
    e = s1.env ∧ find e = some c := by
  have hf := getConstM_frame find s1 c s2 h1
  unfold RunsTo at h2 h1
  unfold getEnvM at h2
  cases h2
  refine ⟨hf, ?_⟩
  unfold getConstM bindM getEnvM at h1
  simp only at h1
  cases hfind : find s1.env with
  | none => rw [hfind] at h1; simp at h1
  | some c' =>
    rw [hfind] at h1
    simp only [pureM, Out.ok.injEq] at h1
    rw [hf, hfind, h1.1]

/-- The writer is NOT a frame: the form discriminates. -/
theorem setEnvM_not_frame : ¬ ∀ (e : Nat), Frame (setEnvM e : M Nat Unit) := by
  intro h
  have := h 1 ⟨0, 0⟩ () ⟨1, 0⟩ rfl
  exact absurd this (by decide)

end Model
end Tools.ShippingEnvSnapshot

#print axioms Tools.ShippingEnvSnapshot.envSnapshot_of_getConstInfo
#print axioms Tools.ShippingEnvSnapshot.Model.getConstM_frame
#print axioms Tools.ShippingEnvSnapshot.Model.snapshot_model

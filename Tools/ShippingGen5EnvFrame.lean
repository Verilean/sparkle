import Tools.ShippingGen5Env
import Tools.ShippingStRefCorrespondence
set_option autoImplicit false
-- NOT BUILT (unit U1, scripts/gen5/DG_ENV_T2_FREEZE_R3.md rev3.1). No sorry / axiom / native_decide.

/-! # DG-ENV unit U1: `EnvFrameEnd` rows for class-B operations, CONDITIONAL

`EnvFrameEnd x` is the `endW` (either outcome) form of an environment frame, the shape the `Laws` clauses use.
U1-1..U1-7 prove it for `pure`, `bind`, `get`, `set`, `modify`, `modifyGet`, `getEnv`; U1-8 carries `ReadsAt`.
The cell premises (`ReadWorld r`, `SetFrame r cref`, `r.ref ≠ cref.ref`) stay HYPOTHESES of the lemmas: this is a
conditional algebra, NOT a supply of C0, and nothing here says the premises hold of the runtime. No `Laws` /
`RefLawsAOps` / `RefLawsATele` / `T1Hyp` / `T1HypND` field, no `GetEnvFrame`, `EnvSnapshot` or
`getEnvFrame_of_readKeeps` is used (U1-7 is proved directly from `Lean.getEnv = cref.get` and `ReadWorld cref`).
No new law, no shared-definition change. Audit: Tests/Gen5/EnvFrameCheck.lean. -/
namespace Tools.ShippingGen5EnvFrame
open Lean
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingChildInv (endW readOf)
open Tools.ShippingStRefCorrespondence (ReadWorld SetFrame getW setW readOf_get)
open Tools.ShippingGen5Env (ReadsAt)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The `endW` (either outcome) form of an environment frame, the shape the `Laws` clauses use. -/
def EnvFrameEnd {α : Type} (x : MetaM α) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  ∀ w : Void IO.RealWorld, envAt cref (endW mctx mref cctx cref x w) = envAt cref w

/-- (U1-1) -/
theorem envFrameEnd_pure {α : Type} (a : α) :
    EnvFrameEnd (Pure.pure a : MetaM α) mctx mref cctx cref := by
  intro w
  have key : (Pure.pure a : MetaM α) mctx mref cctx cref w = EST.Out.ok a w := rfl
  unfold endW
  rw [key]

/-- (U1-2) -/
theorem envFrameEnd_bind {α β : Type} {m : MetaM α} {f : α → MetaM β}
    (hm : EnvFrameEnd m mctx mref cctx cref) (hf : ∀ a, EnvFrameEnd (f a) mctx mref cctx cref) :
    EnvFrameEnd (m >>= f) mctx mref cctx cref := by
  intro w
  have hmw := hm w
  unfold endW at hmw ⊢
  have key : (m >>= f) mctx mref cctx cref w =
      EST.bind (m mctx mref cctx cref) (fun a => f a mctx mref cctx cref) w := rfl
  rw [key]
  unfold EST.bind
  cases hr : m mctx mref cctx cref w with
  | ok a w1 =>
    rw [hr] at hmw
    have h2 := hf a w1
    unfold endW at h2
    exact h2.trans hmw
  | error e w1 =>
    rw [hr] at hmw
    exact hmw

/-- (U1-3) get -/
theorem envFrameEnd_get {σ : Type} {r : IO.Ref σ} (hr : ReadWorld r) :
    EnvFrameEnd (ST.Ref.get r : MetaM σ) mctx mref cctx cref := by
  intro w
  have key : (ST.Ref.get r : MetaM σ) mctx mref cctx cref w =
      (match (ST.Ref.get r : ST IO.RealWorld σ) w with
        | .mk v w2 => EST.Out.ok v w2) := rfl
  unfold endW
  rw [key, readOf_get, hr w]

/-- (U1-4) set -/
theorem envFrameEnd_set {σ : Type} {r : IO.Ref σ} (v : σ) (hne : r.ref ≠ cref.ref)
    (hf : SetFrame r cref) : EnvFrameEnd (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref := by
  intro w
  have key : (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref w =
      (match (ST.Ref.set r v : ST IO.RealWorld Unit) w with
        | .mk u w2 => EST.Out.ok u w2) := rfl
  have hw : endW mctx mref cctx cref (ST.Ref.set r v : MetaM Unit) w = setW r v w := by
    unfold endW setW; rw [key]
  rw [hw]
  unfold envAt
  exact congrArg Core.State.env (hf hne v w)

/-- (U1-5) modify = get;set -/
theorem envFrameEnd_modify {σ : Type} {r : IO.Ref σ} (f : σ → σ)
    (hr : ReadWorld r) (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref) :
    EnvFrameEnd (ST.Ref.modify r f : MetaM Unit) mctx mref cctx cref := by
  have key : (ST.Ref.modify r f : MetaM Unit) =
      ((ST.Ref.get r : MetaM σ) >>= fun v => (ST.Ref.set r (f v) : MetaM Unit)) := rfl
  rw [key]
  exact envFrameEnd_bind (envFrameEnd_get hr) (fun v => envFrameEnd_set (f v) hne hf)

/-- (U1-6) modifyGet -/
theorem envFrameEnd_modifyGet {σ β : Type} {r : IO.Ref σ} (f : σ → β × σ)
    (hr : ReadWorld r) (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref) :
    EnvFrameEnd (ST.Ref.modifyGet r f : MetaM β) mctx mref cctx cref := by
  have key : (ST.Ref.modifyGet r f : MetaM β) =
      ((ST.Ref.get r : MetaM σ) >>= fun v =>
        (ST.Ref.set r (f v).2 : MetaM Unit) >>= fun _ => (Pure.pure (f v).1 : MetaM β)) := rfl
  rw [key]
  exact envFrameEnd_bind (envFrameEnd_get hr) fun v =>
    envFrameEnd_bind (envFrameEnd_set (f v).2 hne hf) fun _ => envFrameEnd_pure _

/-- (U1-7) getEnv -/
theorem envFrameEnd_getEnv (hr : ReadWorld cref) :
    EnvFrameEnd (Lean.getEnv : MetaM Environment) mctx mref cctx cref := by
  intro w
  have key : (Lean.getEnv : MetaM Environment) mctx mref cctx cref w =
      (match (ST.Ref.get cref : ST IO.RealWorld Core.State) w with
        | .mk v w2 => EST.Out.ok v.env w2) := rfl
  unfold endW
  rw [key, readOf_get, hr w]

/-- (U1-8) the consumer form: `ReadsAt` survives an `EnvFrameEnd` operation (E2 composed). -/
theorem readsAt_endW {env₀ : Environment} {α : Type} {x : MetaM α}
    (hx : EnvFrameEnd x mctx mref cctx cref) {w : Void IO.RealWorld} (h : ReadsAt env₀ cref w) :
    ReadsAt env₀ cref (endW mctx mref cctx cref x w) :=
  Tools.ShippingGen5Env.ReadsAt.of_envEq (hx w) h

end Tools.ShippingGen5EnvFrame

#print axioms Tools.ShippingGen5EnvFrame.envFrameEnd_bind
#print axioms Tools.ShippingGen5EnvFrame.envFrameEnd_modify
#print axioms Tools.ShippingGen5EnvFrame.envFrameEnd_getEnv

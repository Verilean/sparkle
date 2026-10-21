import Tools.ShippingChildTeleCP
import Tools.ShippingChildFallbackA
-- BUILT (unit C, round par/u-c): pf10 exit 0 (no sorry; axioms propext, Classical.choice, Quot.sound).
-- No `sorry`, no `axiom`, no `native_decide`, no new law in RefLawsAOps. Assumption beyond the
-- operations bundle: `T : RefLawsATele O.quiet mref cref` (the telescope family), used for the one
-- `forallTelescopeReducing` of `projFieldName?`.
-- Writing-time guesses:
--  P1 `getConstInfoInduct`/`getConstInfoCtor` unfold to `getEnv >>= fun env => match … | some v =>
--     pure v | none => throwError m!"…"`; the message is closed by `okmsg`;
--  P2 `FVarId.getUserName` is `getDecl` (a read of the local context, or `throwUnknownFVar`).

/-! # `projFieldName?` under the admissible boundary

PROVED (given `T`): `projFieldNameA`. The pieces: `getEnv` (`FramedA.env`), the
`getConstInfoInduct`/`getConstInfoCtor` pair (an environment read and a `throwError` of a
message in the `OkMsg` class), the `try … catch` (`Keeps.tryCatch`), the telescope (`T`) and the
`getUserName` walk (a local-context read, or a `throwError`). -/

namespace Tools.ShippingChildProjFieldA
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildFresh
open Tools.ShippingChildTeleCP
open Tools.ShippingChildFallbackA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
  {I : Void IO.RealWorld → Prop}

section Prims
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  (hS : StableA O.quiet I)
include O hA hS

theorem keepsA_throwError {α : Type} (msg : MessageData) (hmsg : OkMsg msg) :
    Keeps mctx mref cctx cref I (Lean.throwError msg : MetaM α) :=
  keeps_iff.mpr (tripleA_throwErr O hA hS msg hmsg)

theorem keepsA_getConstInfoInduct (n : Name) :
    Keeps mctx mref cctx cref I (getConstInfoInduct n : MetaM InductiveVal) := by
  unfold getConstInfoInduct isInductive?
  refine Keeps.bind (Keeps.bind (keepsA_framed O hA hS FramedA.env) fun _ => Keeps.pure _) fun x => ?_
  cases x with
  | some a => exact Keeps.pure a
  | none => exact keepsA_throwError O hA hS _ (by okmsg)

/- `getConstInfoCtor`: the `unreachable!` arm of `isCtor?` at `MetaM` is `panic`, whose
`Inhabited (MetaM _)` instance is `instInhabitedOfMonad`, i.e. `pure default`. -/
theorem keepsA_getConstInfoCtor (n : Name) :
    Keeps mctx mref cctx cref I (getConstInfoCtor n : MetaM ConstructorVal) := by
  unfold getConstInfoCtor isCtor?
  refine Keeps.bind (Keeps.bind (keepsA_framed O hA hS FramedA.env) fun env => ?_) fun x => ?_
  · split
    · split
      · exact Keeps.pure _
      · unfold panicWithPosWithDecl panic panicCore
        exact Keeps.pure _
    · exact Keeps.pure _
  · cases x with
    | some a => exact Keeps.pure a
    | none => exact keepsA_throwError O hA hS _ (by okmsg)

theorem keepsA_getUserName (id : FVarId) :
    Keeps mctx mref cctx cref I (id.getUserName : MetaM Name) := by
  unfold FVarId.getUserName FVarId.getDecl
  refine Keeps.bind (Keeps.bind (Keeps.of_ok fun w => ⟨_, rfl⟩) fun l => ?_) fun d => Keeps.pure _
  cases l.find? id with
  | some d => exact Keeps.pure d
  | none => exact keepsA_framed O hA hS (FramedA.fvarThrowUnknown id)

end Prims

section Main
variable (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
  (hS : StableA O.quiet I)
include O T hS

theorem projFieldNameA_core (hA : AdmCtx O.quiet mctx cctx) (n s : Name) :
    Keeps mctx mref cctx cref I (projFieldName? n s) := by
  unfold projFieldName?
  refine Keeps.bind (keepsA_framed O hA hS FramedA.env) fun env => ?_
  split
  · rename_i projInfo _
    refine Keeps.bind (Keeps.tryCatch (Keeps.map _ (keepsA_getConstInfoInduct O hA hS s))
      fun e _ => Keeps.pure _) fun r => ?_
    split
    · rename_i indVal
      refine Keeps.bind (keepsA_getConstInfoCtor O hA hS _) fun ctorInfo => ?_
      refine Keeps.bind (keeps_forallTelescopeReducing T hA hS _ _
        (fun m c xs b hA' => ?_)) fun fieldName => Keeps.pure _
      refine Keeps.dite (fun h => ?_) (fun h => Keeps.pure _)
      exact Keeps.bind (keepsA_getUserName O hA' hS _) fun _ => Keeps.pure _
    · exact Keeps.pure _
  · exact Keeps.pure _

end Main

/-- **`ProjFieldNameA`, PROVED from `RefLawsATele`** (the one telescope of `projFieldName?`;
everything else is `FramedA.env`, `Keeps.tryCatch`, `throwError` of `OkMsg` messages, a local
context read and `FramedA.fvarThrowUnknown`). Premise: `T` only. -/
theorem projFieldNameA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) : ProjFieldNameA O I :=
  fun _ _ hA n s => projFieldNameA_core O T hS hA n s




end Tools.ShippingChildProjFieldA

#print axioms Tools.ShippingChildProjFieldA.projFieldNameA
#print axioms Tools.ShippingChildTeleCP.keepsCP_forallTelescopeReducing

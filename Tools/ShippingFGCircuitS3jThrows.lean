import Tools.ShippingChildInvA
import Tools.ShippingStRefCorrespondence
set_option autoImplicit false
-- FG circuit pilot S3j, unit 3 (optional item): the field `RefLawsAOps.frameT` (`Throws p` leaves `cv`/`sv`/`dv` and `quiet`) for the ACTUAL operations of `Throws` (`throwError msg` in MetaM, and its Core lift).  Both constructors of `Throws` read the Core state (and, in MetaM, the Meta state) for the message context and then throw, so the end world is the start world under `ReadWorld mref` and `ReadWorld cref` (two fields of `CellPrem`).  This is a lemma ABOUT THE FIELD'S PROPOSITION: it does not construct an `L`, and `L` stays a binder (the other 13 fields are untouched).  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §60.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3jThrows
open Lean Meta
open Tools.ShippingChildInv (readOf endW Throws)
open Tools.ShippingStRefCorrespondence (ReadWorld getW readOf_get)
open Tools.ShippingChildBndCore (cv sv dv)
open Tools.ShippingChildInvA (AdmCtx)

section Ops
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- the run of `throwError msg` in MetaM, as the two state reads (Core state for the environment, Meta state for the metavariable context) and the throw, by the definitions alone -/
theorem throwError_run {α : Type} (msg : MessageData) (w : Void IO.RealWorld) :
    (throwError msg : MetaM α) mctx mref cctx cref w =
      (match (ST.Ref.get cref : ST IO.RealWorld Core.State) w with
        | .mk v w2 => match (ST.Ref.get mref : ST IO.RealWorld Meta.State) w2 with
          | .mk m w3 => EST.Out.error (Exception.error cctx.ref (MessageData.withContext
              { env := v.env, mctx := m.mctx, lctx := mctx.lctx, opts := cctx.options } msg)) w3) := rfl

/-- the same for the Core `throwError` lifted to MetaM: one read of the Core state, then the throw -/
theorem coreThrowError_run {α : Type} (msg : MessageData) (w : Void IO.RealWorld) :
    (liftM (throwError msg : CoreM α) : MetaM α) mctx mref cctx cref w =
      (match (ST.Ref.get cref : ST IO.RealWorld Core.State) w with
        | .mk v w2 => EST.Out.error (Exception.error cctx.ref (MessageData.withContext
            { env := v.env, mctx := {}, lctx := {}, opts := cctx.options } msg)) w2) := rfl

/-- **every `Throws` operation ends in its start world**, given `ReadWorld` of the Meta and Core state cells (`hcell.2.2.2.2.2.1` and `hcell.2.2.2.2.2.2.2.2.1` of `CellPrem`): the reads return the world unchanged and the throw does not touch it -/
theorem endW_throws (hm : ReadWorld mref) (hc : ReadWorld cref) {α : Type} {p : MetaM α} (hp : Throws p)
    (w : Void IO.RealWorld) : endW mctx mref cctx cref p w = w := by
  cases hp with
  | err msg =>
    unfold endW
    rw [throwError_run, readOf_get cref w, hc w]
    dsimp only
    rw [readOf_get mref w, hm w]
  | coreErr msg =>
    unfold endW
    rw [coreThrowError_run, readOf_get cref w, hc w]

end Ops

/-- **the field `RefLawsAOps.frameT`, for any `quiet`, from the two cell premises**: its proposition (`Throws p` leaves the three tracked values and `quiet`) holds, with the same quantifier structure as the field.  `AdmCtx` is not used. -/
theorem frameT_of_readWorld {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (hm : ReadWorld mref) (hc : ReadWorld cref) (quiet : Void IO.RealWorld → Prop) :
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx quiet mctx cctx →
      ∀ (p : MetaM α), Throws p → ∀ w, quiet w →
      (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
        dv (endW mctx mref cctx cref p w) = dv w) ∧ quiet (endW mctx mref cctx cref p w) := by
  intro mctx cctx α _ p hp w hq
  rw [endW_throws hm hc hp w]
  exact ⟨⟨rfl, rfl, rfl⟩, hq⟩

end Tools.ShippingFGCircuitS3jThrows

#print axioms Tools.ShippingFGCircuitS3jThrows.endW_throws
#print axioms Tools.ShippingFGCircuitS3jThrows.frameT_of_readWorld

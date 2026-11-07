import Tools.ShippingGen2Defs
import Tools.ShippingGen5EnvFrame3
import Tools.ShippingStRefCorrespondence
import Tools.ShippingChildInvA
set_option autoImplicit false
-- FG circuit pilot S3m (option A, non-vacuity): field-level facts about the EXISTING opaque IO definitions.  Nothing here constructs a non-vacuous `CellPrem` / `Laws` value: the first blocking field of each is identified.  Category (b) = theorems about the existing definitions; (a) = the one pure-model lemma, labelled.  No sorry/axiom/native_decide/TRUSTED/law.  docs/FG-CIRCUIT-PILOT.md §63.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3m
open Lean Meta
open Tools.ShippingStRefCorrespondence (ReadWorld SetGet SetFrame getW setW)
open Tools.ShippingGen5EnvFrame3 (CellOK CellPrem)
open Tools.ShippingChildInv (readOf endW Diag SideRef)
open Tools.ShippingChildBndCore (cv sv dv)
open Tools.ShippingChildInvA (RefLawsAOps AdmCtx admCtx_none)
open Tools.ShippingGen2 (Laws)
open Sparkle.Compiler.Elab

/-! ## 1. CellPrem field by field (category (b)) -/

/-- the ten conjuncts of `CellPrem`, the three `CellOK` unfolded: in this order the FIRST is `ReadWorld sparkleChildCache` -/
def CellPremFields (Fresh : (σ : Type) → IO.Ref σ → Prop) (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  ReadWorld sparkleChildCache ∧ sparkleChildCache.ref ≠ cref.ref ∧ SetFrame sparkleChildCache cref ∧
  ReadWorld sparkleChildSynth ∧ sparkleChildSynth.ref ≠ cref.ref ∧ SetFrame sparkleChildSynth cref ∧
  ReadWorld sparkleSynthDepth ∧ sparkleSynthDepth.ref ≠ cref.ref ∧ SetFrame sparkleSynthDepth cref ∧
  (∀ {σ : Type} (r : IO.Ref σ), SideRef r → CellOK cref r) ∧
  (∀ (σ : Type) (r : IO.Ref σ), Fresh σ r → CellOK cref r) ∧
  ReadWorld mref ∧ SetFrame mref cref ∧ mref.ref ≠ cref.ref ∧ ReadWorld cref ∧ SetGet cref

theorem cellPrem_iff_fields (Fresh : (σ : Type) → IO.Ref σ → Prop) (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) : CellPrem Fresh mref cref ↔ CellPremFields Fresh mref cref := by
  constructor
  · rintro ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩, d, e, f, g, h, i, j⟩
    exact ⟨a1, a2, a3, b1, b2, b3, c1, c2, c3, d, e, f, g, h, i, j⟩
  · rintro ⟨a1, a2, a3, b1, b2, b3, c1, c2, c3, d, e, f, g, h, i, j⟩
    exact ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩, d, e, f, g, h, i, j⟩

/-- the first field, unfolded to the primitive: for EVERY world `w` (not only reachable ones), the world after the opaque `ST.Prim.Ref.get sparkleChildCache` is `w` -/
theorem readWorld_cache_unfold :
    ReadWorld sparkleChildCache ↔
      ∀ w : Void IO.RealWorld,
        (match (ST.Ref.get sparkleChildCache : ST IO.RealWorld _) w with | .mk _ w' => w') = w := Iff.rfl

/-- the ref-distinctness fields need TWO distinct pointers.  In the API supplied to this investigation the only pointer found is `Classical.choice ST.RefPointed.property` (`ST.RefPointed` is an opaque `NonemptyType`); no `cref` with `cref.ref ≠ sparkleChildCache.ref` was constructed in the investigated range.  CONDITIONAL refutation only: if the pointer type were a subsingleton `CellPrem` would be false for every `mref cref`.  (Neither is contradictory: in the runtime the pointers differ.) -/
theorem cellPrem_false_of_subsingleton (hs : Subsingleton ST.RefPointed.type)
    (Fresh : (σ : Type) → IO.Ref σ → Prop) (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) : ¬ CellPrem Fresh mref cref :=
  fun h => h.1.2.1 (hs.elim _ _)

/-- (a) PURE MODEL, not the real IO: in an explicit-state model the shape `∀ w, get w = w` is satisfiable AND falsifiable, so the shape alone settles neither; the real `ST.Prim.Ref.get` is an opaque constant that the kernel can neither unfold nor constrain -/
theorem readWorld_shape_both :
    (∃ g : Bool → Bool, ∀ w, g w = w) ∧ (∃ g : Bool → Bool, ¬ ∀ w, g w = w) :=
  ⟨⟨id, fun _ => rfl⟩, ⟨not, fun h => absurd (h true) (by decide)⟩⟩

/-! ## 2. Laws: the first blocking field is `diag`, already at `IO.getStderr` -/

/-- the world after the (opaque, `BaseIO`) `IO.getStderr` -/
def stderrW (w : Void IO.RealWorld) : Void IO.RealWorld :=
  match (IO.getStderr : BaseIO IO.FS.Stream) w with
  | .mk _ w' => w'

/-- what `diag` demands of `quiet` at the diagnostic `ioGetStderr`: the three tracked values and quietness survive the opaque primitive -/
def StderrKeeps (quiet : Void IO.RealWorld → Prop) : Prop :=
  ∀ w, quiet w → (cv (stderrW w) = cv w ∧ sv (stderrW w) = sv w ∧ dv (stderrW w) = dv w) ∧ quiet (stderrW w)

/-- the run of the lifted `IO.getStderr` ends in `stderrW` -/
theorem endW_getStderr (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) :
    endW mctx mref cctx cref (liftM IO.getStderr : MetaM IO.FS.Stream) w = stderrW w := by
  unfold endW stderrW
  rfl

/-- **`diag` of any `Laws.O` (at the default Meta context, admissible) entails `StderrKeeps O.quiet`**.  So a `quiet` that is not `False` on a world `w` needs a fact about the opaque primitive `IO.getStderr` at `w` — nothing in the API gives it. -/
theorem stderrKeeps_of_ops {Fresh : (σ : Type) → IO.Ref σ → Prop} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (O : RefLawsAOps Fresh mref cref) (cctx : Core.Context) :
    StderrKeeps O.quiet := by
  intro w hq
  have h := O.diag (mctx := {}) (cctx := cctx) (admCtx_none rfl) _ Diag.ioGetStderr w hq
  rw [endW_getStderr] at h
  exact h

/-- the same for a `Laws` -/
theorem stderrKeeps_of_laws {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (cctx : Core.Context) : StderrKeeps L.O.quiet :=
  stderrKeeps_of_ops L.O cctx

/-- a STRONG sufficient condition (not the smallest): if the opaque primitive leaves the whole world alone, `StderrKeeps` holds for EVERY `quiet`.  Identity of the entire world is more than `StderrKeeps` needs.  Not supplied for `IO.getStderr`. -/
theorem stderrKeeps_of_id (h : ∀ w, stderrW w = w) (quiet : Void IO.RealWorld → Prop) : StderrKeeps quiet := by
  intro w hq; rw [h w]; exact ⟨⟨rfl, rfl, rfl⟩, hq⟩

/-- an IMPLICATION under the hypothesis `O.quiet w ↔ dv w = 0` (assumed, not a constructed quiet; nothing here shows such an `O` exists, and preserving `dv = 0` under `depthSetQ` updates to arbitrary depths is not established): from `diag` at `ioGetStderr`, at a world with depth 0 the cache/synth values survive `IO.getStderr` and the depth stays 0 -/
theorem diag_stderr_at_depth0 {Fresh : (σ : Type) → IO.Ref σ → Prop} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (O : RefLawsAOps Fresh mref cref) (hO : ∀ w, O.quiet w ↔ dv w = 0)
    (cctx : Core.Context) (w : Void IO.RealWorld) (h0 : dv w = 0) :
    cv (stderrW w) = cv w ∧ sv (stderrW w) = sv w ∧ dv (stderrW w) = 0 := by
  have h := stderrKeeps_of_ops O cctx w ((hO w).2 h0)
  exact ⟨h.1.1, h.1.2.1, ((hO _).1 h.2)⟩

end Tools.ShippingFGCircuitS3m

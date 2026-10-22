import Tools.ShippingInitSession
-- UNBUILT (unit RT4): not yet built. No sorry/axiom/native_decide.

/-! # Unit RT4: the allocation part of `InitHeapRelXfer`, split into named statements (ledger L9f)

`InitHeapRelXfer R Other wS h0` (L9d) says: if `InitHeapRel R (mkRefsW wS) h0` then
`InitHeapRel R (mkSynthW a4) h0`, for every interleaved prefix `a0 a2 a4`. This file splits it.

* PROVED (`initHeapRel_iff`, `xfer_iff_rxfer`): `InitHeapRel R w h0` is `R w h0` plus three equations about
  `h0` ALONE (`InitCells h0`); so the three cell-value conjuncts are carried unchanged and the transfer
  premise is, apart from `InitCells h0`, a statement about `R` and the worlds only (`RXfer`).
* PROVED (`rxfer_of_alloc`, `xfer_of_alloc`): `RXfer` (hence `InitHeapRelXfer`) follows from the L9d premise
  `OthersFrameRefs R Other` and ONE statement per `IO.mkRef` — `MkDepthRelInv`, `MkCacheRelInv`,
  `MkSynthRelInv` ("allocating that cell leaves the model relatedness unchanged, both directions").
  This is a REPLACEMENT of one premise (`InitHeapRelXfer`) by three (one per `mkRef`), NOT a discharge:
  the three are PREMISES, `InitHeapRel` (`hmk`) stays a premise, and no model of `R` is built.
* NOT given by types (checked in `Tests/Compiler/InitTraceTest.lean`): `IO.mkRef`/`ST.Prim.mkRef` is an
  `@[extern] opaque`; no field of `RefLawsAOps` and no declaration of the heap model mentions it; the only
  declarations of this development that mention it are the world transformers `mkRefsW`/`mk*W` and the
  unused `MkRefTrace`. The model heap's `alloc` allocates only `other n` cells; the three tracked cells are
  heap FIELDS (not allocated), so the model has no allocation of the tracked cells at all.
Runtime fit NOT PROVEN; logical inconsistency NOT PROVEN (of the new premises as well). -/

namespace Tools.ShippingInitAlloc
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingStartWorldA Tools.ShippingStartWorldA2 Tools.ShippingStartAtLoad
open Tools.ShippingInitFrame Tools.ShippingInitSession
open Tools.ShippingChildInvA Tools.ShippingChildDepthC

variable {Ob Pr Er : Type}

/-- The three cell-value equations of `InitHeapRel`: statements about the model heap alone. -/
def InitCells (h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er)) : Prop :=
  h0.cache = ({} : Std.HashMap Name Res) ∧ h0.synth = none ∧ h0.depth = 0

theorem initHeapRel_iff (R : Corr Ob Pr Er) (w : Void IO.RealWorld)
    (h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er)) :
    InitHeapRel R w h0 ↔ R w h0 ∧ InitCells h0 := by
  unfold InitHeapRel InitCells
  exact Iff.rfl

/-- The world-only part of the transfer. -/
def RXfer (R : Corr Ob Pr Er) (Other : Void IO.RealWorld → Void IO.RealWorld → Prop)
    (wS : Void IO.RealWorld) (h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er)) : Prop :=
  ∀ a0 a2 a4, Chain Other wS a0 → Chain Other (mkDepthW a0) a2 → Chain Other (mkCacheW a2) a4 →
    R (mkRefsW wS) h0 → R (mkSynthW a4) h0

/-- PROVED: `InitHeapRelXfer` is `RXfer` under the cell equations of `h0`. -/
theorem xfer_iff_rxfer (R : Corr Ob Pr Er) (Other : Void IO.RealWorld → Void IO.RealWorld → Prop)
    (wS : Void IO.RealWorld) (h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er)) :
    InitHeapRelXfer R Other wS h0 ↔ (InitCells h0 → RXfer R Other wS h0) := by
  constructor
  · intro hx hc a0 a2 a4 c0 c1 c2 hr
    exact ((initHeapRel_iff _ _ _).1 (hx a0 a2 a4 c0 c1 c2 ((initHeapRel_iff _ _ _).2 ⟨hr, hc⟩))).1
  · intro hx a0 a2 a4 c0 c1 c2 hr
    obtain ⟨hr, hc⟩ := (initHeapRel_iff _ _ _).1 hr
    exact (initHeapRel_iff _ _ _).2 ⟨hx hc a0 a2 a4 c0 c1 c2 hr, hc⟩

/-- **PREMISE (allocation of the depth ref; heap-model extension).** The first `IO.mkRef` of `Elab.lean`
(`sparkleSynthDepth`) leaves the relatedness of every world to every model heap unchanged. -/
def MkDepthRelInv (R : Corr Ob Pr Er) : Prop := ∀ w h, R (mkDepthW w) h ↔ R w h
/-- **PREMISE (allocation of the cache ref).** -/
def MkCacheRelInv (R : Corr Ob Pr Er) : Prop := ∀ w h, R (mkCacheW w) h ↔ R w h
/-- **PREMISE (allocation of the synth ref).** -/
def MkSynthRelInv (R : Corr Ob Pr Er) : Prop := ∀ w h, R (mkSynthW w) h ↔ R w h

/-- PROVED from `OthersFrameRefs` and the three allocation statements. -/
theorem rxfer_of_alloc (R : Corr Ob Pr Er) (Other : Void IO.RealWorld → Void IO.RealWorld → Prop)
    (wS : Void IO.RealWorld) (h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er))
    (hf : OthersFrameRefs R Other) (hd : MkDepthRelInv R) (hc : MkCacheRelInv R)
    (hs : MkSynthRelInv R) : RXfer R Other wS h0 := by
  intro a0 a2 a4 c0 c1 c2 hr
  have e0 : R wS h0 := (hd wS h0).1 ((hc _ h0).1 ((hs _ h0).1 hr))
  have e1 := (hd a0 h0).2 (frame_chain hf c0 e0)
  have e2 := (hc a2 h0).2 (frame_chain hf c1 e1)
  exact (hs a4 h0).2 (frame_chain hf c2 e2)

/-- PROVED: the L9d transfer premise from the frame premise and the three allocation statements. A
replacement of one premise by three, not a discharge. -/
theorem xfer_of_alloc (R : Corr Ob Pr Er) (Other : Void IO.RealWorld → Void IO.RealWorld → Prop)
    (wS : Void IO.RealWorld) (h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er))
    (hf : OthersFrameRefs R Other) (hd : MkDepthRelInv R) (hc : MkCacheRelInv R)
    (hs : MkSynthRelInv R) : InitHeapRelXfer R Other wS h0 :=
  (xfer_iff_rxfer R Other wS h0).2 fun _ => rxfer_of_alloc R Other wS h0 hf hd hc hs

/-- The session theorem `startContents_session_init` with `hxfer` REPLACED by the three allocation
statements. Same other premises, in the same order; `hxfer` is built, not assumed. -/
theorem startContents_session_init_alloc {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hB : BodyStepC O) (Other : Void IO.RealWorld → Void IO.RealWorld → Prop)
    (hO : OtherCodeKeeps O.quiet Other)
    (R : Corr Ob Pr Er) (Q : Pr → Prop) {wS : Void IO.RealWorld}
    {h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er)}
    (Other₀ : Void IO.RealWorld → Void IO.RealWorld → Prop)
    {w0 : Void IO.RealWorld} (hI : InitOrder Other₀ wS w0)
    (hd : MkDepthRelInv R) (hc : MkCacheRelInv R) (hms : MkSynthRelInv R)
    (hf : OthersFrameRefs R Other₀)
    (hmk : InitHeapRel R (mkRefsW wS) h0) (hget : GetSpec R) (hset : SetSynthSpec R)
    (hq : QuietSpec R Q O.quiet) (hQ0 : Q h0.reg) {w : Void IO.RealWorld}
    (hs : Chain (fun a b => EntryStep mctx mref cctx cref a b ∨ Other a b) w0 w) :
    O.quiet w ∧ StartContents w :=
  startContents_session_init O hA hB Other hO R Q Other₀ hI (xfer_of_alloc R Other₀ wS h0 hf hd hc hms)
    hf hmk hget hset hq hQ0 hs

end Tools.ShippingInitAlloc

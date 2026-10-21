import Tools.ShippingInitFrame
-- UNBUILT (unit RT3): run names in REPORT-RT3.md. No sorry/axiom/native_decide.

/-! # Unit RT3: the session theorem at the end world of the interleaved load (ledger L9e)

`startContents_session_init` unpacks `InitOrder Other₀ wS w0` and hands the SAME end world `w0` of the
interleaved load to L9b's `startContents_session` as the start world of the session chain. Every
condition of `startContents_session_rt` (`hA`, `hB`, `hO`, `hget`, `hset`, `hq`, `hQ0`) is kept as an
explicit premise; `hmk` is kept; `InitOrder`, `OthersFrameRefs`, `InitHeapRelXfer` and the three chain
hypotheses of RT2 are explicit premises too (the chain premises are exactly the unpacked `InitOrder`).
PROVED: only the composition. NOT claimed: that any premise holds for the real load; runtime fit NOT
PROVEN; logical inconsistency NOT PROVEN. `Other₀` (load-time steps) and `Other` (between-command steps)
are separate relations. -/

namespace Tools.ShippingInitSession
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingStartWorldA Tools.ShippingStartWorldA2 Tools.ShippingStartAtLoad
open Tools.ShippingInitFrame
open Tools.ShippingChildInvA Tools.ShippingChildDepthC

variable {Ob Pr Er : Type}

theorem startContents_session_init {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hB : BodyStepC O) (Other : Void IO.RealWorld → Void IO.RealWorld → Prop)
    (hO : OtherCodeKeeps O.quiet Other)
    (R : Corr Ob Pr Er) (Q : Pr → Prop) {wS : Void IO.RealWorld}
    {h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er)}
    (Other₀ : Void IO.RealWorld → Void IO.RealWorld → Prop)
    {w0 : Void IO.RealWorld} (hI : InitOrder Other₀ wS w0)
    (hxfer : InitHeapRelXfer R Other₀ wS h0) (hf : OthersFrameRefs R Other₀)
    (hmk : InitHeapRel R (mkRefsW wS) h0) (hget : GetSpec R) (hset : SetSynthSpec R)
    (hq : QuietSpec R Q O.quiet) (hQ0 : Q h0.reg) {w : Void IO.RealWorld}
    (hs : Chain (fun a b => EntryStep mctx mref cctx cref a b ∨ Other a b) w0 w) :
    O.quiet w ∧ StartContents w := by
  obtain ⟨a0, a2, a4, a6, c0, c1, c2, c3, c4⟩ := hI
  exact startContents_session O hA hB Other hO
    (startAtLoad_of_initOrder R Q O.quiet Other₀ c0 c1 c2 c3 c4 hxfer hf hmk hget hset hq hQ0) hs

end Tools.ShippingInitSession

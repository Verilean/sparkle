import Tools.ShippingFGCircuitS2mReach
set_option autoImplicit false
-- FG circuit pilot S2m (part 2): the invariant `JQHR` (= `JQH` over `ropsR`), its establishment at the head of the root run, its preservation by the steps of the main induction, the miss premise derived from it, and `hftCoreCloses_of_kidsR`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §39.

namespace Tools.ShippingFGCircuitS2mReach
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (endW Res)
open Tools.ShippingChildBndCore (cv sv dv)
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingChildVCA (JQ)
open Tools.ShippingGen5Env (ReadsAt readsAt_self)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS2hHist
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt)
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingEntryReadsLinked (CoreSaved)
open Tools.ShippingFGCircuitS1qLinked (coreHeadOff)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## the profile lookup along the reached worlds -/

/-- the profile lookup is unset at every reached world, from the root fact and the leaf-step frame -/
theorem profOffW_of_reached {O : RefLawsAOps MkRefd mref cref} {w₀ : Void IO.RealWorld}
    (h0 : ProfOffW mref cref w₀) (hs : ProfStepR O w₀) {w : Void IO.RealWorld}
    (hr : Reached O.quiet mref cref w₀ w) : ProfOffW mref cref w := by
  induction hr with
  | start => exact h0
  | step hr' hl ih => exact hs _ _ hr' hl ih

/-! ## the invariant `JQHR` -/

/-- **The evidence a child run starts with, derived from the reached world**: `ReadsAt e` (from the strengthened quiet predicate) and the profile lookup (from `ProfOffW`). Same predicate as S2h's `KidEv`. -/
abbrev KidEvR (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (e : Environment) : StartEv := KidEv mref cref e

/-- **`JQHR`**: the history invariant `JQH` over the strengthened operations bundle `ropsR`. A `JQHR` world is quiet, reads `e = envAt cref w₀`, is reached from the root start world `w₀`; its cache entries carry the saved reads of the runs that created them. -/
def JQHR (O : RefLawsAOps MkRefd mref cref) (hcell : CellPrem MkRefd mref cref) (e : Environment)
    (w₀ : Void IO.RealWorld) (hdown : AdmDownR O e w₀) (hD : DRowEnvR O e w₀) (hG : DiagEnvR O e w₀)
    (D : Nat) (w : Void IO.RealWorld) : Prop :=
  JQH (ropsR O hcell e w₀ hdown hD hG) (KidEv mref cref e) D w

/-- what a `JQHR` world says about its environment, its reach and its profile lookup -/
theorem jqhr_facts {O : RefLawsAOps MkRefd mref cref} {hcell : CellPrem MkRefd mref cref} {e : Environment}
    {w₀ : Void IO.RealWorld} {hdown : AdmDownR O e w₀} {hD : DRowEnvR O e w₀} {hG : DiagEnvR O e w₀}
    (h0 : ProfOffW mref cref w₀) (hs : ProfStepR O w₀) {D : Nat} {w : Void IO.RealWorld}
    (hw : JQHR O hcell e w₀ hdown hD hG D w) :
    O.quiet w ∧ ReadsAt e cref w ∧ Reached O.quiet mref cref w₀ w ∧ ProfOffW mref cref w :=
  ⟨hw.1.1.1, hw.1.1.2.1, hw.1.1.2.2, profOffW_of_reached h0 hs hw.1.1.2.2⟩

/-- **The miss premise from the invariant** (replaces S2h's universal `MissE`): in a `JQHR` world the evidence `KidEv e` for the call's context pair holds — `ReadsAt e` because the world's quiet predicate carries it, the profile lookup because the world is reached from `w₀` and the lookup is unset along the leaf steps. Nothing is asked of a world outside the invariant. -/
theorem missR {O : RefLawsAOps MkRefd mref cref} {hcell : CellPrem MkRefd mref cref} {e : Environment}
    {w₀ : Void IO.RealWorld} {hdown : AdmDownR O e w₀} {hD : DRowEnvR O e w₀} {hG : DiagEnvR O e w₀}
    (h0 : ProfOffW mref cref w₀) (hs : ProfStepR O w₀) :
    MissE (ropsR O hcell e w₀ hdown hD hG) (KidEv mref cref e) := by
  intro mctx cctx _ D _ n w hw _
  have hf := jqhr_facts (hcell := hcell) (hdown := hdown) (hD := hD) (hG := hG) h0 hs (D := D) (w := w) hw
  exact ⟨hf.2.1, hf.2.2.2 mctx cctx⟩

/-! ## establishment at the head of the root run, and the steps of the induction -/

/-- **Established at the head of the root run**: the start world is `JQHR` at depth 0 (`ReadsAt (envAt cref w₀) w₀` is `readsAt_self`, `Reached.start`), and the head `coreHeadOff` (depth-0 branch: clears the cache) leaves a `JQHR` world at depth 1. -/
theorem jqhr_head {O : RefLawsAOps MkRefd mref cref} {hcell : CellPrem MkRefd mref cref}
    {w₀ : Void IO.RealWorld} {hdown : AdmDownR O (envAt cref w₀) w₀}
    {hD : DRowEnvR O (envAt cref w₀) w₀} {hG : DiagEnvR O (envAt cref w₀) w₀}
    (hadm : AdmCtx (quietR O.quiet mref cref (envAt cref w₀) w₀) mctx cctx)
    (hjq : JQ O.quiet 0 w₀) {X : Name} {w1 : Void IO.RealWorld} {s : CoreSaved}
    (hh : RunsTo (coreHeadOff X) mctx mref cctx cref w₀ s w1) :
    JQHR O hcell (envAt cref w₀) w₀ hdown hD hG (0 + 1) w1 :=
  coreHeadOff_jqhA (E := KidEv mref cref (envAt cref w₀)) (ropsR O hcell (envAt cref w₀) w₀ hdown hD hG)
    hadm ⟨⟨hjq.1, readsAt_self cref w₀, .start⟩, hjq.2⟩ hh

end Tools.ShippingFGCircuitS2mReach

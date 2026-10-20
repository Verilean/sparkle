import Tools.ShippingFirstGateChild
import Tools.ShippingCombKidText

variable {tenv : Lean.Environment}

/-! # The children's check of a FIRST-gate child (worker N, round 13)

WRITTEN, NOT BUILT.

`Tools.ShippingCombKidText.gate_real_kidK` gives `kidCheck C n y.1` for a
real child of the SECOND (mixed) gate — its premises assume the first gate
refuses the declaration. `childAdd` is a FIRST-gate child. Here the same
fact for a first-gate child (`quoteDecl dn names n fe`, `fe.WF`, `0 < n`),
the core run replaced by the bridge exactly as in `first_child_fullFacts`:

* `first_child_forwardCheck`: the full entry's module passes the gate
  route's forward check (`post_forwardCheck` on `transition_closed`'s
  print base and typed-post readiness; the checked merge of an
  assignment-only body is `mergeDuplicates`);
* `first_child_kidK`: `∀ C n, kidCheck C n y.1 = true` for a real
  first-gate child (`forwardCheck_text`, `kidCheck_leaf_of_text`). -/
namespace Tools.ShippingFirstGateChild
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.Builder
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineCompose
open Tools.ShippingMachineChild
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingEntrySoundness (RunsTo EnvDefines synthesizeCombinationalCore_reads MReturns
  FExpr evalFE quoteF quoteBody quoteDecl quoteBinders PostReady denoteFE denoteFE_val
  outcome_quote synthesizeFromConst_sound certifiedShape_quote quoteF_congr finishSynth_returns
  CertifiedOutcome)
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingUnifiedMeaning (pack)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingTransitionClosed Tools.ShippingMergeClosed
open Tools.ShippingGateChildComb
open Tools.ShippingSettledSoundness (Acyclic)
open Sparkle.IR.NameHints (Allocated)
open Sparkle.IR.Reorder

set_option linter.unusedSectionVars false

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000 in
/-- **A first-gate child's full-entry module passes the forward check**
(`gate_child_forwardCheck` for the first gate: the prelude of
`first_child_fullFacts`). -/
theorem first_child_forwardCheck {declName : Name} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    Tools.ShippingSVBridge.forwardCheck b = true := by
  obtain ⟨M, D, w1, hcore, hpost, hdes⟩ := synthesizeCombinational_parts hr
  obtain ⟨envR, logProf, ids, cache, returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    first_core_run hcore entry hwf
  have he := wf_ofF 0 names.length n hn fe hwf
  obtain ⟨hclosed, -, ⟨ow, pb⟩, ready, hdesign, hname⟩ :=
    transition_closed (dom := .bvar names.length) (bpos := fun _ => 0) (vpos := fun j => j + 1)
      nd len hrun hm nameLegal (firstBs_positive hn) (ofF n fe) he
      (fun j hj => absurd hj (Nat.not_lt_zero j)) (fun j hj => ⟨names[j], firstBs_bits hj⟩)
      (first_body (dn := dn) hwf)
  obtain ⟨dzb, _, _, _, _⟩ := Tools.ShippingTypedPostSoundness.dropZeroWidth_typed ready
  have hZa : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body.all
      Sparkle.IR.RegDedup.isAssign = true := by
    rw [dzb]
    exact acyclic_isAssign pb.order
  refine Tools.ShippingMixedForwardSoundness.post_forwardCheck pb ready ?_
  rcases hpost with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (Tools.ShippingCombKidText.mergeChecked_assign hZa))

/-- **The children's check of a real FIRST-gate child**, at every depth and
for every child map (`gate_real_kidK` for the first gate). -/
theorem first_child_kidK {c : Name} {y : Tools.ShippingChildInv.Res} {dn : Name}
    {names : List Name} {n : Nat} {fe : FExpr}
    (entry : EntryDefines mctx mref cctx cref c (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (h : Tools.ShippingChildInv.RealChild mref cref c y) :
    ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (k : Nat),
      Tools.ShippingChecksDesign.kidCheck C k y.1 = true := by
  obtain ⟨b, design⟩ := y
  obtain ⟨mctx', cctx', w, w', -, hr⟩ := h.inv
  have entry' : EntryDefines mctx' mref cctx' cref c (quoteDecl dn names n fe) :=
    Tools.ShippingReflectCtx.EntryDefines.ctx entry
  have hfc := first_child_forwardCheck hr entry' hwf hn
  obtain ⟨hall, h2, h3⟩ := Tools.ShippingCombKidText.forwardCheck_text hfc
  have hs : b.body.all Sparkle.IR.OptCheck.seqStmtOk = true :=
    Tools.ShippingMachineShipsComb.assigns_seqOk hall
  exact fun C k => Tools.ShippingLeafTyped.kidCheck_leaf_of_text C k hs h2 h3

end Tools.ShippingFirstGateChild

#print axioms Tools.ShippingFirstGateChild.first_child_forwardCheck
#print axioms Tools.ShippingFirstGateChild.first_child_kidK

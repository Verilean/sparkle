import Tools.ShippingLeafTyped
import Tools.ShippingMixedForwardSoundness
import Tools.ShippingCallsGate
import Tools.ShippingMachineShipsComb
import Tools.ShippingPortWidthsPure

/-! # The children's check of a COMBINATIONAL child: gate children and one-output slotless leaves (G1, round par/a-5)

`kidsPass C (kidCheck C n) o.body` asks `kidCheck C n child` of each
instance's child (`leafCheck` at depth 0, `designCheck C k` deeper).
`Tools.ShippingLeafTyped.leaf_real_kidK_reg` gives it for a leaf machine
WITH a register; `leaf_real_kidK` keeps `hmergePrint` for a slotless leaf,
because `mergeChecked`'s assignment-only branch returns
`mergeDuplicates m` with no print guard. This file removes that hypothesis
in two cases, with NO change to the compiler.

## A. A gate child (`pick`, `pickD`, `rcH`)

The gate route already has the text fact, in another vocabulary:
`Tools.ShippingMixedForwardSoundness.post_forwardCheck` — for the gate
entry's raw module `M` (`PrintBaseAt`, `TypedPostReady`, both from
`transition_closed`) and `m' = dropZeroWidthModule M` or its
`mergeDuplicates`, `forwardCheck m' = true`. And `mergeChecked` of an
assignment-only body IS `mergeDuplicates`.

* `moduleWof_eq`: the emitter's width map `moduleWof m` is
  `printWidths (m.wires ++ m.inputs ++ m.outputs)` (two definitions with
  the same body).
* `seqCheck_of_assignsCheck`: on an assignment-only body `assignsCheck`
  is `seqCheck`.
* `forwardCheck_text`: `forwardCheck m = true` gives the body assignments
  only and conjuncts 2, 3 of `textCheckI` (`seqCheck (wofOf m) (weS m)`,
  the width tables agree on `seqNames`).
* `gate_child_forwardCheck`: `forwardCheck b = true` for the FULL entry's
  module of a gate declaration, over every run (the prelude of
  `gate_child_comb`, copied).
* `gate_real_kidK`: `∀ C n, kidCheck C n y.1 = true` (and of the child's own
  design: empty) for a real gate child — no hypothesis but the child's
  reflection. This is `hkidK` of `core_kidsPass_any` for a gate child.
* `gate_real_notSeq`: `isSeqChild y.1 = false` (its inputs are allocated
  names): the clock clause `hkidClk` of the port matching is vacuous.

## B. A leaf machine whose ONE output is `out` (`pickByteH`, `httpGetByte`)

`validateMerge` accepts an alias `l := y` only at EQUAL wire-table widths
(`wOf l = wOf y`). The wire table gives an output port width 0, so the
output `out` is never turned into an alias of a wire (positive width), and
there is no second output. That is the argument of
`Tools.ShippingTypedPostSoundness.validateStep_typed` (written for the gate
route with the literal name `out`); here it is applied to a MACHINE leaf:

* `typedIn_mergeDuplicates_out`: `TypedIn m`, `m.outputs = [out]`, an
  assignment-only body ⟹ `TypedIn (mergeDuplicates m)`.
* `mergeChecked_text_out`: conjuncts 2, 3 of `textCheckI` of
  `mergeChecked m` for `TypedIn m` with the one output `out` — whatever the
  body (`mergeChecked_print_cases`: the module itself, a module passing the
  print guard, or an assignment-only body).
* `leaf_real_kidK_out`: `leaf_real_kidK` WITHOUT `hmergePrint`, for a leaf
  machine (with or without a register) whose layout has the one output
  `out` (`hone`, decidable).

## What is NOT here

A slotless leaf with SEVERAL outputs (a structure result). The general
statement `TypedIn m → body assignments only → TypedIn (mergeDuplicates m)`
is FALSE as a statement about `validateMerge`: an output `o₂` may become
`o₂ := o₁` for another output `o₁` (both have wire-table width 0, the
checker's width test `0 = 0` passes), and the merged module then READS an
output port — `TypedExpr (weOf m) (.ref o₁) n` fails (`weOf m o₁ = 0`) and
so does conjunct 3 (`declWidth m o₁ = 0 ≠ weS m o₁`). For the modules
`closeMachine` builds this cannot happen — each output is driven by its own
slice `w[lo + width - 1 : lo]` of the packed wire, the `lo`s are distinct,
and renaming keeps slice bounds — but that is a fact about `outAssigns`
and `machOutFields`, not about `TypedIn`. The exact missing lemma is in
`docs/parallel/A-comb-kids.md`, section 2.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingCombKidText
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Semantics
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface
open Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingTypedExprSoundness (TypedExpr)
open Tools.ShippingTypedPostSoundness (TypedStmts OutputTypedAt)
open Tools.ShippingTextTyped (TypedIn)
open Sparkle.IR.RefineCheck (mergeChecked)
open Sparkle.IR.OptCheck (seqStmtOk)
open Tools.ShippingChecksDerived (ff_absurd)

/-! ## Pure: the two vocabularies of the text check -/

/-- The emitter's width map of a module is `printWidths` of its
declarations (wires, inputs, outputs). -/
theorem moduleWof_eq (m : Sparkle.IR.AST.Module) :
    Tools.SVParser.RoundtripProof.moduleWof m =
      Tools.ShippingPrintSoundness.printWidths (m.wires ++ m.inputs ++ m.outputs) := by
  first
    | rfl
    | (funext n
       unfold Tools.SVParser.RoundtripProof.moduleWof Tools.ShippingPrintSoundness.printWidths
       cases (m.wires ++ m.inputs ++ m.outputs).find?
           (fun p => Sparkle.Backend.Verilog.sanitizeName p.name == n) with
       | none => rfl
       | some p =>
         cases p with
         | mk nm ty => cases ty <;> rfl)

/-- `seqCheck` at equal tables. -/
theorem seqCheck_congr {wof wof' : String → Option Nat} {we we' : WEnv} {body : List Stmt}
    (e1 : wof = wof') (e2 : we = we')
    (h : Tools.SVParser.EmitSem.seqCheck wof' we' body = true) :
    Tools.SVParser.EmitSem.seqCheck wof we body = true := by
  subst e1
  subst e2
  exact h

/-- On an assignment-only body the combinational check is the sequential
one. -/
theorem seqCheck_of_assignsCheck {wof : String → Option Nat} {we : WEnv} :
    ∀ (body : List Stmt), body.all Sparkle.IR.RegDedup.isAssign = true →
      Tools.SVParser.EmitSem.assignsCheck wof we body = true →
      Tools.SVParser.EmitSem.seqCheck wof we body = true
  | [], _, _ => rfl
  | st :: rest, ha, hc => by
    have ha' := ha
    rw [List.all_cons, Bool.and_eq_true] at ha'
    cases st with
    | assign l r =>
      simp only [Tools.SVParser.EmitSem.assignsCheck, Bool.and_eq_true] at hc
      simp only [Tools.SVParser.EmitSem.seqCheck, Bool.and_eq_true]
      exact ⟨hc.1, seqCheck_of_assignsCheck rest ha'.2 hc.2⟩
    | _ => exact ff_absurd ha'.1

/-- On an assignment-only body, a predicate true of every name an
assignment reads is true on `seqNames`. -/
theorem seqNames_all_assigns (f : String → Bool) :
    ∀ (body : List Stmt), body.all Sparkle.IR.RegDedup.isAssign = true →
      (∀ l r, Stmt.assign l r ∈ body → (Sparkle.IR.Reorder.refsOf r).all f = true) →
      (Tools.ShippingSeqSVSoundness.seqNames body).all f = true
  | [], _, _ => rfl
  | st :: rest, ha, h => by
    have ha' := ha
    rw [List.all_cons, Bool.and_eq_true] at ha'
    have ih := seqNames_all_assigns f rest ha'.2 (fun l r hm => h l r (List.Mem.tail _ hm))
    cases st with
    | assign l r =>
      have h0 := h l r (List.Mem.head _)
      show (Sparkle.IR.Reorder.refsOf r ++ Tools.ShippingSeqSVSoundness.seqNames rest).all f = true
      rw [List.all_append, Bool.and_eq_true]
      exact ⟨h0, ih⟩
    | _ => exact ff_absurd ha'.1

/-- **`forwardCheck` gives the module's text check**: the body is
assignments only, and conjuncts 2 and 3 of `textCheckI` hold. -/
theorem forwardCheck_text {m : Sparkle.IR.AST.Module}
    (h : Tools.ShippingSVBridge.forwardCheck m = true) :
    m.body.all Sparkle.IR.RegDedup.isAssign = true ∧
    Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf m)
        (Tools.ShippingDesignSV.weS m) m.body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames m.body).all
        (fun x => Sparkle.IR.RegDedup.declWidth m x == Tools.ShippingDesignSV.weS m x) =
          true := by
  have hw : Tools.ShippingDesignSV.wofOf m =
      Tools.ShippingPrintSoundness.printWidths (m.wires ++ m.inputs ++ m.outputs) :=
    moduleWof_eq m
  have hwe : Tools.ShippingDesignSV.weS m = Tools.ShippingSVBridge.forwardWidths m := by
    funext x
    exact congrArg (fun f : String → Option Nat => (f x).getD 0) (moduleWof_eq m)
  unfold Tools.ShippingSVBridge.forwardCheck at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hall : m.body.all Sparkle.IR.RegDedup.isAssign = true := by
    refine List.all_eq_true.mpr fun st hst => ?_
    have hk := List.all_eq_true.mp h1 st hst
    cases st with
    | assign l r => rfl
    | _ => exact ff_absurd hk
  have hrefs : ∀ l r, Stmt.assign l r ∈ m.body →
      (Sparkle.IR.Reorder.refsOf r).all (fun x => Sparkle.IR.RegDedup.declWidth m x ==
        Tools.ShippingSVBridge.forwardWidths m x) = true :=
    fun l r hm => List.all_eq_true.mp h1 _ hm
  refine ⟨hall, seqCheck_congr hw hwe (seqCheck_of_assignsCheck m.body hall h2), ?_⟩
  have hn := seqNames_all_assigns
    (fun x => Sparkle.IR.RegDedup.declWidth m x == Tools.ShippingSVBridge.forwardWidths m x)
    m.body hall hrefs
  rw [hwe]
  exact hn

/-- The checked merge of an assignment-only body is `mergeDuplicates`' own
(validated) merge. -/
theorem mergeChecked_assign {m : Sparkle.IR.AST.Module}
    (hall : m.body.all Sparkle.IR.RegDedup.isAssign = true) :
    mergeChecked m = Sparkle.IR.RegDedup.mergeDuplicates m := by
  unfold Sparkle.IR.RefineCheck.mergeChecked
  simp only [hall, if_true]

/-! ## A. Gate children -/

set_option maxHeartbeats 1000000 in
/-- **A gate child's full-entry module passes the forward check**, over
every run of the full entry, from the declaration's reflection. -/
theorem gate_child_forwardCheck {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    Tools.ShippingSVBridge.forwardCheck b = true := by
  obtain ⟨M, D, w1, hcore, hpost⟩ := Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨logProf, envR, ci, w1', w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hcore
  obtain ⟨d, hd, definition⟩ := entry w1' ci w2 w5 envR w6 get henv
  rw [hd] at run
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have shape := term_gate (d := d) (by rw [definition]; exact peel) he hb hv
  have core := Tools.ShippingGateChild.synthesizeFromConst_mixed_run oldGate (shape _) run.mreturns
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, _, nameLegal⟩ :=
    synthesizeMixedCertified_returns core
  have positive := Tools.ShippingMixedPrintSoundness.mixedShape_positive (shape (fun _ => false))
  obtain ⟨hclosed, hassign, ⟨ow, pb⟩, ready, -, -⟩ :=
    transition_closed nd len hrun hm nameLegal positive e he hb hv rfl
  obtain ⟨dzb, _, _, _, _⟩ := Tools.ShippingTypedPostSoundness.dropZeroWidth_typed ready
  have hZa : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body.all
      Sparkle.IR.RegDedup.isAssign = true := by
    rw [dzb]
    exact acyclic_isAssign pb.order
  refine Tools.ShippingMixedForwardSoundness.post_forwardCheck pb ready ?_
  rcases hpost with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (mergeChecked_assign hZa))

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The children's check of a real GATE child**, at every depth and for
every child map — and of its own design's modules (there are none). No
hypothesis about the merge or the text: the gate route's forward check
gives both. -/
theorem gate_real_kidK {c : Name} {y : Res}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (h : RealChild mref cref c y) :
    (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
        Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n g = true := by
  obtain ⟨mctx', cctx', w, w', -, hr⟩ := h.inv
  have hfc := gate_child_forwardCheck hr (Tools.ShippingReflectCtx.EntryDefines.ctx entry) old
    peel he hb hv
  have hfull := gate_child_fullFacts hr (Tools.ShippingReflectCtx.EntryDefines.ctx entry) old
    peel he hb hv
  obtain ⟨hall, h2, h3⟩ := forwardCheck_text hfc
  have hs : y.1.body.all seqStmtOk = true := Tools.ShippingMachineShipsComb.assigns_seqOk hall
  refine ⟨fun C n => Tools.ShippingLeafTyped.kidCheck_leaf_of_text C n hs h2 h3, ?_⟩
  intro g hg
  rw [hfull.design] at hg
  cases hg

/-- **A real gate child has no clock or reset input** (its inputs are
allocated names): `hkidClk` of the port matching is vacuous for it. -/
theorem gate_real_notSeq {c : Name} {y : Res}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (h : RealChild mref cref c y) : isSeqChild y.1 = false :=
  Tools.ShippingPortWidthsPure.seq_of_alloc_inputs
    (Tools.ShippingCallsGate.childFull_of_real entry old peel he hb hv h).comb.inputAlloc

/-! ## B. A leaf machine with the one output `out` -/

/-- A list of ports whose names are `["out"]` is the one port `out`. -/
theorem single_out {outs : List Port} (h : outs.map (·.name) = ["out"]) :
    ∃ ty, outs = [({ name := "out", ty := ty } : Port)] := by
  cases outs with
  | nil => simp at h
  | cons q rest =>
    cases rest with
    | nil =>
      cases q with
      | mk nm t =>
        have hq : nm = "out" := by simpa using h
        subst hq
        exact ⟨t, rfl⟩
    | cons q2 rest2 => simp at h

/-- **The validated merge of an assignment-only module with the one output
`out` keeps it typed**: the output is not turned into an alias (the
checker's equal-width test separates the port, of wire-table width 0, from
every wire an expression reads). -/
theorem typedIn_mergeDuplicates_out {m : Sparkle.IR.AST.Module} (h : TypedIn m)
    {ty : Sparkle.IR.Type.HWType} (hout : m.outputs = [({ name := "out", ty := ty } : Port)])
    (hall : m.body.all Sparkle.IR.RegDedup.isAssign = true) :
    TypedIn (Sparkle.IR.RegDedup.mergeDuplicates m) := by
  have hq : ({ name := "out", ty := ty } : Port) ∈ m.outputs := by
    rw [hout]
    exact List.Mem.head _
  -- the port `out` is no wire: its wire-table width is 0
  have hz : weOf m "out" = 0 := by
    cases hw : weOf m "out" with
    | zero => rfl
    | succ k =>
      have hpos : 0 < weOf m "out" := by
        rw [hw]
        exact Nat.succ_pos k
      obtain ⟨p, hp, hpn⟩ := List.mem_map.mp (Tools.ShippingTextTyped.pos_wire h.wn hpos).1
      exact absurd hpn (h.ow _ hq p hp)
  have hs : TypedStmts (weOf m) m.body := by
    intro st hst
    have hk := List.all_eq_true.mp hall st hst
    cases st with
    | assign l r =>
      obtain ⟨n, ht, hl⟩ := h.asg l r hst
      refine ⟨l, r, n, rfl, ht, ?_⟩
      rcases hl with hl | ⟨q, hq', hqn, -⟩
      · exact Or.inl hl
      · rw [hout] at hq'
        have e : q = ({ name := "out", ty := ty } : Port) := List.mem_singleton.mp hq'
        rw [e] at hqn
        exact Or.inr hqn.symm
    | _ => exact ff_absurd hk
  have ho : OutputTypedAt ty.bitWidth (weOf m) m.body := by
    intro e hm
    obtain ⟨n, ht, hl⟩ := h.asg "out" e hm
    rcases hl with hl | ⟨q, hq', -, hqw⟩
    · have hn : n = 0 := hl.symm.trans hz
      have hp := ht.positive
      rw [hn] at hp
      exact absurd hp (Nat.lt_irrefl 0)
    · rw [hout] at hq'
      have e' : q = ({ name := "out", ty := ty } : Port) := List.mem_singleton.mp hq'
      rw [e'] at hqw
      have hn : n = ty.bitWidth := hqw.symm
      rw [hn] at ht
      exact ht
  have hty : TypedStmts (weOf (Sparkle.IR.RegDedup.mergeDuplicates m))
      (Sparkle.IR.RegDedup.mergeDuplicates m).body :=
    Tools.ShippingTypedPostSoundness.mergeDuplicates_typed hz hs
  have ho' : OutputTypedAt ty.bitWidth (weOf (Sparkle.IR.RegDedup.mergeDuplicates m))
      (Sparkle.IR.RegDedup.mergeDuplicates m).body :=
    Tools.ShippingTypedPostSoundness.mergeDuplicates_output hz hs ho
  obtain ⟨hi, hoo, hw⟩ := Sparkle.IR.RegDedup.mergeDuplicates_ports m
  refine
    { wn := ?_, ow := ?_, oi := ?_, ostable := ?_, ond := ?_, oty := ?_, kinds := ?_,
      asg := ?_, reg := ?_ }
  · intro p hp
    rw [hw] at hp
    exact h.wn p hp
  · intro q hq1 p hp
    rw [hoo] at hq1
    rw [hw] at hp
    exact h.ow q hq1 p hp
  · intro q hq1 p hp
    rw [hoo] at hq1
    rw [hi] at hp
    exact h.oi q hq1 p hp
  · intro q hq1
    rw [hoo] at hq1
    exact h.ostable q hq1
  · rw [hoo]
    exact h.ond
  · intro q hq1
    rw [hoo] at hq1
    exact h.oty q hq1
  · intro st hst
    obtain ⟨l, e, n, rfl, -, -⟩ := hty st hst
    rfl
  · intro l r hm
    obtain ⟨l', e, n, he, ht, hl⟩ := hty _ hm
    obtain ⟨hl1, hr1⟩ := Stmt.assign.inj he
    subst hl1
    subst hr1
    refine ⟨n, ht, ?_⟩
    rcases hl with hl | hl
    · exact Or.inl hl
    · subst hl
      refine Or.inr ⟨({ name := "out", ty := ty } : Port), ?_, rfl, ?_⟩
      · rw [hoo, hout]
        exact List.Mem.head _
      · exact (ho' _ hm).width.symm.trans ht.width
  · intro o c rk i iv hm
    obtain ⟨l, e, n, he, -, -⟩ := hty _ hm
    cases he

/-- **Conjuncts 2 and 3 of `textCheckI` of the checked merge** of a typed
module with the one output `out`, whatever its body. -/
theorem mergeChecked_text_out {m : Sparkle.IR.AST.Module} (h : TypedIn m)
    {ty : Sparkle.IR.Type.HWType} (hout : m.outputs = [({ name := "out", ty := ty } : Port)]) :
    Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf (mergeChecked m))
        (Tools.ShippingDesignSV.weS (mergeChecked m)) (mergeChecked m).body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames (mergeChecked m).body).all
        (fun x => Sparkle.IR.RegDedup.declWidth (mergeChecked m) x ==
          Tools.ShippingDesignSV.weS (mergeChecked m) x) = true := by
  rcases Sparkle.IR.RefineCheck.mergeChecked_print_cases m with e | hp | hall
  · rw [e]
    exact h.seqCheck
  · exact Tools.ShippingPrintGuard.printOk_sound hp
  · rw [mergeChecked_assign hall]
    exact (typedIn_mergeDuplicates_out h hout hall).seqCheck

/-- **The children's check of a real leaf machine child with the one output
`out`** (with or without a register), at every depth and for every child
map — `leaf_real_kidK` without `hmergePrint`. -/
theorem leaf_real_kidK_out {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    -- the one output `out` (data)
    (hone : d.shape.layout.outs.map (·.name) = ["out"])
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    {y : Res} (h : RealChild mref cref c y) :
    (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
        Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
      ∀ g ∈ y.2.modules,
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n g = true := by
  obtain ⟨m0, hpost, hT, hs0, -, hs, -⟩ :=
    Tools.ShippingLeafTyped.leaf_real_typedIn d ok hbody hC hdomB hno hSS outTy entry closes
      hon hoty h
  have hI := seqChild_of_real d ok hbody hno outTy entry closes h
  -- the returned module's output is `out`; so is the typed module's
  have hyo : y.1.outputs.map (·.name) = ["out"] := hI.outs.trans hone
  have hm0o : m0.outputs.map (·.name) = ["out"] := by
    rcases hpost with e | e
    · rw [← e]
      exact hyo
    · rw [← (Sparkle.IR.RefineCheck.mergeChecked_ports m0).2.1, ← e]
      exact hyo
  obtain ⟨ty, hout⟩ := single_out hm0o
  have htext : Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf y.1)
        (Tools.ShippingDesignSV.weS y.1) y.1.body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames y.1.body).all
        (fun x => Sparkle.IR.RegDedup.declWidth y.1 x == Tools.ShippingDesignSV.weS y.1 x) =
          true := by
    rcases hpost with e | e
    · rw [e]
      exact hT.seqCheck
    · rw [e]
      exact mergeChecked_text_out hT hout
  refine ⟨fun C n => Tools.ShippingLeafTyped.kidCheck_leaf_of_text C n hs htext.1 htext.2, ?_⟩
  intro g hg
  rw [hI.design] at hg
  cases hg

end Tools.ShippingCombKidText

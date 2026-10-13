import Tools.ShippingCombLeafDesign
import Tools.ShippingCastMerge
import Tools.ShippingTransitionTyped
import Tools.ShippingLeafOneOut
import Tools.ShippingChecksCore

/-! # (S1) and (S2) of a slotless leaf, proved GENERALLY from the run — and the closed design-level statement (round par/b-33)

WRITTEN, NOT BUILT.

`Tools.ShippingCombLeafDesign.comb_entry_design0_out` (BUILT at 4103e86f)
has two open antecedents about the module `b` a run returns:

    (S1) simpleBody b = true
    (S2) checkedOptimize b = b ∨ printOk (checkedOptimize b) = true

## Is `b` pinned to a concrete term of `f.machineData`? NO.

[`Tools/ShippingChildRun.lean` 528–540, `synthesizeMachineCertified_runs`]
the core module of a machine without calls is

    closeMachine shape.layout t'    where  closeLets shape.layout.lets t = some t'
                                    and    MReturns (synthesizeMixedCertified … shape.binders shape.body) (t, d₀)

and `t`, the TRANSITION, is an existential witness of a run of the mixed
compiler. What is known of it [`Tools/ShippingClosedTransitionTyped.lean`
73–84; `Tools/ShippingMachineEntry.lean` 642–661] is a set of PROPERTIES:
its body is `B ++ [out := w]` with `B` typed assignments to ALLOCATED wire
names; its port names are `machPorts declName ids cache binders` for an
existential `ids : List FVarId` and `cache : IO.Ref …`. The statements `B`
and every wire name depend on the fresh-name state of the run. There is no
equation `b = (a term of f.machineData)`, so (S1) / (S2) cannot be
discharged by `decide` / `rfl` on a concrete module per declaration.

## But (S1) and (S2) are INVARIANT facts, provable once

What IS known about `t` includes its statement SHAPES: the mixed entry's
`RawValueAt` carries `SimpleStmts t.body` [`ShippingMixedEntrySoundness.lean`
536–541] — `transition_typed_of_run` reads `TypedPostReady` and
`PrintBaseAt` out of the same record and drops this conjunct. So:

* `transition_simple_of_run` — `SimpleStmts t.body` (the proof of
  `Tools.ShippingTransitionTyped.transition_typed_of_run`, lines 67–100,
  copied by a script unchanged, then the fifth conjunct instead of the
  fourth and ninth);
* `closeLets_simple` — `closeLets` adds alias statements `p := a[w-1:0]`
  (a part-select with `lo = 0`: simple) and keeps the others;
* `closeMachine_slotless_shape` — without slots `closeMachine` replaces the
  final `out := w` by the output assignments `o := w[lo+width-1:lo]`
  (`closeMachine_slotless_body`, BUILT): simple when `0 < width`, and a CAST
  statement (`isCastExpr`: a part-select);
* the zero-width cleanup keeps the body (the wired facts, as
  `leaf_run_typedIn_bnd` reads them);
* the checked merge of an assignment-only body is `mergeDuplicates`, which
  keeps `SimpleStmts` (`mergeDuplicates_simple`, BUILT) and a cast statement
  (`Tools.ShippingCastMerge.mergeDuplicates_hasCast`, new, the control
  proof with `isCastExpr`).

Hence `comb_entry_shape`: for EVERY run from a world with `ChildBnd`,

    SimpleStmts b.body ∧ HasCast b.body ∧
      b.outputs.map (·.name) = d.shape.layout.outs.map (·.name)

(the third from `closeMachine_outputs`, BUILT) and then (S1) is `simpleBody_of` and (S2) is its first disjunct by the BUILT
`checkedOptimize_cast` (the optimizer keeps a simple body with a cast). No
compiler change; no evaluation of a module.

`comb_entry_shape`'s proof starts with the proof of
`Tools.ShippingLeafEntryBnd.leaf_run_typedIn_bnd`, lines 89–146, copied by
a script unchanged (the run's analysis down to the wired facts), with two
lines inserted before `ok` is destructured.

## The closed statement

`comb_entry_design0_of_ships`: from the conclusion of `f.machine_ships_comb`
for the run (as `Tools.ShippingLeafDesign.leaf_entry_design0_of_wired` takes
`f.machine_ships_wired`'s) — its three check antecedents discharged:
`simpleBody b` and `checkedOptimize b = b` by `comb_entry_shape`, the text of
`b` by `comb_entry_text_out` (BUILT). Binders the run and `MachineDefines f`
(and the closing, which the generator supplies), ONE antecedent under
`∃ raw`: `ChildBnd`. Because it consumes the ship-level endpoint as a
HYPOTHESIS, a transported endpoint (under `Eq.mpr`: fused loops,
sign-normalised values) needs no special treatment — the route the register
leaves' generator already takes. New data condition, per declaration:
`∀ o ∈ outs, 0 < o.width` (decidable on the layout).

SCOPE: one declaration as an entry, depth 0, no call, no register, one
output `out` of positive width; data conditions decided per declaration
(`CombKid`, the output width); the run, the reflection and the runtime
boundary `ChildBnd` stay premises; `DesignSV` of the module list over the
returned design's child map — not the SV string, not `#sim`; the seeding is
`seedR` (`rst` low). -/
namespace Tools.ShippingCombLeafShape

section Transition
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Sparkle.IR.NameHints (Allocated)
open Tools.ShippingSettledSoundness (Acyclic)
open Tools.ShippingTopoBody Tools.ShippingTopoChecks Tools.ShippingTopoLinked
open Tools.ShippingCloseInstsSome Tools.ShippingCloseChecks Tools.ShippingCloseMachineFacts
open Tools.ShippingInstStmt Tools.ShippingGateChildComb Tools.ShippingKidsComb
open Tools.ShippingCallsParent Tools.ShippingCallsStmts Tools.ShippingDesignWith
open Tools.ShippingRankRun Tools.ShippingRankNames Tools.ShippingCallsRank
open Tools.ShippingClosedOrder Tools.ShippingMachineCloses
open Tools.ShippingCloseLetsSplit (closedBody)
open Tools.ShippingMachineClose (concatParts?_mem mem_frontAliases mem_insertAliases)
open Tools.ShippingCallsAssembly
open Sparkle.IR.OptCheck (seqStmtOk)
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun
open Tools.ShippingChildInv
open Tools.ShippingCallsGate

set_option maxHeartbeats 2000000 in
/-- **The transition of a machine is of the simple shape**: every statement
an assignment whose right-hand side is one of the shapes `simpleRhs` lists.
(`transition_typed_of_run`'s proof, reading another conjunct of `RawValueAt`.) -/
theorem transition_simple_of_run {declName : Lean.Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {logProf : String → IO Unit} {t : Sparkle.IR.AST.Module} {d₀ : Design}
    (run : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      d.shape.binders d.shape.body) (t, d₀)) :
    Tools.ShippingPostSoundness.SimpleStmts t.body := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, _, _, _, outsOk, outsNodup, hwf, hb, hv,
    _, _, hscoped, _, _, _, _, _, _, _, _⟩ := ok
  have hposv : PositiveBinders d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  obtain ⟨raw, -, -⟩ :=
    Tools.ShippingMachineEntry.transition_facts nd len hrun hm nameLegal hwf hb' hv' hbody
  have zero : Tools.ShippingMixedSourceBridge.SourceInputs declName d.shape.binders ids cache
      (fun _ => false) (fun _ n => 0#n) (fun _ => 0) :=
    Tools.ShippingMachineEntry.admissible_zero _ _
  obtain ⟨_, _, _, _, simple, _, _, _, _⟩ := raw _ _ _ (fun _ _ => 0) zero
  exact simple

/-! ## Pure: the shapes `closeLets` and `closeMachine` add -/

/-- An alias statement of `closeLets` is of the simple shape. -/
theorem aliasStmt_simple (p : Port) (a : String) :
    ∃ l r, aliasStmt p a = Stmt.assign l r ∧ Sparkle.IR.OptCheck.simpleRhs r = true := by
  refine ⟨p.name, Expr.slice (Expr.ref a) (p.ty.bitWidth - 1) 0, rfl, ?_⟩
  first
    | exact decide_eq_true (Nat.zero_le _)
    | simp [Sparkle.IR.OptCheck.simpleRhs]

/-- **`closeLets` keeps the simple shape.** -/
theorem closeLets_simple {K : Nat} {t t' : Sparkle.IR.AST.Module} {B : List Stmt} {w : String}
    (hbody : t.body = B ++ [.assign "out" (.ref w)])
    (hacy : Tools.ShippingSettledSoundness.Acyclic t.body)
    (h : closeLets K t = some t') (hs : Tools.ShippingPostSoundness.SimpleStmts t.body) :
    Tools.ShippingPostSoundness.SimpleStmts t'.body := by
  obtain ⟨w0, al, core, -, -, ht', -⟩ := closeLets_eq' hbody hacy h
  rw [ht']
  intro st hst
  have hst' : st ∈ frontAliases al t.body.dropLast ++ insertAliases al t.body.dropLast ++
      [Stmt.assign "out" (Expr.ref core)] := hst
  rcases List.mem_append.mp hst' with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · obtain ⟨pa, -, e⟩ := mem_frontAliases h2
      rw [e]
      exact aliasStmt_simple pa.1 pa.2
    · rcases mem_insertAliases h2 with h3 | ⟨pa, -, e⟩
      · exact hs st (List.dropLast_subset _ h3)
      · rw [e]
        exact aliasStmt_simple pa.1 pa.2
  · have e : st = Stmt.assign "out" (Expr.ref core) := List.mem_singleton.mp h1
    exact ⟨"out", Expr.ref core, e, rfl⟩

/-- An output assignment of `closeMachine`: of the simple shape when the
field is not empty, and a cast (a part-select). -/
theorem outAssign_facts (w : String) (o : OutField) (hpos : 0 < o.width) :
    Sparkle.IR.OptCheck.simpleRhs (fieldRhs w o.lo o.width) = true ∧
      Tools.ShippingControlOptSoundness.isCastExpr (fieldRhs w o.lo o.width) = true := by
  have hle : o.lo ≤ o.lo + o.width - 1 := by omega
  refine ⟨?_, rfl⟩
  first
    | exact decide_eq_true hle
    | simp [Sparkle.IR.OptCheck.simpleRhs, fieldRhs, hle]

/-- **The closed machine without slots: of the simple shape, with a cast
statement** (an output's part-select of the packed wire). -/
theorem closeMachine_slotless_shape {t : Sparkle.IR.AST.Module} {lay : Layout}
    {B : List Stmt} {w : String}
    (hbody : t.body = B ++ [.assign "out" (.ref w)]) (hsl : lay.slots = [])
    (hs : Tools.ShippingPostSoundness.SimpleStmts t.body)
    (hpos : ∀ o ∈ lay.outs, 0 < o.width) (hne : lay.outs ≠ []) :
    Tools.ShippingPostSoundness.SimpleStmts (closeMachine lay t).body ∧
      Tools.ShippingControlOptSoundness.HasCast (closeMachine lay t).body := by
  rw [Tools.ShippingLeafOneOut.closeMachine_slotless_body hbody hsl]
  refine ⟨?_, ?_⟩
  · intro st hst
    rcases List.mem_append.mp hst with h1 | h1
    · exact hs st (by rw [hbody]; exact List.mem_append_left _ h1)
    · have h1' : st ∈ lay.outs.map
          (fun o => Stmt.assign o.name (fieldRhs w o.lo o.width)) := h1
      obtain ⟨o, ho, e⟩ := List.mem_map.mp h1'
      exact ⟨o.name, fieldRhs w o.lo o.width, e.symm, (outAssign_facts w o (hpos o ho)).1⟩
  · obtain ⟨o, ho⟩ : ∃ o, o ∈ lay.outs := by
      cases hout : lay.outs with
      | nil => exact absurd hout hne
      | cons o rest => exact ⟨o, List.mem_cons_self⟩
    have hm : Stmt.assign o.name (fieldRhs w o.lo o.width) ∈ lay.outs.map
        (fun o => Stmt.assign o.name (fieldRhs w o.lo o.width)) :=
      List.mem_map.mpr ⟨o, ho, rfl⟩
    exact ⟨o.name, fieldRhs w o.lo o.width, List.mem_append_right _ hm,
      (outAssign_facts w o (hpos o ho)).2⟩

/-- The names of the layout's output ports. -/
theorem outPorts_names : ∀ (L : List OutField),
    (L.map (fun o => ({ name := o.name, ty := o.ty } : Port))).map (·.name) = L.map (·.name)
  | [] => rfl
  | q :: rest => by
    have ih := outPorts_names rest
    first
      | (show q.name :: _ = q.name :: _
         exact congrArg (List.cons q.name) ih)
      | simpa using ih

end Transition

section Run
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingChecksDerived (ff_absurd)
open Tools.ShippingChecksDepth (and_true_intro)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **The full entry's module of a SLOTLESS machine is of the simple shape
and has a cast statement** — for every run of the full entry that starts in
a world with the runtime laws (`ChildBnd`). No hypothesis about a module. -/
theorem comb_entry_shape {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hsl : d.shape.layout.slots = [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hpos : ∀ o ∈ d.shape.layout.outs, 0 < o.width)
    (houtsNe : d.shape.layout.outs ≠ [])
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hbnd : ChildBnd mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape) :
    Tools.ShippingPostSoundness.SimpleStmts b.body ∧
      Tools.ShippingControlOptSoundness.HasCast b.body ∧
      b.outputs.map (·.name) = d.shape.layout.outs.map (·.name) := by
  obtain ⟨M, D, w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  have closes : MachineClosesAt mctx mref cctx cref c d.shape := machineClosesAt_of_closes closesM
  obtain ⟨bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
    machine_run_of_core hcore entry hbnd
  have hne := closes bb _ _ _ hw9 hd9 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨-, hMeq, hDeq⟩ | ⟨hne', -⟩
  rotate_left
  · exact absurd hno hne'
  obtain ⟨Bc, coreW, hbodyc, typedc, namedc, namesc, inWc, inNdc, wNdc, slotsc, hcoreW⟩ :=
    Tools.ShippingClosedTransitionTyped.closedTransition_of_run d ok hbody hC hSS hdomB run hcl
  -- (inserted, round par/b-33) the transition's shape, before `ok` is destructured
  have hsimpT : Tools.ShippingPostSoundness.SimpleStmts t.body :=
    transition_simple_of_run d ok hbody run
  obtain ⟨-, pbT, Bt, wt, hBt, -⟩ :=
    Tools.ShippingTransitionTyped.transition_typed_of_run d ok hbody run
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, _, _, _, _, _, _, _, _⟩ := ok
  have hposv : PositiveBinders d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  -- the raw module's wiring: the core entry's theorem at this run
  have layW : Tools.ShippingMachineClose.Zip₂
      (fun (f : SlotField) (b : Name × MixedGateBinder) =>
        f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeCombinationalCore_machine_sound hcore entry closesM d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, rlen, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hclean, -⟩ := wired
  obtain ⟨⟨hzb, hzw, -, hzo⟩, -, hregs, -, -, -, -, -, hseq⟩ := hclean hno outTy
  -- (end of the copied prefix) the shapes, step by step
  have hsimpT' : Tools.ShippingPostSoundness.SimpleStmts t'.body :=
    closeLets_simple hBt pbT.order hcl hsimpT
  obtain ⟨hsM, hcM⟩ :=
    closeMachine_slotless_shape (lay := d.shape.layout) hbodyc hsl hsimpT' hpos houtsNe
  have hsZ : Tools.ShippingPostSoundness.SimpleStmts
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body := by
    rw [hzb, hMeq]
    exact hsM
  have hcZ : Tools.ShippingControlOptSoundness.HasCast
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body := by
    rw [hzb, hMeq]
    exact hcM
  -- the output ports: the closed machine's are the layout's, the cleanup keeps them
  have hpw : packedWire? t'.body = some coreW := by simp [packedWire?, hbodyc]
  have hoM : M.outputs =
      d.shape.layout.outs.map (fun o => ({ name := o.name, ty := o.ty } : Port)) := by
    rw [hMeq]
    exact Tools.ShippingChecksCore.closeMachine_outputs hpw
  have hoZ : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).outputs.map (·.name) =
      d.shape.layout.outs.map (·.name) := by
    rw [hzo, hoM]
    exact outPorts_names d.shape.layout.outs
  rcases hpost with e | e
  · rw [e]
    exact ⟨hsZ, hcZ, hoZ⟩
  · have hall : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body.all
        Sparkle.IR.RegDedup.isAssign = true :=
      Tools.ShippingMachineShipsComb.simpleBody_assigns
        (Tools.ShippingPostSoundness.simpleBody_of _ hsZ)
    rw [e, Tools.ShippingCombKidText.mergeChecked_assign hall]
    refine ⟨Tools.ShippingPostSoundness.mergeDuplicates_simple _ hsZ,
      Tools.ShippingCastMerge.mergeDuplicates_hasCast _ hsZ hcZ, ?_⟩
    rw [(Sparkle.IR.RegDedup.mergeDuplicates_ports _).2.1]
    exact hoZ

end Run

section Entry
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingSeqOptSoundness Tools.ShippingRefineSoundness
open Tools.ShippingSeqSVSoundness Tools.ShippingPipelineSoundness
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingMachineShipsComb (seedR)
open Tools.ShippingCombLeafDesign (CombKid)

/-- **A slotless leaf machine with the one output `out`, as an entry, at the
design level — from its ship-level endpoint.** `hships` is what
`f.machine_ships_comb` gives for the run (its `MachineCloses` binder
discharged); its three check antecedents are discharged here, from the run
and `ChildBnd`: `simpleBody b` and the shipped module's text by
`comb_entry_shape` (the module is of the simple shape and has a cast, so the
optimizer keeps it), the module's own text by `comb_entry_text_out`. Binders
the run, the reflection (and the closing, which a generator supplies from the
data); under `∃ raw` ONE antecedent, `ChildBnd`. The child map is that of the
RETURNED design. This is the term `#machine_comb_design0` instantiates. -/
theorem comb_entry_design0_of_ships {declName : Name} {d : MachineData}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {c : Name} {dk : MachineData}
    (hships : ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∀ (wof : String → Option Nat),
        simpleBody b = true →
        Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof)
          (checkedOptimize b).body = true →
        ((seqNames (checkedOptimize b).body).all fun n =>
          declWidth (checkedOptimize b) n == Tools.SVParser.EmitSem.weOf wof n) = true →
        Tools.ShippingMachineShipsComb.MachineShipsComb declName d
          (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) (checkedOptimize b) wof dom src)
    (K : CombKid c dk)
    (hpos : ∀ o ∈ dk.shape.layout.outs, 0 < o.width)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c dk.shape)
    (closes : MachineCloses mctx mref cctx cref c dk.shape) :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (Tools.ShippingChildInv.ChildBnd mref cref w →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
        ∃ cache : IO.Ref (ExprStructMap String),
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → Tools.ShippingHierStateG.KT 0),
            -- the source's inputs are the seeding's (`rst` low)
            (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
              (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
              (seedR b ins t st)) →
            -- the inputs within the declared and the emitted widths; the state within the emitted
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ t x, x ∈ b.inputs.map (·.name) →
              ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x) →
            Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st0 →
            -- a closed run of the emitted text showing the source exists ...
            (∃ envsO,
              Tools.ShippingDesignSV.DesignSV (Tools.ShippingMachineLinked.childMap design.modules)
                0 (checkedOptimize b) (seedR b ins) T ⟨st0, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (q : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) q.name = f j)
            -- ... and EVERY closed run from the same seeding and states shows it
            ∧ ∀ envs', Tools.ShippingDesignSV.DesignSV
                  (Tools.ShippingMachineLinked.childMap design.modules)
                  0 (checkedOptimize b) (seedR b ins) T ⟨st0, mems, kids⟩ envs' →
                envs'.length = T ∧
                ∀ j (hj : j < envs'.length) (k : Nat) (q : OutField) (f : Nat → Nat),
                  d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
                  (envs'[j]'hj) q.name = f j) := by
  obtain ⟨raw, hpost, H⟩ := hships
  refine ⟨raw, hpost, ?_⟩
  intro hbnd
  have hSS' : dk.ss.length = dk.shape.layout.slots.length := by
    rw [K.slots]
    exact K.ss
  have hne : dk.shape.layout.outs ≠ [] := by
    intro h0
    have h1 := K.one
    rw [h0] at h1
    first
      | cases h1
      | simp at h1
  obtain ⟨hs, hc, hbo0⟩ := comb_entry_shape dk K.ok K.body K.calls K.dom K.leaf K.slots hSS'
    K.outTy hpos hne hbnd hr entry closes
  have hbo : b.outputs.map (·.name) = ["out"] := hbo0.trans K.one
  have hsB : simpleBody b = true := Tools.ShippingPostSoundness.simpleBody_of b hs
  have hopt : checkedOptimize b = b ∨
      Sparkle.IR.PrintGuard.printOk (checkedOptimize b) = true :=
    Or.inl (Tools.ShippingControlOptSoundness.checkedOptimize_cast hsB hc)
  have htext := Tools.ShippingCombLeafDesign.comb_entry_text_out dk K.ok K.body K.calls K.dom
    K.leaf hSS' K.outTy hbnd hr entry closes K.outName K.outScalar hbo
  obtain ⟨c2, c3⟩ := Tools.ShippingLeafEntry.text_shipped_of_print htext hopt
  have c2' : Tools.SVParser.EmitSem.seqCheck
      (Tools.ShippingDesignSV.wofOf (checkedOptimize b))
      (Tools.SVParser.EmitSem.weOf (Tools.ShippingDesignSV.wofOf (checkedOptimize b)))
      (checkedOptimize b).body = true := c2
  have c3' : ((seqNames (checkedOptimize b).body).all fun n =>
      declWidth (checkedOptimize b) n ==
        Tools.SVParser.EmitSem.weOf (Tools.ShippingDesignSV.wofOf (checkedOptimize b)) n) =
      true := c3
  have hS := H (Tools.ShippingDesignSV.wofOf (checkedOptimize b)) hsB c2' c3'
  have hsq : (checkedOptimize b).body.all Sparkle.IR.OptCheck.seqStmtOk = true :=
    Tools.ShippingMachineShipsComb.assigns_seqOk
      (Tools.ShippingMachineShipsComb.checkedOptimize_assigns hsB)
  obtain ⟨ids, nd, len, cache, G⟩ :=
    Tools.ShippingCombLeafDesign.comb_design_of_ships hsq hpost hS
  refine ⟨ids, nd, len, cache, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hinsB hinsW hstB
  obtain ⟨envsO, -, hD, hlen, hobs, huniq⟩ := G i bools bits T ins st0 mems hsrc hinsB hinsW hstB
  refine ⟨⟨envsO, hD (Tools.ShippingMachineLinked.childMap design.modules) kids, hlen, hobs⟩, ?_⟩
  intro envs' hD'
  have e := huniq (Tools.ShippingMachineLinked.childMap design.modules) kids envs' hD'
  subst e
  exact ⟨hlen, hobs⟩

end Entry

end Tools.ShippingCombLeafShape

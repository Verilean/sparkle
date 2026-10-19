import Tools.ShippingChecksCore
import Tools.ShippingChecksShipsHier
import Tools.ShippingMachineRanBase
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # Three conjuncts of `shipsHierCheck` from the core run (G1)

For a core run on a machine WITH calls closed by `closeInstsG`
(`instFields ≠ []`: calls with several outputs or of sequential children)
and WITH a register, at the machine boundary — the hypotheses of
`core_kids_facts`, plus `hsl` (a slot) and `hfne` — on the full entry's
module `b`:

* (7) `"rst" ∈ b.inputs.map (·.name)`;
* (3) `(instNames b.body).Nodup`;
* (5) `noSelfRead (childMap D.modules) b.body = true`.

All three are read off `MachineWired` (`Tools/ShippingMachineEntry.lean`),
which the machine entry's soundness theorem gives for the raw module of the
run; nothing about the compiler is proved anew here:
* its input clause: the raw inputs are `(ports ++ (if no slot then [] else
  [clk, rst]) ++ extra)` without the call ports, the call ports allocated
  names — `"rst"` is not allocated (`rst_not_allocated`);
* its clause 14: the instance names are distinct and no instance feeds
  itself (`noSelfFeed`), which is `noSelfRead` at `childMap`
  (`noSelfRead_of_feed`);
* the cleanup and the checked merge keep the inputs, and the body
  (`core_kids_facts`).

What the code does for a SLOTLESS parent (not covered by the theorem, read
from the same input clause): the list is `ports ++ [] ++ extra`, with
`extra = []` or `extra = [clk, rst]`; `withClockFor` adds `clk`, `rst`
exactly when some child has a `clk` or `rst` input and the parent has not
both. So a slotless parent of a sequential child DOES get `rst`; a slotless
parent whose children are all combinational does not — for it conjunct 7 is
false and the sequential route's check rightly fails (such parents ship by
the combinational route `shipsHierHCheck`, which does not ask it). The
wiring clause states `extra` as a disjunction without the condition, so the
slotless-with-sequential-child case is NOT derivable from `MachineWired` as
it stands.

`core_shipsHier_rest`: `shipsHierCheck` from the run and the five conjuncts
still underived (1 `hierBinds`, 2 `linkedWF` of the optimized body, 4 the
optimized module's distinct instance names, 6 `outsExtracted`,
8 `instOutWidthsOk`).

The statement and the first part of `core_raw_facts`' proof are
`core_kids_facts`' (my own), copied by a script.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingChecksRaw
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

theorem rst_not_allocated : ¬ Sparkle.IR.NameHints.Allocated "rst" := by
  intro h
  have := h.2
  revert this
  decide

/-- The instance names, as the wiring states them and as the checks do. -/
theorem instNameOf_eq : ∀ body : List Stmt,
    body.filterMap Sparkle.IR.Machine.instNameOf = Tools.ShippingHierState.instNames body
  | [] => rfl
  | st :: rest => by
    have ih := instNameOf_eq rest
    cases st with
    | inst mn i conns => exact congrArg (fun l => i :: l) ih
    | _ => exact ih

/-- The instance-output wires, as the checks and as the wiring write them. -/
theorem instOutWires_eq (outs : List Port) (conns : List (String × Sparkle.IR.AST.Expr)) :
    Tools.ShippingHierOpen.instOutWires outs conns =
      Sparkle.IR.Machine.instOutWiresOf outs conns := by
  unfold Tools.ShippingHierOpen.instOutWires Sparkle.IR.Machine.instOutWiresOf
  refine congrArg (fun k => outs.filterMap k) (funext fun p => ?_)
  cases conns.lookup p.name with
  | none => rfl
  | some e => cases e <;> rfl

/-- The wiring's self-feed test is the checks' self-read test at `childMap`. -/
theorem noSelfRead_of_feed {ms : List Sparkle.IR.AST.Module} {body : List Stmt}
    (h : Sparkle.IR.Machine.noSelfFeed (moduleByName ms) body = true) :
    Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) body = true := by
  unfold Sparkle.IR.Machine.noSelfFeed at h
  unfold Tools.ShippingHierPremisesBase.noSelfRead
  rw [List.all_eq_true]
  intro st hst
  have h1 := List.all_eq_true.mp h st hst
  cases st with
  | inst mn iname conns =>
    cases hm : moduleByName ms mn with
    | none =>
      have hc : childMap ms mn = none :=
        congrArg (Option.map fun c => (c, Sparkle.IR.RegDedup.declWidth c)) hm
      simp only [hc]
    | some c =>
      have hc : childMap ms mn = some (c, Sparkle.IR.RegDedup.declWidth c) :=
        congrArg (Option.map fun c => (c, Sparkle.IR.RegDedup.declWidth c)) hm
      simp only [hc]
      simp only [hm] at h1
      rw [List.all_eq_true] at h1 ⊢
      intro cn hcn
      have h2 := h1 cn hcn
      obtain ⟨nm, e⟩ := cn
      cases e with
      | ref w =>
        show (!(Tools.ShippingHierOpen.instOutWires c.outputs conns).contains w) = true
        rw [instOutWires_eq]
        exact h2
      | _ => rfl
  | _ => rfl

end Tools.ShippingChecksRaw

/-! ## The general closing's form of `core_*` theorems of this file (`Kid` for `RealChild`, no `hnomem`)

MOVED here from `Tools/ShippingMemKidCore.lean` (round par/b-24): name,
namespace `Tools.ShippingMemKid`, statement and proof unchanged. Each old
theorem whose `…M` form is here is now a COROLLARY of it (statement unchanged,
proof = the body of the built `…_fromM` re-derivation in
`Tools/ShippingCoreFromM.lean`). -/
namespace Tools.ShippingMemKid
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingChecksRaw

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `core_raw_factsMT` over `MachineRan`: the TAIL of the built proof, moved (round par/g-1).
What it takes of the run is that the machine synthesis this core run performed
returned `(M, D)` from an invariant world; `core_raw_factsMT` below is its instance at the
all-worlds closing (`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem core_raw_factsM_ranT {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    "rst" ∈ b.inputs.map (·.name) ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true := by
  have ran0 := ran
  obtain ⟨_, bb, w9, w10, hrun9, hw9, -⟩ := ran0
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd hno hins
  obtain ⟨-, -, hMname, L, hLinst, hperm, -, -, -, -, -, hDeq, -⟩ := hcc.some
  obtain ⟨hseq0, hname0, hd0⟩ := closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl
  -- the raw module's wiring
  have ok' := ok
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok'
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, _, _, _, _, _, _, _, _⟩ := ok'
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
  have layW : Tools.ShippingMachineClose.Zip₂
      (fun (f : SlotField) (b : Name × MixedGateBinder) =>
        f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeMachineCertified_sound hrun9.mreturns d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, -, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, hAlloc, -, -, -, -, -, -, -, -, -, -, -, hG14, -, hcleanAny, hInputs, -⟩ := wired
  obtain ⟨-, -, hzi, -⟩ := hcleanAny outTy
  obtain ⟨hndM, hsfM⟩ := hG14 hfne
  obtain ⟨outWs, extra, houtWs, -, -, hMin⟩ := hInputs
  have hbody' : b.body = M.body :=
    (core_kids_factsM_ranT d ok hbody hC hslots hdomB hins outTy hfne hpost ran).2.1
  have hbin : b.inputs = M.inputs := by
    rcases hpost with h | h
    · rw [h]
      exact hzi
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).1]
      exact hzi
  have hne : d.shape.layout.slots.isEmpty = false := by
    cases hs : d.shape.layout.slots with
    | nil => exact absurd hs hsl
    | cons _ _ => rfl
  have hnotW : "rst" ∉ outWs := by
    intro hm
    obtain ⟨k, -, hk⟩ := houtWs _ hm
    exact rst_not_allocated (hAlloc _ (List.mem_of_getElem? hk))
  have hrstM : "rst" ∈ M.inputs.map (·.name) := by
    rw [hMin]
    refine List.mem_map.mpr ⟨{ name := "rst", ty := .bit }, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · refine List.mem_append_left _ (List.mem_append_right _ ?_)
      rw [hne]
      simp
    · simpa using hnotW
  refine ⟨by rw [hbin]; exact hrstM, ?_, ?_⟩
  · rw [hbody', ← instNameOf_eq]
    exact hndM
  · rw [hbody']
    exact noSelfRead_of_feed hsfM

set_option maxHeartbeats 4000000 in
/-- The `TagsAgree` form of `core_raw_factsM_ranT` (statement unchanged; a corollary). -/
theorem core_raw_factsM_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hagree : Tools.ShippingInstTagged.TagsAgree d.shape)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    "rst" ∈ b.inputs.map (·.name) ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true := by
  have cvK : ∀ {k : Nat} (hk : k < d.shape.insts.length) {y : Res},
      Tools.ShippingInstTagged.KidT mref cref (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y →
        Kid mref cref (d.shape.insts[k]).1 y :=
    fun hk _ hy => Tools.ShippingInstTagged.kid_of_kidT hy (Tools.ShippingInstTagged.agree_at hagree hk)
  apply core_raw_factsM_ranT
  all_goals first | assumption | rfl

set_option maxHeartbeats 4000000 in
/-- **The reset input, the distinct instance names and the self-read test of
the full entry's module**, from the core run of a machine with calls closed
by `closeInstsG` and with a register. -/
theorem core_raw_factsMT {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    "rst" ∈ b.inputs.map (·.name) ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true :=
  core_raw_factsM_ranT d ok hbody hC hslots hdomB hins hsl hfne outTy hpost
    (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes)

set_option maxHeartbeats 4000000 in
/-- The `TagsAgree` form of `core_raw_factsMT` (statement unchanged; a corollary). -/
theorem core_raw_factsM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hagree : Tools.ShippingInstTagged.TagsAgree d.shape)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    "rst" ∈ b.inputs.map (·.name) ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true := by
  have cvK : ∀ {k : Nat} (hk : k < d.shape.insts.length) {y : Res},
      Tools.ShippingInstTagged.KidT mref cref (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y →
        Kid mref cref (d.shape.insts[k]).1 y :=
    fun hk _ hy => Tools.ShippingInstTagged.kid_of_kidT hy (Tools.ShippingInstTagged.agree_at hagree hk)
  apply core_raw_factsMT
  all_goals first | assumption | rfl

end Tools.ShippingMemKid

namespace Tools.ShippingChecksRaw
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `core_raw_facts` over `MachineRan`:
the proof of the built theorem, MOVED here (split in place, branch
`fix/ran-threading-split`) with the run, the reflection, the closing and the boundary
replaced by `ran` and every callee of the chain by its `_ran` form. It takes of the run only
that the machine synthesis this core run performed returned the result from an invariant
world; the theorem below, its statement unchanged, is the instance at the all-worlds closing
(`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem core_raw_facts_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    "rst" ∈ b.inputs.map (·.name) ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true := by
  exact Tools.ShippingMemKid.core_raw_factsM_ran (hagree := (Tools.ShippingInstTagged.tagsAgree_of_nomem hnomem)) d ok hbody hC hslots hdomB hins hsl hfne outTy
    hpost ran

set_option maxHeartbeats 4000000 in
/-- **The reset input, the distinct instance names and the self-read test of
the full entry's module**, from the core run of a machine with calls closed
by `closeInstsG` and with a register. -/
theorem core_raw_facts {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    "rst" ∈ b.inputs.map (·.name) ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true :=
  core_raw_facts_ran d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem hpost
    (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes)

/-- **`shipsHierCheck` from the run and the five conjuncts not derived**:
the optimizer gate, the two post-pass facts, the extraction of the
instance-driven wires and the instance-output widths. -/
theorem core_shipsHier_rest {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    -- 1: the optimizer gate
    (hb : hierBinds b = true)
    -- 2, 4: the post-pass facts
    (hwfO : Tools.ShippingHierOpen.linkedWF (childMap D.modules) (checkedOptimize b).body = true)
    (hndO : (Tools.ShippingHierState.instNames (checkedOptimize b).body).Nodup)
    -- 6, 8: run facts not derived yet
    (houts : Tools.ShippingHierPremisesBase.outsExtracted (childMap D.modules) b = true)
    (hwid : Tools.ShippingHierOpen.instOutWidthsOk (childMap D.modules)
      (Sparkle.IR.RegDedup.declWidth b) b.body = true) :
    Tools.ShippingHierPremisesBase.shipsHierCheck (childMap D.modules) b = true := by
  obtain ⟨hrst, hndB, hself⟩ :=
    core_raw_facts d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem hB hcore hpost entry
      closes
  exact Tools.ShippingChecksShipsHier.shipsHierCheck_of hb hwfO hndB hndO hself houts hrst hwid

end Tools.ShippingChecksRaw

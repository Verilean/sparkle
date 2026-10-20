import Tools.ShippingFirstGateKid
import Tools.ShippingGateChild

/-! # The cone's child facts for a MIXED-gate child (worker W, round 2)

WRITTEN, NOT BUILT.

`Tools.ShippingFirstGateKid.kidFacts_of_first` gives the cone's child facts
(`KidFacts`) of a FIRST-gate child (a leading domain binder, all inputs of one
width, an `FExpr` body). A child the unified MIXED gate compiles — inputs of
different widths, Bool inputs, muxes of compares, no domain binder, e.g.
`pick sel x` — has the same facts, from the mixed gate's own theorems:

* `gate_child_fnR` — what the full entry's module computes, WITHOUT a reset
  premise (`ChildFnR`): `gate_core_facts` + `gate_childFnR` + `childFnR_post`
  (the reset-free twin of `Tools.ShippingGateChild.gate_child_full`; the
  instance arm's connection environment does not pin `rst`, so `KidFacts`
  asks the evaluation on every environment);
* `gate_full_outputs` — the full entry's one output is `out : bitVector w`
  for a result of width `w ≠ 1` (the gate's `PrintBaseAt` gives a printable
  output type of the result's bit width; a printable type of width ≠ 1 is a
  bit vector);
* **`kidFacts_of_gate`** — `KidFacts (ownChild y) C c n v y` for a `RealChild`
  entry `y` of a mixed-gate child `c` with `EntryDefines` (ALLOWED), the
  gate's reading of `c` (its peel, well-formedness, binder positions — what
  `#gate_child c` generates as `c.gate_peel`, `c.gate_wf`, …) and what the
  consumer's child semantics `C` answers on `c` (`hC`, a property of `C`
  alone, discharged per declaration by evaluation). -/
namespace Tools.ShippingGateKid
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingFirstGateChild (ChildFnR gate_childFnR childFnR_post nAlloc_clk nAlloc_rst
  nAlloc_out)
open Tools.ShippingFirstGateKid (ownChild ownChild_self)
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingMachineChild (InRange decB decV)
open Tools.ShippingGateChildComb (ChildFull gate_child_fullFacts synthesizeCombinational_parts)
open Tools.ShippingUnifiedMeaning (Value ChildSem pack)
open Tools.ShippingUnifiedSource (SType Term eval quote)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingChildInv (Res RealChild)
open Tools.ShippingGateParentRun (KidFacts)

set_option linter.unusedSectionVars false

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A mixed-gate child at the full entry, without a reset premise**: the
module of a run computes `F` on its argument ports (`ChildFnR`). The proof of
`Tools.ShippingGateChild.gate_child_full` with the reset-free
`gate_childFnR` / `childFnR_post`. -/
theorem gate_child_fnR {declName : Name} {w w' : Void IO.RealWorld}
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
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    {F : List Nat → Nat}
    (hF : ∀ vs, InRange vs (bs.filter fun b => b.2 != .domain) →
      F vs = (pack srt (eval (fun j => decB bs vs (bpos j)) (fun j w => decV bs vs (vpos j) w) e)).toNat) :
    ChildFnR b (fun vs => InRange vs (bs.filter fun b => b.2 != .domain)) F := by
  obtain ⟨M, D, w1, hcore, hpost, -⟩ := synthesizeCombinational_parts hr
  obtain ⟨ids, cache, nd, len, vals, ins, positive⟩ :=
    Tools.ShippingGateChild.gate_core_facts hcore entry old peel he hb hv
  obtain ⟨hfn, hall, htp⟩ := gate_childFnR nd len vals ins positive hF
  exact childFnR_post hfn htp hall hpost

/-- **The full entry's one output of a mixed-gate child is `out : bitVector w`**
for a result of width `w ≠ 1`. -/
theorem gate_full_outputs {declName : Name} {w w' : Void IO.RealWorld}
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
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (hw1 : srt.width ≠ 1) :
    b.outputs = [{ name := "out", ty := .bitVector srt.width }] := by
  obtain ⟨M, D, w1, hcore, hpost, -⟩ := synthesizeCombinational_parts hr
  obtain ⟨ids, cache, nd, len, vals, ins, positive⟩ :=
    Tools.ShippingGateChild.gate_core_facts hcore entry old peel he hb hv
  obtain ⟨_, _, _, tpr, _, _, _, _, pb⟩ := vals (fun _ => false) (fun _ n => 0#n) (fun _ => 0)
    (fun _ _ => 0) (Tools.ShippingGateChild.admissible_zero _ _)
  have pb := pb positive
  obtain ⟨ty, hout⟩ := pb.output
  have hmem : ({ name := "out", ty := ty } : Port) ∈ M.outputs := by
    rw [hout]
    exact List.mem_cons_self
  have hpt : Tools.ShippingModulePrintSoundness.PrintableType ty := pb.outputs _ hmem
  have hwd : ty.bitWidth = srt.width := pb.outputWidth _ hmem
  have hty : ty = .bitVector srt.width := by
    cases hpt with
    | bit => exact absurd (show srt.width = 1 from hwd.symm) hw1
    | bits n hn =>
      have hn' : n = srt.width := hwd
      rw [hn']
  obtain ⟨_, _, _, ho, _⟩ := Tools.ShippingTypedPostSoundness.dropZeroWidth_typed tpr
  rcases hpost with rfl | rfl
  · rw [ho, hout, hty]
  · rw [(Sparkle.IR.RefineCheck.mergeChecked_ports _).2.1, ho, hout, hty]

set_option maxHeartbeats 1000000 in
/-- **The cone's child facts of a MIXED-gate child, from its `RealChild`
witness and `EntryDefines`** — in the linked context of the run's own child,
with an empty design. The gate's reading of `c` (`peel`, `he`, `hb`, `hv`,
`old`) is what `#gate_child c` generates; `F` is any function the term's
value is (`hF`, `fun _ _ => rfl` for the term's own value); `hC`: what the
consumer's child semantics answers on `c` — the argument count, in-range
values, and the result as `F` of the values. -/
theorem kidFacts_of_gate {c : Name} {b : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (hw1 : srt.width ≠ 1)
    {F : List Nat → Nat}
    (hF : ∀ vs, InRange vs (bs.filter fun b => b.2 != .domain) →
      F vs = (pack srt (eval (fun j => decB bs vs (bpos j)) (fun j w => decV bs vs (vpos j) w) e)).toNat)
    (h : RealChild mref cref c (b, design)) (C : ChildSem) (n : Nat)
    (hn : (bs.filter fun x => x.2 != .domain).length = n)
    (v : Value) (hvw : v.kind.width = srt.width)
    (hC : ∀ (vs : List Value) (u : Value), @ChildSem.childSem C c vs = some u →
      vs.length = n ∧ InRange (vs.map Value.toNat) (bs.filter fun x => x.2 != .domain) ∧
      u.toNat = F (vs.map Value.toNat)) :
    KidFacts (ownChild (b, design)) C c n v (b, design) := by
  -- the child's OWN run, in its own contexts; the reflection moved there
  obtain ⟨mctx', cctx', w, w', -, hr⟩ := h.inv
  have entry' : EntryDefines mctx' mref cctx' cref c value :=
    Tools.ShippingReflectCtx.EntryDefines.ctx entry
  have full : ChildFull c bs b design := gate_child_fullFacts hr entry' old peel he hb hv
  have fn := gate_child_fnR hr entry' old peel he hb hv hF
  have houts := gate_full_outputs hr entry' old peel he hb hv hw1
  have alloc := full.comb.inputAlloc
  have hinLen : b.inputs.length = n := by
    have hl := congrArg List.length full.tys
    simp only [List.length_map] at hl
    exact hl.trans hn
  have hargs : argPorts b = b.inputs := by
    unfold argPorts
    apply List.filter_eq_self.mpr
    intro p hp
    have hc : p.name ≠ "clk" := fun e => nAlloc_clk (by rw [← e]; exact alloc p hp)
    have hr' : p.name ≠ "rst" := fun e => nAlloc_rst (by rw [← e]; exact alloc p hp)
    simp [hc, hr']
  refine ⟨Sparkle.IR.RegDedup.declWidth b, "out", srt.width, full.design, ?_,
    full.comb.inputNames, houts, ?_, hinLen, hvw, ownChild_self (b, design), ?_⟩
  · intro p hp
    exact ⟨beq_false_of_ne (fun e => nAlloc_clk (by rw [← e]; exact alloc p hp)),
      beq_false_of_ne (fun e => nAlloc_rst (by rw [← e]; exact alloc p hp))⟩
  · intro p hp
    exact beq_false_of_ne (fun e => nAlloc_out (by rw [e]; exact alloc p hp))
  · intro mems envIn vs u hsem hports
    obtain ⟨hlen, hrange, hu⟩ := hC vs u hsem
    obtain ⟨outP, houtP, hf⟩ := fn
    have hP : outP = { name := "out", ty := .bitVector srt.width } := by
      rw [houts] at houtP
      exact (List.cons.inj houtP).1.symm
    subst hP
    have hvals : (argPorts b).map (fun p => envIn p.name) = vs.map Value.toNat := by
      rw [hargs]
      apply List.ext_getElem
      · rw [List.length_map, List.length_map, hinLen, hlen]
      · intro k h1 h2
        rw [List.getElem_map, List.getElem_map]
        exact hports k (by rw [List.length_map] at h1; exact h1)
          (by rw [List.length_map] at h2; exact h2)
    obtain ⟨cres, hev, hcres⟩ := hf mems envIn (by rw [hvals]; exact hrange)
    refine ⟨cres, hev, ?_⟩
    rw [hvals] at hcres
    rw [hu]
    exact hcres

/-- The same over a cache entry `y` (a pair). -/
theorem kidFacts_of_gate' {c : Name} {y : Res}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (hw1 : srt.width ≠ 1)
    {F : List Nat → Nat}
    (hF : ∀ vs, InRange vs (bs.filter fun b => b.2 != .domain) →
      F vs = (pack srt (eval (fun j => decB bs vs (bpos j)) (fun j w => decV bs vs (vpos j) w) e)).toNat)
    (h : RealChild mref cref c y) (C : ChildSem) (n : Nat)
    (hn : (bs.filter fun x => x.2 != .domain).length = n)
    (v : Value) (hvw : v.kind.width = srt.width)
    (hC : ∀ (vs : List Value) (u : Value), @ChildSem.childSem C c vs = some u →
      vs.length = n ∧ InRange (vs.map Value.toNat) (bs.filter fun x => x.2 != .domain) ∧
      u.toNat = F (vs.map Value.toNat)) :
    KidFacts (ownChild y) C c n v y := by
  obtain ⟨b, design⟩ := y
  exact kidFacts_of_gate entry old peel he hb hv hw1 hF h C n hn v hvw hC

end Tools.ShippingGateKid

#print axioms Tools.ShippingGateKid.gate_child_fnR
#print axioms Tools.ShippingGateKid.gate_full_outputs
#print axioms Tools.ShippingGateKid.kidFacts_of_gate

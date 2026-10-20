import Tools.ShippingMemClosesKidsT
import Tools.ShippingCallsGate
import Tools.ShippingSeqChildIface
import Tools.ShippingReflectCtx

/-! # A GATE-route (combinational) child under the GENERAL closing: its `ChildIfaceP` (round par/o-gate)

BUILT as written (par/o-gate; integrator runs gt1/gt2; `gateChild_ifaceP_of_real`, `gateKidT_iface`: [propext, Classical.choice, Quot.sound]).

The general closing (`closeInstsG`; `Tools.ShippingMemCloses.machineClosesAt_of_kidsDMT`,
`machineClosesAt_of_kidsDM`, `closeInstsG_of_kidsP`) asks of every child the
interface `Tools.ShippingMemCloses.ChildIfaceP` (`Tools/ShippingMemClosesKids.lean`).
For a register machine without calls it is derived (`seqChild_of_real`,
`ChildIfaceG.toD`, `ChildIfaceD.toP`); for a gate-route child it was not
(`Tools/ShippingChildIfaceGen.lean`: "a gate child … directly under the general
closing (not derived)").

This file derives it, from the EXISTING built gate-child facts, nothing new
about the compiler:

* `ChildFull c bs b design` (`Tools/ShippingGateChildComb.lean`, BUILT): the
  module is assignments only, its one output is `out`, its input ports are
  distinct ALLOCATED names (`inputAlloc`), the port types are the
  declaration's non-domain binders, the name is `ofDecl c`, the design has no
  module;
* `Tools.ShippingCallsGate.childFull_of_real` (BUILT): a `RealChild` of a
  declaration the unified (mixed) gate compiles has `ChildFull` — premises
  exactly those of `gate_child_fullFacts`: the declaration's reflection
  `EntryDefines … c value`, `old` (the FIRST gate does not take it), `peel`
  (the gate's peel of `value` is the quote of a term `e`), `he` (`e` well
  formed), `hb`/`hv` (its input positions are the binders'). `#gate_child c`
  leaves these as `c.gateValue`, `c.gate_old`, `c.gate_peel`, `c.gate_wf`,
  and `bool_positions`/`bits_positions (by decide)`.

Contents:

* `filter_id_of_all`, `not_alloc_clk/rst/out`, `inPortsOf_of_alloc` — an
  allocated input is neither `clk` nor `rst`, so `inPortsOf b = b.inputs`;
* `ChildFull.toG` — `ChildFull` gives `ChildIfaceG c n ["out"] b design`,
  `n` the number of non-domain binders (assignments are `seqStmtOk`; `out` is
  not allocated, so no input is named `out`);
* `ChildFull.toP` — hence `ChildIfaceP (ofDecl c) n ["out"] [] b design`
  (through the BUILT `ChildIfaceG.toD`, `ChildIfaceD.toP`; the design is
  empty, so `ofDecl c ∉ []`);
* `gateChild_ifaceP_of_real` — **a `RealChild` of a gate declaration has the
  general closing's interface**, premises: those of `childFull_of_real`;
* `gateKidT_iface` — the same for the origin-based kid `KidT … o c y` of an
  entry whose origin builds no memory (`o.child? = none`, e.g. `.ord`).

Every premise is explicit (no bundle); nothing is added to `RefLaws` or any
trusted list. NOT covered: a FIRST-gate child (`certifiedShape?` takes it;
`Tools/ShippingFirstGateChild.lean` has a `ChildFull` for it, NOT BUILT — the
`toP` step here applies to it unchanged once built); a gate child with
several outputs (no `ChildFull` for one exists); the generator
(`Tools/ShippingChildIfaceGen.lean` still refuses a gate child under the
general closing — this file gives the theorem it would apply). -/
namespace Tools.ShippingGateChildIfaceP
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST
open Tools.ShippingGateChildComb (ChildFull)
open Tools.ShippingChildInv (Res RealChild)
open Tools.ShippingInstStmtG (inPortsOf)
open Tools.ShippingSeqChildIface (ChildIfaceG)
open Tools.ShippingMemCloses (ChildIfaceP)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingInlineSoundness (EntryDefines)
open Sparkle.IR.NameHints (Allocated)
open Sparkle.IR.OptCheck (seqStmtOk)

theorem filter_id_of_all {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = true) → l.filter p = l
  | [], _ => rfl
  | a :: l, h => by
    have ha : p a = true := h a (List.mem_cons_self ..)
    have ih := filter_id_of_all p l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [List.filter_cons, ha, ih]

theorem not_alloc_clk : ¬ Allocated "clk" := by
  intro h
  have := h.2
  revert this
  decide

theorem not_alloc_rst : ¬ Allocated "rst" := by
  intro h
  have := h.2
  revert this
  decide

theorem not_alloc_out : ¬ Allocated "out" := by
  intro h
  have := h.2
  revert this
  decide

/-- Allocated inputs: none is the clock or the reset, so every input is an
argument port. -/
theorem inPortsOf_of_alloc {b : Sparkle.IR.AST.Module} (h : ∀ p ∈ b.inputs, Allocated p.name) :
    inPortsOf b = b.inputs := by
  unfold inPortsOf
  apply filter_id_of_all
  intro p hp
  have hA := h p hp
  have h1 : p.name ≠ "clk" := fun e => not_alloc_clk (by rw [← e]; exact hA)
  have h2 : p.name ≠ "rst" := fun e => not_alloc_rst (by rw [← e]; exact hA)
  first
    | simp [h1, h2]
    | (simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]; exact ⟨h1, h2⟩)

/-- An assignments-only body is an assignments-and-registers body. -/
theorem seqOk_of_assigns {body : List Stmt} (h : body.all Sparkle.IR.RegDedup.isAssign = true) :
    body.all seqStmtOk = true := by
  rw [List.all_eq_true] at h ⊢
  intro st hst
  have hs := h st hst
  cases st with
  | assign l r => first | rfl | simp [seqStmtOk]
  | _ => simp [Sparkle.IR.RegDedup.isAssign] at hs

/-- **A gate child's full-entry facts give the general closing's
seq-child interface** (`ChildIfaceG`), with the one output `out`. -/
theorem ChildFull.toG {c : Name} {bs : List (Name × MixedGateBinder)}
    {b : Sparkle.IR.AST.Module} {design : Design} (h : ChildFull c bs b design) :
    ChildIfaceG c ((bs.filter fun x => x.2 != .domain).length) ["out"] b design := by
  have hin : inPortsOf b = b.inputs := inPortsOf_of_alloc h.comb.inputAlloc
  obtain ⟨ty, hout⟩ := h.comb.output
  have hlen : b.inputs.length = (bs.filter fun x => x.2 != .domain).length :=
    (Tools.ShippingCallsGate.ChildFull.iface h).2.1
  refine ⟨h.name, h.design, ?_, ?_, ?_, ?_, ?_, seqOk_of_assigns h.comb.assigns⟩
  · rw [hin]
    exact hlen
  · rw [hin]
    exact h.comb.inputNames
  · first
      | (rw [hout]; rfl)
      | rw [hout]
      | simp [hout]
  · intro p hp
    rw [hout] at hp
    have e : p = { name := "out", ty := ty } := List.mem_singleton.mp hp
    subst e
    refine ⟨?_, ?_, ?_⟩
    · intro q hq hqe
      rw [hin] at hq
      have hq' : Allocated q.name := h.comb.inputAlloc q hq
      rw [hqe] at hq'
      exact not_alloc_out hq'
    · show "out" ≠ "clk"
      first | decide | simp
    · show "out" ≠ "rst"
      first | decide | simp
  · rw [hout]
    show (["out"] : List String).Nodup
    exact List.nodup_cons.mpr ⟨(fun hx => nomatch hx), List.nodup_nil⟩

/-- **A gate child's full-entry facts give `ChildIfaceP`**: its module name
`ofDecl c`, as many argument ports as non-domain binders, the output `out`,
no descendant (`names = []`). -/
theorem ChildFull.toP {c : Name} {bs : List (Name × MixedGateBinder)}
    {b : Sparkle.IR.AST.Module} {design : Design} (h : ChildFull c bs b design) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl c) ((bs.filter fun x => x.2 != .domain).length)
      ["out"] [] b design :=
  Tools.ShippingCallsKidsD.ChildIfaceD.toP
    (Tools.ShippingCallsKidsD.ChildIfaceG.toD (ChildFull.toG h)) (fun hx => nomatch hx)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A real child of a gate declaration has the general closing's
interface** — from its OWN run (`RealChild`), the declaration's reflection
(`entry`, moved to that run's contexts inside `childFull_of_real`) and the
gate's reading of the declaration (`old`, `peel`, `he`, `hb`, `hv`: what
`#gate_child c` leaves). -/
theorem gateChild_ifaceP_of_real {c : Name} {y : Res}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : Tools.ShippingUnifiedSource.SType} {e : Tools.ShippingUnifiedSource.Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      Tools.ShippingUnifiedSource.quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (h : RealChild mref cref c y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl c) ((bs.filter fun x => x.2 != .domain).length)
      ["out"] [] y.1 y.2 :=
  ChildFull.toP (Tools.ShippingCallsGate.childFull_of_real entry old peel he hb hv h)

/-- **The origin-based kid of a non-memory entry calling a gate declaration
has the interface** (whatever the entry's name: a declaration under a memory
placeholder name included). -/
theorem gateKidT_iface {o : Sparkle.Compiler.MachInstOrigin.InstOrigin} {c : Name} {y : Res}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : Tools.ShippingUnifiedSource.SType} {e : Tools.ShippingUnifiedSource.Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      Tools.ShippingUnifiedSource.quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (ho : o.child? = none) (h : Tools.ShippingInstTagged.KidT mref cref o c y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl c) ((bs.filter fun x => x.2 != .domain).length)
      ["out"] [] y.1 y.2 :=
  gateChild_ifaceP_of_real entry old peel he hb hv (Tools.ShippingInstTagged.KidT.real h ho)

end Tools.ShippingGateChildIfaceP

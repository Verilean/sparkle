import Tools.ShippingGen2Adapt
import Tools.ShippingGen2CombKid
set_option autoImplicit false

/-! # G-ONEOUT output selection: `CallField` (scripts/gen2/CALLFIELD_FREEZE.md §2)

`CallField` (Tools/ShippingGen2Defs.lean) and its two selection lemmas `callField_group`/`callField_one`
(Tools/ShippingGen2Connect.lean, next to `pkgBsC`; available here through the import) choose the callee output a
parent's call reads. This file adds:
* `CallDecOld` (the `CallDec` text at c7948139, verbatim, renamed) and the group adapters `callDec_group_old` /
  `callDecOld_group` (under `instFields ≠ []`);
* the route-aware per-call residues `HPointG`/`CallOutG` (`HPointAt`/`CallFactF` with the name conjunct replaced by
  `CallField`), the four group adapters to the old texts, and the Gen2 producer `callDec_of_hPointG_at`;
* the one-output consumer data `OneOutCall`, `oneOutCall_of_callDec` (under `instFields = []`) and the run-level
  output shape `oneOut_outputs`.
`HPointAt` (QuadHPoint.lean), `CallFactF` (QuadCalls.lean) and `SeqFactsRN` (CallsLinkedTNR.lean) are NOT changed.
No sorry / axiom / native_decide. -/
namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingQuadComposed (GenFacts)
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingMachineCallsLinkedT (valsOf MemFacts)
open Tools.ShippingMachineChild (InRange boolsOf bitsOf)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain

open Tools.ShippingQuadCalls (CallFactF)
open Tools.ShippingQuadHPoint (HPointAt)

variable {ι : Type} {dom : ι → DomainConfig}

/-! ## 2.2 The old text and the group adapter -/

/-- `CallDec` as it was at c7948139 (Defs:95-105), verbatim, renamed: the name conjunct
`o.name = p.d.shape.instFields.getD k ""`. -/
def CallDecOld (p q : Pkg ι dom) (k : Nat) : Prop :=
  (p.d.shape.instOrigins.getD k .ord).child? = none ∧
  ∃ args, (p.d.shape.insts.map (·.2.1))[k]? = some args ∧
    args.length = q.ports.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      (∀ r (hr : r < args.length), args[r] < p.d.ls.length ∧ ∃ g, (p.lsrc i bools bits)[args[r]]? = some g) ∧
      (∀ τ, InRange (valsOf (p.lsrc i bools bits) args τ) q.ports) ∧
      ∃ (k' : Nat) (o : OutField) (f : Nat → Nat), q.d.shape.layout.outs[k']? = some o ∧ o.name = p.d.shape.instFields.getD k "" ∧
        (q.S i (valsOf (p.lsrc i bools bits) args))[k']? = some f ∧
        ∀ τ, posEnc (fun r => (p.extBS i bools bits r).val τ) (fun r n => (p.extS i bools bits r n).val τ)
          (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

theorem callDec_group_old {p q : Pkg ι dom} {k : Nat} (hG : p.d.shape.instFields ≠ []) :
    CallDec p q k → CallDecOld p q k := by
  rintro ⟨hnone, args, hargs, hlen, hall⟩
  refine ⟨hnone, args, hargs, hlen, fun i bools bits => ?_⟩
  obtain ⟨h4, h5, k', o, f, ho, hcf, hf, hpos⟩ := hall i bools bits
  exact ⟨h4, h5, k', o, f, ho, (callField_group (q := q) (k := k) (o := o) hG).mp hcf, hf, hpos⟩

theorem callDecOld_group {p q : Pkg ι dom} {k : Nat} (hG : p.d.shape.instFields ≠ []) :
    CallDecOld p q k → CallDec p q k := by
  rintro ⟨hnone, args, hargs, hlen, hall⟩
  refine ⟨hnone, args, hargs, hlen, fun i bools bits => ?_⟩
  obtain ⟨h4, h5, k', o, f, ho, hon, hf, hpos⟩ := hall i bools bits
  exact ⟨h4, h5, k', o, f, ho, (callField_group (q := q) (k := k) (o := o) hG).mpr hon, hf, hpos⟩

/-! ## 2.4 Route-aware per-call residue (shares `CallField`) -/

/-- `HPointAt` at the instantiation of the adapters (Adapt.lean:169), with the name conjunct replaced by
`CallField p q k o`. `q` is a parameter: the one-output branch of `CallField` reads `q.d.shape.layout.outs`. -/
def HPointG (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (hk : k < p.d.shape.insts.length),
    ∃ (A : Nat → Signal (dom i) Bool) (B : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      boolsOf (D := dom i) (pkgBsC P (p.d.shape.insts[k]).1) (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1) = A ∧
      bitsOf (D := dom i) (pkgBsC P (p.d.shape.insts[k]).1) (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1) = B ∧
      ∃ (k' : Nat) (o : OutField) (f : Nat → Nat),
        (pkgOutsC P (p.d.shape.insts[k]).1)[k']? = some o ∧ CallField p q k o ∧
        (pkgSrc P i (p.d.shape.insts[k]).1 A B)[k']? = some f ∧
        ∀ τ, posEnc (fun r => (p.extBS i bools bits r).val τ) (fun r n => (p.extS i bools bits r n).val τ)
          (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

/-- The per-call body of `CallFactF` (at `pkgOutsC P`, `pkgS P`), with the name conjunct replaced by `CallField`. -/
def CallOutG (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (hk : k < p.d.shape.insts.length),
    ∃ (k' : Nat) (o : OutField) (f : Nat → Nat),
      (pkgOutsC P (p.d.shape.insts[k]).1)[k']? = some o ∧ CallField p q k o ∧
      (pkgS P i (p.d.shape.insts[k]).1 (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1))[k']? = some f ∧
      ∀ τ, posEnc (fun r => (p.extBS i bools bits r).val τ) (fun r n => (p.extS i bools bits r n).val τ)
        (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

/-- Group adapter: `HPointG` gives the old `HPointAt` (every `q`; no `hP` needed). -/
theorem hPointAt_of_hPointG_group {P : Pkgs ι dom} {p q : Pkg ι dom} {k : Nat} (hG : p.d.shape.instFields ≠ []) :
    HPointG P p q k → HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P) (pkgSrc P) k := by
  intro h i bools bits hk
  obtain ⟨A, B, hA, hB, k', o, f, ho, hcf, hf, hpos⟩ := h i bools bits hk
  exact ⟨A, B, hA, hB, k', o, f, ho, (callField_group (q := q) (k := k) (o := o) hG).mp hcf, hf, hpos⟩

/-- Group adapter: the old `HPointAt` gives `HPointG` (for every `q`). -/
theorem hPointG_of_hPointAt_group {P : Pkgs ι dom} {p q : Pkg ι dom} {k : Nat} (hG : p.d.shape.instFields ≠ []) :
    HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P) (pkgSrc P) k → HPointG P p q k := by
  intro h i bools bits hk
  obtain ⟨A, B, hA, hB, k', o, f, ho, hon, hf, hpos⟩ := h i bools bits hk
  exact ⟨A, B, hA, hB, k', o, f, ho, (callField_group (q := q) (k := k) (o := o) hG).mpr hon, hf, hpos⟩

/-- Group adapter: one `CallOutG` per call gives the old `CallFactF`. -/
theorem callFactF_of_callOutG_group {P : Pkgs ι dom} {p : Pkg ι dom} (hG : p.d.shape.instFields ≠ [])
    (h : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, CallOutG P p q k) :
    CallFactF p.d p.kD p.lsrc p.extS p.extBS (pkgOutsC P) (fun i => pkgS P i) := by
  intro i bools bits k hk
  obtain ⟨q, hq⟩ := h k hk
  obtain ⟨k', o, f, ho, hcf, hf, hpos⟩ := hq i bools bits hk
  exact ⟨k', o, f, ho, (callField_group (q := q) (k := k) (o := o) hG).mp hcf, hf, hpos⟩

/-- Group adapter: the old `CallFactF` gives `CallOutG` at every call (for every `q`). -/
theorem callOutG_of_callFactF_group {P : Pkgs ι dom} {p q : Pkg ι dom} (hG : p.d.shape.instFields ≠ [])
    (hF : CallFactF p.d p.kD p.lsrc p.extS p.extBS (pkgOutsC P) (fun i => pkgS P i)) (k : Nat) : CallOutG P p q k := by
  intro i bools bits hk
  obtain ⟨k', o, f, ho, hon, hf, hpos⟩ := hF i bools bits k hk
  exact ⟨k', o, f, ho, (callField_group (q := q) (k := k) (o := o) hG).mpr hon, hf, hpos⟩

/-- **The Gen2 producer for both routes**: `callDec_of_hPointAt_at` (Adapt.lean) with `hH : HPointG P p q k` and no
`hG`; `CallField` passes through unchanged. -/
theorem callDec_of_hPointG_at (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hP : P (p.d.shape.insts[k]).1 = some q)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hH : HPointG P p q k)
    (hok : p.d.ok = true) (hco : p.d.callsOk p.kD = true)
    (hslots : p.d.ss.length = p.d.shape.layout.slots.length)
    (hargsK : callArgsOkAt p.d p.kD k q.portWidths = true)
    (hlenK : (p.d.shape.insts[k]).2.1.length = q.ports.length) :
    CallDec p q k := by
  refine ⟨hnone, (p.d.shape.insts[k]).2.1, by simp [hk], hlenK, ?_⟩
  intro i bools bits
  have hl := Pkg.lsrc_hl p i bools bits
  refine ⟨?_, call_inRange_at p q k hk hok hco hslots hargsK hlenK i bools bits, ?_⟩
  · intro r hr
    have hlt := callsOk_argsLets p.d p.kD hco k hk r hr
    refine ⟨hlt, ?_⟩
    obtain ⟨v, hv, -⟩ := hl _ _ (List.getElem?_eq_getElem hlt)
    exact ⟨v, hv⟩
  · obtain ⟨A, B, hA, hB, k', o, f, ho, hcf, hf, hpos⟩ := hH i bools bits hk
    refine ⟨k', o, f, ?_, hcf, ?_, hpos⟩
    · simpa [pkgOutsC, hP] using ho
    · have hS := pkgS_dispatch P i (p.d.shape.insts[k]).1 (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1)
      rw [hA, hB] at hS
      have hS' : q.S i (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1) =
          pkgSrc P i (p.d.shape.insts[k]).1 A B := by
        rw [← hS]; simp [pkgS, hP]
      rw [hS']; exact hf

/-! ## 2.5 One-output consumer data -/

/-- What a one-output parent's call `k` gives its consumer: `CallDec`'s non-run conjuncts with the output index fixed
to `0`, the callee's single layout output `o`, and a source observation at `0` for every input value list. `o` sits
inside `∀ i`, as in `CallDec` (no `Nonempty ι`). -/
def OneOutCall (p q : Pkg ι dom) (k : Nat) : Prop :=
  (p.d.shape.instOrigins.getD k .ord).child? = none ∧
  ∃ args, (p.d.shape.insts.map (·.2.1))[k]? = some args ∧
    args.length = q.ports.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      (∀ r (hr : r < args.length), args[r] < p.d.ls.length ∧ ∃ g, (p.lsrc i bools bits)[args[r]]? = some g) ∧
      (∀ τ, InRange (valsOf (p.lsrc i bools bits) args τ) q.ports) ∧
      ∃ (o : OutField), q.d.shape.layout.outs = [o] ∧
        (∀ v : List Nat, ∃ g, (q.S i (fun _ => v))[0]? = some g) ∧
        ∃ f : Nat → Nat, (q.S i (valsOf (p.lsrc i bools bits) args))[0]? = some f ∧
          ∀ τ, posEnc (fun r => (p.extBS i bools bits r).val τ) (fun r n => (p.extS i bools bits r n).val τ)
            (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

theorem oneOutCall_of_callDec {p q : Pkg ι dom} {k : Nat} (h1 : p.d.shape.instFields = []) :
    CallDec p q k → OneOutCall p q k := by
  rintro ⟨hnone, args, hargs, hlen, hall⟩
  refine ⟨hnone, args, hargs, hlen, fun i bools bits => ?_⟩
  obtain ⟨h4, h5, k', o, f, ho, hcf, hf, hpos⟩ := hall i bools bits
  have hsing : q.d.shape.layout.outs = [o] := (callField_one (q := q) (k := k) (o := o) h1).mp hcf
  have hk0 : k' = 0 := by
    rw [hsing] at ho
    rcases k' with _ | j
    · rfl
    · simp at ho
  subst hk0
  refine ⟨h4, h5, o, hsing, ?_, f, hf, hpos⟩
  intro v
  have hg := Pkg.src_get q i (boolsOf (D := dom i) (q.d.bsIn.take q.kD) (fun _ => v))
    (bitsOf (D := dom i) (q.d.bsIn.take q.kD) (fun _ => v)) 0 o (by simp [hsing])
  exact hg

/-- **The run-level output shape** of a one-output child run (the first conjunct of either branch of `ChildRunN`).
It gives the OUTPUT SHAPE only; it does not select the sequential or combinational branch. -/
theorem oneOut_outputs {children : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn : Design} {n : Nat}
    {mc : Sparkle.IR.AST.Module} {bsC : List (Name × MixedGateBinder)} {o : OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)} :
    ChildRunN children dsn n mc bsC [o] S → mc.outputs = [({ name := o.name, ty := o.ty } : Port)] := by
  intro h
  rcases h with h | h
  · first | exact h.1 | simpa using h.1
  · first | exact h.1 | simpa using h.1

end Tools.ShippingGen2

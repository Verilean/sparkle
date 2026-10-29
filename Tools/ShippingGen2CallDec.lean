import Tools.ShippingGen2Connect
import Tools.ShippingQuadHPoint
set_option autoImplicit false

/-! # Gen2 G-CALLDEC probe: the generic reduction and the conditional package bridge
(scripts/gen2/CALLDEC_PROBE_FREEZE.md §2, §4 (ii); approved freeze 16c6ca4b)

* `callDec_of_callFactF`: `CallDec p q k` for one ordinary call from `CallFactF` of `p` (EVERY call: a stronger
  sufficient input), `p`'s data and the call/port tables. The arity, the argument bounds and the range are derived.
* `callFactF_of_hPointAt_pkg`: `CallFactF` of `p` from `HPointAt` of every call (the complete per-call statement,
  output equation included) and the dispatch equation `pkgS`/`pkgSrc` (proved here). Conditional on `HPointAt`.
* `genFacts_restrict`: a `GenFacts` at `(DomainConfig, id)` restricted to `(Unit, fun _ => D₀)`.
Nothing here supplies `CallFactF` or `HPointAt` generically. -/
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

open Tools.ShippingQuadCalls (CallFactF call_inRange ok_bsIn_length letObsB_hl)
open Tools.ShippingQuadHPoint (HPointAt callFactF_of_hPointAt)
open Tools.ShippingPortsMatchRaw (callArgsOk)
open Tools.ShippingSeqParentLemmas (HCausalOf)

variable {ι : Type} {dom : ι → DomainConfig}

/-- `callsOk`'s first conjunct (as `c_callsOk_nIn`, Tests/Compiler/C4ComposedTest.lean:124). -/
theorem callsOk_nIn (d : MachineData) (n : Nat) (h : d.callsOk n = true) : n + d.shape.insts.length = d.nIn := by
  unfold Tools.ShippingMachineAuto.MachineData.callsOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, -⟩, -⟩, -⟩ := h
  exact h1

/-- `callsOk`'s second conjunct: every call argument is a let index. -/
theorem callsOk_argsLets (d : MachineData) (n : Nat) (h : d.callsOk n = true) (k : Nat)
    (hk : k < d.shape.insts.length) (r : Nat) (hr : r < (d.shape.insts[k]).2.1.length) :
    (d.shape.insts[k]).2.1[r] < d.ls.length := by
  unfold Tools.ShippingMachineAuto.MachineData.callsOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨-, h2⟩, -⟩, -⟩ := h
  exact h2 _ (List.getElem_mem hk) _ (List.getElem_mem hr)

/-- **The generic reduction** (freeze §2, exact signature). -/
theorem callDec_of_callFactF (P : Pkgs ι dom) (p q : SrcPkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hP : P (p.d.shape.insts[k]).1 = some q)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hF : CallFactF p.d p.kD p.lsrc p.extS p.extBS (pkgOutsC P) (fun i => pkgS P i))
    (hok : p.d.ok = true) (hco : p.d.callsOk p.kD = true)
    (hslots : p.d.ss.length = p.d.shape.layout.slots.length)
    (widths : Nat → List Nat) (hargs : callArgsOk p.d p.kD widths = true)
    (hw : ∀ (k : Nat) (hk : k < p.d.shape.insts.length), widths k =
      ((pkgBsC P (p.d.shape.insts[k]).1).filter fun b => b.2 != .domain).map fun b => (kindTy b.2).bitWidth)
    (hlen : ∀ (k : Nat) (hk : k < p.d.shape.insts.length), (p.d.shape.insts[k]).2.1.length =
      ((pkgBsC P (p.d.shape.insts[k]).1).filter fun b => b.2 != .domain).length) :
    CallDec p q k := by
  have hnIn := callsOk_nIn p.d p.kD hco
  have hbl := ok_bsIn_length p.d hok
  have hkD : p.kD ≤ p.d.bsIn.length := by omega
  have hIlen : (p.d.bsIn.drop p.kD).length = p.d.shape.insts.length := by
    simp only [List.length_drop]; omega
  have hB : pkgBsC P (p.d.shape.insts[k]).1 = q.d.bsIn.take q.kD := by simp [pkgBsC, hP]
  refine ⟨hnone, (p.d.shape.insts[k]).2.1, by simp [hk], ?_, ?_⟩
  · rw [hlen k hk, hB]; rfl
  · intro i bools bits
    have hl := @letObsB_hl p.d ι dom p.inh p.ρ p.inits p.body p.ext p.extB i bools bits
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      have hlt := callsOk_argsLets p.d p.kD hco k hk r hr
      refine ⟨hlt, ?_⟩
      obtain ⟨v, hv, -⟩ := hl _ _ (List.getElem?_eq_getElem hlt)
      exact ⟨v, hv⟩
    · intro τ
      have h := call_inRange p.d hok hkD hIlen hslots hco widths hargs (pkgBsC P) hw hlen
        (p.lsrc i bools bits) hl k hk τ
      rw [hB] at h
      exact h
    · obtain ⟨k', o, f, ho, hon, hf, hpos⟩ := hF i bools bits k hk
      refine ⟨k', o, f, ?_, hon, ?_, hpos⟩
      · simpa [pkgOutsC, hP] using ho
      · simpa [pkgS, hP] using hf

/-- The callee source of a package assignment, on decoded families. -/
noncomputable def pkgSrc (P : Pkgs ι dom) (i : ι) (c : Name) (A : Nat → Signal (dom i) Bool)
    (B : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) : List (Nat → Nat) :=
  ((P c).map fun q => q.src i A B).getD []

/-- The dispatch equation: `pkgS` is `pkgSrc` on the families decoded with `pkgBsC`. -/
theorem pkgS_dispatch (P : Pkgs ι dom) (i : ι) (c : Name) (vals : Nat → List Nat) :
    pkgS P i c vals = pkgSrc P i c (boolsOf (D := dom i) (pkgBsC P c) vals) (bitsOf (D := dom i) (pkgBsC P c) vals) := by
  unfold pkgS pkgSrc pkgBsC
  cases P c with
  | none => rfl
  | some q => rfl

/-- **The conditional package bridge** (freeze §4 (ii)): `CallFactF` of `p` from the COMPLETE `HPointAt` of every call
(decoded families, output field, source relation and output equation) and the proved dispatch equation. -/
theorem callFactF_of_hPointAt_pkg (P : Pkgs ι dom) (p : SrcPkg ι dom)
    (hH : ∀ k, k < p.d.shape.insts.length →
      HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P) (pkgSrc P) k) :
    CallFactF p.d p.kD p.lsrc p.extS p.extBS (pkgOutsC P) (fun i => pkgS P i) :=
  callFactF_of_hPointAt p.d p.kD dom (pkgBsC P) (pkgSrc P) (fun i c vals => pkgS_dispatch P i c vals) hH

/-- **Index restriction** (freeze §3, 2a): a `GenFacts` at `(DomainConfig, id)` restricted to `(Unit, fun _ => D₀)`. -/
theorem genFacts_restrict (d : MachineData) [Inhabited (HList (tys d.ss))] {ρ : DomainConfig → Type}
    {inits : HList (tys d.ss)}
    {body : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      RegList i (HList (tys d.ss)) (Circuit.SigList i (tys d.ss)) (tys d.ss) →
      Circuit i (Circuit.SigList i (tys d.ss)) (ρ i)}
    {obsR : (i : DomainConfig) → ρ i → List (Nat → Nat)}
    {ext : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal i (BitVec n)}
    {extB : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys d.ss)) → Nat → Signal i Bool}
    {src : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      List (Nat → Nat)}
    (D₀ : DomainConfig)
    (h : GenFacts d (fun i : DomainConfig => i) inits body obsR ext extB src) :
    @GenFacts d Unit (fun _ => D₀) (fun _ => ρ D₀) _ inits (fun _ => body D₀) (fun _ => obsR D₀)
      (fun _ => ext D₀) (fun _ => extB D₀) (fun _ => src D₀) :=
  ⟨h.ok, h.body_eq, h.init, fun _ bools bits S t => h.writes D₀ bools bits S t,
   fun _ bools bits S t => h.result D₀ bools bits S t, fun _ bools bits => h.source D₀ bools bits,
   fun _ bools bits S S' t hS => h.causal D₀ bools bits S S' t hS⟩

end Tools.ShippingGen2

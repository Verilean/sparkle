import Tools.ShippingGen2SrcPkg
import Tools.ShippingMachineSeqLinkedR
import Tools.ShippingServedRealATrace
import Tools.ShippingQuadCalls
set_option autoImplicit false

/-! # loop-pkg step 1: the loop-form package (scripts/gen2/LOOPPKG_FREEZE.md §2 (b), §5.2; approved for step 1)

* `machine_traceL_of_loop_causalRA_ranA`: `machine_traceL_of_loop_causalRA_ran` (Tools/ShippingMachineSeqLinkedR.lean:32) on
  the A-boundary: the same stream witness, with `machine_trace_lets_of_streamBRA_ranA`
  (Tools/ShippingServedRealATrace.lean:36) in place of `_streamBRA_ran`; it never uses `MachineRan`/`ServedReal`.
* `LoopFacts`: EXACTLY the premise list of `machine_trace_of_loop_causal` (Tools/ShippingMachineCausalCtx.lean:412-463);
  `hcausal` is a source-level causality obligation (not DATA, not refl), the others are the generator's refl checks.
* `SrcPkgL`: the loop-form package (its `Inhabited` instances are a field, applied explicitly with `@`).
* `genTraceL`: the wrapper (as `genTrace`, Tools/ShippingQuadComposed.lean:156-182).
* `letObsLoop_hl`: the statement of `letObsB_hl` (QuadCalls.lean:195) over `letObsLoop`. -/
namespace Tools.ShippingGen2Loop
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness Sparkle.IR.AST
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain Tools.ShippingMachineTraceX Tools.ShippingServedRealA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA Tools.ShippingChildFrontCP
open Tools.ShippingMachineCausal
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 2000000 in
theorem machine_traceL_of_loop_causalRA_ranA {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) {α : ι → Type} [∀ i, Inhabited (α i)] {ρ : ι → Type}
    (σ : (i : ι) → α i → HList (tys d.ss))
    (inits : HList (tys d.ss))
    (f : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Signal (dom i) (α i))
    (res : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Signal (dom i) (α i) → ρ i)
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Nat → Signal (dom i) Bool)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (h0 : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (l : Signal (dom i) (α i)),
      σ i ((f i bools bits l).val 0) = inits)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (l : Signal (dom i) (α i))
      (t : Nat),
      σ i ((f i bools bits l).val (t + 1)) =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l)
            (ext i bools bits l) t (σ i (l.val t))).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l)
            (ext i bools bits l) t (σ i (l.val t))).v (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (L : Signal (dom i) (α i))
      (t : Nat),
      (obsR i (res i bools bits L)).map (fun g => g t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits L)
            (ext i bools bits L) t (σ i (L.val t))).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits L)
            (ext i bools bits L) t (σ i (L.val t))).v (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (res i bools bits (Signal.loop (f i bools bits))))
    (hcausal : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (l l' : Signal (dom i) (α i)) (t : Nat), (∀ c, c ≤ t → l.val c = l'.val c) →
      (∀ p w, (ext i bools bits l p w).val t = (ext i bools bits l' p w).val t) ∧
      (∀ p, (extB i bools bits l p).val t = (extB i bools bits l' p).val t))
    (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepC O) (hA : AdmCtx O.quiet mctx cctx) {n : Nat}
    (htr : ∀ (tenv : Lean.Environment) e hint top named, KeepsCP mctx mref cctx cref (JQC O n)
      (translateExprToWire tenv e hint top named))
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (ran : MachineRunJQC O mctx cctx n declName d.shape m design) :
    MachineTraceLBX (ServedRealA O declName d.shape m design) declName d m design dom src
      (fun i bools bits => ext i bools bits (Signal.loop (f i bools bits)))
      (fun i bools bits => extB i bools bits (Signal.loop (f i bools bits)))
      (letObsLoop d dom σ f ext extB) := by
  refine Tools.ShippingServedRealATrace.machine_trace_lets_of_streamBRA_ranA O hB hA htr d dom inits src
    (letObsLoop d dom σ f ext extB) ok hbody hinit _ _ ?_ ran
  intro i bools bits
  refine ⟨fun t => σ i ((Signal.loop (f i bools bits)).val t), ?_, ?_, ?_, ?_⟩
  · show σ i (Signal.loopGo (f i bools bits) 0) = inits
    rw [Signal.loopGo_eq]
    exact h0 i bools bits _
  · intro t
    show σ i (Signal.loopGo (f i bools bits) (t + 1)) = _
    rw [Signal.loopGo_eq, writes]
    have hag : ∀ c, c ≤ t →
        (⟨fun s => if s < t + 1 then Signal.loopGo (f i bools bits) s else default⟩ :
          Signal (dom i) (α i)).val c = (Signal.loop (f i bools bits)).val c := by
      intro c hc
      show (if c < t + 1 then _ else _) = Signal.loopGo (f i bools bits) c
      rw [if_pos (by omega)]
    obtain ⟨hv, hb⟩ := hcausal i bools bits _ _ t hag
    rw [hag t (Nat.le_refl t),
      typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls _ _ _ _ t _ hb hv]
  · intro j
    rw [hsrc i bools bits]
    exact hres i bools bits _ j
  · intro j q g l hg hl
    simp only [letObsLoop, List.getElem?_map, hl, Option.map_some, Option.some.injEq] at hg
    rw [← hg]


/-- **`LoopFacts`**: the premises of `machine_trace_of_loop_causal` as one structure (fields copied verbatim). -/
structure LoopFacts (d : MachineData) {ι : Type} (dom : ι → DomainConfig) {α : ι → Type} [∀ i, Inhabited (α i)]
    {ρ : ι → Type}
    (σ : (i : ι) → α i → HList (tys d.ss))
    (inits : HList (tys d.ss))
    (f : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Signal (dom i) (α i))
    (res : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Signal (dom i) (α i) → ρ i)
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Nat → Signal (dom i) Bool)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)) : Prop where
  ok : d.ok = true
  hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed
  hinit : d.initOk inits = true
  h0 : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (l : Signal (dom i) (α i)),
      σ i ((f i bools bits l).val 0) = inits
  writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (l : Signal (dom i) (α i))
      (t : Nat),
      σ i ((f i bools bits l).val (t + 1)) =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l)
            (ext i bools bits l) t (σ i (l.val t))).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l)
            (ext i bools bits l) t (σ i (l.val t))).v (d.vpos j) w) d.nexts
  hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (L : Signal (dom i) (α i))
      (t : Nat),
      (obsR i (res i bools bits L)).map (fun g => g t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits L)
            (ext i bools bits L) t (σ i (L.val t))).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits L)
            (ext i bools bits L) t (σ i (L.val t))).v (d.vpos j) w) o.2)
  hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (res i bools bits (Signal.loop (f i bools bits)))
  hcausal : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (l l' : Signal (dom i) (α i)) (t : Nat), (∀ c, c ≤ t → l.val c = l'.val c) →
      (∀ p w, (ext i bools bits l p w).val t = (ext i bools bits l' p w).val t) ∧
      (∀ p, (extB i bools bits l p).val t = (extB i bools bits l' p).val t)

/-- **The loop-form source package.** -/
structure SrcPkgL (ι : Type) (dom : ι → DomainConfig) where
  decl : Name
  d : MachineData
  kD : Nat
  α : ι → Type
  inh : ∀ i, Inhabited (α i)
  ρ : ι → Type
  σ : (i : ι) → α i → HList (tys d.ss)
  inits : HList (tys d.ss)
  f : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → Signal (dom i) (α i)
  res : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → ρ i
  obsR : (i : ι) → ρ i → List (Nat → Nat)
  ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)
  extB : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → Nat → Signal (dom i) Bool
  src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    List (Nat → Nat)
  facts : @LoopFacts d ι dom α inh ρ σ inits f res obsR ext extB src

variable {ι : Type} {dom : ι → DomainConfig}

/-- The loop package's `ext`/`extB` along its own loop, and its `let` observations. -/
def SrcPkgL.extS (p : SrcPkgL ι dom) := fun i bools bits =>
  p.ext i bools bits (@Signal.loop _ _ (p.inh i) (p.f i bools bits))
def SrcPkgL.extBS (p : SrcPkgL ι dom) := fun i bools bits =>
  p.extB i bools bits (@Signal.loop _ _ (p.inh i) (p.f i bools bits))
def SrcPkgL.lsrc (p : SrcPkgL ι dom) :=
  @letObsLoop p.d ι dom p.α p.inh p.σ p.f p.ext p.extB

/-- **`genTraceL`** (exact A-boundary form, as `genTrace`). -/
theorem genTraceL (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (p : SrcPkgL ι dom) {D₀ : Nat} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (ran : MachineRunJQC O mctx cctx (D₀ + 1) p.decl p.d.shape m design) :
    MachineTraceLBX (ServedRealA O p.decl p.d.shape m design) p.decl p.d m design dom p.src p.extS p.extBS p.lsrc := by
  letI := p.inh
  exact @machine_traceL_of_loop_causalRA_ranA mctx mref cctx cref p.decl p.d ι dom p.α p.inh p.ρ p.σ p.inits p.f p.res p.obsR
    p.ext p.extB p.src p.facts.ok p.facts.hbody p.facts.hinit p.facts.h0 p.facts.writes p.facts.hres p.facts.hsrc
    p.facts.hcausal O (bodyStepC_of_tele O T) hA (D₀ + 1) (htr_of_tele O hA T D₀) m design ran

/-- **`letObsLoop_hl`**: the loop package's `let` observations are bounded by the sort of the `let`. -/
theorem letObsLoop_hl (p : SrcPkgL ι dom) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    ∀ (a : Nat) (l : Σ s : SType, Term s), p.d.ls[a]? = some l →
      ∃ v, (p.lsrc i bools bits)[a]? = some v ∧ ∀ τ, v τ < 2 ^ l.1.width := by
  intro a l hl
  unfold SrcPkgL.lsrc letObsLoop
  rw [List.getElem?_map, hl]
  exact ⟨_, rfl, fun τ => Tools.ShippingQuadCalls.enc_lt l.1 _⟩

end Tools.ShippingGen2Loop

import Tools.ShippingServedRealATrace
import Tools.ShippingMachineSeqLinkedR
import Tools.ShippingMachineDepthRunRA
-- BUILT (unit SR3h): s2 exit 0 (this file). Used by Tests.Compiler.ParentSeqComposedATest (c14 exit 0).
-- SCOPE (binding): `machine_traceL_of_data_causalRA_ranA` = `machine_traceL_of_data_causalRA_ran` (SeqLinkedR) with `MachineRan`/`ServedReal`
-- replaced by `MachineRunJQC`/`ServedRealA O` (the proof is the old one with the stream lemma `machine_trace_lets_of_streamBRA_ranA`).
-- Premises beyond the old ones: `O`, `BodyStepC O`, `AdmCtx`, the restricted translator `htr`. A history of past synthesis results; not runtime fit.
namespace Tools.ShippingParentSeqComposedA
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineAuto Tools.ShippingMachineFuse
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineCausal
open Tools.ShippingMachineTraceX (MachineTraceLBX)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildDepthC Tools.ShippingChildBndCore Tools.ShippingChildTranslateA

set_option maxHeartbeats 2000000 in
/-- `machine_traceL_of_data_causalRA_ran` on the new boundary (`ServedRealA O`, `MachineRunJQC`). -/
theorem machine_traceL_of_data_causalRA_ranA {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) [Inhabited (HList (tys d.ss))] {ρ : ι → Type}
    (inits : HList (tys d.ss))
    (body : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → Nat → Signal (dom i) Bool)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      valsAt (tys d.ss) (body i bools bits
          (mkRegList S (tys d.ss) (fun s => s) (fun f => f)) (mkHolds (tys d.ss) S)).snd t =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).v (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (obsR i (body i bools bits (mkRegList S (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).v (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i
        (body i bools bits
          (mkRegList (stateLoop inits (body i bools bits)) (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) (stateLoop inits (body i bools bits)))).fst)
    (hcausal : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S S' : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (∀ c, c ≤ t → S.val c = S'.val c) →
      (∀ p w, (ext i bools bits S p w).val t = (ext i bools bits S' p w).val t) ∧
      (∀ p, (extB i bools bits S p).val t = (extB i bools bits S' p).val t))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepC O) (hA : AdmCtx O.quiet mctx cctx) {n : Nat}
    (htr : ∀ (tenv : Lean.Environment) e hint top named, KeepsCP mctx mref cctx cref (JQC O n)
      (translateExprToWire tenv e hint top named))
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (ran : Tools.ShippingServedRealA.MachineRunJQC O mctx cctx n declName d.shape m design) :
    MachineTraceLBX (Tools.ShippingServedRealA.ServedRealA O declName d.shape m design) declName d m design dom src
      (fun i bools bits => ext i bools bits (stateLoop inits (body i bools bits)))
      (fun i bools bits => extB i bools bits (stateLoop inits (body i bools bits)))
      (letObsB d dom inits body ext extB) := by
  refine Tools.ShippingServedRealATrace.machine_trace_lets_of_streamBRA_ranA O hB hA htr d dom inits src (letObsB d dom inits body ext extB) ok hbody
    hinit _ _ ?_ ran
  intro i bools bits
  have hW : ∀ (l l' : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (∀ c, c ≤ t → l.val c = l'.val c) →
      valsAt (tys d.ss) (writesOn (body i bools bits) l) t =
        valsAt (tys d.ss) (writesOn (body i bools bits) l') t := by
    intro l l' t h
    show valsAt (tys d.ss) (body i bools bits (mkRegList l (tys d.ss) (fun s => s) (fun f => f))
        (mkHolds (tys d.ss) l)).snd t =
      valsAt (tys d.ss) (body i bools bits (mkRegList l' (tys d.ss) (fun s => s) (fun f => f))
        (mkHolds (tys d.ss) l')).snd t
    obtain ⟨hv, hb⟩ := hcausal i bools bits l l' t h
    rw [writes i bools bits l t, writes i bools bits l' t, h t (Nat.le_refl t),
      typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l) (extB i bools bits l')
        (ext i bools bits l) (ext i bools bits l') t (l'.val t) hb hv]
  obtain ⟨h0, hs⟩ := circuit_state_causal inits (body i bools bits) hW
  refine ⟨fun t => (stateLoop inits (body i bools bits)).val t, h0, ?_, ?_, ?_⟩
  · intro t
    show (stateLoop inits (body i bools bits)).val (t + 1) = _
    rw [hs t]
    exact writes i bools bits _ t
  · intro j
    rw [hsrc i bools bits]
    exact hres i bools bits (stateLoop inits (body i bools bits)) j
  · intro j q g l hg hl
    simp only [letObsB, List.getElem?_map, hl, Option.map_some, Option.some.injEq] at hg
    rw [← hg]


end Tools.ShippingParentSeqComposedA

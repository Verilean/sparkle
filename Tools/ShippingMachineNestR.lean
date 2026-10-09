import Tools.ShippingMachineNest
import Tools.ShippingMachineTraceX

/-! `machine_traceL_of_nested_ext` carrying `ServedReal` (under `ChildSynthIs`): the proof is the
head's own, the stream lemma replaced (`machine_trace_lets_of_streamBR`). -/
namespace Tools.ShippingMachineNest
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineAuto Tools.ShippingMachineFuse
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineTraceX (MachineTraceLBX ServedReal machine_trace_lets_of_streamBR)

set_option maxHeartbeats 4000000 in
/-- `machine_traceL_of_nested_ext` carrying `ServedReal`. -/
theorem machine_traceL_of_nested_extR {declName : Name} (d : MachineData)
    (dom : ι → DomainConfig) (ss₂ : List SType) [Inhabited (HList (tys ss₂))]
    (l : List (InnerT ι dom ss₂)) (hss : ss₂ ++ sss l = d.ss) {ρ : ι → Type}
    (inits : HList (tys ss₂))
    (body : (i : ι) → (bools : Nat → Signal (dom i) Bool) →
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys ss₂)) (Circuit.SigList (dom i) (tys ss₂)) (tys ss₂) →
      HList (ρs (ats l i bools bits)) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys ss₂)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (bools : Nat → Signal (dom i) Bool) →
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys ss₂)) → Sigs (ats l i bools bits) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk (castSS hss (happendT ss₂ (sss l) inits (initsT l))) = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Sigs (ats l i bools bits)) (t : Nat),
      castSS hss (fstate i bools bits l
        (valsAt (tys ss₂) (body i bools bits (regsOf (tys ss₂) S)
          (resultsOn (regsOf (tys ss₂) S) (ats l i bools bits) Ss) (mkHolds (tys ss₂) S)).snd t)
        (innerValsAt (ats l i bools bits)
          (innerWrites (regsOf (tys ss₂) S) (ats l i bools bits) Ss) t)) =
      evalTerms
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
          (castSS hss (fstate i bools bits l (S.val t) (valsOf (ats l i bools bits) Ss t)))).b
          (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
          (castSS hss (fstate i bools bits l (S.val t) (valsOf (ats l i bools bits) Ss t)))).v
          (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Sigs (ats l i bools bits)) (t : Nat),
      (obsR i (body i bools bits (regsOf (tys ss₂) S)
          (resultsOn (regsOf (tys ss₂) S) (ats l i bools bits) Ss) (mkHolds (tys ss₂) S)).fst).map
          (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (fstate i bools bits l (S.val t) (valsOf (ats l i bools bits) Ss t)))).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (fstate i bools bits l (S.val t) (valsOf (ats l i bools bits) Ss t)))).v
            (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (resOn (fusedBody (ats l i bools bits) (body i bools bits))
        (stateLoop inits (fusedBody (ats l i bools bits) (body i bools bits)))))
    (hext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Sigs (ats l i bools bits)) (t p w : Nat),
      (ext i bools bits S Ss p w).val t =
        (ext i bools bits ⟨fun _ => S.val t⟩
          (constOf (ats l i bools bits) (valsOf (ats l i bools bits) Ss t)) p w).val t)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape)
    (hsyn : Tools.ShippingChildSynth.ChildSynthIs mctx mref cctx cref) :
    MachineTraceLBX (ServedReal mctx mref cctx cref declName d.shape m design) declName d m design dom src (fun i bools bits =>
      ext i bools bits (stateLoop inits (fusedBody (ats l i bools bits) (body i bools bits)))
        (innerLoops (regsOf (tys ss₂)
          (stateLoop inits (fusedBody (ats l i bools bits) (body i bools bits))))
          (ats l i bools bits)))
      (fun _ bools _ => bools)
      (letObsN d dom ss₂ l hss inits body ext) := by
  obtain ⟨shape, nIn, domE, bposL, vposL, vwL, ss, ls, outs, nexts⟩ := d
  simp only at hss
  subst hss
  refine machine_trace_lets_of_streamBR _ dom (happendT ss₂ (sss l) inits (initsT l)) src _ ok hbody
    hinit _ (fun _ bools _ => bools) ?_ hr entry closes hsyn
  intro i bools bits
  -- the recurrence functions, read off the terms, with the extension at the
  -- constant state signals: functions of the states' values
  let E : HList (tys ss₂) → HList (σs (ats l i bools bits)) → Nat → HList (tys (ss₂ ++ sss l)) :=
    fun a xs t => evalTerms
      (fun j => (typedVal nIn (fun j => bposL.getD j 0) (fun j => vposL.getD j 0) (ss₂ ++ sss l) ls
        bools (ext i bools bits ⟨fun _ => a⟩ (constOf (ats l i bools bits) xs)) t
        (fstate i bools bits l a xs)).b (bposL.getD j 0))
      (fun j w => (typedVal nIn (fun j => bposL.getD j 0) (fun j => vposL.getD j 0) (ss₂ ++ sss l) ls
        bools (ext i bools bits ⟨fun _ => a⟩ (constOf (ats l i bools bits) xs)) t
        (fstate i bools bits l a xs)).v (vposL.getD j 0) w) nexts
  have hw : ∀ (S : Signal (dom i) (HList (tys ss₂))) (Ss : Sigs (ats l i bools bits)) (t : Nat),
      fstate i bools bits l
        (valsAt (tys ss₂) (body i bools bits (regsOf (tys ss₂) S)
          (resultsOn (regsOf (tys ss₂) S) (ats l i bools bits) Ss) (mkHolds (tys ss₂) S)).snd t)
        (innerValsAt (ats l i bools bits)
          (innerWrites (regsOf (tys ss₂) S) (ats l i bools bits) Ss) t) =
      E (S.val t) (valsOf (ats l i bools bits) Ss t) t := by
    intro S Ss t
    have h := writes i bools bits S Ss t
    rw [typedVal_congr _ _ _ _ _ bools (ext i bools bits S Ss)
      (ext i bools bits ⟨fun _ => S.val t⟩
        (constOf (ats l i bools bits) (valsOf (ats l i bools bits) Ss t))) t _
      (fun p w => hext i bools bits S Ss t p w)] at h
    exact h
  have hG : OuterPointwise (ats l i bools bits) (body i bools bits)
      (fun a xs t => splitL ss₂ (sss l) (E a xs t)) := by
    intro S Ss t
    show _ = splitL ss₂ (sss l) (E (S.val t) (valsOf (ats l i bools bits) Ss t) t)
    rw [← hw S Ss t]
    unfold fstate
    rw [splitL_happendT]
  have hF : InnerPointwise (ats l i bools bits)
      (fun a xs t => unflat i bools bits l (splitR ss₂ (sss l) (E a xs t))) := by
    intro S Ss t
    show _ = unflat i bools bits l (splitR ss₂ (sss l) (E (S.val t) (valsOf (ats l i bools bits) Ss t) t))
    rw [← hw S Ss t]
    unfold fstate
    rw [splitR_happendT, unflat_flat]
  obtain ⟨h0, x0, hstep⟩ := fused_state inits (ats l i bools bits) (body i bools bits) _ hF _ hG
  simp only at x0 hstep
  refine ⟨fun t => fstate i bools bits l
    ((stateLoop inits (fusedBody (ats l i bools bits) (body i bools bits))).val t)
    (valsOf (ats l i bools bits) (innerLoops (regsOf (tys ss₂)
      (stateLoop inits (fusedBody (ats l i bools bits) (body i bools bits))))
      (ats l i bools bits)) t), ?_, ?_, ?_, ?_⟩
  · show fstate i bools bits l _ _ = _
    rw [h0, x0]
    unfold fstate
    rw [flat_initsOf]
  · intro t
    show fstate i bools bits l _ _ = _
    rw [(hstep t).1, (hstep t).2]
    unfold fstate
    rw [flat_unflat, happendT_split]
    show E _ _ t = _
    simp only [E]
    rw [typedVal_congr _ _ _ _ _ bools
      (ext i bools bits ⟨fun _ => (stateLoop inits (fusedBody (ats l i bools bits) (body i bools bits))).val t⟩
        (constOf (ats l i bools bits) (valsOf (ats l i bools bits)
          (innerLoops (regsOf (tys ss₂) (stateLoop inits (fusedBody (ats l i bools bits) (body i bools bits))))
            (ats l i bools bits)) t)))
      (ext i bools bits (stateLoop inits (fusedBody (ats l i bools bits) (body i bools bits)))
        (innerLoops (regsOf (tys ss₂) (stateLoop inits (fusedBody (ats l i bools bits) (body i bools bits))))
          (ats l i bools bits))) t _
      (fun p w => (hext i bools bits _ _ t p w).symm)]
    rfl
  · intro j
    rw [hsrc i bools bits, fusedBody_result]
    exact hres i bools bits _ _ j
  · intro j q g l' hg hl
    simp only [letObsN, List.getElem?_map, hl, Option.map_some, Option.some.injEq] at hg
    subst hg
    rfl

end Tools.ShippingMachineNest

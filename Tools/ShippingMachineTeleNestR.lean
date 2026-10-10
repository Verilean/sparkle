import Tools.ShippingMachineTeleNest
import Tools.ShippingMachineTraceX

/-! `machine_traceL_of_tele_ext` carrying `ServedReal` (under `ChildBnd`): the proof is the
head's own, the stream lemma replaced (`machine_trace_lets_of_streamBR`). -/
namespace Tools.ShippingMachineTeleNest
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineAuto Tools.ShippingMachineFuse
open Tools.ShippingMachineNest (happendT splitL splitR splitL_happendT splitR_happendT happendT_split castSS)
open Tools.ShippingMachineTele
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineTraceX (MachineTraceLBX ServedReal machine_trace_lets_of_streamBR)

set_option maxHeartbeats 4000000 in
/-- `machine_traceL_of_tele_ext` carrying `ServedReal`. -/
theorem machine_traceL_of_tele_extR {declName : Name} (d : MachineData)
    (dom : ι → DomainConfig) (ss₂ : List SType) [Inhabited (HList (tys ss₂))]
    (l : TeleT ι dom ss₂ (fun _ => [])) (hss : ss₂ ++ l.sss = d.ss) {ρ : ι → Type}
    (inits : HList (tys ss₂))
    (body : (i : ι) → (bools : Nat → Signal (dom i) Bool) →
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys ss₂)) (Circuit.SigList (dom i) (tys ss₂)) (tys ss₂) →
      HList (Tele.ρs (l.at i bools bits)) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys ss₂)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (bools : Nat → Signal (dom i) Bool) →
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys ss₂)) → Tele.Sigs (l.at i bools bits) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk (castSS hss (happendT ss₂ l.sss inits l.initsT)) = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t : Nat),
      castSS hss (l.fstate i bools bits
        (valsAt (tys ss₂) (body i bools bits (regsOf (tys ss₂) S)
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss) (mkHolds (tys ss₂) S)).snd t)
        (Tele.writesAt (regsOf (tys ss₂) S) (l.at i bools bits) () Ss t)) =
      evalTerms
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
          (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).b
          (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
          (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).v
          (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t : Nat),
      (obsR i (body i bools bits (regsOf (tys ss₂) S)
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss) (mkHolds (tys ss₂) S)).fst).map
          (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).v
            (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (resOn (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))
        (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits)))))
    (hext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t p w : Nat),
      (ext i bools bits S Ss p w).val t =
        (ext i bools bits ⟨fun _ => S.val t⟩
          (Tele.constOf (l.at i bools bits) (Tele.valsOf (l.at i bools bits) Ss t)) p w).val t)
    (hI : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)), Tele.InitOk (l.at i bools bits))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape)
    (hsyn : Tools.ShippingChildInv.ChildBnd mref cref w) :
    MachineTraceLBX (ServedReal mctx mref cctx cref declName d.shape m design) declName d m design dom src (fun i bools bits =>
      ext i bools bits (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits)))
        (Tele.loops (regsOf (tys ss₂)
          (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))))
          (l.at i bools bits) ()))
      (fun _ bools _ => bools)
      (letObsT d dom ss₂ l hss inits body ext) := by
  obtain ⟨shape, nIn, domE, bposL, vposL, vwL, ss, ls, outs, nexts⟩ := d
  simp only at hss
  subst hss
  refine machine_trace_lets_of_streamBR _ dom (happendT ss₂ l.sss inits l.initsT) src _ ok hbody
    hinit _ (fun _ bools _ => bools) ?_ hr entry closes hsyn
  intro i bools bits
  -- the recurrence functions, read off the terms, with the extension at the
  -- constant state signals: functions of the states' values
  let E : HList (tys ss₂) → HList (Tele.σs (l.at i bools bits)) → Nat → HList (tys (ss₂ ++ l.sss)) :=
    fun a xs t => evalTerms
      (fun j => (typedVal nIn (fun j => bposL.getD j 0) (fun j => vposL.getD j 0) (ss₂ ++ l.sss) ls
        bools (ext i bools bits ⟨fun _ => a⟩ (Tele.constOf (l.at i bools bits) xs)) t
        (l.fstate i bools bits a xs)).b (bposL.getD j 0))
      (fun j w => (typedVal nIn (fun j => bposL.getD j 0) (fun j => vposL.getD j 0) (ss₂ ++ l.sss) ls
        bools (ext i bools bits ⟨fun _ => a⟩ (Tele.constOf (l.at i bools bits) xs)) t
        (l.fstate i bools bits a xs)).v (vposL.getD j 0) w) nexts
  have hw : ∀ (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t : Nat),
      l.fstate i bools bits
        (valsAt (tys ss₂) (body i bools bits (regsOf (tys ss₂) S)
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss) (mkHolds (tys ss₂) S)).snd t)
        (Tele.writesAt (regsOf (tys ss₂) S) (l.at i bools bits) () Ss t) =
      E (S.val t) (Tele.valsOf (l.at i bools bits) Ss t) t := by
    intro S Ss t
    have h := writes i bools bits S Ss t
    rw [typedVal_congr _ _ _ _ _ bools (ext i bools bits S Ss)
      (ext i bools bits ⟨fun _ => S.val t⟩
        (Tele.constOf (l.at i bools bits) (Tele.valsOf (l.at i bools bits) Ss t))) t _
      (fun p w => hext i bools bits S Ss t p w)] at h
    exact h
  have hG : Tools.ShippingMachineTele.OuterPointwise (l.at i bools bits) (body i bools bits)
      (fun a xs t => splitL ss₂ l.sss (E a xs t)) := by
    intro S Ss t
    show _ = splitL ss₂ l.sss (E (S.val t) (Tele.valsOf (l.at i bools bits) Ss t) t)
    rw [← hw S Ss t]
    unfold TeleT.fstate
    rw [splitL_happendT]
  have hF : TelePointwise (l.at i bools bits)
      (fun a xs t => l.unflat i bools bits (splitR ss₂ l.sss (E a xs t))) := by
    intro S Ss t
    show _ = l.unflat i bools bits (splitR ss₂ l.sss (E (S.val t) (Tele.valsOf (l.at i bools bits) Ss t) t))
    rw [← hw S Ss t]
    unfold TeleT.fstate
    rw [splitR_happendT, TeleT.unflat_flat]
  obtain ⟨h0, x0, hstep⟩ := Tools.ShippingMachineTele.fused_state inits (l.at i bools bits) (body i bools bits) _ hF
      (hI i bools bits) _ hG
  simp only at x0 hstep
  refine ⟨fun t => l.fstate i bools bits
    ((stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))).val t)
    (Tele.valsOf (l.at i bools bits) (Tele.loops (regsOf (tys ss₂)
      (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))))
      (l.at i bools bits) ()) t), ?_, ?_, ?_, ?_⟩
  · show TeleT.fstate i bools bits l _ _ = _
    rw [h0, x0]
    unfold TeleT.fstate
    rw [TeleT.flat_initsOf]
  · intro t
    show TeleT.fstate i bools bits l _ _ = _
    rw [(hstep t).1, (hstep t).2]
    unfold TeleT.fstate
    rw [TeleT.flat_unflat, happendT_split]
    show E _ _ t = _
    simp only [E]
    rw [typedVal_congr _ _ _ _ _ bools
      (ext i bools bits ⟨fun _ => (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))).val t⟩
        (Tele.constOf (l.at i bools bits) (Tele.valsOf (l.at i bools bits)
          (Tele.loops (regsOf (tys ss₂) (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))))
            (l.at i bools bits) ()) t)))
      (ext i bools bits (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits)))
        (Tele.loops (regsOf (tys ss₂) (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))))
          (l.at i bools bits) ())) t _
      (fun p w => (hext i bools bits _ _ t p w).symm)]
    rfl
  · intro j
    rw [hsrc i bools bits, Tools.ShippingMachineTele.fusedBody_result]
    exact hres i bools bits _ _ j
  · intro j q g l' hg hl
    simp only [letObsT, List.getElem?_map, hl, Option.map_some, Option.some.injEq] at hg
    subst hg
    rfl


end Tools.ShippingMachineTeleNest

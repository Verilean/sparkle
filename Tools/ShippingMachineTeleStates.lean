import Tools.ShippingMachineTeleNest
set_option autoImplicit false
-- FG circuit pilot S2c: narrow endpoint evidence for the chain (`Tele`) path of the machine endpoint. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §31.

/-! # The fused states of a chain endpoint, and the argument values of a call

`machine_trace_of_tele_ext` proves the RTL trace of a `circuit do` with a chain of sub-machines through a state stream `σ` whose steps are the data's `nexts` over the Lean extension `ext S Ss` (`machine_trace_of_stream`'s `stream`). That `σ` was internal. `machine_states_of_tele_ext` has the same
premises (the facts the endpoint generator checks) and returns the stream itself, with the Lean state signals it is read from (`S₂`: the enclosing registers, `Ss`: the chain's), so that facts stated on `(S₂, Ss)` — the per-call argument facts `machine_arg_k` — can be applied to it.
`callArgVals` is the value list the generated call semantics (`Tools.ShippingGen5Sem.calleeOut`: `valsOf (lsrcAt d bs vs S) (callArgs d k) t`) hands to the callee, without the Gen5 imports. -/
namespace Tools.ShippingMachineTeleStates
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineAuto Tools.ShippingMachineFuse
open Tools.ShippingMachineNest (happendT splitL splitR splitL_happendT splitR_happendT happendT_split castSS)
open Tools.ShippingMachineTele Tools.ShippingMachineTeleNest
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness

variable {ι : Type}

/-- the values of the let-wires `args` (a call's argument wires) at cycle `t`, read off the typed valuation of the state `x` and the extension `bits` (the Bool inputs `bools`): `valsOf (lsrcAt d bools bits S) args t` at `x = S.val t` -/
def callArgVals {D : DomainConfig} (d : MachineData) (bools : Nat → Signal D Bool)
    (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (t : Nat) (x : HList (tys d.ss))
    (args : List Nat) : List Nat :=
  args.map fun l => ((d.ls[l]?).map fun lt => enc lt.1 (eval
    (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).b (d.bpos j))
    (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).v (d.vpos j) w) lt.2)).getD 0

/-- the argument wires of call `k` of the machine `d` (the compiler's reading order; the same list as `Tools.ShippingGen5Sem.callArgs`) -/
def callArgsOf (d : MachineData) (k : Nat) : List Nat := ((d.shape.insts.map (·.2.1))[k]?).getD []

/-- the machine's fused state at cycle `t` from the Lean state signals: the enclosing registers `S₂` then the chain's `Ss`, flattened and read at the machine's slot list -/
def teleState {dom : ι → DomainConfig} {ss₂ : List SType} {d : MachineData}
    (l : TeleT ι dom ss₂ (fun _ => [])) (hss : ss₂ ++ l.sss = d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S₂ : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t : Nat) : HList (tys d.ss) :=
  castSS hss (l.fstate i bools bits (S₂.val t) (Tele.valsOf (l.at i bools bits) Ss t))

set_option maxHeartbeats 2000000 in
/-- **The fused state stream of a chain endpoint** (the premises of `machine_trace_of_tele_ext` up to `hI`; its conclusion is the stream that theorem builds for `machine_trace_of_stream`, with its state signals): for every inputs there are Lean state signals `S₂`, `Ss` whose fused state starts at the reset tuple, steps by the data's `nexts` over the Lean extension `ext S₂ Ss`, and shows the data's `outs` as `src`. -/
theorem machine_states_of_tele_ext {declName : Name} (d : MachineData)
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
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss)
          (mkHolds (tys ss₂) S)).snd t)
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
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss)
          (mkHolds (tys ss₂) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).v
            (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (resOn (Tools.ShippingMachineTele.fusedBody (l.at i bools bits)
        (body i bools bits))
        (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits)))))
    (hext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t p w : Nat),
      (ext i bools bits S Ss p w).val t =
        (ext i bools bits ⟨fun _ => S.val t⟩
          (Tele.constOf (l.at i bools bits) (Tele.valsOf (l.at i bools bits) Ss t)) p w).val t)
    (hI : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)), Tele.InitOk (l.at i bools bits)) :
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      ∃ (S₂ : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)),
        teleState l hss i bools bits S₂ Ss 0 = castSS hss (happendT ss₂ l.sss inits l.initsT) ∧
        (∀ t, teleState l hss i bools bits S₂ Ss (t + 1) = evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).v (d.vpos j) w) d.nexts) ∧
        ∀ t, (src i bools bits).map (fun f => f t) = d.outs.map fun o => enc o.1 (eval
          (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).b (d.bpos k))
          (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).v (d.vpos k) w) o.2) := by
  obtain ⟨shape, nIn, domE, bposL, vposL, vwL, ss, ls, outs, nexts⟩ := d
  simp only at hss
  subst hss
  intro i bools bits
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
    show _ = l.unflat i bools bits (splitR ss₂ l.sss
      (E (S.val t) (Tele.valsOf (l.at i bools bits) Ss t) t))
    rw [← hw S Ss t]
    unfold TeleT.fstate
    rw [splitR_happendT, TeleT.unflat_flat]
  obtain ⟨h0, x0, hstep⟩ :=
    Tools.ShippingMachineTele.fused_state inits (l.at i bools bits) (body i bools bits) _ hF
      (hI i bools bits) _ hG
  simp only at x0 hstep
  refine ⟨stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits)),
    Tele.loops (regsOf (tys ss₂) (stateLoop inits
      (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))))
      (l.at i bools bits) (), ?_, ?_, ?_⟩
  · show TeleT.fstate i bools bits l _ _ = _
    rw [h0, x0]
    unfold TeleT.fstate
    rw [TeleT.flat_initsOf]
    rfl
  · intro t
    show TeleT.fstate i bools bits l _ _ = _
    rw [(hstep t).1, (hstep t).2]
    unfold TeleT.fstate
    rw [TeleT.flat_unflat, happendT_split]
    show E _ _ t = _
    simp only [E]
    rw [typedVal_congr _ _ _ _ _ bools
      (ext i bools bits ⟨fun _ => (stateLoop inits
          (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))).val t⟩
        (Tele.constOf (l.at i bools bits) (Tele.valsOf (l.at i bools bits)
          (Tele.loops (regsOf (tys ss₂) (stateLoop inits
            (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))))
            (l.at i bools bits) ()) t)))
      (ext i bools bits (stateLoop inits
          (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits)))
        (Tele.loops (regsOf (tys ss₂) (stateLoop inits
          (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))))
          (l.at i bools bits) ())) t _
      (fun p w => (hext i bools bits _ _ t p w).symm)]
    rfl
  · intro t
    rw [hsrc i bools bits, Tools.ShippingMachineTele.fusedBody_result]
    exact hres i bools bits _ _ t

end Tools.ShippingMachineTeleStates
#print axioms Tools.ShippingMachineTeleStates.machine_states_of_tele_ext

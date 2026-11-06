import Tools.ShippingFGCircuitS1uSrc
import Tools.ShippingGen5SemCongr
import Tools.ShippingMachineTeleStates
set_option autoImplicit false
-- FG circuit pilot S2c: `HftRootLink` from the chain endpoint's facts `machine_states` / `machine_arg_k`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §31.

/-! # S2c (part A): typed agreement of two typed valuations

Two input families that agree, at every INPUT position `p < nIn`, at the declared sort (`d.K p`) give typed valuations that agree at every position (sort-aware, `AgrAt`), and hence the same value for every well-formed term. The generated call semantics (`ExtStage`) puts the call's value at the
position `kD + k` for EVERY width, the Lean extension (`extendBits`) only at the call's own width; the data's terms read the position only at its declared width, so the two give the same terms' values. -/
namespace Tools.ShippingFGCircuitS2cLink
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingMachineRef (reads)
open Tools.ShippingGen5Sem
open Tools.ShippingUnifiedSource

/-- the typed valuations agree at every position below `N`, at the declared sort -/
theorem partial_tagree (d : MachineData) (hok : d.ok = true) {D : DomainConfig}
    (bs bs' : Nat → Signal D Bool) (vs vs' : (j n : Nat) → Signal D (BitVec n)) (t : Nat) (x : HList (tys d.ss))
    (hb : ∀ p, p < d.nIn → (bs p).val t = (bs' p).val t)
    (hv : ∀ p w, p < d.nIn → d.K p = some (.bits w) → (vs p w).val t = (vs' p w).val t) :
    ∀ m, m ≤ d.ls.length → ∀ p, p < d.nIn + d.ss.length + m →
      AgrAt d (partialVal d bs vs t x m) (partialVal d bs' vs' t x m) p := by
  obtain ⟨fb, fv, fslots⟩ := ok_Kfacts d hok
  have hLT := Tools.ShippingQuadCalls.ok_letsTyped d hok
  intro m
  induction m with
  | zero =>
    intro _ p hp
    have e0 : partialVal d bs vs t x 0 =
        slotVal d.nIn d.ss x 0 ⟨fun p => (bs p).val t, fun p w => (vs p w).val t⟩ := rfl
    have e0' : partialVal d bs' vs' t x 0 =
        slotVal d.nIn d.ss x 0 ⟨fun p => (bs' p).val t, fun p w => (vs' p w).val t⟩ := rfl
    rw [e0, e0']
    rcases Nat.lt_or_ge p d.nIn with h1 | h1
    · have s1 := slotVal_lt d.nIn d.ss x 0 ⟨fun p => (bs p).val t, fun p w => (vs p w).val t⟩ p (by omega)
      have s2 := slotVal_lt d.nIn d.ss x 0 ⟨fun p => (bs' p).val t, fun p w => (vs' p w).val t⟩ p (by omega)
      refine ⟨fun _ => ?_, fun w hKw => ?_⟩
      · rw [s1.1, s2.1]; exact hb p h1
      · rw [(s1.2 w), (s2.2 w)]; exact hv p w h1 hKw
    · have hi : p - d.nIn < d.ss.length := by omega
      have hK := fslots (p - d.nIn) hi
      rw [show d.nIn + (p - d.nIn) = p by omega] at hK
      refine ⟨fun hKb => ?_, fun w hKw => ?_⟩
      · rw [hK] at hKb
        have a1 := (slotVal_at d.nIn d.ss x 0 ⟨fun p => (bs p).val t, fun p w => (vs p w).val t⟩ (p - d.nIn) .bool hKb).1 rfl
        have a2 := (slotVal_at d.nIn d.ss x 0 ⟨fun p => (bs' p).val t, fun p w => (vs' p w).val t⟩ (p - d.nIn) .bool hKb).1 rfl
        rw [show d.nIn + 0 + (p - d.nIn) = p by omega] at a1 a2
        exact encodeBool_inj' (a1.trans a2.symm)
      · rw [hK] at hKw
        have a1 := (slotVal_at d.nIn d.ss x 0 ⟨fun p => (bs p).val t, fun p w => (vs p w).val t⟩ (p - d.nIn) (.bits w) hKw).2 w rfl
        have a2 := (slotVal_at d.nIn d.ss x 0 ⟨fun p => (bs' p).val t, fun p w => (vs' p w).val t⟩ (p - d.nIn) (.bits w) hKw).2 w rfl
        rw [show d.nIn + 0 + (p - d.nIn) = p by omega] at a1 a2
        exact BitVec.eq_of_toNat_eq (a1.trans a2.symm)
  | succ m ih =>
    intro hm p hp
    have hm' : m < d.ls.length := hm
    have ihm := ih (by omega)
    obtain ⟨hwf, hrd, hKP⟩ := LetsTyped.get3 hLT m (d.ls[m]) (List.getElem?_eq_getElem hm')
    rw [partialVal_succ d bs vs t x m hm', partialVal_succ d bs' vs' t x m hm']
    by_cases hpP : p = d.nIn + d.ss.length + m
    · subst hpP
      have hev : eval (fun j => (partialVal d bs vs t x m).b (d.bpos j))
            (fun j w => (partialVal d bs vs t x m).v (d.vpos j) w) (d.ls[m]).2 =
          eval (fun j => (partialVal d bs' vs' t x m).b (d.bpos j))
            (fun j w => (partialVal d bs' vs' t x m).v (d.vpos j) w) (d.ls[m]).2 := by
        refine eval_congr_wf (okB := fun j => decide (d.bpos j < d.nIn + d.ss.length + m))
          (okV := fun j => decide (d.vpos j < d.nIn + d.ss.length + m)) (kb := d.kb) (kv := d.kv) (vw := d.vw)
          (fun j hj hokj => ?_) (fun j hj hokj => ?_) _ hwf hrd
        · exact (ihm _ (by simpa using hokj)).1 (fb j hj).1
        · exact (ihm _ (by simpa using hokj)).2 (d.vw j) (fv j hj).1
      generalize d.ls[m] = lm at hev hKP
      obtain ⟨s, e⟩ := lm
      simp only at hev hKP
      cases s with
      | bool =>
        refine ⟨fun _ => ?_, fun w hw => ?_⟩
        · rw [set_b_eq, set_b_eq]; exact hev
        · rw [hKP] at hw; cases hw
      | bits w0 =>
        refine ⟨fun hw => ?_, fun w hw => ?_⟩
        · rw [hKP] at hw; cases hw
        · rw [hKP] at hw
          have : w0 = w := by injection hw with h; injection h
          subst this
          rw [set_v_eq, set_v_eq]; exact hev
    · have hp2 : p < d.nIn + d.ss.length + m := by omega
      have a := ihm p hp2
      exact ⟨fun h => by rw [set_b_ne hpP, set_b_ne hpP]; exact a.1 h,
        fun w h => by rw [set_v_ne hpP, set_v_ne hpP]; exact a.2 w h⟩

theorem typedVal_tagree (d : MachineData) (hok : d.ok = true) {D : DomainConfig}
    (bs bs' : Nat → Signal D Bool) (vs vs' : (j n : Nat) → Signal D (BitVec n)) (t : Nat) (x : HList (tys d.ss))
    (hb : ∀ p, p < d.nIn → (bs p).val t = (bs' p).val t)
    (hv : ∀ p w, p < d.nIn → d.K p = some (.bits w) → (vs p w).val t = (vs' p w).val t) :
    ∀ p, p < d.nIn + d.ss.length + d.ls.length →
      AgrAt d (typedVal d.nIn d.bpos d.vpos d.ss d.ls bs vs t x) (typedVal d.nIn d.bpos d.vpos d.ss d.ls bs' vs' t x) p := by
  intro p hp
  rw [typedVal_eq_partial, typedVal_eq_partial]
  exact partial_tagree d hok bs bs' vs vs' t x hb hv d.ls.length (Nat.le_refl _) p hp

/-- a well-formed term has the same value under typed valuations that agree at the declared sorts -/
theorem eval_tagree (d : MachineData) (hok : d.ok = true) {T T' : TVal}
    (h : ∀ p, p < d.nIn + d.ss.length + d.ls.length → AgrAt d T T' p) {s : SType} (e : Term s)
    (hwf : e.WF d.kb d.kv d.vw) :
    eval (fun j => T.b (d.bpos j)) (fun j w => T.v (d.vpos j) w) e =
      eval (fun j => T'.b (d.bpos j)) (fun j w => T'.v (d.vpos j) w) e := by
  obtain ⟨fb, fv, -⟩ := ok_Kfacts d hok
  exact eval_congr_wf (okB := fun _ => true) (okV := fun _ => true) (kb := d.kb) (kv := d.kv) (vw := d.vw)
    (fun j hj _ => (h _ (fb j hj).2).1 (fb j hj).1) (fun j hj _ => (h _ (fv j hj).2).2 (d.vw j) (fv j hj).1)
    e hwf (reads_true e)

/-! # S2c (part B): states and outputs from the encoded values -/

theorem Terms.fields_length : ∀ {ss : List SType} (ts : Terms ss), ts.fields.length = ss.length
  | _, .nil => rfl
  | _, .cons _ ts => by simp [Terms.fields, Terms.fields_length ts]

theorem enc_inj : ∀ (s : SType) (a b : s.Type), enc s a = enc s b → a = b
  | .bool, a, b, h => encodeBool_inj' h
  | .bits _, a, b, h => BitVec.eq_of_toNat_eq h

theorem hlist_ext_of_encState : ∀ (ss : List SType) (x y : HList (tys ss)),
    (∀ i, encState ss x i = encState ss y i) → x = y
  | [], x, y, _ => rfl
  | s :: ss, x, y, h => by
    refine Prod.ext (enc_inj s _ _ (h 0)) (hlist_ext_of_encState ss x.2 y.2 fun i => h (i + 1))

theorem inits_unique (d : MachineData) (x y : HList (tys d.ss)) (hx : d.initOk x = true) (hy : d.initOk y = true) :
    x = y := by
  apply hlist_ext_of_encState
  intro i
  by_cases hi : i < d.ss.length
  · unfold MachineData.initOk at hx hy
    have h1 := List.all_eq_true.mp hx i (List.mem_range.mpr hi)
    have h2 := List.all_eq_true.mp hy i (List.mem_range.mpr hi)
    exact (beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2).symm
  · rw [encState_ge d.ss x i (by omega), encState_ge d.ss y i (by omega)]

theorem ok_nextsWF (d : MachineData) (h : d.ok = true) : ∀ g ∈ d.nexts.fields, g.2.WF d.kb d.kv d.vw := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, hslots, fb, fv, fslots, flets, nextsWF, houts, hne⟩ := h
  exact nextsWF

theorem ok_outsFit (d : MachineData) (h : d.ok = true) :
    outsFitB d.kb d.kv d.vw d.fields d.shape.layout.outs d.outs = true := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, hslots, fb, fv, fslots, flets, nextsWF, houts, hne⟩ := h
  exact houts

theorem outs_wf (d : MachineData) (h : d.ok = true) (hlen : d.outs.length = d.shape.layout.outs.length) :
    ∀ o ∈ d.outs, o.2.WF d.kb d.kv d.vw := by
  intro o ho
  obtain ⟨k, hk, hko⟩ := List.getElem_of_mem ho
  have hk' : k < d.shape.layout.outs.length := by omega
  exact (outsFit_get (ok_outsFit d h) (o := d.shape.layout.outs[k]) (List.getElem?_eq_getElem hk')
    (by rw [List.getElem?_eq_getElem hk, hko])).1

/-- the next states agree under typed valuations that agree at the declared sorts -/
theorem nexts_tagree (d : MachineData) (hok : d.ok = true) {T T' : TVal}
    (h : ∀ p, p < d.nIn + d.ss.length + d.ls.length → AgrAt d T T' p) :
    evalTerms (fun j => T.b (d.bpos j)) (fun j w => T.v (d.vpos j) w) d.nexts =
      evalTerms (fun j => T'.b (d.bpos j)) (fun j w => T'.v (d.vpos j) w) d.nexts := by
  apply hlist_ext_of_encState
  intro i
  by_cases hi : i < d.ss.length
  · have hl : i < d.nexts.fields.length := by rw [Terms.fields_length]; exact hi
    obtain ⟨g, hg⟩ : ∃ g, d.nexts.fields[i]? = some g := ⟨_, List.getElem?_eq_getElem hl⟩
    rw [encState_evalTerms _ _ d.nexts i g hg, encState_evalTerms _ _ d.nexts i g hg,
      eval_tagree d hok h g.2 (ok_nextsWF d hok g (List.mem_of_getElem? hg))]
  · rw [encState_ge d.ss _ i (by omega), encState_ge d.ss _ i (by omega)]

/-- the outputs agree under typed valuations that agree at the declared sorts -/
theorem outs_tagree (d : MachineData) (hok : d.ok = true) (hwf : ∀ o ∈ d.outs, o.2.WF d.kb d.kv d.vw) {T T' : TVal}
    (h : ∀ p, p < d.nIn + d.ss.length + d.ls.length → AgrAt d T T' p) :
    d.outs.map (fun o => enc o.1 (eval (fun j => T.b (d.bpos j)) (fun j w => T.v (d.vpos j) w) o.2)) =
      d.outs.map (fun o => enc o.1 (eval (fun j => T'.b (d.bpos j)) (fun j w => T'.v (d.vpos j) w) o.2)) := by
  apply List.map_congr_left
  intro o ho
  rw [eval_tagree d hok h o.2 (hwf o ho)]

/-- the argument values of a call agree under typed valuations that agree at the declared sorts -/
theorem callArgVals_tagree (d : MachineData) (hok : d.ok = true) {D : DomainConfig}
    (bs bs' : Nat → Signal D Bool) (vs vs' : (j n : Nat) → Signal D (BitVec n)) (t : Nat) (x : HList (tys d.ss))
    (hb : ∀ p, p < d.nIn → (bs p).val t = (bs' p).val t)
    (hv : ∀ p w, p < d.nIn → d.K p = some (.bits w) → (vs p w).val t = (vs' p w).val t)
    (args : List Nat) (hargs : ∀ l ∈ args, ∀ lt, d.ls[l]? = some lt → lt.2.WF d.kb d.kv d.vw) :
    Tools.ShippingMachineTeleStates.callArgVals d bs vs t x args =
      Tools.ShippingMachineTeleStates.callArgVals d bs' vs' t x args := by
  unfold Tools.ShippingMachineTeleStates.callArgVals
  apply List.map_congr_left
  intro l hl
  cases hls : d.ls[l]? with
  | none => rfl
  | some lt =>
    simp only [Option.map_some, Option.getD_some]
    rw [eval_tagree d hok (typedVal_tagree d hok bs bs' vs vs' t x hb hv) lt.2 (hargs l hl lt hls)]

end Tools.ShippingFGCircuitS2cLink

import Tools.ShippingFGCircuitS1uSrc
import Tools.ShippingGen5SemCongr
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

end Tools.ShippingFGCircuitS2cLink

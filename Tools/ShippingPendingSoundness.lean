import Tools.ShippingTranslationOrder

/-! # Pending parent results survive recursive operand translation

The protected name is reserved but absent from the body, source bindings and
semantically meaningful cache records. First prove recursive protection, then
use it to prove order preservation for the entire supported expression
fragment. Both follow the shipping entry, including validated cache hits,
with no recursive hypothesis. Protection is the explicit input to the
protection theorem and is derived internally by the order theorem. Initial
semantic/order invariants and final width agreement remain explicit; synthesis
initialization, output emission and downstream passes are separate obligations.
-/
namespace Tools.ShippingPendingSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Reorder
open Tools.ShippingTranslateSoundness Tools.ShippingTranslationOrder
open Tools.ShippingBindingsSoundness (visible)

structure Protected (ctx : CompilerState) (ρ : Valuation) (s : CircuitState) (p : String) : Prop where
  reserved : s.usedNames.contains p = true
  pending : Pending s p
  unbound : ∀ id n (x : BitVec n), ρ id = some ⟨n, x⟩ → visible ctx s.sourceBindings id ≠ some p
  unrecorded : ∀ e n (x : BitVec n), s.translateRecord.get? p = some e → ¬ Denotes ρ e n x

theorem Protected.transfer {ctx ρ s t p} (hp : Protected ctx ρ s p)
    (hu : ∀ x, s.usedNames.contains x = true → t.usedNames.contains x = true)
    (hb : t.sourceBindings = s.sourceBindings) (hr : RecordFresh s t)
    (hpending : Pending t p) : Protected ctx ρ t p := by
  refine ⟨hu p hp.reserved, hpending, ?_, ?_⟩
  · rw [hb]; exact hp.unbound
  · intro e n x he hd
    rcases hr p e he with he | hf
    · exact hp.unrecorded e n x he hd
    · rw [hp.reserved] at hf; cases hf

theorem Protected.makeWire {ctx ρ s t p hint ty named name}
    (hp : Protected ctx ρ s p)
    (h : Returns (CompilerM.makeWire hint ty named) ctx s name t) :
    Protected ctx ρ t p ∧ name ≠ p := by
  obtain ⟨hn, ht⟩ := makeWire_returns h
  obtain ⟨hf, hu, hb, _⟩ := CircuitM.makeWire_spec hint ty named s
  rw [← hn] at hf hu
  rw [← ht] at hu hb
  have hneq : name ≠ p := by intro he; rw [he, hp.reserved] at hf; cases hf
  refine ⟨hp.transfer (fun x hx => by rw [hu]; simp [Std.HashSet.contains_insert, hx])
    (by rw [ht]; exact CircuitM.makeWire_sourceBindings _ _ _ _) ?_ ?_, hneq⟩
  · intro x e he; left
    rwa [ht, CircuitM.makeWire_translateRecord] at he
  · change p ∉ footprint t.module.body
    rw [hb]; exact hp.pending

theorem pending_emit {ctx s t p l rhs u}
    (h : Returns (CompilerM.emitAssign l rhs) ctx s u t)
    (hp : Pending s p) (hl : p ≠ l) (hr : p ∉ refsOf rhs) : Pending t p := by
  change p ∉ footprint t.module.body
  rw [emitAssign_returns h, emitAssign_body_cons, footprint_cons]
  simpa only [List.mem_cons, List.mem_append, not_or, Pending] using And.intro hl (And.intro hr hp)

def Protects (rec : TranslateFn) (ctx : CompilerState) (ρ : Valuation) : Prop :=
  ∀ e hint named n (x : BitVec n) s w t p, Denotes ρ e n x →
    Returns (rec e hint false named) ctx s w t → BoundLookup ctx ρ s →
    Protected ctx ρ s p → Pending t p ∧ w ≠ p

theorem literal_protects {ctx ρ s t p args hint named result}
    (h : Returns (translateSignalPureLiteral? args hint named) ctx s result t)
    (hp : Protected ctx ρ s p) : Pending t p ∧ ∀ w, result = some w → w ≠ p := by
  unfold translateSignalPureLiteral? at h
  split at h
  · obtain ⟨name, sA, hm, rest⟩ := Returns.bind h
    obtain ⟨u, sB, he, ret⟩ := Returns.bind rest
    obtain ⟨hr, ht⟩ := Returns.pure ret
    obtain ⟨hpA, hne⟩ := hp.makeWire hm
    refine ⟨ht ▸ pending_emit he hpA.pending (Ne.symm hne) (by simp [refsOf]), ?_⟩
    intro w hw; rw [hr] at hw; cases hw; exact hne
  · obtain ⟨hr, ht⟩ := Returns.pure h
    exact ⟨ht ▸ hp.pending, fun w hw => by rw [hr] at hw; cases hw⟩

theorem binary_protects {rec : TranslateFn} {ctx we mems initial ρ}
    (ih : Spec rec ctx we mems initial ρ) (ip : Protects rec ctx ρ)
    {e : Lean.Expr} {m : Name} {us : List Level} {op hint named n} {x : BitVec n}
    {s t : CircuitState} {w p : String}
    (hfn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (hd : Denotes ρ e n x)
    (h : Returns (translateCanonicalSignalBinary rec e op e.getAppArgs true true hint named) ctx s w t)
    (hb : BoundLookup ctx ρ s) (hp : Protected ctx ρ s p) : Pending t p ∧ w ≠ p := by
  cases hd with
  | fvar _ => simp [Lean.Expr.getAppFn] at hfn
  | pureLit hfn' _ _ =>
    rw [hfn] at hfn'; cases hfn'; rw [signalBinOpOf_pure] at hop; cases hop
  | @binary _ m' us' bop _ x1 x2 hfn' hop' _ hwid hd1 hd2 =>
    rw [hfn] at hfn'; cases hfn'
    have he : op = bop.operator := by rw [hop] at hop'; exact Option.some.inj hop'
    subst he
    unfold translateCanonicalSignalBinary at h
    simp only [hwid] at h
    obtain ⟨hw, s0, hty, rest⟩ := Returns.bind h
    obtain ⟨hwidth, hs0⟩ := Returns.pure hty
    rw [hwidth] at rest
    obtain ⟨res, sA, hm, rest⟩ := Returns.bind rest
    rw [hs0] at hm
    obtain ⟨wa, sB, ha, rest⟩ := Returns.bind rest
    obtain ⟨wb, sC, hb', rest⟩ := Returns.bind rest
    obtain ⟨u, sD, hem, ret⟩ := Returns.bind rest
    obtain ⟨hw, ht⟩ := Returns.pure ret
    obtain ⟨hpA, hres⟩ := hp.makeWire hm
    obtain ⟨hn, hsA⟩ := makeWire_returns hm
    obtain ⟨_, hu, _, _⟩ := CircuitM.makeWire_spec hint (.bitVector n) named s
    rw [← hsA] at hu
    have hba : BoundLookup ctx ρ sA := hb.transfer (fun z hz => by
      rw [hu]; simp [Std.HashSet.contains_insert, hz]) (by
        rw [hsA]; exact CircuitM.makeWire_sourceBindings _ _ _ _)
    obtain ⟨ga, sba, rfa, _⟩ := ih.grows _ _ _ _ _ _ _ _ hd1 ha hba
    obtain ⟨hpa, hwa⟩ := ip _ _ _ _ _ _ _ _ p hd1 ha hba hpA
    have hpB := hpA.transfer ga.1 sba rfa hpa
    have hbb := hba.transfer ga.1 sba
    obtain ⟨hpb, hwb⟩ := ip _ _ _ _ _ _ _ _ p hd2 hb' hbb hpB
    refine ⟨ht ▸ pending_emit hem hpb (Ne.symm hres) ?_, hw ▸ hres⟩
    simp [refsOf, refsOf.refsList, Ne.symm hwa, Ne.symm hwb]

theorem core_protects {rec : TranslateFn} {ctx we mems initial ρ}
    (ih : Spec rec ctx we mems initial ρ) (ip : Protects rec ctx ρ)
    {e : Lean.Expr} {hint named n} {x : BitVec n} {s t : CircuitState}
    {result : Option String} {p : String}
    (hd : Denotes ρ e n x) (hb : BoundLookup ctx ρ s)
    (h : Returns (translateCore rec e hint false named) ctx s result t)
    (hp : Protected ctx ρ s p) : Pending t p ∧ ∃ w, result = some w ∧ w ≠ p := by
  cases hd with
  | @fvar id _ _ hv =>
    obtain ⟨hr, ht⟩ := lookupVar_returns h
    obtain ⟨w, hw, _⟩ := hb id _ _ hv
    refine ⟨ht ▸ hp.pending, w, hr.trans hw, ?_⟩
    intro he; exact hp.unbound id _ _ hv (he ▸ hw)
  | pureLit hfn hback hlit =>
    unfold translateCore at h
    split at h
    · simp [Lean.Expr.getAppFn] at hfn
    · rw [hfn] at h
      simp only [beq_self_eq_true, if_true] at h
      obtain ⟨hpend, hne⟩ := literal_protects h hp
      unfold translateSignalPureLiteral? at h
      rw [hback] at h
      simp only [Option.bind_some, hlit] at h
      obtain ⟨w, _, _, rest⟩ := Returns.bind h
      obtain ⟨_, _, _, ret⟩ := Returns.bind rest
      have hr := (Returns.pure ret).1
      exact ⟨hpend, w, hr, hne w hr⟩
  | @binary _ m us bop _ x1 x2 hfn hop hk hwid hd1 hd2 =>
    have hd := Denotes.binary hfn hop hk hwid hd1 hd2
    unfold translateCore at h
    split at h
    · simp [Lean.Expr.getAppFn] at hfn
    · rw [hfn] at h
      have hm : (m == ``Sparkle.Core.Signal.Signal.pure) = false := by
        cases hh : (m == ``Sparkle.Core.Signal.Signal.pure) with
        | false => rfl
        | true =>
          have he : m = ``Sparkle.Core.Signal.Signal.pure := by simpa using hh
          rw [he, signalBinOpOf_pure] at hop; cases hop
      simp only [hm, Bool.false_eq_true, if_false, hop, hk, hwid] at h
      obtain ⟨w, sd, htr, ret⟩ := Returns.bind h
      obtain ⟨hr, ht⟩ := Returns.pure ret
      obtain ⟨hpend, hne⟩ := binary_protects ih ip hfn hop hd htr hb hp
      exact ⟨ht ▸ hpend, w, hr, hne⟩

theorem core_continuation_protects {rec : TranslateFn} {ctx we mems initial ρ}
    (ih : Spec rec ctx we mems initial ρ) (ip : Protects rec ctx ρ)
    {e : Lean.Expr} {hint named c n} {x : BitVec n} {s t : CircuitState}
    {K : Option String → CompilerM String} {result p : String}
    (hK : ∀ name, K (some name) = if e.isFVar = true then pure name else
      (recordTranslation e name c >>= fun _ => pure name))
    (hd : Denotes ρ e n x) (hb : BoundLookup ctx ρ s)
    (h : Returns (translateCore rec e hint false named >>= K) ctx s result t)
    (hp : Protected ctx ρ s p) : Pending t p ∧ result ≠ p := by
  obtain ⟨r, sc, hc, hk⟩ := Returns.bind h
  obtain ⟨hpend, w, hr, hne⟩ := core_protects ih ip hd hb hc hp
  rw [hr, hK] at hk
  split at hk
  · obtain ⟨hw, ht⟩ := Returns.pure hk
    exact ⟨ht ▸ hpend, hw ▸ hne⟩
  · obtain ⟨_, sr, hrec, ret⟩ := Returns.bind hk
    have hs := recordTranslation_returns hrec
    obtain ⟨hw, ht⟩ := Returns.pure ret
    refine ⟨?_, hw ▸ hne⟩
    rw [ht, hs]; exact hpend

theorem step_protects {fallback : TranslateFn → TranslateFn} {rec : TranslateFn}
    {ctx we mems initial ρ}
    (ih : Spec rec ctx we mems initial ρ) (ip : Protects rec ctx ρ) :
    Protects (translateStepWith fallback rec) ctx ρ := by
  intro e hint named n x s result t p hd h hb hp
  unfold translateStepWith at h
  dsimp only at h
  by_cases hc : ((!named && !e.isFVar && !false) && translateCoreShape e) = true
  · rw [if_pos hc] at h
    obtain ⟨r, sc, hc, hk⟩ := Returns.bind h
    obtain ⟨hs, hrecord⟩ := cacheLookupValidated_returns hc
    split at hk
    · rename_i w
      obtain ⟨hw, ht⟩ := Returns.pure hk
      refine ⟨ht ▸ hs ▸ hp.pending, ?_⟩
      intro he
      have hr := hrecord w rfl
      rw [← hw, he] at hr
      exact hp.unrecorded e n x hr hd
    · rw [hs] at hk
      exact core_continuation_protects ih ip (fun _ => rfl) hd hb hk hp
  · rw [if_neg hc] at h
    exact core_continuation_protects ih ip (fun _ => rfl) hd hb h hp

theorem fuel_protects {ctx we mems initial ρ} :
    ∀ fuel, Spec (translateFuelFix translateStep fuel) ctx we mems initial ρ ∧
      Protects (translateFuelFix translateStep fuel) ctx ρ
  | 0 => ⟨spec_of_never (fun _ _ _ _ _ _ _ h => Returns.throw h), by
      intro e hint named n x s w t p hd h hb hp; exact False.elim (Returns.throw h)⟩
  | k + 1 =>
    have ih := fuel_protects k
    ⟨translateStepWith_spec ih.1, step_protects ih.1 ih.2⟩

/-- Any supported expression, with arbitrary nesting of canonical operators,
preserves a protected pending name and cannot return it, at the real entry. -/
theorem translateExprToWire_protects {ctx ρ} : Protects (fun e h t n => translateExprToWire e h t n) ctx ρ :=
  (fuel_protects (ctx := ctx) (ρ := ρ) (we := fun _ => 0) (mems := fun _ _ => 0)
    (initial := fun _ => 0) translateFuelLimit).2


/-- Order preservation, using the translator's existing semantic invariant
and final width agreement. Neither source truth nor pending-name protection
is assumed for the recursive calls at the final entry. -/
def Orders (rec : TranslateFn) (ctx : CompilerState)
    (we : Sparkle.IR.Semantics.WEnv) (mems : Sparkle.IR.Semantics.MEnv)
    (initial : Sparkle.IR.Semantics.Env) (ρ : Valuation) : Prop :=
  ∀ e hint named n (x : BitVec n) s env0 w t, Denotes ρ e n x →
    Returns (rec e hint false named) ctx s w t →
    Inv ctx ρ we mems initial s env0 → WidthsAgree we t → OrderInv s → OrderInv t

theorem binary_orders {rec : TranslateFn} {ctx we mems initial ρ}
    (ih : Spec rec ctx we mems initial ρ) (ip : Protects rec ctx ρ)
    (io : Orders rec ctx we mems initial ρ)
    {e : Lean.Expr} {m : Name} {us : List Level} {op hint named n} {x : BitVec n}
    {s t : CircuitState} {w : String} {env0 : Sparkle.IR.Semantics.Env}
    (hfn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (hd : Denotes ρ e n x)
    (h : Returns (translateCanonicalSignalBinary rec e op e.getAppArgs true true hint named) ctx s w t)
    (hi : Inv ctx ρ we mems initial s env0) (hw : WidthsAgree we t) (ho : OrderInv s) :
    OrderInv t := by
  cases hd with
  | fvar _ => simp [Lean.Expr.getAppFn] at hfn
  | pureLit hfn' _ _ =>
    rw [hfn] at hfn'; cases hfn'; rw [signalBinOpOf_pure] at hop; cases hop
  | @binary _ m' us' bop _ x1 x2 hfn' hop' _ hwid hd1 hd2 =>
    rw [hfn] at hfn'; cases hfn'
    have he : op = bop.operator := by rw [hop] at hop'; exact Option.some.inj hop'
    subst he
    unfold translateCanonicalSignalBinary at h
    simp only [hwid] at h
    obtain ⟨ty, s0, hty, rest⟩ := Returns.bind h
    obtain ⟨hty, hs0⟩ := Returns.pure hty
    rw [hty] at rest
    obtain ⟨res, sA, hm, rest⟩ := Returns.bind rest
    rw [hs0] at hm
    obtain ⟨wa, sB, ha, rest⟩ := Returns.bind rest
    obtain ⟨wb, sC, hb, rest⟩ := Returns.bind rest
    obtain ⟨u, sD, hem, ret⟩ := Returns.bind rest
    obtain ⟨_, ht⟩ := Returns.pure ret
    rw [ht] at hw ⊢
    obtain ⟨hres, hsA⟩ := makeWire_returns hm
    obtain ⟨hf, hu, hbody, _⟩ := CircuitM.makeWire_spec hint (.bitVector n) named s
    rw [← hres] at hf hu
    rw [← hsA] at hu hbody
    have hsb : sA.sourceBindings = s.sourceBindings := by
      rw [hsA]; exact CircuitM.makeWire_sourceBindings _ _ _ _
    have hrec : sA.translateRecord = s.translateRecord := by
      rw [hsA]; exact CircuitM.makeWire_translateRecord _ _ _ _
    have hg : ∀ z, s.usedNames.contains z = true → sA.usedNames.contains z = true := by
      intro z hz; rw [hu]; simp [Std.HashSet.contains_insert, hz]
    have hiA := hi.transfer (runs_of_body_eq hbody hi.runs)
      (by rw [hbody]; exact hi.sized) hg hsb hrec (fun _ _ => rfl)
    obtain ⟨hoA, hpend, hused⟩ := makeWire_order hm ho
    have hpA : Protected ctx ρ sA res := ⟨hused, hpend,
      by rw [hsb]; exact fresh_not_bound hi.lookup hf,
      by rw [hrec]; exact fresh_not_recorded hi.record hf⟩
    obtain ⟨ga, sba, rfa, _⟩ := ih.grows _ _ _ _ _ _ _ _ hd1 ha hiA.lookup
    have hblB := hiA.lookup.transfer ga.1 sba
    obtain ⟨gb, _, _, _⟩ := ih.grows _ _ _ _ _ _ _ _ hd2 hb hblB
    have hwC : WidthsAgree we sC := hw.mono (by
      intro p hp; rw [emitAssign_returns hem, emitAssign_wires]; exact hp)
    have hwB := hwC.mono gb.2.1
    obtain ⟨envB, hiB, _, useA, _, _⟩ := ih.sem _ _ _ _ _ _ _ _ _ hd1 ha hiA hwB
    have hoB := io _ _ _ _ _ _ _ _ _ hd1 ha hiA hwB hoA
    have hoC := io _ _ _ _ _ _ _ _ _ hd2 hb hiB hwC hoB
    obtain ⟨_, _, _, useB, _, _⟩ := ih.sem _ _ _ _ _ _ _ _ _ hd2 hb hiB hwC
    obtain ⟨hpa, hwa⟩ := ip _ _ _ _ _ _ _ _ res hd1 ha hiA.lookup hpA
    have hpB := hpA.transfer ga.1 sba rfa hpa
    obtain ⟨hpc, hwb⟩ := ip _ _ _ _ _ _ _ _ res hd2 hb hblB hpB
    apply emitAssign_order hem hoC hpc (gb.1 res (ga.1 res hused))
    · simp [refsOf, refsOf.refsList, Ne.symm hwa, Ne.symm hwb]
    · intro z hz
      have hz' : z = wa ∨ z = wb := by simpa [refsOf, refsOf.refsList] using hz
      rcases hz' with rfl | rfl
      · exact gb.1 _ useA
      · exact useB

theorem core_orders {rec : TranslateFn} {ctx we mems initial ρ}
    (ih : Spec rec ctx we mems initial ρ) (ip : Protects rec ctx ρ)
    (io : Orders rec ctx we mems initial ρ)
    {e : Lean.Expr} {hint named n} {x : BitVec n} {s t : CircuitState}
    {result : Option String} {env0 : Sparkle.IR.Semantics.Env}
    (hd : Denotes ρ e n x)
    (h : Returns (translateCore rec e hint false named) ctx s result t)
    (hi : Inv ctx ρ we mems initial s env0) (ho : OrderInv s) :
    (∃ w, result = some w) ∧ (WidthsAgree we t → OrderInv t) := by
  cases hd with
  | fvar hv =>
    obtain ⟨ht, hex⟩ := core_leaf_order (.fvar hv) (Or.inl rfl) hi.lookup h ho
    exact ⟨hex, fun _ => ht⟩
  | pureLit hfn hback hlit =>
    obtain ⟨ht, hex⟩ := core_leaf_order (.pureLit hfn hback hlit)
      (Or.inr ⟨_, hfn⟩) hi.lookup h ho
    exact ⟨hex, fun _ => ht⟩
  | @binary _ m us bop _ x1 x2 hfn hop hk hwid hd1 hd2 =>
    have hd := Denotes.binary hfn hop hk hwid hd1 hd2
    unfold translateCore at h
    split at h
    · simp [Lean.Expr.getAppFn] at hfn
    · rw [hfn] at h
      have hm : (m == ``Sparkle.Core.Signal.Signal.pure) = false := by
        cases hh : (m == ``Sparkle.Core.Signal.Signal.pure) with
        | false => rfl
        | true =>
          have he : m = ``Sparkle.Core.Signal.Signal.pure := by simpa using hh
          rw [he, signalBinOpOf_pure] at hop; cases hop
      simp only [hm, Bool.false_eq_true, if_false, hop, hk, hwid] at h
      obtain ⟨w, sd, htr, ret⟩ := Returns.bind h
      obtain ⟨hr, ht⟩ := Returns.pure ret
      refine ⟨⟨w, hr⟩, ?_⟩
      rw [ht]
      intro hw
      exact binary_orders ih ip io hfn hop hd htr hi hw ho

theorem core_continuation_orders {rec : TranslateFn} {ctx we mems initial ρ}
    (ih : Spec rec ctx we mems initial ρ) (ip : Protects rec ctx ρ)
    (io : Orders rec ctx we mems initial ρ)
    {e : Lean.Expr} {hint named c n} {x : BitVec n} {s t : CircuitState}
    {K : Option String → CompilerM String} {result : String} {env0 : Sparkle.IR.Semantics.Env}
    (hK : ∀ name, K (some name) = if e.isFVar = true then pure name else
      (recordTranslation e name c >>= fun _ => pure name))
    (hd : Denotes ρ e n x)
    (h : Returns (translateCore rec e hint false named >>= K) ctx s result t)
    (hi : Inv ctx ρ we mems initial s env0) (hw : WidthsAgree we t) (ho : OrderInv s) :
    OrderInv t := by
  obtain ⟨r, sc, hc, hk⟩ := Returns.bind h
  obtain ⟨⟨w, hr⟩, horder⟩ := core_orders ih ip io hd hc hi ho
  rw [hr, hK] at hk
  split at hk
  · have ht := (Returns.pure hk).2
    rw [ht] at hw ⊢; exact horder hw
  · obtain ⟨_, sr, hrec, ret⟩ := Returns.bind hk
    have hs := recordTranslation_returns hrec
    have ht := (Returns.pure ret).2
    rw [ht, hs] at hw ⊢
    exact horder hw

theorem step_orders {fallback : TranslateFn → TranslateFn} {rec : TranslateFn}
    {ctx we mems initial ρ}
    (ih : Spec rec ctx we mems initial ρ) (ip : Protects rec ctx ρ)
    (io : Orders rec ctx we mems initial ρ) :
    Orders (translateStepWith fallback rec) ctx we mems initial ρ := by
  intro e hint named n x s env0 result t hd h hi hw ho
  unfold translateStepWith at h
  dsimp only at h
  by_cases hc : ((!named && !e.isFVar && !false) && translateCoreShape e) = true
  · rw [if_pos hc] at h
    obtain ⟨r, sc, hc, hk⟩ := Returns.bind h
    have hs := (cacheLookupValidated_returns hc).1
    split at hk
    · rw [(Returns.pure hk).2, hs]; exact ho
    · rw [hs] at hk
      exact core_continuation_orders ih ip io (fun _ => rfl) hd hk hi hw ho
  · rw [if_neg hc] at h
    exact core_continuation_orders ih ip io (fun _ => rfl) hd h hi hw ho

theorem fuel_orders {ctx we mems initial ρ} :
    ∀ fuel, Orders (translateFuelFix translateStep fuel) ctx we mems initial ρ
  | 0 => by
    intro e hint named n x s env0 w t hd h hi hw ho
    exact False.elim (Returns.throw h)
  | k + 1 => step_orders (fuel_protects k).1 (fuel_protects (we := we)
      (mems := mems) (initial := initial) k).2 (fuel_orders k)

/-- Order preservation for arbitrary nesting of the supported operators,
inputs and literals at the shipping entry. Recursion and cache paths are
closed; initial semantic/order invariants and final widths are explicit. -/
theorem translateExprToWire_orders {ctx we mems initial ρ} :
    Orders (fun e h t n => translateExprToWire e h t n) ctx we mems initial ρ :=
  fuel_orders translateFuelLimit

/-- The general translator theorem now yields a unique simultaneous solution,
not only an in-order execution. No leaf restriction or recursive premise. -/
theorem translateExprToWire_settled {ctx : CompilerState}
    {we : Sparkle.IR.Semantics.WEnv} {mems : Sparkle.IR.Semantics.MEnv}
    {initial env0 : Sparkle.IR.Semantics.Env} {s t : CircuitState}
    {e : Lean.Expr} {hint : String} {named : Bool} {result : String}
    {ρ : Valuation} {n : Nat} {x : BitVec n}
    (hd : Denotes ρ e n x)
    (h : Returns (translateExprToWire e hint false named) ctx s result t)
    (hi : Inv ctx ρ we mems initial s env0) (ho : OrderInv s) (hw : WidthsAgree we t) :
    ∃ env, Tools.ShippingSettledSoundness.IREquations we t.module.finalize.body env ∧
      Tools.ShippingSettledSoundness.ExternalValues t.module.finalize.body initial env ∧
      env result = x.toNat ∧
      ∀ other, Tools.ShippingSettledSoundness.IREquations we t.module.finalize.body other →
        Tools.ShippingSettledSoundness.ExternalValues t.module.finalize.body initial other → other = env := by
  obtain ⟨env, hinv, _, _, _, hval⟩ := translateExprToWire_sound hd h hi hw
  have ha : Tools.ShippingSettledSoundness.Acyclic t.module.finalize.body :=
    (translateExprToWire_orders _ _ _ _ _ _ _ _ _ hd h hi hw ho).1
  have hq := Tools.ShippingSettledSoundness.assign_equations ha hinv.runs
  have hx := Tools.ShippingSettledSoundness.assign_frame ha hinv.runs
  exact ⟨env, hq, hx, hval, fun other hq' hx' =>
    Tools.ShippingSettledSoundness.equations_unique ha hq' hx' hq hx⟩

end Tools.ShippingPendingSoundness

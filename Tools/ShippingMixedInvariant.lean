import Tools.ShippingBoolMuxSoundness

/-! Joint Bool/BitVec state invariant. In particular, writing a Bool cache record
must preserve BitVec records too (and conversely). This is infrastructure for
mixed recursive translation, not yet a closed source-to-RTL theorem. -/
namespace Tools.ShippingMixedInvariant
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingBoolSourceSoundness
open Tools.ShippingMuxRecursionSoundness Tools.ShippingCompareLoweringSoundness
open Tools.ShippingBoolLiteralSoundness Tools.ShippingBoolMuxSoundness
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingMuxLoweringSoundness Tools.ShippingTypedExprSoundness

/-- A source variable cannot simultaneously be a Bool and a BitVec input. -/
def Separate (ρ : BoolValuation) (β : Valuation) : Prop :=
  ∀ id b, ρ id = some b → β id = none

/-- The two source relations cannot assign competing widths to one record. -/
theorem denotes_disjoint {ρ β e b n} {x : BitVec n} (sep : Separate ρ β)
    (hb : BoolDenotes ρ β e b) (hv : Denotes β e n x) : False := by
  cases hb with
  | fvar hr =>
    cases hv with
    | fvar hv => rw [sep _ _ hr] at hv; cases hv
    | binary hf _ _ _ _ _ | pureLit hf _ _ => simp [Lean.Expr.getAppFn] at hf
  | pureLit hf hl =>
    cases hv with
    | fvar _ => simp [Lean.Expr.getAppFn] at hf
    | binary hf' hop _ _ _ _ =>
      rw [hf] at hf'; cases hf'
      simp [signalBinOpOf] at hop
    | pureLit _ hl' hv =>
      rw [hl] at hl'; cases hl'
      cases b <;> simp [bitVecLitValue?] at hv
  | compare le hf _ _ =>
    cases hv with
    | fvar _ => simp [Lean.Expr.getAppFn] at hf
    | binary hf' hop _ _ _ _ =>
      rw [hf] at hf'; cases hf'
      cases le <;> simp [compareName, signalBinOpOf] at hop
    | pureLit hf' _ _ => cases le <;> simp_all [compareName]
  | mux hf _ _ _ =>
    cases hv with
    | fvar _ => simp [Lean.Expr.getAppFn] at hf
    | binary hf' hop _ _ _ _ =>
      rw [hf] at hf'; cases hf'
      simp [signalBinOpOf] at hop
    | pureLit hf' _ _ => simp_all

structure Records (ρ : BoolValuation) (β : Valuation) (we : WEnv)
    (s : CircuitState) (env : Env) : Prop where
  bool : BoolRecordOk ρ β we s env
  bits : RecordOk β we s env

theorem Records.transfer {ρ β we s t env env'} (h : Records ρ β we s env)
    (hr : t.translateRecord = s.translateRecord)
    (hu : ∀ w, s.usedNames.contains w = true → t.usedNames.contains w = true)
    (hv : ∀ w, s.usedNames.contains w = true → env' w = env w) :
    Records ρ β we t env' := by
  refine ⟨h.bool.transfer hr hu hv, ?_⟩
  intro w e he n x hd
  rw [hr] at he
  obtain ⟨used, val, width⟩ := h.bits w e he n x hd
  exact ⟨hu w used, (hv w used).trans val, width⟩

theorem Records.insert_bool {ρ β we s env e w b} (sep : Separate ρ β)
    (h : Records ρ β we s env) (hd : BoolDenotes ρ β e b)
    (hu : s.usedNames.contains w = true) (hv : env w = encodeBool b) (hw : we w = 1) :
    Records ρ β we {s with translateRecord := s.translateRecord.insert w e} env := by
  refine ⟨h.bool.insert hd hu hv hw, ?_⟩
  intro w' e' he n x hx
  simp only [Std.HashMap.get?_insert] at he
  split at he
  · cases he; exact (denotes_disjoint sep hd hx).elim
  · exact h.bits w' e' he n x hx

theorem Records.insert_bits {ρ β we s env e w n} {x : BitVec n} (sep : Separate ρ β)
    (h : Records ρ β we s env) (hd : Denotes β e n x)
    (hu : s.usedNames.contains w = true) (hv : env w = x.toNat) (hw : we w = n) :
    Records ρ β we {s with translateRecord := s.translateRecord.insert w e} env := by
  refine ⟨?_, h.bits.insert hd hu hv hw⟩
  intro w' e' he b hb
  simp only [Std.HashMap.get?_insert] at he
  split at he
  · cases he; exact (denotes_disjoint sep hb hd).elim
  · exact h.bool w' e' he b hb

/-- Both input families use the actual scoped/persistent lookup. -/
structure Inputs (ctx : CompilerState) (ρ : BoolValuation) (β : Valuation)
    (we : WEnv) (s : CircuitState) (env : Env) : Prop where
  bool : ∀ id b, ρ id = some b → ∃ w, visible ctx s.sourceBindings id = some w ∧
    s.usedNames.contains w = true ∧ env w = encodeBool b ∧ we w = 1
  lookup : BoundLookup ctx β s
  values : BoundValues ctx β we s env

theorem Inputs.transfer {ctx ρ β we s t env env'} (h : Inputs ctx ρ β we s env)
    (hb : t.sourceBindings = s.sourceBindings)
    (hu : ∀ w, s.usedNames.contains w = true → t.usedNames.contains w = true)
    (hv : ∀ w, s.usedNames.contains w = true → env' w = env w) :
    Inputs ctx ρ β we t env' := by
  refine ⟨?_, h.lookup.transfer hu hb, ?_⟩
  · intro id b he
    obtain ⟨w, hw, used, val, width⟩ := h.bool id b he
    exact ⟨w, by rw [hb]; exact hw, hu w used, (hv w used).trans val, width⟩
  · intro id n x w he hw
    rw [hb] at hw
    obtain ⟨v, hv', used⟩ := h.lookup id n x he
    have eq : v = w := Option.some.inj (hv'.symm.trans hw)
    subst v
    obtain ⟨val, width⟩ := h.values id n x w he hw
    exact ⟨(hv w used).trans val, width⟩

/-- Typed bodies admit comparisons and muxes, unlike the old `SizedBody`. -/
structure MixedInv (ctx : CompilerState) (ρ : BoolValuation) (β : Valuation)
    (we : WEnv) (mems : MEnv) (initial : Env) (s : CircuitState) (env : Env) : Prop where
  separate : Separate ρ β
  runs : Runs we mems initial s env
  inputs : Inputs ctx ρ β we s env
  records : Records ρ β we s env
  typed : TypedBody we s

theorem MixedInv.transfer {ctx ρ β we mems initial s t env env'}
    (h : MixedInv ctx ρ β we mems initial s env)
    (run : Runs we mems initial t env') (typed : TypedBody we t)
    (hb : t.sourceBindings = s.sourceBindings) (hr : t.translateRecord = s.translateRecord)
    (hu : ∀ w, s.usedNames.contains w = true → t.usedNames.contains w = true)
    (hv : ∀ w, s.usedNames.contains w = true → env' w = env w) :
    MixedInv ctx ρ β we mems initial t env' :=
  ⟨h.separate, run, h.inputs.transfer hb hu hv, h.records.transfer hr hu hv, typed⟩

/-- The actual record write preserves both kinds of meaning, independent of
whether the optional mutable cache is enabled. -/
theorem recordTranslation_mixed_bool {ctx ρ β we mems initial s t env e w b cacheable u}
    (h : MixedInv ctx ρ β we mems initial s env) (hd : BoolDenotes ρ β e b)
    (hu : s.usedNames.contains w = true) (hv : env w = encodeBool b) (hw : we w = 1)
    (hr : Returns (recordTranslation e w cacheable) ctx s u t) :
    MixedInv ctx ρ β we mems initial t env := by
  rw [recordTranslation_returns hr]
  exact ⟨h.separate, h.runs, ⟨h.inputs.bool, h.inputs.lookup, h.inputs.values⟩, h.records.insert_bool h.separate hd hu hv hw, h.typed⟩

theorem recordTranslation_mixed_bits {ctx ρ β we mems initial s t env e w n cacheable u}
    {x : BitVec n} (h : MixedInv ctx ρ β we mems initial s env) (hd : Denotes β e n x)
    (hu : s.usedNames.contains w = true) (hv : env w = x.toNat) (hw : we w = n)
    (hr : Returns (recordTranslation e w cacheable) ctx s u t) :
    MixedInv ctx ρ β we mems initial t env := by
  rw [recordTranslation_returns hr]
  exact ⟨h.separate, h.runs, ⟨h.inputs.bool, h.inputs.lookup, h.inputs.values⟩, h.records.insert_bits h.separate hd hu hv hw, h.typed⟩

/-- Uniform semantic result for either source type, retaining both invariants. -/
structure Outcome (ctx : CompilerState) (ρ : BoolValuation) (β : Valuation)
    (we : WEnv) (mems : MEnv) (initial prior : Env) (s t : CircuitState)
    (w : String) (width value : Nat) : Prop where
  used : t.usedNames.contains w = true
  width_eq : we w = width
  grows : ∀ z, s.usedNames.contains z = true → t.usedNames.contains z = true
  execution : ∃ result, MixedInv ctx ρ β we mems initial t result ∧ result w = value ∧
    (∀ z, s.usedNames.contains z = true → result z = prior z)

/-- Shared Bool emission preserves the joint invariant, including BitVec
inputs and records. This applies to literals, comparisons and Bool muxes. -/
theorem emitBoolResult_mixed {ctx ρ β we mems initial s t prior rhs hint named w b}
    (h : MixedInv ctx ρ β we mems initial s prior)
    (typed : TypedExpr we rhs 1) (value : evalExpr we prior rhs = some (encodeBool b))
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (emitBoolResult rhs hint named) ctx s w t) :
    Outcome ctx ρ β we mems initial prior s t w 1 (encodeBool b) := by
  have step := emitBoolResult_correct hr h.runs h.records.bool h.typed typed value widths
  obtain ⟨result, run, _, val, frame⟩ := step.execution
  obtain ⟨_, state⟩ := emitBoolResult_returns hr
  have bindings : t.sourceBindings = s.sourceBindings := by
    rw [state, emitAssign_sourceBindings, CircuitM.makeWire_sourceBindings]
  have records : t.translateRecord = s.translateRecord := by
    rw [state, emitAssign_translateRecord, CircuitM.makeWire_translateRecord]
  exact ⟨step.used, step.width, step.grows, result,
    h.transfer run step.typed bindings records step.grows frame, val, frame⟩

theorem mixed_bool_hit {ctx ρ β we mems initial s t prior e w b}
    (h : MixedInv ctx ρ β we mems initial s prior) (hd : BoolDenotes ρ β e b)
    (hr : Returns (cacheLookupValidated e) ctx s (some w) t) :
    Outcome ctx ρ β we mems initial prior s t w 1 (encodeBool b) := by
  obtain ⟨hs, used, val, width⟩ := validatedBoolHit_correct h.records.bool hd hr
  subst t
  exact ⟨used, width, fun _ hz => hz, prior, h, val, fun _ _ => rfl⟩

theorem translateFallback_literal_mixed {ctx ρ β we mems initial s t prior dom hint named top w}
    (rec : TranslateFn) (b : Bool) (h : MixedInv ctx ρ β we mems initial s prior)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateFallback rec (literalE dom b) hint top named) ctx s w t) :
    Outcome ctx ρ β we mems initial prior s t w 1 (encodeBool b) := by
  have hd := BoolDenotes.quotePure (ρ := ρ) (β := β) dom b
  rw [translateFallback_bool rec _ hint top named (by cases b <;> rfl)] at hr
  rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
  · exact mixed_bool_hit h hd hit
  · rw [literal_uncached] at miss
    have hs := recordTranslation_returns record
    have wm : ScalarWidthsAgree we sm := by intro p hp; apply widths p; rw [hs]; exact hp
    have ev : evalExpr we prior (.const (if b then 1 else 0) 1) = some (encodeBool b) := by
      have he := evalExpr_const_lt we prior (encodeBool b) 1 (encodeBool_lt b)
      cases b <;> simpa [encodeBool] using he
    have step := emitBoolResult_mixed h (.const _ 1 (by decide)) ev wm miss
    obtain ⟨result, inv, val, frame⟩ := step.execution
    refine ⟨?_, step.width_eq, ?_, result,
      recordTranslation_mixed_bool inv hd step.used val step.width_eq record, val, frame⟩
    · rw [hs]; exact step.used
    · rw [hs]; exact step.grows

/-- Literal leaves now preserve the invariant required by *mixed* parents,
through both actual cache layers. No child translation premise is needed. -/
theorem translateStep_literal_mixed {ctx ρ β we mems initial s t prior dom hint named top w}
    (rec : TranslateFn) (b : Bool) (h : MixedInv ctx ρ β we mems initial s prior)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateStepWith translateFallback rec (literalE dom b) hint top named) ctx s w t) :
    Outcome ctx ρ β we mems initial prior s t w 1 (encodeBool b) := by
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
    have hs := (cacheLookupValidated_returns rh).1
    subst sh
    split at hr
    · obtain ⟨hw, hs'⟩ := Returns.pure hr
      subst w t
      exact mixed_bool_hit h (BoolDenotes.quotePure dom b) rh
    · rw [literal_core] at hr
      obtain ⟨v, sc, rv, hr⟩ := Returns.bind hr
      obtain ⟨hv, hs⟩ := Returns.pure rv
      subst v sc
      exact translateFallback_literal_mixed rec b h widths hr
  · rw [literal_core] at hr
    obtain ⟨v, sc, rv, hr⟩ := Returns.bind hr
    obtain ⟨hv, hs⟩ := Returns.pure rv
    subst v sc
    exact translateFallback_literal_mixed rec b h widths hr

theorem translateExprToWire_literal_mixed {ctx ρ β we mems initial s t prior dom hint named top w}
    (b : Bool) (h : MixedInv ctx ρ β we mems initial s prior)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateExprToWire (literalE dom b) hint top named) ctx s w t) :
    Outcome ctx ρ β we mems initial prior s t w 1 (encodeBool b) := by
  change Returns (translateStepWith translateFallback
    (translateFuelFix translateStep (translateFuelLimit - 1)) (literalE dom b) hint top named) ctx s w t at hr
  exact translateStep_literal_mixed _ b h widths hr

/-- Mixed-invariant composition for the real three-child Bool mux sequence. -/
theorem translateBoolMux_mixed {ctx ρ β we mems initial s t prior rec ce ae be hint named w}
    (c a b : Bool) (h : MixedInv ctx ρ β we mems initial s prior)
    (hc : ChildSpec rec ctx we mems initial (MixedInv ctx ρ β we mems initial)
      ce "mux_cond" 1 (encodeBool c))
    (ha : ChildSpec rec ctx we mems initial (MixedInv ctx ρ β we mems initial)
      ae "mux_then" 1 (encodeBool a))
    (hb : ChildSpec rec ctx we mems initial (MixedInv ctx ρ β we mems initial)
      be "mux_else" 1 (encodeBool b))
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateMuxWith rec (pure .bit) ce ae be hint named) ctx s w t) :
    Outcome ctx ρ β we mems initial prior s t w 1 (encodeBool (if c then a else b)) := by
  obtain ⟨cw, aw, bw, sc, sa, sb, sq, ty, rc, ra, rb, rq, re⟩ := translateMuxWith_returns hr
  obtain ⟨hty, hsq⟩ := Returns.pure rq
  subst ty sq
  obtain ⟨vc, gc, ec, uc, wc, cv, mc, fc⟩ := hc s sc cw prior h h.runs rc
  obtain ⟨va, ga, ea, ua, wa, av, ma, fa⟩ := ha sc sa aw vc gc ec ra
  obtain ⟨vb, gb, eb, ub, wb, bv, mb, fb⟩ := hb sa sb bw va ga ea rb
  have cv' : vb cw = encodeBool c := (fb cw (ma cw uc)).trans ((fa cw uc).trans cv)
  have av' : vb aw = encodeBool a := (fb aw ua).trans av
  have step := emitBoolResult_mixed gb
    (.mux (wc ▸ TypedExpr.ref (we := we) cw (by omega))
      (wa ▸ TypedExpr.ref (we := we) aw (by omega))
      (wb ▸ TypedExpr.ref (we := we) bw (by omega)))
    (bool_mux_rhs we vb cw aw bw c a b cv' av' bv) widths re
  have mono : ∀ z, s.usedNames.contains z = true → sb.usedNames.contains z = true :=
    fun z hz => mb z (ma z (mc z hz))
  obtain ⟨result, inv, val, frame⟩ := step.execution
  exact ⟨step.used, step.width_eq, fun z hz => step.grows z (mono z hz), result, inv, val,
    fun z hz => (frame z (mono z hz)).trans ((fb z (ma z (mc z hz))).trans
      ((fa z (mc z hz)).trans (fc z hz)))⟩

/-- The validated-cache wrapper composes with *joint* preservation, rather
than discarding the BitVec half after a successful Bool translation. -/
theorem translateControlCachedWith_mixed {ctx ρ β we mems initial s t prior lower e hint top named w b}
    (h : MixedInv ctx ρ β we mems initial s prior) (hd : BoolDenotes ρ β e b)
    (widths : ScalarWidthsAgree we t)
    (node : ∀ sm r, ScalarWidthsAgree we sm → Returns (lower e hint top named) ctx s r sm →
      Outcome ctx ρ β we mems initial prior s sm r 1 (encodeBool b))
    (hr : Returns (translateControlCachedWith lower e hint top named) ctx s w t) :
    Outcome ctx ρ β we mems initial prior s t w 1 (encodeBool b) := by
  rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
  · exact mixed_bool_hit h hd hit
  · have hs := recordTranslation_returns record
    have wm : ScalarWidthsAgree we sm := by intro p hp; apply widths p; rw [hs]; exact hp
    have step := node sm w wm miss
    obtain ⟨result, inv, val, frame⟩ := step.execution
    refine ⟨?_, step.width_eq, ?_, result,
      recordTranslation_mixed_bool inv hd step.used val step.width_eq record, val, frame⟩
    · rw [hs]; exact step.used
    · rw [hs]; exact step.grows

theorem translateFallback_boolMux_mixed {ctx ρ β we mems initial s t prior rec dom ce ae be hint named top w}
    (c a b : Bool) (h : MixedInv ctx ρ β we mems initial s prior)
    (dc : BoolDenotes ρ β ce c) (da : BoolDenotes ρ β ae a) (db : BoolDenotes ρ β be b)
    (hc : ChildSpec rec ctx we mems initial (MixedInv ctx ρ β we mems initial)
      ce "mux_cond" 1 (encodeBool c))
    (ha : ChildSpec rec ctx we mems initial (MixedInv ctx ρ β we mems initial)
      ae "mux_then" 1 (encodeBool a))
    (hb : ChildSpec rec ctx we mems initial (MixedInv ctx ρ β we mems initial)
      be "mux_else" 1 (encodeBool b))
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateFallback rec (boolMuxE dom ce ae be) hint top named) ctx s w t) :
    Outcome ctx ρ β we mems initial prior s t w 1 (encodeBool (if c then a else b)) := by
  rw [translateFallback_bool rec _ hint top named rfl] at hr
  apply translateControlCachedWith_mixed h (BoolDenotes.quoteMux dom ce ae be dc da db) widths ?_ hr
  intro sm r wm miss
  change Returns (translateMuxWith rec (pure .bit) ce ae be hint named) ctx s r sm at miss
  exact translateBoolMux_mixed c a b h hc ha hb wm miss

/-- The real fvar step returns the existing binding without recording it. -/
theorem translateStep_fvar_returns {ctx s t id rec hint top named w v}
    (bound : visible ctx s.sourceBindings id = some v)
    (hr : Returns (translateStepWith translateFallback rec (.fvar id) hint top named) ctx s w t) :
    w = v ∧ t = s := by
  unfold translateStepWith at hr
  simp only [Lean.Expr.isFVar, Bool.not_true, Bool.and_false, Bool.false_and,
    Bool.false_eq_true, if_false] at hr
  obtain ⟨r, sc, core, k⟩ := Returns.bind hr
  obtain ⟨hr, hs⟩ := lookupVar_returns (id := id) core
  rw [bound] at hr
  rw [hr] at k
  obtain ⟨hw, ht⟩ := Returns.pure k
  exact ⟨hw, ht.trans hs⟩

theorem translateStep_bool_input_mixed {ctx ρ β we mems initial s t prior rec id hint top named w b}
    (h : MixedInv ctx ρ β we mems initial s prior) (value : ρ id = some b)
    (hr : Returns (translateStepWith translateFallback rec (.fvar id) hint top named) ctx s w t) :
    Outcome ctx ρ β we mems initial prior s t w 1 (encodeBool b) := by
  obtain ⟨v, bound, used, val, width⟩ := h.inputs.bool id b value
  obtain ⟨hw, ht⟩ := translateStep_fvar_returns bound hr
  subst w t
  exact ⟨used, width, fun _ hz => hz, prior, h, val, fun _ _ => rfl⟩

theorem translateStep_bits_input_mixed {ctx ρ β we mems initial s t prior rec id hint top named w n}
    {x : BitVec n} (h : MixedInv ctx ρ β we mems initial s prior) (value : β id = some ⟨n, x⟩)
    (hr : Returns (translateStepWith translateFallback rec (.fvar id) hint top named) ctx s w t) :
    Outcome ctx ρ β we mems initial prior s t w n x.toNat := by
  obtain ⟨v, bound, used⟩ := h.inputs.lookup id n x value
  obtain ⟨val, width⟩ := h.inputs.values id n x v value bound
  obtain ⟨hw, ht⟩ := translateStep_fvar_returns bound hr
  subst w t
  exact ⟨used, width, fun _ hz => hz, prior, h, val, fun _ _ => rfl⟩

/-- Comparison operands can retain Bool records while producing BitVec values;
the comparison result then preserves those BitVec records as well. -/
theorem translateUnsignedCompare_mixed {ctx ρ β we mems initial s t prior rec ae be hint named w le n}
    (x y : BitVec n) (hn : 0 < n) (h : MixedInv ctx ρ β we mems initial s prior)
    (ha : ChildSpec rec ctx we mems initial (MixedInv ctx ρ β we mems initial) ae "a" n x.toNat)
    (hb : ChildSpec rec ctx we mems initial (MixedInv ctx ρ β we mems initial) be "b" n y.toNat)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateUnsignedCompare rec le ae be hint named) ctx s w t) :
    Outcome ctx ρ β we mems initial prior s t w 1 (encodeBool (compareValue le x y)) := by
  obtain ⟨aw, bw, sa, sb, ra, rb, re⟩ := translateUnsignedCompare_returns hr
  obtain ⟨va, ga, ea, ua, wa, xa, ma, fa⟩ := ha s sa aw prior h h.runs ra
  obtain ⟨vb, gb, eb, ub, wb, yb, mb, fb⟩ := hb sa sb bw va ga ea rb
  have xb : vb aw = x.toNat := (fb aw ua).trans xa
  have step := emitBoolResult_mixed gb
    (.compare (n := n) (by cases le <;> rfl)
      (wa ▸ TypedExpr.ref (we := we) aw (by omega))
      (wb ▸ TypedExpr.ref (we := we) bw (by omega)))
    (compare_rhs_correct le x y we vb aw bw xb yb) widths re
  obtain ⟨result, inv, val, frame⟩ := step.execution
  exact ⟨step.used, step.width_eq, fun z hz => step.grows z (mb z (ma z hz)), result, inv, val,
    fun z hz => (frame z (mb z (ma z hz))).trans ((fb z (ma z hz)).trans (fa z hz))⟩

theorem translateFallback_compare_mixed {ctx ρ β we mems initial s t prior rec dom ae be hint named top w le n}
    (x y : BitVec n) (hn : 0 < n) (h : MixedInv ctx ρ β we mems initial s prior)
    (da : Denotes β ae n x) (db : Denotes β be n y)
    (ha : ChildSpec rec ctx we mems initial (MixedInv ctx ρ β we mems initial) ae "a" n x.toNat)
    (hb : ChildSpec rec ctx we mems initial (MixedInv ctx ρ β we mems initial) be "b" n y.toNat)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateFallback rec
      (mkApp4 (.const (compareName le) []) dom (Tools.ShippingEntrySoundness.natE n) ae be)
      hint top named) ctx s w t) :
    Outcome ctx ρ β we mems initial prior s t w 1 (encodeBool (compareValue le x y)) := by
  rw [translateFallback_bool rec _ hint top named (by cases le <;> rfl)] at hr
  apply translateControlCachedWith_mixed h (BoolDenotes.quoteCompare dom ae be le da db) widths ?_ hr
  intro sm r wm miss
  rw [translateBoolUncachedWith_compare] at miss
  exact translateUnsignedCompare_mixed x y hn h ha hb wm miss

end Tools.ShippingMixedInvariant

import Tools.ShippingUnifiedCache

/-! State invariant for the mutual source domain. The actual cache wrapper
preserves execution, typed assignments, input values and all live wires once
its uncached handler satisfies the same contract. Closing that recursive
handler contract and the entry/output connection remains separate work. -/
namespace Tools.ShippingUnifiedInvariant
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedMeaning Tools.ShippingUnifiedCache
open Tools.ShippingTranslateSoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingBindingsSoundness Tools.ShippingScalarSoundness
open Tools.ShippingMuxRecursionSoundness
open Tools.ShippingLinkCtx

set_option linter.unusedSectionVars false

variable [LinkCtx] [ChildSem]

structure Inputs (ctx : CompilerState) (inputs : FVarId → Option Value)
    (we : WEnv) (s : CircuitState) (env : Env) : Prop where
  lookup : ∀ id v, inputs id = some v → ∃ w, visible ctx s.sourceBindings id = some w ∧
    s.usedNames.contains w = true ∧ env w = v.toNat ∧ we w = v.kind.width

theorem Inputs.transfer {ctx inputs we s t env env'} (h : Inputs ctx inputs we s env)
    (hb : t.sourceBindings = s.sourceBindings)
    (hu : ∀ w, s.usedNames.contains w = true → t.usedNames.contains w = true)
    (hv : ∀ w, s.usedNames.contains w = true → env' w = env w) : Inputs ctx inputs we t env' := by
  constructor
  intro id v hi
  obtain ⟨w, bound, used, value, width⟩ := h.lookup id v hi
  exact ⟨w, by rw [hb]; exact bound, hu w used, (hv w used).trans value, width⟩

structure Inv (ctx : CompilerState) (valuation : FVarId → Option Value)
    (we : WEnv) (mems : MEnv) (initial : Env) (s : CircuitState) (env : Env) : Prop where
  runs : LinkCtx.Runs we mems initial s env
  inputs : Inputs ctx valuation we s env
  records : Records valuation we s env
  typed : LinkCtx.Typed we s

theorem Inv.transfer {ctx inputs we mems initial s t env env'}
    (h : Inv ctx inputs we mems initial s env)
    (run : LinkCtx.Runs we mems initial t env') (typed : LinkCtx.Typed we t)
    (hb : t.sourceBindings = s.sourceBindings) (hr : t.translateRecord = s.translateRecord)
    (hu : ∀ w, s.usedNames.contains w = true → t.usedNames.contains w = true)
    (hv : ∀ w, s.usedNames.contains w = true → env' w = env w) :
    Inv ctx inputs we mems initial t env' :=
  ⟨run, h.inputs.transfer hb hu hv, h.records.transfer hr hu hv, typed⟩

theorem Inv.record {ctx inputs we mems initial s t env e w v cacheable u}
    (h : Inv ctx inputs we mems initial s env) (meaning : Meaning inputs e v)
    (used : s.usedNames.contains w = true) (value : env w = v.toNat) (width : we w = v.kind.width)
    (hr : Returns (recordTranslation e w cacheable) ctx s u t) : Inv ctx inputs we mems initial t env := by
  have record := record_preserves h.records meaning used value width hr
  rw [recordTranslation_returns hr] at record ⊢
  exact ⟨LinkCtx.runs_body (s := s) rfl h.runs, ⟨h.inputs.lookup⟩, record,
    LinkCtx.typed_body (s := s) rfl (fun _ hq => hq) (fun _ hq => hq) h.typed⟩

/-- Includes the live-wire frame needed when a later child refers to an earlier
child's result, and when arithmetic reserves its parent name before children. -/
structure Outcome (ctx : CompilerState) (inputs : FVarId → Option Value)
    (we : WEnv) (mems : MEnv) (initial prior : Env) (s t : CircuitState)
    (w : String) (v : Value) : Prop where
  used : t.usedNames.contains w = true
  width : we w = v.kind.width
  grows : ∀ z, s.usedNames.contains z = true → t.usedNames.contains z = true
  execution : ∃ result, Inv ctx inputs we mems initial t result ∧ result w = v.toNat ∧
    (∀ z, s.usedNames.contains z = true → result z = prior z)

theorem hit_outcome {ctx inputs we mems initial s t prior e w v}
    (h : Inv ctx inputs we mems initial s prior) (meaning : Meaning inputs e v)
    (hr : Returns (cacheLookupValidated e) ctx s (some w) t) :
    Outcome ctx inputs we mems initial prior s t w v := by
  obtain ⟨state, used, value, width⟩ := validated_hit h.records meaning hr
  subst t
  exact ⟨used, width, fun _ hu => hu, prior, h, value, fun _ _ => rfl⟩

theorem cached_outcome {ctx inputs we mems initial s t prior e w v lower hint top named}
    (h : Inv ctx inputs we mems initial s prior) (meaning : Meaning inputs e v)
    (miss : ∀ sm wm, Returns (lower e hint top named) ctx s wm sm →
      Outcome ctx inputs we mems initial prior s sm wm v)
    (hr : Returns (translateControlCachedWith lower e hint top named) ctx s w t) :
    Outcome ctx inputs we mems initial prior s t w v := by
  rcases Tools.ShippingBoolSourceSoundness.translateControlCachedWith_returns hr with hit | ⟨sm, lower, record⟩
  · exact hit_outcome h meaning hit
  · have step := miss sm w lower
    obtain ⟨result, invariant, value, frame⟩ := step.execution
    refine ⟨?_, step.width, ?_, result, invariant.record meaning step.used value step.width record, value, frame⟩
    · rw [recordTranslation_returns record]; exact step.used
    · rw [recordTranslation_returns record]; exact step.grows

/-- The existing prepared input invariant supplies the stronger source lookup
without asking callers for another valuation or a type oracle. -/
theorem Inputs.of_mixed {ctx ρ β we s env}
    (h : Tools.ShippingMixedInvariant.Inputs ctx ρ β we s env) :
    Inputs ctx (inputValues ρ β) we s env := by
  constructor
  intro id v hi
  unfold inputValues at hi
  cases hb : ρ id with
  | some b =>
    simp only [hb] at hi
    cases hi
    exact h.bool id b hb
  | none =>
    simp only [hb] at hi
    cases hv : β id with
    | none => simp [hv] at hi
    | some value =>
      obtain ⟨n, x⟩ := value
      simp only [hv, Option.map_some, Option.some.injEq] at hi
      subst v
      obtain ⟨w, bound, used⟩ := h.lookup id n x hv
      obtain ⟨value, width⟩ := h.values id n x w hv bound
      exact ⟨w, bound, used, value, width⟩

open Tools.ShippingBuilderSoundness

theorem Inv.allocate {ctx inputs we mems initial s env}
    (h : Inv ctx inputs we mems initial s env) (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    Inv ctx inputs we mems initial (CircuitM.makeWire hint ty named s).2 env := by
  have hm := CircuitM.makeWire_spec hint ty named s
  apply h.transfer (LinkCtx.runs_body hm.2.2.1 h.runs)
    (LinkCtx.typed_body hm.2.2.1
      (fun q hq => by rw [hm.2.2.2]; exact List.mem_cons_of_mem _ hq)
      (fun q hq => by rw [makeWire_inputs]; exact hq) h.typed)
    (CircuitM.makeWire_sourceBindings _ _ _ _) (CircuitM.makeWire_translateRecord _ _ _ _)
  · intro w used
    rw [hm.2.1]
    simp [Std.HashSet.contains_insert, used]
  · intro w used; rfl

/-- Covers the parent's final assignment after reserving its name and
recursively generating children. The remaining recursive proof must preserve
these no-alias/no-record facts across those children. -/
theorem Inv.emit_reserved {ctx inputs we mems initial s prior w rhs value}
    (h : Inv ctx inputs we mems initial s prior)
    (inputSafe : ∀ id v, inputs id = some v → visible ctx s.sourceBindings id ≠ some w)
    (recordSafe : ∀ e v, s.translateRecord.get? w = some e → ¬ Meaning inputs e v)
    (typed : TypedExpr we rhs (we w)) (ev : evalExpr we prior rhs = some value) :
    Inv ctx inputs we mems initial (CircuitM.emitAssign w rhs s).2 (write prior w value) := by
  refine ⟨LinkCtx.runs_emit h.runs ev, ⟨?_⟩, ?_, LinkCtx.typed_emit h.typed typed⟩
  · intro id v hi
    obtain ⟨z, bound, used, val, width⟩ := h.inputs.lookup id v hi
    have ne : z ≠ w := by intro eq; subst z; exact inputSafe id v hi bound
    exact ⟨z, bound, used, by simpa [write, ne] using val, width⟩
  · intro z e record v meaning
    have ne : z ≠ w := by intro eq; subst z; exact recordSafe e v record meaning
    obtain ⟨used, val, width⟩ := h.records z e record v meaning
    exact ⟨used, by simpa [write, ne] using val, width⟩

end Tools.ShippingUnifiedInvariant

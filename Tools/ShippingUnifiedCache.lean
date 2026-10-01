import Tools.ShippingUnifiedMeaning

/-! Preservation of unified source meanings by the actual validated cache.
These lemmas close both hit and record-write obligations without an assumption
about the mutable ExprStructMap. They do not yet connect every recursive source
constructor to the compiler's synthesis/output endpoint. -/
namespace Tools.ShippingUnifiedCache
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedMeaning Tools.ShippingTranslateSoundness
open Tools.ShippingScalarSoundness

set_option linter.unusedSectionVars false

variable [ChildSem]

/-- One record invariant for both source sorts, including recursive mux values. -/
def Records (inputs : FVarId → Option Value) (we : WEnv) (s : CircuitState) (env : Env) : Prop :=
  ∀ w e, s.translateRecord.get? w = some e → ∀ v, Meaning inputs e v →
    s.usedNames.contains w = true ∧ env w = v.toNat ∧ we w = v.kind.width

theorem Records.empty {inputs we s env} (h : s.translateRecord = {}) : Records inputs we s env := by
  intro w e he
  simp [h] at he

theorem Records.transfer {inputs we s t env env'} (h : Records inputs we s env)
    (hr : t.translateRecord = s.translateRecord)
    (hu : ∀ w, s.usedNames.contains w = true → t.usedNames.contains w = true)
    (hv : ∀ w, s.usedNames.contains w = true → env' w = env w) : Records inputs we t env' := by
  intro w e he v meaning
  rw [hr] at he
  obtain ⟨used, value, width⟩ := h w e he v meaning
  exact ⟨hu w used, (hv w used).trans value, width⟩

theorem Records.insert {inputs we s env e w v} (h : Records inputs we s env)
    (meaning : Meaning inputs e v) (used : s.usedNames.contains w = true)
    (value : env w = v.toNat) (width : we w = v.kind.width) :
    Records inputs we {s with translateRecord := s.translateRecord.insert w e} env := by
  intro w' e' he v' meaning'
  simp only [Std.HashMap.get?_insert] at he
  split at he
  · rename_i same
    have same' : w = w' := by simpa only [beq_iff_eq] using same
    subst w'
    cases he
    have eq := meaning.deterministic meaning'
    subst v'
    exact ⟨used, value, width⟩
  · exact h w' e' he v' meaning'

/-- The state-side record is checked against the *requested* expression, so
mutable-cache collisions or stale entries need no external map law. -/
theorem validated_hit {inputs we ctx s t env e w v}
    (h : Records inputs we s env) (meaning : Meaning inputs e v)
    (hr : Returns (cacheLookupValidated e) ctx s (some w) t) :
    t = s ∧ t.usedNames.contains w = true ∧ env w = v.toNat ∧ we w = v.kind.width := by
  obtain ⟨state, record⟩ := cacheLookupValidated_returns hr
  obtain ⟨used, value, width⟩ := h w e (record w rfl) v meaning
  exact ⟨state, state ▸ used, value, width⟩

/-- The real record update preserves the invariant whether or not optional
mutable caching is enabled for this call. -/
theorem record_preserves {inputs we ctx s t env e w v cacheable u}
    (h : Records inputs we s env) (meaning : Meaning inputs e v)
    (used : s.usedNames.contains w = true) (value : env w = v.toNat) (width : we w = v.kind.width)
    (hr : Returns (recordTranslation e w cacheable) ctx s u t) : Records inputs we t env := by
  rw [recordTranslation_returns hr]
  exact h.insert meaning used value width

/-- A fresh emission cannot overwrite any wire carrying a unified source
meaning. This applies equally to new mux records and existing operators. -/
theorem Records.write_fresh {inputs we s env w value} (h : Records inputs we s env)
    (fresh : s.usedNames.contains w = false) : Records inputs we s (write env w value) := by
  apply h.transfer rfl (fun _ hu => hu)
  intro z hz
  have ne : z ≠ w := by intro eq; subst z; rw [fresh] at hz; cases hz
  simp [write, ne]

/-- A name fresh at the current state has no record with a known source meaning.
Protection after reserving a parent name is a separate recursive obligation. -/
theorem fresh_not_recorded {inputs we s env w e v} (h : Records inputs we s env)
    (fresh : s.usedNames.contains w = false) (meaning : Meaning inputs e v) :
    s.translateRecord.get? w ≠ some e := by
  intro record
  have used := (h w e record v meaning).1
  rw [fresh] at used
  cases used

/-- The existing cache wrapper also works for a unified meaning once its
uncached lowering preserves this stronger record invariant. That premise is
what the remaining recursive translation proof must establish. -/
theorem cached_action {inputs we ctx s t env e w v lower hint top named}
    (h : Records inputs we s env) (meaning : Meaning inputs e v)
    (miss : ∀ sm wm, Returns (lower e hint top named) ctx s wm sm →
      ∃ result, Records inputs we sm result ∧ sm.usedNames.contains wm = true ∧
        result wm = v.toNat ∧ we wm = v.kind.width)
    (hr : Returns (translateControlCachedWith lower e hint top named) ctx s w t) :
    ∃ result, Records inputs we t result ∧ t.usedNames.contains w = true ∧
      result w = v.toNat ∧ we w = v.kind.width := by
  rcases Tools.ShippingBoolSourceSoundness.translateControlCachedWith_returns hr with hit | ⟨sm, lower, record⟩
  · obtain ⟨state, used, val, width⟩ := validated_hit h meaning hit
    exact ⟨env, state ▸ h, used, val, width⟩
  · obtain ⟨result, invariant, used, val, width⟩ := miss sm w lower
    refine ⟨result, record_preserves invariant meaning used val width record, ?_, val, width⟩
    rw [recordTranslation_returns record]
    exact used

end Tools.ShippingUnifiedCache

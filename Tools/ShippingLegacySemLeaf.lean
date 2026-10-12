import Tools.ShippingLegacySemHarnessAt
import Tools.ShippingLegacySemEntryWalk

/-! # The entry's leaf at the flags the entry uses

`LegacyDom` (`Tools/ShippingLegacySemContract.lean`) gives `Contract` — every
hint, top flag and name flag — so its inline constructor asks its dispatch
premise at every flag. For a call at the CACHEABLE flags (`named = false ∧
top = false`) that premise is not provable today: the caching shim returns
an unvalidated hit there. The walked dispatch (`plain_call_reaches`) covers
the non-cacheable flags.

The entry translates its leaf at ONE flag setting: `emitLeaves` calls the
translator with `(portName, isTopLevel := false, isNamed := true)`, and the
inline attempt passes the hint and the name flag on to the unfolding. So the
leaf — and the unfoldings of the leaf, as long as they are calls again — are
only ever translated NAMED.

**Defined here**

* `ReachesUnfoldAt rec ctx e hint top named` — `ReachesUnfold` at one flag
  setting (what `plain_call_reaches` concludes).
* `LeafDom ctx inputs hint named` — the domain of a leaf translated at
  `(hint, false, named)`: an expression of `LegacyDom` (any flags), or a call
  the inline arm lowers AT THESE FLAGS whose unfoldings are leaves at the
  same flags.

**Proved here**

* `leaf_fuel_spec`, `leaf_fuel_order`, `leaf_translate_spec`,
  `leaf_translate_order` — `ActionSpec` and `ActionOrder` of the shipping
  translator on a `LeafDom` expression at its flags.
* `leaf_output` — the harness's output statement from a `LeafDom` leaf
  (`harness_sound_spec`).
* `leaf_entry_output_walked` — the entry's, from the walk
  (`legacy_entry_walk`).

**What `LeafDom` does not give**: a `Contract` (all flags). A `LeafDom`
expression that is not in `LegacyDom` cannot be used as a child of a
certified node (children are translated at `(hint, false, false)`, the
cacheable flags) — that case still needs the shim's hit validated. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedRecursion
open Tools.ShippingUnifiedProtection

/-- `ReachesUnfold` at one hint and flag setting. -/
def ReachesUnfoldAt (rec : TranslateFn) (ctx : CompilerState) (e : Lean.Expr) (hint : String)
    (top named : Bool) : Prop :=
  ∀ (s t : CircuitState) (w : String),
    Returns (translateFallback rec e hint top named) ctx s w t →
    ∃ e' : Lean.Expr, InlineUnfolds e e' ∧ Returns (rec e' hint false named) ctx s w t

theorem ReachesUnfold.atFlags {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    (h : ReachesUnfold rec ctx e) (hint : String) (top named : Bool) :
    ReachesUnfoldAt rec ctx e hint top named :=
  fun s t w hr => h hint top named s t w hr

/-- The domain of a leaf translated at `(hint, isTopLevel := false, named)`. -/
inductive LeafDom (ctx : CompilerState) (inputs : FVarId → Option Value) (hint : String)
    (named : Bool) : Lean.Expr → Value → Prop where
  | dom {e : Lean.Expr} {v : Value} : LegacyDom ctx inputs e v →
      LeafDom ctx inputs hint named e v
  | inlineAt {e : Lean.Expr} {v : Value} : NotCore e →
      (∀ rec : TranslateFn, ReachesUnfoldAt rec ctx e hint false named) →
      (∀ e' : Lean.Expr, InlineUnfolds e e' → LeafDom ctx inputs hint named e' v) →
      LeafDom ctx inputs hint named e v

/-- **Frame and outcome of a leaf at its flags, at every fuel.** -/
theorem leaf_fuel_spec {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {hint : String} {named : Bool}
    {e : Lean.Expr} {v : Value} (h : LeafDom ctx inputs hint named e v) :
    ∀ fuel : Nat, ActionSpec (translateFuelFix translateStep fuel e hint false named)
      ctx inputs we mems initial v := by
  induction h with
  | dom hd =>
    intro fuel
    have hc := legacy_fuel_contract (we := we) (mems := mems) (initial := initial) hd fuel
    exact ⟨hc.frame hint false named, hc.sem hint false named⟩
  | inlineAt nc reach _ ih =>
    intro fuel
    cases fuel with
    | zero =>
      constructor
      · intro s t w lookup hr; exact (Returns.throw hr).elim
      · intro s t w prior hinv widths hr; exact (Returns.throw hr).elim
    | succ fuel =>
      constructor
      · intro s t w lookup hr
        have hstep : Returns (translateStepWith translateFallback
            (translateFuelFix translateStep fuel) _ hint false named) ctx s w t := hr
        obtain ⟨e', hU, htr⟩ := reach _ s t w (step_run_fallback nc hstep)
        exact (ih e' hU fuel).frame s t w lookup htr
      · intro s t w prior hinv widths hr
        have hstep : Returns (translateStepWith translateFallback
            (translateFuelFix translateStep fuel) _ hint false named) ctx s w t := hr
        obtain ⟨e', hU, htr⟩ := reach _ s t w (step_run_fallback nc hstep)
        exact (ih e' hU fuel).sem s t w prior hinv widths htr

/-- **Order of a leaf at its flags, at every fuel.** -/
theorem leaf_fuel_order {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {hint : String} {named : Bool}
    {e : Lean.Expr} {v : Value} (h : LeafDom ctx inputs hint named e v) :
    ∀ fuel : Nat, ActionOrder (translateFuelFix translateStep fuel e hint false named)
      ctx inputs we mems initial := by
  induction h with
  | dom hd =>
    intro fuel
    exact legacy_fuel_order hd fuel hint named
  | inlineAt nc reach _ ih =>
    intro fuel
    cases fuel with
    | zero =>
      intro s t w prior hr hinv widths order
      exact (Returns.throw hr).elim
    | succ fuel =>
      intro s t w prior hr hinv widths order
      have hstep : Returns (translateStepWith translateFallback
          (translateFuelFix translateStep fuel) _ hint false named) ctx s w t := hr
      obtain ⟨e', hU, htr⟩ := reach _ s t w (step_run_fallback nc hstep)
      exact ih e' hU fuel s t w prior htr hinv widths order

/-- The shipping translator on a leaf at its flags: frame and outcome. -/
theorem leaf_translate_spec {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {hint : String} {named : Bool}
    {e : Lean.Expr} {v : Value} (h : LeafDom ctx inputs hint named e v) :
    ActionSpec (translateExprToWire e hint false named) ctx inputs we mems initial v :=
  leaf_fuel_spec h translateFuelLimit

/-- The shipping translator on a leaf at its flags: order. -/
theorem leaf_translate_order {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {hint : String} {named : Bool}
    {e : Lean.Expr} {v : Value} (h : LeafDom ctx inputs hint named e v) :
    ActionOrder (translateExprToWire e hint false named) ctx inputs we mems initial :=
  leaf_fuel_order h translateFuelLimit

/-- **The output of a leaf of `LeafDom`**: a run of the harness and the leaf
in the entry-flag domain. -/
theorem leaf_output {logProf : String → IO Unit} {declName : Name}
    {bs : List (Name × MixedGateBinder)} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {leaf : Lean.Expr} {returned : String}
    {st : CircuitState} {m : Sparkle.IR.AST.Module}
    (run : HarnessRun logProf declName bs ids cache leaf returned st)
    (hm : m = (addClockResetIfSequential st.module).finalize)
    (legal : Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true)
    (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) (mems : MEnv)
    (values : Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
      (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
        declName.toString))
    (v : Value) (pos : 0 < v.kind.width)
    (dom : LeafDom (setupOf declName bs ids cache bools bits).context
      (Tools.ShippingUnifiedMeaning.inputValues (setupOf declName bs ids cache bools bits).bools
        (setupOf declName bs ids cache bools bits).bits) "out" true leaf v) :
    Tools.ShippingMixedEntrySoundness.RawValueAt v.kind.width bs m initial mems v.toNat :=
  harness_sound_spec run hm legal bools bits initial mems values v pos
    (leaf_translate_spec dom) (leaf_translate_order dom)

/-- **The output of a legacy-route declaration, leaf at the entry flags.** As
`legacy_entry_output_walked`, with the leaf asked in `LeafDom … "out" true`
instead of `LegacyDom`. -/
theorem leaf_entry_output_walked {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Design} {cfe : Bool}
    (old : cfe = true → certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : cfe = true → mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : cfe = true → ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeSpec (stripMemoizeWrappers body0) (EntryFacts bs leafOf))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf declName [] false cfe (.defnInfo dv) isInst) (m, d)) :
    MemoHit declName m d ∨
    ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.Nodup ∧ ids.length = bs.length ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          declName.toString) →
      ∀ v : Value, 0 < v.kind.width →
      LeafDom (setupOf declName bs ids cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName bs ids cache bools bits).bools
          (setupOf declName bs ids cache bools bits).bits) "out" true (leafOf ids) v →
      Tools.ShippingMixedEntrySoundness.RawValueAt v.kind.width bs m initial mems v.toNat := by
  rcases legacy_entry_walk old mixed hmach htele hr with hit |
    ⟨body0, xs, inner, leaves, cache, returned, st, hopen, ⟨ids, nd, len, bw, hl⟩, hsplit,
      run, hm, legal⟩
  · exact Or.inl hit
  · refine Or.inr ⟨ids, cache, nd, len, ?_⟩
    intro bools bits initial mems values v pos dom
    rw [hl leaves hsplit] at run
    have run' : HarnessRun logProf declName bs ids cache (leafOf ids) returned st :=
      bw _ _ _ _ _ run
    exact leaf_output run' hm legal bools bits initial mems values v pos dom

end Tools.ShippingLegacySem

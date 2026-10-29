import Tools.ShippingMachineEntry
import Tools.ShippingMachineAuto
set_option autoImplicit false
-- BUILT: g2nm-eb60056f at eb60056f (exit 0); audited in g2sb-93e9994c.
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # S4 stage B: the two names lemmas behind `NamesEq`
(scripts/gen2/S4_STAGEB_FREEZE.md rev1 §1, §4; approved at a66699bb)

* `machPorts_names_indep`: the port NAMES of the binder walk depend on the declaration name and the
  binder list only, not on the fresh ids or on the wire cache (lengths equal). The allocator state
  moves by `extend`, which reads the binder's name and kind only (MixedEntrySoundness:25-38), and
  `start` sets it to `CircuitM.init` (MixedEntrySoundness:456-457); the ids and the cache reach only
  `context`, `bools`, `bits`.
* `ranA_inputs_machPorts`: on the harness run inside `MachineRanA` (its
  `MReturns synthesizeMixedCertified … (t, d₀)`), the transition module's inputs are the walk's ports
  for SOME ids/cache of the binders' length (`synthesizeMixedCertified_returns` + `transition_facts`,
  as at MachineEntry:1077-1081/1449; WF premises from `d.ok`, as at TransitionTyped:66-97).

Together: `t.inputs.map (·.name) = (machPorts c ids cache d.shape.binders).map (·.name)` for ANY
`ids` of the binders' length and any `cache` (freeze §1 `NamesEq`). -/
namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto

/-- **Port names are allocator-only**: two walks over the same binders with ids of the binders'
length (any ids, any caches) give the same port names. -/
theorem machPorts_names_indep (c : Name) {bs : List (Name × MixedGateBinder)} {ids ids' : List FVarId}
    (cache cache' : IO.Ref (ExprStructMap String))
    (hl : ids.length = bs.length) (hl' : ids'.length = bs.length) :
    (machPorts c ids cache bs).map (·.name) = (machPorts c ids' cache' bs).map (·.name) := by
  -- the walk itself (names AND types) agrees, from allocator states that agree
  have key : ∀ (bs : List (Name × MixedGateBinder)) (ids ids' : List FVarId)
      (a a' : Tools.ShippingMixedEntrySoundness.Setup),
      ids.length = bs.length → ids'.length = bs.length → a.state = a'.state →
      inputPorts (fun _ => false) (fun _ n => 0#n) (bs.zip ids) a =
        inputPorts (fun _ => false) (fun _ n => 0#n) (bs.zip ids') a' := by
    intro bs
    induction bs with
    | nil =>
      intro ids ids' a a' _ _ _
      rfl
    | cons b rest ih =>
      intro ids ids' a a' hl hl' hs
      cases ids with
      | nil => simp at hl
      | cons i is =>
        cases ids' with
        | nil => simp at hl'
        | cons i' is' =>
          have hl2 : is.length = rest.length := by simpa using hl
          have hl2' : is'.length = rest.length := by simpa using hl'
          obtain ⟨name, kind⟩ := b
          have hst : ∀ (k : MixedGateBinder),
              (Tools.ShippingMixedEntrySoundness.extend a ((name, k), i)
                (fun _ => false) (fun _ n => 0#n)).state =
              (Tools.ShippingMixedEntrySoundness.extend a' ((name, k), i')
                (fun _ => false) (fun _ n => 0#n)).state := by
            intro k
            cases k <;> simp [Tools.ShippingMixedEntrySoundness.extend, hs]
          cases kind with
          | domain =>
            simp only [List.zip_cons_cons, inputPorts]
            exact ih is is' _ _ hl2 hl2' (hst .domain)
          | bool =>
            simp only [List.zip_cons_cons, inputPorts, hs]
            rw [ih is is' _ _ hl2 hl2' (hst .bool)]
          | bits n =>
            simp only [List.zip_cons_cons, inputPorts, hs]
            rw [ih is is' _ _ hl2 hl2' (hst (.bits n))]
  have h := key bs ids ids'
    (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
      (Sparkle.IR.ModuleName.ofDecl c))
    (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache')
      (Sparkle.IR.ModuleName.ofDecl c))
    hl hl' rfl
  unfold machPorts
  rw [h]

/-- **The transition's inputs are a binder walk's ports**, on the harness run inside `MachineRanA`
(`t` is that run's transition module). The ids/cache are those of the run, existential. -/
theorem ranA_inputs_machPorts {tenv : Lean.Environment} {c : Name}
    (d : Tools.ShippingMachineAuto.MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {logProf : String → IO Unit} {t : Sparkle.IR.AST.Module} {d₀ : Design}
    (run : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) logProf c
      d.shape.binders d.shape.body) (t, d₀)) :
    ∃ (ids₀ : List FVarId) (cache₀ : IO.Ref (ExprStructMap String)),
      ids₀.length = d.shape.binders.length ∧ machPorts c ids₀ cache₀ d.shape.binders = t.inputs := by
  simp only [Tools.ShippingMachineAuto.MachineData.ok, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at ok
  obtain ⟨_, _, _, _, _, _, _, _, hwf, hb, hv,
    _, _, _, _, _, _, _, _, _, _, _⟩ := ok
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  obtain ⟨ids, cache, _, _, nd, len, hrun, hm, _, nameLegal⟩ :=
    Tools.ShippingMixedEntrySoundness.synthesizeMixedCertified_returns run
  obtain ⟨_, _, hin⟩ :=
    Tools.ShippingMachineEntry.transition_facts nd len hrun hm nameLegal hwf hb' hv' hbody
  exact ⟨ids, cache, len, (hin _ _).symm⟩

end Tools.ShippingGen2

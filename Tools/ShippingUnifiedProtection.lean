import Tools.ShippingUnifiedRecursion

/-! Pending-parent protection and dependency order for the unified recursive
translation. Arithmetic reserves its parent before children that may now
contain muxes, comparisons and Bool inputs, so protection covers every node
kind, including validated cache hits. -/
namespace Tools.ShippingUnifiedProtection
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Reorder
open Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingTranslationOrder
open Tools.ShippingCompareLoweringSoundness Tools.ShippingMuxRecursionSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingBoolMuxSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxTypeSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingScalarSoundness
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedBinarySoundness (Frame ScalarWires binary_returns core_binary_returns)
open Tools.ShippingMixedRecursion (emit_bool_frame compare_step boolBin_step boolEq_step
  boolNot_step translateBoolUncachedWith_boolBin translateBoolBinary_returns)
open Tools.ShippingMixedInvariant (translateStep_fvar_returns)
open Tools.ShippingVectorMuxRecursion (emit_vector_frame vector_step vectorMuxUncached_muxE emit_vector_order)
open Tools.ShippingMixedOrderSoundness (emit_bool_order)

/-- The protected name is reserved, absent from the body, not bound to any
unified input and carries no record with a live source meaning. -/
structure Protected (ctx : CompilerState) (inputs : FVarId → Option Value)
    (s : CircuitState) (p : String) : Prop where
  reserved : s.usedNames.contains p = true
  pending : Pending s p
  unbound : ∀ id v, inputs id = some v → visible ctx s.sourceBindings id ≠ some p
  unrecorded : ∀ e v, s.translateRecord.get? p = some e → ¬ Meaning inputs e v

theorem Protected.transfer {ctx inputs s t p} (hp : Protected ctx inputs s p)
    (hu : ∀ x, s.usedNames.contains x = true → t.usedNames.contains x = true)
    (hb : t.sourceBindings = s.sourceBindings) (hr : RecordFresh s t)
    (hpending : Pending t p) : Protected ctx inputs t p := by
  refine ⟨hu p hp.reserved, hpending, ?_, ?_⟩
  · rw [hb]; exact hp.unbound
  · intro e v he hd
    rcases hr p e he with he | hf
    · exact hp.unrecorded e v he hd
    · rw [hp.reserved] at hf; cases hf

theorem Protected.frame {ctx inputs s t p} (hp : Protected ctx inputs s p)
    (f : Frame s t) (hpending : Pending t p) : Protected ctx inputs t p :=
  hp.transfer f.used f.bindings f.records hpending

/-- Fresh allocation immediately followed by an assignment can neither touch
the pending name nor read it, provided its RHS avoids it. -/
theorem allocate_assign_protect {ctx inputs s t p w ty rhs hint named}
    (hw : w = (CircuitM.makeWire hint ty named s).1)
    (ht : t = (CircuitM.emitAssign w rhs (CircuitM.makeWire hint ty named s).2).2)
    (hp : Protected ctx inputs s p) (refs : p ∉ refsOf rhs) :
    Pending t p ∧ w ≠ p := by
  have hm := CircuitM.makeWire_spec hint ty named s
  have fresh : s.usedNames.contains w = false := by rw [hw]; exact hm.1
  have hne : w ≠ p := by intro he; rw [he, hp.reserved] at fresh; cases fresh
  have hb : t.module.body = .assign w rhs :: s.module.body := by
    rw [ht, emitAssign_body_cons, hm.2.2.1]
  refine ⟨?_, hne⟩
  show p ∉ footprint t.module.body
  rw [hb, footprint_cons]
  intro hmem
  rcases List.mem_cons.mp hmem with heq | hmem
  · exact hne heq.symm
  · rcases List.mem_append.mp hmem with hmem | hmem
    · exact refs hmem
    · exact hp.pending hmem

/-- Fresh allocation alone protects the pending name. -/
theorem makeWire_protect {ctx inputs s p hint ty named}
    (hp : Protected ctx inputs s p) :
    Protected ctx inputs (CircuitM.makeWire hint ty named s).2 p ∧
      (CircuitM.makeWire hint ty named s).1 ≠ p := by
  have hm := CircuitM.makeWire_spec hint ty named s
  have fresh : s.usedNames.contains (CircuitM.makeWire hint ty named s).1 = false := hm.1
  have hne : (CircuitM.makeWire hint ty named s).1 ≠ p := by
    intro he; rw [he, hp.reserved] at fresh; cases fresh
  refine ⟨hp.transfer ?_ (CircuitM.makeWire_sourceBindings _ _ _ _) ?_ ?_, hne⟩
  · intro x hx; rw [hm.2.1]; simp [Std.HashSet.contains_insert, hx]
  · intro x e he; left; rwa [CircuitM.makeWire_translateRecord] at he
  · show p ∉ footprint (CircuitM.makeWire hint ty named s).2.module.body
    rw [hm.2.2.1]; exact hp.pending

/-- Protection obligation for one recursive/action call. Pending names stay
pending and are never returned as a result. -/
def ActionProtect (action : CompilerM String) (ctx : CompilerState)
    (inputs : FVarId → Option Value) : Prop :=
  ∀ s w t p, Returns action ctx s w t → Lookup ctx inputs s → Protected ctx inputs s p →
    Pending t p ∧ w ≠ p

/-- A validated hit cannot return the protected name because its record would
then carry the requested meaning; a miss records only the fresh result. -/
theorem cached_protect {ctx inputs lower e hint top named v}
    (meaning : Meaning inputs e v)
    (node : ActionProtect (lower e hint top named) ctx inputs) :
    ActionProtect (translateControlCachedWith lower e hint top named) ctx inputs := by
  intro s w t p hr lookup hp
  rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
  · obtain ⟨hs, hrecord⟩ := cacheLookupValidated_returns hit
    subst t
    refine ⟨hp.pending, ?_⟩
    intro he
    subst w
    exact hp.unrecorded e v (hrecord p rfl) meaning
  · obtain ⟨hpend, hne⟩ := node s w sm p miss lookup hp
    have hs := recordTranslation_returns record
    refine ⟨?_, hne⟩
    show p ∉ footprint t.module.body
    rw [hs]; exact hpend

/-- Two-child emission (comparison and Bool logic): children protect, then
the fresh Bool result reads only child wires. -/
theorem compare_protect {ctx inputs we mems initial rec ae be le hint named va vb}
    (ca : Child rec ctx inputs we mems initial ae "a" va)
    (cb : Child rec ctx inputs we mems initial be "b" vb)
    (pa : ActionProtect (rec ae "a" false false) ctx inputs)
    (pb : ActionProtect (rec be "b" false false) ctx inputs) :
    ActionProtect (translateSignalCompare rec le ae be hint named) ctx inputs := by
  intro s w t p hr lookup hp
  obtain ⟨a, b, sa, sb, ra, rb, re⟩ := translateSignalCompare_returns hr
  have fa := ca.frame s sa a lookup ra
  obtain ⟨hpa, hwa⟩ := pa s a sa p ra lookup hp
  have hpA := hp.frame fa hpa
  have lookupA := lookup.transfer fa
  have fb := cb.frame sa sb b lookupA rb
  obtain ⟨hpb, hwb⟩ := pb sa b sb p rb lookupA hpA
  have hpB := hpA.frame fb hpb
  obtain ⟨hw, ht⟩ := emitBoolResult_returns re
  exact allocate_assign_protect hw ht hpB
    (by simp [refsOf, refsOf.refsList, Ne.symm hwa, Ne.symm hwb])

theorem boolBin_protect {ctx inputs we mems initial rec ae be kind hint named va vb}
    (ca : Child rec ctx inputs we mems initial ae "a" va)
    (cb : Child rec ctx inputs we mems initial be "b" vb)
    (pa : ActionProtect (rec ae "a" false false) ctx inputs)
    (pb : ActionProtect (rec be "b" false false) ctx inputs) :
    ActionProtect (translateBoolBinary rec kind ae be hint named) ctx inputs := by
  intro s w t p hr lookup hp
  obtain ⟨a, b, sa, sb, ra, rb, re⟩ := translateBoolBinary_returns hr
  have fa := ca.frame s sa a lookup ra
  obtain ⟨hpa, hwa⟩ := pa s a sa p ra lookup hp
  have hpA := hp.frame fa hpa
  have lookupA := lookup.transfer fa
  have fb := cb.frame sa sb b lookupA rb
  obtain ⟨hpb, hwb⟩ := pb sa b sb p rb lookupA hpA
  have hpB := hpA.frame fb hpb
  obtain ⟨hw, ht⟩ := emitBoolResult_returns re
  exact allocate_assign_protect hw ht hpB
    (by simp [refsOf, refsOf.refsList, Ne.symm hwa, Ne.symm hwb])

/-- Three-child mux emission at either result type. -/
theorem muxWith_protect {ctx inputs we mems initial rec ce ae be hint named ty vc va vb}
    (query : CompilerM Sparkle.IR.Type.HWType)
    (hq : query = pure ty)
    (cc : Child rec ctx inputs we mems initial ce "mux_cond" vc)
    (ca : Child rec ctx inputs we mems initial ae "mux_then" va)
    (cb : Child rec ctx inputs we mems initial be "mux_else" vb)
    (pc : ActionProtect (rec ce "mux_cond" false false) ctx inputs)
    (pa : ActionProtect (rec ae "mux_then" false false) ctx inputs)
    (pb : ActionProtect (rec be "mux_else" false false) ctx inputs) :
    ActionProtect (translateMuxWith rec query ce ae be hint named) ctx inputs := by
  subst hq
  intro s w t p hr lookup hp
  obtain ⟨cw, aw, bw, sc, sa, sb, sq, ty', rc, ra, rb, rq, re⟩ := translateMuxWith_returns hr
  obtain ⟨hty, hsq⟩ := Returns.pure rq
  subst ty' sq
  have fc := cc.frame s sc cw lookup rc
  obtain ⟨hpc, hwc⟩ := pc s cw sc p rc lookup hp
  have hpC := hp.frame fc hpc
  have lookupC := lookup.transfer fc
  have fa := ca.frame sc sa aw lookupC ra
  obtain ⟨hpa, hwa⟩ := pa sc aw sa p ra lookupC hpC
  have hpA := hpC.frame fa hpa
  have lookupA := lookupC.transfer fa
  have fb := cb.frame sa sb bw lookupA rb
  obtain ⟨hpb, hwb⟩ := pb sa bw sb p rb lookupA hpA
  have hpB := hpA.frame fb hpb
  obtain ⟨hw, ht⟩ := emitMuxResult_returns re
  exact allocate_assign_protect hw ht hpB
    (by simp [refsOf, refsOf.refsList, Ne.symm hwc, Ne.symm hwa, Ne.symm hwb])

/-- The parent name is reserved before both children; each child preserves
its pending status, so the final assignment cannot read it. -/
theorem binary_protect {ctx inputs we mems initial rec e args hint named n va vb}
    (op : Binary) (width : canonicalSignalBitVecWidth args = some n)
    (ca : Child rec ctx inputs we mems initial args[args.size - 2]! "op_a" va)
    (cb : Child rec ctx inputs we mems initial args[args.size - 1]! "op_b" vb)
    (pa : ActionProtect (rec args[args.size - 2]! "op_a" false false) ctx inputs)
    (pb : ActionProtect (rec args[args.size - 1]! "op_b" false false) ctx inputs) :
    ActionProtect (translateCanonicalSignalBinary rec e op.operator args true true hint named)
      ctx inputs := by
  intro s w t p hr lookup hp
  obtain ⟨sa, sb, sc, a, b, hw, hsa, ra, rb, ht⟩ := binary_returns width hr
  have fa : Frame s sa := by rw [hsa]; exact Frame.makeWire s hint n named
  obtain ⟨hpA', hne⟩ := makeWire_protect (hint := hint) (ty := .bitVector n) (named := named) hp
  have hpA : Protected ctx inputs sa p := by rw [hsa]; exact hpA'
  have hne' : w ≠ p := by rw [hw]; exact hne
  have lookupA := lookup.transfer fa
  have fb := ca.frame sa sb a lookupA ra
  obtain ⟨hpa, hwa⟩ := pa sa a sb p ra lookupA hpA
  have hpB := hpA.frame fb hpa
  have lookupB := lookupA.transfer fb
  have fc := cb.frame sb sc b lookupB rb
  obtain ⟨hpb, hwb⟩ := pb sb b sc p rb lookupB hpB
  have hpC := hpB.frame fc hpb
  refine ⟨?_, hne'⟩
  show p ∉ footprint t.module.body
  rw [ht, emitAssign_body_cons, footprint_cons]
  intro hmem
  rcases List.mem_cons.mp hmem with heq | hmem
  · exact hne' heq.symm
  · rcases List.mem_append.mp hmem with hmem | hmem
    · revert hmem
      simp [refsOf, refsOf.refsList, Ne.symm hwa, Ne.symm hwb]
    · exact hpC.pending hmem

/-- Every reference of a width-cast right-hand side is the child wire. -/
theorem setwRhs_refs {ws wt : Nat} {sw x : String}
    (hx : x ∈ refsOf (setwRhs ws wt sw)) : x = sw := by
  unfold setwRhs at hx
  split at hx
  · simpa [refsOf, refsOf.refsList] using hx
  · split at hx
    · simpa [refsOf, refsOf.refsList] using hx
    · simpa [refsOf] using hx

/-- One-child width cast: the child protects, then the fresh target-width
result reads only the child wire. -/
theorem setw_protect {ctx inputs we mems initial rec ae hint named va} {ws wt : Nat}
    (ca : Child rec ctx inputs we mems initial ae "s" va)
    (pa : ActionProtect (rec ae "s" false false) ctx inputs) :
    ActionProtect (do
        let sw ← rec ae "s" false false
        emitCastResult (setwRhs ws wt sw) wt hint named) ctx inputs := by
  intro s w t p hr lookup hp
  obtain ⟨sw, sm, ra, re⟩ := Returns.bind hr
  have fa := ca.frame s sm sw lookup ra
  obtain ⟨hpa, hwa⟩ := pa s sw sm p ra lookup hp
  have hpA := hp.frame fa hpa
  obtain ⟨hw, ht⟩ := emitCastResult_returns re
  apply allocate_assign_protect hw ht hpA
  intro hmem
  exact hwa (setwRhs_refs hmem).symm

/-- Input leaves return an existing binding: no state change, and the bound
wire cannot be the pending name. -/
theorem input_protect {ctx inputs id v rec hint named} (hi : inputs id = some v) :
    ActionProtect (translateStepWith translateFallback rec (.fvar id) hint false named)
      ctx inputs := by
  intro s w t p hr lookup hp
  obtain ⟨z, bound, _⟩ := lookup.lookup id v hi
  obtain ⟨hw, ht⟩ := translateStep_fvar_returns bound hr
  subst w t
  exact ⟨hp.pending, fun he => hp.unbound id v hi (he ▸ bound)⟩

theorem bool_literal_protect {ctx inputs rec dom hint named} (b : Bool) :
    ActionProtect (translateStepWith translateFallback rec (literalE dom b) hint false named)
      ctx inputs := by
  have meaning : Meaning inputs (literalE dom b) (.bool b) := .value (view_boolLit dom b)
  have fallback : ActionProtect (translateFallback rec (literalE dom b) hint false named)
      ctx inputs := by
    rw [translateFallback_bool rec _ hint false named (by cases b <;> rfl)]
    apply cached_protect meaning
    show ActionProtect (translateBoolUncachedWith rec _ (literalE dom b) hint false named) ctx inputs
    rw [literal_uncached]
    intro s w t p hr lookup hp
    obtain ⟨hw, ht⟩ := emitBoolResult_returns hr
    exact allocate_assign_protect hw ht hp (by simp [refsOf])
  intro s w t p hr lookup hp
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
    obtain ⟨hs, hrecord⟩ := cacheLookupValidated_returns rh
    subst sh
    split at hr
    · rename_i w0
      obtain ⟨hw, ht⟩ := Returns.pure hr
      refine ⟨ht ▸ hp.pending, ?_⟩
      intro he
      have hrec := hrecord w0 rfl
      rw [← hw, he] at hrec
      exact hp.unrecorded _ _ hrec meaning
    · rw [literal_core] at hr
      obtain ⟨z, sc, rv, hr⟩ := Returns.bind hr
      obtain ⟨hz, hs⟩ := Returns.pure rv
      subst z sc
      exact fallback s w t p hr lookup hp
  · rw [literal_core] at hr
    obtain ⟨z, sc, rv, hr⟩ := Returns.bind hr
    obtain ⟨hz, hs⟩ := Returns.pure rv
    subst z sc
    exact fallback s w t p hr lookup hp

/-- The uncached literal branch of `translateCore`, protected. -/
theorem literal_branch_protect {ctx inputs s t p args hint named result}
    (h : Returns (translateSignalPureLiteral? args hint named) ctx s result t)
    (hp : Protected ctx inputs s p) :
    Pending t p ∧ ∀ w, result = some w → w ≠ p := by
  unfold translateSignalPureLiteral? at h
  split at h
  · rename_i wN vN heq
    obtain ⟨name, sA, hm, rest⟩ := Returns.bind h
    obtain ⟨hn', hsA⟩ := makeWire_returns hm
    obtain ⟨u, sB, he, ret⟩ := Returns.bind rest
    obtain ⟨hres, ht⟩ := Returns.pure ret
    have ht' : t = (CircuitM.emitAssign name (.const (vN : Int) wN)
        (CircuitM.makeWire hint (.bitVector wN) named s).2).2 := by
      rw [ht, emitAssign_returns he, hsA]
    obtain ⟨hpend, hne⟩ := allocate_assign_protect hn' ht' hp (by simp [refsOf])
    refine ⟨hpend, fun w hw => ?_⟩
    rw [hres] at hw
    cases hw
    exact hne
  · obtain ⟨hres, ht⟩ := Returns.pure h
    exact ⟨ht ▸ hp.pending, fun w hw => by rw [hres] at hw; cases hw⟩

theorem literal_cont_protect {ctx inputs rec s t p e us hint top named w c n v cacheable}
    {K : Option String → CompilerM String}
    (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us)
    (back : e.getAppArgs.back? = some c) (lit : bitVecLitValue? c = some (n, v))
    (hk : ∀ z, K (some z) = (recordTranslation e z cacheable >>= fun _ => pure z))
    (hr : Returns (translateCore rec e hint top named >>= K) ctx s w t)
    (hp : Protected ctx inputs s p) : Pending t p ∧ w ≠ p := by
  obtain ⟨r, sm, core, rest⟩ := Returns.bind hr
  unfold translateCore at core
  split at core
  · simp [Lean.Expr.getAppFn] at fn
  · rw [fn] at core
    simp only [beq_self_eq_true, if_true] at core
    obtain ⟨hpend, hne⟩ := literal_branch_protect core hp
    obtain ⟨w', hr'⟩ := literal_payload_some back lit core
    subst r
    rw [hk] at rest
    obtain ⟨u, sr, record, ret⟩ := Returns.bind rest
    obtain ⟨hw, ht⟩ := Returns.pure ret
    subst w t
    have hs := recordTranslation_returns record
    refine ⟨?_, hne w' rfl⟩
    show p ∉ footprint _
    rw [hs]
    exact hpend

theorem bits_literal_protect {ctx inputs rec dom n v hint named} {vi : Nat → Lean.Expr}
    (hv : v < 2 ^ n) :
    ActionProtect (translateStepWith translateFallback rec (quoteF dom n vi (.lit v))
      hint false named) ctx inputs := by
  have fn : (quoteF dom n vi (.lit v)).getAppFn =
      .const ``Sparkle.Core.Signal.Signal.pure [.zero] := rfl
  have meaning : Meaning inputs (quoteF dom n vi (.lit v)) (.bits n (BitVec.ofNat n v)) :=
    .value (view_bitsLit dom n v hv vi)
  have back : (quoteF dom n vi (.lit v)).getAppArgs.back? =
      some (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v)) := rfl
  have lit : bitVecLitValue? (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v)) =
      some (n, v) := litValue_natE n v hv
  have nf := isFVar_false_of_const fn
  intro s w t p hr lookup hp
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
    obtain ⟨hs, hrecord⟩ := cacheLookupValidated_returns rh
    subst sh
    split at hr
    · rename_i w0
      obtain ⟨hw, ht⟩ := Returns.pure hr
      refine ⟨ht ▸ hp.pending, ?_⟩
      intro he
      have hrec := hrecord w0 rfl
      rw [← hw, he] at hrec
      exact hp.unrecorded _ _ hrec meaning
    · exact literal_cont_protect (cacheable := !named && !(quoteF dom n vi (.lit v)).isFVar && !false)
        fn back lit (fun z => by simp only [nf, Bool.false_eq_true, if_false]) hr hp
  · exact literal_cont_protect (cacheable := !named && !(quoteF dom n vi (.lit v)).isFVar && !false)
      fn back lit (fun z => by simp only [nf, Bool.false_eq_true, if_false]) hr hp

/-- Actual core/cache step for canonical binary nodes: a validated hit cannot
return the protected name, a lowering protects it through both children. -/
theorem binary_step_protect {ctx inputs we mems initial rec e m us hint named n va vb v}
    (op : Binary)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op.operator)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (meaning : Meaning inputs e v)
    (ca : Child rec ctx inputs we mems initial e.getAppArgs[e.getAppArgs.size - 2]! "op_a" va)
    (cb : Child rec ctx inputs we mems initial e.getAppArgs[e.getAppArgs.size - 1]! "op_b" vb)
    (pa : ActionProtect (rec e.getAppArgs[e.getAppArgs.size - 2]! "op_a" false false) ctx inputs)
    (pb : ActionProtect (rec e.getAppArgs[e.getAppArgs.size - 1]! "op_b" false false) ctx inputs) :
    ActionProtect (translateStepWith translateFallback rec e hint false named) ctx inputs := by
  have nf := isFVar_false_of_const fn
  have cont : ∀ {s w t p} {K : Option String → CompilerM String},
      (∀ z, K (some z) = (recordTranslation e z (!named && !e.isFVar && !false) >>=
        fun _ => pure z)) →
      Returns (translateCore rec e hint false named >>= K) ctx s w t →
      Lookup ctx inputs s → Protected ctx inputs s p → Pending t p ∧ w ≠ p := by
    intro s w t p K hk hr lookup hp
    obtain ⟨r, sc, hcore, rest⟩ := Returns.bind hr
    obtain ⟨z, he, lower⟩ := core_binary_returns fn hop kinds width hcore
    subst r
    obtain ⟨hpend, hne⟩ := binary_protect op width ca cb pa pb s z sc p lower lookup hp
    rw [hk] at rest
    obtain ⟨u, sr, record, ret⟩ := Returns.bind rest
    obtain ⟨hw, ht⟩ := Returns.pure ret
    subst w t
    have hs := recordTranslation_returns record
    refine ⟨?_, hne⟩
    show p ∉ footprint _
    rw [hs]
    exact hpend
  intro s w t p hr lookup hp
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
    obtain ⟨hs, hrecord⟩ := cacheLookupValidated_returns rh
    subst sh
    split at hr
    · rename_i w0
      obtain ⟨hw, ht⟩ := Returns.pure hr
      refine ⟨ht ▸ hp.pending, ?_⟩
      intro he
      have hrec := hrecord w0 rfl
      rw [← hw, he] at hrec
      exact hp.unrecorded _ _ hrec meaning
    · exact cont (fun z => by simp only [nf, Bool.false_eq_true, if_false]) hr lookup hp
  · exact cont (fun z => by simp only [nf, Bool.false_eq_true, if_false]) hr lookup hp

/-- Closed fuel induction: every unified node keeps a protected pending
parent pending and never returns it, at per-operation widths. -/
theorem fuel_protects (fuel : Nat) {ctx : CompilerState} {inputs : FVarId → Option Value}
    {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bi vi : Nat → FVarId} {bools : Nat → Bool} {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → inputs (bi j) = some (.bool (bools j)))
    (hv : ∀ j, j < kv → inputs (vi j) = some (.bits (vw j) (bits j (vw j)))) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → ∀ hint named,
      ActionProtect (translateFuelFix translateStep fuel
        (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e) hint false named) ctx inputs := by
  induction fuel with
  | zero =>
    intro s e he hint named s' w t p hr lookup hp
    exact (Returns.throw hr).elim
  | succ fuel ih =>
    intro s e he hint named
    have fc : ∀ {s' : SType} (e' : Term s'), e'.WF kb kv vw →
        Contract (translateFuelFix translateStep fuel) ctx inputs (fun _ => 0) (fun _ _ => 0)
          (fun _ => 0) (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e')
          (pack s' (eval bools bits e')) :=
      fun e' he' => fuel_contract fuel hb hv e' he'
    change ActionProtect (translateStepWith translateFallback
      (translateFuelFix translateStep fuel) _ hint false named) _ _
    cases e with
    | boolInput j => exact input_protect (hb j he)
    | bitsInput w j =>
      obtain ⟨hj, hw, hpos⟩ := he
      cases hw
      exact input_protect (hv j hj)
    | boolLit b => exact bool_literal_protect b
    | bitsLit w v => exact bits_literal_protect he.1
    | binary op a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      have ck := op_checks op dom (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
        (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b) w
      have ca : Child (translateFuelFix translateStep fuel) ctx inputs (fun _ => 0) (fun _ _ => 0) (fun _ => 0)
          ((binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs[(binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs.size - 2]!)
          "op_a" (pack (.bits w) (eval bools bits a)) := by
        rw [ck.2.2.2.2.1]
        exact ((fc a ha).child "op_a")
      have cb : Child (translateFuelFix translateStep fuel) ctx inputs (fun _ => 0) (fun _ _ => 0) (fun _ => 0)
          ((binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs[(binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs.size - 1]!)
          "op_b" (pack (.bits w) (eval bools bits b)) := by
        rw [ck.2.2.2.2.2.1]
        exact ((fc b hb').child "op_b")
      have pa : ActionProtect (translateFuelFix translateStep fuel
          ((binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs[(binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs.size - 2]!)
          "op_a" false false) ctx inputs := by
        rw [ck.2.2.2.2.1]
        exact ih a ha "op_a" false
      have pb : ActionProtect (translateFuelFix translateStep fuel
          ((binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs[(binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs.size - 1]!)
          "op_b" false false) ctx inputs := by
        rw [ck.2.2.2.2.2.1]
        exact ih b hb' "op_b" false
      exact binary_step_protect op ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1
        (meaning_quote hb hv (.binary op a b) ⟨ha, hb'⟩) ca cb pa pb
    | compare le a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (compareE le dom w (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
          (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)) hint false named) ctx inputs
      rw [compare_step, translateFallback_bool _ _ hint false named (by cases le <;> rfl)]
      have meaning : Meaning inputs
          (compareE le dom w (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b))
          (pack .bool (eval bools bits (.compare le a b))) :=
        meaning_quote hb hv (.compare le a b) ⟨ha, hb'⟩
      apply cached_protect meaning
      show ActionProtect (translateBoolUncachedWith _ _ _ hint false named) ctx inputs
      rw [Tools.ShippingCompareLoweringSoundness.translateBoolUncachedWith_compare]
      exact compare_protect ((fc a ha).child "a")
        ((fc b hb').child "b")
        (ih a ha "a" false) (ih b hb' "b" false)
    | boolBinary kind a b =>
      obtain ⟨ha, hb'⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (boolBinE kind dom (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
          (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)) hint false named) ctx inputs
      rw [boolBin_step, translateFallback_bool _ _ hint false named (by cases kind <;> rfl)]
      have meaning : Meaning inputs
          (boolBinE kind dom (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b))
          (pack .bool (eval bools bits (.boolBinary kind a b))) :=
        meaning_quote hb hv (.boolBinary kind a b) ⟨ha, hb'⟩
      apply cached_protect meaning
      show ActionProtect (translateBoolUncachedWith _ _ _ hint false named) ctx inputs
      rw [translateBoolUncachedWith_boolBin]
      exact boolBin_protect ((fc a ha).child "a")
        ((fc b hb').child "b")
        (ih a ha "a" false) (ih b hb' "b" false)
    | boolNot a =>
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (boolNotE dom (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a))
        hint false named) ctx inputs
      rw [boolNot_step, translateFallback_bool _ _ hint false named rfl]
      apply cached_protect (meaning_quote hb hv (.boolNot a) he)
      show ActionProtect (translateSignalCompare (translateFuelFix translateStep fuel) .eq
        (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
        (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
          (.const ``Bool.false [])) hint named) ctx inputs
      exact compare_protect ((fc a he).child "a")
        ((fc (.boolLit false) trivial).child "b")
        (ih a he "a" false) (ih (.boolLit false) trivial "b" false)
    | boolEq a b =>
      obtain ⟨ha, hb'⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (boolEqE dom (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
          (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)) hint false named) ctx inputs
      rw [boolEq_step, translateFallback_bool _ _ hint false named rfl]
      apply cached_protect (meaning_quote hb hv (.boolEq a b) ⟨ha, hb'⟩)
      show ActionProtect (translateSignalCompare (translateFuelFix translateStep fuel) .eq
        (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
        (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b) hint named) ctx inputs
      exact compare_protect ((fc a ha).child "a")
        ((fc b hb').child "b")
        (ih a ha "a" false) (ih b hb' "b" false)
    | mux c a b =>
      obtain ⟨hc, ha, hb'⟩ := he
      cases s with
      | bool =>
        show ActionProtect (translateStepWith translateFallback
          (translateFuelFix translateStep fuel)
          (boolMuxE dom (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) c)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)) hint false named) ctx inputs
        rw [boolMux_step, translateFallback_bool _ _ hint false named rfl]
        apply cached_protect (meaning_quote hb hv (.mux c a b) ⟨hc, ha, hb'⟩)
        show ActionProtect (translateMuxWith (translateFuelFix translateStep fuel) (pure .bit)
          _ _ _ hint named) ctx inputs
        exact muxWith_protect _ rfl ((fc c hc).child "mux_cond")
          ((fc a ha).child "mux_then")
          ((fc b hb').child "mux_else")
          (ih c hc "mux_cond" false) (ih a ha "mux_then" false) (ih b hb' "mux_else" false)
      | bits w =>
        show ActionProtect (translateStepWith translateFallback
          (translateFuelFix translateStep fuel)
          (muxE dom (bitVecE w) (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) c)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)) hint false named) ctx inputs
        rw [vector_step]
        have meaning : Meaning inputs
            (muxE dom (bitVecE w) (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) c)
              (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
              (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b))
            (pack (.bits w) (eval bools bits (.mux c a b))) :=
          meaning_quote hb hv (.mux c a b) ⟨hc, ha, hb'⟩
        apply cached_protect meaning
        show ActionProtect (translateVectorMuxUncachedWith (translateFuelFix translateStep fuel) w
          (muxE dom (bitVecE w) (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) c)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)) hint false named) ctx inputs
        rw [vectorMuxUncached_muxE]
        exact muxWith_protect _ rfl ((fc c hc).child "mux_cond")
          ((fc a ha).child "mux_then")
          ((fc b hb').child "mux_else")
          (ih c hc "mux_cond" false) (ih a ha "mux_then" false) (ih b hb' "mux_else" false)
    | setw w' a =>
      rename_i w
      obtain ⟨ha, hpos⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (setwE dom w w' (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a))
        hint false named) ctx inputs
      rw [setw_step _ _ _ _ _ (a.wf_pos ha) hpos]
      apply cached_protect (meaning_quote hb hv (.setw w' a) ⟨ha, hpos⟩)
      show ActionProtect (translateSetWidthUncachedWith (translateFuelFix translateStep fuel) w w'
        (setwE dom w w' (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a))
        hint false named) ctx inputs
      rw [setwUncached_setwE]
      exact setw_protect ((fc a ha).child "s") (ih a ha "s" false)

/-- Order obligation for one recursive/action call. -/
def ActionOrder (action : CompilerM String) (ctx : CompilerState)
    (inputs : FVarId → Option Value) (we : WEnv) (mems : MEnv) (initial : Env) : Prop :=
  ∀ s t w prior, Returns action ctx s w t → Inv ctx inputs we mems initial s prior →
    ScalarWidthsAgree we t → OrderInv s → OrderInv t

theorem cached_order {ctx inputs we mems initial lower e hint top named}
    (node : ActionOrder (lower e hint top named) ctx inputs we mems initial) :
    ActionOrder (translateControlCachedWith lower e hint top named) ctx inputs we mems initial := by
  intro s t w prior hr h widths order
  rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
  · rw [(cacheLookupValidated_returns hit).1]; exact order
  · have hs := recordTranslation_returns record
    have wm : ScalarWidthsAgree we sm := by intro p hp; apply widths p; rw [hs]; exact hp
    have ho := node s sm w prior miss h wm order
    rw [hs]
    exact ho

theorem input_order {ctx inputs we mems initial rec id v hint named} (hi : inputs id = some v) :
    ActionOrder (translateStepWith translateFallback rec (.fvar id) hint false named)
      ctx inputs we mems initial := by
  intro s t w prior hr h widths order
  obtain ⟨z, bound, _, _, _⟩ := h.inputs.lookup id v hi
  rw [(translateStep_fvar_returns bound hr).2]
  exact order

theorem bool_literal_order {rec ctx inputs we mems initial dom hint named} (b : Bool) :
    ActionOrder (translateStepWith translateFallback rec (literalE dom b) hint false named)
      ctx inputs we mems initial := by
  have fallback : ActionOrder (translateFallback rec (literalE dom b) hint false named)
      ctx inputs we mems initial := by
    rw [translateFallback_bool rec _ hint false named (by cases b <;> rfl)]
    apply cached_order
    show ActionOrder (translateBoolUncachedWith rec _ _ hint false named) _ _ _ _ _
    rw [literal_uncached]
    intro s t w prior hr h widths order
    exact emit_bool_order hr order (by simp [refsOf])
  intro s t w prior hr h widths order
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
    have hs := (cacheLookupValidated_returns rh).1
    subst sh
    split at hr
    · obtain ⟨hw, ht⟩ := Returns.pure hr
      subst w t; exact order
    · rw [literal_core] at hr
      obtain ⟨z, sc, rv, hr⟩ := Returns.bind hr
      obtain ⟨hz, hs⟩ := Returns.pure rv
      subst z sc
      exact fallback s t w prior hr h widths order
  · rw [literal_core] at hr
    obtain ⟨z, sc, rv, hr⟩ := Returns.bind hr
    obtain ⟨hz, hs⟩ := Returns.pure rv
    subst z sc
    exact fallback s t w prior hr h widths order

theorem literal_cont_order {ctx rec s t e us hint top named w c n v cacheable}
    {K : Option String → CompilerM String}
    (fn : e.getAppFn = .const ``Sparkle.Core.Signal.Signal.pure us)
    (back : e.getAppArgs.back? = some c) (lit : bitVecLitValue? c = some (n, v))
    (hk : ∀ z, K (some z) = (recordTranslation e z cacheable >>= fun _ => pure z))
    (hr : Returns (translateCore rec e hint top named >>= K) ctx s w t)
    (order : OrderInv s) : OrderInv t := by
  obtain ⟨r, sm, core, rest⟩ := Returns.bind hr
  unfold translateCore at core
  split at core
  · simp [Lean.Expr.getAppFn] at fn
  · rw [fn] at core
    simp only [beq_self_eq_true, if_true] at core
    obtain ⟨orderM, _⟩ := translateSignalPureLiteral_order core order
    obtain ⟨w', hr'⟩ := literal_payload_some back lit core
    subst r
    rw [hk] at rest
    obtain ⟨u, sr, record, ret⟩ := Returns.bind rest
    obtain ⟨hw, ht⟩ := Returns.pure ret
    subst w t
    rw [recordTranslation_returns record]
    exact orderM

theorem bits_literal_order {rec ctx inputs we mems initial dom n v hint named}
    {vi : Nat → Lean.Expr} (hv : v < 2 ^ n) :
    ActionOrder (translateStepWith translateFallback rec (quoteF dom n vi (.lit v))
      hint false named) ctx inputs we mems initial := by
  have fn : (quoteF dom n vi (.lit v)).getAppFn =
      .const ``Sparkle.Core.Signal.Signal.pure [.zero] := rfl
  have back : (quoteF dom n vi (.lit v)).getAppArgs.back? =
      some (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v)) := rfl
  have lit : bitVecLitValue? (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v)) =
      some (n, v) := litValue_natE n v hv
  have nf := isFVar_false_of_const fn
  intro s t w prior hr h widths order
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
    have hs := (cacheLookupValidated_returns rh).1
    subst sh
    split at hr
    · obtain ⟨hw, ht⟩ := Returns.pure hr
      subst w t; exact order
    · exact literal_cont_order (cacheable := !named && !(quoteF dom n vi (.lit v)).isFVar && !false)
        fn back lit (fun z => by simp only [nf, Bool.false_eq_true, if_false]) hr order
  · exact literal_cont_order (cacheable := !named && !(quoteF dom n vi (.lit v)).isFVar && !false)
      fn back lit (fun z => by simp only [nf, Bool.false_eq_true, if_false]) hr order

theorem compare_order {ctx inputs we mems initial rec ae be le hint named va vb}
    (ca : Child rec ctx inputs we mems initial ae "a" va)
    (cb : Child rec ctx inputs we mems initial be "b" vb)
    (oa : ActionOrder (rec ae "a" false false) ctx inputs we mems initial)
    (ob : ActionOrder (rec be "b" false false) ctx inputs we mems initial) :
    ActionOrder (translateSignalCompare rec le ae be hint named) ctx inputs we mems initial := by
  intro s t w prior hr h widths order
  obtain ⟨a, b, sa, sb, ra, rb, re⟩ := translateSignalCompare_returns hr
  have fa := ca.frame s sa a (Lookup.ofInputs h.inputs) ra
  have fb := cb.frame sa sb b ((Lookup.ofInputs h.inputs).transfer fa) rb
  have fe := (emit_bool_frame (by cases le <;> rfl) re).1
  have wa := (fb.decls.trans fe.decls).widths widths
  have wb := fe.decls.widths widths
  have aout := ca.sem s sa a prior h wa ra
  obtain ⟨va', ia, _, _⟩ := aout.execution
  have bout := cb.sem sa sb b va' ia wb rb
  apply emit_bool_order re (ob _ _ _ _ rb ia wb (oa _ _ _ _ ra h wa order))
  intro x hx
  have hx : x = a ∨ x = b := by simpa [refsOf, refsOf.refsList] using hx
  rcases hx with rfl | rfl
  · exact fb.used _ aout.used
  · exact bout.used

theorem boolBin_order {ctx inputs we mems initial rec ae be kind hint named va vb}
    (ca : Child rec ctx inputs we mems initial ae "a" va)
    (cb : Child rec ctx inputs we mems initial be "b" vb)
    (oa : ActionOrder (rec ae "a" false false) ctx inputs we mems initial)
    (ob : ActionOrder (rec be "b" false false) ctx inputs we mems initial) :
    ActionOrder (translateBoolBinary rec kind ae be hint named) ctx inputs we mems initial := by
  intro s t w prior hr h widths order
  obtain ⟨a, b, sa, sb, ra, rb, re⟩ := translateBoolBinary_returns hr
  have fa := ca.frame s sa a (Lookup.ofInputs h.inputs) ra
  have fb := cb.frame sa sb b ((Lookup.ofInputs h.inputs).transfer fa) rb
  have fe := (emit_bool_frame (by cases kind <;> rfl) re).1
  have wa := (fb.decls.trans fe.decls).widths widths
  have wb := fe.decls.widths widths
  have aout := ca.sem s sa a prior h wa ra
  obtain ⟨va', ia, _, _⟩ := aout.execution
  have bout := cb.sem sa sb b va' ia wb rb
  apply emit_bool_order re (ob _ _ _ _ rb ia wb (oa _ _ _ _ ra h wa order))
  intro x hx
  have hx : x = a ∨ x = b := by simpa [refsOf, refsOf.refsList] using hx
  rcases hx with rfl | rfl
  · exact fb.used _ aout.used
  · exact bout.used

theorem mux_order {ctx inputs we mems initial rec ce ae be hint named vc va vb}
    (cc : Child rec ctx inputs we mems initial ce "mux_cond" vc)
    (ca : Child rec ctx inputs we mems initial ae "mux_then" va)
    (cb : Child rec ctx inputs we mems initial be "mux_else" vb)
    (oc : ActionOrder (rec ce "mux_cond" false false) ctx inputs we mems initial)
    (oa : ActionOrder (rec ae "mux_then" false false) ctx inputs we mems initial)
    (ob : ActionOrder (rec be "mux_else" false false) ctx inputs we mems initial) :
    ActionOrder (translateMuxWith rec (pure .bit) ce ae be hint named)
      ctx inputs we mems initial := by
  intro s t w prior hr h widths order
  obtain ⟨cw, aw, bw, sc, sa, sb, sq, ty, rc, ra, rb, rq, re⟩ := translateMuxWith_returns hr
  obtain ⟨hty, hsq⟩ := Returns.pure rq
  subst ty sq
  have lookup := Lookup.ofInputs h.inputs
  have fc := cc.frame s sc cw lookup rc
  have fa := ca.frame sc sa aw (lookup.transfer fc) ra
  have fb := cb.frame sa sb bw ((lookup.transfer fc).transfer fa) rb
  have fe := (emit_bool_frame rfl re).1
  have wc := ((fa.decls.trans fb.decls).trans fe.decls).widths widths
  have wa := (fb.decls.trans fe.decls).widths widths
  have wb := fe.decls.widths widths
  have cout := cc.sem s sc cw prior h wc rc
  obtain ⟨vc', ic, _, _⟩ := cout.execution
  have aout := ca.sem sc sa aw vc' ic wa ra
  obtain ⟨va', ia, _, _⟩ := aout.execution
  have bout := cb.sem sa sb bw va' ia wb rb
  apply emit_bool_order re (ob _ _ _ _ rb ia wb (oa _ _ _ _ ra ic wa (oc _ _ _ _ rc h wc order)))
  intro x hx
  have hx : x = cw ∨ x = aw ∨ x = bw := by simpa [refsOf, refsOf.refsList] using hx
  rcases hx with rfl | rfl | rfl
  · exact fb.used _ (fa.used _ cout.used)
  · exact fb.used _ aout.used
  · exact bout.used

theorem vector_order {ctx inputs we mems initial rec ce ae be hint named n vc va vb}
    (cc : Child rec ctx inputs we mems initial ce "mux_cond" vc)
    (ca : Child rec ctx inputs we mems initial ae "mux_then" va)
    (cb : Child rec ctx inputs we mems initial be "mux_else" vb)
    (oc : ActionOrder (rec ce "mux_cond" false false) ctx inputs we mems initial)
    (oa : ActionOrder (rec ae "mux_then" false false) ctx inputs we mems initial)
    (ob : ActionOrder (rec be "mux_else" false false) ctx inputs we mems initial) :
    ActionOrder (translateMuxWith rec (pure (.bitVector n)) ce ae be hint named)
      ctx inputs we mems initial := by
  intro s t w prior hr h widths order
  obtain ⟨cw, aw, bw, sc, sa, sb, sq, ty, rc, ra, rb, rq, re⟩ := translateMuxWith_returns hr
  obtain ⟨hty, hsq⟩ := Returns.pure rq
  subst ty sq
  have lookup := Lookup.ofInputs h.inputs
  have fc := cc.frame s sc cw lookup rc
  have fa := ca.frame sc sa aw (lookup.transfer fc) ra
  have fb := cb.frame sa sb bw ((lookup.transfer fc).transfer fa) rb
  have wc := ((fa.decls.trans fb.decls).trans (emit_vector_frame re).1.decls).widths widths
  have wa := (fb.decls.trans (emit_vector_frame re).1.decls).widths widths
  have wb := (emit_vector_frame re).1.decls.widths widths
  have cout := cc.sem s sc cw prior h wc rc
  obtain ⟨vc', ic, _, _⟩ := cout.execution
  have aout := ca.sem sc sa aw vc' ic wa ra
  obtain ⟨va', ia, _, _⟩ := aout.execution
  have bout := cb.sem sa sb bw va' ia wb rb
  apply emit_vector_order re (ob _ _ _ _ rb ia wb (oa _ _ _ _ ra ic wa (oc _ _ _ _ rc h wc order)))
  intro x hx
  have hx : x = cw ∨ x = aw ∨ x = bw := by simpa [refsOf, refsOf.refsList] using hx
  rcases hx with rfl | rfl | rfl
  · exact fb.used _ (fa.used _ cout.used)
  · exact fb.used _ aout.used
  · exact bout.used

/-- Fresh width-cast emission keeps the acyclic order: the RHS reads only
already-used wires and the target is new. -/
theorem emit_cast_order {ctx s t w rhs wt hint named}
    (hr : Returns (emitCastResult rhs wt hint named) ctx s w t) (order : OrderInv s)
    (refs : ∀ x ∈ refsOf rhs, s.usedNames.contains x = true) : OrderInv t := by
  obtain ⟨hw, ht⟩ := emitCastResult_returns hr
  have alloc := CircuitM.makeWire_spec hint (.bitVector wt) named s
  have fresh : s.usedNames.contains w = false := hw ▸ alloc.1
  have old : w ∉ footprint s.module.body := by
    intro hp; have used := order.2 w hp; rw [fresh] at used; cases used
  have noSelf : w ∉ refsOf rhs := by
    intro hp; have used := refs w hp; rw [fresh] at used; cases used
  constructor
  · rw [ht, emitAssign_body_cons, alloc.2.2.1, List.reverse_cons]
    exact acyclic_snoc order.1
      (fun h => old ((footprint_reverse_mem _ _).mp h)) noSelf
  · intro x hx
    rw [ht, emitAssign_body_cons, alloc.2.2.1, footprint_cons] at hx
    rw [ht, emitAssign_usedNames, alloc.2.1, ← hw]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [Std.HashSet.contains_insert]
    · rcases List.mem_append.mp hx with hx | hx
      · simp [Std.HashSet.contains_insert, refs x hx]
      · simp [Std.HashSet.contains_insert, order.2 x hx]

theorem setw_order {ctx inputs we mems initial rec ae hint named va} {ws wt : Nat}
    (hwt : 0 < wt)
    (ca : Child rec ctx inputs we mems initial ae "s" va)
    (oa : ActionOrder (rec ae "s" false false) ctx inputs we mems initial) :
    ActionOrder (do
        let sw ← rec ae "s" false false
        emitCastResult (setwRhs ws wt sw) wt hint named) ctx inputs we mems initial := by
  intro s t w prior hr h widths order
  obtain ⟨sw, sm, ra, re⟩ := Returns.bind hr
  have wa := (emit_cast_frame (setwRhs_simple ws wt hwt sw) re).1.decls.widths widths
  have aout := ca.sem s sm sw prior h wa ra
  apply emit_cast_order re (oa _ _ _ _ ra h wa order)
  intro x hx
  cases setwRhs_refs hx
  exact aout.used

/-- Order for the allocator-before-children binary node: protection carries
the reserved parent through both recursive children. -/
theorem binary_order {ctx inputs we mems initial rec e args hint named n} {x y : BitVec n}
    (op : Binary)
    (width : canonicalSignalBitVecWidth args = some n)
    (ca : Child rec ctx inputs we mems initial args[args.size - 2]! "op_a" (.bits n x))
    (cb : Child rec ctx inputs we mems initial args[args.size - 1]! "op_b" (.bits n y))
    (pa : ActionProtect (rec args[args.size - 2]! "op_a" false false) ctx inputs)
    (pb : ActionProtect (rec args[args.size - 1]! "op_b" false false) ctx inputs)
    (oa : ActionOrder (rec args[args.size - 2]! "op_a" false false) ctx inputs we mems initial)
    (ob : ActionOrder (rec args[args.size - 1]! "op_b" false false) ctx inputs we mems initial) :
    ActionOrder (translateCanonicalSignalBinary rec e op.operator args true true hint named)
      ctx inputs we mems initial := by
  intro s t w prior h hi hw ho
  unfold translateCanonicalSignalBinary at h
  simp only [width] at h
  obtain ⟨ty, s0, hty, rest⟩ := Returns.bind h
  obtain ⟨htyv, hs0⟩ := Returns.pure hty
  rw [htyv] at rest
  obtain ⟨res, sA, hm, rest⟩ := Returns.bind rest
  rw [hs0] at hm
  obtain ⟨wa, sB, ha, rest⟩ := Returns.bind rest
  obtain ⟨wb, sC, hb', rest⟩ := Returns.bind rest
  obtain ⟨u, sD, hem, ret⟩ := Returns.bind rest
  obtain ⟨hwv, ht⟩ := Returns.pure ret
  rw [ht] at hw ⊢
  obtain ⟨hres, hsA⟩ := makeWire_returns hm
  obtain ⟨hf, hu, hbody, _⟩ := CircuitM.makeWire_spec hint (.bitVector n) named s
  rw [← hres] at hf hu
  rw [← hsA] at hu
  have hsb : sA.sourceBindings = s.sourceBindings := by
    rw [hsA]; exact CircuitM.makeWire_sourceBindings _ _ _ _
  have hrec : sA.translateRecord = s.translateRecord := by
    rw [hsA]; exact CircuitM.makeWire_translateRecord _ _ _ _
  have hiA : Inv ctx inputs we mems initial sA prior := by
    rw [hsA]; exact hi.allocate hint (.bitVector n) named
  obtain ⟨hoA, hpend, hused⟩ := makeWire_order hm ho
  have hpA : Protected ctx inputs sA res := by
    refine ⟨hused, hpend, ?_, ?_⟩
    · intro id v hiv bound
      rw [hsb] at bound
      obtain ⟨z, hz, huz, _, _⟩ := hi.inputs.lookup id v hiv
      have eq : z = res := Option.some.inj (hz.symm.trans bound)
      subst z
      rw [hf] at huz
      cases huz
    · intro e' v record meaning
      rw [hrec] at record
      exact fresh_not_recorded hi.records hf meaning record
  have lookupA := Lookup.ofInputs hiA.inputs
  have ga := ca.frame sA sB wa lookupA ha
  have gb := cb.frame sB sC wb (lookupA.transfer ga) hb'
  have hwC : ScalarWidthsAgree we sC := by
    intro p hp
    apply hw p
    rw [emitAssign_returns hem, emitAssign_wires]
    exact hp
  have hwB := gb.decls.widths hwC
  have va := ca.sem sA sB wa prior hiA hwB ha
  obtain ⟨envB, hiB, _, _⟩ := va.execution
  have vb := cb.sem sB sC wb envB hiB hwC hb'
  have hoB := oa sA sB wa prior ha hiA hwB hoA
  have hoC := ob sB sC wb envB hb' hiB hwC hoB
  obtain ⟨hpa, hwa⟩ := pa sA wa sB res ha lookupA hpA
  have hpB := hpA.frame ga hpa
  obtain ⟨hpc, hwb⟩ := pb sB wb sC res hb' (lookupA.transfer ga) hpB
  apply emitAssign_order hem hoC hpc (gb.used res (ga.used res hused))
  · simp [refsOf, refsOf.refsList, Ne.symm hwa, Ne.symm hwb]
  · intro z hz
    have hz' : z = wa ∨ z = wb := by simpa [refsOf, refsOf.refsList] using hz
    rcases hz' with rfl | rfl
    · exact gb.used _ va.used
    · exact vb.used

theorem binary_step_order {ctx inputs we mems initial rec e m us hint named n} {x y : BitVec n}
    (op : Binary)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op.operator)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (ca : Child rec ctx inputs we mems initial e.getAppArgs[e.getAppArgs.size - 2]! "op_a" (.bits n x))
    (cb : Child rec ctx inputs we mems initial e.getAppArgs[e.getAppArgs.size - 1]! "op_b" (.bits n y))
    (pa : ActionProtect (rec e.getAppArgs[e.getAppArgs.size - 2]! "op_a" false false) ctx inputs)
    (pb : ActionProtect (rec e.getAppArgs[e.getAppArgs.size - 1]! "op_b" false false) ctx inputs)
    (oa : ActionOrder (rec e.getAppArgs[e.getAppArgs.size - 2]! "op_a" false false) ctx inputs we mems initial)
    (ob : ActionOrder (rec e.getAppArgs[e.getAppArgs.size - 1]! "op_b" false false) ctx inputs we mems initial) :
    ActionOrder (translateStepWith translateFallback rec e hint false named)
      ctx inputs we mems initial := by
  have nf := isFVar_false_of_const fn
  have cont : ∀ {s t w prior} {K : Option String → CompilerM String},
      (∀ z, K (some z) = (recordTranslation e z (!named && !e.isFVar && !false) >>=
        fun _ => pure z)) →
      Returns (translateCore rec e hint false named >>= K) ctx s w t →
      Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we t →
      OrderInv s → OrderInv t := by
    intro s t w prior K hk hr h widths order
    obtain ⟨r, sc, hcore, rest⟩ := Returns.bind hr
    obtain ⟨z, he, lower⟩ := core_binary_returns fn hop kinds width hcore
    subst r
    rw [hk] at rest
    obtain ⟨u, sr, record, ret⟩ := Returns.bind rest
    obtain ⟨hw, ht⟩ := Returns.pure ret
    subst w t
    have hs := recordTranslation_returns record
    have wm : ScalarWidthsAgree we sc := by intro p hp; apply widths p; rw [hs]; exact hp
    have := binary_order (x := x) (y := y) op width ca cb pa pb oa ob
      s sc z prior lower h wm order
    rw [hs]
    exact this
  intro s t w prior hr h widths order
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
    have hs := (cacheLookupValidated_returns rh).1
    subst sh
    split at hr
    · obtain ⟨hw, ht⟩ := Returns.pure hr
      subst w t; exact order
    · exact cont (fun z => by simp only [nf, Bool.false_eq_true, if_false]) hr h widths order
  · exact cont (fun z => by simp only [nf, Bool.false_eq_true, if_false]) hr h widths order

/-- Closed unified order induction along the same actual fuel recursion.
No recursive order or protection premise reaches callers. -/
theorem fuel_orders (fuel : Nat) {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bi vi : Nat → FVarId} {bools : Nat → Bool} {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → inputs (bi j) = some (.bool (bools j)))
    (hv : ∀ j, j < kv → inputs (vi j) = some (.bits (vw j) (bits j (vw j)))) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → ∀ hint named,
      ActionOrder (translateFuelFix translateStep fuel
        (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e) hint false named)
        ctx inputs we mems initial := by
  induction fuel with
  | zero =>
    intro s e he hint named s' t w prior hr h widths order
    exact (Returns.throw hr).elim
  | succ fuel ih =>
    intro s e he hint named
    change ActionOrder (translateStepWith translateFallback
      (translateFuelFix translateStep fuel) _ hint false named) _ _ _ _ _
    cases e with
    | boolInput j => exact input_order (hb j he)
    | bitsInput w j =>
      obtain ⟨hj, hw, hpos⟩ := he
      cases hw
      exact input_order (hv j hj)
    | boolLit b => exact bool_literal_order b
    | bitsLit w v => exact bits_literal_order he.1
    | binary op a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      have ck := op_checks op dom (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
        (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b) w
      have ca : Child (translateFuelFix translateStep fuel) ctx inputs we mems initial
          ((binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs[(binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs.size - 2]!)
          "op_a" (.bits w (eval bools bits a)) := by
        rw [ck.2.2.2.2.1]
        exact ((fuel_contract fuel hb hv a ha).child "op_a")
      have cb : Child (translateFuelFix translateStep fuel) ctx inputs we mems initial
          ((binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs[(binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs.size - 1]!)
          "op_b" (.bits w (eval bools bits b)) := by
        rw [ck.2.2.2.2.2.1]
        exact ((fuel_contract fuel hb hv b hb').child "op_b")
      have pa : ActionProtect (translateFuelFix translateStep fuel
          ((binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs[(binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs.size - 2]!)
          "op_a" false false) ctx inputs := by
        rw [ck.2.2.2.2.1]
        exact fuel_protects fuel hb hv a ha "op_a" false
      have pb : ActionProtect (translateFuelFix translateStep fuel
          ((binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs[(binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs.size - 1]!)
          "op_b" false false) ctx inputs := by
        rw [ck.2.2.2.2.2.1]
        exact fuel_protects fuel hb hv b hb' "op_b" false
      have oa : ActionOrder (translateFuelFix translateStep fuel
          ((binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs[(binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs.size - 2]!)
          "op_a" false false) ctx inputs we mems initial := by
        rw [ck.2.2.2.2.1]
        exact ih a ha "op_a" false
      have ob : ActionOrder (translateFuelFix translateStep fuel
          ((binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs[(binE dom w op (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)).getAppArgs.size - 1]!)
          "op_b" false false) ctx inputs we mems initial := by
        rw [ck.2.2.2.2.2.1]
        exact ih b hb' "op_b" false
      exact binary_step_order op ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 ca cb pa pb oa ob
    | compare le a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (compareE le dom w (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
          (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b))
        hint false named) ctx inputs we mems initial
      rw [compare_step, translateFallback_bool _ _ hint false named (by cases le <;> rfl)]
      apply cached_order
      show ActionOrder (translateBoolUncachedWith _ _ _ hint false named) _ _ _ _ _
      rw [Tools.ShippingCompareLoweringSoundness.translateBoolUncachedWith_compare]
      exact compare_order ((fuel_contract fuel hb hv a ha).child "a")
        ((fuel_contract fuel hb hv b hb').child "b")
        (ih a ha "a" false) (ih b hb' "b" false)
    | boolBinary kind a b =>
      obtain ⟨ha, hb'⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (boolBinE kind dom (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
          (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b))
        hint false named) ctx inputs we mems initial
      rw [boolBin_step, translateFallback_bool _ _ hint false named (by cases kind <;> rfl)]
      apply cached_order
      show ActionOrder (translateBoolUncachedWith _ _ _ hint false named) _ _ _ _ _
      rw [translateBoolUncachedWith_boolBin]
      exact boolBin_order ((fuel_contract fuel hb hv a ha).child "a")
        ((fuel_contract fuel hb hv b hb').child "b")
        (ih a ha "a" false) (ih b hb' "b" false)
    | boolNot a =>
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (boolNotE dom (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a))
        hint false named) ctx inputs we mems initial
      rw [boolNot_step, translateFallback_bool _ _ hint false named rfl]
      apply cached_order
      show ActionOrder (translateSignalCompare (translateFuelFix translateStep fuel) .eq
        (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
        (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
          (.const ``Bool.false [])) hint named) _ _ _ _ _
      exact compare_order ((fuel_contract fuel hb hv a he).child "a")
        ((fuel_contract fuel hb hv (.boolLit false) trivial).child "b")
        (ih a he "a" false) (ih (.boolLit false) trivial "b" false)
    | boolEq a b =>
      obtain ⟨ha, hb'⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (boolEqE dom (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
          (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b))
        hint false named) ctx inputs we mems initial
      rw [boolEq_step, translateFallback_bool _ _ hint false named rfl]
      apply cached_order
      show ActionOrder (translateSignalCompare (translateFuelFix translateStep fuel) .eq
        (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
        (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b) hint named) _ _ _ _ _
      exact compare_order ((fuel_contract fuel hb hv a ha).child "a")
        ((fuel_contract fuel hb hv b hb').child "b")
        (ih a ha "a" false) (ih b hb' "b" false)
    | mux c a b =>
      obtain ⟨hc, ha, hb'⟩ := he
      cases s with
      | bool =>
        show ActionOrder (translateStepWith translateFallback
          (translateFuelFix translateStep fuel)
          (boolMuxE dom (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) c)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b))
          hint false named) ctx inputs we mems initial
        rw [boolMux_step, translateFallback_bool _ _ hint false named rfl]
        apply cached_order
        show ActionOrder (translateMuxWith (translateFuelFix translateStep fuel) (pure .bit)
          _ _ _ hint named) _ _ _ _ _
        exact mux_order ((fuel_contract fuel hb hv c hc).child "mux_cond")
          ((fuel_contract fuel hb hv a ha).child "mux_then")
          ((fuel_contract fuel hb hv b hb').child "mux_else")
          (ih c hc "mux_cond" false) (ih a ha "mux_then" false) (ih b hb' "mux_else" false)
      | bits w =>
        show ActionOrder (translateStepWith translateFallback
          (translateFuelFix translateStep fuel)
          (muxE dom (bitVecE w) (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) c)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b))
          hint false named) ctx inputs we mems initial
        rw [vector_step]
        apply cached_order
        show ActionOrder (translateVectorMuxUncachedWith (translateFuelFix translateStep fuel) w
          (muxE dom (bitVecE w) (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) c)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a)
            (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) b)) hint false named)
          ctx inputs we mems initial
        rw [vectorMuxUncached_muxE]
        exact vector_order ((fuel_contract fuel hb hv c hc).child "mux_cond")
          ((fuel_contract fuel hb hv a ha).child "mux_then")
          ((fuel_contract fuel hb hv b hb').child "mux_else")
          (ih c hc "mux_cond" false) (ih a ha "mux_then" false) (ih b hb' "mux_else" false)
    | setw w' a =>
      rename_i w
      obtain ⟨ha, hpos⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (setwE dom w w' (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a))
        hint false named) ctx inputs we mems initial
      rw [setw_step _ _ _ _ _ (a.wf_pos ha) hpos]
      apply cached_order
      show ActionOrder (translateSetWidthUncachedWith (translateFuelFix translateStep fuel) w w'
        (setwE dom w w' (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) a))
        hint false named) ctx inputs we mems initial
      rw [setwUncached_setwE]
      exact setw_order hpos ((fuel_contract fuel hb hv a ha).child "s") (ih a ha "s" false)

/-- Real-entry order for any unified quoted source. -/
theorem translateExprToWire_orders {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bi vi : Nat → FVarId} {bools : Nat → Bool} {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → inputs (bi j) = some (.bool (bools j)))
    (hv : ∀ j, j < kv → inputs (vi j) = some (.bits (vw j) (bits j (vw j))))
    {s : SType} (e : Term s) (he : e.WF kb kv vw) (hint : String) (named : Bool) :
    ActionOrder (translateExprToWire
      (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e) hint false named)
      ctx inputs we mems initial :=
  fuel_orders translateFuelLimit hb hv e he hint named

end Tools.ShippingUnifiedProtection

import Tools.ShippingMixedLiteralSoundness

/-! Mixed-state composition for the shipping allocator-before-children binary
lowering. Child contracts expose structural facts before semantic simulation. -/
namespace Tools.ShippingMixedBinarySoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingMixedInvariant
open Tools.ShippingMixedLiteralSoundness Tools.ShippingCompareLoweringSoundness
open Tools.ShippingMuxRecursionSoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingScalarSoundness Tools.ShippingBindingsSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingPostSoundness Sparkle.IR.OptCheck
open Tools.ShippingBoolSourceSoundness Tools.ShippingMuxLoweringSoundness

/-- Only concrete scalar types are introduced by the closed mixed translator. -/
def ScalarWires (s : CircuitState) : Prop :=
  ∀ p ∈ s.module.wires, p.ty = .bit ∨ ∃ n, p.ty = .bitVector n

structure Frame (s t : CircuitState) : Prop where
  decls : DeclGrows s t
  used : ∀ z, s.usedNames.contains z = true → t.usedNames.contains z = true
  bindings : t.sourceBindings = s.sourceBindings
  records : RecordFresh s t
  wires : WiresOk s → WiresOk t
  scalar : ScalarWires s → ScalarWires t
  outputs : t.module.outputs = s.module.outputs
  inputs : t.module.inputs = s.module.inputs
  simple : SimpleStmts s.module.body → SimpleStmts t.module.body
  parameters : t.module.parameters = s.module.parameters
  primitive : t.module.isPrimitive = s.module.isPrimitive
  wireNames : ∀ p ∈ t.module.wires, p ∈ s.module.wires ∨ Sparkle.IR.NameHints.Allocated p.name

theorem Frame.refl (s : CircuitState) : Frame s s :=
  ⟨fun _ hp => hp, fun _ hp => hp, rfl, fun _ _ he => Or.inl he, fun h => h, fun h => h, rfl, rfl, fun h => h, rfl, rfl, fun _ hp => Or.inl hp⟩

theorem Frame.trans {s t u} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨h.decls.trans k.decls, fun z hz => k.used z (h.used z hz),
    k.bindings.trans h.bindings, h.records.trans k.records h.used, fun hw => k.wires (h.wires hw),
    fun hs => k.scalar (h.scalar hs), k.outputs.trans h.outputs, k.inputs.trans h.inputs, fun hs => k.simple (h.simple hs), k.parameters.trans h.parameters, k.primitive.trans h.primitive, fun p hp => (k.wireNames p hp).elim (h.wireNames p) Or.inr⟩

theorem Frame.record_reserved {s t w e} (h : Frame s t)
    (used : s.usedNames.contains w = true) (he : t.translateRecord.get? w = some e) :
    s.translateRecord.get? w = some e := by
  rcases h.records w e he with old | fresh
  · exact old
  · simp [used] at fresh

theorem Frame.makeWire (s : CircuitState) (hint : String) (n : Nat) (named : Bool) :
    Frame s (CircuitM.makeWire hint (.bitVector n) named s).2 := by
  have hm := CircuitM.makeWire_spec hint (.bitVector n) named s
  refine ⟨?_, ?_, CircuitM.makeWire_sourceBindings _ _ _ _, ?_, ?_, ?_, makeWire_outputs _ _ _ _, makeWire_inputs _ _ _ _, ?_, (DeclFrame.makeWire hint n named s).parameters, (DeclFrame.makeWire hint n named s).primitive, (DeclFrame.makeWire hint n named s).wireNames⟩
  · intro p hp; rw [hm.2.2.2]; exact List.mem_cons_of_mem _ hp
  · intro z hz; rw [hm.2.1]; simp [Std.HashSet.contains_insert, hz]
  · intro w e he; left; rw [CircuitM.makeWire_translateRecord] at he; exact he
  · exact WiresOk.fresh hm.1 hm.2.1 hm.2.2.2
  · intro hs p hp
    rw [hm.2.2.2] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inr ⟨n, rfl⟩
    · exact hs p hp
  · intro hs; rw [hm.2.2.1]; exact hs

theorem Frame.emitAssign (s : CircuitState) (w : String) (rhs : Sparkle.IR.AST.Expr)
    (hr : simpleRhs rhs = true) : Frame s (CircuitM.emitAssign w rhs s).2 := by
  refine ⟨fun _ hp => hp, fun _ hp => hp, rfl, fun _ _ he => Or.inl he,
    fun h => h, fun h => h, rfl, rfl, ?_, rfl, rfl, fun _ hp => Or.inl hp⟩
  intro hs stmt hmem
  rw [emitAssign_body_cons] at hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact ⟨w, rhs, rfl, hr⟩
  · exact hs stmt hmem

/-- Environment-free binding facts prevent an input fvar from taking the
legacy inlining route while structural child properties are established. -/
structure Lookup (ctx : CompilerState) (ρ : BoolValuation) (β : Valuation)
    (s : CircuitState) : Prop where
  bool : ∀ id b, ρ id = some b → ∃ w, visible ctx s.sourceBindings id = some w ∧
    s.usedNames.contains w = true
  bits : BoundLookup ctx β s

theorem Lookup.ofInputs {ctx ρ β we s env} (h : Inputs ctx ρ β we s env) : Lookup ctx ρ β s := by
  refine ⟨?_, h.lookup⟩
  intro id b hi
  obtain ⟨w, bound, used, _, _⟩ := h.bool id b hi
  exact ⟨w, bound, used⟩

theorem Lookup.transfer {ctx ρ β s t} (h : Lookup ctx ρ β s) (f : Frame s t) : Lookup ctx ρ β t := by
  refine ⟨?_, h.bits.transfer f.used f.bindings⟩
  intro id b hi
  obtain ⟨w, bound, used⟩ := h.bool id b hi
  exact ⟨w, by rw [f.bindings]; exact bound, f.used w used⟩

/-- Structure is available without a semantic or final-width premise. The
semantic half can then use widths transported back from a later sibling. -/
structure Child (rec : TranslateFn) (ctx : CompilerState) (ρ : BoolValuation) (β : Valuation)
    (we : WEnv) (mems : MEnv) (initial : Env) (e : Lean.Expr) (hint : String)
    (width value : Nat) : Prop where
  frame : ∀ s t w, Lookup ctx ρ β s → Returns (rec e hint false false) ctx s w t → Frame s t
  sem : ∀ s t w prior, MixedInv ctx ρ β we mems initial s prior → ScalarWidthsAgree we t →
    Returns (rec e hint false false) ctx s w t →
    Outcome ctx ρ β we mems initial prior s t w width value

/-- A write to a name without a live source interpretation preserves the joint
invariant even if that name was already reserved before recursive children. -/
theorem emit_reserved_mixed {ctx ρ β we mems initial s prior w rhs value}
    (h : MixedInv ctx ρ β we mems initial s prior)
    (nb : ∀ id b, ρ id = some b → visible ctx s.sourceBindings id ≠ some w)
    (nv : ∀ id n (x : BitVec n), β id = some ⟨n, x⟩ → visible ctx s.sourceBindings id ≠ some w)
    (rb : ∀ e, s.translateRecord.get? w = some e → ∀ b, ¬ BoolDenotes ρ β e b)
    (rv : ∀ e, s.translateRecord.get? w = some e → ∀ n (x : BitVec n), ¬ Denotes β e n x)
    (typed : TypedExpr we rhs (we w)) (ev : evalExpr we prior rhs = some value) :
    MixedInv ctx ρ β we mems initial (CircuitM.emitAssign w rhs s).2 (write prior w value) := by
  refine ⟨h.separate, emitAssign_sound _ we mems initial prior w rhs value h.runs ev,
    ⟨?_, h.inputs.lookup, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro id b hi
    obtain ⟨v, bound, used, val, width⟩ := h.inputs.bool id b hi
    have ne : v ≠ w := by intro eq; subst v; exact nb id b hi bound
    exact ⟨v, bound, used, by simpa [write, ne] using val, width⟩
  · intro id n x v hi bound
    have ne : v ≠ w := by intro eq; subst v; exact nv id n x hi bound
    obtain ⟨val, width⟩ := h.inputs.values id n x v hi bound
    exact ⟨by simpa [write, ne] using val, width⟩
  · intro v e he b hd
    have ne : v ≠ w := by intro eq; subst v; exact rb e he b hd
    obtain ⟨used, val, width⟩ := h.records.bool v e he b hd
    exact ⟨used, by simpa [write, ne] using val, width⟩
  · intro v e he n x hd
    have ne : v ≠ w := by intro eq; subst v; exact rv e he n x hd
    obtain ⟨used, val, width⟩ := h.records.bits v e he n x hd
    exact ⟨used, by simpa [write, ne] using val, width⟩
  · unfold TypedBody
    rw [emitAssign_body_cons]
    intro st hs
    rcases List.mem_cons.mp hs with hs | hs
    · subst st; exact ⟨w, rhs, rfl, typed⟩
    · exact h.typed st hs

/-- Exact execution decomposition; the allocator precedes both recursive calls. -/
theorem binary_returns {ctx s t rec e op args hint named w n}
    (width : canonicalSignalBitVecWidth args = some n)
    (hr : Returns (translateCanonicalSignalBinary rec e op args true true hint named) ctx s w t) :
    ∃ sa sb sc a b,
      w = (CircuitM.makeWire hint (.bitVector n) named s).1 ∧
      sa = (CircuitM.makeWire hint (.bitVector n) named s).2 ∧
      Returns (rec args[args.size - 2]! "op_a" false false) ctx sa a sb ∧
      Returns (rec args[args.size - 1]! "op_b" false false) ctx sb b sc ∧
      t = (CircuitM.emitAssign w (.op op [.ref a, .ref b]) sc).2 := by
  unfold translateCanonicalSignalBinary at hr
  simp only [width] at hr
  obtain ⟨ty, sq, query, rest⟩ := Returns.bind hr
  obtain ⟨hty, hsq⟩ := Returns.pure query
  subst ty sq
  obtain ⟨r, sa, mk, rest⟩ := Returns.bind rest
  obtain ⟨hw, hsa⟩ := makeWire_returns mk
  obtain ⟨a, sb, ra, rest⟩ := Returns.bind rest
  obtain ⟨b, sc, rb, rest⟩ := Returns.bind rest
  obtain ⟨u, sd, emit, rest⟩ := Returns.bind rest
  obtain ⟨hrw, ht⟩ := Returns.pure rest
  subst w t
  exact ⟨sa, sb, sc, a, b, hw, hsa, ra, rb, emitAssign_returns emit⟩

/-- All eight canonical binary operators in a mixed state. Child structure
supplies intermediate widths and protects the preallocated result's record. -/
theorem translateCanonicalSignalBinary_mixed {ctx ρ β we mems initial s t prior rec e args hint named w n}
    (op : Binary) (x y : BitVec n) (hn : 0 < n)
    (h : MixedInv ctx ρ β we mems initial s prior)
    (width : canonicalSignalBitVecWidth args = some n)
    (ca : Child rec ctx ρ β we mems initial args[args.size - 2]! "op_a" n x.toNat)
    (cb : Child rec ctx ρ β we mems initial args[args.size - 1]! "op_b" n y.toNat)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateCanonicalSignalBinary rec e op.operator args true true hint named) ctx s w t) :
    Frame s t ∧ Outcome ctx ρ β we mems initial prior s t w n (op.apply x y).toNat := by
  have lookup := Lookup.ofInputs h.inputs
  obtain ⟨sa, sb, sc, a, b, hw, hsa, ra, rb, ht⟩ := binary_returns width hr
  have alloc := CircuitM.makeWire_spec hint (.bitVector n) named s
  have fresh : s.usedNames.contains w = false := by rw [hw]; exact alloc.1
  have usedA : sa.usedNames.contains w = true := by rw [hsa, alloc.2.1, hw]; simp
  have fa : Frame s sa := by rw [hsa]; exact Frame.makeWire s hint n named
  have fb := ca.frame sa sb a (lookup.transfer fa) ra
  have fc := cb.frame sb sc b ((lookup.transfer fa).transfer fb) rb
  have fd : Frame sc t := by rw [ht]; exact Frame.emitAssign sc w _ (by cases op <;> rfl)
  have all := ((fa.trans fb).trans fc).trans fd
  have ia : MixedInv ctx ρ β we mems initial sa prior := by
    apply h.transfer ?_ ?_ fa.bindings ?_ fa.used (fun _ _ => rfl)
    · apply runs_of_body_eq ?_ h.runs; rw [hsa]; exact alloc.2.2.1
    · unfold TypedBody; rw [hsa, alloc.2.2.1]; exact h.typed
    · rw [hsa, CircuitM.makeWire_translateRecord]
  have wa := ca.sem sa sb a prior ia ((fc.decls.trans fd.decls).widths widths) ra
  obtain ⟨vb, ib, av, aframe⟩ := wa.execution
  have wb := cb.sem sb sc b vb ib (fd.decls.widths widths) rb
  obtain ⟨vc, ic, bv, bframe⟩ := wb.execution
  have av' : vc a = x.toNat := (bframe a wa.used).trans av
  have resultWidth : we w = n := by
    apply widths ({name := w, ty := .bitVector n} : Port)
    apply fd.decls; apply fc.decls; apply fb.decls
    rw [hsa, alloc.2.2.2, hw]; simp
  have sameBindings : sc.sourceBindings = s.sourceBindings :=
    fc.bindings.trans (fb.bindings.trans fa.bindings)
  have oldRecord : ∀ ex, sc.translateRecord.get? w = some ex → s.translateRecord.get? w = some ex := by
    intro ex he
    have old := fb.record_reserved usedA (fc.record_reserved (fb.used w usedA) he)
    rw [hsa, CircuitM.makeWire_translateRecord] at old
    exact old
  have nb : ∀ id b, ρ id = some b → visible ctx sc.sourceBindings id ≠ some w := by
    intro id value hi bound
    rw [sameBindings] at bound
    obtain ⟨v, hv, hu, _, _⟩ := h.inputs.bool id value hi
    have eq : v = w := Option.some.inj (hv.symm.trans bound)
    subst v; simp [fresh] at hu
  have nv : ∀ id k (z : BitVec k), β id = some ⟨k, z⟩ → visible ctx sc.sourceBindings id ≠ some w := by
    intro id k z hi bound
    rw [sameBindings] at bound
    obtain ⟨v, hv, hu⟩ := h.inputs.lookup id k z hi
    have eq : v = w := Option.some.inj (hv.symm.trans bound)
    subst v; simp [fresh] at hu
  have nrBool : ∀ ex, sc.translateRecord.get? w = some ex → ∀ b, ¬ BoolDenotes ρ β ex b := by
    intro ex he value hd
    have hu := (h.records.bool w ex (oldRecord ex he) value hd).1
    simp [fresh] at hu
  have nrBits : ∀ ex, sc.translateRecord.get? w = some ex → ∀ k (z : BitVec k), ¬ Denotes β ex k z := by
    intro ex he k z hd
    have hu := (h.records.bits w ex (oldRecord ex he) k z hd).1
    simp [fresh] at hu
  have typed : TypedExpr we (.op op.operator [.ref a, .ref b]) (we w) := by
    rw [resultWidth]
    exact .bin op (wa.width_eq ▸ TypedExpr.ref (we := we) a (by rw [wa.width_eq]; exact hn))
      (wb.width_eq ▸ TypedExpr.ref (we := we) b (by rw [wb.width_eq]; exact hn)) (by cases op <;> rfl)
  have rhs := Binary.rhs_correct op we vc a b x y wa.width_eq wb.width_eq av' bv
  have final := emit_reserved_mixed ic nb nv nrBool nrBits typed rhs
  rw [← ht] at final
  refine ⟨all, fd.used w (fc.used w (fb.used w usedA)), resultWidth, all.used,
    write vc w (op.apply x y).toNat, final, ?_, ?_⟩
  · simp [write]
  · intro z hz
    have ne : z ≠ w := by intro eq; subst z; simp [fresh] at hz
    simp only [write, ne, if_false]
    exact (bframe z (fb.used z (fa.used z hz))).trans (aframe z (fa.used z hz))

/-- The structural half is independent of semantic invariants and widths. -/
theorem binary_frame {ctx ρ β we mems initial s t rec e args hint named w n va vb}
    (op : Binary) (lookup : Lookup ctx ρ β s) (width : canonicalSignalBitVecWidth args = some n)
    (ca : Child rec ctx ρ β we mems initial args[args.size - 2]! "op_a" n va)
    (cb : Child rec ctx ρ β we mems initial args[args.size - 1]! "op_b" n vb)
    (hr : Returns (translateCanonicalSignalBinary rec e op.operator args true true hint named) ctx s w t) :
    Frame s t ∧ s.usedNames.contains w = false := by
  obtain ⟨sa, sb, sc, a, b, hw, hsa, ra, rb, ht⟩ := binary_returns width hr
  have fa : Frame s sa := by rw [hsa]; exact Frame.makeWire s hint n named
  have fb := ca.frame sa sb a (lookup.transfer fa) ra
  have fc := cb.frame sb sc b ((lookup.transfer fa).transfer fb) rb
  have fd : Frame sc t := by rw [ht]; exact Frame.emitAssign sc w _ (by cases op <;> rfl)
  refine ⟨((fa.trans fb).trans fc).trans fd, ?_⟩
  rw [hw]; exact (CircuitM.makeWire_spec hint (.bitVector n) named s).1

theorem core_binary_returns {ctx s t rec e m us op hint top named r n}
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (hr : Returns (translateCore rec e hint top named) ctx s r t) :
    ∃ w, r = some w ∧ Returns
      (translateCanonicalSignalBinary rec e op e.getAppArgs true true hint named) ctx s w t := by
  have ne : m ≠ ``Sparkle.Core.Signal.Signal.pure := by
    intro eq; subst m; simp [signalBinOpOf] at hop
  unfold translateCore at hr
  split at hr
  · simp [Lean.Expr.getAppFn] at fn
  · rw [fn] at hr
    simp only [beq_eq_false_iff_ne.mpr ne, Bool.false_eq_true, if_false, hop, kinds, width] at hr
    obtain ⟨w, sm, lower, rest⟩ := Returns.bind hr
    obtain ⟨hr', ht⟩ := Returns.pure rest
    subst r t
    exact ⟨w, rfl, lower⟩

/-- Fresh-result record insertion keeps the parent's structural contract. -/
theorem Frame.record_new {s t u e w cacheable ctx resultUnit} (h : Frame s t)
    (fresh : s.usedNames.contains w = false)
    (hr : Returns (recordTranslation e w cacheable) ctx t resultUnit u) : Frame s u := by
  have hs := recordTranslation_returns hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp; rw [hs]; exact h.decls p hp
  · intro z hz; rw [hs]; exact h.used z hz
  · rw [hs]; exact h.bindings
  · intro z ex he
    rw [hs] at he
    simp only [Std.HashMap.get?_insert] at he
    split at he
    · next eq =>
        have eq' : w = z := by simpa using eq
        subst z; exact Or.inr fresh
    · exact h.records z ex he
  · intro hw; rw [hs]; exact h.wires hw
  · intro hw; rw [hs]; exact h.scalar hw
  · rw [hs]; exact h.outputs
  · rw [hs]; exact h.inputs
  · intro hb; rw [hs]; exact h.simple hb
  · rw [hs]; exact h.parameters
  · rw [hs]; exact h.primitive
  · intro p hp; rw [hs] at hp; exact h.wireNames p hp

theorem core_binary_recorded {ctx ρ β we mems initial s t prior rec e m us hint named top w n cacheable}
    {K : Option String → CompilerM String} (op : Binary) (x y : BitVec n) (hn : 0 < n)
    (h : MixedInv ctx ρ β we mems initial s prior)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op.operator)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (da : Denotes β e.getAppArgs[e.getAppArgs.size - 2]! n x)
    (db : Denotes β e.getAppArgs[e.getAppArgs.size - 1]! n y)
    (ca : Child rec ctx ρ β we mems initial e.getAppArgs[e.getAppArgs.size - 2]! "op_a" n x.toNat)
    (cb : Child rec ctx ρ β we mems initial e.getAppArgs[e.getAppArgs.size - 1]! "op_b" n y.toNat)
    (hk : ∀ v, K (some v) = (recordTranslation e v cacheable >>= fun _ => pure v))
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateCore rec e hint top named >>= K) ctx s w t) :
    Frame s t ∧ Outcome ctx ρ β we mems initial prior s t w n (op.apply x y).toNat := by
  obtain ⟨r, sm, core, rest⟩ := Returns.bind hr
  obtain ⟨v, he, lower⟩ := core_binary_returns fn hop kinds width core
  rw [he, hk] at rest
  obtain ⟨u, sr, record, rest⟩ := Returns.bind rest
  obtain ⟨hw, ht⟩ := Returns.pure rest
  subst w t
  have hs := recordTranslation_returns record
  have wm : ScalarWidthsAgree we sm := by intro p hp; apply widths p; rw [hs]; exact hp
  obtain ⟨growth, fresh⟩ := binary_frame op (Lookup.ofInputs h.inputs) width ca cb lower
  obtain ⟨_, step⟩ := translateCanonicalSignalBinary_mixed op x y hn h width ca cb wm lower
  obtain ⟨result, inv, val, frame⟩ := step.execution
  refine ⟨growth.record_new fresh record, ?_, step.width_eq, ?_, result,
    recordTranslation_mixed_bits inv (.binary fn hop kinds width da db)
      step.used val step.width_eq record, val, frame⟩
  · rw [hs]; exact step.used
  · rw [hs]; exact step.grows

/-- Actual core/cache step for binary expressions. Recursive child contracts
remain explicit; the node and its record update preserve the joint invariant. -/
theorem translateStep_binary_mixed {ctx ρ β we mems initial s t prior rec e m us hint named top w n}
    (op : Binary) (x y : BitVec n) (hn : 0 < n)
    (h : MixedInv ctx ρ β we mems initial s prior)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op.operator)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (da : Denotes β e.getAppArgs[e.getAppArgs.size - 2]! n x)
    (db : Denotes β e.getAppArgs[e.getAppArgs.size - 1]! n y)
    (ca : Child rec ctx ρ β we mems initial e.getAppArgs[e.getAppArgs.size - 2]! "op_a" n x.toNat)
    (cb : Child rec ctx ρ β we mems initial e.getAppArgs[e.getAppArgs.size - 1]! "op_b" n y.toNat)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateStepWith translateFallback rec e hint top named) ctx s w t) :
    Frame s t ∧ Outcome ctx ρ β we mems initial prior s t w n (op.apply x y).toNat := by
  have nf := isFVar_false_of_const fn
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
    have hs := (cacheLookupValidated_returns rh).1
    subst sh
    split at hr
    · obtain ⟨hw, ht⟩ := Returns.pure hr
      subst w t
      have step := (mixed_bits_hit h (.binary fn hop kinds width da db) rh).2
      have he := (cacheLookupValidated_returns rh).1
      rw [he] at step ⊢
      exact ⟨Frame.refl _, step⟩
    · apply core_binary_recorded (cacheable := !named && !e.isFVar && !top)
        op x y hn h fn hop kinds width da db ca cb ?_ widths hr
      intro v; simp only [nf, Bool.false_eq_true, if_false]
  · apply core_binary_recorded (cacheable := !named && !e.isFVar && !top)
      op x y hn h fn hop kinds width da db ca cb ?_ widths hr
    intro v; simp only [nf, Bool.false_eq_true, if_false]

/-- Structural record/update reasoning does not require an initial semantic
invariant or a width environment agreeing with the final state. -/
theorem core_binary_record_frame {ctx ρ β we mems initial s t rec e m us hint named top w n va vb cacheable}
    {K : Option String → CompilerM String} (op : Binary) (lookup : Lookup ctx ρ β s)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op.operator)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (ca : Child rec ctx ρ β we mems initial e.getAppArgs[e.getAppArgs.size - 2]! "op_a" n va)
    (cb : Child rec ctx ρ β we mems initial e.getAppArgs[e.getAppArgs.size - 1]! "op_b" n vb)
    (hk : ∀ v, K (some v) = (recordTranslation e v cacheable >>= fun _ => pure v))
    (hr : Returns (translateCore rec e hint top named >>= K) ctx s w t) : Frame s t := by
  obtain ⟨r, sm, core, rest⟩ := Returns.bind hr
  obtain ⟨v, he, lower⟩ := core_binary_returns fn hop kinds width core
  rw [he, hk] at rest
  obtain ⟨u, sr, record, rest⟩ := Returns.bind rest
  obtain ⟨hw, ht⟩ := Returns.pure rest
  subst w t
  obtain ⟨growth, fresh⟩ := binary_frame op lookup width ca cb lower
  exact growth.record_new fresh record

theorem translateStep_binary_frame {ctx ρ β we mems initial s t rec e m us hint named top w n va vb}
    (op : Binary) (lookup : Lookup ctx ρ β s) (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op.operator)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (ca : Child rec ctx ρ β we mems initial e.getAppArgs[e.getAppArgs.size - 2]! "op_a" n va)
    (cb : Child rec ctx ρ β we mems initial e.getAppArgs[e.getAppArgs.size - 1]! "op_b" n vb)
    (hr : Returns (translateStepWith translateFallback rec e hint top named) ctx s w t) : Frame s t := by
  have nf := isFVar_false_of_const fn
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
    have hs := (cacheLookupValidated_returns rh).1
    subst sh
    split at hr
    · obtain ⟨hw, ht⟩ := Returns.pure hr
      subst w t; exact Frame.refl _
    · apply core_binary_record_frame (cacheable := !named && !e.isFVar && !top)
        op lookup fn hop kinds width ca cb ?_ hr
      intro v; simp only [nf, Bool.false_eq_true, if_false]
  · apply core_binary_record_frame (cacheable := !named && !e.isFVar && !top)
      op lookup fn hop kinds width ca cb ?_ hr
    intro v; simp only [nf, Bool.false_eq_true, if_false]

/-- Actual fuel-bounded translator; the only recursive hypotheses concern
its smaller-fuel operand calls. They must still be closed by induction. -/
theorem translateExprToWire_binary_mixed {ctx ρ β we mems initial s t prior e m us hint named top w n}
    (op : Binary) (x y : BitVec n) (hn : 0 < n)
    (h : MixedInv ctx ρ β we mems initial s prior)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op.operator)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (da : Denotes β e.getAppArgs[e.getAppArgs.size - 2]! n x)
    (db : Denotes β e.getAppArgs[e.getAppArgs.size - 1]! n y)
    (ca : Child (translateFuelFix translateStep (translateFuelLimit - 1)) ctx ρ β we mems initial
      e.getAppArgs[e.getAppArgs.size - 2]! "op_a" n x.toNat)
    (cb : Child (translateFuelFix translateStep (translateFuelLimit - 1)) ctx ρ β we mems initial
      e.getAppArgs[e.getAppArgs.size - 1]! "op_b" n y.toNat)
    (widths : ScalarWidthsAgree we t)
    (hr : Returns (translateExprToWire e hint top named) ctx s w t) :
    Frame s t ∧ Outcome ctx ρ β we mems initial prior s t w n (op.apply x y).toNat := by
  change Returns (translateStepWith translateFallback
    (translateFuelFix translateStep (translateFuelLimit - 1)) e hint top named) ctx s w t at hr
  exact translateStep_binary_mixed op x y hn h fn hop kinds width da db ca cb widths hr

end Tools.ShippingMixedBinarySoundness

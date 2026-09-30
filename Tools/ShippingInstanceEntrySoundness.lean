import Tools.ShippingMemoryEntrySoundness

/-! # S6-2: the certified sub-module instance entry

The canonical hierarchical parent — one call to an `@[hardware_module]`
constant on bare input binders, returning one scalar Signal — now routes
through the certified front end (the run's `instancePredicate` admits it
at the gate) and is lowered by the provable
`translateInstanceUncachedWith` arm. This file connects that route:

* `instE2` — the quoted two-input canonical call, with definitional
  shape lemmas (`instFVars`, matcher spines).
* `instance_term_gate` — gate acceptance from the source positions, AT
  the run's predicate (the instance family's acceptance genuinely
  depends on it, unlike the ∀-predicate old families).
* the `Returns`/`MReturns` extensions the lowering decomposition needs
  (`liftMetaM` value exposure, `tryCatch`).

The child compile itself is pinned by the `SubSynthDefines`-style
boundary (every run of the nested child synthesis in scope returns the
same pair), mirroring `EnvDefines` — see
docs/ShippingCompiler-TrustBase.md §6. -/

namespace Tools.ShippingInstanceEntrySoundness

open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness (Returns recordTranslation_returns
  emitAssign_body_cons)
open Tools.ShippingEntrySoundness (MReturns RunsTo emitLeaves_single
  addOutput_state addClockReset_facts)
open Tools.ShippingMemoryEntrySoundness (mixedGateBVar?_pos)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Sparkle.IR.Semantics (Env)
open Tools.ShippingMixedEntrySoundness (Setup start prepare Admissible
  prepare_returns prepare_layout synthesizeMixedCertified_returns)
open Tools.ShippingMixedInputSoundness (empty_layout)
open Tools.ShippingMixedInvariant (translateStep_fvar_returns)
open Tools.ShippingRegisterSoundness (not_allocated_out prepare_const
  admissible_zero prepare_wires_allocated init_wires)
open Tools.ShippingBoolSourceSoundness (translateControlCachedWith_returns)
open Tools.ShippingTranslateSoundness (cacheLookupValidated_returns)

/-! ## The quoted canonical call -/

/-- The two-input canonical instance call: `@mn dom a b`. -/
def instE2 (mn : Name) (lvls : List Level) (dom a b : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.const mn lvls) dom) a) b

theorem instFVars_instE2 (xs : Array Lean.Expr) (d : Nat) (mn : Name)
    (lvls : List Level) (dom a b : Lean.Expr) :
    instFVars xs d (instE2 mn lvls dom a b) =
      instE2 mn lvls (instFVars xs d dom) (instFVars xs d a) (instFVars xs d b) := rfl

/-- The spine check on the quoted call, from the binder positions. -/
theorem unifiedInstanceSpine_instE2 {bs : List (Name × MixedGateBinder)}
    {dpos apos bpos : Nat} {mn : Name} {lvls : List Level}
    {kd ka kb : MixedGateBinder} {nd na nb : Name}
    (hd : bs[dpos]? = some (nd, kd)) (ha : bs[apos]? = some (na, ka))
    (hb : bs[bpos]? = some (nb, kb)) :
    unifiedInstanceSpine (bs.map (·.2)).toArray
      (instE2 mn lvls (inputExpr bs.length dpos) (inputExpr bs.length apos)
        (inputExpr bs.length bpos)) = true := by
  show ((mixedGateBVar? (bs.map Prod.snd).toArray (bs.length - 1 - bpos)).isSome &&
    ((mixedGateBVar? (bs.map Prod.snd).toArray (bs.length - 1 - apos)).isSome &&
      ((mixedGateBVar? (bs.map Prod.snd).toArray (bs.length - 1 - dpos)).isSome &&
        true))) = true
  rw [mixedGateBVar?_pos hd, mixedGateBVar?_pos ha, mixedGateBVar?_pos hb]
  rfl

theorem unifiedInstanceRoot_instE2 {bs : List (Name × MixedGateBinder)}
    {dpos apos bpos : Nat} {mn : Name} {lvls : List Level}
    {kd ka kb : MixedGateBinder} {nd na nb : Name} {isInst : Lean.Expr → Bool}
    (htag : isInst (instE2 mn lvls (inputExpr bs.length dpos)
      (inputExpr bs.length apos) (inputExpr bs.length bpos)) = true)
    (hd : bs[dpos]? = some (nd, kd)) (ha : bs[apos]? = some (na, ka))
    (hb : bs[bpos]? = some (nb, kb)) :
    unifiedInstanceRoot isInst (bs.map (·.2)).toArray
      (instE2 mn lvls (inputExpr bs.length dpos) (inputExpr bs.length apos)
        (inputExpr bs.length bpos)) = true := by
  unfold unifiedInstanceRoot
  rw [htag, unifiedInstanceSpine_instE2 hd ha hb]
  rfl

/-- Gate acceptance for the canonical instance parent, AT the run's
predicate: the tag premise is about that predicate, and the scalar-result
premise is the declaration's own type. -/
theorem instance_term_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {dpos apos bpos : Nat} {mn : Name} {lvls : List Level}
    {kd ka kb : MixedGateBinder} {nd na nb : Name} {isInst : Lean.Expr → Bool}
    (peel : mixedGatePeel d.value = some (bs,
      instE2 mn lvls (inputExpr bs.length dpos) (inputExpr bs.length apos)
        (inputExpr bs.length bpos)))
    (htag : isInst (instE2 mn lvls (inputExpr bs.length dpos)
      (inputExpr bs.length apos) (inputExpr bs.length bpos)) = true)
    (hscalar : mixedGateResultScalar d.type = true)
    (hd : bs[dpos]? = some (nd, kd)) (ha : bs[apos]? = some (na, ka))
    (hb : bs[bpos]? = some (nb, kb)) :
    mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs,
      instE2 mn lvls (inputExpr bs.length dpos) (inputExpr bs.length apos)
        (inputExpr bs.length bpos)) := by
  have root := unifiedInstanceRoot_instE2 (lvls := lvls) htag hd ha hb
  simp only [mixedCertifiedShape?, List.isEmpty_nil, Bool.not_true,
    peel, root, hscalar, Bool.true_and, Bool.true_or, if_true]
  rfl

/-! ## `Returns`/`MReturns` extensions for the lowering decomposition -/

/-- A lifted MetaM action's VALUE, not just the untouched builder state:
the inner action ran (in some meta context) and returned it. -/
theorem Returns.liftMetaM_mreturns {α : Type} {x : MetaM α} {ctx : CompilerState}
    {s s' : CircuitState} {a : α}
    (h : Returns (CompilerM.liftMetaM x) ctx s a s') : MReturns x a ∧ s' = s := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change (EST.bind (x mctx mref cctx cref) fun a => EST.pure (a, s)) w = _ at hrun
  unfold EST.bind at hrun
  split at hrun
  · rename_i b w1 heq
    simp only [EST.pure] at hrun
    cases hrun
    exact ⟨⟨mctx, mref, cctx, cref, w, _, heq⟩, rfl⟩
  · cases hrun

/-! ## The dispatch step: the canonical call reaches the instance arm -/

/-- The head of the quoted call. -/
theorem instE2_getAppFn (mn : Name) (lvls : List Level) (dom a b : Lean.Expr) :
    (instE2 mn lvls dom a b).getAppFn = .const mn lvls := rfl

set_option maxHeartbeats 1000000 in
/-- One certified step on the canonical instance call lands in the instance
arm: the head constant is none of the core or fallback shapes (each a
decidable fact of the DECLARATION, discharged by `rfl` per instance). -/
theorem instance_step (rec : TranslateFn) (mn : Name) (lvls : List Level)
    (dF aF bF : Lean.Expr) (hint : String) (top named : Bool)
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hctrl : isBoolControl (instE2 mn lvls dF aF bF) = false)
    (hmux : canonicalMuxType? (instE2 mn lvls dF aF bF) = none)
    (hsetw : canonicalSetWidth? (instE2 mn lvls dF aF bF) = none)
    (hreg : canonicalRegister? (instE2 mn lvls dF aF bF) = none)
    (hregEn : canonicalRegisterEnable? (instE2 mn lvls dF aF bF) = none)
    (hloopR : canonicalLoopRegister? (instE2 mn lvls dF aF bF) = none)
    (hcdo : canonicalCircuitDo? (instE2 mn lvls dF aF bF) = none)
    (hcdo2 : canonicalCircuitDo2? (instE2 mn lvls dF aF bF) = none)
    (hmem : canonicalMemory? (instE2 mn lvls dF aF bF) = none) :
    translateStepWith translateFallback rec (instE2 mn lvls dF aF bF) hint top named =
      translateInstanceOrFallback rec (instE2 mn lvls dF aF bF) hint top named := by
  have shape : translateCoreShape (instE2 mn lvls dF aF bF) = false := by
    show ((mn == ``Sparkle.Core.Signal.Signal.pure) ||
      (match signalBinOpOf mn,
          canonicalSignalBinKinds mn (instE2 mn lvls dF aF bF).getAppArgs,
          canonicalSignalBitVecWidth (instE2 mn lvls dF aF bF).getAppArgs with
       | some _, some (true, true), some _ => true
       | _, _, _ => false)) = false
    rw [hpure, hbin]
    rfl
  have core : translateCore rec (instE2 mn lvls dF aF bF) hint top named = pure none := by
    show (if (mn == ``Sparkle.Core.Signal.Signal.pure) = true then
        translateSignalPureLiteral? (instE2 mn lvls dF aF bF).getAppArgs hint named
      else
        match signalBinOpOf mn,
            canonicalSignalBinKinds mn (instE2 mn lvls dF aF bF).getAppArgs,
            canonicalSignalBitVecWidth (instE2 mn lvls dF aF bF).getAppArgs with
        | some op, some (true, true), some _ => do
          let w ← translateCanonicalSignalBinary rec (instE2 mn lvls dF aF bF) op
            (instE2 mn lvls dF aF bF).getAppArgs true true hint named
          pure (some w)
        | _, _, _ => pure none) = pure none
    rw [hpure, hbin]
    rfl
  have step : translateStepWith translateFallback rec
      (instE2 mn lvls dF aF bF) hint top named =
      translateFallback rec (instE2 mn lvls dF aF bF) hint top named := by
    simp [translateStepWith, shape, core]
    rfl
  rw [step]
  simp only [translateFallback, hctrl, Bool.false_eq_true, if_false, hmux, hsetw,
    hreg, hregEn, hloopR, hcdo, hcdo2, hmem]

/-! ## Compiler-level emitter specs for the instance lowering -/

theorem makeWireC_returns {hint : String} {ty : Sparkle.IR.Type.HWType} {named : Bool}
    {ctx : CompilerState} {s s' : CircuitState} {w : String}
    (h : Returns (CompilerM.makeWire hint ty (named := named)) ctx s w s') :
    w = (CircuitM.makeWire hint ty named s).1 ∧
    s' = (CircuitM.makeWire hint ty named s).2 := by
  unfold CompilerM.makeWire at h
  obtain ⟨cs, s1, hget, k1⟩ := Returns.bind h
  obtain ⟨hcs, hs1⟩ := Returns.get hget
  subst hcs hs1
  split at k1
  rename_i name cs' hmk
  obtain ⟨u, s2, hset, k2⟩ := Returns.bind k1
  have hs2 : s2 = cs' := Returns.set hset
  have goal : w = name ∧ s' = s2 := by
    split at k2
    · obtain ⟨u2, s3, hlift, k3⟩ := Returns.bind k2
      have h3 : s3 = s2 := Returns.liftMetaM hlift
      obtain ⟨hw, hs'⟩ := Returns.pure k3
      exact ⟨hw, hs'.trans h3⟩
    · obtain ⟨hw, hs'⟩ := Returns.pure k2
      exact ⟨hw, hs'⟩
  rw [hmk]; exact ⟨goal.1, goal.2.trans hs2⟩

theorem freshNameC_returns {hint : String} {named : Bool}
    {ctx : CompilerState} {s s' : CircuitState} {w : String}
    (h : Returns (CompilerM.freshName hint (named := named)) ctx s w s') :
    w = (CircuitM.freshName hint named s).1 ∧
    s' = (CircuitM.freshName hint named s).2 := by
  unfold CompilerM.freshName at h
  obtain ⟨cs, s1, hget, k1⟩ := Returns.bind h
  obtain ⟨hcs, hs1⟩ := Returns.get hget
  rw [hcs, hs1] at k1
  split at k1
  rename_i name cs' hmk
  obtain ⟨u, s2, hset, k2⟩ := Returns.bind k1
  have hs2 : s2 = cs' := Returns.set hset
  obtain ⟨hw, hs'⟩ := Returns.pure k2
  rw [hmk]
  exact ⟨hw, (hs'.trans hs2 : s' = cs')⟩

theorem emitInstanceC_returns {mnS instName : String}
    {conns : List (String × Sparkle.IR.AST.Expr)}
    {ctx : CompilerState} {s s' : CircuitState} {u : Unit}
    (h : Returns (CompilerM.emitInstance mnS instName conns) ctx s u s') :
    s' = { s with module := s.module.addStmt (.inst mnS instName conns) } := by
  unfold CompilerM.emitInstance at h
  obtain ⟨cs, s1, hget, k1⟩ := Returns.bind h
  obtain ⟨hcs, hs1⟩ := Returns.get hget
  rw [hcs, hs1] at k1
  split at k1
  rename_i u1 cs' hmk
  have hs' : s' = cs' := Returns.set k1
  have hval : CircuitM.emitInstance mnS instName conns s =
      ((), { s with module := s.module.addStmt (.inst mnS instName conns) }) := rfl
  rw [hval] at hmk
  cases hmk
  exact hs'

theorem addModuleToDesignC_returns {m : Sparkle.IR.AST.Module}
    {ctx : CompilerState} {s s' : CircuitState} {u : Unit}
    (h : Returns (CompilerM.addModuleToDesign m) ctx s u s') :
    s' = { s with design := s.design.addModule m } := by
  unfold CompilerM.addModuleToDesign at h
  obtain ⟨cs, s1, hget, k1⟩ := Returns.bind h
  obtain ⟨hcs, hs1⟩ := Returns.get hget
  rw [hcs, hs1] at k1
  split at k1
  rename_i u1 cs' hmk
  have hs' : s' = cs' := Returns.set k1
  have hval : CircuitM.addModuleToDesign m s =
      ((), { s with design := s.design.addModule m }) := rfl
  rw [hval] at hmk
  cases hmk
  exact hs'

/-- Name allocation never touches the design. -/
theorem freshNamed_design (b : String) (s : CircuitState) :
    (CircuitM.freshNamed b s).2.design = s.design := by
  unfold CircuitM.freshNamed
  split <;> rfl

theorem freshName_design (hint : String) (named : Bool) (s : CircuitState) :
    (CircuitM.freshName hint named s).2.design = s.design := by
  unfold CircuitM.freshName
  split
  · exact freshNamed_design _ _
  · rfl

theorem makeWire_design (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool)
    (s : CircuitState) :
    (CircuitM.makeWire hint ty named s).2.design = s.design := by
  have h : (CircuitM.makeWire hint ty named s).2.design =
      (CircuitM.freshName (CircuitM.sanitizeName hint) named s).2.design := rfl
  rw [h]
  exact freshName_design _ _ _

theorem input_design (s : CircuitState) (name : String) (ty : Sparkle.IR.Type.HWType) :
    (Tools.ShippingMixedInputSoundness.inputState s name ty).design = s.design := by
  have h : (Tools.ShippingMixedInputSoundness.inputState s name ty).design =
      (CircuitM.makeWire name ty true s).2.design := rfl
  rw [h]
  exact makeWire_design _ _ _ _

/-- Input preparation never touches the design. -/
theorem prepare_design {bools bits} (L : List ((Name × MixedGateBinder) × FVarId))
    (a : Tools.ShippingMixedEntrySoundness.Setup) :
    (Tools.ShippingMixedEntrySoundness.prepare bools bits L a).state.design =
      a.state.design := by
  induction L generalizing a with
  | nil => rfl
  | cons binder rest ih =>
    obtain ⟨⟨name, kind⟩, id⟩ := binder
    cases kind with
    | domain => exact ih a
    | bool => exact (ih _).trans (input_design _ _ _)
    | bits n => exact (ih _).trans (input_design _ _ _)

theorem instE2_getAppArgs (mn : Name) (lvls : List Level) (dom a b : Lean.Expr) :
    (instE2 mn lvls dom a b).getAppArgs = #[dom, a, b] := rfl

/-! ## The run-boundary predicates (retained, `EnvDefines`-style) -/

/-- Every environment this run's instance arm reads designates `mn` as a
`@[hardware_module]`. Retained: the tag lives in the runtime environment. -/
def HardwareTagged (mn : Name) : Prop :=
  ∀ env, MReturns instArmEnv env → Sparkle.Compiler.isHardwareModule env mn = true

/-- Every nested child synthesis of `mn` this run performs returns exactly
the pinned pair — the hierarchical mirror of `EnvDefines`. -/
def SubSynthDefines (mn : Name) (mc : Sparkle.IR.AST.Module) (dc : Design) : Prop :=
  ∀ r, MReturns (Rec.synthesizeCombinational
    (fun e h t n => translateFuelFix translateStep 1048574 e h t n) mn) r →
    r = (mc, dc)

/-- Every read of the single-out instance dedupe cache in this run comes back
empty (the caches are reset at depth 0 of every top-level synthesis). -/
def InstanceCacheEmpty : Prop :=
  ∀ c, MReturns instArmCacheGet c → ∀ k, c.get? k = none

/-! ## Loop helpers, unfolded -/

theorem instClkRst_skip {ps : List Port} {acc : List (String × Sparkle.IR.AST.Expr)}
    {ctx : CompilerState} {s s' : CircuitState} {r : List (String × Sparkle.IR.AST.Expr)}
    (hps : ∀ p ∈ ps, (p.name == "clk") = false ∧ (p.name == "rst") = false)
    (h : Returns (instClkRst acc ps) ctx s r s') : r = acc ∧ s' = s := by
  induction ps generalizing acc with
  | nil =>
    unfold instClkRst at h
    obtain ⟨hr, hs⟩ := Returns.pure h
    exact ⟨hr, hs⟩
  | cons p rest ih =>
    unfold instClkRst at h
    rw [(hps p (List.mem_cons_self)).1, (hps p (List.mem_cons_self)).2] at h
    simp only [Bool.or_self, Bool.false_eq_true, if_false] at h
    exact ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) h

/-! ## The monolith -/

/-- Everything the mixed certified entry guarantees when the quoted body is
the canonical two-input instance call: the compiled parent is EXACTLY the
canonical `instBody` shape over the pinned child compile, the design holds
exactly that child, and the argument wires carry the prepared source values.
The environment-dependent facts of the run (the tag, the child compile, the
cache reset) enter as the named boundary predicates. -/
def InstancePreserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) (d : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (mn : Name) (lvls : List Level) (dId aId bId : FVarId)
      (mc : Sparkle.IR.AST.Module) (dc : Design) (wOut wA wB : Nat) (xin yin : String),
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      instE2 mn lvls (.fvar dId) (.fvar aId) (.fvar bId) →
    -- the head constant is none of the core/fallback shapes
    (mn == ``Sparkle.Core.Signal.Signal.pure) = false →
    signalBinOpOf mn = none →
    isBoolControl (instE2 mn lvls (.fvar dId) (.fvar aId) (.fvar bId)) = false →
    canonicalMuxType? (instE2 mn lvls (.fvar dId) (.fvar aId) (.fvar bId)) = none →
    canonicalSetWidth? (instE2 mn lvls (.fvar dId) (.fvar aId) (.fvar bId)) = none →
    canonicalRegister? (instE2 mn lvls (.fvar dId) (.fvar aId) (.fvar bId)) = none →
    canonicalRegisterEnable? (instE2 mn lvls (.fvar dId) (.fvar aId) (.fvar bId)) = none →
    canonicalLoopRegister? (instE2 mn lvls (.fvar dId) (.fvar aId) (.fvar bId)) = none →
    canonicalCircuitDo? (instE2 mn lvls (.fvar dId) (.fvar aId) (.fvar bId)) = none →
    canonicalCircuitDo2? (instE2 mn lvls (.fvar dId) (.fvar aId) (.fvar bId)) = none →
    canonicalMemory? (instE2 mn lvls (.fvar dId) (.fvar aId) (.fvar bId)) = none →
    -- the run boundaries
    HardwareTagged mn → SubSynthDefines mn mc dc → InstanceCacheEmpty →
    -- the child's canonical combinational single-output shape
    dc.modules = [] →
    mc.inputs = [⟨xin, .bitVector wA⟩, ⟨yin, .bitVector wB⟩] →
    mc.outputs = [⟨"out", .bitVector wOut⟩] →
    (xin == "clk") = false → (xin == "rst") = false →
    (yin == "clk") = false → (yin == "rst") = false →
    ∃ (instName outW aW bW : String),
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) (av : BitVec wA) (bv : BitVec wB),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits env0 (bs.zip ids) a →
    p.bits aId = some ⟨wA, av⟩ → p.bits bId = some ⟨wB, bv⟩ →
    m.body = [.inst mc.name instName
        [(xin, .ref aW), (yin, .ref bW), ("out", .ref outW)],
      .assign "out" (.ref outW)] ∧
    d.modules = [mc] ∧
    outW ≠ "out" ∧ aW ≠ "out" ∧ bW ≠ "out" ∧
    env0 aW = av.toNat ∧ env0 bW = bv.toNat

end Tools.ShippingInstanceEntrySoundness

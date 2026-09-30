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
    (fun e h t n => translateFuelFix translateStep 1048575 e h t n) mn) r →
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

theorem instRegisterChild_fresh {existing : List String}
    {mc : Sparkle.IR.AST.Module} {ctx : CompilerState} {s s' : CircuitState} {u : Unit}
    (hex : existing.contains mc.name = false)
    (hmods : s.design.modules = [])
    (h : Returns (instRegisterChild existing mc) ctx s u s') :
    s' = { s with design := s.design.addModule mc } := by
  unfold instRegisterChild at h
  obtain ⟨cs, s1, hget, k⟩ := Returns.bind h
  obtain ⟨hcs, hs1⟩ := Returns.get hget
  subst hcs hs1
  rw [hex, hmods] at k
  exact addModuleToDesignC_returns
    (by exact k : Returns (CompilerM.addModuleToDesign mc) _ _ u s')

/-- The uncached instance lowering, unfolded to its explicit bind chain
(definitional; the `have`-bound intermediates zeta-reduce away). -/
theorem instanceUncached_run (rec : TranslateFn) (mn : Name)
    (mc : Sparkle.IR.AST.Module) (dc : Design) (so : Port) (e : Lean.Expr)
    (hint : String) (top named : Bool) :
    translateInstanceUncachedWith rec mn mc dc so e hint top named = (do
      let cs0 ← get
      instAddModules (cs0.design.modules.map (fun x => x.name)) dc.modules
      instRegisterChild (cs0.design.modules.map (fun x => x.name)) mc
      let connections0 ← instClkRst [] mc.inputs
      instArityCheck mn
        (mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst")).length
        e.getAppArgs.size
      let connections ← instArgs rec connections0
        ((mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst")).zip
          (e.getAppArgs.toList.drop (e.getAppArgs.size -
            (mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst")).length))) 0
      let csP ← get
      let instCache ← CompilerM.liftMetaM instArmCacheGet
      match instCache.get? s!"{csP.module.name}#{mc.name}#{String.intercalate ";"
          (connections.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))}" with
      | some cachedW => pure cachedW
      | _ => do
        let w ← CompilerM.makeWire hint so.ty (named := named)
        CompilerM.liftMetaM (instArmCachePut s!"{csP.module.name}#{mc.name}#{String.intercalate ";"
          (connections.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))}" w)
        let instName ← CompilerM.freshName s!"inst_{mc.name}"
        CompilerM.emitInstance mc.name instName
          (((so.name, Sparkle.IR.AST.Expr.ref w) :: connections).reverse)
        pure w) := rfl

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

set_option maxHeartbeats 2000000 in
theorem synthesizeMixedCertified_instance_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d)) :
    InstancePreserves declName bs body m d := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, hd, -⟩ :=
    synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro mn lvls dId aId bId mc dc wOut wA wB xin yin qeq hpure hbin hctrl hmux hsetw
    hreg hregEn hloopR hcdo hcdo2 hmem htag hsub hcachemiss hdc hins houts hx1 hx2 hy1 hy2
  -- Static decomposition at the zero valuation.
  have leaf := prepare_returns (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString)
    (bools := fun _ => false) (bits := fun _ _ => 0) run
  rw [qeq] at leaf
  obtain ⟨w, sm0, ty, tr, freshOut, ht, hty⟩ := emitLeaves_single leaf
  have stepEq : translateExprToWire
      (instE2 mn lvls (.fvar dId) (.fvar aId) (.fvar bId)) "out" false true =
      translateInstanceOrFallback (translateFuelFix translateStep 1048575)
        (instE2 mn lvls (.fvar dId) (.fvar aId) (.fvar bId)) "out" false true := by
    show translateStepWith translateFallback (translateFuelFix translateStep 1048575)
      (instE2 mn lvls (.fvar dId) (.fvar aId) (.fvar bId)) "out" false true = _
    exact instance_step _ mn lvls _ _ _ _ _ _ hpure hbin hctrl hmux hsetw hreg
      hregEn hloopR hcdo hcdo2 hmem
  rw [stepEq] at tr
  unfold translateInstanceOrFallback at tr
  obtain ⟨env, sE, hEnvRead, tr⟩ := Returns.bind tr
  obtain ⟨hEnvM, hsE⟩ := Returns.liftMetaM_mreturns hEnvRead
  subst hsE
  rw [htag env hEnvM] at tr
  simp only [if_true] at tr
  obtain ⟨sub, sS, hSubRead, tr⟩ := Returns.bind tr
  obtain ⟨hSubM, hsS⟩ := Returns.liftMetaM_mreturns hSubRead
  subst hsS
  rw [hsub sub hSubM] at tr
  rw [show ((mc, dc).1.outputs) = mc.outputs from rfl, houts] at tr
  simp only [] at tr
  -- the validated cache wrapper: the record is empty, so it is a miss
  have empty0 := empty_layout (entryCompilerState false cache) declName.toString (fun _ => 0)
  have record0 : (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.translateRecord
      = {} :=
    (prepare_layout (bs.zip ids) _ empty0.1 empty0.2 (admissible_zero _ _)).2.2.2
  rcases translateControlCachedWith_returns tr with hit | ⟨smR, missRun, record⟩
  · obtain ⟨-, hrec⟩ := cacheLookupValidated_returns hit
    have dead := hrec w rfl
    rw [record0] at dead
    simp at dead
  -- the uncached lowering, step by step
  rw [instanceUncached_run] at missRun
  obtain ⟨cs0, sG, hget0, k1⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) missRun
  obtain ⟨hcs0, hsG⟩ := Returns.get hget0
  subst hcs0 hsG
  have hpdes : (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.design =
      Design.empty declName.toString :=
    prepare_design (bs.zip ids) _
  rw [hdc] at k1
  obtain ⟨u0, sA, hAdd0, k2⟩ := Returns.bind (m := instAddModules _ []) k1
  obtain ⟨-, hsA⟩ := Returns.pure (by exact hAdd0 : Returns (pure ()) _ _ u0 sA)
  subst hsA
  -- register the child
  obtain ⟨uR, sB, hReg, k3⟩ := Returns.bind (m := instRegisterChild _ mc) k2
  have hsB := instRegisterChild_fresh (by rw [hpdes]; rfl) (by rw [hpdes]; rfl) hReg
  -- clk/rst plumbing is empty for the combinational child
  obtain ⟨conns0, sC, hClk, k4⟩ := Returns.bind (m := instClkRst [] mc.inputs) k3
  rw [hins] at hClk
  obtain ⟨hconns0, hsC⟩ := instClkRst_skip (fun p hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hx1, hx2⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨hy1, hy2⟩
      · cases hp) hClk
  subst hconns0 hsC
  -- the port filter and the aligned argument list compute
  have hfil : mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst") =
      [⟨xin, .bitVector wA⟩, ⟨yin, .bitVector wB⟩] := by
    rw [hins]
    simp [List.filter, bne, hx1, hx2, hy1, hy2]
  rw [hfil, instE2_getAppArgs] at k4
  -- the arity guard reduces to its skip arm
  obtain ⟨uG, sH, hGuard, k5⟩ := Returns.bind (m := instArityCheck mn _ _) k4
  obtain ⟨-, hsH⟩ := Returns.pure (by exact hGuard : Returns (pure ()) _ _ uG sH)
  subst hsH
  -- the argument walk, then its two operand reads (opaque for now)
  obtain ⟨conns, sF, hArgs, k6⟩ := Returns.bind (m := instArgs _ _ _ 0) k5
  unfold instArgs at hArgs
  obtain ⟨aW, sD, rA, hArgs⟩ :=
    Returns.bind (m := translateFuelFix translateStep 1048575 (Lean.Expr.fvar aId) _ _ _) hArgs
  unfold instArgs at hArgs
  obtain ⟨bW, sE2, rB, hArgs⟩ :=
    Returns.bind (m := translateFuelFix translateStep 1048575 (Lean.Expr.fvar bId) _ _ _) hArgs
  obtain ⟨hconns, hsF⟩ := Returns.pure hArgs
  subst hconns hsF
  -- the parent-name read
  obtain ⟨csP, sP2, hgetP, k7⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) k6
  obtain ⟨hcsP, hsP2⟩ := Returns.get hgetP
  subst hcsP hsP2
  -- the dedupe cache comes back empty
  obtain ⟨cVal, sQ, hCacheRead, k8⟩ :=
    Returns.bind (m := CompilerM.liftMetaM instArmCacheGet) k7
  obtain ⟨hCacheM, hsQ⟩ := Returns.liftMetaM_mreturns hCacheRead
  subst hsQ
  simp only [hcachemiss cVal hCacheM] at k8
  -- the result wire, the cache insert, the instance name, the statement
  obtain ⟨outW, sW, hMk, k9⟩ := Returns.bind (m := CompilerM.makeWire "out" _ true) k8
  obtain ⟨houtW, hsW⟩ := makeWireC_returns hMk
  obtain ⟨uP, sV, hPut, k10⟩ :=
    Returns.bind (m := CompilerM.liftMetaM (instArmCachePut _ _)) k9
  have hsV := Returns.liftMetaM hPut
  subst hsV
  obtain ⟨instName, sN, hFresh, k11⟩ := Returns.bind (m := CompilerM.freshName _) k10
  obtain ⟨hinstName, hsN⟩ := freshNameC_returns hFresh
  obtain ⟨uE, sI, hEmit, k12⟩ :=
    Returns.bind (m := CompilerM.emitInstance mc.name _ _) k11
  have hsI := emitInstanceC_returns hEmit
  obtain ⟨hwEq, hsmR⟩ := Returns.pure k12
  subst hwEq
  have hrec := recordTranslation_returns record
  refine ⟨instName, w, aW, bW, ?_⟩
  intro bools bits env0 av bv a p adm ha0 hb0
  -- transport the zero-valuation spellings to the real valuation
  have empty := empty_layout (entryCompilerState false cache) declName.toString env0
  have prepared := prepare_layout (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString) empty.1 empty.2 adm
  obtain ⟨pc, ps⟩ := prepare_const (fun _ => false) bools (fun _ _ => 0) bits
    (bs.zip ids) _ _ rfl rfl
  rw [ps] at hsB
  rw [pc] at rA rB
  have fuelEq : translateFuelFix translateStep 1048575 =
      translateStepWith translateFallback (translateFuelFix translateStep 1048574) := rfl
  rw [fuelEq] at rA rB
  have designSB : ∀ (s : CircuitState) dd,
      ({ s with design := dd } : CircuitState).sourceBindings = s.sourceBindings :=
    fun _ _ => rfl
  have designMod : ∀ (s : CircuitState) dd,
      ({ s with design := dd } : CircuitState).module = s.module :=
    fun _ _ => rfl
  obtain ⟨aW', aBound, aDecl, aVal⟩ := prepared.1.bits aId wA av ha0
  obtain ⟨bW', bBound, bDecl, bVal⟩ := prepared.1.bits bId wB bv hb0
  have aBound2 : Tools.ShippingBindingsSoundness.visible
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
      sH.sourceBindings aId = some aW' := by
    rw [hsB, designSB]
    exact aBound
  have bBound2 : Tools.ShippingBindingsSoundness.visible
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
      sH.sourceBindings bId = some bW' := by
    rw [hsB, designSB]
    exact bBound
  obtain ⟨haW, hsD⟩ := translateStep_fvar_returns aBound2 rA
  subst hsD
  obtain ⟨hbW, hsE2⟩ := translateStep_fvar_returns bBound2 rB
  subst hsE2
  rw [← haW] at aVal aDecl
  rw [← hbW] at bVal bDecl
  -- the real-valuation prepared state: empty body, empty design, only
  -- allocated wires
  have hbodyR : (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.module.body
      = [] := by
    rw [prepared.2.2.1]; rfl
  have hpdesR : (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.design =
      Design.empty declName.toString := prepare_design (bs.zip ids) _
  have inputNotOut : ∀ (q : Sparkle.IR.AST.Port),
      q ∈ (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.module.wires →
      q.name ≠ "out" := by
    intro q hq eq
    have alloc := prepare_wires_allocated bools bits (bs.zip ids) _
      (by rw [show (start (entryCompilerState false cache) declName.toString).state =
          CircuitM.init declName.toString from rfl, init_wires]
          intro x hx; cases hx) q hq
    rw [eq] at alloc
    exact not_allocated_out alloc
  -- the module body, assembled from the emitter chain
  have addOutBody : ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).body = mo.body :=
    fun _ _ => rfl
  have stBody : st.module.body =
      .assign "out" (.ref w) ::
        .inst mc.name instName
          ((((⟨"out", .bitVector wOut⟩ : Port).name, Sparkle.IR.AST.Expr.ref w) ::
            ((⟨yin, .bitVector wB⟩ : Port).name, Sparkle.IR.AST.Expr.ref bW) ::
            ((⟨xin, .bitVector wA⟩ : Port).name, Sparkle.IR.AST.Expr.ref aW) :: []).reverse) :: (prepare bools bits (bs.zip ids)
              (start (entryCompilerState false cache) declName.toString)).state.module.body := by
    rw [ht, emitAssign_body_cons, addOutput_state]
    show _ :: (sm0.module.addOutput _).body = _
    rw [addOutBody, hrec]
    show _ :: smR.module.body = _
    rw [hsmR, hsI]
    show _ :: (_ :: sN.module.body) = _
    rw [hsN, (CircuitM.freshName_spec _ _ _).2.2, hsW]
    rw [(CircuitM.makeWire_spec "out" _ true _).2.2.1]
    rw [hsB, designMod]
  have mBody : m.body = (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.module.body.reverse ++
      [.inst mc.name instName
        ((((⟨"out", .bitVector wOut⟩ : Port).name, Sparkle.IR.AST.Expr.ref w) ::
          ((⟨yin, .bitVector wB⟩ : Port).name, Sparkle.IR.AST.Expr.ref bW) ::
            ((⟨xin, .bitVector wA⟩ : Port).name, Sparkle.IR.AST.Expr.ref aW) :: []).reverse),
       .assign "out" (.ref w)] := by
    rw [hm]
    show ((addClockResetIfSequential st.module).finalize).body = _
    simp only [Sparkle.IR.AST.Module.finalize,
      (addClockReset_facts st.module).1, stBody]
    simp
  -- the design: exactly the child
  have stDesign : st.design = ((prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.design).addModule mc := by
    rw [ht]
    show sm0.design = _
    rw [hrec]
    show smR.design = _
    rw [hsmR, hsI]
    show sN.design = _
    rw [hsN]
    rw [show ∀ s, ((CircuitM.freshName (toString "inst_" ++ toString mc.name) false s).2).design
        = s.design from fun s => freshName_design _ _ s, hsW]
    rw [makeWire_design]
    rw [hsB]
  -- the result-wire freshness
  have wNotOut : w ≠ "out" := by
    intro eq
    have alloc := CircuitM.makeWire_allocated "out"
      (Sparkle.IR.Type.HWType.bitVector wOut) true sQ
    rw [← houtW, eq] at alloc
    exact not_allocated_out alloc
  refine ⟨?_, ?_, wNotOut, inputNotOut _ aDecl, inputNotOut _ bDecl, aVal, bVal⟩
  · rw [mBody, hbodyR]
    rfl
  · rw [hd, stDesign, hpdesR]
    rfl

/-! ## The one-input canonical call (sequential children take this shape) -/

/-- The one-input canonical instance call: `@mn dom a`. -/
def instE1 (mn : Name) (lvls : List Level) (dom a : Lean.Expr) : Lean.Expr :=
  .app (.app (.const mn lvls) dom) a

theorem instFVars_instE1 (xs : Array Lean.Expr) (d : Nat) (mn : Name)
    (lvls : List Level) (dom a : Lean.Expr) :
    instFVars xs d (instE1 mn lvls dom a) =
      instE1 mn lvls (instFVars xs d dom) (instFVars xs d a) := rfl

theorem instE1_getAppArgs (mn : Name) (lvls : List Level) (dom a : Lean.Expr) :
    (instE1 mn lvls dom a).getAppArgs = #[dom, a] := rfl

theorem unifiedInstanceSpine_instE1 {bs : List (Name × MixedGateBinder)}
    {dpos apos : Nat} {mn : Name} {lvls : List Level}
    {kd ka : MixedGateBinder} {nd na : Name}
    (hd : bs[dpos]? = some (nd, kd)) (ha : bs[apos]? = some (na, ka)) :
    unifiedInstanceSpine (bs.map (·.2)).toArray
      (instE1 mn lvls (inputExpr bs.length dpos) (inputExpr bs.length apos)) = true := by
  show ((mixedGateBVar? (bs.map Prod.snd).toArray (bs.length - 1 - apos)).isSome &&
    ((mixedGateBVar? (bs.map Prod.snd).toArray (bs.length - 1 - dpos)).isSome &&
      true)) = true
  rw [mixedGateBVar?_pos hd, mixedGateBVar?_pos ha]
  rfl

theorem unifiedInstanceRoot_instE1 {bs : List (Name × MixedGateBinder)}
    {dpos apos : Nat} {mn : Name} {lvls : List Level}
    {kd ka : MixedGateBinder} {nd na : Name} {isInst : Lean.Expr → Bool}
    (htag : isInst (instE1 mn lvls (inputExpr bs.length dpos)
      (inputExpr bs.length apos)) = true)
    (hd : bs[dpos]? = some (nd, kd)) (ha : bs[apos]? = some (na, ka)) :
    unifiedInstanceRoot isInst (bs.map (·.2)).toArray
      (instE1 mn lvls (inputExpr bs.length dpos) (inputExpr bs.length apos)) = true := by
  unfold unifiedInstanceRoot
  rw [htag, unifiedInstanceSpine_instE1 hd ha]
  rfl

theorem instance1_term_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {dpos apos : Nat} {mn : Name} {lvls : List Level}
    {kd ka : MixedGateBinder} {nd na : Name} {isInst : Lean.Expr → Bool}
    (peel : mixedGatePeel d.value = some (bs,
      instE1 mn lvls (inputExpr bs.length dpos) (inputExpr bs.length apos)))
    (htag : isInst (instE1 mn lvls (inputExpr bs.length dpos)
      (inputExpr bs.length apos)) = true)
    (hscalar : mixedGateResultScalar d.type = true)
    (hd : bs[dpos]? = some (nd, kd)) (ha : bs[apos]? = some (na, ka)) :
    mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs,
      instE1 mn lvls (inputExpr bs.length dpos) (inputExpr bs.length apos)) := by
  have root := unifiedInstanceRoot_instE1 (lvls := lvls) htag hd ha
  simp only [mixedCertifiedShape?, List.isEmpty_nil, Bool.not_true,
    peel, root, hscalar, Bool.true_and, Bool.true_or, if_true]
  rfl

set_option maxHeartbeats 1000000 in
theorem instance1_step (rec : TranslateFn) (mn : Name) (lvls : List Level)
    (dF aF : Lean.Expr) (hint : String) (top named : Bool)
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hctrl : isBoolControl (instE1 mn lvls dF aF) = false)
    (hmux : canonicalMuxType? (instE1 mn lvls dF aF) = none)
    (hsetw : canonicalSetWidth? (instE1 mn lvls dF aF) = none)
    (hreg : canonicalRegister? (instE1 mn lvls dF aF) = none)
    (hregEn : canonicalRegisterEnable? (instE1 mn lvls dF aF) = none)
    (hloopR : canonicalLoopRegister? (instE1 mn lvls dF aF) = none)
    (hcdo : canonicalCircuitDo? (instE1 mn lvls dF aF) = none)
    (hcdo2 : canonicalCircuitDo2? (instE1 mn lvls dF aF) = none)
    (hmem : canonicalMemory? (instE1 mn lvls dF aF) = none) :
    translateStepWith translateFallback rec (instE1 mn lvls dF aF) hint top named =
      translateInstanceOrFallback rec (instE1 mn lvls dF aF) hint top named := by
  have shape : translateCoreShape (instE1 mn lvls dF aF) = false := by
    show ((mn == ``Sparkle.Core.Signal.Signal.pure) ||
      (match signalBinOpOf mn,
          canonicalSignalBinKinds mn (instE1 mn lvls dF aF).getAppArgs,
          canonicalSignalBitVecWidth (instE1 mn lvls dF aF).getAppArgs with
       | some _, some (true, true), some _ => true
       | _, _, _ => false)) = false
    rw [hpure, hbin]
    rfl
  have core : translateCore rec (instE1 mn lvls dF aF) hint top named = pure none := by
    show (if (mn == ``Sparkle.Core.Signal.Signal.pure) = true then
        translateSignalPureLiteral? (instE1 mn lvls dF aF).getAppArgs hint named
      else
        match signalBinOpOf mn,
            canonicalSignalBinKinds mn (instE1 mn lvls dF aF).getAppArgs,
            canonicalSignalBitVecWidth (instE1 mn lvls dF aF).getAppArgs with
        | some op, some (true, true), some _ => do
          let w ← translateCanonicalSignalBinary rec (instE1 mn lvls dF aF) op
            (instE1 mn lvls dF aF).getAppArgs true true hint named
          pure (some w)
        | _, _, _ => pure none) = pure none
    rw [hpure, hbin]
    rfl
  have step : translateStepWith translateFallback rec
      (instE1 mn lvls dF aF) hint top named =
      translateFallback rec (instE1 mn lvls dF aF) hint top named := by
    simp [translateStepWith, shape, core]
    rfl
  rw [step]
  simp only [translateFallback, hctrl, Bool.false_eq_true, if_false, hmux, hsetw,
    hreg, hregEn, hloopR, hcdo, hcdo2, hmem]

/-! ## clk/rst plumbing for a sequential child -/

theorem not_allocated_clk : ¬ Sparkle.IR.NameHints.Allocated "clk" := by
  intro h
  have := h.2
  revert this
  decide

theorem not_allocated_rst : ¬ Sparkle.IR.NameHints.Allocated "rst" := by
  intro h
  have := h.2
  revert this
  decide

/-- Peel a `get` deterministically: `bind get f ≡ f s` holds definitionally
in the state stack, so the SAME run witnesses the continuation. (Plain
`Returns.bind` can degenerate here: because `get` is state-invariant, the
unifier may solve its continuation as `fun _ => ⟨whole program⟩`.) -/
theorem Returns.get_bind {α : Type} {f : CircuitState → CompilerM α}
    {ctx : CompilerState} {s s'' : CircuitState} {b : α}
    (h : Returns (Bind.bind (MonadState.get : CompilerM CircuitState) f) ctx s b s'') :
    Returns (f s) ctx s b s'' := h

/-- The sequential child's canonical port walk: the data port skips, clk and
rst each add the missing parent port and connect to it. -/
theorem instClkRst_seq {xin : String} {wA : Nat}
    {ctx : CompilerState} {s s' : CircuitState}
    {r : List (String × Sparkle.IR.AST.Expr)}
    (hx1 : (xin == "clk") = false) (hx2 : (xin == "rst") = false)
    (hclk : s.module.inputs.any (fun p => p.name == "clk") = false)
    (hrst : (CircuitM.addInput "clk" .bit s).2.module.inputs.any
      (fun p => p.name == "rst") = false)
    (h : Returns (instClkRst []
      [⟨xin, .bitVector wA⟩, ⟨"clk", .bit⟩, ⟨"rst", .bit⟩]) ctx s r s') :
    r = [("rst", .ref "rst"), ("clk", .ref "clk")] ∧
    s' = (CircuitM.addInput "rst" .bit (CircuitM.addInput "clk" .bit s).2).2 := by
  unfold instClkRst at h
  rw [hx1, hx2] at h
  simp only [Bool.or_self, Bool.false_eq_true, if_false] at h
  -- the clk port: the outer guard and the missing-input guard both close
  unfold instClkRst at h
  rw [if_pos (show ((("clk" : String) == "clk" || ("clk" : String) == "rst") = true)
    by decide)] at h
  replace h := Returns.get_bind h
  try dsimp only at h
  rw [hclk] at h
  rw [if_pos (show (((!false) = true)) by decide)] at h
  obtain ⟨u1, sA1, hAdd1, h⟩ := Returns.bind (m := CompilerM.addInput "clk" .bit) h
  have hsA1 : sA1 = (CircuitM.addInput "clk" .bit s).2 :=
    Tools.ShippingEntrySoundness.addInput_returns
      (by exact hAdd1 : Returns (CompilerM.addInput "clk" .bit) _ _ u1 sA1)
  subst hsA1
  -- the rst port
  unfold instClkRst at h
  rw [if_pos (show ((("rst" : String) == "clk" || ("rst" : String) == "rst") = true)
    by decide)] at h
  replace h := Returns.get_bind h
  try dsimp only at h
  rw [hrst] at h
  rw [if_pos (show (((!false) = true)) by decide)] at h
  obtain ⟨u2, sA2, hAdd2, h⟩ := Returns.bind (m := CompilerM.addInput "rst" .bit) h
  have hsA2 : sA2 = (CircuitM.addInput "rst" .bit
      (CircuitM.addInput "clk" .bit s).2).2 :=
    Tools.ShippingEntrySoundness.addInput_returns
      (by exact hAdd2 : Returns (CompilerM.addInput "rst" .bit) _ _ u2 sA2)
  subst hsA2
  -- the walk closes
  unfold instClkRst at h
  obtain ⟨hr, hs⟩ := Returns.pure h
  exact ⟨hr, hs⟩

/-! ## Record-update helpers for the clk/rst layer -/

theorem addInput_sourceBindings (n : String) (ty : Sparkle.IR.Type.HWType)
    (s : CircuitState) :
    (CircuitM.addInput n ty s).2.sourceBindings = s.sourceBindings := rfl

theorem addInput_body (n : String) (ty : Sparkle.IR.Type.HWType) (s : CircuitState) :
    (CircuitM.addInput n ty s).2.module.body = s.module.body := rfl

theorem addInput_design (n : String) (ty : Sparkle.IR.Type.HWType) (s : CircuitState) :
    (CircuitM.addInput n ty s).2.design = s.design := rfl

theorem addInput_inputs (n : String) (ty : Sparkle.IR.Type.HWType) (s : CircuitState) :
    (CircuitM.addInput n ty s).2.module.inputs = ⟨n, ty⟩ :: s.module.inputs := rfl

/-! ## The one-input sequential-child contract and monolith -/

/-- The mixed certified entry's guarantee when the quoted body is the
canonical ONE-input instance call on a sequential child (data port plus
clk/rst): the compiled parent is the canonical instance body with the
clk/rst connections and the freshly added parent clock ports, the design
holds exactly the pinned child, and the argument wire carries the prepared
source value. -/
def Instance1Preserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) (d : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (mn : Name) (lvls : List Level) (dId aId : FVarId)
      (mc : Sparkle.IR.AST.Module) (dc : Design) (wOut wA : Nat) (xin : String),
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      instE1 mn lvls (.fvar dId) (.fvar aId) →
    (mn == ``Sparkle.Core.Signal.Signal.pure) = false →
    signalBinOpOf mn = none →
    isBoolControl (instE1 mn lvls (.fvar dId) (.fvar aId)) = false →
    canonicalMuxType? (instE1 mn lvls (.fvar dId) (.fvar aId)) = none →
    canonicalSetWidth? (instE1 mn lvls (.fvar dId) (.fvar aId)) = none →
    canonicalRegister? (instE1 mn lvls (.fvar dId) (.fvar aId)) = none →
    canonicalRegisterEnable? (instE1 mn lvls (.fvar dId) (.fvar aId)) = none →
    canonicalLoopRegister? (instE1 mn lvls (.fvar dId) (.fvar aId)) = none →
    canonicalCircuitDo? (instE1 mn lvls (.fvar dId) (.fvar aId)) = none →
    canonicalCircuitDo2? (instE1 mn lvls (.fvar dId) (.fvar aId)) = none →
    canonicalMemory? (instE1 mn lvls (.fvar dId) (.fvar aId)) = none →
    HardwareTagged mn → SubSynthDefines mn mc dc → InstanceCacheEmpty →
    dc.modules = [] →
    mc.inputs = [⟨xin, .bitVector wA⟩, ⟨"clk", .bit⟩, ⟨"rst", .bit⟩] →
    mc.outputs = [⟨"out", .bitVector wOut⟩] →
    (xin == "clk") = false → (xin == "rst") = false →
    ∃ (instName outW aW : String),
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) (av : BitVec wA),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits env0 (bs.zip ids) a →
    p.bits aId = some ⟨wA, av⟩ →
    m.body = [.inst mc.name instName
        [("clk", .ref "clk"), ("rst", .ref "rst"), (xin, .ref aW), ("out", .ref outW)],
      .assign "out" (.ref outW)] ∧
    d.modules = [mc] ∧
    (⟨"clk", .bit⟩ : Port) ∈ m.inputs ∧ (⟨"rst", .bit⟩ : Port) ∈ m.inputs ∧
    outW ≠ "out" ∧ aW ≠ "out" ∧
    env0 aW = av.toNat

set_option maxHeartbeats 2000000 in
theorem synthesizeMixedCertified_instance1_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d)) :
    Instance1Preserves declName bs body m d := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, hd, -⟩ :=
    synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro mn lvls dId aId mc dc wOut wA xin qeq hpure hbin hctrl hmux hsetw
    hreg hregEn hloopR hcdo hcdo2 hmem htag hsub hcachemiss hdc hins houts hx1 hx2
  have leaf := prepare_returns (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString)
    (bools := fun _ => false) (bits := fun _ _ => 0) run
  rw [qeq] at leaf
  obtain ⟨w, sm0, ty, tr, freshOut, ht, hty⟩ := emitLeaves_single leaf
  have stepEq : translateExprToWire
      (instE1 mn lvls (.fvar dId) (.fvar aId)) "out" false true =
      translateInstanceOrFallback (translateFuelFix translateStep 1048575)
        (instE1 mn lvls (.fvar dId) (.fvar aId)) "out" false true := by
    show translateStepWith translateFallback (translateFuelFix translateStep 1048575)
      (instE1 mn lvls (.fvar dId) (.fvar aId)) "out" false true = _
    exact instance1_step _ mn lvls _ _ _ _ _ hpure hbin hctrl hmux hsetw hreg
      hregEn hloopR hcdo hcdo2 hmem
  rw [stepEq] at tr
  unfold translateInstanceOrFallback at tr
  obtain ⟨env, sE, hEnvRead, tr⟩ := Returns.bind tr
  obtain ⟨hEnvM, hsE⟩ := Returns.liftMetaM_mreturns hEnvRead
  subst hsE
  rw [htag env hEnvM] at tr
  simp only [if_true] at tr
  obtain ⟨sub, sS, hSubRead, tr⟩ := Returns.bind tr
  obtain ⟨hSubM, hsS⟩ := Returns.liftMetaM_mreturns hSubRead
  subst hsS
  rw [hsub sub hSubM] at tr
  rw [show ((mc, dc).1.outputs) = mc.outputs from rfl, houts] at tr
  simp only [] at tr
  have empty0 := empty_layout (entryCompilerState false cache) declName.toString (fun _ => 0)
  have record0 : (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.translateRecord
      = {} :=
    (prepare_layout (bs.zip ids) _ empty0.1 empty0.2 (admissible_zero _ _)).2.2.2
  rcases translateControlCachedWith_returns tr with hit | ⟨smR, missRun, record⟩
  · obtain ⟨-, hrec⟩ := cacheLookupValidated_returns hit
    have dead := hrec w rfl
    rw [record0] at dead
    simp at dead
  rw [instanceUncached_run] at missRun
  obtain ⟨cs0, sG, hget0, k1⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) missRun
  obtain ⟨hcs0, hsG⟩ := Returns.get hget0
  subst hcs0 hsG
  have hpdes : (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.design =
      Design.empty declName.toString :=
    prepare_design (bs.zip ids) _
  rw [hdc] at k1
  obtain ⟨u0, sA, hAdd0, k2⟩ := Returns.bind (m := instAddModules _ []) k1
  obtain ⟨-, hsA⟩ := Returns.pure (by exact hAdd0 : Returns (pure ()) _ _ u0 sA)
  subst hsA
  obtain ⟨uR, sB, hReg, k3⟩ := Returns.bind (m := instRegisterChild _ mc) k2
  have hsB := instRegisterChild_fresh (by rw [hpdes]; rfl) (by rw [hpdes]; rfl) hReg
  -- clk/rst plumbing adds the two parent clock ports
  obtain ⟨conns0, sC, hClk, k4⟩ := Returns.bind (m := instClkRst [] mc.inputs) k3
  rw [hins] at hClk
  have hdecl0 := Tools.ShippingMixedEntrySoundness.prepare_declarations
    (bools := fun _ => false) (bits := fun _ _ => 0) (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString)
    (by exact List.nil_sublist _)
    (by rw [show (start (entryCompilerState false cache) declName.toString).state =
        CircuitM.init declName.toString from rfl, init_wires]
        intro x hx; cases hx)
  have hinAlloc : ∀ q ∈ (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.module.inputs,
      Sparkle.IR.NameHints.Allocated q.name :=
    fun q hq => hdecl0.2 q (hdecl0.1.subset hq)
  have hclkAny : sB.module.inputs.any (fun p => p.name == "clk") = false := by
    rw [hsB]
    apply List.any_eq_false.mpr
    intro q hq hcl
    exact not_allocated_clk ((eq_of_beq hcl) ▸ hinAlloc q hq)
  have hrstAny : (CircuitM.addInput "clk" .bit sB).2.module.inputs.any
      (fun p => p.name == "rst") = false := by
    rw [addInput_inputs]
    apply List.any_eq_false.mpr
    intro q hq hcl
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd (eq_of_beq hcl) (by decide)
    · rw [hsB] at hq
      exact not_allocated_rst ((eq_of_beq hcl) ▸ hinAlloc q hq)
  obtain ⟨hconns0, hsC⟩ := instClkRst_seq hx1 hx2 hclkAny hrstAny hClk
  subst hconns0 hsC
  have hfil : mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst") =
      [⟨xin, .bitVector wA⟩] := by
    rw [hins]
    simp [List.filter, bne, hx1, hx2]
  rw [hfil, instE1_getAppArgs] at k4
  obtain ⟨uG, sH, hGuard, k5⟩ := Returns.bind (m := instArityCheck mn _ _) k4
  obtain ⟨-, hsH⟩ := Returns.pure (by exact hGuard : Returns (pure ()) _ _ uG sH)
  subst hsH
  obtain ⟨conns, sF, hArgs, k6⟩ := Returns.bind (m := instArgs _ _ _ 0) k5
  unfold instArgs at hArgs
  obtain ⟨aW, sD, rA, hArgs⟩ :=
    Returns.bind (m := translateFuelFix translateStep 1048575 (Lean.Expr.fvar aId) _ _ _) hArgs
  obtain ⟨hconns, hsF⟩ := Returns.pure hArgs
  subst hconns hsF
  obtain ⟨csP, sP2, hgetP, k7⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) k6
  obtain ⟨hcsP, hsP2⟩ := Returns.get hgetP
  subst hcsP hsP2
  obtain ⟨cVal, sQ, hCacheRead, k8⟩ :=
    Returns.bind (m := CompilerM.liftMetaM instArmCacheGet) k7
  obtain ⟨hCacheM, hsQ⟩ := Returns.liftMetaM_mreturns hCacheRead
  subst hsQ
  simp only [hcachemiss cVal hCacheM] at k8
  obtain ⟨outW, sW, hMk, k9⟩ := Returns.bind (m := CompilerM.makeWire "out" _ true) k8
  obtain ⟨houtW, hsW⟩ := makeWireC_returns hMk
  obtain ⟨uP, sV, hPut, k10⟩ :=
    Returns.bind (m := CompilerM.liftMetaM (instArmCachePut _ _)) k9
  have hsV := Returns.liftMetaM hPut
  subst hsV
  obtain ⟨instName, sN, hFresh, k11⟩ := Returns.bind (m := CompilerM.freshName _) k10
  obtain ⟨hinstName, hsN⟩ := freshNameC_returns hFresh
  obtain ⟨uE, sI, hEmit, k12⟩ :=
    Returns.bind (m := CompilerM.emitInstance mc.name _ _) k11
  have hsI := emitInstanceC_returns hEmit
  obtain ⟨hwEq, hsmR⟩ := Returns.pure k12
  subst hwEq
  have hrec := recordTranslation_returns record
  refine ⟨instName, w, aW, ?_⟩
  intro bools bits env0 av a p adm ha0
  have empty := empty_layout (entryCompilerState false cache) declName.toString env0
  have prepared := prepare_layout (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString) empty.1 empty.2 adm
  obtain ⟨pc, ps⟩ := prepare_const (fun _ => false) bools (fun _ _ => 0) bits
    (bs.zip ids) _ _ rfl rfl
  rw [ps] at hsB
  rw [pc] at rA
  have fuelEq : translateFuelFix translateStep 1048575 =
      translateStepWith translateFallback (translateFuelFix translateStep 1048574) := rfl
  rw [fuelEq] at rA
  have designSB : ∀ (s : CircuitState) dd,
      ({ s with design := dd } : CircuitState).sourceBindings = s.sourceBindings :=
    fun _ _ => rfl
  have designMod : ∀ (s : CircuitState) dd,
      ({ s with design := dd } : CircuitState).module = s.module :=
    fun _ _ => rfl
  obtain ⟨aW', aBound, aDecl, aVal⟩ := prepared.1.bits aId wA av ha0
  have aBound2 : Tools.ShippingBindingsSoundness.visible
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
      ((CircuitM.addInput "rst" .bit
        (CircuitM.addInput "clk" .bit sB).2).2).sourceBindings aId = some aW' := by
    rw [addInput_sourceBindings, addInput_sourceBindings, hsB, designSB]
    exact aBound
  obtain ⟨haW, hsD⟩ := translateStep_fvar_returns aBound2 rA
  subst hsD
  rw [← haW] at aVal aDecl
  have hbodyR : (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.module.body
      = [] := by
    rw [prepared.2.2.1]; rfl
  have hpdesR : (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.design =
      Design.empty declName.toString := prepare_design (bs.zip ids) _
  have inputNotOut : ∀ (q : Sparkle.IR.AST.Port),
      q ∈ (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.module.wires →
      q.name ≠ "out" := by
    intro q hq eq
    have alloc := prepare_wires_allocated bools bits (bs.zip ids) _
      (by rw [show (start (entryCompilerState false cache) declName.toString).state =
          CircuitM.init declName.toString from rfl, init_wires]
          intro x hx; cases hx) q hq
    rw [eq] at alloc
    exact not_allocated_out alloc
  have addOutBody : ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).body = mo.body :=
    fun _ _ => rfl
  have stBody : st.module.body =
      .assign "out" (.ref w) ::
        .inst mc.name instName
          ((((⟨"out", .bitVector wOut⟩ : Port).name, Sparkle.IR.AST.Expr.ref w) ::
            ((⟨xin, .bitVector wA⟩ : Port).name, Sparkle.IR.AST.Expr.ref aW) ::
            ("rst", Sparkle.IR.AST.Expr.ref "rst") ::
            ("clk", Sparkle.IR.AST.Expr.ref "clk") :: []).reverse) ::
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).state.module.body := by
    rw [ht, emitAssign_body_cons, addOutput_state]
    show _ :: (sm0.module.addOutput _).body = _
    rw [addOutBody, hrec]
    show _ :: smR.module.body = _
    rw [hsmR, hsI]
    show _ :: (_ :: sN.module.body) = _
    rw [hsN, (CircuitM.freshName_spec _ _ _).2.2, hsW]
    rw [(CircuitM.makeWire_spec "out" _ true _).2.2.1]
    rw [addInput_body, addInput_body, hsB, designMod]
  have mBody : m.body = (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.module.body.reverse ++
      [.inst mc.name instName
        ((((⟨"out", .bitVector wOut⟩ : Port).name, Sparkle.IR.AST.Expr.ref w) ::
          ((⟨xin, .bitVector wA⟩ : Port).name, Sparkle.IR.AST.Expr.ref aW) ::
          ("rst", Sparkle.IR.AST.Expr.ref "rst") ::
          ("clk", Sparkle.IR.AST.Expr.ref "clk") :: []).reverse),
       .assign "out" (.ref w)] := by
    rw [hm]
    show ((addClockResetIfSequential st.module).finalize).body = _
    simp only [Sparkle.IR.AST.Module.finalize,
      (addClockReset_facts st.module).1, stBody]
    simp
  have stDesign : st.design = ((prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.design).addModule mc := by
    rw [ht]
    show sm0.design = _
    rw [hrec]
    show smR.design = _
    rw [hsmR, hsI]
    show sN.design = _
    rw [hsN]
    rw [show ∀ s, ((CircuitM.freshName (toString "inst_" ++ toString mc.name) false s).2).design
        = s.design from fun s => freshName_design _ _ s, hsW]
    rw [makeWire_design]
    rw [addInput_design, addInput_design, hsB]
  have emitAssignInputs : ∀ (l : String) (r : Sparkle.IR.AST.Expr) (s : CircuitState),
      (CircuitM.emitAssign l r s).2.module.inputs = s.module.inputs :=
    fun _ _ _ => rfl
  have addOutputInputs : ∀ (n : String) (ty : Sparkle.IR.Type.HWType) (s : CircuitState),
      (CircuitM.addOutput n ty s).2.module.inputs = s.module.inputs :=
    fun _ _ _ => rfl
  have makeWireInputs : ∀ (h : String) (ty : Sparkle.IR.Type.HWType) (n : Bool)
      (s : CircuitState),
      (CircuitM.makeWire h ty n s).2.module.inputs = s.module.inputs := by
    intro h ty n s
    show ((CircuitM.freshName (CircuitM.sanitizeName h) n s).2.module.addWire _).inputs = _
    rw [(CircuitM.freshName_spec _ _ _).2.2]
    rfl
  have stInputs : st.module.inputs =
      ⟨"rst", .bit⟩ :: ⟨"clk", .bit⟩ :: (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.module.inputs := by
    rw [ht]
    show (CircuitM.emitAssign "out" _ (CircuitM.addOutput "out" ty sm0).2).2.module.inputs = _
    rw [emitAssignInputs, addOutputInputs, hrec]
    show smR.module.inputs = _
    rw [hsmR, hsI]
    show sN.module.inputs = _
    rw [hsN, (CircuitM.freshName_spec _ _ _).2.2, hsW, makeWireInputs]
    rw [addInput_inputs, addInput_inputs, hsB, designMod]
  have hclkMem : (⟨"clk", .bit⟩ : Port) ∈ m.inputs := by
    rw [hm]
    show _ ∈ ((addClockResetIfSequential st.module).finalize).inputs
    show _ ∈ (addClockResetIfSequential st.module).inputs.reverse
    rw [List.mem_reverse]
    exact (addClockReset_facts st.module).2.2.2 _
      (by rw [stInputs]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hrstMem : (⟨"rst", .bit⟩ : Port) ∈ m.inputs := by
    rw [hm]
    show _ ∈ ((addClockResetIfSequential st.module).finalize).inputs
    show _ ∈ (addClockResetIfSequential st.module).inputs.reverse
    rw [List.mem_reverse]
    exact (addClockReset_facts st.module).2.2.2 _
      (by rw [stInputs]; exact List.mem_cons_self)
  have wNotOut : w ≠ "out" := by
    intro eq
    have alloc := CircuitM.makeWire_allocated "out"
      (Sparkle.IR.Type.HWType.bitVector wOut) true
      (CircuitM.addInput "rst" Sparkle.IR.Type.HWType.bit
        (CircuitM.addInput "clk" Sparkle.IR.Type.HWType.bit sB).2).2
    rw [← houtW, eq] at alloc
    exact not_allocated_out alloc
  refine ⟨?_, ?_, hclkMem, hrstMem, wNotOut, inputNotOut _ aDecl, aVal⟩
  · rw [mBody, hbodyR]
    rfl
  · rw [hd, stDesign, hpdesR]
    rfl

/-- The run's predicate on the quoted one-input call computes to the tag check. -/
theorem instancePredicate_instE1 (env : Environment) (mn : Name) (lvls : List Level)
    (dom a : Lean.Expr) :
    Sparkle.Compiler.Elab.instancePredicate env (instE1 mn lvls dom a) =
      Sparkle.Compiler.isHardwareModule env mn := rfl

/-- The run's predicate on the quoted call computes to the tag check. -/
theorem instancePredicate_instE2 (env : Environment) (mn : Name) (lvls : List Level)
    (dom a b : Lean.Expr) :
    Sparkle.Compiler.Elab.instancePredicate env (instE2 mn lvls dom a b) =
      Sparkle.Compiler.isHardwareModule env mn := rfl

/-- The declaration dispatcher selects the proved instance path. Unlike the
old families, the shape premise lives AT the run's predicate — instance
acceptance genuinely depends on the environment's tags. -/
theorem synthesizeFromConst_instance_sound {logProf declName ci bs body m d}
    {isInst : Lean.Expr → Bool}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      [] false true ci isInst) (m, d)) :
    InstancePreserves declName bs body m d := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_instance_sound run

/-- The one-input dispatcher, mirroring the two-input one. -/
theorem synthesizeFromConst_instance1_sound {logProf declName ci bs body m d}
    {isInst : Lean.Expr → Bool}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      [] false true ci isInst) (m, d)) :
    Instance1Preserves declName bs body m d := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_instance1_sound run

/-- The instance result is tied to the declaration AND the environment THIS
run read: the gate holds at `instancePredicate envR` for the run's own
`getEnv` result, exposed here alongside `getConstInfo`. -/
theorem synthesizeCombinationalCore_instance_sound {declName : Name}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, d) w') :
    ∃ (ci : ConstantInfo) (envR : Environment) (w1 w2 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        mixedCertifiedShape? false [] ci
          (Sparkle.Compiler.Elab.instancePredicate envR) = some (bs, body) →
        InstancePreserves declName bs body m d ∧
        Instance1Preserves declName bs body m d := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    Tools.ShippingEntrySoundness.synthesizeCombinationalCore_reads hr
  exact ⟨ci, envR, w1, w2, w5, w6, get, henv, fun _ _ old shape =>
    ⟨synthesizeFromConst_instance_sound old shape run.mreturns,
     synthesizeFromConst_instance1_sound old shape run.mreturns⟩⟩

/-- The entry endpoint under the run's environment boundaries: if the run's
environment defines the declaration as the canonical two-input instance call
on a `@[hardware_module]`-tagged child (and the declaration's type is one
scalar Signal), the compiled pair satisfies the instance contract. -/
theorem instance_entry_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {value : Lean.Expr}
    {mn : Name} {lvls : List Level} {dpos apos bpos : Nat}
    {bs : List (Name × MixedGateBinder)}
    {kd ka kb : MixedGateBinder} {nd na nb : Name}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, d) w')
    (env : Tools.ShippingEntrySoundness.EnvDefines mctx mref cctx cref declName value)
    (tag : ∀ wE e wE', RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref wE e wE' →
      Sparkle.Compiler.isHardwareModule e mn = true)
    (old : ∀ dv : DefinitionVal, dv.value = value →
      certifiedShape? false [] (.defnInfo dv) = none)
    (hscalar : ∀ dv : DefinitionVal, dv.value = value →
      mixedGateResultScalar dv.type = true)
    (peel : mixedGatePeel value = some (bs,
      instE2 mn lvls (inputExpr bs.length dpos) (inputExpr bs.length apos)
        (inputExpr bs.length bpos)))
    (hd : bs[dpos]? = some (nd, kd)) (ha : bs[apos]? = some (na, ka))
    (hb : bs[bpos]? = some (nb, kb)) :
    InstancePreserves declName bs
      (instE2 mn lvls (inputExpr bs.length dpos) (inputExpr bs.length apos)
        (inputExpr bs.length bpos)) m d := by
  obtain ⟨ci, envR, w1, w2, w5, w6, get, henv, sel⟩ :=
    synthesizeCombinationalCore_instance_sound hr
  obtain ⟨dv, rfl, hval⟩ := env w1 ci w2 get
  have htag : Sparkle.Compiler.Elab.instancePredicate envR
      (instE2 mn lvls (inputExpr bs.length dpos) (inputExpr bs.length apos)
        (inputExpr bs.length bpos)) = true := by
    rw [instancePredicate_instE2]
    exact tag _ _ _ henv
  have shape := instance_term_gate (d := dv) (by rw [hval]; exact peel) htag
    (hscalar dv hval) hd ha hb
  exact (sel bs _ (old dv hval) shape).1

/-- The one-input entry endpoint under the run's environment boundaries. -/
theorem instance1_entry_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {value : Lean.Expr}
    {mn : Name} {lvls : List Level} {dpos apos : Nat}
    {bs : List (Name × MixedGateBinder)}
    {kd ka : MixedGateBinder} {nd na : Name}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, d) w')
    (env : Tools.ShippingEntrySoundness.EnvDefines mctx mref cctx cref declName value)
    (tag : ∀ wE e wE', RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref wE e wE' →
      Sparkle.Compiler.isHardwareModule e mn = true)
    (old : ∀ dv : DefinitionVal, dv.value = value →
      certifiedShape? false [] (.defnInfo dv) = none)
    (hscalar : ∀ dv : DefinitionVal, dv.value = value →
      mixedGateResultScalar dv.type = true)
    (peel : mixedGatePeel value = some (bs,
      instE1 mn lvls (inputExpr bs.length dpos) (inputExpr bs.length apos)))
    (hd : bs[dpos]? = some (nd, kd)) (ha : bs[apos]? = some (na, ka)) :
    Instance1Preserves declName bs
      (instE1 mn lvls (inputExpr bs.length dpos) (inputExpr bs.length apos)) m d := by
  obtain ⟨ci, envR, w1, w2, w5, w6, get, henv, sel⟩ :=
    synthesizeCombinationalCore_instance_sound hr
  obtain ⟨dv, rfl, hval⟩ := env w1 ci w2 get
  have htag : Sparkle.Compiler.Elab.instancePredicate envR
      (instE1 mn lvls (inputExpr bs.length dpos) (inputExpr bs.length apos)) = true := by
    rw [instancePredicate_instE1]
    exact tag _ _ _ henv
  have shape := instance1_term_gate (d := dv) (by rw [hval]; exact peel) htag
    (hscalar dv hval) hd ha
  exact (sel bs _ (old dv hval) shape).2

end Tools.ShippingInstanceEntrySoundness

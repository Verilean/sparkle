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
open Tools.ShippingLinkCtx (Linked instLinked_sound)

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
    (hkind : fallbackKind (instE2 mn lvls dF aF bF) = .other) :
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
  simp only [translateFallback, hkind]

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

/-- A passed linkage check leaves the state untouched and certifies the
linkage of the statement about to be emitted. -/
theorem instLinkCheck_returns {recName : Name} {child : Sparkle.IR.AST.Module}
    {conns : List (String × Sparkle.IR.AST.Expr)}
    {ctx : CompilerState} {s s' : CircuitState} {u : Unit}
    (h : Returns (instLinkCheck recName child conns) ctx s u s') :
    s' = s ∧ instLinked s.module child conns = true := by
  unfold instLinkCheck at h
  obtain ⟨cs, s1, hget, k⟩ := Returns.bind (m := (get : CompilerM CircuitState)) h
  obtain ⟨hcs, hs1⟩ := Returns.get hget
  rw [hcs, hs1] at k
  unfold instLinkGuard at k
  cases hl : instLinked s.module child conns with
  | true =>
    rw [hl] at k
    obtain ⟨-, hs⟩ := Returns.pure (by exact k : Returns (pure ()) _ _ u s')
    exact ⟨hs, rfl⟩
  | false =>
    rw [hl] at k
    exact (Returns.throw (by exact k)).elim

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

theorem instE2_spineArgs (mn : Name) (lvls : List Level) (dom a b : Lean.Expr) :
    instSpineArgs (instE2 mn lvls dom a b) = [dom, a, b] := rfl

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

/-- No cache entry validates against an empty record: at a root call the
single-out dedupe cache cannot hit, whatever it holds. -/
theorem instHit_empty (o : Option String) (e : Lean.Expr) :
    o.filter (instHitValid {} e) = none := by
  cases o with
  | none => rfl
  | some cw =>
    have : instHitValid {} e cw = false := by
      unfold instHitValid
      simp
    simp [Option.filter, this]

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
        (instSpineArgs e).length
      let connections ← instArgs rec connections0
        ((mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst")).zip
          ((instSpineArgs e).drop ((instSpineArgs e).length -
            (mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst")).length))) 0
      let csP ← get
      let instCache ← CompilerM.liftMetaM instArmCacheGet
      match (instCache.get? s!"{csP.module.name}#{mc.name}#{String.intercalate ";"
          (connections.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))}").filter
          (instHitValid cs0.translateRecord e) with
      | some cachedW => pure cachedW
      | _ => do
        let w ← CompilerM.makeWire hint so.ty (named := named)
        CompilerM.liftMetaM (instArmCachePut s!"{csP.module.name}#{mc.name}#{String.intercalate ";"
          (connections.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))}" w)
        let instName ← CompilerM.freshName s!"inst_{mc.name}"
        instLinkCheck mn mc (((so.name, Sparkle.IR.AST.Expr.ref w) :: connections).reverse)
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
    fallbackKind (instE2 mn lvls (.fvar dId) (.fvar aId) (.fvar bId)) = .other →
    -- the run boundaries
    HardwareTagged mn → SubSynthDefines mn mc dc →
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
  intro mn lvls dId aId bId mc dc wOut wA wB xin yin qeq hpure hbin hkind htag hsub hdc hins houts hx1 hx2 hy1 hy2
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
    exact instance_step _ mn lvls _ _ _ _ _ _ hpure hbin hkind
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
  rw [hfil, instE2_spineArgs] at k4
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
  rw [record0, instHit_empty] at k8
  simp only [] at k8
  -- the result wire, the cache insert, the instance name, the statement
  obtain ⟨outW, sW, hMk, k9⟩ := Returns.bind (m := CompilerM.makeWire "out" _ true) k8
  obtain ⟨houtW, hsW⟩ := makeWireC_returns hMk
  obtain ⟨uP, sV, hPut, k10⟩ :=
    Returns.bind (m := CompilerM.liftMetaM (instArmCachePut _ _)) k9
  have hsV := Returns.liftMetaM hPut
  subst hsV
  obtain ⟨instName, sN, hFresh, k11⟩ := Returns.bind (m := CompilerM.freshName _) k10
  obtain ⟨hinstName, hsN⟩ := freshNameC_returns hFresh
  obtain ⟨uL, sL, hLink, k11⟩ := Returns.bind (m := instLinkCheck _ _ _) k11
  obtain ⟨hsL, hlinked⟩ := instLinkCheck_returns hLink
  rw [hsL] at k11
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

theorem instE1_spineArgs (mn : Name) (lvls : List Level) (dom a : Lean.Expr) :
    instSpineArgs (instE1 mn lvls dom a) = [dom, a] := rfl

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
    (hkind : fallbackKind (instE1 mn lvls dF aF) = .other) :
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
  simp only [translateFallback, hkind]

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
    fallbackKind (instE1 mn lvls (.fvar dId) (.fvar aId)) = .other →
    HardwareTagged mn → SubSynthDefines mn mc dc →
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
  intro mn lvls dId aId mc dc wOut wA xin qeq hpure hbin hkind htag hsub hdc hins houts hx1 hx2
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
    exact instance1_step _ mn lvls _ _ _ _ _ hpure hbin hkind
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
  rw [hfil, instE1_spineArgs] at k4
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
  rw [record0, instHit_empty] at k8
  simp only [] at k8
  obtain ⟨outW, sW, hMk, k9⟩ := Returns.bind (m := CompilerM.makeWire "out" _ true) k8
  obtain ⟨houtW, hsW⟩ := makeWireC_returns hMk
  obtain ⟨uP, sV, hPut, k10⟩ :=
    Returns.bind (m := CompilerM.liftMetaM (instArmCachePut _ _)) k9
  have hsV := Returns.liftMetaM hPut
  subst hsV
  obtain ⟨instName, sN, hFresh, k11⟩ := Returns.bind (m := CompilerM.freshName _) k10
  obtain ⟨hinstName, hsN⟩ := freshNameC_returns hFresh
  obtain ⟨uL, sL, hLink, k11⟩ := Returns.bind (m := instLinkCheck _ _ _) k11
  obtain ⟨hsL, hlinked⟩ := instLinkCheck_returns hLink
  rw [hsL] at k11
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

/-! ## The n-ary canonical call (combinational children of any arity) -/

/-- The n-ary canonical instance call: `@mn dom a₁ … aₙ`. -/
def instEN (mn : Name) (lvls : List Level) (dom : Lean.Expr)
    (args : List Lean.Expr) : Lean.Expr :=
  args.foldl (fun f a => .app f a) (.app (.const mn lvls) dom)

theorem spineArgs_foldl (f : Lean.Expr) (args : List Lean.Expr) :
    instSpineArgs (args.foldl (fun f a => .app f a) f) = instSpineArgs f ++ args := by
  induction args generalizing f with
  | nil => simp
  | cons a as ih =>
    rw [List.foldl_cons, ih]
    show (instSpineArgs f ++ [a]) ++ as = _
    simp

theorem instEN_spineArgs (mn : Name) (lvls : List Level) (dom : Lean.Expr)
    (args : List Lean.Expr) :
    instSpineArgs (instEN mn lvls dom args) = dom :: args := by
  unfold instEN
  rw [spineArgs_foldl]
  rfl

theorem getAppFn_foldl (f : Lean.Expr) (args : List Lean.Expr) :
    (args.foldl (fun f a => .app f a) f).getAppFn = f.getAppFn := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldl_cons, ih]
    rfl

theorem instEN_getAppFn (mn : Name) (lvls : List Level) (dom : Lean.Expr)
    (args : List Lean.Expr) :
    (instEN mn lvls dom args).getAppFn = .const mn lvls := by
  unfold instEN
  rw [getAppFn_foldl]
  rfl

theorem instFVars_foldl (xs : Array Lean.Expr) (d : Nat) (f : Lean.Expr)
    (args : List Lean.Expr) :
    instFVars xs d (args.foldl (fun f a => .app f a) f) =
      (args.map (instFVars xs d)).foldl (fun f a => .app f a) (instFVars xs d f) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldl_cons, ih]
    rfl

theorem instFVars_instEN (xs : Array Lean.Expr) (d : Nat) (mn : Name)
    (lvls : List Level) (dom : Lean.Expr) (args : List Lean.Expr) :
    instFVars xs d (instEN mn lvls dom args) =
      instEN mn lvls (instFVars xs d dom) (args.map (instFVars xs d)) := by
  unfold instEN
  rw [instFVars_foldl]
  rfl

/-- The call is an application whatever the arity. -/
theorem foldl_app_isApp (f : Lean.Expr) (args : List Lean.Expr) (hf : f.isApp = true) :
    (args.foldl (fun f a => .app f a) f).isApp = true := by
  induction args generalizing f with
  | nil => exact hf
  | cons a as ih => exact ih (.app f a) rfl

theorem foldl_app_shape (f : Lean.Expr) (args : List Lean.Expr)
    (hf : ∃ g a, f = .app g a) :
    ∃ g a, args.foldl (fun f a => .app f a) f = .app g a := by
  induction args generalizing f with
  | nil => exact hf
  | cons a as ih => exact ih (.app f a) ⟨f, a, rfl⟩

theorem instEN_app (mn : Name) (lvls : List Level) (dom : Lean.Expr)
    (args : List Lean.Expr) :
    ∃ f a, instEN mn lvls dom args = .app f a := by
  unfold instEN
  exact foldl_app_shape _ _ ⟨_, _, rfl⟩

theorem unifiedInstanceSpine_foldl {kinds : Array MixedGateBinder} (f : Lean.Expr)
    (args : List Lean.Expr) (hf : unifiedInstanceSpine kinds f = true)
    (hargs : ∀ a ∈ args, ∃ i, a = .bvar i ∧ (mixedGateBVar? kinds i).isSome = true) :
    unifiedInstanceSpine kinds (args.foldl (fun f a => .app f a) f) = true := by
  induction args generalizing f with
  | nil => exact hf
  | cons a as ih =>
    obtain ⟨i, rfl, hi⟩ := hargs a List.mem_cons_self
    apply ih
    · show ((mixedGateBVar? kinds i).isSome && unifiedInstanceSpine kinds f) = true
      rw [hi, hf]
      rfl
    · exact fun b hb => hargs b (List.mem_cons_of_mem _ hb)

/-- Gate acceptance for the n-ary canonical parent, AT the run's predicate. -/
theorem instanceN_term_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {mn : Name} {lvls : List Level} {dpos : Nat} {poss : List Nat}
    {isInst : Lean.Expr → Bool}
    (peel : mixedGatePeel d.value = some (bs,
      instEN mn lvls (inputExpr bs.length dpos) (poss.map (inputExpr bs.length))))
    (htag : isInst (instEN mn lvls (inputExpr bs.length dpos)
      (poss.map (inputExpr bs.length))) = true)
    (hscalar : mixedGateResultScalar d.type = true)
    (hd : ∃ nd kd, bs[dpos]? = some (nd, kd))
    (hpos : ∀ q ∈ poss, ∃ nq kq, bs[q]? = some (nq, kq)) :
    mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs,
      instEN mn lvls (inputExpr bs.length dpos) (poss.map (inputExpr bs.length))) := by
  have spine : unifiedInstanceSpine (bs.map (·.2)).toArray
      (instEN mn lvls (inputExpr bs.length dpos) (poss.map (inputExpr bs.length))) = true := by
    unfold instEN
    apply unifiedInstanceSpine_foldl
    · obtain ⟨nd, kd, hdp⟩ := hd
      show ((mixedGateBVar? (bs.map Prod.snd).toArray (bs.length - 1 - dpos)).isSome &&
        true) = true
      rw [mixedGateBVar?_pos hdp]
      rfl
    · intro a ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      obtain ⟨nq, kq, hqp⟩ := hpos q hq
      refine ⟨bs.length - 1 - q, rfl, ?_⟩
      rw [mixedGateBVar?_pos hqp]
      rfl
  have happ : (instEN mn lvls (inputExpr bs.length dpos)
      (poss.map (inputExpr bs.length))).isApp = true := by
    unfold instEN
    exact foldl_app_isApp _ _ rfl
  have root : unifiedInstanceRoot isInst (bs.map (·.2)).toArray
      (instEN mn lvls (inputExpr bs.length dpos) (poss.map (inputExpr bs.length))) = true := by
    unfold unifiedInstanceRoot
    rw [htag, happ, spine]
    rfl
  simp only [mixedCertifiedShape?, List.isEmpty_nil, Bool.not_true,
    peel, root, hscalar, Bool.true_and, Bool.true_or, if_true]
  rfl

set_option maxHeartbeats 1000000 in
/-- One certified step on the n-ary canonical call lands in the instance arm. -/
theorem instanceN_step (rec : TranslateFn) (mn : Name) (lvls : List Level)
    (dF : Lean.Expr) (argsF : List Lean.Expr) (hint : String) (top named : Bool)
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hkind : fallbackKind (instEN mn lvls dF argsF) = .other) :
    translateStepWith translateFallback rec (instEN mn lvls dF argsF) hint top named =
      translateInstanceOrFallback rec (instEN mn lvls dF argsF) hint top named := by
  have hfn := instEN_getAppFn mn lvls dF argsF
  have shape : translateCoreShape (instEN mn lvls dF argsF) = false := by
    unfold translateCoreShape
    rw [hfn]
    show ((mn == ``Sparkle.Core.Signal.Signal.pure) ||
      (match signalBinOpOf mn,
          canonicalSignalBinKinds mn (instEN mn lvls dF argsF).getAppArgs,
          canonicalSignalBitVecWidth (instEN mn lvls dF argsF).getAppArgs with
       | some _, some (true, true), some _ => true
       | _, _, _ => false)) = false
    rw [hpure, hbin]
    rfl
  have core : translateCore rec (instEN mn lvls dF argsF) hint top named = pure none := by
    obtain ⟨f, a, he⟩ := instEN_app mn lvls dF argsF
    rw [he] at hfn ⊢
    show (match (Lean.Expr.app f a).getAppFn with
      | .const m _ =>
        if m == ``Sparkle.Core.Signal.Signal.pure then
          translateSignalPureLiteral? (Lean.Expr.app f a).getAppArgs hint named
        else
          match signalBinOpOf m, canonicalSignalBinKinds m (Lean.Expr.app f a).getAppArgs,
              canonicalSignalBitVecWidth (Lean.Expr.app f a).getAppArgs with
          | some op, some (true, true), some _ => do
            let w ← translateCanonicalSignalBinary rec (Lean.Expr.app f a) op
              (Lean.Expr.app f a).getAppArgs true true hint named
            pure (some w)
          | _, _, _ => pure none
      | _ => pure none) = pure none
    rw [hfn]
    simp only [hpure, Bool.false_eq_true, if_false, hbin]
  have step : translateStepWith translateFallback rec
      (instEN mn lvls dF argsF) hint top named =
      translateFallback rec (instEN mn lvls dF argsF) hint top named := by
    simp [translateStepWith, shape, core]
    rfl
  rw [step]
  simp only [translateFallback, hkind]

/-- Choose one witness per index, as a list. -/
theorem list_choice : ∀ (n : Nat) (Q : (i : Nat) → i < n → String → Prop),
    (∀ i hi, ∃ w, Q i hi w) →
    ∃ l : List String, l.length = n ∧ ∀ i (hi : i < n) (hl : i < l.length), Q i hi (l[i]'hl)
  | 0, _, _ => ⟨[], rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | n + 1, Q, h => by
    obtain ⟨w0, hw0⟩ := h 0 (Nat.succ_pos n)
    obtain ⟨l, hlen, hl⟩ := list_choice n
      (fun i hi w => Q (i + 1) (Nat.succ_lt_succ hi) w)
      (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))
    refine ⟨w0 :: l, by simp [hlen], ?_⟩
    intro i hi hli
    cases i with
    | zero => exact hw0
    | succ i => exact hl i (Nat.lt_of_succ_lt_succ hi) (by simpa using hli)

/-- The argument walk over bound input variables: every operand read is a
pure lookup, so the builder state is untouched and the connection list is
the port/wire pairing (prepended in walk order). -/
theorem instArgs_resolve {rec' : TranslateFn} {ctx : CompilerState} {s : CircuitState} :
    ∀ (pairs : List (Port × Lean.Expr)) (wires : List String)
      (acc : List (String × Sparkle.IR.AST.Expr)) (i : Nat)
      (r : List (String × Sparkle.IR.AST.Expr)) (s' : CircuitState),
    pairs.length = wires.length →
    (∀ k (hk : k < pairs.length) (hk' : k < wires.length),
      ∃ id, (pairs[k]'hk).2 = .fvar id ∧
        Tools.ShippingBindingsSoundness.visible ctx s.sourceBindings id =
          some (wires[k]'hk')) →
    Returns (instArgs (translateStepWith translateFallback rec') acc pairs i) ctx s r s' →
    s' = s ∧ r = ((pairs.zip wires).map
      (fun pw => (pw.1.1.name, Sparkle.IR.AST.Expr.ref pw.2))).reverse ++ acc
  | [], wires, acc, i, r, s', hlen, _, h => by
    unfold instArgs at h
    obtain ⟨hr, hs⟩ := Returns.pure h
    exact ⟨hs, by rw [hr]; rfl⟩
  | (p, e) :: rest, [], acc, i, r, s', hlen, _, _ => by
    simp at hlen
  | (p, e) :: rest, w :: ws, acc, i, r, s', hlen, hb, h => by
    unfold instArgs at h
    obtain ⟨id, he, hvis⟩ := hb 0 (by simp) (by simp)
    have he' : e = .fvar id := he
    subst he'
    obtain ⟨aw, s1, hread, hrest⟩ :=
      Returns.bind (m := translateStepWith translateFallback rec' (.fvar id) _ _ _) h
    obtain ⟨haw, hs1⟩ := translateStep_fvar_returns hvis hread
    subst hs1
    obtain ⟨hs', hr⟩ := instArgs_resolve rest ws ((p.name, .ref aw) :: acc) (i + 1) r s'
      (by simpa using hlen)
      (fun k hk hk' => by
        have := hb (k + 1) (by simpa using hk) (by simpa using hk')
        simpa using this)
      hrest
    refine ⟨hs', ?_⟩
    rw [hr, haw]
    simp

/-! ## The n-ary combinational contract and monolith -/

/-- The mixed certified entry's guarantee when the quoted body is the
canonical n-ary instance call on a combinational single-output child: the
compiled parent is one instance statement over the connection list (in port
order) plus the output alias, the design holds exactly the pinned child,
and each connection reads the prepared input wire of its argument. -/
def InstanceNPreserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) (d : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (mn : Name) (lvls : List Level) (dId : FVarId) (argIds : List FVarId)
      (mc : Sparkle.IR.AST.Module) (dc : Design) (wOut : Nat) (ports : List Port),
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      instEN mn lvls (.fvar dId) (argIds.map Lean.Expr.fvar) →
    (mn == ``Sparkle.Core.Signal.Signal.pure) = false →
    signalBinOpOf mn = none →
    fallbackKind (instEN mn lvls (.fvar dId) (argIds.map Lean.Expr.fvar)) = .other →
    HardwareTagged mn → SubSynthDefines mn mc dc →
    dc.modules = [] →
    mc.inputs = ports →
    mc.outputs = [⟨"out", .bitVector wOut⟩] →
    (∀ p ∈ ports, (p.name == "clk") = false ∧ (p.name == "rst") = false) →
    ports.length = argIds.length →
    ∃ (instName outW : String) (conns : List (String × Sparkle.IR.AST.Expr)),
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) (ws : Nat → Nat) (vals : (i : Nat) → BitVec (ws i)),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits env0 (bs.zip ids) a →
    (∀ i (h : i < argIds.length), p.bits (argIds[i]'h) = some ⟨ws i, vals i⟩) →
    m.body = [.inst mc.name instName (conns.reverse ++ [("out", .ref outW)]),
      .assign "out" (.ref outW)] ∧
    d.modules = [mc] ∧
    outW ≠ "out" ∧
    ∃ aWs : List String, aWs.length = argIds.length ∧
      conns.reverse = ((ports.zip (argIds.map Lean.Expr.fvar)).zip aWs).map
        (fun pw => (pw.1.1.name, Sparkle.IR.AST.Expr.ref pw.2)) ∧
      ∀ i (h : i < aWs.length),
        env0 (aWs[i]'h) = (vals i).toNat ∧ aWs[i]'h ≠ "out"

set_option maxHeartbeats 2000000 in
theorem synthesizeMixedCertified_instanceN_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d)) :
    InstanceNPreserves declName bs body m d := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, hd, -⟩ :=
    synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro mn lvls dId argIds mc dc wOut ports qeq hpure hbin hkind htag hsub hdc hins houts hnoclk hlenP
  have leaf := prepare_returns (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString)
    (bools := fun _ => false) (bits := fun _ _ => 0) run
  rw [qeq] at leaf
  obtain ⟨w, sm0, ty, tr, freshOut, ht, hty⟩ := emitLeaves_single leaf
  have stepEq : translateExprToWire
      (instEN mn lvls (.fvar dId) (argIds.map Lean.Expr.fvar)) "out" false true =
      translateInstanceOrFallback (translateFuelFix translateStep 1048575)
        (instEN mn lvls (.fvar dId) (argIds.map Lean.Expr.fvar)) "out" false true := by
    show translateStepWith translateFallback (translateFuelFix translateStep 1048575)
      (instEN mn lvls (.fvar dId) (argIds.map Lean.Expr.fvar)) "out" false true = _
    exact instanceN_step _ mn lvls _ _ _ _ _ hpure hbin hkind
  rw [stepEq] at tr
  unfold translateInstanceOrFallback at tr
  rw [instEN_getAppFn] at tr
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
  obtain ⟨conns0, sC, hClk, k4⟩ := Returns.bind (m := instClkRst [] mc.inputs) k3
  rw [hins] at hClk
  obtain ⟨hconns0, hsC⟩ := instClkRst_skip hnoclk hClk
  subst hconns0 hsC
  have hfil : mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst") = ports := by
    rw [hins]
    apply List.filter_eq_self.mpr
    intro p hp
    obtain ⟨h1, h2⟩ := hnoclk p hp
    simp [bne, h1, h2]
  rw [hfil, instEN_spineArgs] at k4
  -- the arity guard: one more spine argument (the domain) than ports
  obtain ⟨uG, sH, hGuard, k5⟩ := Returns.bind (m := instArityCheck mn _ _) k4
  unfold instArityCheck at hGuard
  rw [if_neg (by simp [hlenP])] at hGuard
  obtain ⟨-, hsH⟩ := Returns.pure hGuard
  subst hsH
  -- the argument walk stays opaque until the valuation is known
  have hdrop : (Lean.Expr.fvar dId :: argIds.map Lean.Expr.fvar).drop
      ((Lean.Expr.fvar dId :: argIds.map Lean.Expr.fvar).length - ports.length) =
      argIds.map Lean.Expr.fvar := by
    simp [hlenP]
  rw [hdrop] at k5
  obtain ⟨conns, sF, hArgs, k6⟩ := Returns.bind (m := instArgs _ _ _ 0) k5
  obtain ⟨csP, sP2, hgetP, k7⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) k6
  obtain ⟨hcsP, hsP2⟩ := Returns.get hgetP
  subst hcsP hsP2
  obtain ⟨cVal, sQ, hCacheRead, k8⟩ :=
    Returns.bind (m := CompilerM.liftMetaM instArmCacheGet) k7
  obtain ⟨hCacheM, hsQ⟩ := Returns.liftMetaM_mreturns hCacheRead
  subst hsQ
  rw [record0, instHit_empty] at k8
  simp only [] at k8
  obtain ⟨outW, sW, hMk, k9⟩ := Returns.bind (m := CompilerM.makeWire "out" _ true) k8
  obtain ⟨houtW, hsW⟩ := makeWireC_returns hMk
  obtain ⟨uP, sV, hPut, k10⟩ :=
    Returns.bind (m := CompilerM.liftMetaM (instArmCachePut _ _)) k9
  have hsV := Returns.liftMetaM hPut
  subst hsV
  obtain ⟨instName, sN, hFresh, k11⟩ := Returns.bind (m := CompilerM.freshName _) k10
  obtain ⟨hinstName, hsN⟩ := freshNameC_returns hFresh
  obtain ⟨uL, sL, hLink, k11⟩ := Returns.bind (m := instLinkCheck _ _ _) k11
  obtain ⟨hsL, hlinked⟩ := instLinkCheck_returns hLink
  rw [hsL] at k11
  obtain ⟨uE, sI, hEmit, k12⟩ :=
    Returns.bind (m := CompilerM.emitInstance mc.name _ _) k11
  have hsI := emitInstanceC_returns hEmit
  obtain ⟨hwEq, hsmR⟩ := Returns.pure k12
  subst hwEq
  have hrec := recordTranslation_returns record
  refine ⟨instName, w, conns, ?_⟩
  intro bools bits env0 ws vals a p adm hb
  have empty := empty_layout (entryCompilerState false cache) declName.toString env0
  have prepared := prepare_layout (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString) empty.1 empty.2 adm
  obtain ⟨pc, ps⟩ := prepare_const (fun _ => false) bools (fun _ _ => 0) bits
    (bs.zip ids) _ _ rfl rfl
  rw [ps] at hsB
  rw [pc] at hArgs
  have fuelEq : translateFuelFix translateStep 1048575 =
      translateStepWith translateFallback (translateFuelFix translateStep 1048574) := rfl
  rw [fuelEq] at hArgs
  have designSB : ∀ (s : CircuitState) dd,
      ({ s with design := dd } : CircuitState).sourceBindings = s.sourceBindings :=
    fun _ _ => rfl
  have designMod : ∀ (s : CircuitState) dd,
      ({ s with design := dd } : CircuitState).module = s.module :=
    fun _ _ => rfl
  -- one prepared input wire per argument
  obtain ⟨aWs, hlenW, hQ⟩ := list_choice argIds.length
    (fun i hi wv =>
      Tools.ShippingBindingsSoundness.visible
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.sourceBindings
        (argIds[i]'hi) = some wv ∧
      ({ name := wv, ty := .bitVector (ws i) } : Port) ∈
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.module.wires ∧
      env0 wv = (vals i).toNat)
    (fun i hi => prepared.1.bits (argIds[i]'hi) (ws i) (vals i) (hb i hi))
  have hpairsLen : (ports.zip (argIds.map Lean.Expr.fvar)).length = aWs.length := by
    simp [hlenP, hlenW]
  obtain ⟨hsQ', hconnsEq⟩ := instArgs_resolve
    (ports.zip (argIds.map Lean.Expr.fvar)) aWs [] 0 conns sQ hpairsLen
    (fun k hk hk' => by
      have hkA : k < argIds.length := by rw [← hlenW]; exact hk'
      refine ⟨argIds[k]'hkA, ?_, ?_⟩
      · simp
      · rw [hsB, designSB]
        exact (hQ k hkA hk').1)
    hArgs
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
            conns).reverse) ::
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
    rw [hsQ', hsB, designMod]
  have mBody : m.body = (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.module.body.reverse ++
      [.inst mc.name instName
        ((((⟨"out", .bitVector wOut⟩ : Port).name, Sparkle.IR.AST.Expr.ref w) ::
          conns).reverse),
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
    rw [hsQ', hsB]
  have wNotOut : w ≠ "out" := by
    intro eq
    have alloc := CircuitM.makeWire_allocated "out"
      (Sparkle.IR.Type.HWType.bitVector wOut) true sQ
    rw [← houtW, eq] at alloc
    exact not_allocated_out alloc
  refine ⟨?_, ?_, wNotOut, aWs, hlenW, ?_, ?_⟩
  · rw [mBody, hbodyR]
    simp
  · rw [hd, stDesign, hpdesR]
    rfl
  · rw [hconnsEq]
    simp
  · intro i hi
    have hiA : i < argIds.length := by rw [← hlenW]; exact hi
    obtain ⟨-, hdecl, hval⟩ := hQ i hiA hi
    exact ⟨hval, inputNotOut _ hdecl⟩


/-! ## The clk/rst walk as a pure function (any port list) -/

/-- The clk/rst plumbing, as a pure state transformer: each clk/rst port
connects to the parent port of the same name, adding it when missing. -/
def instClkRstPure (acc : List (String × Sparkle.IR.AST.Expr)) :
    List Port → CircuitState → List (String × Sparkle.IR.AST.Expr) × CircuitState
  | [], s => (acc, s)
  | p :: ps, s =>
    if p.name == "clk" || p.name == "rst" then
      instClkRstPure ((p.name, Sparkle.IR.AST.Expr.ref p.name) :: acc) ps
        (if !s.module.inputs.any (fun q => q.name == p.name) then
          (CircuitM.addInput p.name p.ty s).2 else s)
    else instClkRstPure acc ps s

/-- The monadic walk IS the pure one. -/
theorem instClkRst_pure {ctx : CompilerState} :
    ∀ (ps : List Port) (acc : List (String × Sparkle.IR.AST.Expr))
      (s s' : CircuitState) (r : List (String × Sparkle.IR.AST.Expr)),
    Returns (instClkRst acc ps) ctx s r s' → (r, s') = instClkRstPure acc ps s
  | [], acc, s, s', r, h => by
    unfold instClkRst at h
    obtain ⟨hr, hs⟩ := Returns.pure h
    rw [hr, hs]
    rfl
  | p :: ps, acc, s, s', r, h => by
    unfold instClkRst at h
    by_cases hc : (p.name == "clk" || p.name == "rst") = true
    · rw [if_pos hc] at h
      replace h := Returns.get_bind h
      try dsimp only at h
      by_cases hany : (!s.module.inputs.any (fun q => q.name == p.name)) = true
      · rw [if_pos hany] at h
        obtain ⟨u1, s1, hAdd, h⟩ := Returns.bind (m := CompilerM.addInput p.name p.ty) h
        have hs1 : s1 = (CircuitM.addInput p.name p.ty s).2 :=
          Tools.ShippingEntrySoundness.addInput_returns hAdd
        subst hs1
        have := instClkRst_pure ps _ _ _ _ h
        rw [this]
        show _ = (if (p.name == "clk" || p.name == "rst") = true then _ else _)
        rw [if_pos hc, if_pos hany]
      · rw [if_neg hany] at h
        have := instClkRst_pure ps _ _ _ _ h
        rw [this]
        show _ = (if (p.name == "clk" || p.name == "rst") = true then _ else _)
        rw [if_pos hc, if_neg hany]
    · rw [if_neg hc] at h
      have := instClkRst_pure ps _ _ _ _ h
      rw [this]
      show _ = (if (p.name == "clk" || p.name == "rst") = true then _ else _)
      rw [if_neg hc]

/-- The connection list the walk produces, independent of the state. -/
def clkRstConns (ps : List Port) : List (String × Sparkle.IR.AST.Expr) :=
  ((ps.filter (fun p => p.name == "clk" || p.name == "rst")).map
    (fun p => (p.name, Sparkle.IR.AST.Expr.ref p.name))).reverse

theorem instClkRstPure_fst : ∀ (ps : List Port)
    (acc : List (String × Sparkle.IR.AST.Expr)) (s : CircuitState),
    (instClkRstPure acc ps s).1 = clkRstConns ps ++ acc
  | [], acc, s => rfl
  | p :: ps, acc, s => by
    unfold instClkRstPure
    by_cases hc : (p.name == "clk" || p.name == "rst") = true
    · rw [if_pos hc, instClkRstPure_fst]
      unfold clkRstConns
      simp [List.filter_cons, hc]
    · rw [if_neg hc, instClkRstPure_fst]
      unfold clkRstConns
      simp [List.filter_cons, hc]

theorem instClkRstPure_sourceBindings : ∀ (ps : List Port)
    (acc : List (String × Sparkle.IR.AST.Expr)) (s : CircuitState),
    (instClkRstPure acc ps s).2.sourceBindings = s.sourceBindings
  | [], _, _ => rfl
  | p :: ps, acc, s => by
    unfold instClkRstPure
    split
    · rw [instClkRstPure_sourceBindings]
      split <;> rfl
    · exact instClkRstPure_sourceBindings ps acc s

theorem instClkRstPure_body : ∀ (ps : List Port)
    (acc : List (String × Sparkle.IR.AST.Expr)) (s : CircuitState),
    (instClkRstPure acc ps s).2.module.body = s.module.body
  | [], _, _ => rfl
  | p :: ps, acc, s => by
    unfold instClkRstPure
    split
    · rw [instClkRstPure_body]
      split <;> rfl
    · exact instClkRstPure_body ps acc s

theorem instClkRstPure_design : ∀ (ps : List Port)
    (acc : List (String × Sparkle.IR.AST.Expr)) (s : CircuitState),
    (instClkRstPure acc ps s).2.design = s.design
  | [], _, _ => rfl
  | p :: ps, acc, s => by
    unfold instClkRstPure
    split
    · rw [instClkRstPure_design]
      split <;> rfl
    · exact instClkRstPure_design ps acc s

theorem instClkRstPure_inputs_mono : ∀ (ps : List Port)
    (acc : List (String × Sparkle.IR.AST.Expr)) (s : CircuitState) (q : Port),
    q ∈ s.module.inputs → q ∈ (instClkRstPure acc ps s).2.module.inputs
  | [], _, _, _, h => h
  | p :: ps, acc, s, q, h => by
    unfold instClkRstPure
    split
    · apply instClkRstPure_inputs_mono
      split
      · rw [addInput_inputs]
        exact List.mem_cons_of_mem _ h
      · exact h
    · exact instClkRstPure_inputs_mono ps acc s q h

/-- Every clk/rst port of the child has a same-named parent input after the
walk. -/
theorem instClkRstPure_inputs_names : ∀ (ps : List Port)
    (acc : List (String × Sparkle.IR.AST.Expr)) (s : CircuitState) (p : Port),
    p ∈ ps → (p.name == "clk" || p.name == "rst") = true →
    ∃ q ∈ (instClkRstPure acc ps s).2.module.inputs, q.name = p.name
  | [], _, _, _, h, _ => by cases h
  | p0 :: ps, acc, s, p, h, hcr => by
    unfold instClkRstPure
    rcases List.mem_cons.mp h with rfl | hin
    · rw [if_pos hcr]
      by_cases hany : (!s.module.inputs.any (fun q => q.name == p.name)) = true
      · rw [if_pos hany]
        exact ⟨⟨p.name, p.ty⟩, instClkRstPure_inputs_mono ps _ _ _
          (by rw [addInput_inputs]; exact List.mem_cons_self), rfl⟩
      · rw [if_neg hany]
        have hex : s.module.inputs.any (fun q => q.name == p.name) = true := by
          cases hb : s.module.inputs.any (fun q => q.name == p.name) with
          | true => rfl
          | false => rw [hb] at hany; exact absurd rfl hany
        obtain ⟨q, hq, hqn⟩ := List.any_eq_true.mp hex
        exact ⟨q, instClkRstPure_inputs_mono ps _ _ _ hq, eq_of_beq hqn⟩
    · split
      · exact instClkRstPure_inputs_names ps _ _ p hin hcr
      · exact instClkRstPure_inputs_names ps _ _ p hin hcr

/-! ## The general single-output contract: any arity, with or without clk/rst -/

/-- The mixed certified entry's guarantee when the quoted body is a
canonical instance call on ANY single-output child: the compiled parent is
one instance statement — the child's clk/rst ports connected to same-named
parent ports (present after the walk), its data ports connected in order to
the prepared wires of the arguments — plus the output alias; the design
holds exactly the pinned child. -/
def InstanceGPreserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) (d : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (mn : Name) (lvls : List Level) (dId : FVarId) (argIds : List FVarId)
      (mc : Sparkle.IR.AST.Module) (dc : Design) (wOut : Nat) (ports : List Port),
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      instEN mn lvls (.fvar dId) (argIds.map Lean.Expr.fvar) →
    (mn == ``Sparkle.Core.Signal.Signal.pure) = false →
    signalBinOpOf mn = none →
    fallbackKind (instEN mn lvls (.fvar dId) (argIds.map Lean.Expr.fvar)) = .other →
    HardwareTagged mn → SubSynthDefines mn mc dc →
    dc.modules = [] →
    mc.inputs = ports →
    mc.outputs = [⟨"out", .bitVector wOut⟩] →
    (ports.filter (fun p => p.name != "clk" && p.name != "rst")).length = argIds.length →
    ∃ (instName outW : String) (conns : List (String × Sparkle.IR.AST.Expr)),
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) (ws : Nat → Nat) (vals : (i : Nat) → BitVec (ws i)),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits env0 (bs.zip ids) a →
    (∀ i (h : i < argIds.length), p.bits (argIds[i]'h) = some ⟨ws i, vals i⟩) →
    m.body = [.inst mc.name instName (conns.reverse ++ [("out", .ref outW)]),
      .assign "out" (.ref outW)] ∧
    d.modules = [mc] ∧
    outW ≠ "out" ∧
    Linked m mc (conns.reverse ++ [("out", .ref outW)]) ∧
    (∀ pt ∈ ports, (pt.name == "clk" || pt.name == "rst") = true →
      ∃ q ∈ m.inputs, q.name = pt.name) ∧
    ∃ aWs : List String, aWs.length = argIds.length ∧
      conns.reverse = (clkRstConns ports).reverse ++
        (((ports.filter (fun p => p.name != "clk" && p.name != "rst")).zip
          (argIds.map Lean.Expr.fvar)).zip aWs).map
          (fun pw => (pw.1.1.name, Sparkle.IR.AST.Expr.ref pw.2)) ∧
      ∀ i (h : i < aWs.length),
        env0 (aWs[i]'h) = (vals i).toNat ∧ aWs[i]'h ≠ "out"

set_option maxHeartbeats 2000000 in
theorem synthesizeMixedCertified_instanceG_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d)) :
    InstanceGPreserves declName bs body m d := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, hd, -⟩ :=
    synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro mn lvls dId argIds mc dc wOut ports qeq hpure hbin hkind htag hsub hdc hins houts hlenP
  have leaf := prepare_returns (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString)
    (bools := fun _ => false) (bits := fun _ _ => 0) run
  rw [qeq] at leaf
  obtain ⟨w, sm0, ty, tr, freshOut, ht, hty⟩ := emitLeaves_single leaf
  have stepEq : translateExprToWire
      (instEN mn lvls (.fvar dId) (argIds.map Lean.Expr.fvar)) "out" false true =
      translateInstanceOrFallback (translateFuelFix translateStep 1048575)
        (instEN mn lvls (.fvar dId) (argIds.map Lean.Expr.fvar)) "out" false true := by
    show translateStepWith translateFallback (translateFuelFix translateStep 1048575)
      (instEN mn lvls (.fvar dId) (argIds.map Lean.Expr.fvar)) "out" false true = _
    exact instanceN_step _ mn lvls _ _ _ _ _ hpure hbin hkind
  rw [stepEq] at tr
  unfold translateInstanceOrFallback at tr
  rw [instEN_getAppFn] at tr
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
  -- the clk/rst walk, as the pure transformer
  obtain ⟨conns0, sC, hClk, k4⟩ := Returns.bind (m := instClkRst [] mc.inputs) k3
  rw [hins] at hClk
  have hwalk := instClkRst_pure ports [] sB sC conns0 hClk
  have hconns0 : conns0 = (instClkRstPure [] ports sB).1 := congrArg Prod.fst hwalk
  have hsC : sC = (instClkRstPure [] ports sB).2 := congrArg Prod.snd hwalk
  rw [hins, instEN_spineArgs] at k4
  obtain ⟨uG, sH, hGuard, k5⟩ := Returns.bind (m := instArityCheck mn _ _) k4
  unfold instArityCheck at hGuard
  rw [if_neg (by simp [hlenP])] at hGuard
  obtain ⟨-, hsH⟩ := Returns.pure hGuard
  have hdrop : (Lean.Expr.fvar dId :: argIds.map Lean.Expr.fvar).drop
      ((Lean.Expr.fvar dId :: argIds.map Lean.Expr.fvar).length -
        (ports.filter (fun p => p.name != "clk" && p.name != "rst")).length) =
      argIds.map Lean.Expr.fvar := by
    simp [hlenP]
  rw [hdrop] at k5
  obtain ⟨conns, sF, hArgs, k6⟩ := Returns.bind (m := instArgs _ _ _ 0) k5
  obtain ⟨csP, sP2, hgetP, k7⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) k6
  obtain ⟨hcsP, hsP2⟩ := Returns.get hgetP
  obtain ⟨cVal, sQ, hCacheRead, k8⟩ :=
    Returns.bind (m := CompilerM.liftMetaM instArmCacheGet) k7
  obtain ⟨hCacheM, hsQ⟩ := Returns.liftMetaM_mreturns hCacheRead
  rw [record0, instHit_empty] at k8
  simp only [] at k8
  obtain ⟨outW, sW, hMk, k9⟩ := Returns.bind (m := CompilerM.makeWire "out" _ true) k8
  obtain ⟨houtW, hsW⟩ := makeWireC_returns hMk
  obtain ⟨uP, sV, hPut, k10⟩ :=
    Returns.bind (m := CompilerM.liftMetaM (instArmCachePut _ _)) k9
  have hsV := Returns.liftMetaM hPut
  obtain ⟨instName, sN, hFresh, k11⟩ := Returns.bind (m := CompilerM.freshName _) k10
  obtain ⟨hinstName, hsN⟩ := freshNameC_returns hFresh
  obtain ⟨uL, sL, hLink, k11⟩ := Returns.bind (m := instLinkCheck _ _ _) k11
  obtain ⟨hsL, hlinked⟩ := instLinkCheck_returns hLink
  rw [hsL] at k11
  obtain ⟨uE, sI, hEmit, k12⟩ :=
    Returns.bind (m := CompilerM.emitInstance mc.name _ _) k11
  have hsI := emitInstanceC_returns hEmit
  obtain ⟨hwEq, hsmR⟩ := Returns.pure k12
  have hrec := recordTranslation_returns record
  refine ⟨instName, outW, conns, ?_⟩
  intro bools bits env0 ws vals a p adm hb
  have empty := empty_layout (entryCompilerState false cache) declName.toString env0
  have prepared := prepare_layout (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString) empty.1 empty.2 adm
  obtain ⟨pc, ps⟩ := prepare_const (fun _ => false) bools (fun _ _ => 0) bits
    (bs.zip ids) _ _ rfl rfl
  rw [ps] at hsB
  rw [pc] at hArgs
  have fuelEq : translateFuelFix translateStep 1048575 =
      translateStepWith translateFallback (translateFuelFix translateStep 1048574) := rfl
  rw [fuelEq, hsH, hsC, hconns0] at hArgs
  have designSB : ∀ (s : CircuitState) dd,
      ({ s with design := dd } : CircuitState).sourceBindings = s.sourceBindings :=
    fun _ _ => rfl
  have designMod : ∀ (s : CircuitState) dd,
      ({ s with design := dd } : CircuitState).module = s.module :=
    fun _ _ => rfl
  obtain ⟨aWs, hlenW, hQ⟩ := list_choice argIds.length
    (fun i hi wv =>
      Tools.ShippingBindingsSoundness.visible
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.sourceBindings
        (argIds[i]'hi) = some wv ∧
      ({ name := wv, ty := .bitVector (ws i) } : Port) ∈
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.module.wires ∧
      env0 wv = (vals i).toNat)
    (fun i hi => prepared.1.bits (argIds[i]'hi) (ws i) (vals i) (hb i hi))
  have hpairsLen : ((ports.filter (fun p => p.name != "clk" && p.name != "rst")).zip
      (argIds.map Lean.Expr.fvar)).length = aWs.length := by
    simp [hlenP, hlenW]
  obtain ⟨hsF', hconnsEq⟩ := instArgs_resolve
    ((ports.filter (fun p => p.name != "clk" && p.name != "rst")).zip
      (argIds.map Lean.Expr.fvar)) aWs _ 0 conns sF hpairsLen
    (fun k hk hk' => by
      have hkA : k < argIds.length := by rw [← hlenW]; exact hk'
      refine ⟨argIds[k]'hkA, ?_, ?_⟩
      · simp
      · rw [instClkRstPure_sourceBindings, hsB, designSB]
        exact (hQ k hkA hk').1)
    hArgs
  -- every later state, back to the walk's exit state
  have hsQ' : sQ = (instClkRstPure [] ports sB).2 := by
    rw [hsQ, hsP2, hsF']
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
      .assign "out" (.ref outW) ::
        .inst mc.name instName
          ((((⟨"out", .bitVector wOut⟩ : Port).name, Sparkle.IR.AST.Expr.ref outW) ::
            conns).reverse) ::
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).state.module.body := by
    rw [ht, emitAssign_body_cons, addOutput_state, hwEq]
    show _ :: (sm0.module.addOutput _).body = _
    rw [addOutBody, hrec]
    show _ :: smR.module.body = _
    rw [hsmR, hsI]
    show _ :: (_ :: sN.module.body) = _
    rw [hsN, (CircuitM.freshName_spec _ _ _).2.2, hsV, hsW]
    rw [(CircuitM.makeWire_spec "out" _ true _).2.2.1]
    rw [hsQ', instClkRstPure_body, hsB, designMod]
  have mBody : m.body = (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.module.body.reverse ++
      [.inst mc.name instName
        ((((⟨"out", .bitVector wOut⟩ : Port).name, Sparkle.IR.AST.Expr.ref outW) ::
          conns).reverse),
       .assign "out" (.ref outW)] := by
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
        = s.design from fun s => freshName_design _ _ s, hsV, hsW]
    rw [makeWire_design]
    rw [hsQ', instClkRstPure_design, hsB]
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
  have stInputs : st.module.inputs = (instClkRstPure [] ports sB).2.module.inputs := by
    rw [ht]
    show (CircuitM.emitAssign "out" _ (CircuitM.addOutput "out" ty sm0).2).2.module.inputs = _
    rw [emitAssignInputs, addOutputInputs, hrec]
    show smR.module.inputs = _
    rw [hsmR, hsI]
    show sN.module.inputs = _
    rw [hsN, (CircuitM.freshName_spec _ _ _).2.2, hsV, hsW, makeWireInputs, hsQ']
  have hinNames : ∀ pt ∈ ports, (pt.name == "clk" || pt.name == "rst") = true →
      ∃ q ∈ m.inputs, q.name = pt.name := by
    intro pt hpt hcr
    obtain ⟨q, hq, hqn⟩ := instClkRstPure_inputs_names ports [] sB pt hpt hcr
    refine ⟨q, ?_, hqn⟩
    rw [hm]
    show _ ∈ (addClockResetIfSequential st.module).inputs.reverse
    rw [List.mem_reverse]
    exact (addClockReset_facts st.module).2.2.2 _ (by rw [stInputs]; exact hq)
  have wNotOut : outW ≠ "out" := by
    intro eq
    have alloc := CircuitM.makeWire_allocated "out"
      (Sparkle.IR.Type.HWType.bitVector wOut) true sQ
    rw [← houtW, eq] at alloc
    exact not_allocated_out alloc
  have stWires : st.module.wires = sN.module.wires := by
    rw [ht, Tools.ShippingTranslateSoundness.emitAssign_wires]
    show sm0.module.wires = _
    rw [hrec]
    show smR.module.wires = _
    rw [hsmR, hsI]
    rfl
  have stInputsN : st.module.inputs = sN.module.inputs := by
    rw [ht]
    show (CircuitM.emitAssign "out" _ (CircuitM.addOutput "out" ty sm0).2).2.module.inputs = _
    rw [emitAssignInputs, addOutputInputs, hrec]
    show smR.module.inputs = _
    rw [hsmR, hsI]
    rfl
  have linkedFinish : ∀ {cs : List (String × Sparkle.IR.AST.Expr)},
      Linked sN.module mc cs → Linked m mc cs := by
    intro cs h0
    refine h0.mono ?_ ?_
    · intro q hq
      rw [hm]
      show q ∈ ((addClockResetIfSequential st.module).finalize).wires
      simp only [Sparkle.IR.AST.Module.finalize, (addClockReset_facts st.module).2.1]
      rw [List.mem_reverse, stWires]
      exact hq
    · intro q hq
      rw [hm]
      show q ∈ (addClockResetIfSequential st.module).inputs.reverse
      rw [List.mem_reverse]
      exact (addClockReset_facts st.module).2.2.2 q (by rw [stInputsN]; exact hq)
  have hLinkedM : Linked m mc (conns.reverse ++ [("out", .ref outW)]) := by
    have h0 := instLinked_sound hlinked
    rw [List.reverse_cons] at h0
    exact linkedFinish h0
  refine ⟨?_, ?_, wNotOut, hLinkedM, hinNames, aWs, hlenW, ?_, ?_⟩
  · rw [mBody, hbodyR]
    simp
  · rw [hd, stDesign, hpdesR]
    rfl
  · rw [hconnsEq, instClkRstPure_fst]
    simp
  · intro i hi
    have hiA : i < argIds.length := by rw [← hlenW]; exact hi
    obtain ⟨-, hdecl, hval⟩ := hQ i hiA hi
    exact ⟨hval, inputNotOut _ hdecl⟩


/-! ## Projections of multi-output instance calls -/

/-- The quoted projection root: `@pn dom (call)`. -/
def projE (pn : Name) (lvlsP : List Level) (dom call : Lean.Expr) : Lean.Expr :=
  .app (.app (.const pn lvlsP) dom) call

theorem instFVars_projE (xs : Array Lean.Expr) (d : Nat) (pn : Name)
    (lvlsP : List Level) (dom call : Lean.Expr) :
    instFVars xs d (projE pn lvlsP dom call) =
      projE pn lvlsP (instFVars xs d dom) (instFVars xs d call) := rfl

theorem projE_spineArgs (pn : Name) (lvlsP : List Level) (dom call : Lean.Expr) :
    instSpineArgs (projE pn lvlsP dom call) = [dom, call] := rfl

/-- Gate acceptance for the projection root, AT the run's predicate. -/
theorem instanceProj_term_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {pn : Name} {lvlsP : List Level} {cn : Name} {lvlsC : List Level}
    {dposP dposC : Nat} {poss : List Nat} {isInst : Lean.Expr → Bool}
    (peel : mixedGatePeel d.value = some (bs,
      projE pn lvlsP (inputExpr bs.length dposP)
        (instEN cn lvlsC (inputExpr bs.length dposC) (poss.map (inputExpr bs.length)))))
    (htag : isInst (projE pn lvlsP (inputExpr bs.length dposP)
      (instEN cn lvlsC (inputExpr bs.length dposC) (poss.map (inputExpr bs.length)))) = true)
    (hscalar : mixedGateResultScalar d.type = true)
    (hdP : ∃ nd kd, bs[dposP]? = some (nd, kd))
    (hdC : ∃ nd kd, bs[dposC]? = some (nd, kd))
    (hpos : ∀ q ∈ poss, ∃ nq kq, bs[q]? = some (nq, kq)) :
    mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs,
      projE pn lvlsP (inputExpr bs.length dposP)
        (instEN cn lvlsC (inputExpr bs.length dposC) (poss.map (inputExpr bs.length)))) := by
  have spineC : unifiedInstanceSpine (bs.map (·.2)).toArray
      (instEN cn lvlsC (inputExpr bs.length dposC) (poss.map (inputExpr bs.length))) = true := by
    unfold instEN
    apply unifiedInstanceSpine_foldl
    · obtain ⟨nd, kd, hdp⟩ := hdC
      show ((mixedGateBVar? (bs.map Prod.snd).toArray (bs.length - 1 - dposC)).isSome &&
        true) = true
      rw [mixedGateBVar?_pos hdp]
      rfl
    · intro a ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      obtain ⟨nq, kq, hqp⟩ := hpos q hq
      refine ⟨bs.length - 1 - q, rfl, ?_⟩
      rw [mixedGateBVar?_pos hqp]
      rfl
  have happC : (instEN cn lvlsC (inputExpr bs.length dposC)
      (poss.map (inputExpr bs.length))).isApp = true := by
    unfold instEN
    exact foldl_app_isApp _ _ rfl
  have projSp : unifiedProjSpine (bs.map (·.2)).toArray
      (projE pn lvlsP (inputExpr bs.length dposP)
        (instEN cn lvlsC (inputExpr bs.length dposC) (poss.map (inputExpr bs.length)))) = true := by
    obtain ⟨nd, kd, hdp⟩ := hdP
    show ((mixedGateBVar? (bs.map Prod.snd).toArray (bs.length - 1 - dposP)).isSome &&
      (instEN cn lvlsC (inputExpr bs.length dposC) (poss.map (inputExpr bs.length))).isApp &&
      unifiedInstanceSpine (bs.map Prod.snd).toArray
        (instEN cn lvlsC (inputExpr bs.length dposC) (poss.map (inputExpr bs.length)))) = true
    rw [mixedGateBVar?_pos hdp, happC, spineC]
    rfl
  have root : unifiedInstanceRoot isInst (bs.map (·.2)).toArray
      (projE pn lvlsP (inputExpr bs.length dposP)
        (instEN cn lvlsC (inputExpr bs.length dposC) (poss.map (inputExpr bs.length)))) = true := by
    have happP : (projE pn lvlsP (inputExpr bs.length dposP)
        (instEN cn lvlsC (inputExpr bs.length dposC)
          (poss.map (inputExpr bs.length)))).isApp = true := rfl
    unfold unifiedInstanceRoot
    rw [htag, happP, projSp]
    simp
  simp only [mixedCertifiedShape?, List.isEmpty_nil, Bool.not_true,
    peel, root, hscalar, Bool.true_and, Bool.true_or, if_true]
  rfl

set_option maxHeartbeats 1000000 in
/-- One certified step on the projection root lands in the instance arm. -/
theorem instanceProj_step (rec : TranslateFn) (pn : Name) (lvlsP : List Level)
    (dF callF : Lean.Expr) (hint : String) (top named : Bool)
    (hpure : (pn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf pn = none)
    (hkind : fallbackKind (projE pn lvlsP dF callF) = .other) :
    translateStepWith translateFallback rec (projE pn lvlsP dF callF) hint top named =
      translateInstanceOrFallback rec (projE pn lvlsP dF callF) hint top named := by
  have shape : translateCoreShape (projE pn lvlsP dF callF) = false := by
    show ((pn == ``Sparkle.Core.Signal.Signal.pure) ||
      (match signalBinOpOf pn,
          canonicalSignalBinKinds pn (projE pn lvlsP dF callF).getAppArgs,
          canonicalSignalBitVecWidth (projE pn lvlsP dF callF).getAppArgs with
       | some _, some (true, true), some _ => true
       | _, _, _ => false)) = false
    rw [hpure, hbin]
    rfl
  have core : translateCore rec (projE pn lvlsP dF callF) hint top named = pure none := by
    show (if (pn == ``Sparkle.Core.Signal.Signal.pure) = true then
        translateSignalPureLiteral? (projE pn lvlsP dF callF).getAppArgs hint named
      else
        match signalBinOpOf pn,
            canonicalSignalBinKinds pn (projE pn lvlsP dF callF).getAppArgs,
            canonicalSignalBitVecWidth (projE pn lvlsP dF callF).getAppArgs with
        | some op, some (true, true), some _ => do
          let w ← translateCanonicalSignalBinary rec (projE pn lvlsP dF callF) op
            (projE pn lvlsP dF callF).getAppArgs true true hint named
          pure (some w)
        | _, _, _ => pure none) = pure none
    rw [hpure, hbin]
    rfl
  have step : translateStepWith translateFallback rec
      (projE pn lvlsP dF callF) hint top named =
      translateFallback rec (projE pn lvlsP dF callF) hint top named := by
    simp [translateStepWith, shape, core]
    rfl
  rw [step]
  simp only [translateFallback, hkind]

/-! ## Emitter specs for the multi-output lowering -/

/-- The call key computation leaves the builder state untouched (the saved
state is restored). -/
theorem instCallKey_returns {r : Lean.Expr} {ctx : CompilerState}
    {s s' : CircuitState} {k : UInt64}
    (h : Returns (instCallKey r) ctx s k s') : s' = s := by
  unfold instCallKey at h
  replace h := Returns.get_bind h
  obtain ⟨key, s1, -, h⟩ := Returns.bind (m := canonHardwareKey r) h
  obtain ⟨u, s2, hset, h⟩ := Returns.bind (m := (MonadStateOf.set s : CompilerM PUnit)) h
  have hs2 : s2 = s := Returns.set hset
  obtain ⟨-, hs'⟩ := Returns.pure h
  rw [hs', hs2]

/-- The output-wire walk as a pure state transformer. -/
def outWiresPure (hint : String) :
    List Port → List (String × Sparkle.IR.AST.Expr) → List (String × String) →
    CircuitState →
    (List (String × Sparkle.IR.AST.Expr) × List (String × String)) × CircuitState
  | [], conns, ws, s => ((conns, ws), s)
  | o :: rest, conns, ws, s =>
    outWiresPure hint rest
      ((o.name, Sparkle.IR.AST.Expr.ref
        (CircuitM.makeWire s!"{hint}_{o.name}" o.ty false s).1) :: conns)
      ((o.name, (CircuitM.makeWire s!"{hint}_{o.name}" o.ty false s).1) :: ws)
      (CircuitM.makeWire s!"{hint}_{o.name}" o.ty false s).2

theorem instOutWires_pure {callKey : UInt64} {hint : String} {ctx : CompilerState} :
    ∀ (outs : List Port) (conns : List (String × Sparkle.IR.AST.Expr))
      (ws : List (String × String)) (s s' : CircuitState)
      (r : List (String × Sparkle.IR.AST.Expr) × List (String × String)),
    Returns (instOutWires callKey hint outs conns ws) ctx s r s' →
    (r, s') = outWiresPure hint outs conns ws s
  | [], conns, ws, s, s', r, h => by
    unfold instOutWires at h
    obtain ⟨hr, hs⟩ := Returns.pure h
    rw [hr, hs]
    rfl
  | o :: rest, conns, ws, s, s', r, h => by
    unfold instOutWires at h
    obtain ⟨w, s1, hMk, h⟩ := Returns.bind (m := CompilerM.makeWire _ o.ty false) h
    obtain ⟨hw, hs1⟩ := makeWireC_returns hMk
    obtain ⟨u, s2, hPut, h⟩ :=
      Returns.bind (m := CompilerM.liftMetaM (instArmOutPut callKey o.name w)) h
    have hs2 := Returns.liftMetaM hPut
    have := instOutWires_pure rest _ _ _ _ _ h
    rw [this, hs2, hs1, hw]
    rfl

/-- The output wires, in port order. -/
def outWireNames (hint : String) : List Port → CircuitState → List String
  | [], _ => []
  | o :: rest, s =>
    (CircuitM.makeWire s!"{hint}_{o.name}" o.ty false s).1 ::
      outWireNames hint rest (CircuitM.makeWire s!"{hint}_{o.name}" o.ty false s).2

theorem outWireNames_length (hint : String) : ∀ (outs : List Port) (s : CircuitState),
    (outWireNames hint outs s).length = outs.length
  | [], _ => rfl
  | o :: rest, s => by
    show (outWireNames hint rest _).length + 1 = rest.length + 1
    rw [outWireNames_length]

theorem outWireNames_allocated (hint : String) : ∀ (outs : List Port) (s : CircuitState),
    ∀ w ∈ outWireNames hint outs s, Sparkle.IR.NameHints.Allocated w
  | [], _, w, h => by cases h
  | o :: rest, s, w, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact CircuitM.makeWire_allocated _ _ _ _
    · exact outWireNames_allocated hint rest _ w h

/-- Every output wire is unused in the state the walk starts from. -/
theorem outWireNames_fresh (hint : String) : ∀ (outs : List Port) (s : CircuitState),
    ∀ w ∈ outWireNames hint outs s, s.usedNames.contains w = false
  | [], _, w, h => by cases h
  | o :: rest, s, w, h => by
    have spec := CircuitM.makeWire_spec s!"{hint}_{o.name}" o.ty false s
    rcases List.mem_cons.mp h with hw | h
    · rw [hw]
      exact spec.1
    · have ih := outWireNames_fresh hint rest _ w h
      rw [spec.2.1, Std.HashSet.contains_insert] at ih
      exact (Bool.or_eq_false_iff.mp ih).2

/-- The output wires are pairwise distinct. -/
theorem outWireNames_nodup (hint : String) : ∀ (outs : List Port) (s : CircuitState),
    (outWireNames hint outs s).Nodup
  | [], _ => List.nodup_nil
  | o :: rest, s => by
    have spec := CircuitM.makeWire_spec s!"{hint}_{o.name}" o.ty false s
    show ((CircuitM.makeWire s!"{hint}_{o.name}" o.ty false s).1 ::
      outWireNames hint rest (CircuitM.makeWire s!"{hint}_{o.name}" o.ty false s).2).Nodup
    refine List.nodup_cons.mpr ⟨?_, outWireNames_nodup hint rest _⟩
    intro hmem
    have hfresh := outWireNames_fresh hint rest _ _ hmem
    rw [spec.2.1, Std.HashSet.contains_insert] at hfresh
    simp at hfresh

theorem outWiresPure_fst (hint : String) : ∀ (outs : List Port)
    (conns : List (String × Sparkle.IR.AST.Expr)) (ws : List (String × String))
    (s : CircuitState),
    (outWiresPure hint outs conns ws s).1 =
      (((outs.zip (outWireNames hint outs s)).map
          (fun ow => (ow.1.name, Sparkle.IR.AST.Expr.ref ow.2))).reverse ++ conns,
       ((outs.zip (outWireNames hint outs s)).map
          (fun ow => (ow.1.name, ow.2))).reverse ++ ws)
  | [], conns, ws, s => rfl
  | o :: rest, conns, ws, s => by
    unfold outWiresPure
    rw [outWiresPure_fst]
    simp [outWireNames]

theorem outWiresPure_body (hint : String) : ∀ (outs : List Port)
    (conns : List (String × Sparkle.IR.AST.Expr)) (ws : List (String × String))
    (s : CircuitState),
    (outWiresPure hint outs conns ws s).2.module.body = s.module.body
  | [], _, _, _ => rfl
  | o :: rest, conns, ws, s => by
    unfold outWiresPure
    rw [outWiresPure_body, (CircuitM.makeWire_spec _ _ false _).2.2.1]

theorem outWiresPure_design (hint : String) : ∀ (outs : List Port)
    (conns : List (String × Sparkle.IR.AST.Expr)) (ws : List (String × String))
    (s : CircuitState),
    (outWiresPure hint outs conns ws s).2.design = s.design
  | [], _, _, _ => rfl
  | o :: rest, conns, ws, s => by
    unfold outWiresPure
    rw [outWiresPure_design, makeWire_design]

/-- A successful association lookup is a membership. -/
theorem lookup_some_mem {k v : String} : ∀ (l : List (String × String)),
    l.lookup k = some v → (k, v) ∈ l
  | [], h => by cases h
  | (a, b) :: rest, h => by
    by_cases hk : (k == a) = true
    · have : (some b : Option String) = some v := by
        simpa [List.lookup, hk] using h
      cases this
      rw [eq_of_beq hk]
      exact List.mem_cons_self
    · have hk' : (k == a) = false := by simpa using hk
      have : rest.lookup k = some v := by
        simpa [List.lookup, hk'] using h
      exact List.mem_cons_of_mem _ (lookup_some_mem rest this)


theorem makeWire_inputs (h : String) (ty : Sparkle.IR.Type.HWType) (n : Bool)
    (s : CircuitState) :
    (CircuitM.makeWire h ty n s).2.module.inputs = s.module.inputs := by
  show ((CircuitM.freshName (CircuitM.sanitizeName h) n s).2.module.addWire _).inputs = _
  rw [(CircuitM.freshName_spec _ _ _).2.2]
  rfl

theorem outWiresPure_inputs (hint : String) : ∀ (outs : List Port)
    (conns : List (String × Sparkle.IR.AST.Expr)) (ws : List (String × String))
    (s : CircuitState),
    (outWiresPure hint outs conns ws s).2.module.inputs = s.module.inputs
  | [], _, _, _ => rfl
  | o :: rest, conns, ws, s => by
    unfold outWiresPure
    rw [outWiresPure_inputs, makeWire_inputs]

/-! ## Boundaries of the projection arm -/

/-- The environment facts the projection dispatch reads: the projection
function itself is not a hardware module, it is a projection of
`structName`, and the projected call's head carries the tag. -/
def ProjEnvDefines (pn structName cn : Name) : Prop :=
  ∀ env, MReturns instArmEnv env →
    Sparkle.Compiler.isHardwareModule env pn = false ∧
    env.getProjectionStructureName? pn = some structName ∧
    Sparkle.Compiler.isHardwareModule env cn = true

/-- The projection resolves to the field named `fieldName`. -/
def ProjFieldDefines (pn structName : Name) (fieldName : String) : Prop :=
  ∀ r, MReturns (projFieldName? pn structName) r → r = some fieldName

/-- Every read of the multi-output port map in this run comes back empty
(reset at depth 0 of every top-level synthesis). -/
def OutCacheEmpty : Prop :=
  ∀ c, MReturns instArmOutGet c → ∀ k, c.get? k = none ∧ c.contains k = false

theorem projE_getAppFn (pn : Name) (lvlsP : List Level) (dom call : Lean.Expr) :
    (projE pn lvlsP dom call).getAppFn = .const pn lvlsP := rfl

/-- The uncached projection lowering, unfolded to its explicit bind chain. -/
theorem projUncached_run (rec legacy : TranslateFn) (cn : Name)
    (mc : Sparkle.IR.AST.Module) (dc : Design) (fieldName : String)
    (recordArg e : Lean.Expr) (hint : String) (top named : Bool) :
    translateProjInstanceUncachedWith rec cn mc dc fieldName recordArg legacy
        e hint top named = (do
      let callKey ← instCallKey recordArg
      let portMap ← CompilerM.liftMetaM instArmOutGet
      match portMap.get? (callKey, fieldName) with
      | some w => pure w
      | none =>
        if (match mc.outputs.head? with
            | some firstOutP => portMap.contains (callKey, firstOutP.name)
            | none => false) = true then
          legacy e hint top named
        else do
          let cs0 ← get
          instAddModules (cs0.design.modules.map (fun x => x.name)) dc.modules
          instRegisterChild (cs0.design.modules.map (fun x => x.name)) mc
          let connections0 ← instClkRst [] mc.inputs
          instArityCheck cn
            (mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst")).length
            (instSpineArgs recordArg).length
          let connections ← instArgs rec connections0
            ((mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst")).zip
              ((instSpineArgs recordArg).drop ((instSpineArgs recordArg).length -
                (mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst")).length))) 0
          let (connectionsF, outWires) ←
            instOutWires callKey "sub_call" mc.outputs connections []
          let instName ← CompilerM.freshName s!"inst_{mc.name}"
          instLinkCheck cn mc connectionsF.reverse
          CompilerM.emitInstance mc.name instName connectionsF.reverse
          match outWires.lookup fieldName with
          | some w => pure w
          | none => throw (Exception.error .missing
              s!"Sub-module {cn} has no output port '{fieldName}'")) := rfl

/-- Every association the output walk adds maps to an allocated wire. -/
theorem outWiresPure_ws_allocated (hint : String) : ∀ (outs : List Port)
    (conns : List (String × Sparkle.IR.AST.Expr)) (ws : List (String × String))
    (s : CircuitState) (kv : String × String),
    kv ∈ (outWiresPure hint outs conns ws s).1.2 →
    kv ∈ ws ∨ Sparkle.IR.NameHints.Allocated kv.2
  | [], _, _, _, kv, h => Or.inl h
  | o :: rest, conns, ws, s, kv, h => by
    unfold outWiresPure at h
    rcases outWiresPure_ws_allocated hint rest _ _ _ kv h with hmem | hal
    · rcases List.mem_cons.mp hmem with hkv | hmem
      · refine Or.inr ?_
        rw [hkv]
        exact CircuitM.makeWire_allocated s!"{hint}_{o.name}" o.ty false s
      · exact Or.inl hmem
    · exact Or.inr hal

/-! ## The projection contract and monolith -/

/-- The mixed certified entry's guarantee when the quoted body is a field
projection of a canonical call on a MULTI-output child: the compiled parent
is one instance statement — clk/rst plumbed as in the single-output case,
data ports connected in order to the prepared argument wires, EVERY child
output port connected to its own fresh wire — plus the output alias reading
the projected field's wire; the design holds exactly the pinned child. -/
def ProjInstancePreserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) (d : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (pn structName : Name) (lvlsP : List Level) (dIdP : FVarId) (fieldName : String)
      (cn : Name) (lvlsC : List Level) (dIdC : FVarId) (argIds : List FVarId)
      (mc : Sparkle.IR.AST.Module) (dc : Design) (ports outs : List Port),
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      projE pn lvlsP (.fvar dIdP)
        (instEN cn lvlsC (.fvar dIdC) (argIds.map Lean.Expr.fvar)) →
    (pn == ``Sparkle.Core.Signal.Signal.pure) = false →
    signalBinOpOf pn = none →
    fallbackKind (projE pn lvlsP (.fvar dIdP)
      (instEN cn lvlsC (.fvar dIdC) (argIds.map Lean.Expr.fvar))) = .other →
    ProjEnvDefines pn structName cn → ProjFieldDefines pn structName fieldName →
    SubSynthDefines cn mc dc → OutCacheEmpty →
    dc.modules = [] →
    mc.inputs = ports →
    mc.outputs = outs →
    2 ≤ outs.length →
    outs.any (fun p => p.name == fieldName) = true →
    (ports.filter (fun p => p.name != "clk" && p.name != "rst")).length = argIds.length →
    ∃ (instName outW : String) (oWs : List String)
      (conns : List (String × Sparkle.IR.AST.Expr)),
    oWs.length = outs.length ∧ oWs.Nodup ∧
    ((outs.zip oWs).map (fun ow => (ow.1.name, ow.2))).reverse.lookup fieldName =
      some outW ∧
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) (ws : Nat → Nat) (vals : (i : Nat) → BitVec (ws i)),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits env0 (bs.zip ids) a →
    (∀ i (h : i < argIds.length), p.bits (argIds[i]'h) = some ⟨ws i, vals i⟩) →
    m.body = [.inst mc.name instName
        (conns.reverse ++
          (outs.zip oWs).map (fun ow => (ow.1.name, Sparkle.IR.AST.Expr.ref ow.2))),
      .assign "out" (.ref outW)] ∧
    d.modules = [mc] ∧
    outW ≠ "out" ∧
    Linked m mc (conns.reverse ++
      (outs.zip oWs).map (fun ow => (ow.1.name, Sparkle.IR.AST.Expr.ref ow.2))) ∧
    (∀ pt ∈ ports, (pt.name == "clk" || pt.name == "rst") = true →
      ∃ q ∈ m.inputs, q.name = pt.name) ∧
    ∃ aWs : List String, aWs.length = argIds.length ∧
      conns.reverse = (clkRstConns ports).reverse ++
        (((ports.filter (fun p => p.name != "clk" && p.name != "rst")).zip
          (argIds.map Lean.Expr.fvar)).zip aWs).map
          (fun pw => (pw.1.1.name, Sparkle.IR.AST.Expr.ref pw.2)) ∧
      ∀ i (h : i < aWs.length),
        env0 (aWs[i]'h) = (vals i).toNat ∧ aWs[i]'h ≠ "out"

set_option maxHeartbeats 2000000 in
theorem synthesizeMixedCertified_instanceProj_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d)) :
    ProjInstancePreserves declName bs body m d := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, hd, -⟩ :=
    synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro pn structName lvlsP dIdP fieldName cn lvlsC dIdC argIds mc dc ports outs
    qeq hpure hbin hkind
    hpenv hfield hsub houtcache hdc hins houts h2 hany hlenP
  have leaf := prepare_returns (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString)
    (bools := fun _ => false) (bits := fun _ _ => 0) run
  rw [qeq] at leaf
  obtain ⟨w, sm0, ty, tr, freshOut, ht, hty⟩ := emitLeaves_single leaf
  have stepEq : translateExprToWire
      (projE pn lvlsP (.fvar dIdP)
        (instEN cn lvlsC (.fvar dIdC) (argIds.map Lean.Expr.fvar))) "out" false true =
      translateInstanceOrFallback (translateFuelFix translateStep 1048575)
        (projE pn lvlsP (.fvar dIdP)
          (instEN cn lvlsC (.fvar dIdC) (argIds.map Lean.Expr.fvar))) "out" false true := by
    show translateStepWith translateFallback (translateFuelFix translateStep 1048575)
      (projE pn lvlsP (.fvar dIdP)
        (instEN cn lvlsC (.fvar dIdC) (argIds.map Lean.Expr.fvar))) "out" false true = _
    exact instanceProj_step _ pn lvlsP _ _ _ _ _ hpure hbin hkind
  rw [stepEq] at tr
  unfold translateInstanceOrFallback at tr
  rw [projE_getAppFn] at tr
  obtain ⟨env, sE, hEnvRead, tr⟩ := Returns.bind tr
  obtain ⟨hEnvM, hsE⟩ := Returns.liftMetaM_mreturns hEnvRead
  subst hsE
  obtain ⟨hnotTag, hprojS, hctag⟩ := hpenv env hEnvM
  rw [hnotTag] at tr
  simp only [Bool.false_eq_true, if_false] at tr
  rw [hprojS, projE_spineArgs] at tr
  rw [show ([Lean.Expr.fvar dIdP,
      instEN cn lvlsC (.fvar dIdC) (argIds.map Lean.Expr.fvar)] : List Lean.Expr).getLast? =
      some (instEN cn lvlsC (.fvar dIdC) (argIds.map Lean.Expr.fvar)) from rfl] at tr
  simp only [] at tr
  rw [instEN_getAppFn] at tr
  simp only [] at tr
  rw [hctag] at tr
  simp only [if_true] at tr
  obtain ⟨fo, sP, hFieldRead, tr⟩ :=
    Returns.bind (m := CompilerM.liftMetaM (projFieldName? pn structName)) tr
  obtain ⟨hFieldM, hsP⟩ := Returns.liftMetaM_mreturns hFieldRead
  subst hsP
  rw [hfield fo hFieldM] at tr
  simp only [] at tr
  obtain ⟨sub, sS, hSubRead, tr⟩ := Returns.bind tr
  obtain ⟨hSubM, hsS⟩ := Returns.liftMetaM_mreturns hSubRead
  subst hsS
  rw [hsub sub hSubM] at tr
  have hcond : (decide (2 ≤ (mc, dc).1.outputs.length) &&
      (mc, dc).1.outputs.any (fun p => p.name == fieldName)) = true := by
    show (decide (2 ≤ mc.outputs.length) &&
      mc.outputs.any (fun p => p.name == fieldName)) = true
    rw [houts, hany]
    simp [h2]
  rw [if_pos hcond] at tr
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
  rw [projUncached_run] at missRun
  obtain ⟨callKey, sK, hKey, k0⟩ := Returns.bind (m := instCallKey _) missRun
  have hsK := instCallKey_returns hKey
  obtain ⟨portMap, sM, hMapRead, k0⟩ :=
    Returns.bind (m := CompilerM.liftMetaM instArmOutGet) k0
  obtain ⟨hMapM, hsM⟩ := Returns.liftMetaM_mreturns hMapRead
  have hmiss := houtcache portMap hMapM
  rw [(hmiss (callKey, fieldName)).1] at k0
  simp only [] at k0
  have hnot : (match (mc, dc).1.outputs.head? with
      | some firstOutP => portMap.contains (callKey, firstOutP.name)
      | none => false) = false := by
    cases (mc, dc).1.outputs.head? with
    | none => rfl
    | some f => exact (hmiss _).2
  rw [if_neg (by rw [hnot]; exact Bool.false_ne_true)] at k0
  rw [hsM, hsK] at k0
  obtain ⟨cs0, sG, hget0, k1⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) k0
  obtain ⟨hcs0, hsG⟩ := Returns.get hget0
  subst hcs0 hsG
  have hpdes : (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.design =
      Design.empty declName.toString :=
    prepare_design (bs.zip ids) _
  rw [show (mc, dc).2.modules = dc.modules from rfl, hdc] at k1
  obtain ⟨u0, sA, hAdd0, k2⟩ := Returns.bind (m := instAddModules _ []) k1
  obtain ⟨-, hsA⟩ := Returns.pure (by exact hAdd0 : Returns (pure ()) _ _ u0 sA)
  subst hsA
  obtain ⟨uR, sB, hReg, k3⟩ := Returns.bind (m := instRegisterChild _ mc) k2
  have hsB := instRegisterChild_fresh (by rw [hpdes]; rfl) (by rw [hpdes]; rfl) hReg
  obtain ⟨conns0, sC, hClk, k4⟩ := Returns.bind (m := instClkRst [] mc.inputs) k3
  rw [hins] at hClk
  have hwalk := instClkRst_pure ports [] sB sC conns0 hClk
  have hconns0 : conns0 = (instClkRstPure [] ports sB).1 := congrArg Prod.fst hwalk
  have hsC : sC = (instClkRstPure [] ports sB).2 := congrArg Prod.snd hwalk
  rw [show (mc, dc).1.inputs = ports from hins, instEN_spineArgs] at k4
  obtain ⟨uG, sH, hGuard, k5⟩ := Returns.bind (m := instArityCheck cn _ _) k4
  unfold instArityCheck at hGuard
  rw [if_neg (by simp [hlenP])] at hGuard
  obtain ⟨-, hsH⟩ := Returns.pure hGuard
  have hdrop : (Lean.Expr.fvar dIdC :: argIds.map Lean.Expr.fvar).drop
      ((Lean.Expr.fvar dIdC :: argIds.map Lean.Expr.fvar).length -
        (ports.filter (fun p => p.name != "clk" && p.name != "rst")).length) =
      argIds.map Lean.Expr.fvar := by
    simp [hlenP]
  rw [hdrop] at k5
  obtain ⟨conns, sF, hArgs, k6⟩ := Returns.bind (m := instArgs _ _ _ 0) k5
  rw [show (mc, dc).1.outputs = outs from houts] at k6
  obtain ⟨⟨connsF, outWs⟩, sO, hOut, k7⟩ :=
    Returns.bind (m := instOutWires _ "sub_call" outs _ []) k6
  have hpureO := instOutWires_pure _ _ _ _ _ _ hOut
  try dsimp only at k7
  obtain ⟨instName, sN, hFresh, k8⟩ := Returns.bind (m := CompilerM.freshName _) k7
  obtain ⟨hinstName, hsN⟩ := freshNameC_returns hFresh
  obtain ⟨uL, sL, hLink, k8⟩ := Returns.bind (m := instLinkCheck _ _ _) k8
  obtain ⟨hsL, hlinked⟩ := instLinkCheck_returns hLink
  rw [hsL] at k8
  obtain ⟨uE, sI, hEmit, k9⟩ :=
    Returns.bind (m := CompilerM.emitInstance _ _ _) k8
  have hsI := emitInstanceC_returns hEmit
  have hlk : ∃ wv, outWs.lookup fieldName = some wv := by
    cases hlk : outWs.lookup fieldName with
    | none =>
      rw [hlk] at k9
      exact (Returns.throw k9).elim
    | some wv => exact ⟨wv, rfl⟩
  obtain ⟨outW, hlk⟩ := hlk
  rw [hlk] at k9
  obtain ⟨hwEq, hsmR⟩ := Returns.pure k9
  have hrec := recordTranslation_returns record
  -- the output walk, as the pure transformer
  have hfstO := outWiresPure_fst "sub_call" outs conns [] sF
  have hconnsF : connsF = ((outs.zip (outWireNames "sub_call" outs sF)).map
      (fun ow => (ow.1.name, Sparkle.IR.AST.Expr.ref ow.2))).reverse ++ conns := by
    have := congrArg (fun x => x.1.1) hpureO
    simp only [] at this
    rw [this, hfstO]
  have houtWs : outWs = ((outs.zip (outWireNames "sub_call" outs sF)).map
      (fun ow => (ow.1.name, ow.2))).reverse := by
    have := congrArg (fun x => x.1.2) hpureO
    simp only [] at this
    rw [this, hfstO]
    simp
  have hsO : sO = (outWiresPure "sub_call" outs conns [] sF).2 :=
    congrArg Prod.snd hpureO
  have wNotOut : outW ≠ "out" := by
    intro eq
    have hmem := lookup_some_mem outWs hlk
    have hin : (fieldName, outW) ∈ (outWiresPure "sub_call" outs conns [] sF).1.2 := by
      have := congrArg (fun x => x.1.2) hpureO
      simp only [] at this
      rw [← this]
      exact hmem
    rcases outWiresPure_ws_allocated "sub_call" outs conns [] sF _ hin with hnil | alloc
    · cases hnil
    · rw [eq] at alloc
      exact not_allocated_out alloc
  refine ⟨instName, outW, outWireNames "sub_call" outs sF, conns,
    outWireNames_length _ _ _, outWireNames_nodup _ _ _, by rw [← houtWs]; exact hlk, ?_⟩
  intro bools bits env0 ws vals a p adm hb
  have empty := empty_layout (entryCompilerState false cache) declName.toString env0
  have prepared := prepare_layout (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString) empty.1 empty.2 adm
  obtain ⟨pc, ps⟩ := prepare_const (fun _ => false) bools (fun _ _ => 0) bits
    (bs.zip ids) _ _ rfl rfl
  rw [ps] at hsB
  rw [pc] at hArgs
  have fuelEq : translateFuelFix translateStep 1048575 =
      translateStepWith translateFallback (translateFuelFix translateStep 1048574) := rfl
  rw [fuelEq, hsH, hsC, hconns0] at hArgs
  have designSB : ∀ (s : CircuitState) dd,
      ({ s with design := dd } : CircuitState).sourceBindings = s.sourceBindings :=
    fun _ _ => rfl
  have designMod : ∀ (s : CircuitState) dd,
      ({ s with design := dd } : CircuitState).module = s.module :=
    fun _ _ => rfl
  obtain ⟨aWs, hlenW, hQ⟩ := list_choice argIds.length
    (fun i hi wv =>
      Tools.ShippingBindingsSoundness.visible
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.sourceBindings
        (argIds[i]'hi) = some wv ∧
      ({ name := wv, ty := .bitVector (ws i) } : Port) ∈
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.module.wires ∧
      env0 wv = (vals i).toNat)
    (fun i hi => prepared.1.bits (argIds[i]'hi) (ws i) (vals i) (hb i hi))
  have hpairsLen : ((ports.filter (fun p => p.name != "clk" && p.name != "rst")).zip
      (argIds.map Lean.Expr.fvar)).length = aWs.length := by
    simp [hlenP, hlenW]
  obtain ⟨hsF', hconnsEq⟩ := instArgs_resolve
    ((ports.filter (fun p => p.name != "clk" && p.name != "rst")).zip
      (argIds.map Lean.Expr.fvar)) aWs _ 0 conns sF hpairsLen
    (fun k hk hk' => by
      have hkA : k < argIds.length := by rw [← hlenW]; exact hk'
      refine ⟨argIds[k]'hkA, ?_, ?_⟩
      · simp
      · rw [instClkRstPure_sourceBindings, hsB, designSB]
        exact (hQ k hkA hk').1)
    hArgs
  have hsO' : sO = (outWiresPure "sub_call" outs conns []
      (instClkRstPure [] ports sB).2).2 := by
    rw [hsO, hsF']
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
      .assign "out" (.ref outW) ::
        .inst mc.name instName connsF.reverse ::
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).state.module.body := by
    rw [ht, emitAssign_body_cons, addOutput_state, hwEq]
    show _ :: (sm0.module.addOutput _).body = _
    rw [addOutBody, hrec]
    show _ :: smR.module.body = _
    rw [hsmR, hsI]
    show _ :: (_ :: sN.module.body) = _
    rw [hsN, (CircuitM.freshName_spec _ _ _).2.2, hsO', outWiresPure_body,
      instClkRstPure_body, hsB, designMod]
  have mBody : m.body = (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.module.body.reverse ++
      [.inst mc.name instName connsF.reverse,
       .assign "out" (.ref outW)] := by
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
        = s.design from fun s => freshName_design _ _ s, hsO', outWiresPure_design,
      instClkRstPure_design, hsB]
  have emitAssignInputs : ∀ (l : String) (r : Sparkle.IR.AST.Expr) (s : CircuitState),
      (CircuitM.emitAssign l r s).2.module.inputs = s.module.inputs :=
    fun _ _ _ => rfl
  have addOutputInputs : ∀ (n : String) (ty : Sparkle.IR.Type.HWType) (s : CircuitState),
      (CircuitM.addOutput n ty s).2.module.inputs = s.module.inputs :=
    fun _ _ _ => rfl
  have stInputs : st.module.inputs = (instClkRstPure [] ports sB).2.module.inputs := by
    rw [ht]
    show (CircuitM.emitAssign "out" _ (CircuitM.addOutput "out" ty sm0).2).2.module.inputs = _
    rw [emitAssignInputs, addOutputInputs, hrec]
    show smR.module.inputs = _
    rw [hsmR, hsI]
    show sN.module.inputs = _
    rw [hsN, (CircuitM.freshName_spec _ _ _).2.2, hsO', outWiresPure_inputs]
  have hinNames : ∀ pt ∈ ports, (pt.name == "clk" || pt.name == "rst") = true →
      ∃ q ∈ m.inputs, q.name = pt.name := by
    intro pt hpt hcr
    obtain ⟨q, hq, hqn⟩ := instClkRstPure_inputs_names ports [] sB pt hpt hcr
    refine ⟨q, ?_, hqn⟩
    rw [hm]
    show _ ∈ (addClockResetIfSequential st.module).inputs.reverse
    rw [List.mem_reverse]
    exact (addClockReset_facts st.module).2.2.2 _ (by rw [stInputs]; exact hq)
  have stWires : st.module.wires = sN.module.wires := by
    rw [ht, Tools.ShippingTranslateSoundness.emitAssign_wires]
    show sm0.module.wires = _
    rw [hrec]
    show smR.module.wires = _
    rw [hsmR, hsI]
    rfl
  have stInputsN : st.module.inputs = sN.module.inputs := by
    rw [ht]
    show (CircuitM.emitAssign "out" _ (CircuitM.addOutput "out" ty sm0).2).2.module.inputs = _
    rw [emitAssignInputs, addOutputInputs, hrec]
    show smR.module.inputs = _
    rw [hsmR, hsI]
    rfl
  have linkedFinish : ∀ {cs : List (String × Sparkle.IR.AST.Expr)},
      Linked sN.module mc cs → Linked m mc cs := by
    intro cs h0
    refine h0.mono ?_ ?_
    · intro q hq
      rw [hm]
      show q ∈ ((addClockResetIfSequential st.module).finalize).wires
      simp only [Sparkle.IR.AST.Module.finalize, (addClockReset_facts st.module).2.1]
      rw [List.mem_reverse, stWires]
      exact hq
    · intro q hq
      rw [hm]
      show q ∈ (addClockResetIfSequential st.module).inputs.reverse
      rw [List.mem_reverse]
      exact (addClockReset_facts st.module).2.2.2 q (by rw [stInputsN]; exact hq)
  have hLinkedM : Linked m mc (conns.reverse ++
      (outs.zip (outWireNames "sub_call" outs sF)).map
        (fun ow => (ow.1.name, Sparkle.IR.AST.Expr.ref ow.2))) := by
    have h0 := instLinked_sound hlinked
    rw [hconnsF, List.reverse_append, List.reverse_reverse] at h0
    exact linkedFinish h0
  refine ⟨?_, ?_, wNotOut, hLinkedM, hinNames, aWs, hlenW, ?_, ?_⟩
  · rw [mBody, hbodyR, hconnsF, hsF']
    simp
  · rw [hd, stDesign, hpdesR]
    rfl
  · rw [hconnsEq, instClkRstPure_fst]
    simp
  · intro i hi
    have hiA : i < argIds.length := by rw [← hlenW]; exact hi
    obtain ⟨-, hdecl, hval⟩ := hQ i hiA hi
    exact ⟨hval, inputNotOut _ hdecl⟩

/-- The run's predicate on the quoted n-ary call computes to the tag check. -/
theorem instancePredicate_instEN (env : Environment) (mn : Name) (lvls : List Level)
    (dom : Lean.Expr) (args : List Lean.Expr)
    (h : Sparkle.Compiler.isHardwareModule env mn = true) :
    Sparkle.Compiler.Elab.instancePredicate env (instEN mn lvls dom args) = true := by
  unfold Sparkle.Compiler.Elab.instancePredicate
  rw [instEN_getAppFn]
  show (Sparkle.Compiler.isHardwareModule env mn || _) = true
  rw [h]
  rfl

/-- The run's predicate on the quoted one-input call computes to the tag check. -/
theorem instancePredicate_instE1 (env : Environment) (mn : Name) (lvls : List Level)
    (dom a : Lean.Expr) (h : Sparkle.Compiler.isHardwareModule env mn = true) :
    Sparkle.Compiler.Elab.instancePredicate env (instE1 mn lvls dom a) = true := by
  show (Sparkle.Compiler.isHardwareModule env mn || _) = true
  rw [h]
  rfl

/-- The run's predicate on the quoted call computes to the tag check. -/
theorem instancePredicate_instE2 (env : Environment) (mn : Name) (lvls : List Level)
    (dom a b : Lean.Expr) (h : Sparkle.Compiler.isHardwareModule env mn = true) :
    Sparkle.Compiler.Elab.instancePredicate env (instE2 mn lvls dom a b) = true := by
  show (Sparkle.Compiler.isHardwareModule env mn || _) = true
  rw [h]
  rfl

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

/-- The n-ary dispatcher. -/
theorem synthesizeFromConst_instanceN_sound {logProf declName ci bs body m d}
    {isInst : Lean.Expr → Bool}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      [] false true ci isInst) (m, d)) :
    InstanceNPreserves declName bs body m d := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_instanceN_sound run

/-- The general single-output dispatcher. -/
theorem synthesizeFromConst_instanceG_sound {logProf declName ci bs body m d}
    {isInst : Lean.Expr → Bool}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      [] false true ci isInst) (m, d)) :
    InstanceGPreserves declName bs body m d := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_instanceG_sound run

/-- The run's predicate on the quoted projection: a projection function whose
record argument is a tagged call. -/
theorem instancePredicate_projE (env : Environment) (pn : Name) (lvlsP : List Level)
    (dom : Lean.Expr) (cn : Name) (lvlsC : List Level) (domC : Lean.Expr)
    (args : List Lean.Expr)
    (hproj : ∃ sn, env.getProjectionStructureName? pn = some sn)
    (h : Sparkle.Compiler.isHardwareModule env cn = true) :
    Sparkle.Compiler.Elab.instancePredicate env
      (projE pn lvlsP dom (instEN cn lvlsC domC args)) = true := by
  obtain ⟨sn, hsn⟩ := hproj
  show (Sparkle.Compiler.isHardwareModule env pn ||
    (match env.getProjectionStructureName? pn,
        projE pn lvlsP dom (instEN cn lvlsC domC args) with
     | some _, .app _ record =>
       (match record.getAppFn with
        | .const rn _ => Sparkle.Compiler.isHardwareModule env rn
        | _ => false)
     | _, _ => false)) = true
  rw [hsn]
  show (Sparkle.Compiler.isHardwareModule env pn ||
    (match (instEN cn lvlsC domC args).getAppFn with
     | .const rn _ => Sparkle.Compiler.isHardwareModule env rn
     | _ => false)) = true
  rw [instEN_getAppFn]
  simp [h]

/-- The projection dispatcher. -/
theorem synthesizeFromConst_instanceProj_sound {logProf declName ci bs body m d}
    {isInst : Lean.Expr → Bool}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      [] false true ci isInst) (m, d)) :
    ProjInstancePreserves declName bs body m d := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_instanceProj_sound run

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
        Instance1Preserves declName bs body m d ∧
        InstanceNPreserves declName bs body m d ∧
        InstanceGPreserves declName bs body m d ∧
        ProjInstancePreserves declName bs body m d := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    Tools.ShippingEntrySoundness.synthesizeCombinationalCore_reads hr
  exact ⟨ci, envR, w1, w2, w5, w6, get, henv, fun _ _ old shape =>
    ⟨synthesizeFromConst_instance_sound old shape (Tools.ShippingEntrySoundness.entry_kept shape run).mreturns,
     synthesizeFromConst_instance1_sound old shape (Tools.ShippingEntrySoundness.entry_kept shape run).mreturns,
     synthesizeFromConst_instanceN_sound old shape (Tools.ShippingEntrySoundness.entry_kept shape run).mreturns,
     synthesizeFromConst_instanceG_sound old shape (Tools.ShippingEntrySoundness.entry_kept shape run).mreturns,
     synthesizeFromConst_instanceProj_sound old shape (Tools.ShippingEntrySoundness.entry_kept shape run).mreturns⟩⟩

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
    exact instancePredicate_instE2 _ _ _ _ _ _ (tag _ _ _ henv)
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
    exact instancePredicate_instE1 _ _ _ _ _ (tag _ _ _ henv)
  have shape := instance1_term_gate (d := dv) (by rw [hval]; exact peel) htag
    (hscalar dv hval) hd ha
  exact (sel bs _ (old dv hval) shape).2.1

/-- The n-ary entry endpoint under the run's environment boundaries. -/
theorem instanceN_entry_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {value : Lean.Expr}
    {mn : Name} {lvls : List Level} {dpos : Nat} {poss : List Nat}
    {bs : List (Name × MixedGateBinder)}
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
      instEN mn lvls (inputExpr bs.length dpos) (poss.map (inputExpr bs.length))))
    (hd : ∃ nd kd, bs[dpos]? = some (nd, kd))
    (hpos : ∀ q ∈ poss, ∃ nq kq, bs[q]? = some (nq, kq)) :
    InstanceNPreserves declName bs
      (instEN mn lvls (inputExpr bs.length dpos) (poss.map (inputExpr bs.length))) m d := by
  obtain ⟨ci, envR, w1, w2, w5, w6, get, henv, sel⟩ :=
    synthesizeCombinationalCore_instance_sound hr
  obtain ⟨dv, rfl, hval⟩ := env w1 ci w2 get
  have htag : Sparkle.Compiler.Elab.instancePredicate envR
      (instEN mn lvls (inputExpr bs.length dpos) (poss.map (inputExpr bs.length))) = true := by
    exact instancePredicate_instEN _ _ _ _ _ (tag _ _ _ henv)
  have shape := instanceN_term_gate (d := dv) (by rw [hval]; exact peel) htag
    (hscalar dv hval) hd hpos
  exact (sel bs _ (old dv hval) shape).2.2.1

/-- The general single-output entry endpoint under the run's environment
boundaries: any arity, combinational or sequential child. -/
theorem instanceG_entry_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {value : Lean.Expr}
    {mn : Name} {lvls : List Level} {dpos : Nat} {poss : List Nat}
    {bs : List (Name × MixedGateBinder)}
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
      instEN mn lvls (inputExpr bs.length dpos) (poss.map (inputExpr bs.length))))
    (hd : ∃ nd kd, bs[dpos]? = some (nd, kd))
    (hpos : ∀ q ∈ poss, ∃ nq kq, bs[q]? = some (nq, kq)) :
    InstanceGPreserves declName bs
      (instEN mn lvls (inputExpr bs.length dpos) (poss.map (inputExpr bs.length))) m d := by
  obtain ⟨ci, envR, w1, w2, w5, w6, get, henv, sel⟩ :=
    synthesizeCombinationalCore_instance_sound hr
  obtain ⟨dv, rfl, hval⟩ := env w1 ci w2 get
  have htag : Sparkle.Compiler.Elab.instancePredicate envR
      (instEN mn lvls (inputExpr bs.length dpos) (poss.map (inputExpr bs.length))) = true := by
    exact instancePredicate_instEN _ _ _ _ _ (tag _ _ _ henv)
  have shape := instanceN_term_gate (d := dv) (by rw [hval]; exact peel) htag
    (hscalar dv hval) hd hpos
  exact (sel bs _ (old dv hval) shape).2.2.2.1

/-- The projection entry endpoint under the run's environment boundaries: a
field projection of a canonical call on a tagged multi-output child. -/
theorem instanceProj_entry_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {value : Lean.Expr}
    {pn : Name} {lvlsP : List Level} {cn : Name} {lvlsC : List Level}
    {dposP dposC : Nat} {poss : List Nat}
    {bs : List (Name × MixedGateBinder)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, d) w')
    (env : Tools.ShippingEntrySoundness.EnvDefines mctx mref cctx cref declName value)
    (tag : ∀ wE e wE', RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref wE e wE' →
      (∃ sn, e.getProjectionStructureName? pn = some sn) ∧
      Sparkle.Compiler.isHardwareModule e cn = true)
    (old : ∀ dv : DefinitionVal, dv.value = value →
      certifiedShape? false [] (.defnInfo dv) = none)
    (hscalar : ∀ dv : DefinitionVal, dv.value = value →
      mixedGateResultScalar dv.type = true)
    (peel : mixedGatePeel value = some (bs,
      projE pn lvlsP (inputExpr bs.length dposP)
        (instEN cn lvlsC (inputExpr bs.length dposC) (poss.map (inputExpr bs.length)))))
    (hdP : ∃ nd kd, bs[dposP]? = some (nd, kd))
    (hdC : ∃ nd kd, bs[dposC]? = some (nd, kd))
    (hpos : ∀ q ∈ poss, ∃ nq kq, bs[q]? = some (nq, kq)) :
    ProjInstancePreserves declName bs
      (projE pn lvlsP (inputExpr bs.length dposP)
        (instEN cn lvlsC (inputExpr bs.length dposC) (poss.map (inputExpr bs.length)))) m d := by
  obtain ⟨ci, envR, w1, w2, w5, w6, get, henv, sel⟩ :=
    synthesizeCombinationalCore_instance_sound hr
  obtain ⟨dv, rfl, hval⟩ := env w1 ci w2 get
  have htag : Sparkle.Compiler.Elab.instancePredicate envR
      (projE pn lvlsP (inputExpr bs.length dposP)
        (instEN cn lvlsC (inputExpr bs.length dposC)
          (poss.map (inputExpr bs.length)))) = true :=
    instancePredicate_projE _ _ _ _ _ _ _ _ (tag _ _ _ henv).1 (tag _ _ _ henv).2
  have shape := instanceProj_term_gate (d := dv) (by rw [hval]; exact peel) htag
    (hscalar dv hval) hdP hdC hpos
  exact (sel bs _ (old dv hval) shape).2.2.2.2

end Tools.ShippingInstanceEntrySoundness

import Tools.ShippingInstanceEntrySoundness
import Tools.ShippingUnifiedRecursion

/-! Instance calls as LEAVES of certified cones.

The unified fuel induction is generic in its leaf expressions: every leaf
brings its own contract. This module proves that contract for a canonical
call on a single-output COMBINATIONAL `@[hardware_module]` child, over the
hierarchical semantic context: the arguments are lowered through their own
contracts, one instance statement is emitted, and the result wire carries
the linked child's source function of the argument values. The validated
cache paths (expression cache and single-out instance cache) are covered
without any premise about the mutable caches. -/
namespace Tools.ShippingInstanceLeaf
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingCompareLoweringSoundness (ScalarWidthsAgree)
open Tools.ShippingMixedLiteralSoundness (DeclGrows)
open Tools.ShippingBoolSourceSoundness (translateControlCachedWith_returns)
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingMixedBinarySoundness (Frame ScalarWires)
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion
open Tools.ShippingHierarchySoundness Tools.ShippingLinkCtx
open Tools.ShippingInstanceEntrySoundness
open Tools.ShippingEntrySoundness (MReturns)

set_option linter.unusedSectionVars false

variable [HierCtx] [ChildSem]

/-! ## The hierarchical run step -/

/-- Emitting an instance statement extends the linked run by one child
evaluation on the connection-fed environment. -/
theorem runs_inst {we : WEnv} {mems : MEnv} {initial : Env} {s : CircuitState} {prior : Env}
    {mn iname : String} {conns : List (String × Sparkle.IR.AST.Expr)}
    {child : Sparkle.IR.AST.Module} {cwe : WEnv} {cres : Env}
    (h : LinkCtx.Runs we mems initial s prior)
    (hchild : HierCtx.children mn = some (child, cwe))
    (hrun : evalAssigns cwe mems child.body (connEnv conns prior) = some cres) :
    LinkCtx.Runs we mems initial
      { s with module := s.module.addStmt (.inst mn iname conns) }
      (bindOuts child.outputs conns cres prior) := by
  rw [HierCtx.runs_def] at h ⊢
  have hb : ({ s with module := s.module.addStmt (.inst mn iname conns) } :
      CircuitState).module.finalize.body =
      s.module.finalize.body ++ [.inst mn iname conns] := by
    show (Stmt.inst mn iname conns :: s.module.body).reverse = s.module.body.reverse ++ _
    exact List.reverse_cons
  rw [hb, evalAssignsH_append, h]
  simp [evalAssignsH, hchild, hrun]

/-! ## Structural frames of the instance lowering's own steps -/

theorem frame_design (s : CircuitState) (d' : Design) :
    Frame s { s with design := d' } :=
  ⟨fun _ hp => hp, fun _ hp => hp, rfl, fun _ _ he => Or.inl he, fun h => h, fun h => h,
    rfl, rfl, fun h => h, rfl, rfl, fun _ hp => Or.inl hp⟩

theorem frame_freshName (s : CircuitState) (hint : String) (named : Bool) :
    Frame s (CircuitM.freshName hint named s).2 := by
  have spec := CircuitM.freshName_spec hint named s
  have hmod := spec.2.2
  refine ⟨?_, ?_, CircuitM.freshName_sourceBindings _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp; rw [hmod]; exact hp
  · intro z hz; rw [spec.2.1]; simp [Std.HashSet.contains_insert, hz]
  · intro w e he; left; rw [CircuitM.freshName_translateRecord] at he; exact he
  · intro hw
    refine ⟨by rw [hmod]; exact hw.1, ?_⟩
    intro p hp
    rw [hmod] at hp
    rw [spec.2.1]
    simp [Std.HashSet.contains_insert, hw.2 p hp]
  · intro hs p hp; rw [hmod] at hp; exact hs p hp
  · rw [hmod]
  · rw [hmod]
  · intro hs; rw [hmod]; exact hs
  · rw [hmod]
  · rw [hmod]
  · intro p hp; rw [hmod] at hp; exact Or.inl hp

theorem frame_emitInst (s : CircuitState) (st : Stmt) :
    Frame s { s with module := s.module.addStmt st } :=
  ⟨fun _ hp => hp, fun _ hp => hp, rfl, fun _ _ he => Or.inl he, fun h => h, fun h => h,
    rfl, rfl, fun _ => HierCtx.simple_all _, rfl, rfl, fun _ hp => Or.inl hp⟩

/-- Recording a result that is fresh at the start, or already recorded there
for the same expression, keeps the structural contract. -/
theorem frame_record_valid {s t u : CircuitState} {e : Lean.Expr} {w : String}
    {cacheable : Bool} {ctx : CompilerState} {resultUnit : Unit} (h : Frame s t)
    (ok : s.usedNames.contains w = false ∨ s.translateRecord.get? w = some e)
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
        subst z
        cases he
        rcases ok with fresh | old
        · exact Or.inr fresh
        · exact Or.inl old
    · exact h.records z ex he
  · intro hw; rw [hs]; exact h.wires hw
  · intro hw; rw [hs]; exact h.scalar hw
  · rw [hs]; exact h.outputs
  · rw [hs]; exact h.inputs
  · intro hb; rw [hs]; exact h.simple hb
  · rw [hs]; exact h.parameters
  · rw [hs]; exact h.primitive
  · intro p hp; rw [hs] at hp; exact h.wireNames p hp

/-! ## The operand walk through arbitrary operand contracts -/

theorem instArgs_frame {rec : TranslateFn} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env} :
    ∀ (pairs : List (Port × Lean.Expr)) (vs : List Value)
      (acc : List (String × Sparkle.IR.AST.Expr)) (i : Nat)
      (r : List (String × Sparkle.IR.AST.Expr)) (s t : CircuitState),
    pairs.length = vs.length →
    (∀ k (hk : k < pairs.length) (hk' : k < vs.length),
      Contract rec ctx inputs we mems initial (pairs[k]'hk).2 (vs[k]'hk')) →
    Lookup ctx inputs s →
    Returns (instArgs rec acc pairs i) ctx s r t → Frame s t
  | [], _, acc, i, r, s, t, _, _, _, h => by
    unfold instArgs at h
    obtain ⟨-, hs⟩ := Returns.pure h
    rw [hs]
    exact Frame.refl _
  | (p, e) :: rest, [], acc, i, r, s, t, hlen, _, _, _ => by
    simp at hlen
  | (p, e) :: rest, v :: vs, acc, i, r, s, t, hlen, hc, lookup, h => by
    unfold instArgs at h
    obtain ⟨aw, s1, hread, hrest⟩ := Returns.bind (m := rec e _ false false) h
    have f1 := (hc 0 (by simp) (by simp)).frame _ false false s s1 aw lookup hread
    have f2 := instArgs_frame rest vs _ (i + 1) r s1 t (by simpa using hlen)
      (fun k hk hk' => by
        have := hc (k + 1) (by simpa using hk) (by simpa using hk')
        simpa using this)
      (lookup.transfer f1) hrest
    exact f1.trans f2

theorem instArgs_sem {rec : TranslateFn} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env} :
    ∀ (pairs : List (Port × Lean.Expr)) (vs : List Value)
      (acc : List (String × Sparkle.IR.AST.Expr)) (i : Nat)
      (r : List (String × Sparkle.IR.AST.Expr)) (s t : CircuitState) (prior : Env),
    pairs.length = vs.length →
    (∀ k (hk : k < pairs.length) (hk' : k < vs.length),
      Contract rec ctx inputs we mems initial (pairs[k]'hk).2 (vs[k]'hk')) →
    Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we t →
    Returns (instArgs rec acc pairs i) ctx s r t →
    ∃ (ws : List String) (result : Env), ws.length = pairs.length ∧
      r = ((pairs.zip ws).map
        (fun pw => (pw.1.1.name, Sparkle.IR.AST.Expr.ref pw.2))).reverse ++ acc ∧
      Inv ctx inputs we mems initial t result ∧
      (∀ z, s.usedNames.contains z = true → result z = prior z) ∧
      (∀ z, s.usedNames.contains z = true → t.usedNames.contains z = true) ∧
      ∀ k (hk : k < ws.length) (hk' : k < vs.length),
        result (ws[k]'hk) = (vs[k]'hk').toNat ∧ t.usedNames.contains (ws[k]'hk) = true
  | [], _, acc, i, r, s, t, prior, _, _, h, _, hr => by
    unfold instArgs at hr
    obtain ⟨hr', hs⟩ := Returns.pure hr
    rw [hs]
    exact ⟨[], prior, rfl, by rw [hr']; rfl, h, fun _ _ => rfl, fun _ hz => hz,
      fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | (p, e) :: rest, [], acc, i, r, s, t, prior, hlen, _, _, _, _ => by
    simp at hlen
  | (p, e) :: rest, v :: vs, acc, i, r, s, t, prior, hlen, hc, h, widths, hr => by
    unfold instArgs at hr
    obtain ⟨aw, s1, hread, hrest⟩ := Returns.bind (m := rec e _ false false) hr
    have c0 := hc 0 (by simp) (by simp)
    have lookup := Lookup.ofInputs h.inputs
    have f1 := c0.frame _ false false s s1 aw lookup hread
    have hcRest : ∀ k (hk : k < rest.length) (hk' : k < vs.length),
        Contract rec ctx inputs we mems initial (rest[k]'hk).2 (vs[k]'hk') := by
      intro k hk hk'
      have := hc (k + 1) (by simpa using hk) (by simpa using hk')
      simpa using this
    have f2 := instArgs_frame rest vs _ (i + 1) r s1 t (by simpa using hlen) hcRest
      (lookup.transfer f1) hrest
    have w1 : ScalarWidthsAgree we s1 := f2.decls.widths widths
    have step := c0.sem _ false false s s1 aw prior h w1 hread
    obtain ⟨res1, inv1, val1, fr1⟩ := step.execution
    obtain ⟨ws, result, hlenW, hrEq, invT, frT, grT, vals⟩ :=
      instArgs_sem rest vs _ (i + 1) r s1 t res1 (by simpa using hlen) hcRest inv1 widths hrest
    refine ⟨aw :: ws, result, by simp [hlenW], ?_, invT, ?_, ?_, ?_⟩
    · rw [hrEq]
      simp
    · intro z hz
      rw [frT z (step.grows z hz)]
      exact fr1 z hz
    · intro z hz
      exact grT z (step.grows z hz)
    · intro k hk hk'
      cases k with
      | zero =>
        refine ⟨?_, grT aw step.used⟩
        show result aw = v.toNat
        rw [frT aw step.used]
        exact val1
      | succ k => exact vals k (by simpa using hk) (by simpa using hk')

/-! ## The uncached lowering, decomposed once -/

theorem filter_noclk {ps : List Port}
    (h : ∀ p ∈ ps, (p.name == "clk") = false ∧ (p.name == "rst") = false) :
    ps.filter (fun p => p.name != "clk" && p.name != "rst") = ps := by
  rw [List.filter_eq_self]
  intro p hp
  obtain ⟨h1, h2⟩ := h p hp
  simp [bne, h1, h2]

/-- The shape of one uncached instance lowering on a child with no clk/rst
ports and no nested design: only the design changes before the operand walk,
then either a validated cache hit returns a wire recorded for this very
expression, or a fresh wire is allocated and ONE instance statement emitted. -/
theorem instUncached_shape {rec : TranslateFn} {ctx : CompilerState} {mn : Name}
    {mc : Sparkle.IR.AST.Module} {dc : Design} {so : Port}
    {lvls : List Level} {dom : Lean.Expr} {argsE : List Lean.Expr}
    {hint : String} {top named : Bool} {s t : CircuitState} {w : String}
    (hdc : dc.modules = [])
    (hnoclk : ∀ p ∈ mc.inputs, (p.name == "clk") = false ∧ (p.name == "rst") = false)
    (hlen : mc.inputs.length = argsE.length)
    (run : Returns (translateInstanceUncachedWith rec mn mc dc so
      (instEN mn lvls dom argsE) hint top named) ctx s w t) :
    ∃ (d' : Design) (conns : List (String × Sparkle.IR.AST.Expr)) (sA : CircuitState),
      Returns (instArgs rec [] (mc.inputs.zip argsE) 0) ctx { s with design := d' } conns sA ∧
      ((instHitValid s.translateRecord (instEN mn lvls dom argsE) w = true ∧ t = sA) ∨
       (∃ iname : String, w = (CircuitM.makeWire hint so.ty named sA).1 ∧
         t = { (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2 with
           module := (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2.module.addStmt
             (.inst mc.name iname (conns.reverse ++ [(so.name, .ref w)])) })) := by
  rw [instanceUncached_run] at run
  obtain ⟨cs0, sG, hget0, k1⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) run
  obtain ⟨hcs0, hsG⟩ := Returns.get hget0
  rw [hcs0, hsG] at k1
  rw [hdc] at k1
  obtain ⟨u0, sA0, hAdd0, k2⟩ := Returns.bind (m := instAddModules _ []) k1
  obtain ⟨-, hsA0⟩ := Returns.pure (by exact hAdd0 : Returns (pure ()) _ _ u0 sA0)
  rw [hsA0] at k2
  obtain ⟨uR, sB, hReg, k3⟩ := Returns.bind (m := instRegisterChild _ mc) k2
  have hsB : ∃ d', sB = { s with design := d' } := by
    unfold instRegisterChild at hReg
    obtain ⟨cs, s1, hget, k⟩ := Returns.bind (m := (get : CompilerM CircuitState)) hReg
    obtain ⟨hcs, hs1⟩ := Returns.get hget
    rw [hcs, hs1] at k
    split at k
    · exact ⟨_, addModuleToDesignC_returns k⟩
    · obtain ⟨-, hs⟩ := Returns.pure k
      exact ⟨s.design, hs⟩
  obtain ⟨d', hsB⟩ := hsB
  obtain ⟨conns0, sC, hClk, k4⟩ := Returns.bind (m := instClkRst [] mc.inputs) k3
  obtain ⟨hconns0, hsC⟩ := instClkRst_skip hnoclk hClk
  rw [filter_noclk hnoclk, instEN_spineArgs] at k4
  obtain ⟨uG, sH, hGuard, k5⟩ := Returns.bind (m := instArityCheck mn _ _) k4
  unfold instArityCheck at hGuard
  rw [if_neg (by simp [hlen])] at hGuard
  obtain ⟨-, hsH⟩ := Returns.pure hGuard
  have hdrop : (dom :: argsE).drop ((dom :: argsE).length - mc.inputs.length) = argsE := by
    simp [hlen]
  rw [hdrop, hconns0] at k5
  obtain ⟨conns, sF, hArgs, k6⟩ := Returns.bind (m := instArgs _ _ _ 0) k5
  rw [hsH, hsC, hsB] at hArgs
  refine ⟨d', conns, sF, hArgs, ?_⟩
  obtain ⟨csP, sP2, hgetP, k7⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) k6
  obtain ⟨hcsP, hsP2⟩ := Returns.get hgetP
  obtain ⟨cVal, sQ, hCacheRead, k8⟩ :=
    Returns.bind (m := CompilerM.liftMetaM instArmCacheGet) k7
  have hsQ := Returns.liftMetaM hCacheRead
  cases hhit : (cVal.get? s!"{csP.module.name}#{mc.name}#{String.intercalate ";"
      (conns.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))}").filter
      (instHitValid s.translateRecord (instEN mn lvls dom argsE)) with
  | some cw =>
    rw [hhit] at k8
    obtain ⟨hw, ht⟩ := Returns.pure k8
    left
    refine ⟨?_, by rw [ht, hsQ, hsP2]⟩
    rw [hw]
    cases hget : cVal.get? s!"{csP.module.name}#{mc.name}#{String.intercalate ";"
        (conns.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))}" with
    | none => rw [hget] at hhit; cases hhit
    | some c0 =>
      rw [hget] at hhit
      by_cases hv : instHitValid s.translateRecord (instEN mn lvls dom argsE) c0 = true
      · have : (some c0 : Option String) = some cw := by
          simpa [Option.filter, hv] using hhit
        cases this
        exact hv
      · simp [Option.filter, hv] at hhit
  | none =>
    rw [hhit] at k8
    simp only [] at k8
    obtain ⟨outW, sW, hMk, k9⟩ := Returns.bind (m := CompilerM.makeWire hint _ named) k8
    obtain ⟨houtW, hsW⟩ := makeWireC_returns hMk
    obtain ⟨uP, sV, hPut, k10⟩ :=
      Returns.bind (m := CompilerM.liftMetaM (instArmCachePut _ _)) k9
    have hsV := Returns.liftMetaM hPut
    obtain ⟨instName, sN, hFresh, k11⟩ := Returns.bind (m := CompilerM.freshName _) k10
    obtain ⟨hinstName, hsN⟩ := freshNameC_returns hFresh
    obtain ⟨uE, sI, hEmit, k12⟩ :=
      Returns.bind (m := CompilerM.emitInstance mc.name _ _) k11
    have hsI := emitInstanceC_returns hEmit
    obtain ⟨hwEq, ht⟩ := Returns.pure k12
    right
    refine ⟨instName, ?_, ?_⟩
    · rw [hwEq, houtW, hsQ, hsP2]
    · rw [ht, hsI, hsN, hsV, hsW, hsQ, hsP2, hwEq]
      simp

/-! ## The leaf contract -/

/-- Writing a reserved wire — one no input is bound to and no meaningful
record names — preserves the invariant, whatever statement performed the
write (the run and typing facts of the new state are supplied). -/
theorem inv_write_reserved {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {s t : CircuitState} {prior : Env}
    {w : String} {value : Nat}
    (h : Inv ctx inputs we mems initial s prior)
    (inputSafe : ∀ id v, inputs id = some v → visible ctx s.sourceBindings id ≠ some w)
    (recordSafe : ∀ e v, s.translateRecord.get? w = some e → ¬ Meaning inputs e v)
    (hb : t.sourceBindings = s.sourceBindings) (hr : t.translateRecord = s.translateRecord)
    (hu : ∀ z, s.usedNames.contains z = true → t.usedNames.contains z = true)
    (runs : LinkCtx.Runs we mems initial t (write prior w value))
    (typed : LinkCtx.Typed we t) :
    Inv ctx inputs we mems initial t (write prior w value) := by
  refine ⟨runs, ⟨?_⟩, ?_, typed⟩
  · intro id v hi
    obtain ⟨z, bound, used, val, width⟩ := h.inputs.lookup id v hi
    have ne : z ≠ w := by intro eq; subst z; exact inputSafe id v hi bound
    exact ⟨z, by rw [hb]; exact bound, hu z used, by simpa [write, ne] using val, width⟩
  · intro z e record v meaning
    rw [hr] at record
    have ne : z ≠ w := by intro eq; subst z; exact recordSafe e v record meaning
    obtain ⟨used, val, width⟩ := h.records z e record v meaning
    exact ⟨hu z used, by simpa [write, ne] using val, width⟩

theorem zip3_map {α β γ δ : Type} (f : α → γ → δ) : ∀ (as : List α) (bs : List β)
    (cs : List γ), as.length = bs.length →
    ((as.zip bs).zip cs).map (fun pw => f pw.1.1 pw.2) =
      (as.zip cs).map (fun pw => f pw.1 pw.2)
  | [], _, _, _ => by simp
  | a :: as, [], cs, h => by simp at h
  | a :: as, b :: bs, [], _ => by simp
  | a :: as, b :: bs, c :: cs, h => by
    simp [zip3_map f as bs cs (by simpa using h)]

theorem lookup_append_left {l1 l2 : List (String × Sparkle.IR.AST.Expr)} {k : String}
    {v : Sparkle.IR.AST.Expr} (h : l1.lookup k = some v) : (l1 ++ l2).lookup k = some v := by
  induction l1 with
  | nil => cases h
  | cons p rest ih =>
    obtain ⟨pk, pv⟩ := p
    by_cases hk : (k == pk) = true
    · simp [List.lookup, hk] at h ⊢
      exact h
    · have hk' : (k == pk) = false := by simpa using hk
      simp [List.lookup, hk'] at h ⊢
      exact ih h

/-- The linked child computes its source function: on any environment whose
input ports carry the packed argument values, the child's body drives its
output port with the packed result. -/
def ChildCorrect (mn : Name) (mc : Sparkle.IR.AST.Module) (cwe : WEnv) (outName : String) :
    Prop :=
  ∀ (mems : MEnv) (envIn : Env) (vs : List Value) (v : Value),
    ChildSem.childSem mn vs = some v →
    (∀ k (hk : k < mc.inputs.length) (hk' : k < vs.length),
      envIn (mc.inputs[k]'hk).name = (vs[k]'hk').toNat) →
    ∃ cres, evalAssigns cwe mems mc.body envIn = some cres ∧ cres outName = v.toNat

/-- Every child synthesis of `mn` the run performs, at ANY recursion fuel,
returns the pinned pair (inside a cone the arm runs below the entry fuel). -/
def SubSynthDefinesAll (mn : Name) (mc : Sparkle.IR.AST.Module) (dc : Design) : Prop :=
  ∀ fuel r, MReturns (Rec.synthesizeCombinational
    (fun e h t n => translateFuelFix translateStep fuel e h t n) mn) r → r = (mc, dc)

theorem instHitValid_record {record : Std.HashMap String Lean.Expr} {e : Lean.Expr}
    {cw : String} (h : instHitValid record e cw = true) : record.get? cw = some e := by
  unfold instHitValid at h
  cases hg : record.get? cw with
  | none => rw [hg] at h; cases h
  | some e' =>
    rw [hg] at h
    have : e' = e := @of_decide_eq_true _ (Sparkle.Compiler.ExprDecEq.exprDecEq e' e) h
    rw [this]

/-- Port-name lookups in the connection list the operand walk builds. -/
theorem lookup_zip_ports : ∀ (ports : List Port) (ws : List String) (k : Nat)
    (hk : k < ports.length) (hk' : k < ws.length),
    (ports.map (·.name)).Nodup →
    ((ports.zip ws).map (fun pw => (pw.1.name, Sparkle.IR.AST.Expr.ref pw.2))).lookup
      (ports[k]'hk).name = some (.ref (ws[k]'hk'))
  | [], _, k, hk, _, _ => absurd hk (Nat.not_lt_zero k)
  | p :: ps, [], k, _, hk', _ => absurd hk' (Nat.not_lt_zero k)
  | p :: ps, w :: ws, 0, _, _, _ => by
    simp
  | p :: ps, w :: ws, k + 1, hk, hk', hnd => by
    have hnd' : p.name ∉ ps.map (·.name) ∧ (ps.map (·.name)).Nodup :=
      List.nodup_cons.mp hnd
    have hne : ((ps[k]'(by simpa using hk)).name == p.name) = false := by
      apply beq_false_of_ne
      intro eq
      exact hnd'.1 (by rw [← eq]; exact List.mem_map.mpr ⟨_, List.getElem_mem _, rfl⟩)
    show (match (ps[k]'(by simpa using hk)).name == p.name with
      | true => some (Sparkle.IR.AST.Expr.ref w)
      | false => List.lookup (ps[k]'(by simpa using hk)).name
          ((ps.zip ws).map (fun (pw : Port × String) =>
            (pw.1.name, Sparkle.IR.AST.Expr.ref pw.2)))) = _
    rw [hne]
    exact lookup_zip_ports ps ws k (by simpa using hk) (by simpa using hk') hnd'.2

set_option maxHeartbeats 1000000 in
/-- **The instance-leaf contract.** One certified step on a canonical call
of a tagged single-output combinational child, with every operand under its
own contract, satisfies the unified contract at the linked child's source
value — hits of both validated caches included. -/
theorem inst_leaf_contract {rec : TranslateFn} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env}
    {mn : Name} {lvls : List Level} {dom : Lean.Expr} {argsE : List Lean.Expr}
    {vs : List Value} {v : Value} {mc : Sparkle.IR.AST.Module} {dc : Design} {cwe : WEnv}
    {outName : String} {wOut : Nat}
    (hstep : ∀ hint top named, translateStepWith translateFallback rec
        (instEN mn lvls dom argsE) hint top named =
      translateInstanceOrFallback rec (instEN mn lvls dom argsE) hint top named)
    (htag : HardwareTagged mn)
    (hsub : ∀ r, MReturns (Rec.synthesizeCombinational
      (fun e h t n => rec e h t n) mn) r → r = (mc, dc))
    (hdc : dc.modules = [])
    (hnoclk : ∀ p ∈ mc.inputs, (p.name == "clk") = false ∧ (p.name == "rst") = false)
    (hnodup : (mc.inputs.map (·.name)).Nodup)
    (houts : mc.outputs = [⟨outName, .bitVector wOut⟩])
    (houtFresh : ∀ p ∈ mc.inputs, (outName == p.name) = false)
    (hlen : mc.inputs.length = argsE.length) (hlenV : argsE.length = vs.length)
    (hargs : ∀ k (hk : k < argsE.length) (hk' : k < vs.length),
      Contract rec ctx inputs we mems initial (argsE[k]'hk) (vs[k]'hk'))
    (meaning : Meaning inputs (instEN mn lvls dom argsE) v)
    (hsem : ChildSem.childSem mn vs = some v)
    (hwidth : v.kind.width = wOut)
    (hchild : HierCtx.children mc.name = some (mc, cwe))
    (hcorrect : ChildCorrect mn mc cwe outName) :
    Contract (translateStepWith translateFallback rec) ctx inputs we mems initial
      (instEN mn lvls dom argsE) v := by
  -- the dispatch prefix, shared by both halves
  have prefixRun : ∀ hint top named s t w,
      Returns (translateStepWith translateFallback rec (instEN mn lvls dom argsE)
        hint top named) ctx s w t →
      Returns (translateControlCachedWith
        (translateInstanceUncachedWith rec mn mc dc ⟨outName, .bitVector wOut⟩)
        (instEN mn lvls dom argsE) hint top named) ctx s w t := by
    intro hint top named s t w tr
    rw [hstep] at tr
    unfold translateInstanceOrFallback at tr
    rw [instEN_getAppFn] at tr
    obtain ⟨env, sE, hEnvRead, tr⟩ := Returns.bind tr
    obtain ⟨hEnvM, hsE⟩ := Returns.liftMetaM_mreturns hEnvRead
    rw [hsE] at tr
    rw [htag env hEnvM] at tr
    simp only [if_true] at tr
    obtain ⟨sub, sS, hSubRead, tr⟩ := Returns.bind tr
    obtain ⟨hSubM, hsS⟩ := Returns.liftMetaM_mreturns hSubRead
    rw [hsS] at tr
    rw [hsub sub hSubM] at tr
    rw [show ((mc, dc).1.outputs) = mc.outputs from rfl, houts] at tr
    exact tr
  have pairsLen : (mc.inputs.zip argsE).length = vs.length := by
    simp [hlen, hlenV]
  have pairContracts : ∀ k (hk : k < (mc.inputs.zip argsE).length) (hk' : k < vs.length),
      Contract rec ctx inputs we mems initial ((mc.inputs.zip argsE)[k]'hk).2 (vs[k]'hk') := by
    intro k hk hk'
    have hkA : k < argsE.length := by rw [hlenV]; exact hk'
    have : ((mc.inputs.zip argsE)[k]'hk).2 = argsE[k]'hkA := by simp
    rw [this]
    exact hargs k hkA hk'
  -- the structural frame of one uncached lowering
  have lowerFrame : ∀ hint top named s sm w, Lookup ctx inputs s →
      Returns (translateInstanceUncachedWith rec mn mc dc ⟨outName, .bitVector wOut⟩
        (instEN mn lvls dom argsE) hint top named) ctx s w sm →
      Frame s sm ∧ (s.usedNames.contains w = false ∨
        s.translateRecord.get? w = some (instEN mn lvls dom argsE)) := by
    intro hint top named s sm w lookup run
    obtain ⟨d', conns, sA, hArgs, hcase⟩ := instUncached_shape hdc hnoclk hlen run
    have fD : Frame s { s with design := d' } := frame_design s d'
    have fA := instArgs_frame _ vs _ 0 conns _ sA pairsLen pairContracts
      (lookup.transfer fD) hArgs
    rcases hcase with ⟨hvalid, ht⟩ | ⟨iname, hw, ht⟩
    · rw [ht]
      exact ⟨fD.trans fA, Or.inr (instHitValid_record hvalid)⟩
    · have fW := Tools.ShippingMixedBinarySoundness.Frame.makeWire sA hint wOut named
      have fN := frame_freshName (CircuitM.makeWire hint (.bitVector wOut) named sA).2
        s!"inst_{mc.name}" false
      have fI := frame_emitInst (CircuitM.freshName s!"inst_{mc.name}" false
          (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2
        (.inst mc.name iname (conns.reverse ++ [(outName, .ref w)]))
      refine ⟨?_, Or.inl ?_⟩
      · rw [ht]
        exact (((fD.trans fA).trans fW).trans fN).trans fI
      · have freshA := (CircuitM.makeWire_spec hint (.bitVector wOut) named sA).1
        rw [← hw] at freshA
        cases hu : s.usedNames.contains w with
        | false => rfl
        | true =>
          have := (fD.trans fA).used w hu
          rw [freshA] at this
          cases this
  constructor
  · intro hint top named s t w lookup hr
    rcases translateControlCachedWith_returns (prefixRun hint top named s t w hr) with
      hit | ⟨sm, miss, record⟩
    · have ht := (cacheLookupValidated_returns hit).1
      rw [ht]
      exact Frame.refl s
    · obtain ⟨fl, ok⟩ := lowerFrame hint top named s sm w lookup miss
      exact frame_record_valid fl ok record
  · intro hint top named s t w prior h widths hr
    refine cached_widths_outcome h meaning widths ?_ (prefixRun hint top named s t w hr)
    intro sm r wm run
    obtain ⟨d', conns, sA, hArgs, hcase⟩ := instUncached_shape hdc hnoclk hlen run
    -- only the design changed before the operand walk
    have invD : Inv ctx inputs we mems initial { s with design := d' } prior :=
      h.transfer (LinkCtx.runs_body (s := s) rfl h.runs)
        (LinkCtx.typed_body (s := s) rfl h.typed) rfl rfl
        (fun _ hu => hu) (fun _ _ => rfl)
    have lookupD : Lookup ctx inputs { s with design := d' } := Lookup.ofInputs invD.inputs
    have fA := instArgs_frame _ vs _ 0 conns _ sA pairsLen pairContracts lookupD hArgs
    rcases hcase with ⟨hvalid, ht⟩ | ⟨iname, hw, ht⟩
    · -- a validated single-out cache hit: the wire is recorded for this expression
      have wA : ScalarWidthsAgree we sA := by rw [← ht]; exact wm
      obtain ⟨ws, resA, hlenW, hconns, invA, frA, grA, vals⟩ :=
        instArgs_sem _ vs _ 0 conns _ sA prior pairsLen pairContracts invD wA hArgs
      obtain ⟨used, value, width⟩ :=
        h.records r _ (instHitValid_record hvalid) v meaning
      rw [ht]
      exact ⟨grA r used, width, grA, resA, invA, (frA r used).trans value, frA⟩
    · -- a fresh wire and one instance statement
      have hdeclT : ({ name := r, ty := .bitVector wOut } : Port) ∈ sm.module.wires := by
        rw [ht]
        show _ ∈ (CircuitM.freshName s!"inst_{mc.name}" false
          (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.module.wires
        rw [(CircuitM.freshName_spec _ _ _).2.2,
          (CircuitM.makeWire_spec hint (.bitVector wOut) named sA).2.2.2, hw]
        exact List.mem_cons_self
      have wA : ScalarWidthsAgree we sA := by
        intro p hp
        apply wm p
        rw [ht]
        show p ∈ (CircuitM.freshName s!"inst_{mc.name}" false
          (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.module.wires
        rw [(CircuitM.freshName_spec _ _ _).2.2,
          (CircuitM.makeWire_spec hint (.bitVector wOut) named sA).2.2.2]
        exact List.mem_cons_of_mem _ hp
      obtain ⟨ws, resA, hlenW, hconns, invA, frA, grA, vals⟩ :=
        instArgs_sem _ vs _ 0 conns _ sA prior pairsLen pairContracts invD wA hArgs
      have specW := CircuitM.makeWire_spec hint (.bitVector wOut) named sA
      have freshA : sA.usedNames.contains r = false := by rw [hw]; exact specW.1
      -- the state just before the instance statement
      have invW : Inv ctx inputs we mems initial
          (CircuitM.makeWire hint (.bitVector wOut) named sA).2 resA :=
        invA.allocate hint (.bitVector wOut) named
      have specN := CircuitM.freshName_spec s!"inst_{mc.name}" false
        (CircuitM.makeWire hint (.bitVector wOut) named sA).2
      have invN : Inv ctx inputs we mems initial
          (CircuitM.freshName s!"inst_{mc.name}" false
            (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2 resA :=
        invW.transfer (LinkCtx.runs_body (by rw [specN.2.2]) invW.runs)
          (LinkCtx.typed_body (by rw [specN.2.2]) invW.typed)
          (CircuitM.freshName_sourceBindings _ _ _) (CircuitM.freshName_translateRecord _ _ _)
          (fun z hz => by rw [specN.2.1]; simp [Std.HashSet.contains_insert, hz])
          (fun _ _ => rfl)
      -- the connection list and the child's evaluation
      have hconnsRev : conns.reverse = (mc.inputs.zip ws).map
          (fun pw => (pw.1.name, Sparkle.IR.AST.Expr.ref pw.2)) := by
        rw [hconns, List.append_nil, List.reverse_reverse]
        exact zip3_map (fun (p : Port) (w : String) => (p.name, Sparkle.IR.AST.Expr.ref w))
          mc.inputs argsE ws hlen
      have hwsLen : ws.length = mc.inputs.length := by
        rw [hlenW]
        simp [hlen]
      have hports : ∀ k (hk : k < mc.inputs.length) (hk' : k < vs.length),
          connEnv (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref r)]) resA
            (mc.inputs[k]'hk).name = (vs[k]'hk').toNat := by
        intro k hk hk'
        have hkW : k < ws.length := by rw [hwsLen]; exact hk
        have hl : (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref r)]).lookup
            (mc.inputs[k]'hk).name = some (.ref (ws[k]'hkW)) := by
          apply lookup_append_left
          rw [hconnsRev]
          exact lookup_zip_ports mc.inputs ws k hk hkW hnodup
        rw [connEnv_at hl]
        exact (vals k hkW hk').1
      obtain ⟨cres, hrunC, houtV⟩ := hcorrect mems
        (connEnv (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref r)]) resA) vs v hsem hports
      have hlookOut : (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref r)]).lookup outName =
          some (.ref r) := by
        have hne : ∀ p ∈ conns.reverse, (outName == p.1) = false := by
          intro p hp
          rw [hconnsRev] at hp
          obtain ⟨pw, hpw, rfl⟩ := List.mem_map.mp hp
          exact houtFresh pw.1 (List.of_mem_zip hpw).1
        rw [lookup_append_right hne]
        simp [List.lookup]
      have hbind : bindOuts mc.outputs
          (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref r)]) cres resA =
          write resA r v.toNat := by
        rw [houts]
        show (match (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref r)]).lookup outName with
          | some (.ref w) => fun n => if n = w then cres outName else resA n
          | _ => resA) = _
        rw [hlookOut, houtV]
        rfl
      have runsI := runs_inst (iname := iname)
        (conns := conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref r)])
        invN.runs hchild hrunC
      rw [hbind] at runsI
      have inputSafe : ∀ id u, inputs id = some u →
          visible ctx (CircuitM.freshName s!"inst_{mc.name}" false
            (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.sourceBindings id ≠
            some r := by
        intro id u hi bound
        rw [CircuitM.freshName_sourceBindings, CircuitM.makeWire_sourceBindings] at bound
        obtain ⟨z, hz, hu, _, _⟩ := invA.inputs.lookup id u hi
        have eq : z = r := Option.some.inj (hz.symm.trans bound)
        rw [eq, freshA] at hu
        cases hu
      have recordSafe : ∀ e u, (CircuitM.freshName s!"inst_{mc.name}" false
            (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.translateRecord.get? r =
            some e → ¬ Meaning inputs e u := by
        intro e u record
        rw [CircuitM.freshName_translateRecord, CircuitM.makeWire_translateRecord] at record
        exact fun meaning => fresh_not_recorded invA.records freshA meaning record
      have invT : Inv ctx inputs we mems initial sm (write resA r v.toNat) := by
        rw [ht]
        exact inv_write_reserved invN inputSafe recordSafe rfl rfl (fun _ hz => hz) runsI
          (HierCtx.typed_inst invN.typed)
      have usedN : ∀ z, sA.usedNames.contains z = true → sm.usedNames.contains z = true := by
        intro z hz
        rw [ht]
        show (CircuitM.freshName s!"inst_{mc.name}" false
          (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.usedNames.contains z = true
        rw [specN.2.1, specW.2.1]
        simp [Std.HashSet.contains_insert, hz]
      refine ⟨?_, ?_, fun z hz => usedN z (grA z hz), write resA r v.toNat, invT,
        by simp [write], ?_⟩
      · rw [ht]
        show (CircuitM.freshName s!"inst_{mc.name}" false
          (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.usedNames.contains r = true
        rw [specN.2.1, specW.2.1, ← hw]
        simp [Std.HashSet.contains_insert]
      · rw [wm _ hdeclT, ← hwidth]
        rfl
      · intro z hz
        have hzA := grA z hz
        have ne : z ≠ r := by
          intro eq
          rw [eq, freshA] at hzA
          cases hzA
        simp only [write, ne, if_false]
        exact frA z hz

/-- The meaning of a canonical instance call: the linked child's source
function of its operands' meanings. -/
theorem meaning_inst {inputs : FVarId → Option Value} {mn : Name} {lvls : List Level}
    {dom : Lean.Expr} {argsE : List Lean.Expr} {vs : List Value} {v : Value}
    (hview : view (instEN mn lvls dom argsE) = none)
    (hlen : argsE.length = vs.length)
    (hargs : ∀ k (hk : k < argsE.length) (hk' : k < vs.length),
      Meaning inputs (argsE[k]'hk) (vs[k]'hk'))
    (hsem : ChildSem.childSem mn vs = some v) :
    Meaning inputs (instEN mn lvls dom argsE) v :=
  .inst hview (instEN_getAppFn mn lvls dom argsE) (instEN_spineArgs mn lvls dom argsE)
    hlen.symm hargs hsem

/-- **The instance leaf at every fuel**: the form the leaf-generic fuel
induction consumes. -/
theorem inst_leaf_fuel {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env}
    {mn : Name} {lvls : List Level} {dom : Lean.Expr} {argsE : List Lean.Expr}
    {vs : List Value} {v : Value} {mc : Sparkle.IR.AST.Module} {dc : Design} {cwe : WEnv}
    {outName : String} {wOut : Nat}
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hctrl : isBoolControl (instEN mn lvls dom argsE) = false)
    (hmux : canonicalMuxType? (instEN mn lvls dom argsE) = none)
    (hsetw : canonicalSetWidth? (instEN mn lvls dom argsE) = none)
    (hreg : canonicalRegister? (instEN mn lvls dom argsE) = none)
    (hregEn : canonicalRegisterEnable? (instEN mn lvls dom argsE) = none)
    (hloopR : canonicalLoopRegister? (instEN mn lvls dom argsE) = none)
    (hcdo : canonicalCircuitDo? (instEN mn lvls dom argsE) = none)
    (hcdo2 : canonicalCircuitDo2? (instEN mn lvls dom argsE) = none)
    (hmem : canonicalMemory? (instEN mn lvls dom argsE) = none)
    (hview : view (instEN mn lvls dom argsE) = none)
    (htag : HardwareTagged mn) (hsub : SubSynthDefinesAll mn mc dc)
    (hdc : dc.modules = [])
    (hnoclk : ∀ p ∈ mc.inputs, (p.name == "clk") = false ∧ (p.name == "rst") = false)
    (hnodup : (mc.inputs.map (·.name)).Nodup)
    (houts : mc.outputs = [⟨outName, .bitVector wOut⟩])
    (houtFresh : ∀ p ∈ mc.inputs, (outName == p.name) = false)
    (hlen : mc.inputs.length = argsE.length) (hlenV : argsE.length = vs.length)
    (hargsM : ∀ k (hk : k < argsE.length) (hk' : k < vs.length),
      Meaning inputs (argsE[k]'hk) (vs[k]'hk'))
    (hargs : ∀ k (hk : k < argsE.length) (hk' : k < vs.length), ∀ fuel,
      Contract (translateFuelFix translateStep fuel) ctx inputs we mems initial
        (argsE[k]'hk) (vs[k]'hk'))
    (hsem : ChildSem.childSem mn vs = some v)
    (hwidth : v.kind.width = wOut)
    (hchild : HierCtx.children mc.name = some (mc, cwe))
    (hcorrect : ChildCorrect mn mc cwe outName) :
    ∀ fuel, Contract (translateFuelFix translateStep fuel) ctx inputs we mems initial
      (instEN mn lvls dom argsE) v
  | 0 => by
    constructor
    · intro hint top named s' t w lookup hr; exact (Returns.throw hr).elim
    · intro hint top named s' t w prior h widths hr; exact (Returns.throw hr).elim
  | fuel + 1 => by
    change Contract (translateStepWith translateFallback (translateFuelFix translateStep fuel))
      _ _ _ _ _ _ _
    exact inst_leaf_contract
      (fun hint top named => instanceN_step _ mn lvls dom argsE hint top named hpure hbin
        hctrl hmux hsetw hreg hregEn hloopR hcdo hcdo2 hmem)
      htag (fun r hr => hsub fuel r hr) hdc hnoclk hnodup houts houtFresh hlen hlenV
      (fun k hk hk' => hargs k hk hk' fuel)
      (meaning_inst hview hlenV hargsM hsem) hsem hwidth hchild hcorrect

end Tools.ShippingInstanceLeaf

import Tools.ShippingGateConeRun

variable {tenv : Lean.Environment}

/-! # The run's child cache HAS the cone's callee (worker N, round 6)

WRITTEN, NOT BUILT.

`gate_cone_runG` concludes the cone guarantee over the child cache `mF` at
the end of the parent's translation; the instance leaf's child facts are
asked of `mF`'s entry of the callee (`InstLeafK`: `∀ y, mF.get? mn = some y
→ …`), so a consumer could only conclude something about EVERY entry found.
Here the entry is shown to EXIST:

* `EntryW L D rec e mn`: every returning run of `rec e …` (any hint, any
  flags) from an invariant world at depth `D` ends in a world whose child
  cache has an entry for `mn`. `EntryWN`: the same for the runs whose
  validated-cache lookup is skipped (`!named && !e.isFVar && !top = false`;
  the parent harness translates its body with `named = true`).
* `inst_entryW`: an instance leaf (a canonical call of a callee designated in
  the translator's environment) — `inst_leaf_runs` makes the run's child THE
  end cache's entry.
* `binary_coreEntry` / `binary_entryWN`: a canonical binary node whose
  operand (either one) has `EntryW` — the operand's end cache is contained in
  the node's end cache (the worlds of `binary_coreW`).
* `cone_harness_runKE` / `gate_cone_runGE`: `cone_harness_runK` /
  `gate_cone_runG` (copies; the old theorems are kept) with one more
  conjunct: every callee whose `EntryWN` holds of the instantiated body (for
  every law witness, positive depth and fresh ids) HAS an entry in `mF`.

A cache hit at an inner node (`cacheLookupValidated` returning a recorded
wire) skips the operand translations, so `EntryWN` is NOT claimed for runs
with the lookup; `binary_entryWN` asks `EntryW` (all flags) of the operand
only, which the instance leaf gives. -/
namespace Tools.ShippingGateParentRun

set_option linter.unusedSectionVars false

section entryLemmas
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingTypedExprSoundness
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingCompareLoweringSoundness Tools.ShippingMuxRecursionSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingBoolMuxSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxTypeSoundness
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedBinarySoundness (Frame ScalarWires)
open Tools.ShippingUnifiedRecursion
open Tools.ShippingLinkCtx
open Tools.ShippingHierarchySoundness
open Tools.ShippingInstanceEntrySoundness (instEN)
open Tools.ShippingChildInv (RefLaws InvV J KeepsC Res RealChild CacheInv childKeeps
  cacheLookupValidated_keepsC recordTranslation_keepsC makeWire_keepsC emitAssign_keepsC)
open Tools.ShippingCacheCoherentRun (SubMap sub_trans sub_refl)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **Every returning run of `rec e …`** (any hint and flags, any compiler and
circuit state) from an invariant world at depth `D` ends in a world whose
child cache has an entry for `mn`. -/
def EntryW (L : RefLaws mref cref) (D : Nat) (rec : TranslateFn) (e : Lean.Expr)
    (mn : Lean.Name) : Prop :=
  ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (hint : String) (top named : Bool)
    (ctx : CompilerState) (s t : CircuitState) (w : String) (w0 w1 : Void IO.RealWorld),
    InvV L w0 → L.dval w0 = D →
    RunsC (rec e hint top named) ctx s mctx mref cctx cref w0 (w, t) w1 →
    ∃ y : Res, (L.val w1).get? mn = some y

/-- `EntryW` for the runs that skip the validated-cache lookup
(`!named && !e.isFVar && !top = false`, e.g. `named = true`). -/
def EntryWN (L : RefLaws mref cref) (D : Nat) (rec : TranslateFn) (e : Lean.Expr)
    (mn : Lean.Name) : Prop :=
  ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (hint : String) (top named : Bool)
    (ctx : CompilerState) (s t : CircuitState) (w : String) (w0 w1 : Void IO.RealWorld),
    (!named && !e.isFVar && !top) = false →
    InvV L w0 → L.dval w0 = D →
    RunsC (rec e hint top named) ctx s mctx mref cctx cref w0 (w, t) w1 →
    ∃ y : Res, (L.val w1).get? mn = some y

/-- **The instance leaf has its callee's entry at the end** (`inst_leaf_runs`). -/
theorem inst_entryW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mn : Lean.Name} {lvls : List Level} {dom : Lean.Expr} {argsE : List Lean.Expr}
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hkind : fallbackKind (instEN mn lvls dom argsE) = .other)
    (htag : Sparkle.Compiler.isHardwareModule tenv mn = true) :
    EntryW L D (translateFuelFix (translateStep tenv) (fuel + 1)) (instEN mn lvls dom argsE) mn := by
  intro mctx cctx hint top named ctx s t w w0 w1 hw hd hr
  obtain ⟨y, -, hget, -⟩ :=
    inst_leaf_runs (tenv := tenv) L hD fuel hpure hbin hkind htag hw hd hr
  exact ⟨y, hget⟩

/-- **The core and the record of a binary node keep an operand's entry**:
the operand's end cache is contained in the node's end cache. -/
theorem binary_coreEntry (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {ctx : CompilerState} {e : Lean.Expr} {m : Lean.Name} {us : List Level} {op : Operator}
    {n : Nat} {mn : Lean.Name} {hint : String} {top named cacheable : Bool}
    {s t : CircuitState} {w : String} {w0 w1 : Void IO.RealWorld}
    {K : Option String → CompilerM String}
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (hent : EntryW L D (translateFuelFix (translateStep tenv) fuel)
        e.getAppArgs[e.getAppArgs.size - 2]! mn ∨
      EntryW L D (translateFuelFix (translateStep tenv) fuel)
        e.getAppArgs[e.getAppArgs.size - 1]! mn)
    (hk : ∀ z, K (some z) = (recordTranslation e z cacheable >>= fun _ => Pure.pure z))
    (hw0 : InvV L w0) (hd0 : L.dval w0 = D)
    (hr : RunsC (translateCore (translateFuelFix (translateStep tenv) fuel) e hint top named >>= K)
      ctx s mctx mref cctx cref w0 (w, t) w1) :
    ∃ y : Res, (L.val w1).get? mn = some y := by
  obtain ⟨r, sm, wc, core, rest⟩ := RunsC.bind hr
  rw [core_binary_eq fn hop kinds width] at core
  obtain ⟨z, sm', wz, lower, back⟩ := RunsC.bind core
  obtain ⟨hp, hwz⟩ := RunsC.pure back
  obtain ⟨hrz, -⟩ := Prod.mk.inj hp
  rw [hrz, hk] at rest
  obtain ⟨u, sr, wr, record, fin⟩ := RunsC.bind rest
  obtain ⟨-, hw1⟩ := RunsC.pure fin
  obtain ⟨sa, sb, sc, a, b, wm, wa, wb, -, -, rmk, ra, rb, remit, -⟩ :=
    binary_returnsW width lower
  -- the worlds: makeWire, operand a, operand b, the assign, the record
  obtain ⟨hwm, hdm, -⟩ :=
    keepsW L (fun L' => makeWire_keepsC L' D hint (.bitVector n) named) hw0 hd0 rmk
  obtain ⟨hwa, hda, -⟩ := fuel_runsW (tenv := tenv) L hD fuel hwm hdm ra
  obtain ⟨hwb, hdb, hsbc⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa hda rb
  obtain ⟨hwc, hdc, hscd⟩ :=
    keepsW L (fun L' => emitAssign_keepsC L' D z (.op op [.ref a, .ref b])) hwb hdb remit
  rw [← hwz] at hwc hdc hscd
  obtain ⟨-, -, hsd⟩ :=
    keepsW L (fun L' => recordTranslation_keepsC L' D e z cacheable) hwc hdc record
  have tail : SubMap (L.val wb) (L.val w1) := by
    rw [hw1]; exact sub_trans hscd hsd
  rcases hent with ha | hb
  · obtain ⟨y, hy⟩ := ha mctx cctx "op_a" false false ctx sa sb a wm wa hwm hdm ra
    exact ⟨y, sub_trans hsbc tail mn y hy⟩
  · obtain ⟨y, hy⟩ := hb mctx cctx "op_b" false false ctx sb sc b wa wb hwa hda rb
    exact ⟨y, tail mn y hy⟩

/-- **A canonical binary node, on the runs that skip the lookup, keeps an
operand's entry.** -/
theorem binary_entryWN (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {e : Lean.Expr} {m : Lean.Name} {us : List Level} {op : Operator} {n : Nat} {mn : Lean.Name}
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (hent : EntryW L D (translateFuelFix (translateStep tenv) fuel)
        e.getAppArgs[e.getAppArgs.size - 2]! mn ∨
      EntryW L D (translateFuelFix (translateStep tenv) fuel)
        e.getAppArgs[e.getAppArgs.size - 1]! mn) :
    EntryWN L D (translateFuelFix (translateStep tenv) (fuel + 1)) e mn := by
  have nf := isFVar_false_of_const fn
  intro mctx cctx hint top named ctx s t w w0 w1 hnc hw0 hd0 hr
  change RunsC (translateStepWith (translateFallback tenv)
    (translateFuelFix (translateStep tenv) fuel) e hint top named) ctx s
    mctx mref cctx cref w0 (w, t) w1 at hr
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · rename_i hc
    first
      | (rw [hnc] at hc; simp at hc)
      | simp [hnc] at hc
      | exact absurd hc (by simp [hnc])
  · exact binary_coreEntry (cacheable := !named && !e.isFVar && !top) L hD fuel fn hop kinds
      width hent (fun z => by simp only [nf, Bool.false_eq_true, if_false]) hw0 hd0 hr

end entryLemmas

/-! ## The harness and the full entry, with the entry conjunct -/

section harness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion
open Tools.ShippingUnifiedEntrySoundness (lookup_of_ports)
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingMixedOutputSoundness (PortInputs declaredWidths declaredWidths_agree)
open Tools.ShippingMixedInputSoundness Tools.ShippingEntrySoundness
open Tools.ShippingCompareLoweringSoundness (ScalarWidthsAgree)
open Tools.ShippingMixedLiteralSoundness (DeclGrows)
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingHierarchySoundness Tools.ShippingLinkCtx
open Tools.ShippingHierTermSoundness (HierValue InstsLinked LeafMeaning initial_link)
open Tools.ShippingMixedInvariant (Separate)
open Tools.ShippingMixedBinarySoundness (Frame)
open Tools.ShippingChildInv (RefLaws InvV Res CacheInv ChildBnd bodyRel profLogIO)
open Tools.ShippingCacheCoherentRun (SubMap sub_refl)
open Tools.ShippingGateDefines (GateDefines)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **`cone_harness_runK` with the entry conjunct** (a copy of its proof;
the old theorem is kept): every callee whose `EntryWN` holds of the body
instantiated at fresh ids has an entry in the cache `L.val wT'` of the cone. -/
theorem cone_harness_runKE (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {b : Bool}
    {declName : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)} {body : Lean.Expr}
    {w : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) declName bs body) mctx mref cctx cref w (m, d) w') :
    ∃ wT' : Void IO.RealWorld, CacheInv mref cref (L.val wT') ∧
      HierConePreservesK tenv (L.val wT') declName bs body m ∧
      ∀ mn : Lean.Name,
        (∀ ids : List FVarId, ids.length = bs.length →
          EntryWN L D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) mn) →
        ∃ y : Res, (L.val wT').get? mn = some y := by
  obtain ⟨ids, cache, wT, wT', wire, sm0, ty, st, nd, len, hwT, hdT, htr, -, hst, -, hm, -⟩ :=
    mixedHarness_runs L hw hd hr
  have entry : ∀ mn : Lean.Name,
      (∀ ids : List FVarId, ids.length = bs.length →
        EntryWN L D (translateFuelFix (translateStep tenv) translateFuelLimit)
          (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) mn) →
      ∃ y : Res, (L.val wT').get? mn = some y :=
    fun mn hE => hE ids len mctx cctx "out" false true _ _ sm0 wire wT wT' rfl hwT hdT htr
  obtain ⟨⟨hcT, -, -⟩, -, -⟩ := fuel_runsW (tenv := tenv) L hD translateFuelLimit hwT hdT htr
  refine ⟨wT', hcT, ⟨ids, nd, len, cache, ?_⟩, entry⟩
  intro children C bools bits initial mems a p values
  obtain ⟨hpc, hps⟩ := prepare_cs bools (fun _ => false) bits (fun _ _ => 0) (bs.zip ids)
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName))
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName)) rfl rfl
  rw [← hpc, ← hps] at htr
  have empty := empty_layout (entryCompilerState false cache)
    (Sparkle.IR.ModuleName.ofDecl declName) initial
  have prepared := prepare_layout (bs.zip ids) a empty.1 empty.2 values
  refine ⟨prepared.1.separate prepared.2.1, ?_⟩
  intro dom kb kv vw bE vE bvals vvals srt e he hf hbM hvM hbK hvK qeq
  letI : HierCtx := hierLink children
  letI : ChildSem := C
  rw [qeq] at htr
  have contract : ContractW L (L.val wT') D
      (translateFuelFix (translateStep tenv) translateFuelLimit)
      p.context (inputValues p.bools p.bits) (declaredWidths st) mems initial
      (quote dom bE vE e) (pack srt (eval bvals vvals e)) :=
    fuel_contractW L hD translateFuelLimit (L.val wT') hbM hvM
      (fun j hj fuel => leafK_contractW L hD (declaredWidths st) (hbK j hj) (hbM j hj) fuel)
      (fun j hj fuel => leafK_contractW L hD (declaredWidths st) (hvK j hj) (hvM j hj) fuel)
      e he hf
  have frame := contract.frame mctx cctx "out" false true p.state sm0 wire wT wT'
    (lookup_of_ports prepared.1 prepared.2.1) hwT hdT (sub_refl _) htr
  obtain ⟨growth, finalWires⟩ := outStructure frame prepared.2.1 hst
  have widths := declaredWidths_agree finalWires
  have inv0 : Inv p.context (inputValues p.bools p.bits) (declaredWidths st) mems initial
      p.state initial :=
    initial_link prepared.2.2.1 prepared.2.2.2 (prepared.1.inputs prepared.2.1 growth widths)
  have wsm : ScalarWidthsAgree (declaredWidths st) sm0 := by
    intro q hq; apply widths q; rw [hst, emitAssign_wires]; exact hq
  have step := contract.sem mctx cctx "out" false true p.state sm0 wire initial wT wT'
    inv0 wsm hwT hdT (sub_refl _) htr
  obtain ⟨result, evalr, value, typedSm⟩ := outRuns step hst
  have wireEq : m.wires = st.module.wires.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
  have bodyEq : m.body = st.module.finalize.body := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).1]
  refine ⟨⟨result, ?_, value⟩, ?_⟩
  · rw [moduleWidths_finish wireEq finalWires, bodyEq]
    exact evalr
  · intro mn iname conns hmem
    have hmem' : Stmt.inst mn iname conns ∈ st.module.body := by
      rw [bodyEq] at hmem
      exact List.mem_reverse.mp hmem
    rw [hst, emitAssign_body_cons] at hmem'
    rcases List.mem_cons.mp hmem' with hbad | hmem'
    · cases hbad
    · obtain ⟨child, cwe, hc, hl⟩ := HierCtx.typed_linked typedSm hmem'
      refine ⟨child, cwe, hc, hl.mono ?_ ?_⟩
      · intro q hq
        rw [wireEq, List.mem_reverse, hst, emitAssign_wires]
        exact hq
      · intro q hq
        rw [hm]
        show q ∈ (addClockResetIfSequential st.module).inputs.reverse
        rw [List.mem_reverse]
        exact (addClockReset_facts st.module).2.2.2 q (by rw [hst]; exact hq)

/-- **`gate_cone_runG` with the entry conjunct** (a copy of its proof; the
old theorem is kept): every callee whose `EntryWN` holds of the instantiated
body — for every law witness, every positive depth and every list of fresh
ids — HAS an entry in the cone's child cache `mF`. -/
theorem gate_cone_runGE {f : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
    {body : Lean.Expr} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module}
    {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref f bs body)
    (bnd : ChildBnd mref cref w) :
    ∃ (M : Sparkle.IR.AST.Module) (Dd : Sparkle.IR.AST.Design) (envR : Lean.Environment)
      (a5 a6 : Void IO.RealWorld) (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      b.name = M.name ∧
      ((∀ x ∈ Dd.modules, x.name ≠ M.name) → design.modules = Dd.modules) ∧
      RunsTo (Lean.getEnv : Lean.Meta.MetaM Lean.Environment) mctx mref cctx cref a5 envR a6 ∧
      (∃ dv : Lean.DefinitionVal, mixedCertifiedShape? false [] (.defnInfo dv)
        (Sparkle.Compiler.Elab.instancePredicate envR) = some (bs, body)) ∧
      CacheInv mref cref mF ∧ HierConePreservesK envR mF f bs body M ∧
      ∀ mn : Lean.Name,
        (∀ (L' : RefLaws mref cref) (D : Nat), D ≠ 0 → ∀ ids : List FVarId,
          ids.length = bs.length →
          EntryWN L' D (translateFuelFix (translateStep envR) translateFuelLimit)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) mn) →
        ∃ y : Res, mF.get? mn = some y := by
  obtain ⟨L, ⟨hsv, hdep⟩, hq⟩ := bnd
  obtain ⟨M, Dd, w1, hcore, hpost⟩ :=
    Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨M2, D2, w2, hcore2, -, hname, hmods⟩ := Tools.ShippingCacheCoherentRun.full_split L hr
  obtain ⟨hMD, -⟩ := runsTo_det hcore2 hcore
  obtain ⟨hM, hD⟩ := Prod.mk.inj hMD
  rw [hM] at hname
  rw [hM, hD] at hmods
  have hreads : ∃ (bb : Bool) (envR : Lean.Environment) (ci : Lean.ConstantInfo)
      (a1 a2 a3 a4 a5 a6 : Void IO.RealWorld),
      RunsTo (Lean.getConstInfo f) mctx mref cctx cref a1 ci a2 ∧
      RunsTo (Lean.getEnv : Lean.Meta.MetaM Lean.Environment) mctx mref cctx cref a5 envR a6 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n)
        (profLogIO bb) f [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref a3 (M, Dd) a4 ∧ InvV L a3 ∧ L.dval a3 ≠ 0 := by
    by_cases h0 : L.dval w = 0
    · obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3, -, -, -⟩ :=
        Tools.ShippingCacheCoherentOuter.core_reads_val0 L (fun L' => bodyRel L') hsv hq h0 hcore
      exact ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩
    · rcases hdep with hz | hci
      · exact absurd hz h0
      · obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3, -, -, -⟩ :=
          Tools.ShippingCacheCoherentVia.core_reads_val L (fun L' => bodyRel L')
            ⟨hci, hsv, hq⟩ h0 hcore
        exact ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩
  obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩ := hreads
  -- the reflection at the run's own reads
  obtain ⟨dv, hdv, hold, hshape⟩ := gdef a1 ci a2 a5 envR a6 hget henv
  rw [hdv] at run
  obtain ⟨wa, wb, hwa, hda, hharn⟩ := sfc_mixed_run L hold hshape hw3 run
  have hDa : L.dval wa ≠ 0 := by rw [hda]; exact hd3
  obtain ⟨wT', hcache, hcone, hentry⟩ :=
    cone_harness_runKE (tenv := envR) L (D := L.dval wa) hDa hwa rfl hharn
  exact ⟨M, Dd, envR, a5, a6, L.val wT', hpost, hname, hmods, henv, ⟨dv, hshape⟩, hcache, hcone,
    fun mn hE => hentry mn (fun ids len => hE L (L.dval wa) hDa ids len)⟩

end harness

end Tools.ShippingGateParentRun

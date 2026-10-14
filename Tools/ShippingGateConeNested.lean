import Tools.ShippingGateConeInstArgsW
import Tools.ShippingGateConeEntry

variable {tenv : Lean.Environment}

/-! # Cones whose instance leaves take instance calls as arguments (worker N, round 9)

WRITTEN, NOT BUILT.

`LeafK` / `InstLeafK` (round 3) ask WORLD-FREE contracts of an instance
leaf's arguments, which an instance call does not have. Here:

* `LeafKR` — the leaves of a cone, RECURSIVELY: a world-free leaf contract
  (an input binder, …) or a canonical call of a callee designated in `tenv`
  whose arguments are themselves `LeafKR`s (with their meanings), whose
  child semantics on the argument values is the value, and whose `mF` entry
  has the child facts at that value. (`childAdd (childAdd a b) b`: the outer
  call's first argument is the inner call.) Every `LeafK` gives a `LeafKR`
  (`leafKR_of_leafK`).
* `leafKR_contractW` — a `LeafKR` leaf has a world-indexed contract at every
  fuel (induction on `LeafKR`; the instance case is `inst_leaf_contractWA`).
* `HierConePreservesKR` — `HierConePreservesK` with `LeafKR` leaves;
  `cone_harness_runKER` / `gate_cone_runGER` — copies of
  `cone_harness_runKE` / `gate_cone_runGE` over it (the old theorems are
  kept; only the leaf lemma differs). Premises of `gate_cone_runGER`: the run,
  `GateDefines` (NOT in the classifier's ALLOWED list, ruling pending),
  `ChildBnd` — unchanged.

The cache, precisely: `mF` has ONE entry per callee name. Every call of the
same callee in the run (the inner and the outer `childAdd`) instantiates that
one pair `y` (`inst_leaf_runsW`: each call's child is THE end cache's entry,
and entries are kept up to `mF`). A `LeafKR` asks, at each call, the child
facts of `y` at THAT call's value (`KidFacts children C mn n v y`): one
`KidFacts` per call, all of the same pair. Nothing is asked of the
instance-arm dedupe cache (both of its outcomes are covered). -/
namespace Tools.ShippingGateParentRun

set_option linter.unusedSectionVars false

section leaves
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingUnifiedRecursion
open Tools.ShippingLinkCtx
open Tools.ShippingHierarchySoundness
open Tools.ShippingInstanceEntrySoundness (instEN)
open Tools.ShippingChildInv (RefLaws InvV Res)
open Tools.ShippingCacheCoherentRun (SubMap)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **The leaves of a cone, recursively** (file header): a world-free leaf
contract, or a canonical call whose arguments are again `LeafKR`s. -/
inductive LeafKR (tenv : Lean.Environment)
    (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (C : ChildSem) (mF : Std.HashMap Lean.Name Res) (ctx : CompilerState)
    (inputs : FVarId → Option Value) (mems : MEnv) (initial : Env) :
    Lean.Expr → Value → Prop
  | leaf {e : Lean.Expr} {v : Value} :
      Tools.ShippingHierTermSoundness.LeafContract tenv children C ctx inputs mems initial e v →
      LeafKR tenv children C mF ctx inputs mems initial e v
  | inst {mn : Lean.Name} {lvls : List Level} {dom : Lean.Expr} {argsE : List Lean.Expr}
      {vs : List Value} {v : Value} :
      (mn == ``Sparkle.Core.Signal.Signal.pure) = false →
      signalBinOpOf mn = none →
      fallbackKind (instEN mn lvls dom argsE) = .other →
      Sparkle.Compiler.isHardwareModule tenv mn = true →
      argsE.length = vs.length →
      (∀ k (hk : k < argsE.length) (hk' : k < vs.length),
        LeafKR tenv children C mF ctx inputs mems initial (argsE[k]'hk) (vs[k]'hk')) →
      (∀ k (hk : k < argsE.length) (hk' : k < vs.length),
        Tools.ShippingHierTermSoundness.LeafMeaning C inputs (argsE[k]'hk) (vs[k]'hk')) →
      @ChildSem.childSem C mn vs = some v →
      (∀ y : Res, mF.get? mn = some y → KidFacts children C mn argsE.length v y) →
      LeafKR tenv children C mF ctx inputs mems initial (instEN mn lvls dom argsE) v

/-- Every `LeafK` is a `LeafKR` (a world-free argument contract is a `leaf`). -/
theorem leafKR_of_leafK {children : String → Option (Sparkle.IR.AST.Module × WEnv)}
    {C : ChildSem} {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {mems : MEnv} {initial : Env} {e : Lean.Expr} {v : Value}
    (h : LeafK tenv children C mF ctx inputs mems initial e v)
    (hm : ∀ (mn : Lean.Name) (lvls : List Level) (dom : Lean.Expr) (argsE : List Lean.Expr)
      (vs : List Value), e = instEN mn lvls dom argsE → argsE.length = vs.length →
      ∀ k (hk : k < argsE.length) (hk' : k < vs.length),
        Tools.ShippingHierTermSoundness.LeafMeaning C inputs (argsE[k]'hk) (vs[k]'hk')) :
    LeafKR tenv children C mF ctx inputs mems initial e v := by
  rcases h with hc | ⟨mn, lvls, dom, argsE, vs, he, hpure, hbin, hkind, htag, hlenV, hargs, hsem,
    hkid⟩
  · exact .leaf hc
  · have hmA := hm mn lvls dom argsE vs he hlenV
    subst he
    exact .inst hpure hbin hkind htag hlenV (fun k hk hk' => .leaf (hargs k hk hk')) hmA hsem hkid

/-- **A `LeafKR` leaf has a world-indexed contract at every fuel**, in the
linked context of `children`. -/
theorem leafKR_contractW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (we : WEnv)
    {children : String → Option (Sparkle.IR.AST.Module × WEnv)} {C : ChildSem}
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {inputs : FVarId → Option Value}
    {mems : MEnv} {initial : Env} :
    ∀ {e : Lean.Expr} {v : Value}, LeafKR tenv children C mF ctx inputs mems initial e v →
    Tools.ShippingHierTermSoundness.LeafMeaning C inputs e v → ∀ fuel : Nat,
    letI : HierCtx := hierLink children
    letI : ChildSem := C
    ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial e v := by
  letI : HierCtx := hierLink children
  letI : ChildSem := C
  intro e v h
  induction h with
  | leaf hc =>
    intro _ fuel
    exact ContractW.ofContract (hc we fuel)
  | inst hpure hbin hkind htag hlenV hargs hargsM hsem hkid ih =>
    intro hm fuel
    cases fuel with
    | zero => exact ContractW.zero
    | succ fuel =>
      exact inst_leaf_contractWA L hD fuel hpure hbin hkind htag hlenV
        (fun k hk hk' => ih k hk hk' (hargsM k hk hk') fuel) hm hsem hkid

end leaves

/-! ## The cone result over `LeafKR` leaves, and the harness / full entry -/

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

/-- **`HierConePreservesK` with `LeafKR` leaves** (instance leaves may take
instance calls as arguments). -/
def HierConePreservesKR (tenv : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
    (declName : Lean.Name) (bs : List (Lean.Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (Lean.ExprStructMap String),
    ∀ (children : String → Option (Sparkle.IR.AST.Module × WEnv)) (C : ChildSem)
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (initial : Env) (mems : MEnv),
    let a := start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName)
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits initial (bs.zip ids) a →
    Separate p.bools p.bits ∧
    ∀ (dom : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (bE vE : Nat → Lean.Expr)
      (bvals : Nat → Bool) (vvals : (j : Nat) → (w : Nat) → BitVec w)
      {srt : SType} (e : Term srt),
    e.WF kb kv vw → cfrag e = true →
    (∀ j, j < kb → LeafMeaning C (inputValues p.bools p.bits) (bE j) (.bool (bvals j))) →
    (∀ j, j < kv → LeafMeaning C (inputValues p.bools p.bits) (vE j)
      (.bits (vw j) (vvals j (vw j)))) →
    (∀ j, j < kb → LeafKR tenv children C mF p.context (inputValues p.bools p.bits)
      mems initial (bE j) (.bool (bvals j))) →
    (∀ j, j < kv → LeafKR tenv children C mF p.context (inputValues p.bools p.bits)
      mems initial (vE j) (.bits (vw j) (vvals j (vw j)))) →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body = quote dom bE vE e →
    HierValue children m initial mems (pack srt (eval bvals vvals e)).toNat ∧
      InstsLinked children m

/-- **`cone_harness_runKE` over `LeafKR` leaves** (a copy of its proof; only
the leaf lemma is `leafKR_contractW`). -/
theorem cone_harness_runKER (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {b : Bool}
    {declName : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)} {body : Lean.Expr}
    {w : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) declName bs body) mctx mref cctx cref w (m, d) w') :
    ∃ wT' : Void IO.RealWorld, CacheInv mref cref (L.val wT') ∧
      HierConePreservesKR tenv (L.val wT') declName bs body m ∧
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
      (fun j hj fuel => leafKR_contractW L hD (declaredWidths st) (hbK j hj) (hbM j hj) fuel)
      (fun j hj fuel => leafKR_contractW L hD (declaredWidths st) (hvK j hj) (hvM j hj) fuel)
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

/-- **`gate_cone_runGE` over `LeafKR` leaves** (a copy of its proof; the
harness lemma is `cone_harness_runKER`). Premises unchanged: the run,
`GateDefines` (NOT ALLOWED, ruling pending), `ChildBnd`. -/
theorem gate_cone_runGER {f : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
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
      CacheInv mref cref mF ∧ HierConePreservesKR envR mF f bs body M ∧
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
    cone_harness_runKER (tenv := envR) L (D := L.dval wa) hDa hwa rfl hharn
  exact ⟨M, Dd, envR, a5, a6, L.val wT', hpost, hname, hmods, henv, ⟨dv, hshape⟩, hcache, hcone,
    fun mn hE => hentry mn (fun ids len => hE L (L.dval wa) hDa ids len)⟩

end harness

end Tools.ShippingGateParentRun

import Tools.ShippingChildDepthA
import Tools.ShippingChildCoreC
import Tools.ShippingChildFrontA
-- UNBUILT (unit F, round 2): see the run log in REPORT-F.md for the build names and exits.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field. Law witness: ONE
-- `O : RefLawsAOps MkRefd mref cref` at `hA : AdmCtx O.quiet mctx cctx`; `RefLawsATele` only where
-- the handler `projFieldName?` needs it (unit C's export), as a separate named hypothesis `T`.
-- No `RefLaws` / `RefLawsCore` / `ChildBnd` here. Imports only BUILT modules.

/-! # The composed child/cache theorems, against the INTERFACES.md exports (unit F)

Every export of units A, B, C, D, E that is not built yet enters as a HYPOTHESIS of exactly its
agreed statement (a named parameter), so the integrator plugs the proof in. What is PROVED here is
the composition:

* `bodyStepA_of_exports` (A + B + C + D): the remaining lemma `BodyStepA O` of DepthA from the
  per-handler exports, instantiated at every `JQ O.quiet D`.
* `core_tripleA_of_exports`: the core entry keeps `OutQ` (DepthA `core_tripleA_of_bodies`).
* `hbodyC_of_exports` (A + B + C + D-generic + E): the cache-half body lemma `hbodyC` of CoreC at
  `I := JQC O (D+1)`: the translator at `JQC` is built from the handler exports at THAT invariant
  (`translate_keepsA`), the front ends from D's generic lemma, the child entry from E's output.
* `entry_children_of_exports`: from `hbodyC`, the full entry keeps `JQC` and the closing's
  children are `RealChildA` (CoreC), at every depth.
* `fullEntry_realA_of_exports`: the outermost statement: a start world that is `OutQ` with an
  empty cache, one run of `synthesizeCombinational`, ends in `JQC O 0`.

PREMISES (named, one per owner export) are listed in docs/parallel/main-theorem-connection.md §3.
Nothing here connects to the OLD `ChildBnd` endpoint (`machine_design_closed`): that link has no
proof (docs §2). `RealChildA` is a history of past synthesis results, NOT semantic correctness in
the current environment; `MkRefd` is a history, NOT freshness. -/

namespace Tools.ShippingChildMainA
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildVertA
open Tools.ShippingChildCacheA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildFallbackA
open Tools.ShippingChildDepthA
open Tools.ShippingChildCoreC

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## The handler exports (A, B, C) at an invariant -/

/-- The four handler premises other than `LegacyImplA`, from the exports of A and C, at a stable
`I`, given `LegacyImplA O I` (B's output). Composition of three owners' exports. -/
theorem handlers_of_exports (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref)
    -- A: `legacyCachedA_of_impl (O) (hS) : LegacyImplA O I → LegacyCachedA O I`
    (hA_cached : ∀ {I : Void IO.RealWorld → Prop}, StableA O.quiet I →
      LegacyImplA O I → LegacyCachedA O I)
    -- A: `canonKeyA (O) (hS) : CanonKeyA O I`
    (hA_canon : ∀ {I : Void IO.RealWorld → Prop}, StableA O.quiet I → CanonKeyA O I)
    -- C: `projFieldNameA (O) (T) (hS) : ProjFieldNameA O I`
    (hC_pf : ∀ {I : Void IO.RealWorld → Prop}, RefLawsATele O.quiet mref cref →
      StableA O.quiet I → ProjFieldNameA O I)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) (hImpl : LegacyImplA O I) :
    LegacyCachedA O I ∧ CanonKeyA O I ∧ ProjFieldNameA O I :=
  ⟨hA_cached hS hImpl, hA_canon hS, hC_pf T hS⟩

/-! ## The `JQ` route: `BodyStepA` and the core entry -/

/-- **`BodyStepA O` from the exports of A, B, C, D.**
* `H`: unit B's per-handler premises `H₁A O I … HₖA O I`, conjoined as ONE predicate of `I` only
  so this statement does not depend on B's count `k`; `hB` is B's
  `legacyImplA_of_handlers (O) (hS) (h₁ …) … : LegacyImplA O I` read at that conjunction. The
  premises stay individually owned and named in the audit (docs §3); `hH` asks them at every
  `JQ O.quiet D`.
* `Lg`: unit D's legacy-tail premise (`hlegacy`), stated by D.
* `hD`: D's `bodyStepA_of_handlers (O) (hImpl : ∀ D, LegacyImplA O (JQ O.quiet D))
  (hCached …) (hcanon …) (hpf …) (hlegacy …) : BodyStepA O`. -/
theorem bodyStepA_of_exports (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref)
    (H : (Void IO.RealWorld → Prop) → Prop)
    (hB : ∀ {I : Void IO.RealWorld → Prop}, StableA O.quiet I → H I → LegacyImplA O I)
    (hA_cached : ∀ {I : Void IO.RealWorld → Prop}, StableA O.quiet I →
      LegacyImplA O I → LegacyCachedA O I)
    (hA_canon : ∀ {I : Void IO.RealWorld → Prop}, StableA O.quiet I → CanonKeyA O I)
    (hC_pf : ∀ {I : Void IO.RealWorld → Prop}, RefLawsATele O.quiet mref cref →
      StableA O.quiet I → ProjFieldNameA O I)
    (Lg : Prop)
    (hD : (∀ D, LegacyImplA O (JQ O.quiet D)) → (∀ D, LegacyCachedA O (JQ O.quiet D)) →
      (∀ D, CanonKeyA O (JQ O.quiet D)) → (∀ D, ProjFieldNameA O (JQ O.quiet D)) → Lg →
      BodyStepA O)
    (hH : ∀ D, H (JQ O.quiet D)) (hLg : Lg) : BodyStepA O := by
  have hImpl : ∀ D, LegacyImplA O (JQ O.quiet D) := fun D => hB (stableA_JQ _ D) (hH D)
  exact hD hImpl
    (fun D => (handlers_of_exports O T hA_cached hA_canon hC_pf (stableA_JQ _ D) (hImpl D)).1)
    (fun D => (handlers_of_exports O T hA_cached hA_canon hC_pf (stableA_JQ _ D) (hImpl D)).2.1)
    (fun D => (handlers_of_exports O T hA_cached hA_canon hC_pf (stableA_JQ _ D) (hImpl D)).2.2)
    hLg

/-- **The core entry keeps `OutQ` on every outcome, from the exports** (A + B + C + D + the
built depth induction). -/
theorem core_tripleA_of_exports (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (declName : Name)
    (T : RefLawsATele O.quiet mref cref)
    (H : (Void IO.RealWorld → Prop) → Prop)
    (hB : ∀ {I : Void IO.RealWorld → Prop}, StableA O.quiet I → H I → LegacyImplA O I)
    (hA_cached : ∀ {I : Void IO.RealWorld → Prop}, StableA O.quiet I →
      LegacyImplA O I → LegacyCachedA O I)
    (hA_canon : ∀ {I : Void IO.RealWorld → Prop}, StableA O.quiet I → CanonKeyA O I)
    (hC_pf : ∀ {I : Void IO.RealWorld → Prop}, RefLawsATele O.quiet mref cref →
      StableA O.quiet I → ProjFieldNameA O I)
    (Lg : Prop)
    (hD : (∀ D, LegacyImplA O (JQ O.quiet D)) → (∀ D, LegacyCachedA O (JQ O.quiet D)) →
      (∀ D, CanonKeyA O (JQ O.quiet D)) → (∀ D, ProjFieldNameA O (JQ O.quiet D)) → Lg →
      BodyStepA O)
    (hH : ∀ D, H (JQ O.quiet D)) (hLg : Lg) :
    Triple mctx mref cctx cref (OutQ O.quiet) (synthesizeCombinationalCore declName [] false)
      (fun _ => OutQ O.quiet) (fun e w => OutQ O.quiet w ∧ OkExc e) :=
  core_tripleA_of_bodies O hA declName
    (bodyStepA_of_exports O T H hB hA_cached hA_canon hC_pf Lg hD hH hLg)

/-! ## The `JQC` route: `hbodyC`, the full entry, the children -/

/-- **`hbodyC` of CoreC at depth `D`, from the exports** (A + B + C at `I := JQC O (D+1)`, D's
generic front-end lemma, E's child entry).
* `hD_gen`: D's `fromConst_frontends_keepsCP (O) (hA) (hS) (translate) (htr : RecA O I translate)
  (hchild : ChildSynthA O I) (hsv : ∀ w, I w → sv w = some synthesizeChild) … (hlegacy) : Keeps …
  I (synthesizeFromConst translate …)`, generic in a stable `I` (read from par/u-d 5434407f: it
  adds `hsv` and the separate `ChildSynthA` to INTERFACES.md's statement — drift, see REPORT).
* `hE_synth`: the machine branch's own `synthesizeChild` calls keep `JQC O D` (`ChildKeepsC`
  unfolded) — E's output, assumed here by its content;
* `hE_child`: E's `childEntryA_of_childKeepsC (childKeepsC_all hBS …)` at `D+1 ≥ 1`, i.e.
  `ChildEntryA O (JQC O (D+1))`, from E's `BodyStepC O` (`BS`); `hBS : BS` is E's
  `bodyStepC_of_generic hD_gen …`.
* `hleg`: the legacy tail at `JQC O (D+1)` (D's premise, as stated by FrontA). -/
theorem hbodyC_of_exports (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref)
    (H : (Void IO.RealWorld → Prop) → Prop)
    (hB : ∀ {I : Void IO.RealWorld → Prop}, StableA O.quiet I → H I → LegacyImplA O I)
    (hA_cached : ∀ {I : Void IO.RealWorld → Prop}, StableA O.quiet I →
      LegacyImplA O I → LegacyCachedA O I)
    (hA_canon : ∀ {I : Void IO.RealWorld → Prop}, StableA O.quiet I → CanonKeyA O I)
    (hC_pf : ∀ {I : Void IO.RealWorld → Prop}, RefLawsATele O.quiet mref cref →
      StableA O.quiet I → ProjFieldNameA O I)
    (hD_gen : ∀ {I : Void IO.RealWorld → Prop}, StableA O.quiet I →
      ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ (translate : TranslateFn) (b : Bool) (declName : Name) (ci : ConstantInfo)
        (isInst : Lean.Expr → Bool),
      RecA O I translate →
      (∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
        ∀ c, Keeps mctx mref cctx cref I (synthesizeChild c)) →
      (∀ w, I w → sv w = some synthesizeChild) →
      (certifiedShape? false [] ci = none → mixedCertifiedShape? false [] ci isInst = none →
        Keeps mctx mref cctx cref I
          (synthesizeFromConst translate (profLogIO b) declName [] false false ci isInst)) →
      Keeps mctx mref cctx cref I
        (synthesizeFromConst translate (profLogIO b) declName [] false true ci isInst))
    (BS : Prop)
    (hE_child : BS → ∀ D, 1 ≤ D → ChildEntryA O (JQC O D)) (hBS : BS)
    (hE_synth : BS → ∀ D, 1 ≤ D → ∀ (mctx : Meta.Context) (cctx : Core.Context),
      AdmCtx O.quiet mctx cctx → ∀ c, Keeps mctx mref cctx cref (JQC O D) (synthesizeChild c))
    (hH : ∀ D, H (JQC O D))
    (hleg : ∀ (D : Nat) (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
      ∀ (tenv : Lean.Environment) (b : Bool) (declName : Name) (ci : ConstantInfo)
        (isInst : Lean.Expr → Bool),
      certifiedShape? false [] ci = none → mixedCertifiedShape? false [] ci isInst = none →
      Keeps mctx mref cctx cref (JQC O D)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false false ci isInst))
    (D : Nat) (declName : Name) (hA : AdmCtx O.quiet mctx cctx) :
    ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQC O (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst) := by
  intro tenv _ b ci isInst
  have hS := stableA_JQC O (D + 1)
  have hImpl := hB hS (hH (D + 1))
  obtain ⟨hCached, hCanon, hPf⟩ := handlers_of_exports O T hA_cached hA_canon hC_pf hS hImpl
  have hchild : ChildEntryA O (JQC O (D + 1)) := hE_child hBS (D + 1) (Nat.succ_le_succ (Nat.zero_le D))
  exact hD_gen hS mctx cctx hA _ b declName ci isInst
    (translate_keepsA O hS tenv hImpl hCached hCanon hPf hchild)
    (hE_synth hBS (D + 1) (Nat.succ_le_succ (Nat.zero_le D))) (fun _ h => h.1.2.1)
    (hleg (D + 1) mctx cctx hA tenv b declName ci isInst)

/-- **The full entry keeps `JQC`, and the closing's children are `RealChildA`, at depth `D`**,
from `hbodyC` at every callee/declaration (the output of `hbodyC_of_exports`). Composition of
CoreC's `hentry_of_body` and `closeInstsM_realA'`. -/
theorem entry_children_of_exports (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat}
    (hbodyC : ∀ (c : Name) {tenv : Lean.Environment}, D < sparkleSynthDepthLimit →
      ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQC O (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          c [] false true ci isInst))
    {w : Void IO.RealWorld} (hw : JQC O D w) :
    (∀ (c : Name) {r : Res} {w' : Void IO.RealWorld},
      RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' → JQC O D w') ∧
    (∀ {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
      {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w' : Void IO.RealWorld},
      RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w' →
      ∃ children, Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
          shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
          children (m₀, d₀) = some (m, d) ∧
        children.length = shape.insts.length ∧
        (∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
          RealChildA O (shape.insts[k]).1 y) ∧
        JQC O D w') :=
  ⟨fun c _ _ hr => hentry_of_body O hA (hbodyC c) w _ _ hw hr,
   fun hr => closeInstsM_realA' O hA hbodyC hw hr⟩

/-- The outermost start: an `OutQ` world with an empty cache is a `JQC O 0` world. -/
theorem jqc_zero_of_empty (O : RefLawsAOps MkRefd mref cref) {w : Void IO.RealWorld}
    (hq : OutQ O.quiet w) (hc : cv w = {}) : JQC O 0 w :=
  ⟨(outQ_iff_JQ _ w).mp hq, by rw [hc]; exact cacheInvA_empty O⟩

/-- **The outermost statement of the child/cache work.** From a start world that is `OutQ` with
an empty cache, one run of the full entry `synthesizeCombinational c` in an admissible context
ends in `JQC O 0`, so (by `RealChildA.of_jqc`) every later cache read returns `RealChildA`s only.
`hbodyC` at depth 0 comes from `hbodyC_of_exports`. -/
theorem fullEntry_jqc_of_exports (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {c : Name}
    (hbodyC : ∀ {tenv : Lean.Environment}, 0 < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQC O 1)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          c [] false true ci isInst))
    {w w' : Void IO.RealWorld} {r : Res} (hq : OutQ O.quiet w) (hc : cv w = {})
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') : JQC O 0 w' :=
  hentry_of_body O hA @hbodyC w r w' (jqc_zero_of_empty O hq hc) hr

end Tools.ShippingChildMainA

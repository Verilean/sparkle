import Tools.ShippingHarnessStill

variable {tenv : Lean.Environment}

/-! # The walk leaves the child cache on EVERY constructor of the term language

`Tools.ShippingWalkStill.walk_still` covers the ten constructors of `wfrag`.
This file adds the eleven left out — `boolLit`, `bitsNum`, `boolNot`,
`slice`, `sliceF`, `zextMap`, `concatLitHi`, `concatLitLo`, `appCompare`,
`appBool`, `appBool2` — each by the lemma its built contract
(`Tools.ShippingUnifiedRecursion.fuel_contract_leaves`) rewrites the step
with, and the operations already walked in `WHo`:

* one new step lemma, `step_of_none`: a step whose core answers `none` is the
  fallback (after the validated lookup) — the Bool literal's step, which the
  built contract unfolds by hand;
* `emitSlice_S`, `concatActs_S`, `emitConcatConst_S`: the three emitters not
  walked before (a wire, an assign; the two operand actions in between);
* one `…_still` lemma per constructor;
* `fuel_still_all`, **`walk_still_all`**: for a well-formed term — NO
  fragment condition is left — a returning run of the shipping translator on
  its quotation, in a context binding the inputs, leaves the child cache.

None of the eleven arms reaches a continuation that can touch the child
cache: every one is `rec` on the operands and wire / assign emissions. The
legacy hand-over (`translateBoolUncachedWith`'s `legacy` argument, the
`.other` arm of the fallback) is not taken by any constructor of `Term`:
each step lemma rewrites the step to a named certified arm. So nothing is
left out.

`wfragAll` is therefore the constant `true`; it is kept as a name so that a
measurement can print it next to `wfrag`.

The consumers: `Tools.ShippingHarnessStill.entryStill_leaf` takes
`HarnessStill` as a hypothesis and is reused as it is.
`harnessStill_frag` and `entryStill_gate` call `walk_still` with
`wfrag e = true` and are NOT parametric in the fragment: they are re-derived
here over all terms (`harnessStill_all`, `entryStill_gate_all`) — the text
of the built proofs with the one call replaced; the built files are not
edited.

WRITTEN, NOT BUILT (par/a-41). -/
namespace Tools.ShippingWalkStillMore
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
open Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedRecursion (boolNot_step)
open Tools.ShippingUnifiedRecursion (slice_step sliceUncached_sliceE zextMap_step
  setwUncached_zextMapE sliceF_step sliceFUncached_sliceFE concatLitHi_step
  concatLitUncached_hiE concatLitLo_step concatLitUncached_loE appCompare_step appBool_step
  appBool2_step isBoolControl_appCompareE isBoolControl_appBoolE isBoolControl_appBool2E
  translateBoolUncachedWith_appCompare translateBoolUncachedWith_appBool
  translateBoolUncachedWith_appBool2)
open Tools.ShippingChildInv Tools.ShippingWalkStill

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

variable (L : RefLaws mref cref) {mb : Std.HashMap Lean.Name Res} {ctx : CompilerState}

/-- Every term: the walk needs no fragment condition. -/
def wfragAll {s : SType} (_ : Term s) : Bool := true

/-! ## The emitters not walked before -/

theorem emitSlice_S (rhs : Sparkle.IR.AST.Expr) (len : Nat) (hint : String) (named : Bool) :
    WSt mctx cctx L mb ctx (emitSliceResult rhs len hint named) := by
  unfold emitSliceResult
  refine WHo.bind L (makeWire_S L _ _ _) ?_
  intro w _
  refine WHo.bind L (emitAssign_S L _ _) ?_
  intro _ _
  exact WHo.pure L _ (Q := fun _ => True) trivial

/-- The concatenation's actions: the result wire, the two operand actions,
one assign. -/
theorem concatActs_S {wd : Nat} {hiAct loAct : CompilerM String} {hint : String} {named : Bool}
    (hh : WSt mctx cctx L mb ctx hiAct) (hl : WSt mctx cctx L mb ctx loAct) :
    WSt mctx cctx L mb ctx (translateConcatActs wd hiAct loAct hint named) := by
  unfold translateConcatActs
  refine WHo.bind L (makeWire_S L _ _ _) ?_
  intro r _
  refine WHo.bind L hh ?_
  intro hi _
  refine WHo.bind L hl ?_
  intro lo _
  refine WHo.bind L (emitAssign_S L _ _) ?_
  intro _ _
  exact WHo.pure L _ (Q := fun _ => True) trivial

theorem emitConcatConst_S (k v : Nat) :
    WSt mctx cctx L mb ctx (emitConcatConst k v) := by
  unfold emitConcatConst
  exact emitCast_S L _ _ _ _

/-! ## A step whose core answers `none` -/

variable {rec : TranslateFn}

/-- **One step whose core is `pure none`**: the validated lookup (when the
node is cacheable), then the fallback. -/
theorem step_of_none {fb : TranslateFn → TranslateFn} {e : Lean.Expr} {hint : String}
    {top named : Bool}
    (hcore : translateCore rec e hint top named = Pure.pure none)
    (hfb : WSt mctx cctx L mb ctx (fb rec e hint top named)) :
    WSt mctx cctx L mb ctx (translateStepWith fb rec e hint top named) := by
  have core : WHo mctx cctx L mb ctx (translateCore rec e hint top named) (fun r => r = none) := by
    rw [hcore]
    exact WHo.pure L none (Q := fun r => r = none) rfl
  unfold translateStepWith
  dsimp only
  split
  · refine WHo.bind L (cacheLookup_S L e) ?_
    intro hit _
    split
    · exact WHo.pure L _ (Q := fun _ => True) trivial
    · refine WHo.bind L core ?_
      intro r hr
      subst hr
      first
        | exact hfb
        | (dsimp only; exact hfb)
  · refine WHo.bind L core ?_
    intro r hr
    subst hr
    first
      | exact hfb
      | (dsimp only; exact hfb)

/-! ## Per constructor -/

/-- A Bool literal: the Bool control arm, one wire and one assign. -/
theorem boolLit_still {dom : Lean.Expr} (b : Bool) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec) (literalE dom b) := by
  intro hint top named
  apply step_of_none L (literal_core rec dom b hint top named)
  rw [translateFallback_bool rec _ hint top named (by cases b <;> rfl)]
  apply controlCached_S L
  rw [literal_uncached]
  unfold emitBoolLiteral
  exact emitBool_S L _ _ _

/-- A numeric literal at the `OfNat` instance: the core's literal arm. -/
theorem bitsNum_still {dom : Lean.Expr} {n v : Nat} (hv : v < 2 ^ n) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec) (numSigE dom n v) := by
  intro hint top named
  have fn : (numSigE dom n v).getAppFn =
      .const ``Sparkle.Core.Signal.Signal.pure [.zero] := rfl
  have back : (numSigE dom n v).getAppArgs.back? = some (numLitE n v) := rfl
  exact step_of_core L (core_literal L fn back (litValue_numLitE n v hv))

/-- A Bool negation: the comparison of the operand with the literal `false`. -/
theorem boolNot_still {dom ae : Lean.Expr}
    (ha : WCh mctx cctx L mb ctx rec ae)
    (hf : WCh mctx cctx L mb ctx rec
      (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
        (.const ``Bool.false []))) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec) (boolNotE dom ae) := by
  intro hint top named
  rw [boolNot_step, translateFallback_bool rec _ hint top named rfl]
  apply controlCached_S L
  show WSt mctx cctx L mb ctx (translateSignalCompare rec .eq ae
    (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
      (.const ``Bool.false [])) hint named)
  exact compare_arm L (ha _ _ _) (hf _ _ _)

/-- A slice map: the operand, then one part-select assign. -/
theorem slice_still {dom ae : Lean.Expr} {nm : Lean.Name} {ws start len : Nat}
    (hlen : 0 < len) (hr : start + len ≤ ws) (ha : WCh mctx cctx L mb ctx rec ae) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec)
      (sliceE dom nm ws start len ae) := by
  intro hint top named
  rw [slice_step rec dom ae nm ws start len hint top named hlen hr]
  apply controlCached_S L
  rw [sliceUncached_sliceE]
  exact WHo.bind L (ha _ _ _) fun sw _ => emitSlice_S L _ _ _ _

/-- The zero-extending map: the operand, then the cast's assign. -/
theorem zextMap_still {dom ae : Lean.Expr} {nm : Lean.Name} {k n : Nat}
    (hk : 0 < k) (hn : 0 < n) (ha : WCh mctx cctx L mb ctx rec ae) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec)
      (zextMapE dom nm k n ae) := by
  intro hint top named
  rw [zextMap_step rec dom nm ae k n hint top named hk hn]
  apply controlCached_S L
  rw [setwUncached_zextMapE]
  exact WHo.bind L (ha _ _ _) fun sw _ => emitCast_S L _ _ _ _

/-- A slice written with `<$>`. -/
theorem sliceF_still {dom ae : Lean.Expr} {nm : Lean.Name} {ws start len : Nat}
    (hlen : 0 < len) (hr : start + len ≤ ws) (ha : WCh mctx cctx L mb ctx rec ae) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec)
      (sliceFE dom nm ws start len ae) := by
  intro hint top named
  rw [sliceF_step rec dom nm ae ws start len hint top named hlen hr]
  apply controlCached_S L
  rw [sliceFUncached_sliceFE]
  exact WHo.bind L (ha _ _ _) fun sw _ => emitSlice_S L _ _ _ _

/-- A concatenation with a literal high operand. -/
theorem concatLitHi_still {dom be : Lean.Expr} {k v n : Nat}
    (hk : 0 < k) (hv : v < 2 ^ k) (hn : 0 < n) (hb : WCh mctx cctx L mb ctx rec be) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec)
      (concatLitHiE dom k v n be) := by
  intro hint top named
  rw [concatLitHi_step rec dom be k v n hint top named hk hv hn]
  apply controlCached_S L
  rw [concatLitUncached_hiE]
  exact concatActs_S L (emitConcatConst_S L k v) (hb _ _ _)

/-- A concatenation with a literal low operand. -/
theorem concatLitLo_still {dom ae : Lean.Expr} {m k v : Nat}
    (hk : 0 < k) (hv : v < 2 ^ k) (hm : 0 < m) (ha : WCh mctx cctx L mb ctx rec ae) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec)
      (concatLitLoE dom m k v ae) := by
  intro hint top named
  rw [concatLitLo_step rec dom ae m k v hint top named hk hv hm]
  apply controlCached_S L
  rw [concatLitUncached_loE]
  exact concatActs_S L (ha _ _ _) (emitConcatConst_S L k v)

/-- A comparison lifted through the applicative. -/
theorem appCompare_still {le : SignalCompareKind} {dom ae be : Lean.Expr} {n : Nat}
    (ha : WCh mctx cctx L mb ctx rec ae) (hb : WCh mctx cctx L mb ctx rec be) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec)
      (appCompareE le dom n ae be) := by
  intro hint top named
  rw [appCompare_step, translateFallback_bool rec _ hint top named
    (isBoolControl_appCompareE dom ae be n le)]
  apply controlCached_S L
  rw [translateBoolUncachedWith_appCompare]
  unfold translateAppCompare
  refine WHo.bind L (ha _ _ _) ?_
  intro aw _
  refine WHo.bind L (hb _ _ _) ?_
  intro bw _
  unfold emitCompareResult
  exact emitBool_S L _ _ _

/-- A Bool operator lifted through the applicative. -/
theorem appBool_still {kind : SignalBoolBinKind} {dom ae be : Lean.Expr}
    (ha : WCh mctx cctx L mb ctx rec ae) (hb : WCh mctx cctx L mb ctx rec be) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec)
      (appBoolE kind dom ae be) := by
  intro hint top named
  rw [appBool_step, translateFallback_bool rec _ hint top named
    (isBoolControl_appBoolE dom ae be kind)]
  apply controlCached_S L
  rw [translateBoolUncachedWith_appBool]
  unfold translateAppBoolBinary
  refine WHo.bind L (ha _ _ _) ?_
  intro aw _
  refine WHo.bind L (hb _ _ _) ?_
  intro bw _
  exact emitBool_S L _ _ _

/-- A two-level Bool body lifted through the applicative: two assigns. -/
theorem appBool2_still {f : AppBool2} {dom ae be : Lean.Expr}
    (ha : WCh mctx cctx L mb ctx rec ae) (hb : WCh mctx cctx L mb ctx rec be) :
    WCh mctx cctx L mb ctx (translateStepWith (translateFallback tenv) rec)
      (appBool2E f dom ae be) := by
  intro hint top named
  rw [appBool2_step, translateFallback_bool rec _ hint top named
    (isBoolControl_appBool2E dom ae be f)]
  apply controlCached_S L
  rw [translateBoolUncachedWith_appBool2]
  unfold translateAppBool2
  refine WHo.bind L (ha _ _ _) ?_
  intro aw _
  refine WHo.bind L (hb _ _ _) ?_
  intro bw _
  refine WHo.bind L (emitBool_S L _ _ _) ?_
  intro nw _
  exact emitBool_S L _ _ _

/-! ## The induction over every constructor -/

/-- **The walk leaves the cache, at every fuel, for every well-formed term**
over leaf expressions that are still at every fuel (the cases of
`Tools.ShippingUnifiedRecursion.fuel_contract_leaves`, all of them). -/
theorem fuel_still_all (fuel : Nat) {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bE vE : Nat → Lean.Expr}
    (hbS : ∀ j, j < kb → ∀ fuel,
      WCh mctx cctx L mb ctx (translateFuelFix (translateStep tenv) fuel) (bE j))
    (hvS : ∀ j, j < kv → ∀ fuel,
      WCh mctx cctx L mb ctx (translateFuelFix (translateStep tenv) fuel) (vE j)) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw →
      WCh mctx cctx L mb ctx (translateFuelFix (translateStep tenv) fuel) (quote dom bE vE e) := by
  induction fuel with
  | zero =>
    intro s e _ hint top named
    unfold translateFuelFix
    exact WSt.throw L _
  | succ fuel ih =>
    intro s e he
    change WCh mctx cctx L mb ctx
      (translateStepWith (translateFallback tenv) (translateFuelFix (translateStep tenv) fuel)) _
    cases e with
    | boolInput j => exact hbS j he (fuel + 1)
    | bitsInput w j =>
      obtain ⟨hj, hw, hpos⟩ := he
      cases hw
      exact hvS j hj (fuel + 1)
    | boolLit b => exact boolLit_still L b
    | bitsLit w v =>
      obtain ⟨hval, hpos⟩ := he
      exact bitsLit_still L hval
    | bitsNum w v =>
      obtain ⟨hval, hpos⟩ := he
      exact bitsNum_still L hval
    | binary op a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      have ck := op_checks op dom (quote dom bE vE a) (quote dom bE vE b) w
      have ca : WSt mctx cctx L mb ctx
          ((translateFuelFix (translateStep tenv) fuel)
            ((binE dom w op (quote dom bE vE a)
              (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
              (quote dom bE vE b)).getAppArgs.size - 2]!) "op_a" false false) := by
        rw [ck.2.2.2.2.1]
        exact ih a ha _ _ _
      have cb : WSt mctx cctx L mb ctx
          ((translateFuelFix (translateStep tenv) fuel)
            ((binE dom w op (quote dom bE vE a)
              (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
              (quote dom bE vE b)).getAppArgs.size - 1]!) "op_b" false false) := by
        rw [ck.2.2.2.2.2.1]
        exact ih b hb' _ _ _
      intro hint top named
      exact step_of_core L
        (core_binary L ck.1 ck.2.1 ck.2.2.2.2.2.2 ck.2.2.1 ck.2.2.2.1 ca cb)
    | compare op a b =>
      obtain ⟨ha, hb'⟩ := he
      exact compare_still L (ih a ha) (ih b hb')
    | boolBinary op a b =>
      obtain ⟨ha, hb'⟩ := he
      exact boolBin_still L (ih a ha) (ih b hb')
    | boolNot a =>
      exact boolNot_still L (ih a he) (ih (.boolLit false) trivial)
    | boolEq a b =>
      obtain ⟨ha, hb'⟩ := he
      exact boolEq_still L (ih a ha) (ih b hb')
    | mux c a b =>
      obtain ⟨hc, ha, hb'⟩ := he
      cases s with
      | bool => exact boolMux_still L (ih c hc) (ih a ha) (ih b hb')
      | bits w => exact vector_still L (ih c hc) (ih a ha) (ih b hb')
    | setw w' a =>
      obtain ⟨ha, hpos⟩ := he
      exact setw_still L (a.wf_pos ha) hpos (ih a ha)
    | appCompare op a b =>
      obtain ⟨ha, hb'⟩ := he
      exact appCompare_still L (ih a ha) (ih b hb')
    | appBool op a b =>
      obtain ⟨ha, hb'⟩ := he
      exact appBool_still L (ih a ha) (ih b hb')
    | appBool2 f a b =>
      obtain ⟨ha, hb'⟩ := he
      exact appBool2_still L (ih a ha) (ih b hb')
    | slice nm start len a =>
      obtain ⟨ha, hlen, hr⟩ := he
      exact slice_still L hlen hr (ih a ha)
    | concat a b =>
      obtain ⟨ha, hb'⟩ := he
      exact concat_still L (a.wf_pos ha) (b.wf_pos hb') (ih a ha) (ih b hb')
    | concatLitHi k v b =>
      obtain ⟨hb', hk, hlt⟩ := he
      exact concatLitHi_still L hk hlt (b.wf_pos hb') (ih b hb')
    | concatLitLo a k v =>
      obtain ⟨ha, hk, hlt⟩ := he
      exact concatLitLo_still L hk hlt (a.wf_pos ha) (ih a ha)
    | zextMap nm k a =>
      obtain ⟨ha, hk⟩ := he
      exact zextMap_still L hk (a.wf_pos ha) (ih a ha)
    | sliceF nm start len a =>
      obtain ⟨ha, hlen, hr⟩ := he
      exact sliceF_still L hlen hr (ih a ha)

/-- **The certified walk leaves the child cache — every constructor.** For a
well-formed term whose input binders are bound in the context: a returning
run of the shipping translator on its quotation, from a world satisfying the
cache invariant, ends in one with the SAME cache value. -/
theorem walk_still_all {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bi vi : Nat → FVarId}
    (hb : ∀ j, j < kb → WBound ctx (bi j)) (hv : ∀ j, j < kv → WBound ctx (vi j))
    {s : SType} (e : Term s) (he : e.WF kb kv vw) :
    WCh mctx cctx L mb ctx (fun e hint top named => translateExprToWire tenv e hint top named)
      (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e) :=
  fuel_still_all L translateFuelLimit (fun j hj => input_fuel L (hb j hj))
    (fun j hj => input_fuel L (hv j hj)) e he

end Tools.ShippingWalkStillMore

/-! ## The consumers, over every term -/

namespace Tools.ShippingWalkStillMore
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingChildInv Tools.ShippingWalkStill Tools.ShippingHarnessStill
open Tools.ShippingCacheCoherentCert (HarnessStill EntryStill)
open Tools.ShippingCacheCoherentRun (full_split)
open Tools.ShippingCacheCoherentVia (core_reads_val coreVia_of)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

variable (L : RefLaws mref cref) {mb : Std.HashMap Lean.Name Res} {ctx : CompilerState}

/-- **`HarnessStill` for the quotation of ANY well-formed term over the
binders** (the hypotheses of the built `transition_facts`; no fragment
condition). The text of `Tools.ShippingHarnessStill.harnessStill_frag` with
`walk_still_all` in the place of `walk_still`. -/
theorem harnessStill_all {declName : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
    {body dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    {s : SType} {e : Term s} (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (hbody : body = quote dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vpos j)) e) :
    HarnessStill L declName bs body := by
  intro tenv mctx cctx b w r w' hw _ hr
  subst hbody
  have hS : WSI L (L.val w) w := ⟨hw, rfl⟩
  unfold synthesizeMixedCertified at hr
  obtain ⟨ids, w1, hids, hr⟩ := RunsTo.bind hr
  obtain ⟨-, -, hS1⟩ := mapM_hoare _ (WSI L (L.val w)) (fun _ _ => True)
    (fun x w y w' hp hy => by
      exact ⟨trivial, (framedM L Framed.freshFVar w y w' hp hy).1⟩)
    bs ids hS hids
  split at hr
  · rename_i hnd
    dsimp only at hr
    obtain ⟨cacheRef, w2, hmk, hr⟩ := RunsTo.bind hr
    have hS2 : WSI L (L.val w) w2 := (framedM L (Framed.mkExprCache _) w1 cacheRef w2 hS1 hmk).1
    obtain ⟨⟨a, fs⟩, w3, hrun, hr⟩ := RunsTo.bind hr
    -- the instantiated body is the quotation over the fresh ids
    have hq := Tools.ShippingUnifiedExecutionSoundness.instantiated_quote
      (xs := (ids.map Lean.Expr.fvar).toArray) (dom := dom)
      (binp := fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bpos j))
      (vinp := fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vpos j))
      (bids := fun j => ids[bpos j]!) (vids := fun j => ids[vpos j]!)
      (fun j hj => by
        obtain ⟨name, pos⟩ := hb j hj
        exact Tools.ShippingMixedSourceBridge.instantiated_input hnd.2
          (List.getElem_of_getElem? pos).choose)
      (fun j hj => by
        obtain ⟨name, pos⟩ := hv j hj
        exact Tools.ShippingMixedSourceBridge.instantiated_input hnd.2
          (List.getElem_of_getElem? pos).choose)
      e he
    have hcomp : WSt mctx cctx L (L.val w) (entryCompilerState false cacheRef)
        (bindMixedCertifiedInputs
          (emitLeaves (fun e hint top named => translateExprToWire tenv e hint top named) cacheRef
            (profLogIO b)
            [("out", instFVars (ids.map Lean.Expr.fvar).toArray 0
              (quote dom
                (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bpos j))
                (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vpos j)) e))]
            none 0) (bs.zip ids)) := by
      refine bind_S L _ (bs.zip ids) _ [] (fun i hi => by cases hi) (fun ctx' _ hl => ?_)
      refine emitLeaves_S L b cacheRef _ none 0 (fun p hp => ?_)
      have hp' : p = ("out", instFVars (ids.map Lean.Expr.fvar).toArray 0
          (quote dom
            (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bpos j))
            (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vpos j)) e)) := by
        simpa using hp
      rw [hp']
      show WSt mctx cctx L (L.val w) ctx' (translateExprToWire tenv
        (instFVars (ids.map Lean.Expr.fvar).toArray 0
          (quote dom
            (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bpos j))
            (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vpos j)) e))
        "out" false true)
      rw [hq]
      exact walk_still_all L
        (fun j hj => by
          obtain ⟨name, pos⟩ := hb j hj
          exact hl _ (Tools.ShippingMixedSourceBridge.zip_member hnd.2 pos)
            (show MixedGateBinder.bool ≠ MixedGateBinder.domain from fun h => nomatch h))
        (fun j hj => by
          obtain ⟨name, pos⟩ := hv j hj
          exact hl _ (Tools.ShippingMixedSourceBridge.zip_member hnd.2 pos)
            (show MixedGateBinder.bits (vw j) ≠ MixedGateBinder.domain from fun h => nomatch h))
        e he "out" false true
    have hS3 := (hcomp _ w2 (a, fs) w3 hS2 hrun).1
    have hww : w' = w3 := finishSynth_world hr
    rw [hww]
    exact hS3.2
  · exfalso
    have e' : (EST.Out.error _ w1 : EST.Out Exception IO.RealWorld
        (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) = EST.Out.ok r w' := hr
    cases e'

/-- **`EntryStill` of a gate child on the mixed route**, any term (the
hypotheses of the built `Tools.ShippingGateChildComb.gate_child_fullFacts`).
The text of `Tools.ShippingHarnessStill.entryStill_gate` over
`harnessStill_all`. -/
theorem entryStill_gate_all (hB : ∀ L' : RefLaws mref cref, BodyRel L') {c : Lean.Name}
    {value dom : Lean.Expr} {bs : List (Lean.Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {s : SType} {e : Term s}
    (entry : ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context),
      Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bpos j))
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    EntryStill L c := by
  intro mctx cctx w r w' hw hd hrun
  obtain ⟨M', D'⟩ := r
  obtain ⟨M, D, wc, hcore, hval, -, -⟩ := full_split L hrun
  obtain ⟨b, envR, ci, w1, w2, w3, w4, w5, w6, hget, henv, run, hw3, hd3, hv3, -, hv4⟩ :=
    core_reads_val L hB hw hd hcore
  obtain ⟨d, hdd, definition⟩ := entry mctx cctx w1 ci w2 w5 envR w6 hget henv
  rw [hdd] at run
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have shape := Tools.ShippingUnifiedExecutionSoundness.term_gate (d := d)
    (by rw [definition]; exact peel) he hb hv
  have hs := sfc_mixed_val L oldGate (shape _) (harnessStill_all L he hb hv rfl) hw3 hd3 run
  rw [hval, hv4, hs, hv3]

end Tools.ShippingWalkStillMore

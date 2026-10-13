import Tools.ShippingWalkStill
import Tools.ShippingUnifiedExecutionSoundness

/-! # The harness shell: `HarnessStill` and `EntryStill` as theorems

`Tools.ShippingWalkStill.walk_still`: a returning run of the translator on
the quotation of a term of the fragment `wfrag`, in a context that binds the
input binders, leaves the child cache. This file puts the SHELL around it —
ordinary code, walked in the same logic (`WHo`: returning runs, a fixed
compiler context) — and gets the two statements
`Tools.ShippingCacheCoherentCert` left open:

* `bind_S`: the binder walk (`bindMixedCertifiedInputs`): per non-domain
  binder a wire, an input port, and the reader's map extended by
  `(id, wire)` (`CompilerM.withVarMapping`) — so inside the continuation
  EVERY non-domain binder of the list is `WBound`;
* `emitLeaves_S`: the leaf emission (the text of the built
  `emitLeaves_tripleC`, its do-block restated as there);
* `finishSynth_world`: a returning `finishSynth` leaves the world;
* `harnessStill_frag`: **`HarnessStill L declName bs body`** when
  `body = quote dom … e` with `e` well-formed, in the fragment, its inputs
  at non-domain binder positions — the hypotheses of the built
  `transition_facts`, plus `wfrag e = true`. All decided by reading;
* `machine_leaf_val`, `entryStill_leaf`: **`EntryStill L c`** for a machine
  without calls (`coreVia_of`, then the machine synthesis is the harness and
  a `pure`);
* `sfc_mixed_val`, `entryStill_gate`: **`EntryStill L c`** for a gate child
  on the mixed route (the hypotheses of the built `gate_child_fullFacts`,
  plus `wfrag e = true`).

Nothing is assumed beyond `RefLaws` (and `BodyRel` / `HarnessRel`, built).

WRITTEN, NOT BUILT (par/a-37). -/
namespace Tools.ShippingHarnessStill
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingChildInv Tools.ShippingWalkStill
open Tools.ShippingCacheCoherentCert (HarnessStill EntryStill)
open Tools.ShippingCacheCoherentRun (full_split)
open Tools.ShippingCacheCoherentVia (core_reads_val coreVia_of)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

variable (L : RefLaws mref cref) {mb : Std.HashMap Lean.Name Res} {ctx : CompilerState}

/-! ## More of the logic -/

/-- A throw has no returning run: any postcondition. -/
theorem WHo.throwQ {α : Type} (e : Exception) {Q : α → Prop} :
    WHo mctx cctx L mb ctx (throw e : CompilerM α) Q := by
  intro st w p w' _ hr
  have h : (EST.Out.error e w : EST.Out Exception IO.RealWorld (α × CircuitState)) =
      EST.Out.ok p w' := hr
  cases h

theorem WHo.ite {α : Type} {c : Prop} [Decidable c] {a b : CompilerM α} {Q : α → Prop}
    (ha : c → WHo mctx cctx L mb ctx a Q) (hb : ¬c → WHo mctx cctx L mb ctx b Q) :
    WHo mctx cctx L mb ctx (if c then a else b) Q := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

/-- A continuation run under another reader. -/
theorem WHo.withReader {α : Type} {k : CompilerM α} {Q : α → Prop}
    (f : CompilerState → CompilerState) (h : WHo mctx cctx L mb (f ctx) k Q) :
    WHo mctx cctx L mb ctx (withReader f k) Q :=
  fun st w p w' hw hr => h st w p w' hw hr

/-- A diagnostic `MetaM` operation on a returning run. -/
theorem diagM {α : Type} {m : Lean.Meta.MetaM α} (hp : Diag m)
    (w : Void IO.RealWorld) (a : α) (w' : Void IO.RealWorld) (hw : WSI L mb w)
    (h : RunsTo m mctx mref cctx cref w a w') : WSI L mb w' ∧ True := by
  obtain ⟨⟨hv, hs, -⟩, hq⟩ := L.sameD hp h hw.1.2.2
  refine ⟨⟨⟨?_, ?_, hq⟩, ?_⟩, trivial⟩
  · rw [hv]; exact hw.1.1
  · rw [hs]; exact hw.1.2.1
  · rw [hv]; exact hw.2

theorem addInput_S (name : String) (ty : Sparkle.IR.Type.HWType) :
    WSt mctx cctx L mb ctx (CompilerM.addInput name ty) := by
  unfold CompilerM.addInput
  refine WHo.bind L (WSt.get L) ?_
  intro cs _
  split
  refine WHo.bind L (WSt.set L _) ?_
  intro _ _
  split
  · exact wireWidth_S L _
  · exact WHo.pure L _ (Q := fun _ => True) trivial

theorem addOutput_S (name : String) (ty : Sparkle.IR.Type.HWType) :
    WSt mctx cctx L mb ctx (CompilerM.addOutput name ty) := by
  unfold CompilerM.addOutput
  refine WHo.bind L (WSt.get L) ?_
  intro cs _
  split
  refine WHo.bind L (WSt.set L _) ?_
  intro _ _
  split
  · exact wireWidth_S L _
  · exact WHo.pure L _ (Q := fun _ => True) trivial

/-! ## The binder walk -/

/-- A binding in front keeps what was bound. -/
theorem wbound_keep {fv i : FVarId} {wire : String} (h : WBound ctx i) :
    WBound { ctx with varMap := (fv, wire) :: ctx.varMap } i := by
  by_cases e : i = fv
  · rw [e]
    exact wbound_of_lookup (lookup_cons_self fv wire ctx.varMap)
  · intro st
    have hb := h st
    show (CircuitM.lookupSourceBinding (((fv, wire) :: ctx.varMap).lookup i) i.name st).1 ≠ none
    rw [lookup_cons_ne wire ctx.varMap e]
    exact hb

/-- One input port: the continuation runs with the binder bound, and
whatever was bound still is. -/
theorem bindInputPort_S {α : Type} (fv : FVarId) (bn : String) (ty : Sparkle.IR.Type.HWType)
    (k : CompilerM α) (B : List FVarId) (hB : ∀ i ∈ B, WBound ctx i)
    (hk : ∀ ctx' : CompilerState, (∀ i ∈ fv :: B, WBound ctx' i) → WSt mctx cctx L mb ctx' k) :
    WSt mctx cctx L mb ctx (bindInputPort fv bn ty k) := by
  unfold bindInputPort CompilerM.withVarMapping
  refine WHo.bind L (makeWire_S L _ _ _) ?_
  intro w _
  refine WHo.bind L (addInput_S L _ _) ?_
  intro _ _
  refine WHo.bind L (Q1 := fun c => c = ctx) (WHo.ofPure L fun st => ⟨ctx, st, rfl, rfl⟩) ?_
  intro old hold
  subst hold
  dsimp only
  refine WHo.withReader L _ (hk _ ?_)
  intro i hi
  rcases List.mem_cons.mp hi with e | hi'
  · rw [e]
    exact wbound_of_lookup (lookup_cons_self fv w _)
  · exact wbound_keep (hB i hi')

/-- **The binder walk**: its continuation runs in a context where every
non-domain binder of the list is bound (and what was bound before still is). -/
theorem bind_S {α : Type} (k : CompilerM α) :
    ∀ (l : List ((Lean.Name × MixedGateBinder) × FVarId)) (ctx : CompilerState)
      (B : List FVarId), (∀ i ∈ B, WBound ctx i) →
      (∀ ctx' : CompilerState, (∀ i ∈ B, WBound ctx' i) →
        (∀ p ∈ l, p.1.2 ≠ .domain → WBound ctx' p.2) → WSt mctx cctx L mb ctx' k) →
      WSt mctx cctx L mb ctx (bindMixedCertifiedInputs k l)
  | [], ctx, B, hB, hk => by
    unfold bindMixedCertifiedInputs
    exact hk ctx hB (fun p hp _ => by cases hp)
  | ((_, .domain), _) :: rest, ctx, B, hB, hk => by
    unfold bindMixedCertifiedInputs
    refine bind_S k rest ctx B hB (fun ctx' h1 h2 => hk ctx' h1 (fun p hp hne => ?_))
    rcases List.mem_cons.mp hp with e | hp'
    · rw [e] at hne
      exact absurd rfl hne
    · exact h2 p hp' hne
  | ((nm, .bool), id) :: rest, ctx, B, hB, hk => by
    unfold bindMixedCertifiedInputs
    refine bindInputPort_S L _ _ _ _ B hB (fun ctx' hB' =>
      bind_S k rest ctx' (id :: B) hB' (fun ctx'' h1 h2 =>
        hk ctx'' (fun i hi => h1 i (List.mem_cons_of_mem _ hi)) (fun p hp hne => ?_)))
    rcases List.mem_cons.mp hp with e | hp'
    · rw [e]
      exact h1 id (List.mem_cons_self ..)
    · exact h2 p hp' hne
  | ((nm, .bits n), id) :: rest, ctx, B, hB, hk => by
    unfold bindMixedCertifiedInputs
    refine bindInputPort_S L _ _ _ _ B hB (fun ctx' hB' =>
      bind_S k rest ctx' (id :: B) hB' (fun ctx'' h1 h2 =>
        hk ctx'' (fun i hi => h1 i (List.mem_cons_of_mem _ hi)) (fun p hp hne => ?_)))
    rcases List.mem_cons.mp hp with e | hp'
    · rw [e]
      exact h1 id (List.mem_cons_self ..)
    · exact h2 p hp' hne

/-! ## The leaf emission -/

/-- **`emitLeaves` leaves the cache, given the translator does on each leaf**
(the text of `Tools.ShippingChildInv.emitLeaves_tripleC`). -/
theorem emitLeaves_S (b : Bool) (cacheRef : IO.Ref (Lean.ExprStructMap String)) :
    ∀ (leaves : List (String × Lean.Expr)) (fw : Option String) (idx : Nat),
      (∀ p ∈ leaves, WSt mctx cctx L mb ctx (translateExprToWire p.2 p.1 false true)) →
      WSt mctx cctx L mb ctx
        (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cacheRef
          (profLogIO b) leaves fw idx)
  | [], fw, idx, _ => by
    unfold emitLeaves
    exact WHo.pure L _ (Q := fun _ => True) trivial
  | (pn, le) :: rest, fw, idx, hT => by
    unfold emitLeaves
    have clock : WSt mctx cctx L mb ctx (CompilerM.liftMetaM (liftM IO.monoMsNow)) :=
      WHo.lift L (framedM L Framed.monoMs)
    have calls : WSt mctx cctx L mb ctx (CompilerM.liftMetaM (ST.Ref.get sparkleCallCounter)) :=
      WHo.lift L (framedM L (Framed.sideGet .callCounter))
    have hits : WSt mctx cctx L mb ctx (CompilerM.liftMetaM (ST.Ref.get sparkleCacheHits)) :=
      WHo.lift L (framedM L (Framed.sideGet .cacheHits))
    have log : ∀ msg, WSt mctx cctx L mb ctx (CompilerM.liftMetaM (liftM (profLogIO b msg))) :=
      fun msg => WHo.lift L (diagM L (Diag.profLog b msg))
    refine WHo.bind L clock ?_; intro t0 _
    refine WHo.bind L calls ?_; intro c0 _
    refine WHo.bind L hits ?_; intro h0 _
    refine WHo.bind L (log _) ?_; intro _ _
    refine WHo.bind L (hT (pn, le) (List.mem_cons_self ..)) ?_; intro lw _
    refine WHo.bind L clock ?_; intro t1 _
    refine WHo.bind L calls ?_; intro c1 _
    refine WHo.bind L hits ?_; intro h1 _
    refine WHo.bind L (log _) ?_; intro _ _
    -- the tail after the translation cache's update
    have tail : ∀ u : Unit, WSt mctx cctx L mb ctx
        ((fun (__r : Unit) => (do
          let cs ← get
          have __do_jp : Unit → CompilerM String := fun __r =>
            have wireDecl := List.find? (fun p => p.name == lw) cs.module.wires;
            have outputType :=
              match wireDecl with
              | some decl => decl.ty
              | none =>
                match List.find? (fun p => p.name == lw) cs.module.inputs with
                | some inputPort => inputPort.ty
                | none => Sparkle.IR.Type.HWType.bitVector 8;
            do
            CompilerM.addOutput pn outputType
            CompilerM.emitAssign pn (Sparkle.IR.AST.Expr.ref lw)
            emitLeaves (fun e hint top named => translateExprToWire e hint top named) cacheRef
                (profLogIO b) rest (if fw.isNone = true then some lw else fw) (idx + 1)
          if cs.usedNames.contains pn = true then do
              let __r ←
                throw
                    (Exception.error Syntax.missing
                      (toMessageData "output port name '" ++ toMessageData pn ++
                        toMessageData "' is already a name of this module"))
              __do_jp __r
            else __do_jp () : CompilerM String)) u) := by
      intro u
      dsimp only
      refine WHo.bind L (WSt.get L) ?_
      intro cs _
      have rest' : WSt mctx cctx L mb ctx
          (do
            CompilerM.addOutput pn
              (match List.find? (fun p => p.name == lw) cs.module.wires with
              | some decl => decl.ty
              | none =>
                match List.find? (fun p => p.name == lw) cs.module.inputs with
                | some inputPort => inputPort.ty
                | none => Sparkle.IR.Type.HWType.bitVector 8)
            CompilerM.emitAssign pn (Sparkle.IR.AST.Expr.ref lw)
            emitLeaves (fun e hint top named => translateExprToWire e hint top named) cacheRef
                (profLogIO b) rest (if fw.isNone = true then some lw else fw) (idx + 1)) := by
        refine WHo.bind L (addOutput_S L _ _) ?_
        intro _ _
        refine WHo.bind L (emitAssign_S L _ _) ?_
        intro _ _
        exact emitLeaves_S b cacheRef rest _ _ (fun p hp => hT p (List.mem_cons_of_mem _ hp))
      refine WHo.ite L (fun _ => ?_) (fun _ => rest')
      refine WHo.bind L (Q1 := fun _ => False) (WHo.throwQ L _) ?_
      intro _ hf
      exact hf.elim
    dsimp only
    refine WHo.ite L (fun _ => ?_) (fun _ => tail ())
    refine WHo.bind L (WHo.lift L (framedM L (Framed.exprCacheModify _ _))) ?_
    intro u _
    exact tail u

/-! ## `finishSynth`, and the harness -/

/-- A returning `finishSynth` (no parameters, not symbolic) leaves the world. -/
theorem finishSynth_world {declName : Lean.Name} {st : CircuitState}
    {r : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (h : RunsTo (finishSynth declName [] false st) mctx mref cctx cref w r w') : w' = w := by
  unfold finishSynth at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  rcases RunsTo.ite h with h | h
  · exact (RunsTo.pure_world h).2
  · exfalso
    have e : (EST.Out.error _ w : EST.Out Exception IO.RealWorld
        (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) = EST.Out.ok r w' := h
    cases e

/-- The input positions, from the form the machine data decides
(`MachineData.ok`). -/
theorem bool_pos_of_map {bs : List (Lean.Name × MixedGateBinder)} {kb : Nat} {bpos : Nat → Nat}
    (h : ∀ j, j < kb → (bs[bpos j]?).map (·.2) = some MixedGateBinder.bool) :
    ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool) := by
  intro j hj
  have := h j hj
  cases hx : bs[bpos j]? with
  | none => rw [hx] at this; cases this
  | some b =>
    obtain ⟨name, k⟩ := b
    rw [hx] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact ⟨name, by rw [← this]⟩

theorem bits_pos_of_map {bs : List (Lean.Name × MixedGateBinder)} {kv : Nat} {vpos vw : Nat → Nat}
    (h : ∀ j, j < kv → (bs[vpos j]?).map (·.2) = some (MixedGateBinder.bits (vw j))) :
    ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)) := by
  intro j hj
  have := h j hj
  cases hx : bs[vpos j]? with
  | none => rw [hx] at this; cases this
  | some b =>
    obtain ⟨name, k⟩ := b
    rw [hx] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact ⟨name, by rw [← this]⟩

/-- **`HarnessStill` is a theorem** for a body that is the quotation of a
well-formed term of the fragment over the binders (the hypotheses of the
built `transition_facts`, and `wfrag`). -/
theorem harnessStill_frag {declName : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
    {body dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    {s : SType} {e : Term s} (he : e.WF kb kv vw) (hf : wfrag e = true)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (hbody : body = quote dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vpos j)) e) :
    HarnessStill L declName bs body := by
  intro mctx cctx b w r w' hw _ hr
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
          (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cacheRef
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
      show WSt mctx cctx L (L.val w) ctx' (translateExprToWire
        (instFVars (ids.map Lean.Expr.fvar).toArray 0
          (quote dom
            (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bpos j))
            (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vpos j)) e))
        "out" false true)
      rw [hq]
      exact walk_still L
        (fun j hj => by
          obtain ⟨name, pos⟩ := hb j hj
          exact hl _ (Tools.ShippingMixedSourceBridge.zip_member hnd.2 pos)
            (show MixedGateBinder.bool ≠ MixedGateBinder.domain from fun h => nomatch h))
        (fun j hj => by
          obtain ⟨name, pos⟩ := hv j hj
          exact hl _ (Tools.ShippingMixedSourceBridge.zip_member hnd.2 pos)
            (show MixedGateBinder.bits (vw j) ≠ MixedGateBinder.domain from fun h => nomatch h))
        e he hf "out" false true
    have hS3 := (hcomp _ w2 (a, fs) w3 hS2 hrun).1
    have hww : w' = w3 := finishSynth_world hr
    rw [hww]
    exact hS3.2
  · exfalso
    have e' : (EST.Out.error _ w1 : EST.Out Exception IO.RealWorld
        (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) = EST.Out.ok r w' := hr
    cases e'

/-! ## `EntryStill`: a machine without calls -/

/-- The machine synthesis of a shape without calls: the harness, then a
`pure`. -/
theorem machine_leaf_val {b : Bool} {declName : Lean.Name} {shape : MachineShape}
    {r : Option Res} {w w' : Void IO.RealWorld}
    (hstill : HarnessStill L declName shape.binders shape.body) (hno : shape.insts = [])
    (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w r w') : L.val w' = L.val w := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hv1 : L.val w1 = L.val w := hstill mctx cctx b w (t, d') w1 hw hd run
  dsimp only at hr
  split at hr
  · split at hr
    · rw [(RunsTo.pure_world hr).2]
      exact hv1
    · rename_i hi
      rw [hi] at hno
      cases hno
  · rw [(RunsTo.pure_world hr).2]
    exact hv1

/-- **`EntryStill` of a machine without calls**, from the route premises
(`MachineDefines`, `MachineClosesAt`) and `HarnessStill` of its transition. -/
theorem entryStill_leaf (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    (hH : ∀ L' : RefLaws mref cref, HarnessRel L') {c : Lean.Name} {shape : MachineShape}
    (entry : ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context),
      Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref c shape)
    (closes : ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context),
      MachineClosesAt mctx mref cctx cref c shape)
    (hno : shape.insts = [])
    (hstill : HarnessStill L c shape.binders shape.body) : EntryStill L c := by
  intro mctx cctx w r w' hw hd hrun
  obtain ⟨M', D'⟩ := r
  obtain ⟨M, D, wc, hcore, hval, -, -⟩ := full_split L hrun
  obtain ⟨b, w9, w10, hmach, hw9, hd9, hv9, hv10⟩ :=
    coreVia_of L hB hH entry closes mctx cctx w M D wc hw hd hcore
  rw [hval, hv10, machine_leaf_val L hstill hno hw9 hd9 hmach, hv9]

/-! ## `EntryStill`: a gate child on the mixed route -/

/-- The mixed arm of `synthesizeFromConst`: the log line, the harness, the
memo insert, `return`. -/
theorem sfc_mixed_val {b : Bool} {declName : Lean.Name} {ci : ConstantInfo}
    {isInst : Lean.Expr → Bool} {bs : List (Lean.Name × MixedGateBinder)} {body : Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hst : HarnessStill L declName bs body) (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire e h t n) (profLogIO b)
      declName [] false true ci isInst) mctx mref cctx cref w (m, d) w') :
    L.val w' = L.val w := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  obtain ⟨_, wa, hlog, hr⟩ := RunsTo.bind hr
  obtain ⟨⟨hva, hsa, hda⟩, hqa⟩ := L.sameD (.profLog _ _) hlog hw.2.2
  have hwa : InvV L wa := ⟨by rw [hva]; exact hw.1, by rw [hsa]; exact hw.2.1, hqa⟩
  have hdA : L.dval wa ≠ 0 := by rw [hda]; exact hd
  obtain ⟨res, wb, hharn, hr⟩ := RunsTo.bind hr
  have hvb : L.val wb = L.val wa := hst mctx cctx b wa res wb hwa hdA hharn
  obtain ⟨_, wc, hmod, hr⟩ := RunsTo.bind hr
  have hvc := (L.same (.sideModify _ .subModule) hmod).1
  obtain ⟨-, hww⟩ := RunsTo.pure_world hr
  rw [hww, hvc, hvb, hva]

/-- **`EntryStill` of a gate child on the mixed route** (the hypotheses of
the built `Tools.ShippingGateChildComb.gate_child_fullFacts`, and `wfrag`). -/
theorem entryStill_gate (hB : ∀ L' : RefLaws mref cref, BodyRel L') {c : Lean.Name}
    {value dom : Lean.Expr} {bs : List (Lean.Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {s : SType} {e : Term s}
    (entry : ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context),
      Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bpos j))
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw) (hf : wfrag e = true)
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
  have hs := sfc_mixed_val L oldGate (shape _) (harnessStill_frag L he hf hb hv rfl) hw3 hd3 run
  rw [hval, hv4, hs, hv3]

end Tools.ShippingHarnessStill

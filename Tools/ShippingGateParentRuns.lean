import Tools.ShippingInstArmGrow
import Tools.ShippingChildBody
import Tools.ShippingCacheCoherentVia
import Tools.ShippingMixedEntrySoundness

variable {tenv : Lean.Environment}

/-! # The mixed harness shell, world by world, for a gate-route parent (worker N, round 1)

WRITTEN, NOT BUILT.

`Tools/ShippingHarnessStill.lean` walks the harness `synthesizeMixedCertified`
in `WHo` (the cache VALUE fixed), and the S6 shape proofs
(`Tools/ShippingInstanceEntrySoundness.lean`) walk it with `Returns`
(existential worlds). Neither keeps the world in which the translator starts
on the parent's body, which is what the instance arm's child synthesis needs
(`childSynthEntry_post`: an invariant world of positive depth). This file
walks the SAME code with `RunsTo`, keeping the worlds, and the circuit
states exactly as `prepare` / `emitLeaves_single` describe them:

* small rules: `runs_keep` / `op_runs` (a returning run of an operation whose
  `Keeps` lemma is built keeps the invariant and the depth), `lift_runs`
  (a lifted `MetaM` action: the circuit state unchanged, the inner run),
  `RunsTo.bindC` / `RunsTo.bindR` (a `CompilerM` bind with its worlds;
  the text of the built `Returns.bind`), `runsToReturns`;
* `bindInputPort_runs`, `bindMixed_runs`: the binder walk ends in the state
  and context `prepare` computes (any valuation: the state does not depend
  on it), from an invariant world of the same depth (the text of the built
  `prepare_returns`, with worlds);
* `emitLeaves_single_runs`: one leaf — the translator's run from an
  invariant world of the depth, and the state facts of the built
  `emitLeaves_single` (the port is fresh, the final state is the output
  port and its `assign` after the translator);
* `mixedHarness_runs`: **the harness shell** — from a returning run of
  `synthesizeMixedCertified` from an invariant world at depth `D`: the fresh
  ids, the translation cache, the translator's run on the instantiated body
  in the prepared context and state from an invariant world at depth `D`,
  and the returned pair as `finishSynth` builds it;
* `instanceArm_run`: the instance arm at a tagged constant head, from an
  invariant world of positive depth — the child pair it synthesises is a
  `RealChild`, and the rest of the run IS a run of `armCont` on that pair,
  from the arm's own circuit state (the states kept, unlike the `∃ st s'`
  of the built `instanceArm_grow`).

Nothing is assumed beyond `RefLaws` (and the proved `bodyRel`). -/
namespace Tools.ShippingGateParentRun
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingChildInv
open Tools.ShippingCacheCoherentVia (keeps_runs)
open Tools.ShippingWalkGrow (childSynthEntry_post)
open Tools.ShippingMixedEntrySoundness (Setup start prepare)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-! ## Small rules -/

/-- A returning run of an action that keeps `J L.plain D` keeps the
invariant and the depth. -/
theorem runs_keep (L : RefLaws mref cref) {D : Nat} {α : Type} {m : MetaM α}
    (hk : Keeps mctx mref cctx cref (J L.plain D) m)
    {w : Void IO.RealWorld} {a : α} {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D) (r : RunsTo m mctx mref cctx cref w a w') :
    InvV L w' ∧ L.dval w' = D := by
  have h := keeps_runs hk (show J L.plain D w from ⟨hw, hd, trivial⟩) r
  exact ⟨h.1, h.2.1⟩

/-- An operation of the frame / diagnostic class. -/
theorem op_runs (L : RefLaws mref cref) {D : Nat} {α : Type} {p : MetaM α} (hp : Op p)
    {w : Void IO.RealWorld} {a : α} {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D) (r : RunsTo p mctx mref cctx cref w a w') :
    InvV L w' ∧ L.dval w' = D :=
  runs_keep L (keeps_iff.mpr (Triple.op L.plain hp D)) hw hd r

/-- A run of a `CompilerM` action is a `Returns` of it. -/
theorem runsToReturns {α : Type} {c : CompilerM α} {ctx : CompilerState} {s : CircuitState}
    {w : Void IO.RealWorld} {a : α} {s' : CircuitState} {w' : Void IO.RealWorld}
    (h : RunsTo (c ctx s) mctx mref cctx cref w (a, s') w') : Returns c ctx s a s' :=
  ⟨mctx, mref, cctx, cref, w, w', h⟩

/-- A `CompilerM` bind, with its worlds (the text of `Returns.bind`). -/
theorem RunsTo.bindC {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    {ctx : CompilerState} {s : CircuitState} {w : Void IO.RealWorld} {r : β × CircuitState}
    {w' : Void IO.RealWorld}
    (h : RunsTo ((c >>= f) ctx s) mctx mref cctx cref w r w') :
    ∃ (a : α) (s1 : CircuitState) (w1 : Void IO.RealWorld),
      RunsTo (c ctx s) mctx mref cctx cref w (a, s1) w1 ∧
      RunsTo (f a ctx s1) mctx mref cctx cref w1 r w' := by
  unfold RunsTo at h
  change (EST.bind (c ctx s mctx mref cctx cref)
    fun p => f p.1 ctx p.2 mctx mref cctx cref) w = _ at h
  unfold EST.bind at h
  split at h
  · rename_i p w1 heq
    exact ⟨p.1, p.2, w1, heq, h⟩
  · cases h

/-- A `CompilerM` bind: the first action with its worlds, the rest as a
`Returns` (for the built state lemmas). -/
theorem RunsTo.bindR {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    {ctx : CompilerState} {s : CircuitState} {w : Void IO.RealWorld} {r : β × CircuitState}
    {w' : Void IO.RealWorld}
    (h : RunsTo ((c >>= f) ctx s) mctx mref cctx cref w r w') :
    ∃ (a : α) (s1 : CircuitState) (w1 : Void IO.RealWorld),
      RunsTo (c ctx s) mctx mref cctx cref w (a, s1) w1 ∧ Returns (f a) ctx s1 r.1 r.2 := by
  obtain ⟨a, s1, w1, h1, h2⟩ := RunsTo.bindC h
  exact ⟨a, s1, w1, h1, mctx, mref, cctx, cref, w1, w', h2⟩

/-- A lifted `MetaM` action: the circuit state is unchanged and the inner
action ran between the same worlds (the text of `Returns.liftMetaM`). -/
theorem lift_runs {α : Type} {x : MetaM α} {ctx : CompilerState} {s : CircuitState}
    {w : Void IO.RealWorld} {a : α} {s' : CircuitState} {w' : Void IO.RealWorld}
    (h : RunsTo (CompilerM.liftMetaM x ctx s) mctx mref cctx cref w (a, s') w') :
    s' = s ∧ RunsTo x mctx mref cctx cref w a w' := by
  unfold RunsTo at h
  change (EST.bind (x mctx mref cctx cref) fun a => EST.pure (a, s)) w = _ at h
  unfold EST.bind at h
  split at h
  · rename_i b w1 heq
    simp only [EST.pure] at h
    cases h
    exact ⟨rfl, heq⟩
  · cases h

/-! ## The binder walk -/

/-- One input port: the continuation runs in the context and state the
built `bindInputPort_returns` names, from an invariant world of the depth. -/
theorem bindInputPort_runs (L : RefLaws mref cref) {D : Nat} {α : Type} {id : FVarId}
    {nm : String} {ty : Sparkle.IR.Type.HWType} {k : CompilerM α} {ctx : CompilerState}
    {s : CircuitState} {w : Void IO.RealWorld} {p : α × CircuitState} {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (h : RunsTo (bindInputPort id nm ty k ctx s) mctx mref cctx cref w p w') :
    ∃ w1 : Void IO.RealWorld, InvV L w1 ∧ L.dval w1 = D ∧
      RunsTo (k { ctx with varMap := (id, (CircuitM.makeWire nm ty true s).1) :: ctx.varMap }
        (CircuitM.addInput (CircuitM.makeWire nm ty true s).1 ty
          (CircuitM.makeWire nm ty true s).2).2) mctx mref cctx cref w1 p w' := by
  unfold bindInputPort CompilerM.withVarMapping at h
  obtain ⟨wn, sA, w1, hmk, h⟩ := RunsTo.bindC h
  obtain ⟨hw1, hd1⟩ := runs_keep L (makeWire_keepsC L.plain D nm ty true ctx s) hw hd hmk
  obtain ⟨hwn, hsA⟩ := makeWire_returns (runsToReturns hmk)
  obtain ⟨u, sB, w2, hin, h⟩ := RunsTo.bindC h
  obtain ⟨hw2, hd2⟩ :=
    runs_keep L (keepsC_iff.mpr (addInput_tripleC L.plain D wn ty) ctx sA) hw1 hd1 hin
  have hsB := addInput_returns (runsToReturns hin)
  obtain ⟨old, sC, w3, hrd, h⟩ := RunsTo.bindC h
  have hrd' : RunsTo (Pure.pure (ctx, sB) : MetaM (CompilerState × CircuitState))
      mctx mref cctx cref w2 (old, sC) w3 := hrd
  obtain ⟨hold, hw3⟩ := RunsTo.pure_world hrd'
  obtain ⟨e1, e2⟩ := Prod.mk.inj hold
  subst e1 e2 hw3
  refine ⟨_, hw2, hd2, ?_⟩
  rw [← hwn, ← hsA, ← hsB]
  exact h

/-- **The binder walk** ends in the context and state `prepare` computes, from
an invariant world of the same depth (the text of the built
`prepare_returns`, with worlds; the valuation only labels the setup). -/
theorem bindMixed_runs (L : RefLaws mref cref) {D : Nat} {α : Type} (k : CompilerM α)
    (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) :
    ∀ (l : List ((Lean.Name × MixedGateBinder) × FVarId)) (a : Setup) (w : Void IO.RealWorld)
      (p : α × CircuitState) (w' : Void IO.RealWorld),
      InvV L w → L.dval w = D →
      RunsTo (bindMixedCertifiedInputs k l a.context a.state) mctx mref cctx cref w p w' →
      ∃ w1 : Void IO.RealWorld, InvV L w1 ∧ L.dval w1 = D ∧
        RunsTo (k (prepare bools bits l a).context (prepare bools bits l a).state)
          mctx mref cctx cref w1 p w'
  | [], a, w, p, w', hw, hd, h => ⟨w, hw, hd, h⟩
  | ((_, .domain), _) :: rest, a, w, p, w', hw, hd, h =>
    bindMixed_runs L k bools bits rest a w p w' hw hd h
  | ((nm, .bool), id) :: rest, a, w, p, w', hw, hd, h => by
    obtain ⟨w1, hw1, hd1, h1⟩ := bindInputPort_runs L hw hd h
    exact bindMixed_runs L k bools bits rest
      (Tools.ShippingMixedEntrySoundness.extend a ((nm, .bool), id) bools bits) w1 p w' hw1 hd1 h1
  | ((nm, .bits n), id) :: rest, a, w, p, w', hw, hd, h => by
    obtain ⟨w1, hw1, hd1, h1⟩ := bindInputPort_runs L hw hd h
    exact bindMixed_runs L k bools bits rest
      (Tools.ShippingMixedEntrySoundness.extend a ((nm, .bits n), id) bools bits) w1 p w' hw1 hd1 h1

/-! ## The leaf emission -/

/-- **One return leaf, with its worlds**: the clock, the counters and the log
line (frame / diagnostic operations: the invariant and the depth kept, the
circuit state unchanged), the translator's run, then the text of the built
`emitLeaves_single` for the rest. -/
theorem emitLeaves_single_runs (L : RefLaws mref cref) {D : Nat} {b : Bool}
    {cacheRef : IO.Ref (Lean.ExprStructMap String)} {port : String} {e : Lean.Expr}
    {ctx : CompilerState} {s : CircuitState} {w : Void IO.RealWorld} {r : String × CircuitState}
    {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (h : RunsTo (emitLeaves (fun e hint top named => translateExprToWire tenv e hint top named)
      cacheRef (profLogIO b) [(port, e)] none 0 ctx s) mctx mref cctx cref w r w') :
    ∃ (w1 w2 : Void IO.RealWorld) (wire : String) (s1 : CircuitState)
      (ty : Sparkle.IR.Type.HWType),
      InvV L w1 ∧ L.dval w1 = D ∧
      RunsTo (translateExprToWire tenv e port false true ctx s) mctx mref cctx cref w1
        (wire, s1) w2 ∧
      s1.usedNames.contains port = false ∧
      r.2 = (CircuitM.emitAssign port (.ref wire) (CircuitM.addOutput port ty s1).2).2 ∧
      ty = leafOutputType s1 wire := by
  unfold emitLeaves at h
  -- the clock read
  obtain ⟨_, sa, wa, sta0, ha⟩ := RunsTo.bindC h
  obtain ⟨hsa, sta⟩ := lift_runs sta0
  subst hsa
  obtain ⟨hwa, hda⟩ := op_runs L (Op.framed Framed.monoMs) hw hd sta
  -- the call counter
  obtain ⟨_, sb, wb, stb0, hb⟩ := RunsTo.bindC ha
  obtain ⟨hsb, stb⟩ := lift_runs stb0
  subst hsb
  obtain ⟨hwb, hdb⟩ := op_runs L (Op.framed (Framed.sideGet .callCounter)) hwa hda stb
  -- the cache-hit counter
  obtain ⟨_, sc, wc, stc0, hc⟩ := RunsTo.bindC hb
  obtain ⟨hsc, stc⟩ := lift_runs stc0
  subst hsc
  obtain ⟨hwc, hdc⟩ := op_runs L (Op.framed (Framed.sideGet .cacheHits)) hwb hdb stc
  -- the log line
  obtain ⟨_, sd, wd, std0, hd0⟩ := RunsTo.bindC hc
  obtain ⟨hsd, std⟩ := lift_runs std0
  subst hsd
  obtain ⟨hwd, hdd⟩ := op_runs L (Op.diag (Diag.profLog b _)) hwc hdc std
  -- the translator
  obtain ⟨wire, s1, w2, htr, h⟩ := RunsTo.bindR hd0
  -- the rest: the text of `emitLeaves_single`
  peel_lift h; peel_lift h; peel_lift h; peel_lift h
  try dsimp only at h
  have h1 := Returns.lift_or_skip h
  clear h
  obtain ⟨cs, s3, hget, h2⟩ := Returns.bind h1
  obtain ⟨hcs, hs3⟩ := Returns.get hget
  obtain ⟨hfresh, h3⟩ := Returns.guard_throw h2
  obtain ⟨_, s5, hout, h4⟩ := Returns.bind h3
  have hs5 := addOutput_returns hout
  obtain ⟨_, s6, hem, h5⟩ := Returns.bind h4
  have hs6 := emitAssign_returns hem
  unfold emitLeaves at h5
  obtain ⟨-, hs'⟩ := Returns.pure h5
  rw [hcs] at hfresh hs5
  exact ⟨wd, w2, wire, s1, leafOutputType s1 wire, hwd, hdd, htr, hfresh,
    by rw [hs', hs6, hs5, hs3]; rfl, rfl⟩

/-! ## The harness shell -/

/-- **The mixed harness shell, world by world.** A returning run of the
harness from an invariant world at depth `D`: fresh distinct ids, a
translation cache, and the translator's run on the instantiated body — in the
context and state the binder walk prepares (`prepare`, the all-zero
valuation: the state does not depend on it) — from an invariant world at
depth `D`; the leaf's port is fresh, the final circuit state is the output
port and its `assign` after the translator, and the returned pair is what
`finishSynth` builds from it. -/
theorem mixedHarness_runs (L : RefLaws mref cref) {D : Nat} {b : Bool} {declName : Lean.Name}
    {bs : List (Lean.Name × MixedGateBinder)} {body : Lean.Expr}
    {w : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) declName bs body) mctx mref cctx cref w (m, d) w') :
    ∃ (ids : List FVarId) (cache : IO.Ref (Lean.ExprStructMap String))
      (wT wT' : Void IO.RealWorld) (wire : String) (sm0 : CircuitState)
      (ty : Sparkle.IR.Type.HWType) (st : CircuitState),
      ids.Nodup ∧ ids.length = bs.length ∧ InvV L wT ∧ L.dval wT = D ∧
      RunsTo (translateExprToWire tenv (instFVars (ids.map Lean.Expr.fvar).toArray 0 body)
          "out" false true
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName))).context
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName))).state)
        mctx mref cctx cref wT (wire, sm0) wT' ∧
      sm0.usedNames.contains "out" = false ∧
      st = (CircuitM.emitAssign "out" (.ref wire) (CircuitM.addOutput "out" ty sm0).2).2 ∧
      ty = leafOutputType sm0 wire ∧
      m = (addClockResetIfSequential st.module).finalize ∧ d = st.design := by
  unfold synthesizeMixedCertified at hr
  obtain ⟨ids, w1, hids, hr⟩ := RunsTo.bind hr
  obtain ⟨hw1, hd1⟩ := runs_keep L
    (keeps_iff.mpr (Triple.mapM _ (fun _ => Triple.frame L.plain Framed.freshFVar D) bs))
    hw hd hids
  split at hr
  · rename_i hnd
    dsimp only at hr
    obtain ⟨cacheRef, w2, hmk, hr⟩ := RunsTo.bind hr
    obtain ⟨hw2, hd2⟩ := op_runs L (Op.framed (Framed.mkExprCache _)) hw1 hd1 hmk
    obtain ⟨⟨a, fs⟩, w3, hrun, hr⟩ := RunsTo.bind hr
    have hfin : RunsTo (finishSynth declName [] false fs) mctx mref cctx cref w3 (m, d) w' := hr
    obtain ⟨hm, hdd, -⟩ := finishSynth_returns hfin.mreturns
    have hrun' : RunsTo (bindMixedCertifiedInputs
        (emitLeaves (fun e hint top named => translateExprToWire tenv e hint top named) cacheRef
          (profLogIO b) [("out", instFVars (ids.map Lean.Expr.fvar).toArray 0 body)] none 0)
        (bs.zip ids)
        (start (entryCompilerState false cacheRef) (Sparkle.IR.ModuleName.ofDecl declName)).context
        (start (entryCompilerState false cacheRef) (Sparkle.IR.ModuleName.ofDecl declName)).state)
        mctx mref cctx cref w2 (a, fs) w3 := hrun
    obtain ⟨w4, hw4, hd4, hleaf⟩ := bindMixed_runs L _ (fun _ => false) (fun _ _ => 0)
      (bs.zip ids)
      (start (entryCompilerState false cacheRef) (Sparkle.IR.ModuleName.ofDecl declName))
      w2 (a, fs) w3 hw2 hd2 hrun'
    obtain ⟨wT, wT', wire, sm0, ty, hwT, hdT, htr, hfresh, hst, hty⟩ :=
      emitLeaves_single_runs L hw4 hd4 hleaf
    exact ⟨ids, cacheRef, wT, wT', wire, sm0, ty, fs, hnd.1, hnd.2, hwT, hdT, htr, hfresh,
      hst, hty, hm, hdd⟩
  · exfalso
    have e' : (EST.Out.error _ w1 : EST.Out Exception IO.RealWorld
        (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) = EST.Out.ok (m, d) w' := hr
    cases e'

/-! ## The instance arm, with the circuit states -/

/-- **The instance arm at a tagged constant head, with its states.** From an
invariant world of positive depth: the child pair the arm synthesises is a
`RealChild` of the head, and the rest of the run is a run of `armCont` on
that pair from the arm's own circuit state to the run's end state. (The
built `instanceArm_grow` states the `armCont` run with `∃ st s'`; the shape
proof needs these two states.) -/
theorem instanceArm_run (L : RefLaws mref cref)
    {env : Lean.Environment} {rec : TranslateFn} {e : Lean.Expr} {mn : Lean.Name}
    {us : List Level}
    (hfn : e.getAppFn = .const mn us)
    (htag : Sparkle.Compiler.isHardwareModule env mn = true)
    {hint : String} {top named : Bool} {ctx : CompilerState} {st : CircuitState}
    {w : Void IO.RealWorld} {wire : String} {s' : CircuitState} {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hr : RunsTo (translateInstanceOrFallback env rec e hint top named ctx st)
      mctx mref cctx cref w (wire, s') w') :
    ∃ y : Res, RealChild mref cref mn y ∧
      Returns (armCont rec mn y e hint top named) ctx st wire s' := by
  unfold translateInstanceOrFallback at hr
  rw [hfn] at hr
  try dsimp only at hr
  rw [htag] at hr
  simp only [if_true] at hr
  obtain ⟨⟨sub, s1⟩, w1, r1, r2⟩ := RunsTo.bind hr
  obtain ⟨hs1, rc⟩ := lift_runs r1
  obtain ⟨hreal, -⟩ := childSynthEntry_post L (fun L' => bodyRel L') hw hd rc
  refine ⟨sub, hreal, ?_⟩
  have r2' : RunsTo (armCont rec mn sub e hint top named ctx s1) mctx mref cctx cref w1
      (wire, s') w' := r2
  rw [hs1] at r2'
  exact ⟨mctx, mref, cctx, cref, w1, w', r2'⟩

end Tools.ShippingGateParentRun

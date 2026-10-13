import Tools.ShippingLegacySemSliceEmit
import Tools.ShippingLegacySemBeta
import Tools.ShippingLegacySemChain
import Tools.ShippingLegacySemPre
import Tools.ShippingLegacySemWalk4

variable {tenv : Lean.Environment}

/-! # The accepting `Signal.fst` / `Signal.snd` arms of `Rec.handleTupleProjections`, walked

(Round 23 had this file as statements only: transcriptions `fstArmProg` /
`sndArmProg` and `FstArmIs` / `SndArmIs`, "a run of the handler is a run of
the transcription". That form is dropped: (1) a `match` written here is a
different matcher constant from the handler's, so the transcription is not
definitionally the handler's arm; (2) nothing could be done with a `Returns`
of the transcription that cannot be done with the handler's run itself. The
walk now ends in the PARTS of the run.)

**Program text** (`Sparkle/Compiler/Elab.lean`, `Rec.handleTupleProjections`,
5647–5757):

```
T0  let isTupleName := name == fst || name == snd || name == bundle2 || name == map
    unless isTupleName do return none                                    -- 5654–5660
T1  if name == ``Signal.fst && args.size >= 1 then                       -- 5662
T2    trace[…]
T3    let s := args[args.size-1]!
      let wireS ← translateExprToWire s "s" (isTopLevel := false)        -- isNamed = false
T4    let wireWidth ← CompilerM.getWireWidth wireS                       -- reads an IO.Ref first
T5    let exprType ← cachedInferType e;  let hwType ← inferHWTypeFromSignal exprType
T6    let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
      let width := match hwType with | .bitVector w => w | .bit => 1 | _ => 8
T7    let sType ← cachedInferType s;  let sHWType ← inferHWTypeFromSignal sType
      let typeTotal := match sHWType with | .bitVector w => w | .bit => 1 | _ => 8
      let totalWidth := min wireWidth typeTotal
      let lo := if totalWidth ≥ width then totalWidth - width else 0
      let hi := if totalWidth ≥ 1 then totalWidth - 1 else 0
T8    CompilerM.emitAssign resWire (.slice (.ref wireS) hi lo);  return some resWire
    if name == ``Signal.snd && args.size >= 1 then                       -- 5687
      (T2–T6 the same)
      let actualWidth := min width wireWidth
      let hi := if actualWidth ≥ 1 then actualWidth - 1 else 0
      CompilerM.emitAssign resWire (.slice (.ref wireS) hi 0);  return some resWire
```

**Elaborated shape EXPECTED (not observed)**: `if isTupleName = true then ARMS
else pure none` (either polarity is handled), `ARMS = if (name == fst &&
decide (args.size ≥ 1)) = true then FST else if (… snd …) = true then SND
else …`, each arm a chain of binds after its trace.

**Premises of the walk** (definitions here)

* `ExprHW e hw` — ORACLE: every successful `cachedInferType e` followed by
  `inferHWTypeFromSignal` on its result returns `hw` and leaves the builder
  state. (`cachedInferType` reads the `IO.Ref` type cache before
  `inferType`: the type it returns is whatever the cache holds — the premise
  is about the composite, so it covers a hit and a miss alike.)
* `WireWidthReads ctx s w n` — THE RUN / THE WORLD: every successful
  `CompilerM.getWireWidth w` from `s` returns `n` and leaves `s`.
  `getWireWidth` (210–233) reads the `IO.Ref` `sparkleWireWidthCache` first;
  the builder state's ports are consulted only on a miss. FALSE of a run in
  which the cache holds another width for the name.
* `ArgWidthReads tr ctx a M` — `WireWidthReads … M` for the wire every run
  of the argument's translation returns, at its end state.
* `ArgRunsBody tr ctx e` — THE RUN / THE WORLD: a successful run of the
  caching shim on `e` at the arm's argument flags `("s", false, false)` is a
  run of the body. FALSE of a run that hits a stale entry of the `IO.Ref`
  expression cache; the same gap as `NoSubModule` / the unvalidated hit of
  `legacyShim_returns`.

**Proved here**

* `fstArm_run`, `sndArm_run` — THE ARM, INVERTED to its parts: a successful
  run of the handler on the name, under the oracle and width premises, is a
  run of the argument's translation at `("s", false, false)` returning `sw`,
  then the allocation of a wire of type `hwTypeFromWidth w` and the
  assignment `sliceRhs (M - w) w sw` (fst: the high `w` bits of `M`) resp.
  `sliceRhs 0 w sw` (snd: the low `w` bits); the result is `some` of that
  wire.
* `chain_tuple` — `Rec.translateExprToWireApp` up to the second handler
  (`chain_plain`'s walk, stopped there): a run of the handler from the same
  state, and if it returned a wire, that wire and end state are the
  application's.
* `tuple_reach` — one step of the translator on the node to that handler run
  (`step_run_fallback`, `fallback_eq_arm`, `arm_to_shim`, the shim premise
  `ShimBody`, `pre_plain`, `chain_tuple`).
* `shimBody_named`, `shimBody_of_argRunsBody`.
* `fstNode_runs`, `sndNode_runs` — `SliceRuns` of the node at fuel
  `fuel + 1` over its argument at fuel `fuel`.
* `handlerCase_fst`, `handlerCase_snd` — THE ARMS AS HANDLER CASES, with the
  sub-expression `(a, "s", false)` at the packed value `Value.bits M u`; the
  node's value is `Value.bits w (u.extractLsb' (M - w) w)` resp.
  `Value.bits w (u.extractLsb' 0 w)`. Frame, outcome and order are the
  certified slice lowering's (`sliceNode_spec`, `sliceNode_order`).

A one-bit result (a `Bool` or `BitVec 1` field: a `bit` wire) is carried as
`Value.bits 1 _`: `Outcome` and the entry's `RawValueAt` read a value only
through `kind.width` and `toNat`. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingMixedBinarySoundness (Frame)
open Tools.ShippingUnifiedRecursion
open Tools.ShippingUnifiedProtection
open Tools.ShippingBindingsSoundness (visible)

/-! ## The premises -/

/-- ORACLE: the hardware type of the expression's inferred type, as the arm
computes it (`cachedInferType`, then `inferHWTypeFromSignal`). -/
def ExprHW (e : Lean.Expr) (hw : Sparkle.IR.Type.HWType) : Prop :=
  ∀ (ctx : CompilerState) (s s1 t : CircuitState) (ty : Lean.Expr)
    (h : Sparkle.IR.Type.HWType),
    Returns (cachedInferType e) ctx s ty s1 →
    Returns (inferHWTypeFromSignal ty) ctx s1 h t →
    h = hw ∧ s1 = s ∧ t = s

/-- THE RUN / THE WORLD: the width read for the wire `w` from the state `s`
is `n`. False of a run in which `sparkleWireWidthCache` holds another width
for the name. -/
def WireWidthReads (ctx : CompilerState) (s : CircuitState) (w : String) (n : Nat) : Prop :=
  ∀ (k : Nat) (t : CircuitState),
    Returns (CompilerM.getWireWidth w) ctx s k t → k = n ∧ t = s

/-- `WireWidthReads … M` for the wire the argument's translation returns. -/
def ArgWidthReads (tr : TranslateFn) (ctx : CompilerState) (a : Lean.Expr) (M : Nat) : Prop :=
  ∀ (s : CircuitState) (sw : String) (s1 : CircuitState),
    Returns (tr a "s" false false) ctx s sw s1 → WireWidthReads ctx s1 sw M

/-- THE RUN / THE WORLD: a successful run of the caching shim on `e`, at the
flags the tuple arms translate their argument at, is a run of the body.
False of a run that hits a stale entry of the `IO.Ref` expression cache —
the same gap as `NoSubModule` and the unvalidated hit of
`legacyShim_returns`. -/
def ArgRunsBody (tr : TranslateFn) (ctx : CompilerState) (e : Lean.Expr) : Prop :=
  ∀ (s t : CircuitState) (w : String),
    Returns (Rec.translateExprToWireCached tr e "s" false false) ctx s w t →
    Returns (Rec.translateExprToWireImpl (fun e h t n => tr e h t n) e "s" false false)
      ctx s w t

/-- The shim stage of a node at `(hint, false, named)`: its run is the
body's. -/
def ShimBody (rec : TranslateFn) (ctx : CompilerState) (e : Lean.Expr) (hint : String)
    (named : Bool) : Prop :=
  ∀ (s t : CircuitState) (w : String),
    Returns (Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint false named)
      ctx s w t →
    Returns (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint false named)
      ctx s w t

/-- A named call is not cacheable: the shim runs the body. -/
theorem shimBody_named {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    {hint : String} : ShimBody rec ctx e hint true := by
  intro s t w h
  have hnc : (!true && !e.isFVar && !false) = false := rfl
  rcases legacyShim_returns h with hb | ⟨hc, _, _⟩
  · exact hb
  · exact absurd (hnc.symm.trans hc) (by decide)

/-- At the argument flags the shim stage is the premise `ArgRunsBody`. -/
theorem shimBody_of_argRunsBody {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    (h : ArgRunsBody rec ctx e) : ShimBody rec ctx e "s" false :=
  fun s t w hr => h s t w hr

/-- The closed name tests of a head that reaches the tuple handler: the
body's inline arms (`ImplName`, which has the four of `handleErrorPatterns`),
the three inline guards of the application walk (`GlueName`), and
`handleCircuitMonad`'s five. -/
structure TupleHead (name : Name) : Prop where
  impl : ImplName name
  glue : GlueName name
  notBind : (name == ``Bind.bind) = false
  notPure : (name == ``Pure.pure) = false
  prodMk : (name == ``Prod.mk) = false
  prodFst : (name == ``Prod.fst) = false
  prodSnd : (name == ``Prod.snd) = false

/-! ## The arms, inverted -/

/-- The slice of the `Signal.fst` arm, in the certified lowering's form. -/
theorem fstSlice_eq (sw : String) {M w : Nat} (hw0 : 0 < w) (hwM : w ≤ M) :
    Sparkle.IR.AST.Expr.slice (Sparkle.IR.AST.Expr.ref sw) (M - 1) (M - w) =
      sliceRhs (M - w) w sw := by
  have hh : M - w + w - 1 = M - 1 := by omega
  unfold sliceRhs
  rw [hh]

/-- The slice of the `Signal.snd` arm, in the certified lowering's form. -/
theorem sndSlice_eq (sw : String) {w : Nat} :
    Sparkle.IR.AST.Expr.slice (Sparkle.IR.AST.Expr.ref sw) (w - 1) 0 = sliceRhs 0 w sw := by
  have hh : 0 + w - 1 = w - 1 := by omega
  unfold sliceRhs
  rw [hh]

set_option maxHeartbeats 2000000 in
/-- **The `Signal.fst` arm, inverted to its parts.** -/
theorem fstArm_run {tr : TranslateFn} {e a : Lean.Expr} {name : Name}
    {args : Array Lean.Expr} {hint : String} {named : Bool} {ctx : CompilerState}
    {s t : CircuitState} {r : Option String} {M w : Nat}
    (hn : (name == ``Sparkle.Core.Signal.Signal.fst) = true)
    (hsz : 1 ≤ args.size) (ha : args[args.size - 1]! = a)
    (hE : ExprHW e (Sparkle.IR.Type.hwTypeFromWidth w))
    (hS : ExprHW a (Sparkle.IR.Type.HWType.bitVector M))
    (hW : ArgWidthReads tr ctx a M)
    (hw0 : 0 < w) (hwM : w ≤ M)
    (h : Returns (Rec.handleTupleProjections tr e name args hint named) ctx s r t) :
    ∃ (sw : String) (s1 : CircuitState) (res : String),
      Returns (tr a "s" false false) ctx s sw s1 ∧ r = some res ∧
      res = (CircuitM.makeWire hint (Sparkle.IR.Type.hwTypeFromWidth w) named s1).1 ∧
      t = (CircuitM.emitAssign res (sliceRhs (M - w) w sw)
        (CircuitM.makeWire hint (Sparkle.IR.Type.hwTypeFromWidth w) named s1).2).2 := by
  unfold Rec.handleTupleProjections at h
  -- T0: the name test; the branch that returns `none` contradicts `hn`
  rcases returns_ite h with ⟨hc0, k0⟩ | ⟨hc0, k0⟩
  all_goals try (exfalso; revert hc0; simp [hn]; done)
  -- T1: the `Signal.fst` guard (after a `pure ()` of the `unless`, if any)
  first
    | (have k1 := returns_ite_pos k0
        (by first | simp [hn, hsz] | (rw [hn]; simpa using hsz)))
    | (obtain ⟨u0, s0, hu0, k0'⟩ := Returns.bind k0
       obtain ⟨_, hs0⟩ := Returns.pure hu0
       rw [hs0] at k0'
       have k1 := returns_ite_pos k0'
        (by first | simp [hn, hsz] | (rw [hn]; simpa using hsz)))
  -- T2: the trace
  have k2 := returns_trace_then k1
  -- T3: the argument, at `("s", false, false)`
  obtain ⟨sw, s1, hsub0, k3⟩ := Returns.bind k2
  have hsub : Returns (tr a "s" false false) ctx s sw s1 := by
    rw [← ha]
    exact hsub0
  -- T4: the wire's width (premise: the world)
  obtain ⟨ww, s2, hww, k4⟩ := Returns.bind k3
  obtain ⟨hwwM, hs2⟩ := hW s sw s1 hsub ww s2 hww
  rw [hs2] at k4
  -- T5: the node's hardware type (oracle)
  obtain ⟨ety, s3, hety, k5⟩ := Returns.bind k4
  obtain ⟨hwT, s4, hhw, k6⟩ := Returns.bind k5
  obtain ⟨hT, _, hs4⟩ := hE ctx s1 s3 s4 ety hwT hety hhw
  rw [hs4] at k6
  -- T6: the result wire
  obtain ⟨res, s5, hmk, k7⟩ := Returns.bind k6
  obtain ⟨hres, hs5⟩ := makeWire_returns hmk
  -- T7: the argument's hardware type (oracle)
  obtain ⟨sty, s6, hsty0, k8⟩ := Returns.bind k7
  obtain ⟨shw, s7, hshw, k9⟩ := Returns.bind k8
  have hsty : Returns (cachedInferType a) ctx s5 sty s6 := by
    rw [← ha]
    exact hsty0
  obtain ⟨hST, _, hs7⟩ := hS ctx s5 s6 s7 sty shw hsty hshw
  -- T8: the assignment, the result
  obtain ⟨u, s8, hem, k10⟩ := Returns.bind k9
  obtain ⟨hr, ht⟩ := Returns.pure k10
  have hs8 := emitAssign_returns hem
  rw [hwwM, hST] at hs8
  have hM1 : 1 ≤ M := Nat.le_trans hw0 hwM
  -- the slice bounds, computed
  have hrhs : s8 = (CircuitM.emitAssign res
      (Sparkle.IR.AST.Expr.slice (Sparkle.IR.AST.Expr.ref sw) (M - 1) (M - w)) s7).2 := by
    by_cases h1 : w = 1
    · have hb : hwT = Sparkle.IR.Type.HWType.bit := by
        rw [hT, h1]
        rfl
      rw [hb] at hs8
      rw [h1]
      first
        | exact hs8
        | (simp only [Nat.min_self, ge_iff_le, hM1, ↓reduceIte] at hs8
           exact hs8)
        | (simp [hM1] at hs8
           exact hs8)
        | simpa [hM1] using hs8
    · have hb : hwT = Sparkle.IR.Type.HWType.bitVector w := by
        rw [hT]
        unfold Sparkle.IR.Type.hwTypeFromWidth
        simp [h1]
      rw [hb] at hs8
      first
        | exact hs8
        | (simp only [Nat.min_self, ge_iff_le, hM1, hwM, ↓reduceIte] at hs8
           exact hs8)
        | (simp [hM1, hwM] at hs8
           exact hs8)
        | simpa [hM1, hwM] using hs8
  have hres' : res =
      (CircuitM.makeWire hint (Sparkle.IR.Type.hwTypeFromWidth w) named s1).1 := by
    rw [← hT]
    exact hres
  refine ⟨sw, s1, res, hsub, hr, hres', ?_⟩
  rw [ht, hrhs, fstSlice_eq sw hw0 hwM, hs7, hs5, hT]

set_option maxHeartbeats 2000000 in
/-- **The `Signal.snd` arm, inverted to its parts.** -/
theorem sndArm_run {tr : TranslateFn} {e a : Lean.Expr} {name : Name}
    {args : Array Lean.Expr} {hint : String} {named : Bool} {ctx : CompilerState}
    {s t : CircuitState} {r : Option String} {M w : Nat}
    (hf : (name == ``Sparkle.Core.Signal.Signal.fst) = false)
    (hn : (name == ``Sparkle.Core.Signal.Signal.snd) = true)
    (hsz : 1 ≤ args.size) (ha : args[args.size - 1]! = a)
    (hE : ExprHW e (Sparkle.IR.Type.hwTypeFromWidth w))
    (hW : ArgWidthReads tr ctx a M)
    (hw0 : 0 < w) (hwM : w ≤ M)
    (h : Returns (Rec.handleTupleProjections tr e name args hint named) ctx s r t) :
    ∃ (sw : String) (s1 : CircuitState) (res : String),
      Returns (tr a "s" false false) ctx s sw s1 ∧ r = some res ∧
      res = (CircuitM.makeWire hint (Sparkle.IR.Type.hwTypeFromWidth w) named s1).1 ∧
      t = (CircuitM.emitAssign res (sliceRhs 0 w sw)
        (CircuitM.makeWire hint (Sparkle.IR.Type.hwTypeFromWidth w) named s1).2).2 := by
  unfold Rec.handleTupleProjections at h
  -- T0: the name test
  rcases returns_ite h with ⟨hc0, k0⟩ | ⟨hc0, k0⟩
  all_goals try (exfalso; revert hc0; simp [hf, hn]; done)
  -- T1: the `Signal.fst` guard fails, the `Signal.snd` guard holds
  first
    | (rcases returns_ite k0 with ⟨hcf, _⟩ | ⟨_, k1a⟩
       · exact absurd hcf (by simp [hf])
       have k1 := returns_ite_pos k1a
        (by first | simp [hn, hsz] | (rw [hn]; simpa using hsz)))
    | (obtain ⟨u0, s0, hu0, k0'⟩ := Returns.bind k0
       obtain ⟨_, hs0⟩ := Returns.pure hu0
       rw [hs0] at k0'
       rcases returns_ite k0' with ⟨hcf, _⟩ | ⟨_, k1a⟩
       · exact absurd hcf (by simp [hf])
       have k1 := returns_ite_pos k1a
        (by first | simp [hn, hsz] | (rw [hn]; simpa using hsz)))
  -- T2: the trace
  have k2 := returns_trace_then k1
  -- T3: the argument
  obtain ⟨sw, s1, hsub0, k3⟩ := Returns.bind k2
  have hsub : Returns (tr a "s" false false) ctx s sw s1 := by
    rw [← ha]
    exact hsub0
  -- T4: the wire's width
  obtain ⟨ww, s2, hww, k4⟩ := Returns.bind k3
  obtain ⟨hwwM, hs2⟩ := hW s sw s1 hsub ww s2 hww
  rw [hs2] at k4
  -- T5: the node's hardware type
  obtain ⟨ety, s3, hety, k5⟩ := Returns.bind k4
  obtain ⟨hwT, s4, hhw, k6⟩ := Returns.bind k5
  obtain ⟨hT, _, hs4⟩ := hE ctx s1 s3 s4 ety hwT hety hhw
  rw [hs4] at k6
  -- T6: the result wire
  obtain ⟨res, s5, hmk, k7⟩ := Returns.bind k6
  obtain ⟨hres, hs5⟩ := makeWire_returns hmk
  -- T8: the assignment, the result
  obtain ⟨u, s8, hem, k10⟩ := Returns.bind k7
  obtain ⟨hr, ht⟩ := Returns.pure k10
  have hs8 := emitAssign_returns hem
  rw [hwwM] at hs8
  have hM1 : 1 ≤ M := Nat.le_trans hw0 hwM
  have hrhs : s8 = (CircuitM.emitAssign res
      (Sparkle.IR.AST.Expr.slice (Sparkle.IR.AST.Expr.ref sw) (w - 1) 0) s5).2 := by
    by_cases h1 : w = 1
    · have hb : hwT = Sparkle.IR.Type.HWType.bit := by
        rw [hT, h1]
        rfl
      rw [hb] at hs8
      rw [h1]
      first
        | exact hs8
        | (simp only [Nat.min_eq_left hM1, ge_iff_le, Nat.le_refl, ↓reduceIte] at hs8
           exact hs8)
        | (simp [Nat.min_eq_left hM1] at hs8
           exact hs8)
        | simpa [Nat.min_eq_left hM1] using hs8
    · have hb : hwT = Sparkle.IR.Type.HWType.bitVector w := by
        rw [hT]
        unfold Sparkle.IR.Type.hwTypeFromWidth
        simp [h1]
      rw [hb] at hs8
      have hw1 : 1 ≤ w := hw0
      first
        | exact hs8
        | (simp only [Nat.min_eq_left hwM, ge_iff_le, hw1, ↓reduceIte] at hs8
           exact hs8)
        | (simp [Nat.min_eq_left hwM, hw1] at hs8
           exact hs8)
        | simpa [Nat.min_eq_left hwM, hw1] using hs8
  have hres' : res =
      (CircuitM.makeWire hint (Sparkle.IR.Type.hwTypeFromWidth w) named s1).1 := by
    rw [← hT]
    exact hres
  refine ⟨sw, s1, res, hsub, hr, hres', ?_⟩
  rw [ht, hrhs, sndSlice_eq sw, hs5, hT]

/-! ## From the translator's step to the handler -/

set_option maxHeartbeats 1000000 in
/-- **`Rec.translateExprToWireApp` up to the tuple handler** (the walk of
`chain_plain`, stopped at the second handler). -/
theorem chain_tuple {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr} {name : Name}
    {us : List Level} (hfn : e.getAppFn = .const name us) (th : TupleHead name)
    (hint : String) (named : Bool) (s t : CircuitState) (w : String)
    (h : Returns (Rec.translateExprToWireApp (fun e h t n => rec e h t n) e hint named)
      ctx s w t) :
    ∃ (r2 : Option String) (t2 : CircuitState),
      Returns (Rec.handleTupleProjections (fun e h t n => rec e h t n) e name e.getAppArgs
        hint named) ctx s r2 t2 ∧
      ∀ w2 : String, r2 = some w2 → w = w2 ∧ t = t2 := by
  unfold Rec.translateExprToWireApp at h
  rw [hfn] at h
  -- the trace, then `handleErrorPatterns` under the profile wrapper
  have k1 := returns_trace_then h
  obtain ⟨u, s1, hep, k2⟩ := Returns.bind k1
  have hs1 : s1 = s :=
    handleErrorPatterns_frame (s := s) th.impl.notIte th.impl.notDite th.impl.decRec
      th.impl.decCases u s1 (profHandler_returns hep)
  rw [hs1] at k2
  -- the three inline guards
  rcases returns_ite k2 with ⟨hc, _⟩ | ⟨_, k3⟩
  · exact absurd hc (by
      simp only [th.glue.punit, th.glue.unit, Bool.or_self, Bool.false_and, Bool.false_eq_true,
        not_false_eq_true])
  rcases returns_ite k3 with ⟨hc, _⟩ | ⟨_, k4⟩
  · exact absurd hc (by
      simp only [th.glue.sigPure, th.glue.sigLit, Bool.or_self, Bool.false_and,
        Bool.false_eq_true, not_false_eq_true])
  rcases returns_ite k4 with ⟨hc, _⟩ | ⟨_, k5⟩
  · exact absurd hc (by
      simp only [th.glue.seq, th.glue.fmap, Bool.or_self, Bool.false_and, Bool.false_eq_true,
        not_false_eq_true])
  -- `handleCircuitMonad` returns `none`
  obtain ⟨r1, t1, hh1, m1⟩ := Returns.bind k5
  obtain ⟨hr1, ht1⟩ :=
    handleCircuitMonad_none (s := s) th.notBind th.notPure th.prodMk th.prodFst th.prodSnd
      r1 t1 (profHandler_returns hh1)
  rw [hr1, ht1] at m1
  -- `handleTupleProjections`: its wire is returned
  obtain ⟨r2, t2, hh2, m2⟩ := Returns.bind m1
  refine ⟨r2, t2, profHandler_returns hh2, ?_⟩
  intro w2 hr2
  rw [hr2] at m2
  obtain ⟨hw, ht⟩ := Returns.pure m2
  exact ⟨hw, ht⟩

/-- **One step of the translator on a tuple-projection node, to the
handler's run.** -/
theorem tuple_reach {rec : TranslateFn} {ctx : CompilerState} {f a : Lean.Expr} {name : Name}
    {us : List Level} {hint : String} {named : Bool} {s t : CircuitState} {w : String}
    (hfn : (Lean.Expr.app f a).getAppFn = .const name us) (th : TupleHead name)
    (hkind : fallbackKind (Lean.Expr.app f a) = .other) (nc : NotCore (Lean.Expr.app f a))
    (hplain : PlainHead tenv name) (hmap : HasMappedFVar ctx (Lean.Expr.app f a))
    (hshim : ShimBody rec ctx (Lean.Expr.app f a) hint named)
    (hr : Returns (translateStepWith (translateFallback tenv) rec (Lean.Expr.app f a) hint false named)
      ctx s w t) :
    ∃ (r2 : Option String) (t2 : CircuitState),
      Returns (Rec.handleTupleProjections (fun e h t n => rec e h t n) (Lean.Expr.app f a) name
        (Lean.Expr.app f a).getAppArgs hint named) ctx s r2 t2 ∧
      ∀ w2 : String, r2 = some w2 → w = w2 ∧ t = t2 := by
  have h1 := step_run_fallback nc hr
  rw [fallback_eq_arm rec (Lean.Expr.app f a) hint false named hkind] at h1
  have h2 := arm_to_shim hfn hplain h1
  have h3 := hshim s t w h2
  have h4 := pre_plain hfn th.impl hmap hint false named s t w h3
  exact chain_tuple hfn th hint named s t w h4

/-! ## The node -/

/-- The facts of ONE tuple-projection node `.app f a` with head `name`, its
argument `a` of packed width `M`, its result of width `w`, in the context
`ctx`. Classes: `head`, `arg`, `size`, `kind`, `notCore` — closed
computations on the expression; `mapped` — the body's `whnf` test
(kernel-opaque `Expr.find?`); `nodeHW` — oracle; `widthReads` — the run /
the world; `pos`, `le` — arithmetic. -/
structure TupleNode (tenv : Lean.Environment) (ctx : CompilerState) (name : Name) (f a : Lean.Expr) (M w : Nat) :
    Prop where
  head : ∃ us : List Level, (Lean.Expr.app f a).getAppFn = .const name us
  arg : (Lean.Expr.app f a).getAppArgs[(Lean.Expr.app f a).getAppArgs.size - 1]! = a
  size : 1 ≤ (Lean.Expr.app f a).getAppArgs.size
  kind : fallbackKind (Lean.Expr.app f a) = .other
  notCore : NotCore (Lean.Expr.app f a)
  mapped : HasMappedFVar ctx (Lean.Expr.app f a)
  nodeHW : ExprHW (Lean.Expr.app f a) (Sparkle.IR.Type.hwTypeFromWidth w)
  widthReads : ∀ fuel : Nat, ArgWidthReads (translateFuelFix (translateStep tenv) fuel) ctx a M
  pos : 0 < w
  le : w ≤ M

/-- A name is itself. -/
theorem name_beq_self (n : Name) : (n == n) = true := by
  first
    | exact beq_self_eq_true n
    | simp

/-- **The runs of a `Signal.fst` node are slice-node runs** over its
argument: the high `w` bits. -/
theorem fstNode_runs {ctx : CompilerState} {f a : Lean.Expr} {M w : Nat} {hint : String}
    {named : Bool} (fuel : Nat)
    (th : TupleHead ``Sparkle.Core.Signal.Signal.fst)
    (hplain : PlainHead tenv ``Sparkle.Core.Signal.Signal.fst)
    (nd : TupleNode tenv ctx ``Sparkle.Core.Signal.Signal.fst f a M w)
    (hS : ExprHW a (Sparkle.IR.Type.HWType.bitVector M))
    (hshim : ShimBody (translateFuelFix (translateStep tenv) fuel) ctx (Lean.Expr.app f a) hint named) :
    SliceRuns (translateFuelFix (translateStep tenv) (fuel + 1) (Lean.Expr.app f a) hint false named)
      (translateFuelFix (translateStep tenv) fuel a "s" false false) ctx hint named (M - w) w := by
  intro s t r hr
  have hstep : Returns (translateStepWith (translateFallback tenv)
      (translateFuelFix (translateStep tenv) fuel) (Lean.Expr.app f a) hint false named)
      ctx s r t := hr
  obtain ⟨us, hfn⟩ := nd.head
  obtain ⟨r2, t2, harm, hres⟩ :=
    tuple_reach hfn th nd.kind nd.notCore hplain nd.mapped hshim hstep
  obtain ⟨sw, s1, res, hsub, hr2, hw, ht2⟩ :=
    fstArm_run (name_beq_self _) nd.size nd.arg nd.nodeHW hS (nd.widthReads fuel) nd.pos nd.le
      harm
  obtain ⟨hrr, htt⟩ := hres res hr2
  refine ⟨sw, s1, hsub, ?_, ?_⟩
  · rw [hrr]
    exact hw
  · rw [htt, hrr]
    exact ht2

/-- **The runs of a `Signal.snd` node are slice-node runs** over its
argument: the low `w` bits. -/
theorem sndNode_runs {ctx : CompilerState} {f a : Lean.Expr} {M w : Nat} {hint : String}
    {named : Bool} (fuel : Nat)
    (th : TupleHead ``Sparkle.Core.Signal.Signal.snd)
    (hplain : PlainHead tenv ``Sparkle.Core.Signal.Signal.snd)
    (hne : ((``Sparkle.Core.Signal.Signal.snd : Name) == ``Sparkle.Core.Signal.Signal.fst) = false)
    (nd : TupleNode tenv ctx ``Sparkle.Core.Signal.Signal.snd f a M w)
    (hshim : ShimBody (translateFuelFix (translateStep tenv) fuel) ctx (Lean.Expr.app f a) hint named) :
    SliceRuns (translateFuelFix (translateStep tenv) (fuel + 1) (Lean.Expr.app f a) hint false named)
      (translateFuelFix (translateStep tenv) fuel a "s" false false) ctx hint named 0 w := by
  intro s t r hr
  have hstep : Returns (translateStepWith (translateFallback tenv)
      (translateFuelFix (translateStep tenv) fuel) (Lean.Expr.app f a) hint false named)
      ctx s r t := hr
  obtain ⟨us, hfn⟩ := nd.head
  obtain ⟨r2, t2, harm, hres⟩ :=
    tuple_reach hfn th nd.kind nd.notCore hplain nd.mapped hshim hstep
  obtain ⟨sw, s1, res, hsub, hr2, hw, ht2⟩ :=
    sndArm_run hne (name_beq_self _) nd.size nd.arg nd.nodeHW (nd.widthReads fuel) nd.pos nd.le
      harm
  obtain ⟨hrr, htt⟩ := hres res hr2
  refine ⟨sw, s1, hsub, ?_, ?_⟩
  · rw [hrr]
    exact hw
  · rw [htt, hrr]
    exact ht2

/-- **The `Signal.fst` arm is a handler case**: the argument at
`("s", false)` with the packed value `u`, the node at the high `w` bits. -/
theorem handlerCase_fst {ctx : CompilerState} {inputs : FVarId → Option Value}
    {hint : String} {named : Bool} {f a : Lean.Expr} {M w : Nat} {u : BitVec M}
    (th : TupleHead ``Sparkle.Core.Signal.Signal.fst)
    (hplain : PlainHead tenv ``Sparkle.Core.Signal.Signal.fst)
    (nd : TupleNode tenv ctx ``Sparkle.Core.Signal.Signal.fst f a M w)
    (hS : ExprHW a (Sparkle.IR.Type.HWType.bitVector M))
    (hshim : ∀ fuel : Nat,
      ShimBody (translateFuelFix (translateStep tenv) fuel) ctx (Lean.Expr.app f a) hint named) :
    HandlerCase tenv ctx inputs hint named (Lean.Expr.app f a)
      (Value.bits w (BitVec.extractLsb' (M - w) w u))
      (fun h' n' e' v' => h' = "s" ∧ n' = false ∧ e' = a ∧ v' = Value.bits M u) where
  spec := by
    intro fuel we mems initial ih
    have hle := nd.le
    exact sliceNode_spec nd.pos (by omega) (fstNode_runs fuel th hplain nd hS (hshim fuel))
      (ih "s" false a (Value.bits M u) ⟨rfl, rfl, rfl, rfl⟩)
  order := by
    intro fuel we mems initial ih io
    exact sliceNode_order nd.pos (fstNode_runs fuel th hplain nd hS (hshim fuel))
      (ih "s" false a (Value.bits M u) ⟨rfl, rfl, rfl, rfl⟩)
      (io "s" false a (Value.bits M u) ⟨rfl, rfl, rfl, rfl⟩)

/-- **The `Signal.snd` arm is a handler case**: the node at the low `w`
bits. -/
theorem handlerCase_snd {ctx : CompilerState} {inputs : FVarId → Option Value}
    {hint : String} {named : Bool} {f a : Lean.Expr} {M w : Nat} {u : BitVec M}
    (th : TupleHead ``Sparkle.Core.Signal.Signal.snd)
    (hplain : PlainHead tenv ``Sparkle.Core.Signal.Signal.snd)
    (hne : ((``Sparkle.Core.Signal.Signal.snd : Name) == ``Sparkle.Core.Signal.Signal.fst) = false)
    (nd : TupleNode tenv ctx ``Sparkle.Core.Signal.Signal.snd f a M w)
    (hshim : ∀ fuel : Nat,
      ShimBody (translateFuelFix (translateStep tenv) fuel) ctx (Lean.Expr.app f a) hint named) :
    HandlerCase tenv ctx inputs hint named (Lean.Expr.app f a)
      (Value.bits w (BitVec.extractLsb' 0 w u))
      (fun h' n' e' v' => h' = "s" ∧ n' = false ∧ e' = a ∧ v' = Value.bits M u) where
  spec := by
    intro fuel we mems initial ih
    have hle := nd.le
    exact sliceNode_spec nd.pos (by omega) (sndNode_runs fuel th hplain hne nd (hshim fuel))
      (ih "s" false a (Value.bits M u) ⟨rfl, rfl, rfl, rfl⟩)
  order := by
    intro fuel we mems initial ih io
    exact sliceNode_order nd.pos (sndNode_runs fuel th hplain hne nd (hshim fuel))
      (ih "s" false a (Value.bits M u) ⟨rfl, rfl, rfl, rfl⟩)
      (io "s" false a (Value.bits M u) ⟨rfl, rfl, rfl, rfl⟩)

end Tools.ShippingLegacySem

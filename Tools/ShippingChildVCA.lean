import Tools.ShippingChildFresh
import Tools.ShippingChildVC
-- BUILT by the integrator: vc1 exit 0 (315 jobs) (round par/vert, base 777630e9). Isolated (only Tools/ShippingChildVertA.lean
-- uses it). No `sorry`, no `axiom`, no `native_decide`, no new law; every law used is a field of
-- `RefLawsAOps` (no `RefLaws`, no `RefLawsCore`, no `RefLawsCore.toAOps`).
-- Writing-time guesses:
--  V1 `cases hm : p mctx mref cctx cref w` + `rw [hm] at h` on the `keeps_iff`/`Triple` match (the
--     `tripleO_op` pattern, ShippingChildBalance.lean);
--  V2 `O.frameQ hA _ FramedA.depthGet w hq` infers `Fresh` from `O` (FramedA's implicit index);
--  V3 `rw [hk.2.2]` in `show a = dv w1` with `hk.2.2 : dv w1 = dv w` then
--     `exact runsTo_get_readOf _ hm` (`dv w` unfolds to `readOf sparkleSynthDepth w` by `exact`);
--  V4 `(Throws.err (α := α) msg)` / `(Op.throwErr (α := α) msg hmsg)` as in ShippingChildBalance;
--  V5 the `Nat.add_sub_cancel` rewrite is not needed here (`tripleJ_depthModify` concludes `f D`).

/-! # VC combinators under the restricted laws (`RefLawsAOps`)

The law-INDEPENDENT rules are reused directly (they mention no law):
`Triple.bind`/`bindQ`/`pure`/`ite`/`tryFinally`/`conseq`/`of_runs`/`mapM`, `keeps_iff`,
`throwError_not_runs` (Tools/ShippingChildKeeps.lean), `Triple.throw`
(ShippingChildHarness.lean), `Keeps.bind`/`pure`/`dite`/`throw`/`mapM`
(ShippingChildVC.lean). What depends on a law is re-proved here from
`RefLawsAOps` fields, for an invariant `I` that is STABLE: it implies `quiet`
and is kept by every world change leaving the three tracked values and
quietness (`StableA`). `JQ q D` (quiet, synthesis ref `some synthesizeChild`,
depth `D`) is the invariant of the vertical path; `OutQ q = JQ q 0`.

The telescope family (`RefLawsATele`) is NOT used here (the path needs none). -/

namespace Tools.ShippingChildVCA
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
  {Fresh : (σ : Type) → IO.Ref σ → Prop}

/-- An invariant the restricted laws can carry: it implies quietness, and it
survives every world change that leaves the three tracked values and
quietness. -/
def StableA (quiet : Void IO.RealWorld → Prop) (I : Void IO.RealWorld → Prop) : Prop :=
  (∀ w, I w → quiet w) ∧
  (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') → I w → I w')

/-- The invariant of the vertical path: quiet, the synthesis ref holds
`synthesizeChild`, the depth is `D` (no cache half: the outermost entry
clears the cache). -/
def JQ (quiet : Void IO.RealWorld → Prop) (D : Nat) (w : Void IO.RealWorld) : Prop :=
  quiet w ∧ sv w = some synthesizeChild ∧ dv w = D

/-- `JQ` with the thrown exception in the class. -/
def EQ (quiet : Void IO.RealWorld → Prop) (D : Nat) : Exception → Void IO.RealWorld → Prop :=
  fun e w => JQ quiet D w ∧ OkExc e

theorem stableA_JQ (quiet : Void IO.RealWorld → Prop) (D : Nat) : StableA quiet (JQ quiet D) :=
  ⟨fun _ h => h.1, fun _ _ _ hs hd hq h => ⟨hq h.1, hs.trans h.2.1, hd.trans h.2.2⟩⟩

theorem outQ_iff_JQ (quiet : Void IO.RealWorld → Prop) (w : Void IO.RealWorld) :
    OutQ quiet w ↔ JQ quiet 0 w :=
  Iff.rfl

/-! ## Per-operation steps -/

/-- A provenance-framed operation keeps a stable invariant (exceptions in the
class) — `keeps_outQ` generalised from `OutQ` to any stable `I`. -/
theorem keepsA_framed (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) {α : Type} {p : MetaM α}
    (hp : FramedA Fresh p) : Keeps mctx mref cctx cref I p := by
  intro w hw
  have hq := hS.1 w hw
  have hk := O.frame hA p hp w hq
  have hq' := O.frameQ hA p hp w hq
  refine ⟨hS.2 w _ hk.1 hk.2.1 hk.2.2 (fun _ => hq') hw, ?_⟩
  unfold ErrOk
  cases hm : p mctx mref cctx cref w with  -- guess: V1
  | ok a w1 => exact True.intro
  | error e w1 => exact O.excOk hA p (.framed hp.toFramed) w e w1 hq hm

/-- A diagnostic operation keeps a stable invariant (`O.diag`). -/
theorem keepsA_diag (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) {α : Type} {p : MetaM α}
    (hp : Diag p) : Keeps mctx mref cctx cref I p := by
  intro w hw
  have hq := hS.1 w hw
  have hk := O.diag hA p hp w hq
  refine ⟨hS.2 w _ hk.1.1 hk.1.2.1 hk.1.2.2 (fun _ => hk.2) hw, ?_⟩
  unfold ErrOk
  cases hm : p mctx mref cctx cref w with
  | ok a w1 => exact True.intro
  | error e w1 => exact O.excOk hA p (.diag hp) w e w1 hq hm

/-- `throwError` of a message in the class: no returning run; the throwing
run keeps a stable invariant (`O.frameT`, `O.excOk`). -/
theorem tripleA_throwErr (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) {α : Type} (msg : MessageData)
    (hmsg : OkMsg msg) {Q : α → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref I (Lean.throwError msg : MetaM α) Q (fun e w => I w ∧ OkExc e) := by
  intro w hw
  have hq := hS.1 w hw
  have hk := O.frameT hA _ (Throws.err (α := α) msg) w hq  -- guess: V4
  unfold endW at hk
  cases hm : (Lean.throwError msg : MetaM α) mctx mref cctx cref w with
  | ok a w1 => exact (throwError_not_runs msg hm).elim
  | error e w1 =>
    rw [hm] at hk
    exact ⟨hS.2 w _ hk.1.1 hk.1.2.1 hk.1.2.2 (fun _ => hk.2) hw,
      O.excOk hA _ (Op.throwErr (α := α) msg hmsg) w e w1 hq hm⟩

/-- The depth read: a stable invariant is kept, and the value read is the
depth of the end world. -/
theorem tripleA_depthGet (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) :
    Triple mctx mref cctx cref I (ST.Ref.get sparkleSynthDepth : MetaM Nat)
      (fun d w => I w ∧ d = dv w) (fun e w => I w ∧ OkExc e) := by
  intro w hw
  have hK := keeps_iff.mp (keepsA_framed O hA hS FramedA.depthGet) w hw
  have hk := O.frame hA _ FramedA.depthGet w (hS.1 w hw)  -- guess: V2
  unfold endW at hk
  cases hm : (ST.Ref.get sparkleSynthDepth : MetaM Nat) mctx mref cctx cref w with
  | ok a w1 =>
    rw [hm] at hK hk
    refine ⟨hK, ?_⟩
    show a = dv w1
    rw [hk.2.2]  -- guess: V3
    exact runsTo_get_readOf _ hm
  | error e w1 => rw [hm] at hK; exact hK

/-- The cache's clear keeps `JQ` (it cannot fail): `O.cacheSet`,
`O.cacheSetQ`. -/
theorem tripleJ_clear (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQ O.quiet D) (sparkleChildCache.set {} : MetaM Unit)
      (fun _ => JQ O.quiet D) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := O.cacheSet hA _ _ _ _ h hw.1
    exact ⟨O.cacheSetQ hA _ _ _ _ h hw.1, hk.2.1.trans hw.2.1, hk.2.2.trans hw.2.2⟩

/-- Setting the depth moves `JQ` to that depth (it cannot fail):
`O.depthSet`, `O.depthSetQ`. -/
theorem tripleJ_depthSet (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D v : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQ O.quiet D) (ST.Ref.set sparkleSynthDepth v : MetaM Unit)
      (fun _ => JQ O.quiet v) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := O.depthSet hA _ _ _ _ h hw.1
    exact ⟨O.depthSetQ hA _ _ _ _ h hw.1, hk.2.1.trans hw.2.1, hk.2.2⟩

/-- Modifying the depth moves `JQ` to `f D` (it cannot fail):
`RefLawsAOps.depthModify'` for the values; quietness from `O.frameQ` of the
read and `O.depthSetQ` of the write (`modify_split`). -/
theorem tripleJ_depthModify (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) (f : Nat → Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQ O.quiet D) (ST.Ref.modify sparkleSynthDepth f : MetaM Unit)
      (fun _ => JQ O.quiet (f D)) R :=
  Triple.of_runs (refModify_runs _ _) fun w u w' hw h => by
    have hk := O.depthModify' hA f hw.1 h
    have hq' : O.quiet w' := by
      obtain ⟨w1, hg, hs⟩ := modify_split sparkleSynthDepth f h
      have hq1 := O.frameQ hA _ FramedA.depthGet w hw.1
      rw [endW_of_runs hg] at hq1
      exact O.depthSetQ hA _ _ _ _ hs hq1
    refine ⟨hq', hk.2.1.trans hw.2.1, ?_⟩
    rw [hk.2.2, hw.2.2]

/-! ## `IO.mkRef` threads provenance -/

/-- **The allocation, with provenance of its result**: from a stable
invariant, a returning `IO.mkRef v` (framed by `FramedA.mkExprCache`) ends in
`I` with `MkRefd` of the ref it returned. -/
theorem tripleA_mkExprCache (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) (v : Lean.ExprStructMap String) :
    Triple mctx mref cctx cref I (IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String)))
      (fun r w => I w ∧ MkRefd _ r) (fun e w => I w ∧ OkExc e) := by
  intro w hw
  have hK := keeps_iff.mp (keepsA_framed O hA hS (FramedA.mkExprCache v)) w hw
  cases hm : (IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String))) mctx mref cctx cref w with
  | ok r w1 => rw [hm] at hK; exact ⟨hK, mkRefd_of_runs hm⟩
  | error e w1 => rw [hm] at hK; exact hK

/-- **`r ← IO.mkRef v; k r`**: the continuation need only keep the invariant
for refs WITH PROVENANCE (`MkRefd`) — the premise under which the new
boundary's local-ref laws (`FramedA MkRefd (.exprCacheGet r hr)`, …) apply. -/
theorem keepsA_mkExprCache_bind (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (v : Lean.ExprStructMap String) {β : Type}
    {k : IO.Ref (Lean.ExprStructMap String) → MetaM β}
    (hk : ∀ r, MkRefd _ r → Keeps mctx mref cctx cref I (k r)) :
    Keeps mctx mref cctx cref I
      ((IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String))) >>= k) :=
  keeps_iff.mpr (Triple.bindQ (φ := MkRefd _) (tripleA_mkExprCache O hA hS v)
    fun r hr => keeps_iff.mp (hk r hr))

/-- A use of such a ref: the cache read of an `MkRefd` ref keeps a stable
invariant — the law applied is `O.frame` at `FramedA.exprCacheGet r hr`,
whose provenance premise `hr` is now DISCHARGED by the threading above
(not `True`). -/
theorem keepsA_exprCacheGet (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (r : IO.Ref (Lean.ExprStructMap String)) (hr : MkRefd _ r) :
    Keeps mctx mref cctx cref I (ST.Ref.get r : MetaM (Lean.ExprStructMap String)) :=
  keepsA_framed O hA hS (FramedA.exprCacheGet r hr)

end Tools.ShippingChildVCA

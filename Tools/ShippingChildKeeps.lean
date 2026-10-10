import Tools.ShippingChildInv

/-! # The real entry keeps the child invariant — on every outcome

`Triple P m Q R`: from a world satisfying `P`, a run of `m` that RETURNS `a`
ends in a world satisfying `Q a`, and one that THROWS ends in a world
satisfying `R`. Nothing is said only of successful runs: a failure's side
effects are part of the statement, which is what lets a caller that catches
the failure, or a `finally`, continue from the failing run's world.

Proved here, from the generic laws (`RefLaws`) alone unless stated:

* the rules of the calculus for the `MetaM` operations the entry uses
  (`pure`, bind, `if`, `try … finally`, a framed operation, a ref operation —
  which cannot fail, `throwError` — which cannot return);
* **the memoised entry** (`child_keeps`): IF the real entry keeps the
  invariant at depth `D`, so does `synthesizeChild` — a hit leaves the world;
  a miss runs the entry (kept, also when it throws) and then modifies the
  cache as it is AFTER that run, inserting a `RealChild`;
* **the entry's shell** (`core_keeps` / `full_keeps`): IF `synthesizeFromConst`
  keeps the invariant at depth `D + 1`, the entry keeps it at depth `D` —
  through the prefix, the depth guard, the clear or the nested resets, the
  depth bump, the body, and the `finally` (which runs, and restores the
  depth, whether the body returned or threw);
* **the recursion** (`entry_keeps`): from `BodyRel` — the body keeps the
  invariant PROVIDED the memoised child entry does — the entry keeps it at
  every depth. The induction is on `sparkleSynthDepthLimit - D`: at the limit
  the entry throws before doing anything; below it, the body runs at `D + 1`,
  where the child entry keeps the invariant by the induction hypothesis and
  `child_keeps`. No circular use of the conclusion.

`BodyRel` and `HarnessRel` are the two premises (see
`Tools/ShippingChildInv.lean`). -/
namespace Tools.ShippingChildInv
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section Calculus
variable (mctx mref cctx cref)

/-- From `P`: a returning run ends in `Q a`, a throwing run in `R`. -/
def Triple {α : Type} (P : Void IO.RealWorld → Prop) (m : MetaM α)
    (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop) : Prop :=
  ∀ w, P w → match m mctx mref cctx cref w with
    | .ok a w' => Q a w'
    | .error _ w' => R w'

end Calculus

theorem keeps_iff {α : Type} {I : Void IO.RealWorld → Prop} {m : MetaM α} :
    Keeps mctx mref cctx cref I m ↔ Triple mctx mref cctx cref I m (fun _ => I) I := by
  constructor
  · intro h w hw
    have := h w hw
    unfold endW at this
    split <;> rename_i heq <;> rw [heq] at this <;> exact this
  · intro h w hw
    have := h w hw
    unfold endW
    split <;> rename_i heq <;> rw [heq] at this <;> exact this

theorem Triple.conseq {α : Type} {P P' : Void IO.RealWorld → Prop} {m : MetaM α}
    {Q Q' : α → Void IO.RealWorld → Prop} {R R' : Void IO.RealWorld → Prop}
    (h : Triple mctx mref cctx cref P m Q R) (hP : ∀ w, P' w → P w)
    (hQ : ∀ a w, Q a w → Q' a w) (hR : ∀ w, R w → R' w) :
    Triple mctx mref cctx cref P' m Q' R' := by
  intro w hw
  have := h w (hP w hw)
  split <;> rename_i heq <;> rw [heq] at this
  · exact hQ _ _ this
  · exact hR _ this

theorem Triple.pure {α : Type} {P : Void IO.RealWorld → Prop} {a : α}
    {Q : α → Void IO.RealWorld → Prop} {R : Void IO.RealWorld → Prop} (h : ∀ w, P w → Q a w) :
    Triple mctx mref cctx cref P (Pure.pure a : MetaM α) Q R := by
  intro w hw
  change match (EST.Out.ok a w : EST.Out Exception IO.RealWorld α) with
    | .ok a w' => Q a w' | .error _ w' => R w'
  exact h w hw

theorem Triple.bind {α β : Type} {P : Void IO.RealWorld → Prop} {m : MetaM α} {f : α → MetaM β}
    {Q : α → Void IO.RealWorld → Prop} {Q' : β → Void IO.RealWorld → Prop}
    {R : Void IO.RealWorld → Prop}
    (h1 : Triple mctx mref cctx cref P m Q R)
    (h2 : ∀ a, Triple mctx mref cctx cref (Q a) (f a) Q' R) :
    Triple mctx mref cctx cref P (m >>= f) Q' R := by
  intro w hw
  have h := h1 w hw
  change match (EST.bind (m mctx mref cctx cref) fun a => f a mctx mref cctx cref) w with
    | .ok a w' => Q' a w' | .error _ w' => R w'
  unfold EST.bind
  cases hm : m mctx mref cctx cref w with
  | ok a w1 => rw [hm] at h; exact h2 a w1 h
  | error e w1 => rw [hm] at h; exact h

/-- A bind whose first run also establishes a fact `φ` of its result. -/
theorem Triple.bindQ {α β : Type} {P P' : Void IO.RealWorld → Prop} {m : MetaM α}
    {f : α → MetaM β} {φ : α → Prop} {Q' : β → Void IO.RealWorld → Prop}
    {R : Void IO.RealWorld → Prop}
    (h1 : Triple mctx mref cctx cref P m (fun a w => P' w ∧ φ a) R)
    (h2 : ∀ a, φ a → Triple mctx mref cctx cref P' (f a) Q' R) :
    Triple mctx mref cctx cref P (m >>= f) Q' R :=
  Triple.bind h1 fun a w hw => h2 a hw.2 w hw.1

theorem Triple.ite {α : Type} {c : Prop} [Decidable c] {P : Void IO.RealWorld → Prop}
    {a b : MetaM α} {Q : α → Void IO.RealWorld → Prop} {R : Void IO.RealWorld → Prop}
    (ha : c → Triple mctx mref cctx cref P a Q R) (hb : ¬c → Triple mctx mref cctx cref P b Q R) :
    Triple mctx mref cctx cref P (if c then a else b) Q R := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

/-- `try x finally fin`: `fin` runs from the world `x` ends in, whether `x`
returned or threw; the whole run ends where `fin` ends. -/
theorem Triple.tryFinally {α β : Type} {P M N : Void IO.RealWorld → Prop} {x : MetaM α}
    {fin : MetaM β}
    (hx : Triple mctx mref cctx cref P x (fun _ => M) M)
    (hf : Triple mctx mref cctx cref M fin (fun _ => N) N) :
    Triple mctx mref cctx cref P (_root_.tryFinally x fin) (fun _ => N) N := by
  intro w hw
  have h1 := hx w hw
  change match (EST.bind (@MonadFinally.tryFinally' (EST Exception IO.RealWorld) _ _ _
      (x mctx mref cctx cref) (fun _ => fin mctx mref cctx cref)) (fun p => EST.pure p.1)) w with
    | .ok _ w' => N w' | .error _ w' => N w'
  unfold EST.bind
  simp only [MonadFinally.tryFinally']
  cases hxw : x mctx mref cctx cref w with
  | ok a w1 =>
    rw [hxw] at h1
    have h2 := hf w1 h1
    dsimp only
    cases hfw : fin mctx mref cctx cref w1 <;> rw [hfw] at h2 <;> simpa [EST.pure] using h2
  | error e w1 =>
    rw [hxw] at h1
    have h2 := hf w1 h1
    dsimp only
    cases hfw : fin mctx mref cctx cref w1 <;> rw [hfw] at h2 <;> simpa [EST.pure] using h2

/-- A run that always returns: its triple from its successful runs. -/
theorem Triple.of_runs {α : Type} {P : Void IO.RealWorld → Prop} {m : MetaM α}
    {Q : α → Void IO.RealWorld → Prop} {R : Void IO.RealWorld → Prop}
    (total : ∀ w, ∃ a w', RunsTo m mctx mref cctx cref w a w')
    (h : ∀ w a w', P w → RunsTo m mctx mref cctx cref w a w' → Q a w') :
    Triple mctx mref cctx cref P m Q R := by
  intro w hw
  obtain ⟨a, w', hr⟩ := total w
  have := h w a w' hw hr
  unfold RunsTo at hr
  rw [hr]; exact this

/-! ## The invariant under the laws -/

variable (L : RefLaws mctx mref cctx cref)

theorem J_same {D : Nat} {w w'}
    (hk : L.val w' = L.val w ∧ L.sval w' = L.sval w ∧ L.dval w' = L.dval w) (h : J L D w) :
    J L D w' := by
  unfold J InvV; rw [hk.1, hk.2.1, hk.2.2]; exact h

/-- A framed operation keeps the invariant at its depth, on every outcome. -/
theorem Triple.frame {α : Type} {p : MetaM α} (hp : Framed p) (D : Nat) :
    Triple mctx mref cctx cref (J L D) p (fun _ => J L D) (J L D) :=
  keeps_iff.mp fun w hw => J_same L (L.frame p hp w) hw

/-- A framed operation, with a fact of its result on a successful run. -/
theorem Triple.frameQ {α : Type} {p : MetaM α} (hp : Framed p) (D : Nat) {φ : α → Prop}
    (hφ : ∀ w a w', J L D w → RunsTo p mctx mref cctx cref w a w' → φ a) :
    Triple mctx mref cctx cref (J L D) p (fun a w => J L D w ∧ φ a) (J L D) := by
  intro w hw
  have hk := L.frame p hp w
  unfold endW at hk
  cases hm : p mctx mref cctx cref w with
  | ok a w1 => rw [hm] at hk; exact ⟨J_same L hk hw, hφ w a w1 hw hm⟩
  | error e w1 => rw [hm] at hk; exact J_same L hk hw

/-- `throwError` does not return. -/
theorem throwError_not_runs {α : Type} (msg : MessageData) {w a w'}
    (h : RunsTo (Lean.throwError msg : MetaM α) mctx mref cctx cref w a w') : False := by
  unfold Lean.throwError at h
  obtain ⟨_, _, -, h⟩ := RunsTo.bind h
  obtain ⟨_, _, -, h⟩ := RunsTo.bind h
  exact MReturns.throw h.mreturns

/-- `throwError`: no returning run; the throwing run keeps the invariant. -/
theorem Triple.throwErr {α : Type} (msg : MessageData) (D : Nat)
    {Q : α → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (J L D) (Lean.throwError msg : MetaM α) Q (J L D) := by
  intro w hw
  have hk := L.frame _ (Framed.throwErr (α := α) msg) w
  unfold endW at hk
  cases hm : (Lean.throwError msg : MetaM α) mctx mref cctx cref w with
  | ok a w1 => exact (throwError_not_runs msg hm).elim
  | error e w1 => rw [hm] at hk; exact J_same L hk hw

/-- The cache's clear keeps the invariant at its depth (it cannot fail). -/
theorem Triple.clear (D : Nat) {R : Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (J L D) (sparkleChildCache.set {} : MetaM Unit)
      (fun _ => J L D) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    obtain ⟨hv, hs, hd⟩ := L.cacheSet _ _ _ _ h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hv]; exact cacheInv_empty
    · rw [hs]; exact hw.1.2
    · rw [hd]; exact hw.2

/-- Setting the depth moves the invariant to that depth (it cannot fail). -/
theorem Triple.depthSet (D v : Nat) {R : Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (J L D) (ST.Ref.set sparkleSynthDepth v : MetaM Unit)
      (fun _ => J L v) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    obtain ⟨hv, hs, hd⟩ := L.depthSet _ _ _ _ h
    refine ⟨⟨?_, ?_⟩, hd⟩
    · rw [hv]; exact hw.1.1
    · rw [hs]; exact hw.1.2

theorem Triple.depthModify (D : Nat) (f : Nat → Nat) {R : Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (J L D) (ST.Ref.modify sparkleSynthDepth f : MetaM Unit)
      (fun _ => J L (f D)) R :=
  Triple.of_runs (refModify_runs _ _) fun w u w' hw h => by
    obtain ⟨hv, hs, hd⟩ := L.depthModify _ _ _ _ h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hv]; exact hw.1.1
    · rw [hs]; exact hw.1.2
    · rw [hd, hw.2]

/-! ## The memoised entry -/

/-- **The memoised entry keeps the invariant, given that the real entry
does** — on every outcome. A hit leaves the world. A miss runs the real entry
from an invariant world: if it throws, the world it ends in satisfies the
invariant and `synthesizeChild` throws from there; if it returns, its result
is a `RealChild` and the cache AS IT IS after that run gets it inserted. -/
theorem child_keeps (D : Nat)
    (hE : ∀ c, Keeps mctx mref cctx cref (J L D) (synthesizeCombinational c)) :
    ChildKeeps L D := by
  intro c
  rw [keeps_iff]
  unfold synthesizeChild
  refine Triple.bind (Q := fun m w1 => J L D w1 ∧ m = L.val w1)
    (Triple.of_runs (refGet_runs _) fun w m w' hw h =>
      ⟨J_same L (L.same .cacheGet h) hw, by rw [L.cacheGet _ _ _ h, (L.same .cacheGet h).1]⟩) ?_
  intro m
  cases hc : m.get? c with
  | some r =>
    simp only [hc]
    exact Triple.pure fun w hw => hw.1
  | none =>
    simp only [hc]
    refine Triple.bind (Q := fun r w2 => J L D w2 ∧ RealChild mctx mref cctx cref c r) ?_ ?_
    · intro w1 hw1
      have hk := hE c w1 hw1.1
      unfold endW at hk
      cases hm : synthesizeCombinational c mctx mref cctx cref w1 with
      | ok r w2 => rw [hm] at hk; exact ⟨hk, RealChild.of_inv (invW_of_invV L hw1.1.1) hm⟩
      | error e w2 => rw [hm] at hk; exact hk
    · intro r
      refine Triple.bind (Q := fun _ w3 => J L D w3)
        (Triple.of_runs (refModify_runs _ _) fun w u w' hw h => ?_) ?_
      · obtain ⟨hv, hs, hd⟩ := L.cacheModify _ _ _ _ h
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hv]; exact cacheInv_insert hw.1.1.1 hw.2
        · rw [hs]; exact hw.1.1.2
        · rw [hd]; exact hw.1.2
      · intro _
        exact Triple.pure fun w hw => hw

/-! ## The entry's shell -/

/-- Prefix steps that keep the invariant at depth `D`: a `pure`, the cache's
clear, a set or a read of another per-synthesis ref. -/
macro "tpure " L:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (Triple.pure (Q := fun _ => J $L $D) (fun w hw => hw)) ?_; intro _))
macro "tclear " L:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (Triple.clear $L $D) ?_; intro _))
macro "tset " L:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (Triple.frame $L (Framed.sideSet _ ?s) $D) ?_
   case s => constructor
   intro _))
macro "tget " L:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (Triple.frame $L (Framed.sideGet ?s) $D) ?_
   case s => constructor
   intro _))

/-- The `finally` of the entry: the depth goes back down, and a nested run
restores its parent's two per-module maps. -/
theorem fin_triple (D d : Nat) (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat) :
    Triple mctx mref cctx cref (J L (D + 1))
      (do
        ST.Ref.modify sparkleSynthDepth fun x => x - 1
        if (d != 0) = true then do
            ST.Ref.set sparkleFvarValueMap m1
            ST.Ref.set sparkleWireWidthCache m2
          else pure () : MetaM Unit)
      (fun _ => J L D) (J L D) := by
  refine Triple.bind (Triple.depthModify L (D + 1) _) ?_
  intro _
  simp only [Nat.add_sub_cancel]
  refine Triple.ite (fun _ => ?_) (fun _ => Triple.pure fun w hw => hw)
  refine Triple.bind (Triple.frame L (Framed.sideSet _ .fvarValue) D) ?_
  intro _
  exact Triple.frame L (Framed.sideSet _ .wireWidth) D

/-- **The core entry keeps the invariant at depth `D`, given that
`synthesizeFromConst` does at depth `D + 1`** — on every outcome. At the depth
limit the entry throws before changing anything (so the premise is asked
only below the limit). Otherwise: the prefix, the clear or the nested resets,
the depth bump to `D + 1`, the body — which may return or throw — and the
`finally`, which runs from whichever world the body ended in and brings the
depth back to `D`. -/
theorem core_keeps (D : Nat) (declName : Name)
    (hbody : D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (J L (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire e h t n) (profLogIO b)
          declName [] false true ci isInst)) :
    Keeps mctx mref cctx cref (J L D) (synthesizeCombinationalCore declName [] false) := by
  rw [keeps_iff]
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (Triple.frame L (Framed.ioEnv _) D) ?_
  intro prof
  refine Triple.bind (Triple.frame L (Framed.profLog prof.isSome _) D) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = D)
    (Triple.frameQ L Framed.depthGet D fun w d w' hw h => by rw [L.depthGet _ _ _ h]; exact hw.2) ?_
  intro d hd
  subst hd
  refine Triple.ite (fun _ => ?_) (fun hlt => ?_)
  · -- at the limit: the entry throws
    refine Triple.bind (Q := fun _ _ => False) (Triple.throwErr L _ d) ?_
    intro _ w hf
    exact hf.elim
  · have hlt : d < sparkleSynthDepthLimit := Nat.lt_of_not_ge hlt
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat),
        Triple mctx mref cctx cref (J L (d + 1))
          (_root_.tryFinally
            (do
              let constInfo ← getConstInfo declName
              let env ← getEnv
              synthesizeFromConst (fun e h t n => translateExprToWire e h t n)
                (profLogIO prof.isSome) declName [] false true
                (entryConst true false [] constInfo (instancePredicate env) (userInliner env)
                  (structEnv env))
                (instancePredicate env))
            (do
              ST.Ref.modify sparkleSynthDepth fun x => x - 1
              if (d != 0) = true then do
                  ST.Ref.set sparkleFvarValueMap m1
                  ST.Ref.set sparkleWireWidthCache m2
                else pure () : MetaM Unit))
          (fun _ => J L d) (J L d) := by
      intro m1 m2
      refine Triple.tryFinally (M := J L (d + 1)) ?_ (fin_triple L d d m1 m2)
      refine Triple.bind (Triple.frame L (Framed.constInfo _) (d + 1)) ?_
      intro ci
      refine Triple.bind (Triple.frame L Framed.env (d + 1)) ?_
      intro env
      exact keeps_iff.mp (hbody hlt prof.isSome _ _)
    by_cases h0 : (d == 0) = true
    · simp only [h0, ↓reduceIte]
      tpure L d; tpure L d
      tset L d; tset L d; tset L d; tset L d
      tclear L d
      tset L d; tset L d; tset L d; tset L d; tset L d; tset L d; tset L d
      refine Triple.bind (Triple.depthSet L d (d + 1)) ?_
      intro _
      exact body _ _
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      tget L d; tget L d
      tset L d; tset L d; tset L d; tset L d; tset L d
      refine Triple.bind (Triple.depthSet L d (d + 1)) ?_
      intro _
      exact body _ _

/-- The full entry: the core, then the pure cleanup and one environment
variable read. -/
theorem full_keeps (D : Nat) (declName : Name)
    (hcore : Keeps mctx mref cctx cref (J L D) (synthesizeCombinationalCore declName [] false)) :
    Keeps mctx mref cctx cref (J L D) (synthesizeCombinational declName) := by
  rw [keeps_iff]
  unfold synthesizeCombinational synthesizeCombinationalWith
  refine Triple.bind (keeps_iff.mp hcore) ?_
  rintro ⟨m, d⟩
  dsimp only
  refine Triple.bind (Triple.frame L (Framed.ioEnv _) D) ?_
  intro x
  exact Triple.ite (fun _ => Triple.pure fun w hw => hw) (fun _ => Triple.pure fun w hw => hw)

/-! ## The recursion, by induction on the depth -/

/-- **The real entry keeps the invariant at every depth**, from `BodyRel`.
Induction on how far below the limit the depth is. At the limit the entry
throws. Below it, the body runs one level deeper, where the memoised child
entry keeps the invariant by `child_keeps` and the induction hypothesis — so
`BodyRel`'s premise holds there. -/
theorem entry_keeps (hB : BodyRel L) :
    ∀ (k D : Nat), sparkleSynthDepthLimit ≤ D + k →
      ∀ c, Keeps mctx mref cctx cref (J L D) (synthesizeCombinational c) := by
  intro k
  induction k with
  | zero =>
    intro D hD c
    exact full_keeps L D c (core_keeps L D c fun hlt => absurd hD (Nat.not_le_of_lt (by simpa using hlt)))
  | succ k ih =>
    intro D hD c
    refine full_keeps L D c (core_keeps L D c fun _ b ci isInst => ?_)
    exact hB (D + 1) (child_keeps L (D + 1) (ih (D + 1) (by omega))) b c ci isInst

theorem entry_keeps_all (hB : BodyRel L) (D : Nat) (c : Name) :
    Keeps mctx mref cctx cref (J L D) (synthesizeCombinational c) :=
  entry_keeps L hB sparkleSynthDepthLimit D (Nat.le_add_left _ _) c

theorem childKeeps_all (hB : BodyRel L) (D : Nat) : ChildKeeps L D :=
  child_keeps L D (entry_keeps_all L hB D)

/-! ## On a successful run -/

/-- A returning run of the real entry from an invariant world ends in one. -/
theorem entry_inv (hB : BodyRel L) {c : Name} {w r w'} (hw : InvW mctx mref cctx cref w)
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') :
    InvW mctx mref cctx cref w' := by
  have := entry_keeps_all L hB (L.dval w) c w ⟨invV_of_invW L hw, rfl⟩
  rw [endW_of_runs h] at this
  exact invW_of_invV L this.1

/-- A returning run of the machine route's harness, with the entry's logger,
from an invariant world ends in one. -/
theorem harness_inv (hB : BodyRel L) (hH : HarnessRel L) {b : Bool} {declName bs body}
    {w r w'} (hw : InvW mctx mref cctx cref w)
    (h : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) declName bs body)
      mctx mref cctx cref w r w') : InvW mctx mref cctx cref w' := by
  have := hH (L.dval w) (childKeeps_all L hB _) b declName bs body w ⟨invV_of_invW L hw, rfl⟩
  rw [endW_of_runs h] at this
  exact invW_of_invV L this.1

/-! ## The machine route's own code -/

theorem Triple.mapM_loop {α β : Type} {I : Void IO.RealWorld → Prop} (f : α → MetaM β)
    (hf : ∀ x, Triple mctx mref cctx cref I (f x) (fun _ => I) I) :
    ∀ (l : List α) (acc : List β),
      Triple mctx mref cctx cref I (List.mapM.loop f l acc) (fun _ => I) I
  | [], _ => Triple.pure fun _ hw => hw
  | x :: xs, acc => Triple.bind (hf x) fun y => Triple.mapM_loop f hf xs (y :: acc)

theorem Triple.mapM {α β : Type} {I : Void IO.RealWorld → Prop} (f : α → MetaM β)
    (hf : ∀ x, Triple mctx mref cctx cref I (f x) (fun _ => I) I) (l : List α) :
    Triple mctx mref cctx cref I (l.mapM f) (fun _ => I) I :=
  Triple.mapM_loop f hf l []

/-- The synthesis ref's read, in an invariant world: `synthesizeChild`. -/
theorem Triple.synthRead (D : Nat) :
    Triple mctx mref cctx cref (J L D) (sparkleChildSynth.get : MetaM _)
      (fun s w => J L D w ∧ s = some synthesizeChild) (J L D) :=
  Triple.frameQ L Framed.synthGet D fun _ _ _ hw h => (L.synthGet _ _ _ h).trans hw.1.2

/-- **The one-output closing keeps the invariant**, given the memoised child
entry does: the synthesis ref's read, then one `synthesizeChild` per call
(each may return or throw), then a pure closing. -/
theorem closeInstsM_keeps (D : Nat) (hC : ChildKeeps L D) (shape : MachineShape)
    (t m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    Keeps mctx mref cctx cref (J L D) (closeInstsM shape t m design) := by
  rw [keeps_iff]
  unfold closeInstsM
  refine Triple.bindQ (Triple.synthRead L D) ?_
  intro s hs
  subst hs
  dsimp only
  refine Triple.bind (Triple.mapM _ (fun x => ?_) _) ?_
  · obtain ⟨c, b, k⟩ := x
    exact keeps_iff.mp (hC c)
  · intro _
    exact Triple.pure fun _ hw => hw

/-- **The general closing keeps the invariant**: a memory call's child is
built (pure), any other is a `synthesizeChild`. -/
theorem closeInstsGM_keeps (D : Nat) (hC : ChildKeeps L D) (shape : MachineShape)
    (t m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    Keeps mctx mref cctx cref (J L D) (closeInstsGM shape t m design) := by
  rw [keeps_iff]
  unfold closeInstsGM
  refine Triple.bindQ (Triple.synthRead L D) ?_
  intro s hs
  subst hs
  dsimp only
  refine Triple.bind (Triple.mapM _ (fun x => ?_) _) ?_
  · obtain ⟨c, b, k⟩ := x
    dsimp only
    cases Sparkle.Compiler.MachMemory.memChild? c with
    | some md => exact Triple.pure fun _ hw => hw
    | none => exact keeps_iff.mp (hC c)
  · intro _
    exact Triple.pure fun _ hw => hw

/-- **The machine synthesis keeps the invariant** — on every outcome — given
that its harness does (`HarnessRel`) and the memoised child entry does: the
harness, the pure `closeLets` / `closeMachine`, and the closing's children. -/
theorem machine_keeps (hH : HarnessRel L) (D : Nat) (hC : ChildKeeps L D) (b : Bool)
    (declName : Name) (shape : MachineShape) :
    Keeps mctx mref cctx cref (J L D)
      (synthesizeMachineCertified (fun e hint top named => translateExprToWire e hint top named)
        (profLogIO b) declName shape) := by
  rw [keeps_iff]
  unfold synthesizeMachineCertified
  refine Triple.bind (keeps_iff.mp (hH D hC b declName _ _)) ?_
  rintro ⟨t, d⟩
  dsimp only
  split
  · split
    · exact Triple.pure fun _ hw => hw
    · split
      · exact keeps_iff.mp (closeInstsM_keeps L D hC _ _ _ _)
      · exact keeps_iff.mp (closeInstsGM_keeps L D hC _ _ _ _)
  · exact Triple.pure fun _ hw => hw

end Tools.ShippingChildInv

import Tools.ShippingChildBody
import Tools.ShippingChildBndInit
-- BUILT by the integrator: bl1 exit 0 (317 jobs), axioms standard (ax2) (round par/bal, base 87874a82). No `sorry`, no `axiom`, no `native_decide`.
-- Writing-time guesses are marked `-- (writing-time guess Gk: …)` and listed at the end of the
-- header below.

/-! # Depth balance of an OUTERMOST entry run, on every outcome

`ChildBnd` (`Tools/ShippingChildInv.lean`) is the start condition of an entry
run. For a run started at synthesis depth 0 (an outermost run: one top-level
command) this file proves, from ONE law witness `L : RefLaws mref cref` and
nothing else (no new law; `BodyRel` is the proved `bodyRel`), that the run
ENDS — whether it returns or throws — in a world where

* the depth is back to 0 (`L.dval = 0`),
* the synthesis ref still holds `some synthesizeChild` (`L.sval`),
* the world is still quiet for `L` (`L.quiet`),

so `StartV L` holds there by its LEFT disjunct, and an exception the run
throws is in the class (`ErrOk`). Hence the next outermost entry run from that
world starts with `ChildBnd` (for the same witness), and so on along any list
of entries.

Route. An outermost start does NOT give the invariant `J L 0` (it needs
`CacheInv` of the CURRENT cache, which `StartV`'s depth-0 branch does not
provide). So the prefix is walked under the weaker `Out0 L` (synthesis ref,
quiet, depth 0); the cache clear (`sparkleChildCache.set {}`) ESTABLISHES
`J L 0` from any cache (`tripleO_clear`); from there the existing machinery
(`Triple.depthSet`, the body at depth 1 by `bodyRel` + `childKeeps`, the
`finally` by `fin_triple`) brings the world back to `J L 0`, which implies
`Out0 L`. The paths that throw BEFORE the bump (the depth guard; any
exception of the prefix operations) never touch the depth: they are covered
by the frame laws (`frame`, `diag`, `frameT`) under `Out0`.

Entries covered:

* the CORE entry `synthesizeCombinationalCore declName [] false` — the one
  the `<p>_designClosedB` / `<p>_sat` theorems run (`hcore`, e.g.
  `Tests/Compiler/MemNameCollisionSatTest.lean:51`);
* the FULL entry `synthesizeCombinational declName` (the core, then the
  pure post-processing and one environment-variable read).

Results:

* `core_triple0` / `full_triple0`: the `Triple` from `Out0 L` to `Out0 L`
  (every outcome; exceptions `OkExc`), for a witness with `L.aux {}`.
* **`core_balance` / `full_balance`**: `StartV L w → L.quiet w → L.dval w = 0 →
  Out0 L (endW … entry w) ∧ ErrOk … entry w` for ANY witness `L`.
* `ChildBnd0 w := ∃ L, StartV L w ∧ L.quiet w ∧ L.dval w = 0` (the
  outermost boundary); `ChildBnd0.bnd : ChildBnd0 w → ChildBnd w`;
  `childBnd0_iff : ChildBnd0 w ↔ ChildBnd w ∧ readOf sparkleSynthDepth w = 0`.
* **`core_bnd0` / `full_bnd0`**: `ChildBnd0 w → ChildBnd0 (endW … entry w)`;
  law-free reading `core_bnd_readOf`: `ChildBnd w → readOf depth w = 0 →
  ChildBnd (endW …) ∧ readOf depth (endW …) = 0`.
* Two consecutive entries: `core_then_core` (a returning run of
  `core n1 >>= fun _ => core n2` splits at a world with `ChildBnd0`, so the
  second run's `hB` premise is discharged from the first's).
* n entries: `endSeq e ns w` (each entry from the previous one's end world,
  whatever its outcome); `endSeq_bnd` (`ChildBnd0` at every intermediate
  world), `endSeq_append`, `seq_start_bnd` (the start world of the entry at
  position `pre.length` has `ChildBnd`).

NOT proved here (premises / open):

* The initial contents of the refs at the FIRST entry (`readOf` facts, rows
  R13 / R14 of `docs/parallel/childbnd-residual.md`) and `QuietAt` there: the
  chain starts from a `ChildBnd0` premise.
* Commands run BETWEEN entries (other Lean commands, other elaborators): not
  covered; `endSeq` assumes each entry starts exactly in the previous one's
  end world. Their frame needs a runtime semantics.
* The joint satisfiability of the laws (R0): not shown, so every result here
  may be vacuous.

Writing-time guesses (for the integrator):
* G1 `simp only [h0, ↓reduceIte]` with `h0 : (d == 0) = true` turns the
  saved-map `if`s into `pure {}` and selects the clear branch, exactly as in
  `core_keeps`'s `d == 0` branch (which uses the same `simp`).
* G2 `have h0 : (d == 0) = true := by subst hd; first | rfl | decide | simp`.
* G3 `Out0 L.plain w` and `Out0 L w` are accepted as defeq by `exact`
  (projections of `RefLaws.plain`, as in `entry_inv`), re-packed component-wise.
* G4 `endSeq` unfolds on `[]` / `n :: ns` by `rfl` / `simp only [endSeq]`.
* G5 `Triple.conseq` with explicit `(P := J L d) (Q := …) (R := JE L d)`
  unifies the remaining program from the goal.
* G6 `bodyRel L (d + 1) hC mctx cctx prof.isSome declName _ _` (the
  `entry_keeps` application pattern) unifies `tenv` with the `getEnv` result;
  fallback `body_keeps`.
-/
namespace Tools.ShippingChildBalance
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## 1. The outermost condition -/

/-- The condition of an outermost world for the witness `L`: the synthesis
ref holds `synthesizeChild`, the world is quiet, the depth is 0. (No cache
half: the outermost entry clears the cache.) -/
def Out0 (L : RefLaws mref cref) (w : Void IO.RealWorld) : Prop :=
  L.sval w = some synthesizeChild ∧ L.quiet w ∧ L.dval w = 0

/-- `Out0`, with the thrown exception in the class. -/
def E0 (L : RefLaws mref cref) : Exception → Void IO.RealWorld → Prop :=
  fun e w => Out0 L w ∧ OkExc e

theorem out0_of_startV (L : RefLaws mref cref) {w : Void IO.RealWorld}
    (hs : StartV L w) (hq : L.quiet w) (hd : L.dval w = 0) : Out0 L w :=
  ⟨hs.1, hq, hd⟩

theorem startV_of_out0 (L : RefLaws mref cref) {w : Void IO.RealWorld} (h : Out0 L w) :
    StartV L w :=
  ⟨h.1, Or.inl h.2.2⟩

/-- The invariant at depth `d = 0` implies the outermost condition. -/
theorem out0_of_J (L : RefLaws mref cref) {d : Nat} (hd : d = 0) {w : Void IO.RealWorld}
    (h : J L d w) : Out0 L w :=
  ⟨h.1.2.1, h.1.2.2, h.2.1.trans hd⟩

/-! ## 2. Steps of the prefix under `Out0` (frame laws only) -/

/-- An operation from an outermost world ends in one, on every outcome: the
synthesis ref and the depth are left (frame / diagnostic / throw laws), and
quietness is kept. -/
theorem out0_end (L : RefLaws mref cref) {α : Type} {p : MetaM α} (hp : Op p)
    {w : Void IO.RealWorld} (hw : Out0 L w) : Out0 L (endW mctx mref cctx cref p w) := by
  cases hp with
  | framed hf =>
    have hk := L.frame (mctx := mctx) (cctx := cctx) p hf w
    exact ⟨hk.2.1.trans hw.1, L.frameQ (mctx := mctx) (cctx := cctx) p hf w hw.2.1,
      hk.2.2.trans hw.2.2⟩
  | diag hd =>
    have hk := L.diag (mctx := mctx) (cctx := cctx) p hd w hw.2.1
    exact ⟨hk.1.2.1.trans hw.1, hk.2, hk.1.2.2.trans hw.2.2⟩
  | throwErr msg _ =>
    have hk := L.frameT (mctx := mctx) (cctx := cctx) _ (Throws.err (α := α) msg) w
    exact ⟨hk.1.2.1.trans hw.1, hk.2 hw.2.1, hk.1.2.2.trans hw.2.2⟩
  | coreThrowErr msg _ =>
    have hk := L.frameT (mctx := mctx) (cctx := cctx) _ (Throws.coreErr (α := α) msg) w
    exact ⟨hk.1.2.1.trans hw.1, hk.2 hw.2.1, hk.1.2.2.trans hw.2.2⟩

theorem tripleO_op (L : RefLaws mref cref) {α : Type} {p : MetaM α} (hp : Op p) :
    Triple mctx mref cctx cref (Out0 L) p (fun _ => Out0 L) (E0 L) := by
  intro w hw
  have hk := out0_end (mctx := mctx) (cctx := cctx) L hp hw
  unfold endW at hk
  cases hm : p mctx mref cctx cref w with
  | ok a w1 => rw [hm] at hk; exact hk
  | error e w1 => rw [hm] at hk; exact ⟨hk, L.excOk p hp w e w1 hw.2.1 hm⟩

/-- A framed operation, with a fact of its result on a successful run. -/
theorem tripleO_frameQ (L : RefLaws mref cref) {α : Type} {p : MetaM α} (hp : Framed p)
    {φ : α → Prop}
    (hφ : ∀ w a w', Out0 L w → RunsTo p mctx mref cctx cref w a w' → φ a) :
    Triple mctx mref cctx cref (Out0 L) p (fun a w => Out0 L w ∧ φ a) (E0 L) := by
  intro w hw
  have hk := out0_end (mctx := mctx) (cctx := cctx) L (.framed hp) hw
  unfold endW at hk
  cases hm : p mctx mref cctx cref w with
  | ok a w1 => rw [hm] at hk; exact ⟨hk, hφ w a w1 hw hm⟩
  | error e w1 => rw [hm] at hk; exact ⟨hk, L.excOk p (.framed hp) w e w1 hw.2.1 hm⟩

/-- `throwError` (the depth guard) from an outermost world: no returning run;
the throwing run ends in an outermost world. -/
theorem tripleO_throwErr (L : RefLaws mref cref) {α : Type} (msg : MessageData)
    (hmsg : OkMsg msg) {Q : α → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (Out0 L) (Lean.throwError msg : MetaM α) Q (E0 L) := by
  intro w hw
  have hk := out0_end (mctx := mctx) (cctx := cctx) L (Op.throwErr (α := α) msg hmsg) hw
  unfold endW at hk
  cases hm : (Lean.throwError msg : MetaM α) mctx mref cctx cref w with
  | ok a w1 => exact (throwError_not_runs msg hm).elim
  | error e w1 =>
    rw [hm] at hk
    exact ⟨hk, L.excOk _ (Op.throwErr (α := α) msg hmsg) w e w1 hw.2.1 hm⟩

/-- **The clear ESTABLISHES the invariant at depth `d = 0`** from an outermost
world, whatever the cache held (it cannot fail). -/
theorem tripleO_clear (L : RefLaws mref cref) (hA : L.aux {}) (d : Nat) (hd : d = 0)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (Out0 L) (sparkleChildCache.set {} : MetaM Unit)
      (fun _ => J L d) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    obtain ⟨hv, hs, hdd⟩ := L.cacheSet _ _ _ _ h
    refine ⟨⟨?_, ?_, L.cacheSetQ _ _ _ _ h hw.2.1⟩, hdd.trans (hw.2.2.trans hd.symm), ?_⟩
    · rw [hv]; exact cacheInv_empty
    · rw [hs]; exact hw.1
    · rw [hv]; exact hA

/-- A `pure` of the prefix under `Out0`. -/
macro "bpure0 " L:term:max : tactic => `(tactic|
  (refine Triple.bind (Triple.pure (Q := fun _ => Out0 $L) (fun w hw => hw)) ?_; intro _))
/-- A set of another per-synthesis ref under `Out0`. -/
macro "bset0 " L:term:max : tactic => `(tactic|
  (refine Triple.bind (tripleO_op $L (Op.framed (Framed.sideSet _ ?s))) ?_
   case s => constructor
   intro _))

/-! ## 3. The core entry from an outermost world -/

/-- **The core entry from an outermost world ends in one — on every
outcome.** The prefix (environment read, logger, depth read) under `Out0`;
the depth guard throws under `Out0`; otherwise (depth 0) the saved maps are
`pure {}`, four resets, the CLEAR (which establishes `J L 0`), seven resets,
the bump to 1, the body (kept at depth 1 by `bodyRel` and `childKeeps`), and
the `finally`, which brings the depth back to 0 from whichever world the
body ended in. -/
theorem core_triple0 (L : RefLaws mref cref) (hA : L.aux {}) (declName : Name) :
    Triple mctx mref cctx cref (Out0 L) (synthesizeCombinationalCore declName [] false)
      (fun _ => Out0 L) (E0 L) := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (tripleO_op L (.framed (Framed.ioEnv _))) ?_
  intro prof
  refine Triple.bind (tripleO_op L (.diag (Diag.profLog prof.isSome _))) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = 0)
    (tripleO_frameQ L Framed.depthGet fun w d w' hw h => by
      rw [L.depthGet _ _ _ h]; exact hw.2.2) ?_
  intro d hd
  -- the body and the `finally`, at depth `d + 1` back to `d` (as in `core_keeps`)
  have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
      (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
      (m7 : Std.HashMap String String),
      Triple mctx mref cctx cref (J L (d + 1))
        (_root_.tryFinally
          (do
            let constInfo ← getConstInfo declName
            let env ← getEnv
            synthesizeFromConst (fun e h t n => translateExprToWire env e h t n)
              (profLogIO prof.isSome) declName [] false true
              (entryConst true false [] constInfo (instancePredicate env) (userInliner env)
                (structEnv env))
              (instancePredicate env))
          (do
            ST.Ref.modify sparkleSynthDepth fun x => x - 1
            if (d != 0) = true then do
                ST.Ref.set sparkleFvarValueMap m1
                ST.Ref.set sparkleWireWidthCache m2
                ST.Ref.set sparkleLetWireCache m3
                ST.Ref.set sparkleLoopWireCache m4
                ST.Ref.set sparkleWireCanon m5
                ST.Ref.set sparkleSubInstanceOutputs m6
                ST.Ref.set sparkleSingleOutInstanceCache m7
              else pure () : MetaM Unit))
        (fun _ => J L d) (JE L d) := by
    intro m1 m2 m3 m4 m5 m6 m7
    refine Triple.tryFinally (M := J L (d + 1)) (E := OkExc) ?_
      (fin_triple L d d m1 m2 m3 m4 m5 m6 m7)
    refine Triple.bind (Triple.frame L (Framed.constInfo _) (d + 1)) ?_
    intro ci
    refine Triple.bind (Triple.frame L Framed.env (d + 1)) ?_
    intro env
    have hC : ChildKeeps L (d + 1) := childKeeps L (d + 1) (fun h => absurd h (Nat.succ_ne_zero _))
    -- (writing-time guess G6: the `entry_keeps` application pattern; fallback `body_keeps`)
    first
      | exact keeps_iff.mp (bodyRel L (d + 1) hC mctx cctx prof.isSome declName _ _)
      | exact keeps_iff.mp (body_keeps L (d + 1) hC prof.isSome declName _ _)
  refine Triple.ite (fun _ => ?_) (fun _ => ?_)
  · -- at the limit: the entry throws before touching the depth
    refine Triple.bind (Q := fun _ _ => False)
      (tripleO_throwErr L _ (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · -- (writing-time guess G2)
    have h0 : (d == 0) = true := by subst hd; first | rfl | decide | simp
    -- (writing-time guess G1: as in `core_keeps`'s `d == 0` branch)
    simp only [h0, ↓reduceIte]
    bpure0 L; bpure0 L; bpure0 L; bpure0 L; bpure0 L; bpure0 L; bpure0 L
    bset0 L; bset0 L; bset0 L; bset0 L
    refine Triple.bind (tripleO_clear L hA d hd) ?_
    intro _
    -- from the clear on, the invariant at depth `d` (= 0); weakened at the end
    -- (writing-time guess G5)
    refine Triple.conseq (P := J L d) (Q := fun _ => J L d) (R := JE L d) ?_
      (fun _ h => h) (fun _ _ h => out0_of_J L hd h) (fun _ _ h => ⟨out0_of_J L hd h.1, h.2⟩)
    tset L d; tset L d; tset L d; tset L d; tset L d; tset L d; tset L d
    refine Triple.bind (Triple.depthSet L d (d + 1)) ?_
    intro _
    exact body _ _ _ _ _ _ _

/-- The full entry: the core, then one environment-variable read and pure
post-processing. -/
theorem full_triple0 (L : RefLaws mref cref) (hA : L.aux {}) (declName : Name) :
    Triple mctx mref cctx cref (Out0 L) (synthesizeCombinational declName)
      (fun _ => Out0 L) (E0 L) := by
  unfold synthesizeCombinational synthesizeCombinationalWith
  refine Triple.bind (core_triple0 L hA declName) ?_
  rintro ⟨m, d⟩
  dsimp only
  refine Triple.bind (tripleO_op L (.framed (Framed.ioEnv _))) ?_
  intro x
  exact Triple.ite (fun _ => Triple.pure fun w hw => hw) (fun _ => Triple.pure fun w hw => hw)

/-- From a `Triple` with `Out0` on both outcomes: the end world and `ErrOk`. -/
theorem out0_endW_of_triple (L : RefLaws mref cref) {α : Type} {m : MetaM α}
    (h : Triple mctx mref cctx cref (Out0 L) m (fun _ => Out0 L) (E0 L))
    {w : Void IO.RealWorld} (hw : Out0 L w) :
    Out0 L (endW mctx mref cctx cref m w) ∧ ErrOk mctx mref cctx cref m w := by
  have := h w hw
  unfold endW ErrOk
  cases hm : m mctx mref cctx cref w with
  | ok a w' => rw [hm] at this; exact ⟨this, trivial⟩
  | error e w' => rw [hm] at this; exact ⟨this.1, this.2⟩

/-! ## 4. The balance, for any witness -/

/-- **Outermost balance of the core entry, every outcome.** From a world with
the start condition, quiet, at depth 0 — for ANY law witness `L` — the run of
the core entry ends (returning or throwing) in a world with the synthesis ref
`some synthesizeChild`, quiet, at depth 0; an exception is `OkExc`. -/
theorem core_balance (L : RefLaws mref cref) (declName : Name) {w : Void IO.RealWorld}
    (hs : StartV L w) (hq : L.quiet w) (hd : L.dval w = 0) :
    Out0 L (endW mctx mref cctx cref (synthesizeCombinationalCore declName [] false) w) ∧
      ErrOk mctx mref cctx cref (synthesizeCombinationalCore declName [] false) w := by
  -- the witness with the trivial auxiliary predicate (same values, same `quiet`)
  have h := out0_endW_of_triple L.plain (core_triple0 (mctx := mctx) (cctx := cctx)
    L.plain trivial declName) (w := w) ⟨hs.1, hq, hd⟩
  -- (writing-time guess G3: `L.plain`'s projections are `L`'s by `rfl`)
  exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2⟩, h.2⟩

/-- **Outermost balance of the full entry, every outcome.** -/
theorem full_balance (L : RefLaws mref cref) (declName : Name) {w : Void IO.RealWorld}
    (hs : StartV L w) (hq : L.quiet w) (hd : L.dval w = 0) :
    Out0 L (endW mctx mref cctx cref (synthesizeCombinational declName) w) ∧
      ErrOk mctx mref cctx cref (synthesizeCombinational declName) w := by
  have h := out0_endW_of_triple L.plain (full_triple0 (mctx := mctx) (cctx := cctx)
    L.plain trivial declName) (w := w) ⟨hs.1, hq, hd⟩
  exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2⟩, h.2⟩

/-! ## 5. The outermost boundary, kept -/

section Bnd0
variable (mref cref)

/-- **The outermost boundary**: `ChildBnd` with the depth 0, for the same
witness. -/
def ChildBnd0 (w : Void IO.RealWorld) : Prop :=
  ∃ L : RefLaws mref cref, StartV L w ∧ L.quiet w ∧ L.dval w = 0

end Bnd0

theorem ChildBnd0.bnd {w : Void IO.RealWorld} (h : ChildBnd0 mref cref w) :
    ChildBnd mref cref w := by
  obtain ⟨L, hs, hq, _⟩ := h
  exact ⟨L, hs, hq⟩

/-- The outermost boundary is `ChildBnd` with the depth ref reading 0 (the
contexts only serve to run a read). -/
theorem childBnd0_iff (mctx : Meta.Context) (cctx : Core.Context) {w : Void IO.RealWorld} :
    ChildBnd0 mref cref w ↔ ChildBnd mref cref w ∧ readOf sparkleSynthDepth w = 0 := by
  constructor
  · rintro ⟨L, hs, hq, hd⟩
    exact ⟨⟨L, hs, hq⟩, (refLaws_dval_eq L mctx cctx w).symm.trans hd⟩
  · rintro ⟨⟨L, hs, hq⟩, hd⟩
    exact ⟨L, hs, hq, (refLaws_dval_eq L mctx cctx w).trans hd⟩

theorem childBnd0_of_out0 (L : RefLaws mref cref) {w : Void IO.RealWorld} (h : Out0 L w) :
    ChildBnd0 mref cref w :=
  ⟨L, startV_of_out0 L h, h.2.1, h.2.2⟩

/-- **The core entry keeps the outermost boundary**, on every outcome. -/
theorem core_bnd0 (declName : Name) {w : Void IO.RealWorld} (h : ChildBnd0 mref cref w) :
    ChildBnd0 mref cref
      (endW mctx mref cctx cref (synthesizeCombinationalCore declName [] false) w) := by
  obtain ⟨L, hs, hq, hd⟩ := h
  exact childBnd0_of_out0 L (core_balance (mctx := mctx) (cctx := cctx) L declName hs hq hd).1

/-- **The full entry keeps the outermost boundary**, on every outcome. -/
theorem full_bnd0 (declName : Name) {w : Void IO.RealWorld} (h : ChildBnd0 mref cref w) :
    ChildBnd0 mref cref (endW mctx mref cctx cref (synthesizeCombinational declName) w) := by
  obtain ⟨L, hs, hq, hd⟩ := h
  exact childBnd0_of_out0 L (full_balance (mctx := mctx) (cctx := cctx) L declName hs hq hd).1

/-- The same, read by the depth ref's contents (no witness in the statement
beyond `ChildBnd`'s). -/
theorem core_bnd_readOf (declName : Name) {w : Void IO.RealWorld}
    (hB : ChildBnd mref cref w) (hd : readOf sparkleSynthDepth w = 0) :
    ChildBnd mref cref (endW mctx mref cctx cref (synthesizeCombinationalCore declName [] false) w) ∧
      readOf sparkleSynthDepth
        (endW mctx mref cctx cref (synthesizeCombinationalCore declName [] false) w) = 0 :=
  (childBnd0_iff mctx cctx).mp (core_bnd0 (mctx := mctx) (cctx := cctx) declName ((childBnd0_iff mctx cctx).mpr ⟨hB, hd⟩))

/-! ## 6. Consecutive entries -/

/-- **Two consecutive core entries**: a returning run of `core n1` then
`core n2` from an outermost-boundary world splits at a world where the
outermost boundary holds again — so the second run's `ChildBnd` premise
(`hB`, via `ChildBnd0.bnd`) is discharged from the first's. -/
theorem core_then_core (n1 n2 : Name) {w w'' : Void IO.RealWorld} {r : Res}
    (hB : ChildBnd0 mref cref w)
    (h : RunsTo (synthesizeCombinationalCore n1 [] false >>= fun _ =>
      synthesizeCombinationalCore n2 [] false) mctx mref cctx cref w r w'') :
    ∃ (r1 : Res) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore n1 [] false) mctx mref cctx cref w r1 w1 ∧
      ChildBnd0 mref cref w1 ∧
      RunsTo (synthesizeCombinationalCore n2 [] false) mctx mref cctx cref w1 r w'' := by
  obtain ⟨r1, w1, h1, h2⟩ := RunsTo.bind h
  have hb := core_bnd0 (mctx := mctx) (cctx := cctx) n1 hB
  rw [endW_of_runs h1] at hb
  exact ⟨r1, w1, h1, hb, h2⟩

section Seq
variable (mctx mref cctx cref)

/-- The world a sequence of entry runs ends in: each entry starts in the world
the previous one ended in, WHATEVER its outcome (a failed command does not
stop the next). Nothing else runs in between (see the header). -/
def endSeq (e : Name → MetaM Res) : List Name → Void IO.RealWorld → Void IO.RealWorld
  | [], w => w
  | n :: ns, w => endSeq e ns (endW mctx mref cctx cref (e n) w)

end Seq

theorem endSeq_append (e : Name → MetaM Res) :
    ∀ (pre post : List Name) (w : Void IO.RealWorld),
      endSeq mctx mref cctx cref e (pre ++ post) w =
        endSeq mctx mref cctx cref e post (endSeq mctx mref cctx cref e pre w)
  | [], post, w => rfl
  | n :: pre, post, w => by
    -- (writing-time guess G4)
    first
      | exact endSeq_append e pre post _
      | (simp only [List.cons_append, endSeq]; exact endSeq_append e pre post _)

/-- **Along a sequence**: an entry that keeps the outermost boundary keeps it
through any number of runs. -/
theorem endSeq_bnd (e : Name → MetaM Res)
    (he : ∀ n w, ChildBnd0 mref cref w →
      ChildBnd0 mref cref (endW mctx mref cctx cref (e n) w)) :
    ∀ (ns : List Name) (w : Void IO.RealWorld), ChildBnd0 mref cref w →
      ChildBnd0 mref cref (endSeq mctx mref cctx cref e ns w)
  | [], w, h => h
  | n :: ns, w, h => by
    -- (writing-time guess G4)
    first
      | exact endSeq_bnd e he ns _ (he n w h)
      | (simp only [endSeq]; exact endSeq_bnd e he ns _ (he n w h))

/-- **The entry at position `pre.length` of a sequence of core entries starts
with `ChildBnd`**, from `ChildBnd0` at the start of the first, and the
sequence runs it from there. -/
theorem seq_start_bnd (pre post : List Name) (n : Name) {w : Void IO.RealWorld}
    (h : ChildBnd0 mref cref w) :
    ChildBnd mref cref
        (endSeq mctx mref cctx cref (fun c => synthesizeCombinationalCore c [] false) pre w) ∧
      endSeq mctx mref cctx cref (fun c => synthesizeCombinationalCore c [] false)
          (pre ++ n :: post) w =
        endSeq mctx mref cctx cref (fun c => synthesizeCombinationalCore c [] false) post
          (endW mctx mref cctx cref (synthesizeCombinationalCore n [] false)
            (endSeq mctx mref cctx cref (fun c => synthesizeCombinationalCore c [] false) pre w)) :=
  ⟨(endSeq_bnd (mctx := mctx) (cctx := cctx) _ (fun n _ hw => core_bnd0 n hw) pre w h).bnd,
    -- (writing-time guess G4: the cons step of `endSeq` and the beta of `e n` by `rfl`)
    by rw [endSeq_append]; try rfl⟩

end Tools.ShippingChildBalance

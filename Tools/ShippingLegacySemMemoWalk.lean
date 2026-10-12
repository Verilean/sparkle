import Tools.ShippingMemoLaws
import Tools.ShippingLegacySemProj

/-! # The legacy entry in `RunsTo` form: THIS run's memo read

Every legacy entry theorem so far concludes `MemoHit declName m d ∨ …`, with
`MemoHit` = "SOME run of the memo's read returned a map holding `(m, d)`"
(`MReturns`: the world is quantified per run). No heap law can refute or
characterise that. Here the walk is restated for ONE run in fixed state
references and worlds (`RunsTo`), under the extended runtime boundary
`RefLawsM` (`Tools/ShippingMemoLaws.lean` — an EXTENSION of the trust base).

**Proved here**

* `legacy_entry_walk_at` — a returning run of `synthesizeFromConst` on a
  definition the three gates decline (or with the front end off) performs
  the memo's read at a world `wr` where the memo's map is the START world's
  (`L.mval wr = L.mval w`: between the two there is at most one `getEnv`),
  and then either returns the entry stored under `declName`, or — the read
  found none — is what `legacy_entry_walk_in` says of a compiling run. The
  prefix is walked with `RunsTo.bind` (worlds kept); after the read the run
  is handed to the existing `MReturns` / `MRunsIn` walk, whose steps are
  repeated unchanged.
* `legacy_entry_walk_start` — the same with the hit stated by the start
  world: `(L.mval w).get? declName = some (m, d) ∨ …`.
* `list_entry_outputDN_at`, `proj_entry_output_at` — `list_entry_outputDN`
  and `proj_entry_output` (`Tools/ShippingLegacySemProj.lean`) for a
  `RunsTo` run, the first disjunct now `(L.mval w).get? declName = some (m,
  d)`: a fact about THIS run's start world. Their proofs are the old ones.
* `proj_entry_output_miss` — no disjunct when the start world's memo has no
  entry for `declName`.
* `outer_miss` — **the depth-0 miss, derived**: in a returning run of the
  core entry from depth 0 (quiet start world), on a declaration whose entry
  constant the three gates decline, the legacy arm's read of the memo in
  this run returns a map with NO entry (for any name): reset →
  (`outer_reset_reaches`) → read.
* `proj_entry_output_outer` — **the projection class at the outermost
  entry, with no `MemoHit`**.

**The side condition of the miss** is exactly "the run reaches the read
through `machine? = none`" — here: the machine gate declines the entry
constant for every structure environment (`hmach`, already a premise of the
old theorem). If the machine gate ACCEPTS and `synthesizeMachineCertified`
then returns `none` (`closeLets` / `closeInsts` fail), the run falls through
to the same read AFTER the harness and the children's syntheses ran: those
are callbacks, not in `MemoFrameOp`, and each child writes its own name to
the memo. That case is outside these theorems.

**Premises added to the old ones by `proj_entry_output_outer`**: the
boundary (`L : RefLawsM`, `L.dval w = 0`, `L.quiet w`), and ONE link the old
statement did not need because it was about `synthesizeFromConst` on a given
constant: `EntryConstIs` — the entry constant of this run is `.defnInfo dv`
(the entry reads the declaration itself). `mixed` is asked for the instance
predicate of the environment the run read. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedMeaning (Value)
open Tools.ShippingMemo (RefLawsM EntryConstIs outer_reset_reaches)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## `RunsTo` inversions -/

theorem runsTo_ite_pos {α : Type} {c : Prop} [Decidable c] {a b : MetaM α}
    {w w' : Void IO.RealWorld} {r : α}
    (h : RunsTo (if c then a else b) mctx mref cctx cref w r w') (hc : c) :
    RunsTo a mctx mref cctx cref w r w' := by
  rw [if_pos hc] at h
  exact h

theorem runsTo_ite_neg {α : Type} {c : Prop} [Decidable c] {a b : MetaM α}
    {w w' : Void IO.RealWorld} {r : α}
    (h : RunsTo (if c then a else b) mctx mref cctx cref w r w') (hc : ¬ c) :
    RunsTo b mctx mref cctx cref w r w' := by
  rw [if_neg hc] at h
  exact h

/-- A `pure` returns its value and leaves the world. -/
theorem runsTo_pure {α : Type} {a b : α} {w w' : Void IO.RealWorld}
    (h : RunsTo (Pure.pure a : MetaM α) mctx mref cctx cref w b w') : b = a ∧ w' = w :=
  Tools.ShippingChildInv.RunsTo.pure_world h

/-! ## The walk -/

/-- **The legacy arm of the entry, walked for ONE run, the memo's read
located.** The telescope's fact is asked only on the compiling branch (it is
a premise of the implication there), so the read's part needs none. -/
theorem legacy_entry_walk_at (L : RefLawsM mref cref)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {P : Meta.Context → Array Lean.Expr → Lean.Expr → Prop}
    {m : Sparkle.IR.AST.Module} {d : Design}
    {cfe : Bool} {w w' : Void IO.RealWorld}
    (old : cfe = true → certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : cfe = true → mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : cfe = true → ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (hr : RunsTo (synthesizeFromConst translate logProf declName [] false cfe
      (.defnInfo dv) isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (memo : Std.HashMap Name (Sparkle.IR.AST.Module × Design)) (wr wr' : Void IO.RealWorld),
      RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref wr memo wr' ∧
      L.mval wr = L.mval w ∧
      (memo.get? declName = some (m, d) ∨
       (memo.get? declName = none ∧
        ((∀ body0, MReturns (openRecordInputs dv.value) body0 →
            TelescopeIn (stripMemoizeWrappers body0) P) →
         ∃ (body0 : Lean.Expr) (mctx1 : Meta.Context) (xs : Array Lean.Expr)
           (inner : Lean.Expr) (leaves : Array (String × Lean.Expr))
           (cache : IO.Ref (ExprStructMap String)) (returned : String) (st : CircuitState),
           MReturns (openRecordInputs dv.value) body0 ∧ P mctx1 xs inner ∧
           MReturns (splitReturnLeaves inner) leaves ∧
           RunsIn (bindInputsLegacy [] false xs 0
               (emitLeaves translate cache logProf leaves.toList none 0))
             mctx1 (entryCompilerState false cache) (CircuitM.init declName.toString)
             returned st ∧
           m = (addClockResetIfSequential st.module).finalize ∧
           Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true))) := by
  unfold synthesizeFromConst at hr
  cases cfe
  all_goals
    -- the two certified gates decline (front end on), or are not asked (off)
    first
      | simp only [↓reduceIte, old rfl, mixed rfl] at hr
      | simp only [Bool.false_eq_true, ↓reduceIte] at hr
    -- the machine shape declines, or is not asked: `machine? = none`,
    -- `machineResult? = none`. The five shapes of `legacy_entry_walk_in`,
    -- step for step, with the worlds kept: the only operation is one
    -- `getEnv` (front end on), which is of the enumerated frame class
    first
      | (have a1 := runsTo_ite_pos hr rfl
         obtain ⟨env, wa, henv, a2⟩ := RunsTo.bind a1
         obtain ⟨y, wy, hy, a3⟩ := RunsTo.bind a2
         obtain ⟨rfl, ey⟩ := runsTo_pure hy
         rw [hmach rfl] at a3
         obtain ⟨y2, wy2, hy2, h2⟩ := RunsTo.bind a3
         obtain ⟨rfl, ey2⟩ := runsTo_pure hy2
         have hmv : L.mval wy2 = L.mval w := by
           rw [ey2, ey]
           exact L.envSame henv)
      | (obtain ⟨mq, wq, hmq, b1⟩ := RunsTo.bind hr
         have b2 := runsTo_ite_pos hmq rfl
         obtain ⟨env, wa, henv, b3⟩ := RunsTo.bind b2
         obtain ⟨hn, eq1⟩ := runsTo_pure b3
         rw [hmach rfl] at hn
         subst hn
         obtain ⟨y2, wy2, hy2, h2⟩ := RunsTo.bind b1
         obtain ⟨rfl, ey2⟩ := runsTo_pure hy2
         have hmv : L.mval wy2 = L.mval w := by
           rw [ey2, eq1]
           exact L.envSame henv)
      | (have a1 := runsTo_ite_neg hr (by decide)
         obtain ⟨y, wy, hy, a3⟩ := RunsTo.bind a1
         obtain ⟨rfl, ey⟩ := runsTo_pure hy
         obtain ⟨y2, wy2, hy2, h2⟩ := RunsTo.bind a3
         obtain ⟨rfl, ey2⟩ := runsTo_pure hy2
         have hmv : L.mval wy2 = L.mval w := by
           rw [ey2, ey])
      | (obtain ⟨mq, wq, hmq, b1⟩ := RunsTo.bind hr
         obtain ⟨hn, eq1⟩ := runsTo_pure (runsTo_ite_neg hmq (by decide))
         subst hn
         obtain ⟨y2, wy2, hy2, h2⟩ := RunsTo.bind b1
         obtain ⟨rfl, ey2⟩ := runsTo_pure hy2
         have hmv : L.mval wy2 = L.mval w := by
           rw [ey2, eq1])
      | (obtain ⟨y, wy, hy, a3⟩ := RunsTo.bind hr
         obtain ⟨rfl, ey⟩ := runsTo_pure hy
         obtain ⟨y2, wy2, hy2, h2⟩ := RunsTo.bind a3
         obtain ⟨rfl, ey2⟩ := runsTo_pure hy2
         have hmv : L.mval wy2 = L.mval w := by
           rw [ey2, ey])
    -- the memo read: THIS run's, at a world whose memo is the start world's
    have h3 := runsTo_ite_pos h2 rfl
    obtain ⟨memo, wm, hmemo, h4⟩ := RunsTo.bind h3
    -- from here on the walk is the existing one (no heap fact is needed
    -- after the read)
    have h4 := RunsTo.mreturns h4
    cases hget : memo.get? declName with
    | some cached =>
      rw [hget] at h4
      obtain ⟨_, _, h5⟩ := MReturns.bind h4
      have e := MReturns.pure h5
      exact ⟨memo, _, wm, hmemo, hmv, Or.inl (by rw [hget, e])⟩
    | none =>
      rw [hget] at h4
      refine ⟨memo, _, wm, hmemo, hmv, Or.inr ⟨hget, fun htele => ?_⟩⟩
      obtain ⟨_, _, h5⟩ := MReturns.bind h4      -- log
      obtain ⟨_, _, h6⟩ := MReturns.bind h5      -- log (the `.defnInfo` alternative)
      obtain ⟨t0, _, h7⟩ := MReturns.bind h6     -- clock
      obtain ⟨_, _, h8⟩ := MReturns.bind h7      -- log
      obtain ⟨body0, hopen, h9⟩ := MReturns.bind h8
      obtain ⟨t1, _, h10⟩ := MReturns.bind h9    -- clock
      obtain ⟨_, _, h11⟩ := MReturns.bind h10    -- log
      -- the telescope: from here on the run is in the context `mctx1`
      obtain ⟨mctx1, xs, inner, hP, h12⟩ := htele body0 hopen _ _ _ h11
      obtain ⟨_, _, h13⟩ := MRunsIn.bind h12    -- log
      -- the retained-parameter check is under `if symbolicMode`: a join
      -- point, already reduced by `simp`, or a plain bind
      first
        | (have h14 := MRunsIn.ite_neg h13 Bool.false_ne_true
           obtain ⟨leaves, hsplit, h15⟩ := MRunsIn.bind h14)
        | (obtain ⟨leaves, hsplit, h15⟩ := MRunsIn.bind h13
           have hsplit : MRunsIn (splitReturnLeaves inner) mctx1 leaves := hsplit)
        | (obtain ⟨_, _, h14⟩ := MRunsIn.bind h13
           obtain ⟨leaves, hsplit, h15⟩ := MRunsIn.bind h14)
      obtain ⟨t2, _, h16⟩ := MRunsIn.bind h15   -- clock
      obtain ⟨_, _, h17⟩ := MRunsIn.bind h16    -- log
      obtain ⟨cache, _, h18⟩ := MRunsIn.bind h17
      obtain ⟨⟨returned, st⟩, run, h19⟩ := MRunsIn.bind h18
      obtain ⟨res, hfin, h20⟩ := MRunsIn.bind h19
      have hres : (m, d) = res := by
        first
          | (have c1 := MRunsIn.ite_pos h20 rfl
             obtain ⟨_, _, c2⟩ := MRunsIn.bind c1
             exact MRunsIn.pure c2)
          | (obtain ⟨_, _, c2⟩ := MRunsIn.bind h20
             exact MRunsIn.pure c2)
      subst hres
      obtain ⟨hm, _, legal⟩ := finishSynth_returns (MRunsIn.returns hfin)
      exact ⟨body0, mctx1, xs, inner, leaves, cache, returned, st, hopen, hP,
        MRunsIn.returns hsplit, MRunsIn.run run, hm, legal⟩

/-- **The walk, the hit stated by the START world's memo.** -/
theorem legacy_entry_walk_start (L : RefLawsM mref cref)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {P : Meta.Context → Array Lean.Expr → Lean.Expr → Prop}
    {m : Sparkle.IR.AST.Module} {d : Design}
    {cfe : Bool} {w w' : Void IO.RealWorld}
    (old : cfe = true → certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : cfe = true → mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : cfe = true → ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) P)
    (hr : RunsTo (synthesizeFromConst translate logProf declName [] false cfe
      (.defnInfo dv) isInst) mctx mref cctx cref w (m, d) w') :
    (L.mval w).get? declName = some (m, d) ∨
    ∃ (body0 : Lean.Expr) (mctx1 : Meta.Context) (xs : Array Lean.Expr) (inner : Lean.Expr)
      (leaves : Array (String × Lean.Expr)) (cache : IO.Ref (ExprStructMap String))
      (returned : String) (st : CircuitState),
      MReturns (openRecordInputs dv.value) body0 ∧ P mctx1 xs inner ∧
      MReturns (splitReturnLeaves inner) leaves ∧
      RunsIn (bindInputsLegacy [] false xs 0
          (emitLeaves translate cache logProf leaves.toList none 0))
        mctx1 (entryCompilerState false cache) (CircuitM.init declName.toString) returned st ∧
      m = (addClockResetIfSequential st.module).finalize ∧
      Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true := by
  obtain ⟨memo, wr, wr', hg, hv, hcase⟩ :=
    legacy_entry_walk_at L (P := P) old mixed hmach hr
  have e : memo = L.mval w := (L.read hg).trans hv
  rcases hcase with hit | ⟨_, H⟩
  · rw [e] at hit
    exact Or.inl hit
  · exact Or.inr (H htele)

/-! ## The entry theorems for one run -/

/-- **`list_entry_outputDN` for ONE run**: the first disjunct is a fact about
this run's start world. -/
theorem list_entry_outputDN_at (L : RefLawsM mref cref)
    {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Design} {cfe : Bool} {w w' : Void IO.RealWorld}
    (old : cfe = true → certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : cfe = true → mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : cfe = true → ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (ListScopeDN bs leafOf))
    (hleaf : ∀ ids : List FVarId, ids.length = bs.length →
      (leafOf ids).isLambda = false ∧ SignalTyped (leafOf ids))
    (hr : RunsTo (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf declName [] false cfe (.defnInfo dv) isInst) mctx mref cctx cref w (m, d) w') :
    (L.mval w).get? declName = some (m, d) ∨
    ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.length = bs.length ∧ ids.Nodup ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          declName.toString) →
      ∀ v : Value, 0 < v.kind.width →
      LeafDom (setupOf declName bs ids cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName bs ids cache bools bits).bools
          (setupOf declName bs ids cache bools bits).bits)
        "out" true (leafOf ids) v →
      Tools.ShippingMixedEntrySoundness.RawValueAt v.kind.width bs m initial mems v.toNat := by
  rcases legacy_entry_walk_start L old mixed hmach htele hr with hit |
    ⟨body0, mctx1, xs, inner, leaves, cache, returned, st, hopen,
      ⟨ids, hinner, hdecls, hnd⟩, hsplit, run, hm, legal⟩
  · exact Or.inl hit
  · have hlen : ids.length = bs.length := DeclsAtD.length bs ids 0 hdecls
    refine Or.inr ⟨ids, cache, hlen, hnd, ?_⟩
    rw [hinner] at hsplit
    have hl : leaves.toList = [("out", leafOf ids)] :=
      splitReturnLeaves_scalar (hleaf ids hlen).1 (hleaf ids hlen).2 hsplit
    rw [hl] at run
    intro bools bits initial mems values v pos dom
    have leaf := bindInputsLegacy_prepareD (bools := bools) (bits := bits) bs ids 0
      (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
        declName.toString) hdecls run
    exact harness_sound_leaf (bs := bs) (ids := ids) hm legal bools bits initial mems
      values leaf v pos (leaf_translate_spec dom) (leaf_translate_order dom)

/-- **The projection class for ONE run**: `proj_entry_output` with the first
disjunct a fact about this run's start world — the memo there holds `(m, d)`
under `declName`. -/
theorem proj_entry_output_at (L : RefLawsM mref cref)
    {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Design} {i : Nat} {nm : Name} {k : MixedGateBinder}
    {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htel : LamTelescopeND)
    (hbody : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      ∃ (sp : List (Name × Lean.Expr × BinderInfo)) (b : Lean.Expr),
        stripMemoizeWrappers body0 = lams sp b ∧
        b.isLambda = false ∧
        TypesOkFrom sp bs #[] ∧
        ∀ ids : List FVarId, ids.length = bs.length →
          b.instantiateRevRange 0 (ids.map Lean.Expr.fvar).toArray.size
            (ids.map Lean.Expr.fvar).toArray = leafOf ids)
    (hfield : AtIdx bs i (nm, k)) (hk : k ≠ MixedGateBinder.domain)
    (hpos : 0 < kindWidth k)
    (hshape : ∀ ids : List FVarId, ids.length = bs.length →
      ∃ (f a : Lean.Expr) (n : Name) (ty b : Lean.Expr) (bi : BinderInfo),
        leafOf ids = Lean.Expr.app f a ∧
        (Lean.Expr.app f a).getAppFn = Lean.Expr.lam n ty b bi)
    (hkind : ∀ ids : List FVarId, ids.length = bs.length →
      fallbackKind (leafOf ids) = .other)
    (hwhnf : ∀ (ids : List FVarId) (x : FVarId), ids.length = bs.length → AtIdx ids i x →
      WhnfIsVar (leafOf ids) x)
    (hres : ∀ ids : List FVarId, ids.length = bs.length → SignalTyped (leafOf ids))
    (hr : RunsTo (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf declName [] false true (.defnInfo dv) isInst) mctx mref cctx cref w (m, d) w') :
    (L.mval w).get? declName = some (m, d) ∨
    ∃ (ids : List FVarId) (x : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.length = bs.length ∧ ids.Nodup ∧ AtIdx ids i x ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          declName.toString) →
      Tools.ShippingMixedEntrySoundness.RawValueAt (kindValue bools bits k x).kind.width bs m
        initial mems (kindValue bools bits k x).toNat := by
  have htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (ListScopeDN bs leafOf) := by
    intro body0 hopen
    obtain ⟨sp, b, hb, hl, hT, hi⟩ := hbody body0 hopen
    exact telescopeIn_of_lamsN htel hb hl hT hi
  have hleaf : ∀ ids : List FVarId, ids.length = bs.length →
      (leafOf ids).isLambda = false ∧ SignalTyped (leafOf ids) := by
    intro ids hlen
    obtain ⟨f, a, n, ty, b, bi, he, _⟩ := hshape ids hlen
    refine ⟨?_, hres ids hlen⟩
    rw [he]
    first | done | rfl
  rcases list_entry_outputDN_at L (cfe := true) (bs := bs) (leafOf := leafOf)
      (fun _ => old) (fun _ => mixed) (fun _ => hmach) htele hleaf hr with
    hit | ⟨ids, cache, hlen, hnd, H⟩
  · exact Or.inl hit
  · obtain ⟨x, hx⟩ := AtIdx.transfer bs ids i (nm, k) hlen hfield
    refine Or.inr ⟨ids, x, cache, hlen, hnd, hx, ?_⟩
    intro bools bits initial mems values
    obtain ⟨f, a, n, ty, b, bi, he, hfnL⟩ := hshape ids hlen
    have hk' := hkind ids hlen
    have hw := hwhnf ids x hlen hx
    rw [he] at hk'
    rw [he] at hw
    have hin : Tools.ShippingUnifiedMeaning.inputValues
        (setupOf declName bs ids cache bools bits).bools
        (setupOf declName bs ids cache bools bits).bits x =
        some (kindValue bools bits k x) :=
      prepare_inputValue (bools := bools) (bits := bits) bs ids i
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          declName.toString) nm k x hnd hfield hx hk
    have dom : LeafDom (setupOf declName bs ids cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName bs ids cache bools bits).bools
          (setupOf declName bs ids cache bools bits).bits)
        "out" true (leafOf ids) (kindValue bools bits k x) := by
      rw [he]
      exact leafDom_betaWire hfnL hk' hw hin
    have pos : 0 < (kindValue bools bits k x).kind.width := by
      rw [kindValue_width]
      exact hpos
    exact H bools bits initial mems values (kindValue bools bits k x) pos dom

/-- **The projection class, no memo disjunct, when the start world's memo has
no entry for the declaration.** Premises: those of `proj_entry_output` (the
run in `RunsTo` form), the boundary `L`, and the miss at the start world. -/
theorem proj_entry_output_miss (L : RefLawsM mref cref)
    {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Design} {i : Nat} {nm : Name} {k : MixedGateBinder}
    {w w' : Void IO.RealWorld}
    (hmiss : (L.mval w).get? declName = none)
    (old : certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htel : LamTelescopeND)
    (hbody : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      ∃ (sp : List (Name × Lean.Expr × BinderInfo)) (b : Lean.Expr),
        stripMemoizeWrappers body0 = lams sp b ∧
        b.isLambda = false ∧
        TypesOkFrom sp bs #[] ∧
        ∀ ids : List FVarId, ids.length = bs.length →
          b.instantiateRevRange 0 (ids.map Lean.Expr.fvar).toArray.size
            (ids.map Lean.Expr.fvar).toArray = leafOf ids)
    (hfield : AtIdx bs i (nm, k)) (hk : k ≠ MixedGateBinder.domain)
    (hpos : 0 < kindWidth k)
    (hshape : ∀ ids : List FVarId, ids.length = bs.length →
      ∃ (f a : Lean.Expr) (n : Name) (ty b : Lean.Expr) (bi : BinderInfo),
        leafOf ids = Lean.Expr.app f a ∧
        (Lean.Expr.app f a).getAppFn = Lean.Expr.lam n ty b bi)
    (hkind : ∀ ids : List FVarId, ids.length = bs.length →
      fallbackKind (leafOf ids) = .other)
    (hwhnf : ∀ (ids : List FVarId) (x : FVarId), ids.length = bs.length → AtIdx ids i x →
      WhnfIsVar (leafOf ids) x)
    (hres : ∀ ids : List FVarId, ids.length = bs.length → SignalTyped (leafOf ids))
    (hr : RunsTo (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf declName [] false true (.defnInfo dv) isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (ids : List FVarId) (x : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.length = bs.length ∧ ids.Nodup ∧ AtIdx ids i x ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          declName.toString) →
      Tools.ShippingMixedEntrySoundness.RawValueAt (kindValue bools bits k x).kind.width bs m
        initial mems (kindValue bools bits k x).toNat := by
  rcases proj_entry_output_at L (i := i) (nm := nm) (k := k) old mixed hmach htel hbody hfield
      hk hpos hshape hkind hwhnf hres hr with hit | H
  · rw [hmiss] at hit
    cases hit
  · exact H

/-! ## The outermost entry -/

/-- The entry hands on the declaration AS READ when no gate accepts its
unfolding either (the legacy route's case of `entryConst`). -/
theorem entryConst_legacy_kept {ci : ConstantInfo} {isInst : Lean.Expr → Bool}
    {inl : Lean.Expr → Lean.Expr} {projs : StructEnv}
    (h1 : certifiedShape? false [] (inlinedConst inl ci) = none)
    (h2 : mixedCertifiedShape? false [] (inlinedConst inl ci) isInst = none)
    (h3 : machineShape? false [] (inlinedConst inl ci) projs = none) :
    entryConst true false [] ci isInst inl projs = ci := by
  unfold entryConst
  split
  · rw [h1, h2, h3]
    first
      | done
      | rfl
      | simp
  · rfl

/-- **`EntryConstIs` from reflection facts**: every read of the declaration
in these contexts and state references returns the definition `dv`, and for
every environment read there no gate accepts its unfolding. -/
theorem entryConstIs_of_reads {declName : Name} {dv : DefinitionVal}
    (hci : ∀ (w1 : Void IO.RealWorld) (ci : ConstantInfo) (w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 → ci = .defnInfo dv)
    (hinl : ∀ (envR : Environment) (w5 w6 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
      certifiedShape? false [] (inlinedConst (userInliner envR) (.defnInfo dv)) = none ∧
      mixedCertifiedShape? false [] (inlinedConst (userInliner envR) (.defnInfo dv))
        (Sparkle.Compiler.Elab.instancePredicate envR) = none ∧
      machineShape? false [] (inlinedConst (userInliner envR) (.defnInfo dv))
        (structEnv envR) = none) :
    EntryConstIs mctx mref cctx cref declName dv := by
  unfold EntryConstIs
  intro ci envR w1 w2 w5 w6 hget henv
  obtain ⟨h1, h2, h3⟩ := hinl envR w5 w6 henv
  rw [hci w1 ci w2 hget]
  exact entryConst_legacy_kept h1 h2 h3

/-- **The depth-0 miss, derived.** A returning run of the core entry from a
world at synthesis depth 0 (quiet), on a declaration whose entry constant is
`.defnInfo dv` and is declined by the three gates: the legacy arm's read of
the memo IN THIS RUN (at `wr`) returns a map with no entry — for any name, so
in particular for `declName`. From the reset (`memoSet`), the frame of the
enumerated operations up to `synthesizeFromConst` (`outer_reset_reaches`) and
of the one `getEnv` inside it (`legacy_entry_walk_at`), and `memoGet`. -/
theorem outer_miss (L : RefLawsM mref cref) {declName : Name} {dv : DefinitionVal}
    {m : Sparkle.IR.AST.Module} {d : Design} {w w' : Void IO.RealWorld}
    (h0 : L.dval w = 0) (hq : L.quiet w)
    (hconst : EntryConstIs mctx mref cctx cref declName dv)
    (old : certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : ∀ (envR : Environment) (w5 w6 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
      mixedCertifiedShape? false [] (.defnInfo dv)
        (Sparkle.Compiler.Elab.instancePredicate envR) = none)
    (hmach : ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref
      w (m, d) w') :
    ∃ (memo : Std.HashMap Name (Sparkle.IR.AST.Module × Design)) (wr wr' : Void IO.RealWorld),
      RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref wr memo wr' ∧
      L.mval wr = {} ∧ ∀ n : Name, memo.get? n = none := by
  obtain ⟨b, envR, ci, w1, w2, w3, w4, w5, w6, hget, henv, hrun, hempty⟩ :=
    outer_reset_reaches L h0 hq hr
  rw [hconst ci envR w1 w2 w5 w6 hget henv] at hrun
  obtain ⟨memo, wr, wr', hg, hv, _⟩ :=
    legacy_entry_walk_at L (P := fun _ _ _ => True) (cfe := true)
      (fun _ => old) (fun _ => mixed envR w5 w6 henv) (fun _ => hmach) hrun
  have hE : L.mval wr = {} := hv.trans hempty
  have e : memo = {} := (L.read hg).trans hE
  subst e
  exact ⟨_, wr, wr', hg, hE, fun n => Tools.ShippingMemo.get?_empty n⟩

/-- **The projection class at the OUTERMOST entry, with no memo disjunct.**
A returning run of the core entry `synthesizeCombinationalCore declName []
false` (the form the machine-route endpoints use) from a world at synthesis
depth 0, under the extended boundary: the module's `out` carries the value
of the input bound for the field's binder.

Premises: the boundary (`L`, `L.dval w = 0`, `L.quiet w`); `EntryConstIs` —
the entry constant of this run is `.defnInfo dv` (the old theorem was about
`synthesizeFromConst` on a given constant and did not need it); and the
premises of `proj_entry_output`, `mixed` for the instance predicate of the
environment the run read. -/
theorem proj_entry_output_outer (L : RefLawsM mref cref) {declName : Name}
    {dv : DefinitionVal}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Design} {i : Nat} {nm : Name} {k : MixedGateBinder}
    {w w' : Void IO.RealWorld}
    (h0 : L.dval w = 0) (hq : L.quiet w)
    (hconst : EntryConstIs mctx mref cctx cref declName dv)
    (old : certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : ∀ (envR : Environment) (w5 w6 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
      mixedCertifiedShape? false [] (.defnInfo dv)
        (Sparkle.Compiler.Elab.instancePredicate envR) = none)
    (hmach : ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htel : LamTelescopeND)
    (hbody : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      ∃ (sp : List (Name × Lean.Expr × BinderInfo)) (b : Lean.Expr),
        stripMemoizeWrappers body0 = lams sp b ∧
        b.isLambda = false ∧
        TypesOkFrom sp bs #[] ∧
        ∀ ids : List FVarId, ids.length = bs.length →
          b.instantiateRevRange 0 (ids.map Lean.Expr.fvar).toArray.size
            (ids.map Lean.Expr.fvar).toArray = leafOf ids)
    (hfield : AtIdx bs i (nm, k)) (hk : k ≠ MixedGateBinder.domain)
    (hpos : 0 < kindWidth k)
    (hshape : ∀ ids : List FVarId, ids.length = bs.length →
      ∃ (f a : Lean.Expr) (n : Name) (ty b : Lean.Expr) (bi : BinderInfo),
        leafOf ids = Lean.Expr.app f a ∧
        (Lean.Expr.app f a).getAppFn = Lean.Expr.lam n ty b bi)
    (hkind : ∀ ids : List FVarId, ids.length = bs.length →
      fallbackKind (leafOf ids) = .other)
    (hwhnf : ∀ (ids : List FVarId) (x : FVarId), ids.length = bs.length → AtIdx ids i x →
      WhnfIsVar (leafOf ids) x)
    (hres : ∀ ids : List FVarId, ids.length = bs.length → SignalTyped (leafOf ids))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref
      w (m, d) w') :
    ∃ (ids : List FVarId) (x : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.length = bs.length ∧ ids.Nodup ∧ AtIdx ids i x ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          declName.toString) →
      Tools.ShippingMixedEntrySoundness.RawValueAt (kindValue bools bits k x).kind.width bs m
        initial mems (kindValue bools bits k x).toNat := by
  obtain ⟨b, envR, ci, w1, w2, w3, w4, w5, w6, hget, henv, hrun, hempty⟩ :=
    outer_reset_reaches L h0 hq hr
  rw [hconst ci envR w1 w2 w5 w6 hget henv] at hrun
  have hmiss : (L.mval w3).get? declName = none := by
    rw [hempty]
    first
      | done
      | exact Tools.ShippingMemo.get?_empty declName
  exact proj_entry_output_miss L (i := i) (nm := nm) (k := k) hmiss old
    (mixed envR w5 w6 henv) hmach htel hbody hfield hk hpos hshape hkind hwhnf hres hrun

end Tools.ShippingLegacySem

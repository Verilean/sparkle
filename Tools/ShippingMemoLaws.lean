import Tools.ShippingChildRun

/-! # The per-synthesis memo `sparkleSubModuleCache` in the runtime boundary

**This file EXTENDS the trust base.** `RefLawsM` is `RefLaws`
(`Tools/ShippingChildInv.lean`) plus laws about ONE more cell, the memo
`sparkleSubModuleCache`. Like `RefLaws` it is a parameter — never proved
against the runtime, and nothing here says the laws are consistent with it.
A theorem under `RefLawsM` is a theorem under MORE assumptions than one under
`RefLaws`. It is not a completion of the general theorem.

**One boundary.** `RefLawsM mref cref` is a structure extending
`RefLaws mref cref`: the same state references, the same worlds
(`Void IO.RealWorld`), the same reading of a run (`RunsTo`). The memo's value
in a world is one more value function (`mval`) next to `val`, `sval`, `dval`
of the SAME witness. There is no second `Nonempty` witness: a consumer that
needs both the child cache's laws and the memo's takes one `L : RefLawsM` and
uses `L.toRefLaws` where `RefLaws` is asked.

**What is added** (each field is an assumption):

* `mval` — the memo's map in each world;
* `memoGet`, `memoSet`, `memoModify` — a successful `get` / `set` / `modify`
  of the memo is a functional read / write of `mval`;
* `distinct` — each ref of the enumerated class `MemoOther` is not the memo
  (`¬ HEq r sparkleSubModuleCache`). NOT provable in the logic: an
  `initialize` constant is opaque, and `sparkleChildCache` has the memo's own
  type. It is the assumption "two `initialize … ← IO.mkRef` declarations
  allocate two cells";
* `memoFrame` — a successful run of an operation of the enumerated class
  `MemoFrameOp` leaves `mval`. The class has THREE constructors: a `set` of a
  ref of `MemoOther` that is not the memo (the side condition is an argument
  of the constructor), `getConstInfo`, `getEnv`.

**What is NOT added**: no law about what the memo contains (nothing says a
stored result is correct, nothing says a read misses); no frame for the
memo's own operations; no frame for a callback, a translator run, a harness,
a diagnostic operation or any ref outside `MemoOther`. `RefLaws.frame` cannot
serve as the memo's frame: its class `Framed` contains the memo's own `set` /
`modify` (`SideRef.subModule`), which change `mval`.

**Proved here** (`outer_reset_reaches`): a returning run of the core entry
`synthesizeCombinationalCore declName [] false` that starts at synthesis
depth 0 in a quiet world reaches `synthesizeFromConst` in a world where the
memo is EMPTY — the reset `sparkleSubModuleCache.set {}`, then eight `set`s
of other refs, the depth's `set`, `getConstInfo`, `getEnv`, each of the
enumerated class. The steps are those of `core_reads_inv`
(`Tools/ShippingChildRun.lean`) and `core_keeps`
(`Tools/ShippingChildKeeps.lean`), which were built: two `pure`s, three
`set`s (type cache and its two counters), THE RESET, the child cache's
`set`, seven `set`s, the depth's `set`, the `try`, `getConstInfo`, `getEnv`. -/
namespace Tools.ShippingMemo
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingChildInv
open Sparkle.Compiler.Elab

/-- **The refs written between the memo's reset and its read** at an
outermost entry — an enumeration, by name. Each is declared by its own
`initialize` in `Sparkle/Compiler/Elab.lean`; `sparkleChildCache` has the
memo's type, the others have other types. -/
inductive MemoOther : {σ : Type} → IO.Ref σ → Prop
  | childCache : MemoOther sparkleChildCache
  | subInstOut : MemoOther sparkleSubInstanceOutputs
  | singleOut : MemoOther sparkleSingleOutInstanceCache
  | fvarValue : MemoOther sparkleFvarValueMap
  | wireWidth : MemoOther sparkleWireWidthCache
  | letWire : MemoOther sparkleLetWireCache
  | loopWire : MemoOther sparkleLoopWireCache
  | wireCanon : MemoOther sparkleWireCanon
  | synthDepth : MemoOther sparkleSynthDepth

/-- **The operations between the memo's reset and its read**, enumerated.
`otherSet` carries its side condition: the ref is one of `MemoOther` AND it
is not the memo. No constructor is a callback, a recursive call, a
diagnostic operation or an operation of the memo itself. -/
inductive MemoFrameOp : {α : Type} → MetaM α → Prop
  | otherSet {σ : Type} (r : IO.Ref σ) (v : σ) : MemoOther r →
      ¬ HEq r sparkleSubModuleCache → MemoFrameOp (ST.Ref.set r v : MetaM Unit)
  | constInfo (n : Name) : MemoFrameOp (getConstInfo n : MetaM _)
  | env : MemoFrameOp (getEnv : MetaM Environment)

/-- **The runtime boundary with the memo** (a parameter, never proved): the
generic laws `RefLaws` of the SAME state references and worlds, and the
memo's value with its get / set / modify laws, the assumed distinctness of
the enumerated refs from the memo, and the frame of the enumerated
operations — on successful runs. -/
structure RefLawsM (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) extends RefLaws mref cref where
  /-- The memo's map in each world. -/
  mval : Void IO.RealWorld → Std.HashMap Name Res
  /-- A successful read returns the memo's map and leaves it. -/
  memoGet : ∀ {mctx : Meta.Context} {cctx : Core.Context} w m w',
    RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref w m w' →
    m = mval w ∧ mval w' = mval w
  /-- After a successful `set v` the memo's map is `v`. -/
  memoSet : ∀ {mctx : Meta.Context} {cctx : Core.Context} v w u w',
    RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w' → mval w' = v
  /-- After a successful `modify f` the memo's map is `f` of what it was. -/
  memoModify : ∀ {mctx : Meta.Context} {cctx : Core.Context}
    (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleSubModuleCache.modify f : MetaM Unit) mctx mref cctx cref w u w' →
    mval w' = f (mval w)
  /-- ASSUMED: an enumerated ref is not the memo. -/
  distinct : ∀ {σ : Type} (r : IO.Ref σ), MemoOther r → ¬ HEq r sparkleSubModuleCache
  /-- A successful run of an enumerated operation leaves the memo's map. -/
  memoFrame : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type} (p : MetaM α),
    MemoFrameOp p → ∀ w a w', RunsTo p mctx mref cctx cref w a w' → mval w' = mval w

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The empty memo has no entry. -/
theorem get?_empty (n : Name) : ({} : Std.HashMap Name Res).get? n = none := by
  first
    | simp
    | exact Std.HashMap.get?_empty
    | rfl

namespace RefLawsM
variable (L : RefLawsM mref cref)

/-- A `set` of an enumerated ref leaves the memo (the distinctness is the
boundary's own assumption `distinct`). -/
theorem setOther {σ : Type} {r : IO.Ref σ} (hr : MemoOther r) {v : σ} {w u w'}
    (h : RunsTo (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref w u w') :
    L.mval w' = L.mval w :=
  L.memoFrame _ (MemoFrameOp.otherSet r v hr (L.distinct r hr)) w u w' h

theorem constInfoSame {n : Name} {w ci w'}
    (h : RunsTo (getConstInfo n : MetaM _) mctx mref cctx cref w ci w') :
    L.mval w' = L.mval w :=
  L.memoFrame _ (MemoFrameOp.constInfo n) w ci w' h

theorem envSame {w e w'}
    (h : RunsTo (getEnv : MetaM Environment) mctx mref cctx cref w e w') :
    L.mval w' = L.mval w :=
  L.memoFrame _ MemoFrameOp.env w e w' h

/-- What a read returns, by the start world's value. -/
theorem read {w m w'}
    (h : RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref w m w') :
    m = L.mval w :=
  (L.memoGet w m w' h).1

end RefLawsM

/-- **The outermost entry reaches `synthesizeFromConst` with an EMPTY memo.**
A returning run of the core entry from a world where the synthesis depth
reads 0 (`L.dval w = 0`) and the diagnostic environment is quiet (the profile
logger runs before the depth is read: its frame is `RefLaws.diag`, asked in a
quiet world): the run reads the declaration and the environment, and runs
`synthesizeFromConst` on the entry constant with its own logger from a world
`w3` in which the memo's map is `{}`.

Derived, not assumed: `memoSet` at the reset, then `memoFrame` at each of the
eleven operations between the reset and `w3`. -/
theorem outer_reset_reaches (L : RefLawsM mref cref) {declName : Name}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (h0 : L.dval w = 0) (hq : L.quiet w)
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w') :
    ∃ (b : Bool) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire e h t n) (profLogIO b)
        declName [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref w3 (M, D) w4 ∧
      L.mval w3 = {} := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
  obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
  obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
  -- the depth this run read is the start world's: the profile variable's
  -- read is framed, the logger is a diagnostic operation in a quiet world
  have q1 := L.toRefLaws.sameQ (.ioEnv _) s1 hq
  obtain ⟨⟨_, _, c2⟩, _⟩ := L.toRefLaws.sameD (.profLog _ _) s2 q1
  have hd : d = L.dval w := by
    rw [L.toRefLaws.depthGet _ _ _ s3, c2, (L.toRefLaws.same (.ioEnv _) s1).2.2]
  -- a returning run passed the depth guard
  rcases RunsTo.ite h with h | h
  · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
    exact (throwError_not_runs _ ht).elim
  have hz : (d == 0) = true := by
    first
      | (rw [hd, h0]; first | done | rfl)
      | simp [hd, h0]
  simp only [hz, ↓reduceIte] at h
  obtain ⟨_, _, _, h⟩ := RunsTo.bind h        -- pure: the saved fvar map
  obtain ⟨_, _, _, h⟩ := RunsTo.bind h        -- pure: the saved width cache
  obtain ⟨_, _, _, h⟩ := RunsTo.bind h        -- pure: the saved let-wire cache
  obtain ⟨_, _, _, h⟩ := RunsTo.bind h        -- pure: the saved loop-wire cache
  obtain ⟨_, _, _, h⟩ := RunsTo.bind h        -- pure: the saved alias map
  obtain ⟨_, _, _, h⟩ := RunsTo.bind h        -- sparkleTypeCache.set
  obtain ⟨_, _, _, h⟩ := RunsTo.bind h        -- sparkleTypeCacheHits.set
  obtain ⟨_, _, _, h⟩ := RunsTo.bind h        -- sparkleTypeCacheMiss.set
  obtain ⟨_, x0, hreset, h⟩ := RunsTo.bind h  -- THE RESET: sparkleSubModuleCache.set {}
  obtain ⟨_, x1, e1, h⟩ := RunsTo.bind h      -- sparkleChildCache.set
  obtain ⟨_, x2, e2, h⟩ := RunsTo.bind h      -- sparkleSubInstanceOutputs.set
  obtain ⟨_, x3, e3, h⟩ := RunsTo.bind h      -- sparkleSingleOutInstanceCache.set
  obtain ⟨_, x4, e4, h⟩ := RunsTo.bind h      -- sparkleFvarValueMap.set
  obtain ⟨_, x5, e5, h⟩ := RunsTo.bind h      -- sparkleWireWidthCache.set
  obtain ⟨_, x6, e6, h⟩ := RunsTo.bind h      -- sparkleLetWireCache.set
  obtain ⟨_, x7, e7, h⟩ := RunsTo.bind h      -- sparkleLoopWireCache.set
  obtain ⟨_, x8, e8, h⟩ := RunsTo.bind h      -- sparkleWireCanon.set
  obtain ⟨_, x9, e9, h⟩ := RunsTo.bind h      -- sparkleSynthDepth.set
  obtain ⟨_, h⟩ := RunsTo.try_finally h
  obtain ⟨ci, y1, hget, h⟩ := RunsTo.bind h
  obtain ⟨env, y2, henv, h⟩ := RunsTo.bind h
  have m0 : L.mval x0 = {} := L.memoSet _ _ _ _ hreset
  have m1 : L.mval x1 = {} := (L.setOther MemoOther.childCache e1).trans m0
  have m2 : L.mval x2 = {} := (L.setOther MemoOther.subInstOut e2).trans m1
  have m3 : L.mval x3 = {} := (L.setOther MemoOther.singleOut e3).trans m2
  have m4 : L.mval x4 = {} := (L.setOther MemoOther.fvarValue e4).trans m3
  have m5 : L.mval x5 = {} := (L.setOther MemoOther.wireWidth e5).trans m4
  have m6 : L.mval x6 = {} := (L.setOther MemoOther.letWire e6).trans m5
  have m7 : L.mval x7 = {} := (L.setOther MemoOther.loopWire e7).trans m6
  have m8 : L.mval x8 = {} := (L.setOther MemoOther.wireCanon e8).trans m7
  have m9 : L.mval x9 = {} := (L.setOther MemoOther.synthDepth e9).trans m8
  have m10 : L.mval y1 = {} := (L.constInfoSame hget).trans m9
  have m11 : L.mval y2 = {} := (L.envSame henv).trans m10
  exact ⟨prof.isSome, env, ci, _, y1, _, _, _, _, hget, henv, h, m11⟩

/-- **The entry constant of this run is the definition `dv`**: whatever
declaration and environment a run in these contexts and state references
reads, the constant the entry hands to `synthesizeFromConst` is `.defnInfo
dv`. A reflection of the environment, in the style of `EnvDefines`
(`Tools/ShippingEntrySoundness.lean`) — the link between a theorem about
`synthesizeFromConst` on a GIVEN constant and the entry, which reads it. -/
def EntryConstIs (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (dv : DefinitionVal) : Prop :=
  ∀ (ci : ConstantInfo) (envR : Environment) (w1 w2 w5 w6 : Void IO.RealWorld),
    RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
    entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
      (userInliner envR) (structEnv envR) = .defnInfo dv

/-! ## How the machine route's boundary is re-read

`ChildLaws mref cref = Nonempty (RefLaws mref cref)` and `ChildBnd mref cref
w = ∃ L : RefLaws mref cref, StartV L w ∧ L.quiet w` are the machine route's
boundary. With the memo they are read over the ONE extended structure; the
old ones follow by projection (`toRefLaws`), so a consumer never holds two
unrelated witnesses. Nothing of the machine route is changed. -/

/-- The context-level boundary with the memo: the extended laws exist. -/
def ChildLawsM (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) :
    Prop :=
  Nonempty (RefLawsM mref cref)

/-- The boundary of a run starting in `w`, with the memo: ONE witness of the
extended laws, with the start condition and quietness by ITS values. -/
def ChildBndM (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) : Prop :=
  ∃ L : RefLawsM mref cref, StartV L.toRefLaws w ∧ L.quiet w

theorem ChildLawsM.toChildLaws (h : ChildLawsM mref cref) : ChildLaws mref cref := by
  obtain ⟨L⟩ := h
  exact ⟨L.toRefLaws⟩

theorem ChildBndM.toChildBnd {w : Void IO.RealWorld} (h : ChildBndM mref cref w) :
    ChildBnd mref cref w := by
  obtain ⟨L, hs, hq⟩ := h
  exact ⟨L.toRefLaws, hs, hq⟩

end Tools.ShippingMemo

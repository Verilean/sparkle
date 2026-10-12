import Tools.ShippingMemoLaws

/-! # The outermost entry with ANY translator and either front end

`outer_reset_reaches` (`Tools/ShippingMemoLaws.lean`) is about
`synthesizeCombinationalCore declName [] false` — the real translator, the
certified front end on. A declaration like `useDbl` reaches the legacy arm
only with the front end OFF (with it on, `entryConst` hands over the unfolded
constant and a certified gate takes it), and the tests run the entry with
other translators. Here the same statement for
`synthesizeCombinationalCoreWith translate declName [] false cfe`, any
`translate`, any `cfe`: the prefix between the reset and `synthesizeFromConst`
does not depend on either (they are only passed on).

The proof is `outer_reset_reaches`'s, step for step (it was written without a
build; this copy shares its unverified points). Same boundary, same
assumptions: `RefLawsM` — an EXTENSION of the trust base.

* `outer_reset_reaches_with` — the entry reaches `synthesizeFromConst … cfe
  (entryConst cfe false [] ci …)` in a world with an empty memo;
* `entryConst_off` — with the front end off the entry constant is the
  declaration as read. -/
namespace Tools.ShippingMemo
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingChildInv
open Sparkle.Compiler.Elab

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- With the certified front end off the entry hands on the declaration as
read. -/
theorem entryConst_off (ci : ConstantInfo) (isInst : Lean.Expr → Bool)
    (inl : Lean.Expr → Lean.Expr) (projs : StructEnv) :
    entryConst false false [] ci isInst inl projs = ci := by
  unfold entryConst
  first
    | rfl
    | simp

/-- **The outermost entry reaches `synthesizeFromConst` with an EMPTY memo**,
for any translator and either front end. -/
theorem outer_reset_reaches_with (L : RefLawsM mref cref) {translate : TranslateFn}
    {declName : Name} {cfe : Bool}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (h0 : L.dval w = 0) (hq : L.quiet w)
    (h : RunsTo (synthesizeCombinationalCoreWith translate declName [] false cfe)
      mctx mref cctx cref w (M, D) w') :
    ∃ (b : Bool) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      RunsTo (synthesizeFromConst translate (profLogIO b) declName [] false cfe
        (entryConst cfe false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref w3 (M, D) w4 ∧
      L.mval w3 = {} := by
  unfold synthesizeCombinationalCoreWith at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
  obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
  obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
  have q1 := L.toRefLaws.sameQ (.ioEnv _) s1 hq
  obtain ⟨⟨_, _, c2⟩, _⟩ := L.toRefLaws.sameD (.profLog _ _) s2 q1
  have hd : d = L.dval w := by
    rw [L.toRefLaws.depthGet _ _ _ s3, c2, (L.toRefLaws.same (.ioEnv _) s1).2.2]
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

end Tools.ShippingMemo

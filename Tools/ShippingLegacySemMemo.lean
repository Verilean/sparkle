import Tools.ShippingEntrySoundness

/-! # The memo read of the legacy entry: the heap laws that are missing

**SUPERSEDED (kept as the round-13 sketch; nothing imports this file).** The
structure `MemoLaws` below is a STANDALONE parameter: a witness of it is
unrelated to a witness of `RefLaws`, so the two must not be combined in one
statement. The boundary to use is `RefLawsM`
(`Tools/ShippingMemoLaws.lean`): ONE structure extending `RefLaws` over the
same state references and worlds, with an enumerated frame class in place of
the hypothesis `hframe` here; the miss is derived there
(`outer_reset_reaches`) and in `Tools/ShippingLegacySemMemoWalk.lean`
(`outer_miss`, `proj_entry_output_outer`).

`legacy_entry_walk` (`Tools/ShippingLegacySemEntryWalk.lean`) has a second
outcome, `MemoHit`: the legacy arm of `synthesizeFromConst` first reads
`sparkleSubModuleCache` and returns a cached result on a hit. At an OUTERMOST
entry (`sparkleSynthDepth` = 0) `synthesizeCombinationalCoreWith` executes
`sparkleSubModuleCache.set {}` before it calls `synthesizeFromConst`, so the
read misses — a fact about the heap.

**What exists** (`Tools/ShippingChildInv.lean`): `RefLaws` has value
functions and get / set / modify laws for THREE cells — `sparkleChildCache`
(`val`, `cacheGet`, `cacheSet`, `cacheModify`), `sparkleChildSynth` (`sval`,
`synthGet`, …) and `sparkleSynthDepth` (`dval`, `depthGet`, `depthSet`, …).
`sparkleSubModuleCache` occurs there only as `SideRef.subModule` (line 73):
a member of the FRAME class — its operations leave the three tracked values
(`RefLaws.frame` through `Framed.sideGetIO` / `sideSetIO` / `sideModify`).
There is no value function for it and no get-after-set law.

**The laws needed, named** (`MemoLaws`, a parameter in the style of `RefLaws`
— generic runtime laws, never proved):

* `mval` — the memo's map in each world;
* `memoGet` — a successful `sparkleSubModuleCache.get` returns `mval`;
* `memoSet` — after a successful `sparkleSubModuleCache.set v`, `mval` is `v`.

and, to carry the value from the `set {}` to the read, a FRAME law of `mval`
for the operations in between — at an outermost legacy-front-end entry these
are: eight `set`s of other cells (`sparkleChildCache`,
`sparkleSubInstanceOutputs`, `sparkleSingleOutInstanceCache`,
`sparkleFvarValueMap`, `sparkleWireWidthCache`, `sparkleLetWireCache`,
`sparkleLoopWireCache`, `sparkleWireCanon`), `sparkleSynthDepth.set`,
`getConstInfo`, `getEnv`. `Framed` cannot be reused for this as it is: it
CONTAINS the memo's own `set` / `modify` (as `SideRef.subModule`), which do
change `mval`. The frame is therefore a hypothesis of the lemma below
(`hframe`), to be replaced by a frame class without `SideRef.subModule`.

**Proved here**: `memo_miss_after_reset` — from the three laws and the frame
between the two worlds, the read after a reset finds no entry.

**NOT done**: the statement one level up without the `MemoHit` disjunct. It
needs (1) `legacy_entry_walk` in `RunsTo` form — `MemoHit` there is "SOME run
of the read returned a hit" (`MReturns`), which no heap law can refute; it
has to be "THIS run's read, at this world"; (2) the walk of
`synthesizeCombinationalCoreWith` in `RunsTo` form down to the call
(`RunsTo.bind`, `RunsTo.try_finally` exist), with `dval w = 0` as the
outermost-entry premise (`RefLaws.depthGet`); (3) the frame class above. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness (RunsTo)

/-- The runtime laws of the per-synthesis memo `sparkleSubModuleCache` (a
parameter; not proved, like `RefLaws`). -/
structure MemoLaws (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) where
  mval : Void IO.RealWorld →
    Std.HashMap Lean.Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)
  memoGet : ∀ {mctx : Meta.Context} {cctx : Core.Context} w m w',
    RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref w m w' → m = mval w
  memoSet : ∀ {mctx : Meta.Context} {cctx : Core.Context} v w u w',
    RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w' → mval w' = v

/-- **The read after a reset misses**: the memo was set to the empty map at
`w0`, its value is the same at `w2` as right after the reset (`hframe`), and
it is read at `w2`. -/
theorem memo_miss_after_reset {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (L : MemoLaws mref cref)
    {mctx mctx' : Meta.Context} {cctx cctx' : Core.Context}
    {w0 w1 w2 w3 : Void IO.RealWorld} {u : Unit}
    {memo : Std.HashMap Lean.Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    (hset : RunsTo (sparkleSubModuleCache.set {} : MetaM Unit) mctx mref cctx cref w0 u w1)
    (hframe : L.mval w2 = L.mval w1)
    (hget : RunsTo (sparkleSubModuleCache.get : MetaM _) mctx' mref cctx' cref w2 memo w3)
    (declName : Lean.Name) : memo.get? declName = none := by
  have h1 := L.memoSet _ _ _ _ hset
  have h2 := L.memoGet _ _ _ hget
  rw [h2, hframe, h1]
  first
    | exact Std.HashMap.get?_empty
    | simp
    | rfl

end Tools.ShippingLegacySem

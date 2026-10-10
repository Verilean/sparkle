import Tools.ShippingMachineEntry

/-! # The child cache's invariant: definitions and the generic runtime laws

A machine-route parent's children come from `synthesizeChild` (read from
`sparkleChildSynth`), which memoises the real entry in `sparkleChildCache`.
Both are `IO.Ref`s: their contents are opaque in the logic, so what a read
returns is a property of the WORLD the read runs in. The invariant is stated
per world and proved to be kept by the real run — on EVERY outcome, a failing
run included — instead of assuming that every read in every world is sound.

This file holds the definitions; the proofs are in
`Tools/ShippingChildKeeps.lean` (every outcome, the recursion closed by
induction on the synthesis depth) and `Tools/ShippingChildRun.lean` (what a
successful run of the entry gives its closings).

* `RealChild c r` (inductive): `r` is returned by a run of the real entry
  `synthesizeCombinational c` that STARTS in a world satisfying the
  invariant. The induction is the order in which results enter the cache.
* `InvW w` / `StartW w`: the invariant, and the start condition of an entry
  run (the synthesis ref; and depth 0 or the cache invariant), by what reads
  in `w` return.
* Everything about the invariant depends on the two STATE REFERENCES only,
  not on the Meta and Core contexts: those change inside a run
  (`withLocalDecl`, …) and a child may be synthesised under a changed
  context. A `RealChild`'s run is in SOME contexts; the laws and the
  relative conditions are for EVERY context.
* `endW m … w`: the world a run of `m` from `w` ENDS in, whether it returns
  or throws. `Keeps I m`: from a world satisfying `I`, `m` ends in one.
* `RefLaws` — GENERIC runtime laws, a parameter. The three refs' values per
  world (cache, synthesis ref, synthesis depth); what a successful `get` /
  `set` / `modify` of each does; and the FRAME of the listed operations
  (`Framed`: on every outcome they leave the three values). Nothing about the
  compiler's invariant is in them. That a ref operation cannot fail is NOT a
  law: it is proved from the lift's definition (`refGet_runs` …).
* `BodyRel` / `TranslateRel` — the compiler-specific conditions NOT proved.
  They are RELATIVE: `synthesizeFromConst` with the entry's own logger (resp.
  the translator `translateExprToWire`) keeps the invariant at depth `D` on
  every outcome PROVIDED the memoised child entry does at that depth. The
  machine route's harness around the translator is proved (`harnessRel_of`). They do not presuppose that the entry keeps the
  invariant: that is a theorem (`entry_keeps`), by induction on the depth
  (the entry refuses to start at `sparkleSynthDepthLimit`, and every child
  synthesis runs one level deeper). What is inside them and opaque: the fuel
  fallback's `partial` handlers. -/
namespace Tools.ShippingChildInv
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab

abbrev Res := Sparkle.IR.AST.Module × Sparkle.IR.AST.Design

/-- The entry's profile logger (`logProf`), as the entry writes it. -/
def profLogIO (profile : Bool) (msg : String) : IO Unit := do
  if profile then
    IO.eprintln msg
    (← IO.getStderr).flush
    let h ← IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append
    h.putStrLn msg
    h.flush

/-- The entry's per-synthesis refs other than the three this file tracks. -/
inductive SideRef : {σ : Type} → IO.Ref σ → Prop
  | wireWidth : SideRef sparkleWireWidthCache
  | fvarValue : SideRef sparkleFvarValueMap
  | letWire : SideRef sparkleLetWireCache
  | loopWire : SideRef sparkleLoopWireCache
  | wireCanon : SideRef sparkleWireCanon
  | subModule : SideRef sparkleSubModuleCache
  | subInstOut : SideRef sparkleSubInstanceOutputs
  | singleOut : SideRef sparkleSingleOutInstanceCache
  | typeCache : SideRef sparkleTypeCache
  | typeHits : SideRef sparkleTypeCacheHits
  | typeMiss : SideRef sparkleTypeCacheMiss
  | callCounter : SideRef sparkleCallCounter
  | cacheHits : SideRef sparkleCacheHits

/-- The operations whose frame is a law: reads of the three tracked refs,
any operation on the other per-synthesis refs, the environment-variable read,
the entry's logger, `getConstInfo`, `getEnv`, building an error; and, for the
harness: a fresh free-variable id, the clock read, and creating or modifying
a translation cache (a ref of ANOTHER type than the three tracked ones). -/
inductive Framed : {α : Type} → MetaM α → Prop
  | cacheGet : Framed (sparkleChildCache.get : MetaM _)
  | synthGet : Framed (sparkleChildSynth.get : MetaM _)
  | depthGet : Framed (ST.Ref.get sparkleSynthDepth : MetaM Nat)
  | sideGet {σ : Type} {r : IO.Ref σ} : SideRef r → Framed (ST.Ref.get r : MetaM σ)
  | sideSet {σ : Type} {r : IO.Ref σ} (v : σ) : SideRef r → Framed (ST.Ref.set r v : MetaM Unit)
  | sideModify {σ : Type} {r : IO.Ref σ} (f : σ → σ) : SideRef r →
      Framed (ST.Ref.modify r f : MetaM Unit)
  | ioEnv (n : String) : Framed (liftM (IO.getEnv n) : MetaM _)
  | profLog (b : Bool) (msg : String) : Framed (liftM (profLogIO b msg) : MetaM Unit)
  | constInfo (n : Name) : Framed (getConstInfo n : MetaM _)
  | env : Framed (getEnv : MetaM Environment)
  | throwErr {α : Type} (msg : MessageData) : Framed (throwError msg : MetaM α)
  | freshFVar : Framed (mkFreshFVarId : MetaM FVarId)
  | monoMs : Framed (liftM IO.monoMsNow : MetaM Nat)
  | mkExprCache (v : Lean.ExprStructMap String) :
      Framed (IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String)))
  | exprCacheModify (r : IO.Ref (Lean.ExprStructMap String))
      (f : Lean.ExprStructMap String → Lean.ExprStructMap String) :
      Framed (ST.Ref.modify r f : MetaM Unit)

section Runs
variable (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
  (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)

/-- The world a run of `m` from `w` ends in, whatever its outcome. -/
def endW {α : Type} (m : MetaM α) (w : Void IO.RealWorld) : Void IO.RealWorld :=
  match m mctx mref cctx cref w with
  | .ok _ w' => w'
  | .error _ w' => w'

/-- From a world satisfying `I`, `m` ends in one — returning or throwing. -/
def Keeps {α : Type} (I : Void IO.RealWorld → Prop) (m : MetaM α) : Prop :=
  ∀ w, I w → I (endW mctx mref cctx cref m w)

end Runs

section Defs
/- The invariant depends on the two STATE REFERENCES only. The Meta and Core
contexts (local context, options, …) change inside a run (`withLocalDecl` and
the like), and a child may be synthesised under such a changed context: a
statement tied to the endpoint's own contexts would not survive that. -/
variable (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)

/-- In world `w`, a read of the synthesis ref returns `synthesizeChild`. -/
def SynthAt (w : Void IO.RealWorld) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) s w1,
    RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w s w1 → s = some synthesizeChild

/-- `r` is returned by a run of the real entry on `c` — in SOME Meta and Core
contexts, over these state references — starting in a world where the
cache's entries are `RealChild` and the synthesis ref reads
`synthesizeChild`. -/
inductive RealChild : Name → Res → Prop
  | run {c : Name} {r : Res} (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld)
      (cache : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) m w1,
        RunsTo (sparkleChildCache.get : MetaM _) mctx' mref cctx' cref w m w1 →
        ∀ c' r', m.get? c' = some r' → RealChild c' r')
      (synth : SynthAt mref cref w)
      (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') : RealChild c r

/-- Every entry of the map is a `RealChild`. -/
def CacheInv (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, m.get? c = some r → RealChild mref cref c r

/-- The cache's entries read in `w` are `RealChild`s. -/
def CacheAt (w : Void IO.RealWorld) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) m w1,
    RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w1 → CacheInv mref cref m

/-- The invariant in world `w`, by what reads in `w` return. -/
def InvW (w : Void IO.RealWorld) : Prop :=
  CacheAt mref cref w ∧ SynthAt mref cref w

/-- **The start condition of an entry run** in world `w`: the synthesis ref
reads `synthesizeChild`, and EITHER the synthesis depth reads 0 (an outermost
run: the entry clears the cache, whatever it holds) OR the cache's entries
are `RealChild`s (a nested run inherits the invariant). -/
def StartW (w : Void IO.RealWorld) : Prop :=
  SynthAt mref cref w ∧
    ((∀ (mctx : Meta.Context) (cctx : Core.Context) d w1,
        RunsTo (ST.Ref.get sparkleSynthDepth : MetaM Nat) mctx mref cctx cref w d w1 → d = 0) ∨
     CacheAt mref cref w)

/-- The children of a shape's calls, call by call: the built memory module
for a memory call, a `RealChild` of the call's declaration otherwise. -/
def ChildrenReal (shape : MachineShape) (children : List Res) : Prop :=
  children.length = shape.insts.length ∧
  ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
    (Sparkle.Compiler.MachMemory.memChild? (shape.insts[k]).1 = some y ∨
      RealChild mref cref (shape.insts[k]).1 y)

/-- **Generic runtime laws** (a parameter, never proved), for runs over these
state references in EVERY Meta and Core context. The values of the cache, of
the synthesis ref and of the synthesis depth in each world; what a SUCCESSFUL
`get` / `set` / `modify` of each returns or does to the three values; and the
frame of the operations listed in `Framed` — on EVERY outcome they leave the
three values. -/
structure RefLaws where
  val : Void IO.RealWorld → Std.HashMap Name Res
  sval : Void IO.RealWorld → Option (Name → MetaM Res)
  dval : Void IO.RealWorld → Nat
  frame : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type} (p : MetaM α), Framed p → ∀ w,
    val (endW mctx mref cctx cref p w) = val w ∧ sval (endW mctx mref cctx cref p w) = sval w ∧
      dval (endW mctx mref cctx cref p w) = dval w
  cacheGet : ∀ {mctx : Meta.Context} {cctx : Core.Context} w m w',
    RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w' → m = val w
  cacheSet : ∀ {mctx : Meta.Context} {cctx : Core.Context} v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' →
    val w' = v ∧ sval w' = sval w ∧ dval w' = dval w
  cacheModify : ∀ {mctx : Meta.Context} {cctx : Core.Context}
    (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w' →
    val w' = f (val w) ∧ sval w' = sval w ∧ dval w' = dval w
  synthGet : ∀ {mctx : Meta.Context} {cctx : Core.Context} w s w',
    RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w s w' → s = sval w
  depthGet : ∀ {mctx : Meta.Context} {cctx : Core.Context} w d w',
    RunsTo (ST.Ref.get sparkleSynthDepth : MetaM Nat) mctx mref cctx cref w d w' → d = dval w
  depthSet : ∀ {mctx : Meta.Context} {cctx : Core.Context} v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' →
    val w' = val w ∧ sval w' = sval w ∧ dval w' = v
  depthModify : ∀ {mctx : Meta.Context} {cctx : Core.Context} (f : Nat → Nat) w u w',
    RunsTo (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) mctx mref cctx cref w u w' →
    val w' = val w ∧ sval w' = sval w ∧ dval w' = f (dval w)

end Defs

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The invariant by the values (the laws' view). -/
def InvV (L : RefLaws mref cref) (w : Void IO.RealWorld) : Prop :=
  CacheInv mref cref (L.val w) ∧ L.sval w = some synthesizeChild

/-- The invariant at synthesis depth `D`. -/
def J (L : RefLaws mref cref) (D : Nat) (w : Void IO.RealWorld) : Prop :=
  InvV L w ∧ L.dval w = D

/-- A `CompilerM` action keeps `I`, from every compiler and circuit state. -/
def KeepsC (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) {α : Type} (I : Void IO.RealWorld → Prop)
    (c : CompilerM α) : Prop :=
  ∀ (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState),
    Keeps mctx mref cctx cref I (c ctx st)

/-- The memoised child entry keeps the invariant at depth `D`, on every
outcome, in every Meta and Core context. -/
def ChildKeeps (L : RefLaws mref cref) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) c,
    Keeps mctx mref cctx cref (J L D) (synthesizeChild c)

/-- **The body, relative to the child entry** (not proved): at any depth, IF
the memoised child entry keeps the invariant there, a run of
`synthesizeFromConst` with the entry's own logger keeps it — on every
outcome, in every Meta and Core context. -/
def BodyRel (L : RefLaws mref cref) : Prop :=
  ∀ D, ChildKeeps L D → ∀ (mctx : Meta.Context) (cctx : Core.Context) (b : Bool) declName ci isInst,
    Keeps mctx mref cctx cref (J L D)
      (synthesizeFromConst (fun e h t n => translateExprToWire e h t n) (profLogIO b)
        declName [] false true ci isInst)

/-- **The translator, relative to the child entry** (not proved): at any
depth, IF the memoised child entry keeps the invariant there, a run of the
translator `translateExprToWire` keeps it — on every outcome, from every
compiler state, in every Meta and Core context. -/
def TranslateRel (L : RefLaws mref cref) : Prop :=
  ∀ D, ChildKeeps L D → ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
    KeepsC mctx mref cctx cref (J L D) (translateExprToWire e hint top named)

/-- The machine route's harness, relative to the child entry: the same for
`synthesizeMixedCertified` with the entry's own logger. PROVED from
`TranslateRel` (`harnessRel_of`, `Tools/ShippingChildHarness.lean`). -/
def HarnessRel (L : RefLaws mref cref) : Prop :=
  ∀ D, ChildKeeps L D → ∀ (mctx : Meta.Context) (cctx : Core.Context) (b : Bool) declName bs body,
    Keeps mctx mref cctx cref (J L D)
      (synthesizeMixedCertified (fun e hint top named => translateExprToWire e hint top named)
        (profLogIO b) declName bs body)

section Bnd
variable (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)

/-- The context-level part of the child boundary: generic laws under which
the two relative conditions hold. The world-level part is `StartW` at the
run's start. -/
def ChildLaws : Prop :=
  ∃ L : RefLaws mref cref, BodyRel L ∧ TranslateRel L

/-- **The child boundary of a run starting in `w`**: the laws and the start
condition in the start world. -/
def ChildBnd (w : Void IO.RealWorld) : Prop :=
  ChildLaws mref cref ∧ StartW mref cref w

end Bnd

/-! ## Runs and end worlds -/

theorem endW_of_runs {α : Type} {m : MetaM α} {w a w'}
    (h : RunsTo m mctx mref cctx cref w a w') : endW mctx mref cctx cref m w = w' := by
  unfold RunsTo at h; unfold endW; rw [h]

theorem endW_of_error {α : Type} {m : MetaM α} {w e w'}
    (h : m mctx mref cctx cref w = .error e w') : endW mctx mref cctx cref m w = w' := by
  unfold endW; rw [h]

/-- A ref read cannot fail (the lift of an `ST` action returns). -/
theorem refGet_runs {σ : Type} (r : IO.Ref σ) (w : Void IO.RealWorld) :
    ∃ a w', RunsTo (ST.Ref.get r : MetaM σ) mctx mref cctx cref w a w' := by
  unfold RunsTo
  cases h : (ST.Ref.get r : ST IO.RealWorld σ) w with
  | mk a w' =>
    refine ⟨a, w', ?_⟩
    change (match (ST.Ref.get r : ST IO.RealWorld σ) w with | .mk a s => EST.Out.ok a s) = _
    rw [h]

theorem refSet_runs {σ : Type} (r : IO.Ref σ) (v : σ) (w : Void IO.RealWorld) :
    ∃ a w', RunsTo (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref w a w' := by
  unfold RunsTo
  cases h : (ST.Ref.set r v : ST IO.RealWorld Unit) w with
  | mk a w' =>
    refine ⟨a, w', ?_⟩
    change (match (ST.Ref.set r v : ST IO.RealWorld Unit) w with | .mk a s => EST.Out.ok a s) = _
    rw [h]

theorem refModify_runs {σ : Type} (r : IO.Ref σ) (f : σ → σ) (w : Void IO.RealWorld) :
    ∃ a w', RunsTo (ST.Ref.modify r f : MetaM Unit) mctx mref cctx cref w a w' := by
  unfold RunsTo
  cases h : (ST.Ref.modify r f : ST IO.RealWorld Unit) w with
  | mk a w' =>
    refine ⟨a, w', ?_⟩
    change (match (ST.Ref.modify r f : ST IO.RealWorld Unit) w with | .mk a s => EST.Out.ok a s) = _
    rw [h]

/-- A run that returns does not throw. -/
theorem not_error_of_runs {α : Type} {m : MetaM α} {w a w1 e w2}
    (h : RunsTo m mctx mref cctx cref w a w1) (hf : m mctx mref cctx cref w = .error e w2) :
    False := by
  unfold RunsTo at h; rw [h] at hf; cases hf

/-- A ref read does not depend on the Meta and Core contexts or state refs. -/
theorem refGet_ctx {σ : Type} (r : IO.Ref σ) {mctx' : Meta.Context}
    {mref' : ST.Ref IO.RealWorld Meta.State} {cctx' : Core.Context}
    {cref' : ST.Ref IO.RealWorld Core.State} {w a w'}
    (h : RunsTo (ST.Ref.get r : MetaM σ) mctx mref cctx cref w a w') :
    RunsTo (ST.Ref.get r : MetaM σ) mctx' mref' cctx' cref' w a w' := h

/-! ## The laws on a successful run -/

namespace RefLaws
variable (L : RefLaws mref cref)

/-- A framed operation's successful run leaves the three values. -/
theorem same {α : Type} {p : MetaM α} (hp : Framed p) {w a w'}
    (h : RunsTo p mctx mref cctx cref w a w') :
    L.val w' = L.val w ∧ L.sval w' = L.sval w ∧ L.dval w' = L.dval w := by
  have := L.frame (mctx := mctx) (cctx := cctx) p hp w
  rwa [endW_of_runs h] at this

theorem get {w m w'} (h : RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w') :
    m = L.val w ∧ L.val w' = L.val w ∧ L.sval w' = L.sval w :=
  ⟨L.cacheGet _ _ _ h, (L.same .cacheGet h).1, (L.same .cacheGet h).2.1⟩

end RefLaws

/-! ## The invariant by the values -/

theorem invW_of_invV (L : RefLaws mref cref) {w} (h : InvV L w) : InvW mref cref w := by
  refine ⟨fun mctx cctx m w1 hg => ?_, fun mctx cctx s w1 hs => ?_⟩
  · rw [L.cacheGet _ _ _ hg]; exact h.1
  · rw [L.synthGet _ _ _ hs]; exact h.2

/-- (The contexts only serve to run a read; any will do.) -/
theorem invV_of_invW (mctx : Meta.Context) (cctx : Core.Context) (L : RefLaws mref cref) {w}
    (h : InvW mref cref w) : InvV L w := by
  obtain ⟨m, w1, hg⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    sparkleChildCache w
  obtain ⟨s, w2, hs⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    sparkleChildSynth w
  refine ⟨?_, ?_⟩
  · have := h.1 mctx cctx m w1 hg; rwa [L.cacheGet _ _ _ hg] at this
  · have := h.2 mctx cctx s w2 hs; rwa [L.synthGet _ _ _ hs] at this

theorem startW_of_invW {w} (h : InvW mref cref w) : StartW mref cref w :=
  ⟨h.2, Or.inr h.1⟩

/-- The start condition by the values. -/
def StartV (L : RefLaws mref cref) (w : Void IO.RealWorld) : Prop :=
  L.sval w = some synthesizeChild ∧ (L.dval w = 0 ∨ CacheInv mref cref (L.val w))

theorem startV_of_startW (mctx : Meta.Context) (cctx : Core.Context) (L : RefLaws mref cref) {w}
    (h : StartW mref cref w) : StartV L w := by
  obtain ⟨s, w2, hs⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    sparkleChildSynth w
  refine ⟨?_, ?_⟩
  · have := h.1 mctx cctx s w2 hs; rwa [L.synthGet _ _ _ hs] at this
  · rcases h.2 with hd | hc
    · obtain ⟨d, w1, hg⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx)
        (cref := cref) sparkleSynthDepth w
      left; rw [← L.depthGet _ _ _ hg]; exact hd mctx cctx d w1 hg
    · obtain ⟨m, w1, hg⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx)
        (cref := cref) sparkleChildCache w
      right; have := hc mctx cctx m w1 hg; rwa [L.cacheGet _ _ _ hg] at this

theorem cacheInv_empty : CacheInv mref cref {} := by
  intro c r h; simp at h

theorem cacheInv_insert {m : Std.HashMap Name Res} {c : Name} {r : Res}
    (h : CacheInv mref cref m) (hr : RealChild mref cref c r) :
    CacheInv mref cref (m.insert c r) := by
  intro c' r' h'
  rw [Std.HashMap.get?_insert] at h'
  split at h'
  · rename_i heq
    have : c = c' := by simpa using heq
    subst this
    cases h'
    exact hr
  · exact h c' r' h'

/-- A run of the real entry from an invariant world is a `RealChild`. -/
theorem RealChild.of_inv {c : Name} {r : Res} {w w' : Void IO.RealWorld}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') :
    RealChild mref cref c r :=
  RealChild.run mctx cctx w w' (fun mctx' cctx' m w1 h => hw.1 mctx' cctx' m w1 h) hw.2 hr

/-- A `RealChild`'s run — in some Meta and Core contexts — with the
invariant at its start. -/
theorem RealChild.inv {c : Name} {r : Res} (h : RealChild mref cref c r) :
    ∃ (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld),
      InvW mref cref w ∧ RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' := by
  cases h with
  | run mctx cctx w w' cache synth hr =>
    exact ⟨mctx, cctx, w, w', ⟨fun mctx' cctx' m w1 h => cache mctx' cctx' m w1 h, synth⟩, hr⟩

/-- A `RealChild`'s run: it starts in a world where the boundary holds. -/
theorem RealChild.bnd {c : Name} {r : Res} (hL : ChildLaws mref cref)
    (h : RealChild mref cref c r) :
    ∃ (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld),
      ChildBnd mref cref w ∧ RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' := by
  obtain ⟨mctx, cctx, w, w', hw, hr⟩ := h.inv
  exact ⟨mctx, cctx, w, w', ⟨hL, startW_of_invW hw⟩, hr⟩

theorem ChildBnd.laws {w : Void IO.RealWorld} (h : ChildBnd mref cref w) :
    ChildLaws mref cref := h.1

theorem RunsTo.pure_world {α : Type} {a b : α} {w w' : Void IO.RealWorld}
    (h : RunsTo (Pure.pure a : MetaM α) mctx mref cctx cref w b w') : b = a ∧ w' = w := by
  unfold RunsTo at h
  change EST.Out.ok a w = _ at h
  cases h; exact ⟨rfl, rfl⟩

end Tools.ShippingChildInv

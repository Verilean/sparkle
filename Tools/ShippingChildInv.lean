import Tools.ShippingMachineEntry

/-! # The child cache's invariant, world by world, along the real entry

A machine-route parent's children come from `synthesizeChild` (read from
`sparkleChildSynth`), which memoises the real entry in `sparkleChildCache`.
Both are `IO.Ref`s: their contents are opaque in the logic, so what a read
returns is a property of the WORLD the read runs in. This file states the
invariant per world and proves that the real run keeps it, instead of
assuming that every read in every world is sound.

* `RealChild c r` (inductive): `r` is returned by a run of the real entry
  `synthesizeCombinational c` that STARTS in a world satisfying the
  invariant (every cache entry read there is itself a `RealChild`, and the
  synthesis ref reads `synthesizeChild`). The induction is the order in
  which results enter the cache.
* `InvW w`: the invariant in world `w`, stated by what reads in `w` return
  (no model of the runtime).
* `RefLaws` — GENERIC runtime laws, a parameter (`Nonempty`): the two refs'
  values per world; `get`/`set`/`modify` of the cache and the read of the
  synthesis ref; reads can run; and the FRAME of the other operations the
  entry's prefix performs (`OtherRef`: the entry's other per-synthesis refs;
  the environment variable read; the profile logger; `getConstInfo`;
  `getEnv`). These say nothing about the compiler's invariant.
* `EntryHoare` / `HarnessHoare` — scoped pre/post conditions on runs of the
  real entry and of the machine route's harness (`synthesizeMixedCertified`):
  a run starting in a world satisfying `InvW` ends in one. They are the
  compiler-specific facts NOT proved here: both reach the fuel fallback's
  `partial` handlers (opaque), which can call `synthesizeChild` (whose step
  keeps the invariant, `synthesizeChild_inv`) and touch no other cache writer
  (the source has none besides the depth-0 clear), but the logic cannot see
  their bodies.

PROVED here: the depth-0 clear and every other operation of the entry's
prefix keep the invariant (`core_reads_inv`), the machine route's prefix
(`synthesizeFromConst_machine_inv`), the memoised entry (hit: the world's
cache; miss: the real entry, then the modify applied to the cache as it is
AFTER the child's run — `synthesizeChild_inv`), the closings' children
(`closeInstsGM_inv` / `closeInstsM_inv`), and the machine synthesis as a
whole (`synthesizeMachineCertified_inv`).

Scope of the `Name` key: a cached `RealChild c r` says `r` came from SOME
real run on `c` in these contexts, starting in an invariant world — not that
a fresh run in the current world (whose environment may differ) would return
it. Consumers use it only together with the child's reflection facts
(`MachineDefines` / `EntryDefines`), which hold for every world of the
contexts, so that difference does not matter to them.

Exceptions: `RunsTo` is a successful run. The proved steps contain no
`try`/`catch` that resumes after a failure (the entry's `try … finally`
re-raises; its success path is what is threaded). A failure caught inside
the opaque handlers is covered by `EntryHoare` / `HarnessHoare` being stated
for the whole run. -/
namespace Tools.ShippingChildInv
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab

abbrev Res := Sparkle.IR.AST.Module × Sparkle.IR.AST.Design

section Defs
variable (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
  (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)

/-- In world `w`, a read of the synthesis ref returns `synthesizeChild`. -/
def SynthAt (w : Void IO.RealWorld) : Prop :=
  ∀ s w1, RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w s w1 →
    s = some synthesizeChild

/-- `r` is returned by a run of the real entry on `c`, in these contexts,
starting in a world where the cache's entries are `RealChild` and the
synthesis ref reads `synthesizeChild`. -/
inductive RealChild : Name → Res → Prop
  | run {c : Name} {r : Res} (w w' : Void IO.RealWorld)
      (cache : ∀ m w1, RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w1 →
        ∀ c' r', m.get? c' = some r' → RealChild c' r')
      (synth : SynthAt mctx mref cctx cref w)
      (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') : RealChild c r

/-- Every entry of the map is a `RealChild`. -/
def CacheInv (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, m.get? c = some r → RealChild mctx mref cctx cref c r

/-- The invariant in world `w`, by what reads in `w` return. -/
def InvW (w : Void IO.RealWorld) : Prop :=
  (∀ m w1, RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w1 →
    CacheInv mctx mref cctx cref m) ∧ SynthAt mctx mref cctx cref w

/-- The children of a shape's calls, call by call: the built memory module
for a memory call, a `RealChild` of the call's declaration otherwise. -/
def ChildrenReal (shape : MachineShape) (children : List Res) : Prop :=
  children.length = shape.insts.length ∧
  ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
    (Sparkle.Compiler.MachMemory.memChild? (shape.insts[k]).1 = some y ∨
      RealChild mctx mref cctx cref (shape.insts[k]).1 y)

/-- The entry's per-synthesis refs other than the two this file tracks. -/
inductive OtherRef : {σ : Type} → IO.Ref σ → Prop
  | wireWidth : OtherRef sparkleWireWidthCache
  | depth : OtherRef sparkleSynthDepth
  | fvarValue : OtherRef sparkleFvarValueMap
  | letWire : OtherRef sparkleLetWireCache
  | loopWire : OtherRef sparkleLoopWireCache
  | wireCanon : OtherRef sparkleWireCanon
  | subModule : OtherRef sparkleSubModuleCache
  | subInstOut : OtherRef sparkleSubInstanceOutputs
  | singleOut : OtherRef sparkleSingleOutInstanceCache
  | typeCache : OtherRef sparkleTypeCache
  | typeHits : OtherRef sparkleTypeCacheHits
  | typeMiss : OtherRef sparkleTypeCacheMiss

/-- The entry's profile logger (`logProf`), as the entry writes it. -/
def profLogIO (profile : Bool) (msg : String) : IO Unit := do
  if profile then
    IO.eprintln msg
    (← IO.getStderr).flush
    let h ← IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append
    h.putStrLn msg
    h.flush

/-- **Generic runtime laws** (a parameter, never proved): the values of the
cache and of the synthesis ref in each world; the cache's `get` / `set` /
`modify` and the synthesis ref's read; that reads can run; and the frame of
the other operations of the entry's prefix (they leave both values). -/
structure RefLaws where
  val : Void IO.RealWorld → Std.HashMap Name Res
  sval : Void IO.RealWorld → Option (Name → MetaM Res)
  get : ∀ w m w', RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w' →
    m = val w ∧ val w' = val w ∧ sval w' = sval w
  set : ∀ v w u w', RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' →
    val w' = v ∧ sval w' = sval w
  modify : ∀ (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w' →
    val w' = f (val w) ∧ sval w' = sval w
  synthGet : ∀ w s w', RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w s w' →
    s = sval w ∧ val w' = val w ∧ sval w' = sval w
  getRuns : ∀ w, ∃ m w', RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w'
  synthGetRuns : ∀ w, ∃ s w', RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w s w'
  /-- the synthesis depth's value, read by the entry to decide the clear -/
  dval : Void IO.RealWorld → Nat
  depthGet : ∀ w d w', RunsTo (ST.Ref.get sparkleSynthDepth : MetaM Nat) mctx mref cctx cref w d w' →
    d = dval w
  depthGetRuns : ∀ w, ∃ d w',
    RunsTo (ST.Ref.get sparkleSynthDepth : MetaM Nat) mctx mref cctx cref w d w'
  otherGet : ∀ {σ : Type} (r : IO.Ref σ), OtherRef r → ∀ w a w',
    RunsTo (ST.Ref.get r : MetaM σ) mctx mref cctx cref w a w' → val w' = val w ∧ sval w' = sval w
  otherSet : ∀ {σ : Type} (r : IO.Ref σ), OtherRef r → ∀ v w u w',
    RunsTo (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref w u w' →
    val w' = val w ∧ sval w' = sval w
  otherModify : ∀ {σ : Type} (r : IO.Ref σ), OtherRef r → ∀ (f : σ → σ) w u w',
    RunsTo (ST.Ref.modify r f : MetaM Unit) mctx mref cctx cref w u w' →
    val w' = val w ∧ sval w' = sval w
  ioEnv : ∀ (n : String) w a w', RunsTo (liftM (IO.getEnv n) : MetaM _) mctx mref cctx cref w a w' →
    val w' = val w ∧ sval w' = sval w
  profLog : ∀ (b : Bool) (msg : String) w u w',
    RunsTo (liftM (profLogIO b msg) : MetaM Unit) mctx mref cctx cref w u w' →
    val w' = val w ∧ sval w' = sval w
  ioEnvD : ∀ (n : String) w a w',
    RunsTo (liftM (IO.getEnv n) : MetaM _) mctx mref cctx cref w a w' → dval w' = dval w
  profLogD : ∀ (b : Bool) (msg : String) w u w',
    RunsTo (liftM (profLogIO b msg) : MetaM Unit) mctx mref cctx cref w u w' → dval w' = dval w
  constInfo : ∀ (n : Name) w ci w', RunsTo (getConstInfo n : MetaM _) mctx mref cctx cref w ci w' →
    val w' = val w ∧ sval w' = sval w
  env : ∀ w e w', RunsTo (getEnv : MetaM Environment) mctx mref cctx cref w e w' →
    val w' = val w ∧ sval w' = sval w

/-- The real entry's runs keep the invariant (scoped pre/post; not proved). -/
def EntryHoare : Prop :=
  ∀ c w r w', InvW mctx mref cctx cref w →
    RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' → InvW mctx mref cctx cref w'

/-- The machine route's harness, run with the ENTRY'S OWN logger
(`profLogIO b` — the only logger the entry passes; an arbitrary callback
could write the refs), keeps the invariant (scoped pre/post; not proved). -/
def HarnessHoare : Prop :=
  ∀ (b : Bool) declName bs body w r w', InvW mctx mref cctx cref w →
    RunsTo (synthesizeMixedCertified (fun e hint top named => translateExprToWire e hint top named)
      (profLogIO b) declName bs body) mctx mref cctx cref w r w' → InvW mctx mref cctx cref w'

/-- The context-level part of the child boundary: the generic laws and the
two scoped pre/post conditions. The world-level part is `InvW` at the run's
start. -/
def ChildLaws : Prop :=
  Nonempty (RefLaws mctx mref cctx cref) ∧ EntryHoare mctx mref cctx cref ∧
    HarnessHoare mctx mref cctx cref

/-- **The start condition of an entry run** in world `w`: the synthesis ref
reads `synthesizeChild`, and EITHER the synthesis depth reads 0 (an outermost
run: the entry clears the cache, whatever it holds) OR the cache's entries
are `RealChild`s (a nested run inherits the invariant). -/
def StartW (w : Void IO.RealWorld) : Prop :=
  SynthAt mctx mref cctx cref w ∧
    ((∀ d w1, RunsTo (ST.Ref.get sparkleSynthDepth : MetaM Nat) mctx mref cctx cref w d w1 → d = 0) ∨
     (∀ m w1, RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w1 →
        CacheInv mctx mref cctx cref m))

/-- **The child boundary of a run starting in `w`**: the context-level laws
and the start condition in the start world. -/
def ChildBnd (w : Void IO.RealWorld) : Prop :=
  ChildLaws mctx mref cctx cref ∧ StartW mctx mref cctx cref w

end Defs

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The invariant by the two values (the laws' view). -/
def InvV (L : RefLaws mctx mref cctx cref) (w : Void IO.RealWorld) : Prop :=
  CacheInv mctx mref cctx cref (L.val w) ∧ L.sval w = some synthesizeChild

theorem invW_of_invV (L : RefLaws mctx mref cctx cref) {w} (h : InvV L w) :
    InvW mctx mref cctx cref w := by
  refine ⟨fun m w1 hg => ?_, fun s w1 hs => ?_⟩
  · rw [(L.get _ _ _ hg).1]; exact h.1
  · rw [(L.synthGet _ _ _ hs).1]; exact h.2

theorem invV_of_invW (L : RefLaws mctx mref cctx cref) {w} (h : InvW mctx mref cctx cref w) :
    InvV L w := by
  obtain ⟨m, w1, hg⟩ := L.getRuns w
  obtain ⟨s, w2, hs⟩ := L.synthGetRuns w
  refine ⟨?_, ?_⟩
  · have := h.1 m w1 hg; rwa [(L.get _ _ _ hg).1] at this
  · have := h.2 s w2 hs; rwa [(L.synthGet _ _ _ hs).1] at this

theorem startW_of_invW {w} (h : InvW mctx mref cctx cref w) : StartW mctx mref cctx cref w :=
  ⟨h.2, Or.inr h.1⟩

/-- The start condition by the values. -/
def StartV (L : RefLaws mctx mref cctx cref) (w : Void IO.RealWorld) : Prop :=
  L.sval w = some synthesizeChild ∧ (L.dval w = 0 ∨ CacheInv mctx mref cctx cref (L.val w))

theorem startV_of_startW (L : RefLaws mctx mref cctx cref) {w}
    (h : StartW mctx mref cctx cref w) : StartV L w := by
  obtain ⟨s, w2, hs⟩ := L.synthGetRuns w
  refine ⟨?_, ?_⟩
  · have := h.1 s w2 hs; rwa [(L.synthGet _ _ _ hs).1] at this
  · rcases h.2 with hd | hc
    · obtain ⟨d, w1, hg⟩ := L.depthGetRuns w
      left; rw [← L.depthGet _ _ _ hg]; exact hd d w1 hg
    · obtain ⟨m, w1, hg⟩ := L.getRuns w
      right; have := hc m w1 hg; rwa [(L.get _ _ _ hg).1] at this

/-- The invariant with a CONDITIONAL cache half: the synthesis ref's value,
and the cache's entries when `C` holds. `InvC L True` is `InvV L`; `InvC L
False` is the synthesis ref alone (what an outermost run starts from). -/
def InvC (L : RefLaws mctx mref cctx cref) (C : Prop) (w : Void IO.RealWorld) : Prop :=
  (C → CacheInv mctx mref cctx cref (L.val w)) ∧ L.sval w = some synthesizeChild

theorem invV_of_invC (L : RefLaws mctx mref cctx cref) {w} (h : InvC L True w) : InvV L w :=
  ⟨h.1 trivial, h.2⟩

theorem invC_keep (L : RefLaws mctx mref cctx cref) {C : Prop} {w w'}
    (hk : L.val w' = L.val w ∧ L.sval w' = L.sval w) (h : InvC L C w) : InvC L C w' := by
  unfold InvC; rw [hk.1, hk.2]; exact h

theorem invV_keep (L : RefLaws mctx mref cctx cref) {w w'}
    (hk : L.val w' = L.val w ∧ L.sval w' = L.sval w) (h : InvV L w) : InvV L w' := by
  unfold InvV; rw [hk.1, hk.2]; exact h

theorem cacheInv_empty : CacheInv mctx mref cctx cref {} := by
  intro c r h; simp at h

theorem cacheInv_insert {m : Std.HashMap Name Res} {c : Name} {r : Res}
    (h : CacheInv mctx mref cctx cref m) (hr : RealChild mctx mref cctx cref c r) :
    CacheInv mctx mref cctx cref (m.insert c r) := by
  intro c' r' h'
  rw [Std.HashMap.get?_insert] at h'
  split at h'
  · rename_i heq
    have : c = c' := by simpa using heq
    subst this
    cases h'
    exact hr
  · exact h c' r' h'

theorem RunsTo.pure_world {α : Type} {a b : α} {w w' : Void IO.RealWorld}
    (h : RunsTo (Pure.pure a : MetaM α) mctx mref cctx cref w b w') : b = a ∧ w' = w := by
  unfold RunsTo at h
  change EST.Out.ok a w = _ at h
  cases h; exact ⟨rfl, rfl⟩

/-! ## One step of the prefix -/

theorem inv_pure (L : RefLaws mctx mref cctx cref) {C : Prop} {α : Type} {a b : α} {w w'}
    (h : RunsTo (Pure.pure a : MetaM α) mctx mref cctx cref w b w') (hw : InvC L C w) :
    InvC L C w' := by
  rw [(RunsTo.pure_world h).2]; exact hw

theorem inv_otherGet' (L : RefLaws mctx mref cctx cref) {C : Prop} {σ : Type} {r : IO.Ref σ}
    {w a w'} (h : RunsTo (ST.Ref.get r : MetaM σ) mctx mref cctx cref w a w') (hw : InvC L C w)
    (hr : OtherRef r := by constructor) : InvC L C w' := invC_keep L (L.otherGet r hr _ _ _ h) hw

theorem inv_otherSet' (L : RefLaws mctx mref cctx cref) {C : Prop} {σ : Type} {r : IO.Ref σ}
    {v w u w'} (h : RunsTo (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref w u w')
    (hw : InvC L C w) (hr : OtherRef r := by constructor) : InvC L C w' :=
  invC_keep L (L.otherSet r hr _ _ _ _ h) hw

theorem inv_otherModify' (L : RefLaws mctx mref cctx cref) {C : Prop} {σ : Type} {r : IO.Ref σ}
    {f : σ → σ} {w u w'} (h : RunsTo (ST.Ref.modify r f : MetaM Unit) mctx mref cctx cref w u w')
    (hw : InvC L C w) (hr : OtherRef r := by constructor) : InvC L C w' :=
  invC_keep L (L.otherModify r hr _ _ _ _ h) hw

theorem inv_ioEnv (L : RefLaws mctx mref cctx cref) {C : Prop} {n : String} {w a w'}
    (h : RunsTo (liftM (IO.getEnv n) : MetaM _) mctx mref cctx cref w a w') (hw : InvC L C w) :
    InvC L C w' := invC_keep L (L.ioEnv _ _ _ _ h) hw

theorem inv_profLog (L : RefLaws mctx mref cctx cref) {C : Prop} {b : Bool} {msg : String}
    {w u w'} (h : RunsTo (liftM (profLogIO b msg) : MetaM Unit) mctx mref cctx cref w u w')
    (hw : InvC L C w) : InvC L C w' := invC_keep L (L.profLog _ _ _ _ _ h) hw

/-- **The depth-0 clear ESTABLISHES the cache half**, from any cache: only
the synthesis ref's value is carried over. -/
theorem inv_clear (L : RefLaws mctx mref cctx cref) {C : Prop} {w u w'}
    (h : RunsTo (sparkleChildCache.set {} : MetaM Unit) mctx mref cctx cref w u w')
    (hw : InvC L C w) : InvC L True w' := by
  obtain ⟨hv, hs⟩ := L.set _ _ _ _ h
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hv]; exact cacheInv_empty
  · rw [hs]; exact hw.2

/-- The lemma carrying the invariant over one step, by the step's head. -/
meta def stepLemma (prog : Lean.Expr) : Lean.MetaM (Lean.TSyntax `term) := do
  let prog ← Lean.instantiateMVars prog
  if prog.isAppOf ``Pure.pure then return ← `(inv_pure)
  if prog.isAppOf ``ST.Ref.set then
    if (prog.getAppArgs.find? (·.isConstOf ``sparkleChildCache)).isSome then return ← `(inv_clear)
    return ← `(inv_otherSet')
  if prog.isAppOf ``ST.Ref.get then return ← `(inv_otherGet')
  if prog.isAppOf ``ST.Ref.modify then return ← `(inv_otherModify')
  if prog.isAppOf ``liftM then
    if (prog.find? (·.isConstOf ``IO.getEnv)).isSome then return ← `(inv_ioEnv)
    return ← `(inv_profLog)
  throwError "no frame for the step {prog}"

/-- One bind of the prefix, the invariant carried to the next world. -/
elab "peel_inv " L:term:max h:ident hw:ident : tactic => do
  match ← runHeadIs h.getId ``Bind.bind with
  | some true =>
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      obtain ⟨_, _, $(Lean.mkIdent `step):ident, $h:ident⟩ := RunsTo.bind $h:ident))
    let lem ← Lean.Elab.Tactic.withMainContext do
      let d ← Lean.Meta.getLocalDeclFromUserName `step
      stepLemma (← Lean.instantiateMVars d.type).getAppArgs[1]!
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      (have $hw:ident := $lem $L $(Lean.mkIdent `step):ident $hw
       clear $(Lean.mkIdent `step):ident)))
  | _ => throwError "head is not a bind"

/-- **The entry's prefix ESTABLISHES the invariant** from the start condition.
The run reads the profile variable, logs, and reads the synthesis depth `d`
(none of which touches the three values). If `d = 0` it clears the cache —
which establishes the cache half from ANY cache (`inv_clear`), so only the
synthesis ref's value is needed at the start; otherwise the run is nested and
the start condition's cache half is carried through the other refs' resets.
Then the depth bump, the `try`, `getConstInfo` and `getEnv`. The logger the
entry hands on is its own, `profLogIO b`. -/
theorem core_reads_inv (L : RefLaws mctx mref cctx cref) {declName : Name}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hw : StartV L w)
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
        mctx mref cctx cref w3 (M, D) w4 ∧ InvV L w3 := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
  obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
  obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
  have hd : d = L.dval w := by
    rw [L.depthGet _ _ _ s3, L.profLogD _ _ _ _ _ s2, L.ioEnvD _ _ _ _ s1]
  have keep : L.val wc = L.val w ∧ L.sval wc = L.sval w := by
    obtain ⟨a1, b1⟩ := L.ioEnv _ _ _ _ s1
    obtain ⟨a2, b2⟩ := L.profLog _ _ _ _ _ s2
    obtain ⟨a3, b3⟩ := L.otherGet _ OtherRef.depth _ _ _ s3
    exact ⟨a3.trans (a2.trans a1), b3.trans (b2.trans b1)⟩
  by_cases h0 : (d == 0) = true
  · -- outermost: the clear establishes the cache half
    have hw : InvC L False wc := invC_keep L keep ⟨fun f => f.elim, hw.1⟩
    simp only [h0, ↓reduceIte] at h
    iterate 40 (first | peel_inv L h hw | skip)
    obtain ⟨_, h⟩ := RunsTo.try_finally h
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    have hw := invC_keep L (L.constInfo _ _ _ _ hget) hw
    obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
    have hw := invC_keep L (L.env _ _ _ henv) hw
    exact ⟨prof.isSome, env, ci, _, w2, _, _, _, _, hget, henv, h, invV_of_invC L hw⟩
  · -- nested: the start condition's cache half is inherited
    have hc : CacheInv mctx mref cctx cref (L.val w) := by
      rcases hw.2 with hz | hc
      · exact absurd (by rw [hd, hz]; rfl) h0
      · exact hc
    have hw : InvC L True wc := invC_keep L keep ⟨fun _ => hc, hw.1⟩
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
    iterate 40 (first | peel_inv L h hw | skip)
    obtain ⟨_, h⟩ := RunsTo.try_finally h
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    have hw := invC_keep L (L.constInfo _ _ _ _ hget) hw
    obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
    have hw := invC_keep L (L.env _ _ _ henv) hw
    exact ⟨prof.isSome, env, ci, _, w2, _, _, _, _, hget, henv, h, invV_of_invC L hw⟩

/-! ## The memoised entry and the closings -/

/-- **The memoised entry, world by world.** A hit returns a cached entry (a
`RealChild` by the invariant) and leaves the world's values; a miss runs the
real entry from a world satisfying the invariant (so its result is a
`RealChild`; the run keeps the invariant, `EntryHoare`) and then modifies the
cache AS IT IS after that run, inserting the result. -/
theorem synthesizeChild_inv (L : RefLaws mctx mref cctx cref)
    (hE : EntryHoare mctx mref cctx cref)
    {c : Name} {w w' : Void IO.RealWorld} {y : Res}
    (hw : InvV L w) (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') :
    RealChild mctx mref cctx cref c y ∧ InvV L w' := by
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  obtain ⟨hm, hv, hs⟩ := L.get _ _ _ hget
  have hw1 : InvV L w1 := invV_keep L ⟨hv, hs⟩ hw
  cases hc : m.get? c with
  | some r =>
    simp only [hc] at h
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    refine ⟨?_, hw1⟩
    rw [hm] at hc
    exact hw.1 c _ hc
  | none =>
    simp only [hc] at h
    obtain ⟨r, w2, hrun, h⟩ := RunsTo.bind h
    have hW1 := invW_of_invV L hw1
    have hw2 := invV_of_invW L (hE c w1 r w2 hW1 hrun)
    obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
    obtain ⟨hv3, hs3⟩ := L.modify _ _ _ _ hmod
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    have hr : RealChild mctx mref cctx cref c y :=
      RealChild.run w1 w2 (fun m w h => hW1.1 m w h) hW1.2 hrun
    refine ⟨hr, ?_, ?_⟩
    · rw [hv3]; exact cacheInv_insert hw2.1 hr
    · rw [hs3]; exact hw2.2

/-- A `List.mapM` run whose steps keep `P` and establish `Q` of each result. -/
theorem mapM_loop_hoare {α β : Type} (f : α → MetaM β) (P : Void IO.RealWorld → Prop)
    (Q : α → β → Prop)
    (hf : ∀ x w y w', P w → RunsTo (f x) mctx mref cctx cref w y w' → Q x y ∧ P w') :
    ∀ (l : List α) (acc r : List β) w w', P w →
      RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
      ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
        (∀ k (hk : k < l.length), ∃ y, ys[k]? = some y ∧ Q l[k] y) ∧ P w'
  | [], acc, r, w, w', hp, h => by
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    exact ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero k), hp⟩
  | x :: xs, acc, r, w, w', hp, h => by
    obtain ⟨y, w1, hy, h⟩ := RunsTo.bind h
    obtain ⟨hq, hp1⟩ := hf x w y w1 hp hy
    obtain ⟨ys, hr, hlen, hget, hp'⟩ := mapM_loop_hoare f P Q hf xs (y :: acc) r w1 w' hp1 h
    refine ⟨y :: ys, by simp [hr], by simp [hlen], fun k hk => ?_, hp'⟩
    cases k with
    | zero => exact ⟨y, rfl, hq⟩
    | succ k =>
      obtain ⟨z, hz, hqz⟩ := hget k (by simpa using hk)
      exact ⟨z, by simpa using hz, by simpa using hqz⟩

theorem mapM_hoare {α β : Type} (f : α → MetaM β) (P : Void IO.RealWorld → Prop)
    (Q : α → β → Prop)
    (hf : ∀ x w y w', P w → RunsTo (f x) mctx mref cctx cref w y w' → Q x y ∧ P w')
    (l : List α) (r : List β) {w w'} (hp : P w)
    (h : RunsTo (l.mapM f) mctx mref cctx cref w r w') :
    r.length = l.length ∧ (∀ k (hk : k < l.length), ∃ y, r[k]? = some y ∧ Q l[k] y) ∧ P w' := by
  obtain ⟨ys, hr, hlen, hget, hp'⟩ := mapM_loop_hoare f P Q hf l [] r w w' hp h
  simp only [List.reverse_nil, List.nil_append] at hr
  subst hr
  exact ⟨hlen, hget, hp'⟩

/-- The synthesis ref's read, in an invariant world: `synthesizeChild`. -/
theorem synthRead (L : RefLaws mctx mref cctx cref) {w s w'} (hw : InvV L w)
    (h : RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w s w') :
    s = some synthesizeChild ∧ InvV L w' := by
  obtain ⟨hs, hv, hss⟩ := L.synthGet _ _ _ h
  exact ⟨hs.trans hw.2, invV_keep L ⟨hv, hss⟩ hw⟩

/-- **The general closing's children, world by world.** -/
theorem closeInstsGM_inv (L : RefLaws mctx mref cctx cref) (hE : EntryHoare mctx mref cctx cref)
    {shape t m₀ d₀ m d} {w w'} (hw : InvV L w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) = some (m, d) ∧ MemChildren shape children ∧
      ChildrenReal mctx mref cctx cref shape children ∧ InvV L w' := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := mapM_hoare _ (InvV L)
    (fun (x : Name × List Nat × MixedGateBinder) y =>
      (∀ md, Sparkle.Compiler.MachMemory.memChild? x.1 = some md → y = md) ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1 = some y ∨ RealChild mctx mref cctx cref x.1 y))
    (fun x w y w' hp hy => by
      obtain ⟨c, b, k'⟩ := x
      dsimp only at hy ⊢
      cases hmc : Sparkle.Compiler.MachMemory.memChild? c with
      | some md =>
        rw [hmc] at hy
        obtain ⟨rfl, rfl⟩ := RunsTo.pure_world hy
        exact ⟨⟨fun md' h => by cases h; rfl, Or.inl rfl⟩, hp⟩
      | none =>
        rw [hmc] at hy
        obtain ⟨hrc, hp'⟩ := synthesizeChild_inv L hE hp hy
        exact ⟨⟨fun md' h => (by cases h), Or.inr hrc⟩, hp'⟩)
    shape.insts children hw1 hch
  refine ⟨children, heq.symm, ?_, ⟨hlen, fun k hkl => ?_⟩, hw2⟩
  · intro k c hc md hmd
    have hkl : k < shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
    obtain ⟨y, hky, hm, _⟩ := hk k hkl
    have hck : (shape.insts[k]).1 = c := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hkl] at hc
      simpa using hc
    rw [← hck] at hmd
    rw [hm md hmd] at hky
    exact hky
  · obtain ⟨y, hky, _, hor⟩ := hk k hkl
    exact ⟨y, hky, hor⟩

/-- **The one-output closing's children, world by world.** -/
theorem closeInstsM_inv (L : RefLaws mctx mref cctx cref) (hE : EntryHoare mctx mref cctx cref)
    {shape t m₀ d₀ m d} {w w'} (hw : InvV L w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) = some (m, d) ∧
      ChildrenReal mctx mref cctx cref shape children ∧ InvV L w' := by
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := mapM_hoare _ (InvV L)
    (fun (x : Name × List Nat × MixedGateBinder) y =>
      Sparkle.Compiler.MachMemory.memChild? x.1 = some y ∨ RealChild mctx mref cctx cref x.1 y)
    (fun x w y w' hp hy => by
      obtain ⟨hrc, hp'⟩ := synthesizeChild_inv L hE hp hy
      exact ⟨Or.inr hrc, hp'⟩)
    shape.insts children hw1 hch
  exact ⟨children, heq.symm, ⟨hlen, hk⟩, hw2⟩

/-! ## The machine route -/

/-- `synthesizeFromConst_machine`, the invariant carried to the start of the
machine synthesis. -/
theorem synthesizeFromConst_machine_inv (L : RefLaws mctx mref cctx cref)
    {logProf : String → IO Unit} {declName : Name}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none)
    (miss : mixedCertifiedShape? false [] ci isInst = none) (hw : InvV L w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire e h t n) logProf
      declName [] false true ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR : Environment) (w5 w6 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      ∀ shape, machineShape? false [] ci (structEnv envR) = some shape →
        ∃ r w7 w8, RunsTo (synthesizeMachineCertified
            (fun e hint top named => translateExprToWire e hint top named) logProf declName
            shape) mctx mref cctx cref w7 r w8 ∧ InvV L w7 ∧
          ∀ res, r = some res → res = (m, d) := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, miss, Bool.not_false, Bool.and_self, List.isEmpty_nil] at hr
  obtain ⟨envR, w1, henv, hr⟩ := RunsTo.bind hr
  have hw1 := invV_keep L (L.env _ _ _ henv) hw
  obtain ⟨mach, w2, hp, hr⟩ := RunsTo.bind hr
  obtain ⟨hm, rfl⟩ := RunsTo.pure_world hp
  subst hm
  refine ⟨envR, _, _, henv, ?_⟩
  intro shape hs
  rw [hs] at hr
  dsimp only at hr
  obtain ⟨r, w3, hmach, hr⟩ := RunsTo.bind hr
  refine ⟨r, _, _, hmach, hw1, ?_⟩
  intro res hres
  subst hres
  dsimp only at hr
  have hr := hr.mreturns
  peel_bind hr
  peel_bind hr
  exact (MReturns.pure hr).symm

/-- **The machine synthesis, with its children, from an invariant world.**
The harness keeps the invariant (`HarnessHoare`); the closings' children are
then `RealChild`s (`closeInstsM_inv` / `closeInstsGM_inv`). -/
theorem synthesizeMachineCertified_inv (L : RefLaws mctx mref cctx cref)
    (hE : EntryHoare mctx mref cctx cref) (hH : HarnessHoare mctx mref cctx cref)
    {b : Bool} {declName shape m d} {w w'} (hw : InvV L w)
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w (some (m, d)) w') :
    ∃ t t' d₀, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) declName
        shape.binders shape.body) (t, d₀) ∧
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      ((shape.insts = [] ∧ m = Sparkle.IR.Machine.closeMachine shape.layout t' ∧ d = d₀) ∨
       (shape.insts ≠ [] ∧ ∃ children,
          CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children m d ∧
          ChildrenReal mctx mref cctx cref shape children)) := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := invV_of_invW L (hH b declName _ _ w _ w1 (invW_of_invV L hw) run)
  dsimp only at hr
  split at hr
  · rename_i t' hcl
    split at hr
    · rename_i hi
      have eq := RunsTo.pure_eq hr
      simp only [Option.some.injEq, Prod.mk.injEq] at eq
      obtain ⟨hm, hd⟩ := eq
      exact ⟨t, t', d', run.mreturns, hcl, Or.inl ⟨hi, hm, hd⟩⟩
    · rename_i hi
      have hne : shape.insts ≠ [] := by rw [hi]; exact List.cons_ne_nil _ _
      split at hr
      · rename_i hf
        obtain ⟨children, hc, hreal, _⟩ := closeInstsM_inv L hE hw1 hr
        exact ⟨t, t', d', run.mreturns, hcl, Or.inr ⟨hne, children,
          Or.inl ⟨List.isEmpty_iff.mp hf, hc⟩, hreal⟩⟩
      · rename_i hf
        obtain ⟨children, hc, hmc, hreal, _⟩ := closeInstsGM_inv L hE hw1 hr
        exact ⟨t, t', d', run.mreturns, hcl, Or.inr ⟨hne, children,
          Or.inr ⟨fun h => hf (List.isEmpty_iff.mpr h), hc, hmc⟩, hreal⟩⟩
  · have eq := RunsTo.pure_eq hr
    cases eq

/-- **The children of a real compile, from the run's start world.** One
successful run of the real core entry at the machine boundary, STARTING in a
world satisfying the invariant, returns the closing of its transition with
children that are, call by call, built memory modules or `RealChild`s of the
call's declaration — under the generic laws and the two scoped pre/post
conditions (`ChildLaws`). -/
theorem machine_children_real {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineCloses mctx mref cctx cref declName shape)
    (hb : ChildBnd mctx mref cctx cref w) (hi : shape.insts ≠ []) :
    ∃ t t' d₀ children,
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children m d ∧
      ChildrenReal mctx mref cctx cref shape children := by
  obtain ⟨⟨⟨L⟩, hE, hH⟩, hw⟩ := hb
  obtain ⟨b, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run, hw3⟩ :=
    core_reads_inv L (startV_of_startW L hw) hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv
  obtain ⟨envR', w7, w8, henv', hmach⟩ := synthesizeFromConst_machine_inv L old miss hw3 run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv'
  obtain ⟨r, w9, w10, hrun, hw9, hres⟩ := hmach shape hshape
  have hne := closes (profLogIO b) _ _ _ hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    obtain ⟨t, t', d₀, _, hcl, hmt⟩ := synthesizeMachineCertified_inv L hE hH hw9 hrun
    rcases hmt with ⟨h0, _, _⟩ | ⟨_, children, hcc, hreal⟩
    · exact absurd h0 hi
    · exact ⟨t, t', d₀, children, hcl, hcc, hreal⟩

theorem ChildBnd.laws {w : Void IO.RealWorld} (h : ChildBnd mctx mref cctx cref w) :
    ChildLaws mctx mref cctx cref := h.1

/-- A run of the real entry from an invariant world is a `RealChild`. -/
theorem RealChild.of_inv {c : Name} {r : Res} {w w' : Void IO.RealWorld}
    (hw : InvW mctx mref cctx cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') :
    RealChild mctx mref cctx cref c r :=
  RealChild.run w w' (fun m w1 h => hw.1 m w1 h) hw.2 hr

/-- A `RealChild`'s run: it starts in a world where the boundary holds. -/
theorem RealChild.bnd {c : Name} {r : Res} (hL : ChildLaws mctx mref cctx cref)
    (h : RealChild mctx mref cctx cref c r) :
    ∃ w w', ChildBnd mctx mref cctx cref w ∧
      RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' := by
  cases h with
  | run w w' cache synth hr => exact ⟨w, w', ⟨hL, synth, Or.inr fun m w1 h => cache m w1 h⟩, hr⟩

/-- A `RealChild`'s run, the invariant at its start. -/
theorem RealChild.inv {c : Name} {r : Res} (h : RealChild mctx mref cctx cref c r) :
    ∃ w w', InvW mctx mref cctx cref w ∧
      RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' := by
  cases h with
  | run w w' cache synth hr => exact ⟨w, w', ⟨fun m w1 h => cache m w1 h, synth⟩, hr⟩

/-- **The machine synthesis inside a real core run**, from a start world
where the boundary holds: the run of `synthesizeMachineCertified` the entry
performed starts in a world satisfying the invariant. -/
theorem machine_run_of_core {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (hb : ChildBnd mctx mref cctx cref w) :
    ∃ (b : Bool) (r : Option Res) (w9 w10 : Void IO.RealWorld),
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) declName shape)
        mctx mref cctx cref w9 r w10 ∧ InvW mctx mref cctx cref w9 ∧
      ∀ res, r = some res → res = (m, d) := by
  obtain ⟨⟨L⟩, _, _⟩ := hb.1
  obtain ⟨b, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run, hw3⟩ :=
    core_reads_inv L (startV_of_startW L hb.2) hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv
  obtain ⟨envR', w7, w8, henv', hmach⟩ := synthesizeFromConst_machine_inv L old miss hw3 run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv'
  obtain ⟨r, w9, w10, hrun, hw9, hres⟩ := hmach shape hshape
  exact ⟨b, r, w9, w10, hrun, invW_of_invV L hw9, hres⟩

/-- `synthesizeMachineCertified_inv` from the read-based invariant. -/
theorem synthesizeMachineCertified_runs {b : Bool} {declName shape m d} {w w'}
    (hL : ChildLaws mctx mref cctx cref) (hw : InvW mctx mref cctx cref w)
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w (some (m, d)) w') :
    ∃ t t' d₀, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) declName
        shape.binders shape.body) (t, d₀) ∧
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      ((shape.insts = [] ∧ m = Sparkle.IR.Machine.closeMachine shape.layout t' ∧ d = d₀) ∨
       (shape.insts ≠ [] ∧ ∃ children,
          CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children m d ∧
          ChildrenReal mctx mref cctx cref shape children)) := by
  obtain ⟨⟨L⟩, hE, hH⟩ := hL
  exact synthesizeMachineCertified_inv L hE hH (invV_of_invW L hw) hr

end Tools.ShippingChildInv

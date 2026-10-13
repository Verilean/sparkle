import Tools.ShippingCallsKidsS

/-! # Coherence of the child cache: the modules it holds are a function of their names

`Tools.ShippingCallsKidsS.closes_of_agree` closes a parent whose callees
share a descendant RELATIVE to `CacheAgrees decls w'`: in the cache the run
ends in, the entries of two different callees agree on every module name
they both hold. This file states that as an invariant of the cache CONTENT
(no declaration list handed in from outside) and proves the pure part of
"initial → preserved → consumed". What is NOT proved is said at each step;
`docs/parallel/A-cache-coherence.md` has the reading and the counterexamples.

* `Coherent m`: any two modules of one name held by entries of `m` (an
  entry's module or a module of its design; the two entries may be one) are
  equal.
* `agree_of_coherent`: `Agree decls m` for EVERY `decls`.
* (a) `coherent_empty`; `coherent_after_clear` (the depth-0 clear);
  `ChildBndC` — the start condition with the clause, `ChildBndC.bnd`
  (it is STRONGER than `ChildBnd`), `childBndC_of_zero` (equal at depth 0).
* (b) `coherent_insert`: an insert keeps `Coherent` IF the inserted value
  `Fits` the map (its modules agree by name among themselves and with every
  module the map holds). `fits_of_prov`: `Fits` from "each module of the new
  entry is held by an entry, or has a name no entry holds". `fitsB` /
  `fits_of_fitsB`: the decidable form. `synthesizeChild_coherent`: the REAL
  memoised entry keeps `Coherent` on a returning run IF the real entry's
  result fits the cache its run ends in — that premise is NOT derived, and
  it is FALSE of the compiler as it is for declarations whose modules get
  one name (the probe `Tests/Compiler/CacheCoherenceProbe.lean`).
  `synthesizeChildC` / `synthesizeChildC_coherent`: a CANDIDATE entry (not
  the compiler's; nothing uses it) that checks `fitsB` before the insert and
  throws otherwise — for it the premise is discharged by the check.
* (c) `MachineClosesAtC`: the closing from worlds that satisfy `InvW` AND
  are coherent; `machineClosesAtC_of_S`: it follows from the built relative
  closing `MachineClosesAtS` and `MachineKeepsCoherent` (the machine
  synthesis ends coherent when it starts coherent) — the latter is step (b)
  at the level the closing needs and is NOT derived here.

No endpoint changes: `MachineClosesAtC` is not `MachineClosesAt`, and
nothing consumes it.

WRITTEN, NOT BUILT (par/a-31). -/
namespace Tools.ShippingCacheCoherent
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv Tools.ShippingCallsKidsS

/-- The modules an entry holds: its module, and its design's modules. -/
abbrev mods (y : Res) : List Sparkle.IR.AST.Module := y.1 :: y.2.modules

/-- **The cache's modules are a function of their names**: two modules of one
name held by entries of `m` are equal. -/
def Coherent (m : Std.HashMap Name Res) : Prop :=
  ∀ (c : Name) (y : Res) (c' : Name) (y' : Res), m.get? c = some y → m.get? c' = some y' →
    ∀ a ∈ mods y, ∀ b ∈ mods y', a.name = b.name → a = b

/-- `y` can be added to `m`: its modules agree by name among themselves, and
with every module `m` holds. -/
def Fits (m : Std.HashMap Name Res) (y : Res) : Prop :=
  (∀ a ∈ mods y, ∀ b ∈ mods y, a.name = b.name → a = b) ∧
  (∀ (c' : Name) (y' : Res), m.get? c' = some y' →
    ∀ a ∈ mods y, ∀ b ∈ mods y', a.name = b.name → a = b)

/-! ## The derivation of `Agree` -/

/-- `Agree` over ANY declaration list. -/
theorem agree_of_coherent (decls : List Name) {m : Std.HashMap Name Res} (h : Coherent m) :
    Agree decls m :=
  fun c _ c' _ _ y y' hy hy' a ha b hb hn => h c y c' y' hy hy' a ha b hb hn

/-! ## (a) Initial -/

theorem coherent_empty : Coherent ({} : Std.HashMap Name Res) := by
  intro c y c' y' h
  simp at h

/-! ## (b) Insert, purely -/

/-- **An insert keeps coherence when the inserted value fits.** The key may
be new or not: what is asked is asked of the value against the WHOLE map. -/
theorem coherent_insert {m : Std.HashMap Name Res} {c : Name} {y : Res}
    (h : Coherent m) (hf : Fits m y) : Coherent (m.insert c y) := by
  intro c1 y1 c2 y2 h1 h2 a ha b hb hn
  rw [Std.HashMap.get?_insert] at h1 h2
  split at h1
  · cases h1
    split at h2
    · cases h2
      exact hf.1 a ha b hb hn
    · exact hf.2 c2 y2 h2 a ha b hb hn
  · split at h2
    · cases h2
      exact (hf.2 c1 y1 h1 b hb a ha hn.symm).symm
    · exact h c1 y1 c2 y2 h1 h2 a ha b hb hn

/-- `Fits` from where the new entry's modules come from: its module names
are pairwise different, and each module is held by an entry of `m` or has a
name no entry of `m` holds. -/
theorem fits_of_prov {m : Std.HashMap Name Res} {y : Res} (h : Coherent m)
    (hnd : ((mods y).map (·.name)).Nodup)
    (hprov : ∀ a ∈ mods y, (∃ (c' : Name) (y' : Res), m.get? c' = some y' ∧ a ∈ mods y') ∨
      (∀ (c' : Name) (y' : Res), m.get? c' = some y' → ∀ b ∈ mods y', b.name ≠ a.name)) :
    Fits m y := by
  refine ⟨?_, ?_⟩
  · exact Tools.ShippingCallsKidsD.module_of_name _ hnd
  · intro c' y' hg a ha b hb hn
    rcases hprov a ha with ⟨c2, y2, hg2, ha2⟩ | hfresh
    · exact h c2 y2 c' y' hg2 hg a ha2 b hb hn
    · exact absurd hn.symm (hfresh c' y' hg b hb)

/-- Every module of `y` agrees by name with every module of `y'`. -/
def crossB (y y' : Res) : Bool :=
  (mods y).all fun a => (mods y').all fun b => a.name != b.name || decide (a = b)

/-- `Fits`, decided. -/
def fitsB (m : Std.HashMap Name Res) (y : Res) : Bool :=
  crossB y y && m.toList.all fun e => crossB y e.2

theorem crossB_sound {y y' : Res} (h : crossB y y' = true) :
    ∀ a ∈ mods y, ∀ b ∈ mods y', a.name = b.name → a = b := by
  intro a ha b hb hn
  unfold crossB at h
  have h1 : ((mods y').all fun b => a.name != b.name || decide (a = b)) = true :=
    List.all_eq_true.mp h a ha
  have h2 : (a.name != b.name || decide (a = b)) = true := List.all_eq_true.mp h1 b hb
  simpa [hn] using h2

theorem fits_of_fitsB {m : Std.HashMap Name Res} {y : Res} (h : fitsB m y = true) : Fits m y := by
  unfold fitsB at h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨crossB_sound h1, ?_⟩
  intro c' y' hg
  have hg' : m[c']? = some y' := hg
  have hm : (c', y') ∈ m.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hg'
  have h3 : crossB y y' = true := List.all_eq_true.mp h2 (c', y') hm
  exact crossB_sound h3

theorem coherent_insert_of_fitsB {m : Std.HashMap Name Res} {c : Name} {y : Res}
    (h : Coherent m) (hf : fitsB m y = true) : Coherent (m.insert c y) :=
  coherent_insert h (fits_of_fitsB hf)

/-! ## The worlds -/

/-- What a read of the child cache returns in `w` is coherent. -/
def CoherentAt (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) m w1,
    RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w1 → Coherent m

/-- The start condition by the values, with the clause: at depth 0 nothing is
asked of the cache (the entry clears it); a nested start inherits the
invariant AND coherence. -/
def StartVC {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : RefLaws mref cref) (w : Void IO.RealWorld) : Prop :=
  L.sval w = some synthesizeChild ∧
    (L.dval w = 0 ∨ (CacheInv mref cref (L.val w) ∧ Coherent (L.val w)))

/-- The child boundary with the clause. -/
def ChildBndC (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) : Prop :=
  ∃ L : RefLaws mref cref, StartVC L w ∧ L.quiet w

/-- The machine synthesis does not fall back, from invariant worlds of
positive depth that are COHERENT. Weaker than `MachineClosesAt` (one more
antecedent, on the START world). -/
def MachineClosesAtC (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) : Prop :=
  ∀ (b : Bool) w r w', InvW mref cref w → CoherentAt mref cref w → DepthPos mref cref w →
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w r w' → r ≠ none

/-- **Step (b) at the level the closing needs — a STATEMENT, not a theorem
of this file**: a returning run of the machine synthesis from a coherent
invariant world of positive depth ends in a coherent world. -/
def MachineKeepsCoherent (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) : Prop :=
  ∀ (b : Bool) w r w', InvW mref cref w → CoherentAt mref cref w → DepthPos mref cref w →
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w r w' → CoherentAt mref cref w'

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

theorem coherentAt_of_val (L : RefLaws mref cref) {w : Void IO.RealWorld}
    (h : Coherent (L.val w)) : CoherentAt mref cref w := by
  intro mctx' cctx' m w1 hg
  rw [L.cacheGet _ _ _ hg]
  exact h

/-- (The contexts only serve to run a read; any will do.) -/
theorem val_of_coherentAt (mctx : Meta.Context) (cctx : Core.Context) (L : RefLaws mref cref)
    {w : Void IO.RealWorld} (h : CoherentAt mref cref w) : Coherent (L.val w) := by
  obtain ⟨m, w1, hg⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    sparkleChildCache w
  have := h mctx cctx m w1 hg
  rwa [L.cacheGet _ _ _ hg] at this

/-- A coherent world satisfies `CacheAgrees` over ANY declaration list. -/
theorem cacheAgrees_of_coherentAt (decls : List Name) {w : Void IO.RealWorld}
    (h : CoherentAt mref cref w) : CacheAgrees mref cref decls w :=
  fun mctx' cctx' m w1 hg => agree_of_coherent decls (h mctx' cctx' m w1 hg)

/-! ## (a) The start world -/

/-- The cache's clear (the depth-0 entry's) ends in a coherent world. -/
theorem coherent_after_clear (L : RefLaws mref cref) {w : Void IO.RealWorld} {u : Unit}
    {w' : Void IO.RealWorld}
    (h : RunsTo (sparkleChildCache.set {} : MetaM Unit) mctx mref cctx cref w u w') :
    Coherent (L.val w') := by
  rw [(L.cacheSet _ _ _ _ h).1]
  exact coherent_empty

/-- The boundary with the clause is the STRONGER premise. -/
theorem ChildBndC.bnd {w : Void IO.RealWorld} (h : ChildBndC mref cref w) :
    ChildBnd mref cref w := by
  obtain ⟨L, ⟨hs, hd⟩, hq⟩ := h
  exact ⟨L, ⟨hs, hd.imp id (fun x => x.1)⟩, hq⟩

/-- At depth 0 — an OUTERMOST run — the two boundaries ask the same. -/
theorem childBndC_of_zero (L : RefLaws mref cref) {w : Void IO.RealWorld}
    (hs : L.sval w = some synthesizeChild) (hd : L.dval w = 0) (hq : L.quiet w) :
    ChildBndC mref cref w :=
  ⟨L, ⟨hs, Or.inl hd⟩, hq⟩

/-- An invariant world that is coherent is a start world of the boundary
with the clause. -/
theorem ChildBndC.of_inv (L : RefLaws mref cref) {w : Void IO.RealWorld} (h : InvV L w)
    (hc : Coherent (L.val w)) : ChildBndC mref cref w :=
  ⟨L, ⟨h.2.1, Or.inr ⟨h.1, hc⟩⟩, h.2.2⟩

/-! ## (b) The memoised entry, on a returning run -/

/-- **The real memoised entry keeps coherence on a returning run, IF the real
entry's result fits the cache its run ends in.** A hit leaves the cache. A
miss runs the real entry and inserts its result into the cache as it is
after that run (`coherent_insert`).

The premise `hE` is NOT derived anywhere: it is the statement about
`synthesizeCombinational` that step (b) lacks. -/
theorem synthesizeChild_coherent (L : RefLaws mref cref) {c : Name}
    {w w' : Void IO.RealWorld} {y : Res} (hc : Coherent (L.val w))
    (hE : ∀ (w1 : Void IO.RealWorld) (r : Res) (w2 : Void IO.RealWorld), L.val w1 = L.val w →
      RunsTo (synthesizeCombinational c) mctx mref cctx cref w1 r w2 →
      Coherent (L.val w2) ∧ Fits (L.val w2) r)
    (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') : Coherent (L.val w') := by
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  obtain ⟨-, hv, -⟩ := L.get hget
  cases hcm : m.get? c with
  | some r =>
    simp only [hcm] at h
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    rw [hv]
    exact hc
  | none =>
    simp only [hcm] at h
    obtain ⟨r, w2, hrun, h⟩ := RunsTo.bind h
    obtain ⟨hc2, hfit⟩ := hE w1 r w2 hv hrun
    obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
    obtain ⟨hv3, -, -⟩ := L.cacheModify _ _ _ _ hmod
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    rw [hv3]
    exact coherent_insert hc2 hfit

/-- CANDIDATE, not the compiler's entry and used by nothing: `synthesizeChild`
with a CHECKED insert. A result one of whose modules has the name of a
different cached module is not inserted; the entry throws. -/
def synthesizeChildC (n : Name) : MetaM Res := do
  if let some r := (← sparkleChildCache.get).get? n then return r
  let r ← synthesizeCombinational n
  let m ← sparkleChildCache.get
  if fitsB m r then
    sparkleChildCache.modify (·.insert n r)
    return r
  else
    throwError "child cache: a module of {n} has the name of a different cached module"

/-- **The candidate keeps coherence on a returning run, IF the real entry's
run does** — nothing is asked of the entry's RESULT: the check decides it. -/
theorem synthesizeChildC_coherent (L : RefLaws mref cref) {c : Name}
    {w w' : Void IO.RealWorld} {y : Res} (hc : Coherent (L.val w))
    (hE : ∀ (w1 : Void IO.RealWorld) (r : Res) (w2 : Void IO.RealWorld), L.val w1 = L.val w →
      RunsTo (synthesizeCombinational c) mctx mref cctx cref w1 r w2 → Coherent (L.val w2))
    (h : RunsTo (synthesizeChildC c) mctx mref cctx cref w y w') : Coherent (L.val w') := by
  unfold synthesizeChildC at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  obtain ⟨-, hv, -⟩ := L.get hget
  cases hcm : m.get? c with
  | some r =>
    simp only [hcm] at h
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    rw [hv]
    exact hc
  | none =>
    simp only [hcm] at h
    obtain ⟨r, w2, hrun, h⟩ := RunsTo.bind h
    have hc2 : Coherent (L.val w2) := hE w1 r w2 hv hrun
    obtain ⟨m2, w3, hget2, h⟩ := RunsTo.bind h
    obtain ⟨hm2, hv2, -⟩ := L.get hget2
    by_cases hf : fitsB m2 r = true
    · simp only [hf, ↓reduceIte] at h
      obtain ⟨u, w4, hmod, h⟩ := RunsTo.bind h
      obtain ⟨hv4, -, -⟩ := L.cacheModify _ _ _ _ hmod
      obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
      rw [hm2] at hf
      rw [hv4, hv2]
      exact coherent_insert_of_fitsB hc2 hf
    · simp only [hf, Bool.false_eq_true, ↓reduceIte] at h
      exact (throwError_not_runs _ h).elim

/-! ## (c) Consumption -/

/-- `MachineClosesAt` is the stronger statement. -/
theorem MachineClosesAtC.of_closes {declName : Name} {shape : MachineShape}
    (h : MachineClosesAt mctx mref cctx cref declName shape) :
    MachineClosesAtC mctx mref cctx cref declName shape :=
  fun b w r w' hw _ hd hr => h b w r w' hw hd hr

/-- **The closing from coherent worlds**, from the built relative closing
(`MachineClosesAtS`, for ANY declaration list) and step (b) at the machine
synthesis (`MachineKeepsCoherent`, NOT derived): the run's end world is
coherent, hence satisfies `CacheAgrees` over the list. -/
theorem machineClosesAtC_of_S {declName : Name} {shape : MachineShape} (decls : List Name)
    (hS : MachineClosesAtS mctx mref cctx cref declName shape decls)
    (hK : MachineKeepsCoherent mctx mref cctx cref declName shape) :
    MachineClosesAtC mctx mref cctx cref declName shape :=
  fun b w r w' hw hc hd hr =>
    hS b w r w' hw hd hr (cacheAgrees_of_coherentAt decls (hK b w r w' hw hc hd hr))

end Tools.ShippingCacheCoherent

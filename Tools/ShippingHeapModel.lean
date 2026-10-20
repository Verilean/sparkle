-- BUILT by the integrator: hm1 exit 0, no axioms (ax2) (round par/heap, base 87874a82). No `sorry`, no `axiom`, no `native_decide`.
-- Imports nothing beyond `Init` (the model is generic in the contents' types; see `Sig`).
-- Writing-time guesses (for the integrator), each also marked `-- (guess Gn)` at its site;
-- all six accepted by build hm1 (exit 0, first try):
--   G1 `Ref : Type → Type` with a `Type` index and only a `Nat` field lands in `Type`
--      (indices do not raise the universe); the matches `| _, .cache, … => …` with the
--      index as `_` elaborate (index generalised by the equation compiler).
--   G2 after `cases r` / `cases r'` (index unified with `σ.C` / `σ.S` / `Nat` / `σ.O`, the
--      value `v : α` reverted and reintroduced automatically), the goals close by `rfl`
--      (structure-update projections reduce) or by `if_pos rfl` / `if_neg` on the `other` cell.
--   G3 `change Out.ok … = Out.ok u h' at hr` then `injection` (defeq unfolding of
--      `setM`/`getM`/`bindM` on a hypothesis); fallback `cases hr`.
--   G4 `cases hp` on the `Prop`-valued inductive families `FramedR` / `ThrowsR` / `OpR`
--      (indices `{α}` and the action `p`) substitutes `p`; then `rfl` / `exact hq` close
--      the frame goals because `endW` of a non-throwing action reduces to the new heap.
--   G5 distinct-id side conditions `(@Ref.cache σ).id ≠ (@Ref.synth σ).id` close by
--      `decide` (`RefId` derives `DecidableEq`), fallback `intro e; cases e`.
--   G6 the four families/structure bind their own signature as `τ` (not the section's `σ`),
--      to avoid shadowing; the section's `σ` is then not included in them.

/-! # A minimal explicit heap model for the ref-only fragment of `RefLawsCore`

**What this file is.** A PURE state model, entirely in the logic: a heap with
three tracked cells (the child cache, the synthesis ref, the synthesis depth —
`sparkleChildCache`, `sparkleChildSynth`, `sparkleSynthDepth` in the compiler),
an unbounded family of OTHER cells (`other n`, every other ref: the side refs
`SideRef`, run-local refs, freshly allocated refs) and a printer-registry
component `reg` (the diagnostic environment). Refs are typed (`Ref σ α`);
`hget` / `hset` / `alloc` are pure functions; actions are state functions with an
exception outcome (`M σ α`, the shape of `EST`).

In this model we PROVE

* the generic ref laws: get-after-set (`get_set_same`), frame of a write for a
  ref with a different id (`get_set_other`), read-frame (`runsTo_getM`: a read
  leaves the heap), modify = get;set (`modify_split`, `endW_modifyM`),
  allocation leaves every existing cell and is readable (`allocM_runs`);
* the model analogues of the REF-ONLY fields of `RefLawsCore`
  (`Tools/ShippingChildBndCore.lean`): `frame` (reads of the three refs;
  get/set/modify/modifyGet of other refs; allocation), `frameQ`, `cacheSet`,
  `depthSet`, `cacheSetQ`, `depthSetQ`, `frameT` (a throw) and `excOk` (only
  for the model's own throws), packed as a structure `HeapLaws` whose fields
  have the SAME shape as the `RefLawsCore` fields of the same names;
* `HeapLaws.model` instantiates `HeapLaws` for every signature, every quiet
  predicate on the registry and every exception class. This shows ONLY that the
  ref-only fragment, RESTATED over the pure model (`HeapLaws` over `Heap σ`, a
  different type from the real `Void IO.RealWorld` / `MetaM`), is satisfiable by
  that model (`heapLaws_sat`: a law witness with a quiet start heap and the
  start contents of `childBnd_iff_core`). It says nothing about `RefLawsCore`
  itself (no `RefLawsCore` value is built) nor about the real runtime;
* `frame_all_false`: a frame law over ALL actions (caller-supplied ones
  included) is FALSE in the model — the shape of the `Framed.ioFlush`
  inconsistency removed in `dc50653e` (`docs/ShippingCompiler-TrustBase.md`).

**What this file is NOT.**

* It is NOT connected to Lean's runtime. `ST.Prim.Ref.get/set` are
  `@[extern] opaque` (`Init/System/ST.lean:186-191`, v4.32.1) and the world is
  the opaque `Void IO.RealWorld` (`ST.lean:15-17`). That this pure model is
  ADEQUATE to the extern refs (the "fit") is a SEPARATE, OPEN ledger item; no
  statement here mentions `IO.Ref`, `MetaM` or `Void IO.RealWorld`.
* It does NOT cover the `RefLawsCore` fields about Lean's own code: `diag`
  (printers / stderr / file handles), `excOk` for Lean's elaborator exceptions
  (`OkExc`, `OkEnv`), the `frame`/`frameQ` constructors for Meta primitives
  (`whnf`, `inferType`, `getConstInfo`, …), `telescope`, `lamTelescope`,
  `localDecl`, `letDecl`. These stay open.
* It does NOT discharge `ChildBnd`, `RefLawsCore`, or any premise; it adds no
  law and no axiom. Joint satisfiability of `RefLawsCore` itself (even of its
  ref-only fields, which are stated over `IO.Ref` / `MetaM`, not over `Heap σ`)
  is NOT PROVEN (no proof either way); it stays OPEN.

Audit and ledger: `docs/parallel/heap-model-audit.md`. -/

namespace Tools.ShippingHeapModel

/-- The contents' types. In the compiler: `C = Std.HashMap Name Res` (cache),
`S = Option (Name → MetaM Res)` (synthesis ref); the depth is `Nat` (fixed).
`O`: the contents of every other cell (one type for all of them — instantiate
by a sum type for heterogeneous side refs; the compiler's `sparkleSubModuleCache`
has the SAME type as the cache, and several side refs have type `Nat` like the
depth: same type, different cell, is exactly what `other n` models).
`P`: the printer registry / diagnostic environment. `E`: exceptions. -/
structure Sig where
  C : Type
  S : Type
  O : Type
  P : Type
  E : Type

/-- The heap: three tracked cells, the other cells, the allocation pointer,
the printer registry. -/
structure Heap (σ : Sig) where
  cache : σ.C
  synth : σ.S
  depth : Nat
  other : Nat → σ.O
  next : Nat
  reg : σ.P

/-- Typed refs. The three tracked refs and the other cells are DIFFERENT
constructors: a ref of the model cannot be re-typed onto a tracked cell
(unlike `ST.Ref`, a structure over an untyped pointer, `ST.lean:172`). -/
-- (guess G1)
inductive Ref (σ : Sig) : Type → Type
  | cache : Ref σ σ.C
  | synth : Ref σ σ.S
  | depth : Ref σ Nat
  | other (n : Nat) : Ref σ σ.O

/-- The identity of a ref (its cell). -/
inductive RefId
  | cache
  | synth
  | depth
  | other (n : Nat)
  deriving DecidableEq

variable {σ : Sig}

def Ref.id : {α : Type} → Ref σ α → RefId
  | _, .cache => .cache
  | _, .synth => .synth
  | _, .depth => .depth
  | _, .other n => .other n

/-- Read a cell (pure). -/
def hget : {α : Type} → Ref σ α → Heap σ → α
  | _, .cache, h => h.cache
  | _, .synth, h => h.synth
  | _, .depth, h => h.depth
  | _, .other n, h => h.other n

/-- Write a cell (pure). -/
def hset : {α : Type} → Ref σ α → α → Heap σ → Heap σ
  | _, .cache, v, h => { h with cache := v }
  | _, .synth, v, h => { h with synth := v }
  | _, .depth, v, h => { h with depth := v }
  | _, .other n, v, h => { h with other := fun m => if m = n then v else h.other m }

/-- Allocate a fresh other cell holding `v` (pure): the new ref and heap. -/
def alloc (v : σ.O) (h : Heap σ) : Ref σ σ.O × Heap σ :=
  (.other h.next,
   { h with other := fun m => if m = h.next then v else h.other m, next := h.next + 1 })

/-! ## Generic ref laws (theorems of the model) -/

/-- **Get after set**, same ref. -/
theorem get_set_same {α : Type} (r : Ref σ α) (v : α) (h : Heap σ) : hget r (hset r v h) = v := by
  -- (guess G2)
  cases r with
  | other n =>
    show (if n = n then v else h.other n) = v
    exact if_pos rfl
  | cache => rfl
  | synth => rfl
  | depth => rfl

/-- **Non-aliasing**: a write leaves every cell of a different id. -/
theorem get_set_other {α β : Type} (r : Ref σ α) (r' : Ref σ β) (v : α) (h : Heap σ)
    (hne : r.id ≠ r'.id) : hget r' (hset r v h) = hget r' h := by
  -- (guess G2)
  cases r with
  | other n =>
    cases r' with
    | other m =>
      have hnm : m ≠ n := fun e => hne (by subst e; rfl)
      show (if m = n then v else h.other m) = h.other m
      exact if_neg hnm
    | cache => rfl
    | synth => rfl
    | depth => rfl
  | cache => cases r' <;> first | rfl | exact (hne rfl).elim
  | synth => cases r' <;> first | rfl | exact (hne rfl).elim
  | depth => cases r' <;> first | rfl | exact (hne rfl).elim

/-- A write leaves the printer registry. -/
theorem set_reg {α : Type} (r : Ref σ α) (v : α) (h : Heap σ) : (hset r v h).reg = h.reg := by
  cases r <;> rfl

/-- Allocation returns a cell that reads `v`, and leaves every cell `< next`
and the three tracked cells and the registry. -/
theorem alloc_spec (v : σ.O) (h : Heap σ) :
    hget (alloc v h).1 (alloc v h).2 = v ∧
    (∀ m, m < h.next → (alloc v h).2.other m = h.other m) ∧
    (alloc v h).2.cache = h.cache ∧ (alloc v h).2.synth = h.synth ∧
    (alloc v h).2.depth = h.depth ∧ (alloc v h).2.reg = h.reg ∧
    (alloc v h).2.next = h.next + 1 := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · show (if h.next = h.next then v else h.other h.next) = v
    exact if_pos rfl
  · intro m hm
    show (if m = h.next then v else h.other m) = h.other m
    exact if_neg (Nat.ne_of_lt hm)

/-! ## Actions: state functions with an exception outcome (the shape of `EST`) -/

/-- An outcome: a value or an exception, and the heap it ends in. -/
inductive Out (σ : Sig) (α : Type) where
  | ok (a : α) (h : Heap σ)
  | error (e : σ.E) (h : Heap σ)

/-- An action. -/
abbrev M (σ : Sig) (α : Type) : Type := Heap σ → Out σ α

def pureM {α : Type} (a : α) : M σ α := fun h => .ok a h

def bindM {α β : Type} (x : M σ α) (f : α → M σ β) : M σ β := fun h =>
  match x h with
  | .ok a h' => f a h'
  | .error e h' => .error e h'

def getM {α : Type} (r : Ref σ α) : M σ α := fun h => .ok (hget r h) h

def setM {α : Type} (r : Ref σ α) (v : α) : M σ Unit := fun h => .ok () (hset r v h)

/-- `modify` is DEFINED as a read then a write (as `ST.Prim.Ref.modify` is). -/
def modifyM {α : Type} (r : Ref σ α) (f : α → α) : M σ Unit :=
  bindM (getM r) fun a => setM r (f a)

def modifyGetM {α β : Type} (r : Ref σ α) (f : α → β × α) : M σ β :=
  bindM (getM r) fun a => bindM (setM r (f a).2) fun _ => pureM (f a).1

def allocM (v : σ.O) : M σ (Ref σ σ.O) := fun h => .ok (alloc v h).1 (alloc v h).2

def throwM {α : Type} (e : σ.E) : M σ α := fun h => .error e h

/-- The heap a run ends in, on either outcome (`endW`, `ShippingChildInv.lean:300`). -/
def endW {α : Type} (p : M σ α) (h : Heap σ) : Heap σ :=
  match p h with
  | .ok _ h' => h'
  | .error _ h' => h'

/-- A successful run (`RunsTo`, `ShippingEntrySoundness.lean:937`). -/
def RunsTo {α : Type} (p : M σ α) (h : Heap σ) (a : α) (h' : Heap σ) : Prop :=
  p h = .ok a h'

/-- What a read returns (`readOf`, `ShippingChildInv.lean:102`). -/
def readOf {α : Type} (r : Ref σ α) (h : Heap σ) : α := hget r h

/-- The three tracked values (`cv`/`sv`/`dv`, `ShippingChildBndCore.lean:43-47`). -/
def cv (h : Heap σ) : σ.C := readOf (@Ref.cache σ) h
def sv (h : Heap σ) : σ.S := readOf (@Ref.synth σ) h
def dv (h : Heap σ) : Nat := readOf (@Ref.depth σ) h

/-- **Read-frame**: a read returns the contents and leaves the heap. -/
theorem runsTo_getM {α : Type} (r : Ref σ α) {h : Heap σ} {a : α} {h' : Heap σ}
    (hr : RunsTo (getM r) h a h') : a = readOf r h ∧ h' = h := by
  -- (guess G3)
  change Out.ok (hget r h) h = Out.ok a h' at hr
  injection hr with h1 h2
  exact ⟨h1.symm, h2.symm⟩

/-- A write ends in `hset`. -/
theorem runsTo_setM {α : Type} (r : Ref σ α) (v : α) {h : Heap σ} {u : Unit} {h' : Heap σ}
    (hr : RunsTo (setM r v) h u h') : h' = hset r v h := by
  -- (guess G3)
  change Out.ok () (hset r v h) = Out.ok u h' at hr
  injection hr with _ h2
  exact h2.symm

/-- **modify = get; set** (the model's `modify_split`,
cf. `ShippingChildBndCore.modify_split`). -/
theorem modify_split {α : Type} (r : Ref σ α) (f : α → α) {h : Heap σ} {u : Unit}
    {h' : Heap σ} (hr : RunsTo (modifyM r f) h u h') :
    ∃ h1, RunsTo (getM r) h (readOf r h) h1 ∧ RunsTo (setM r (f (readOf r h))) h1 u h' :=
  -- (guess G3: `modifyM r f h` reduces to `setM r (f (get r h)) h` by `bindM`'s match)
  ⟨h, rfl, hr⟩

/-- The end heap of a `modify`. -/
theorem endW_modifyM {α : Type} (r : Ref σ α) (f : α → α) (h : Heap σ) :
    endW (modifyM r f) h = hset r (f (hget r h)) h := rfl

/-- Allocation's run. -/
theorem allocM_runs (v : σ.O) {h : Heap σ} {r : Ref σ σ.O} {h' : Heap σ}
    (hr : RunsTo (allocM v) h r h') :
    readOf r h' = v ∧ cv h' = cv h ∧ sv h' = sv h ∧ dv h' = dv h ∧ h'.reg = h.reg := by
  -- (guess G3)
  change Out.ok (alloc v h).1 (alloc v h).2 = Out.ok r h' at hr
  injection hr with h1 h2
  subst h1; subst h2
  obtain ⟨hg, _, hc, hs, hd, hreg, _⟩ := alloc_spec v h
  exact ⟨hg, hc, hs, hd, hreg⟩

/-! ## The operation classes (ref-only analogues of `Framed`, `Throws`, `Op`) -/

/-- The ref-only constructors of `Framed` (`ShippingChildInv.lean:189`): reads
of the three tracked refs; get / set / modify / modifyGet of any OTHER cell
(the side refs and run-local refs); allocation of a fresh cell (`IO.mkRef`). -/
inductive FramedR (τ : Sig) : {α : Type} → M τ α → Prop
  | cacheGet : FramedR τ (getM (@Ref.cache τ))
  | synthGet : FramedR τ (getM (@Ref.synth τ))
  | depthGet : FramedR τ (getM (@Ref.depth τ))
  | otherGet (n : Nat) : FramedR τ (getM (@Ref.other τ n))
  | otherSet (n : Nat) (v : τ.O) : FramedR τ (setM (@Ref.other τ n) v)
  | otherModify (n : Nat) (f : τ.O → τ.O) : FramedR τ (modifyM (@Ref.other τ n) f)
  | otherModifyGet {β : Type} (n : Nat) (f : τ.O → β × τ.O) :
      FramedR τ (modifyGetM (@Ref.other τ n) f)
  | alloc (v : τ.O) : FramedR τ (allocM (σ := τ) v)

/-- Throwing (`Throws`, `ShippingChildInv.lean:281`). -/
inductive ThrowsR (τ : Sig) : {α : Type} → M τ α → Prop
  | err {α : Type} (e : τ.E) : ThrowsR τ (throwM (α := α) e)

/-- The operations whose exceptions are asked to be in the class `okE`
(`Op`, `ShippingChildInv.lean:288`, without its `diag` constructor). -/
inductive OpR (τ : Sig) (okE : τ.E → Prop) : {α : Type} → M τ α → Prop
  | framed {α : Type} {p : M τ α} : FramedR τ p → OpR τ okE p
  | throwErr {α : Type} (e : τ.E) : okE e → OpR τ okE (throwM (α := α) e)

/-- A ref-only framed operation never throws. -/
theorem FramedR.runs {α : Type} {p : M σ α} (hp : FramedR σ p) (h : Heap σ) :
    ∃ a h', p h = .ok a h' := by
  -- (guess G4)
  cases hp <;> exact ⟨_, _, rfl⟩

/-- The end heap of a ref-only framed operation keeps the three tracked cells
and the registry. -/
theorem FramedR.keeps {α : Type} {p : M σ α} (hp : FramedR σ p) (h : Heap σ) :
    cv (endW p h) = cv h ∧ sv (endW p h) = sv h ∧ dv (endW p h) = dv h ∧
      (endW p h).reg = h.reg := by
  -- (guess G4: every case reduces to `rfl` — `endW` of a read is `h`, of a write
  -- to `other n` a structure update of `other`, of `alloc` an update of `other`/`next`)
  cases hp <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The law bundle, in the shape of `RefLawsCore` (ref-only fields) -/

/-- **The ref-only fragment of `RefLawsCore`** (`ShippingChildBndCore.lean`
`structure RefLawsCore`), stated over the model: field for field the shape of
the `RefLawsCore` field of the same name, with `MetaM` replaced by `M σ`, the
world by the heap, `Framed`/`Throws`/`Op` by `FramedR`/`ThrowsR`/`OpR`, and
`OkExc` by a parameter `okE`. The `RefLawsCore` fields `diag`, `telescope`,
`lamTelescope`, `localDecl`, `letDecl` and the Meta-primitive constructors of
`Framed` have NO counterpart here (they are about Lean's own code). -/
structure HeapLaws (τ : Sig) (okE : τ.E → Prop) where
  quiet : Heap τ → Prop
  frameT : ∀ {α : Type} (p : M τ α), ThrowsR τ p → ∀ h,
    (cv (endW p h) = cv h ∧ sv (endW p h) = sv h ∧ dv (endW p h) = dv h) ∧
    (quiet h → quiet (endW p h))
  excOk : ∀ {α : Type} (p : M τ α), OpR τ okE p →
    ∀ h e h', quiet h → p h = .error e h' → okE e
  frameQ : ∀ {α : Type} (p : M τ α), FramedR τ p → ∀ h, quiet h → quiet (endW p h)
  cacheSetQ : ∀ (v : τ.C) (h : Heap τ) (u : Unit) (h' : Heap τ),
    RunsTo (setM (@Ref.cache τ) v) h u h' → quiet h → quiet h'
  depthSetQ : ∀ (v : Nat) (h : Heap τ) (u : Unit) (h' : Heap τ),
    RunsTo (setM (@Ref.depth τ) v) h u h' → quiet h → quiet h'
  frame : ∀ {α : Type} (p : M τ α), FramedR τ p → ∀ h,
    cv (endW p h) = cv h ∧ sv (endW p h) = sv h ∧ dv (endW p h) = dv h
  cacheSet : ∀ (v : τ.C) (h : Heap τ) (u : Unit) (h' : Heap τ),
    RunsTo (setM (@Ref.cache τ) v) h u h' → cv h' = v ∧ sv h' = sv h ∧ dv h' = dv h
  depthSet : ∀ (v : Nat) (h : Heap τ) (u : Unit) (h' : Heap τ),
    RunsTo (setM (@Ref.depth τ) v) h u h' → cv h' = cv h ∧ sv h' = sv h ∧ dv h' = v

/-- **The model satisfies the ref-only fragment as restated over `Heap σ`**, for every signature, every
quiet predicate `Q` on the printer registry and every exception class `okE`:
`quiet h := Q h.reg`. This shows only that the fragment RESTATED over `Heap σ`
is satisfiable by this model; it says nothing about `RefLawsCore` itself (stated
over `IO.Ref` / `MetaM` / `Void IO.RealWorld`) nor about the real runtime. -/
def HeapLaws.model (Q : σ.P → Prop) (okE : σ.E → Prop) : HeapLaws σ okE where
  quiet := fun h => Q h.reg
  frameT := by
    intro α p hp h
    -- (guess G4)
    cases hp
    exact ⟨⟨rfl, rfl, rfl⟩, fun hq => hq⟩
  excOk := by
    intro α p hop h e h' _ he
    cases hop with
    | framed hf =>
      obtain ⟨a, h1, hok⟩ := hf.runs h
      rw [hok] at he
      cases he
    | throwErr e0 hok0 =>
      change Out.error e0 h = Out.error e h' at he
      injection he with h1 _
      exact h1 ▸ hok0
  frameQ := by
    intro α p hp h hq
    have hk := hp.keeps h
    show Q (endW p h).reg
    rw [hk.2.2.2]
    exact hq
  cacheSetQ := by
    intro v h u h' hr hq
    have e := runsTo_setM _ v hr
    subst e
    show Q (hset (@Ref.cache σ) v h).reg
    rw [set_reg]
    exact hq
  depthSetQ := by
    intro v h u h' hr hq
    have e := runsTo_setM _ v hr
    subst e
    show Q (hset (@Ref.depth σ) v h).reg
    rw [set_reg]
    exact hq
  frame := by
    intro α p hp h
    have hk := hp.keeps h
    exact ⟨hk.1, hk.2.1, hk.2.2.1⟩
  cacheSet := by
    intro v h u h' hr
    have e := runsTo_setM _ v hr
    subst e
    exact ⟨get_set_same (@Ref.cache σ) v h,
      get_set_other (@Ref.cache σ) (@Ref.synth σ) v h (by first | decide | (intro e; cases e)),
      get_set_other (@Ref.cache σ) (@Ref.depth σ) v h (by first | decide | (intro e; cases e))⟩
  depthSet := by
    intro v h u h' hr
    have e := runsTo_setM _ v hr
    subst e
    exact ⟨get_set_other (@Ref.depth σ) (@Ref.cache σ) v h (by first | decide | (intro e; cases e)),
      get_set_other (@Ref.depth σ) (@Ref.synth σ) v h (by first | decide | (intro e; cases e)),
      get_set_same (@Ref.depth σ) v h⟩

/-- **Satisfiability with the start condition** (the model analogue of the
right-hand side of `childBnd_iff_core`, `ShippingChildBndCore.lean:285`): for
any quiet registry value, a law witness and a quiet heap whose synthesis cell
holds any given `s0`, whose depth is 0 and whose cache holds any given `c0`.
In the MODEL only (`HeapLaws` over `Heap σ`, not `RefLawsCore`). -/
theorem heapLaws_sat (okE : σ.E → Prop) (Q : σ.P → Prop) (p0 : σ.P) (hp0 : Q p0)
    (c0 : σ.C) (s0 : σ.S) (o0 : σ.O) :
    ∃ (L : HeapLaws σ okE) (h : Heap σ),
      L.quiet h ∧ readOf (@Ref.synth σ) h = s0 ∧ readOf (@Ref.depth σ) h = 0 ∧
        readOf (@Ref.cache σ) h = c0 :=
  ⟨HeapLaws.model Q okE,
   { cache := c0, synth := s0, depth := 0, other := fun _ => o0, next := 0, reg := p0 },
   hp0, rfl, rfl, rfl⟩

/-- The fragment RESTATED over `Heap σ` (`HeapLaws`) has a witness (no start condition).
In the MODEL only: not a statement about `RefLawsCore` or the runtime. -/
theorem heapLaws_nonempty (okE : σ.E → Prop) : Nonempty (HeapLaws σ okE) :=
  ⟨HeapLaws.model (fun _ => True) okE⟩

/-! ## Why caller-supplied actions must stay out of a frame law -/

/-- **A frame law over ALL actions is false in the model** as soon as the cache
type has a value different from some heap's cache: a caller may pass the write
itself. (The shape of the `Framed.ioFlush` inconsistency, removed in
`dc50653e`: a frame for the `flush` of any stream, i.e. of any action.) -/
theorem frame_all_false (h : Heap σ) (c : σ.C) (hc : c ≠ h.cache) :
    ¬ (∀ {α : Type} (p : M σ α) (h : Heap σ), cv (endW p h) = cv h) := by
  intro hall
  exact hc (hall (setM (@Ref.cache σ) c) h)

end Tools.ShippingHeapModel

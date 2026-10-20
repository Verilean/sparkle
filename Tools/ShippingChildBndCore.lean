import Tools.ShippingChildBndInit
-- Round par/cbnd. BUILT: cb1 (Init exit 0; Core failed: `C` not in scope in two theorems), cb2 (exit 0 after the integrator added the explicit `(C : RefLawsCore mref cref)` binder to `cacheModify' and depthModify'`); axioms standard (ax1). No `sorry`, no `axiom`, no `native_decide`.
-- Writing-time guesses are marked `-- (writing-time guess, accepted by build cb2: …)`.

/-! # The runtime residual of `RefLaws`, as an EQUIVALENT smaller structure

`RefLaws` (`Tools/ShippingChildInv.lean:333`) has 26 fields. Twelve of them
carry no runtime content once the value functions are taken to BE the refs'
contents (`readOf`, `ShippingChildInv.lean:102`):

* `val`, `sval`, `dval` — every witness's values ARE `readOf` of the three refs
  (`ShippingChildBndInit.refLaws_val_eq` …); here they are DEFINED so;
* `cacheGet`, `synthGet`, `depthGet` — then hold by the definition of the
  lift (`ShippingChildBndInit.runsTo_get_readOf`);
* `aux`, `auxInsert` — a proof parameter; taken `True` (`RefLaws.plain`);
* `cacheModify`, `depthModify`, `cacheModifyQ`, `depthModifyQ` — `ST.Ref.modify`
  is DEFINED (`Init/System/ST.lean`, `ST.Prim.Ref.modify`: a `def`, get then
  set) as a read followed by a write: derived from `frame`/`frameQ` of the
  read and `cacheSet`/`depthSet`/`cacheSetQ`/`depthSetQ` (`modify_split`).

`RefLawsCore` holds the other 14 fields, stated with `readOf`.
`RefLawsCore.toRefLaws` builds a `RefLaws`; `RefLawsCore.ofRefLaws` goes back
(no strengthening). Hence

  `ChildBnd w ↔ (∃ C : RefLawsCore, C.quiet w) ∧ readOf-start-condition at w`

(`childBnd_iff_core`). Every field of `RefLawsCore` relates `readOf` at TWO
worlds (before / after an operation) or speaks of `quiet`; none is provable
without a model of `ST.Prim.Ref.get` / `set` (opaque, `@[extern]`). -/

namespace Tools.ShippingChildBndCore
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- What the cache holds in `w`. -/
def cv (w : Void IO.RealWorld) : Std.HashMap Name Res := readOf sparkleChildCache w
/-- What the synthesis ref holds in `w`. -/
def sv (w : Void IO.RealWorld) : Option (Name → MetaM Res) := readOf sparkleChildSynth w
/-- What the depth ref holds in `w`. -/
def dv (w : Void IO.RealWorld) : Nat := readOf sparkleSynthDepth w

/-! ## `modify` is a read then a write (by definition) -/

/-- **A successful `modify` is a successful read of the current contents
followed by a successful write of `f` of them** — by the definitions of
`ST.Prim.Ref.modify` and `ST.bind`, no law. -/
theorem modify_split {σ : Type} (r : IO.Ref σ) (f : σ → σ) {w : Void IO.RealWorld} {u : Unit}
    {w' : Void IO.RealWorld}
    (h : RunsTo (ST.Ref.modify r f : MetaM Unit) mctx mref cctx cref w u w') :
    ∃ w1, RunsTo (ST.Ref.get r : MetaM σ) mctx mref cctx cref w (readOf r w) w1 ∧
      RunsTo (ST.Ref.set r (f (readOf r w)) : MetaM Unit) mctx mref cctx cref w1 u w' := by
  have hm : ∀ v s, (ST.Ref.get r : ST IO.RealWorld σ) w = ST.Out.mk v s →
      readOf r w = v ∧
      RunsTo (ST.Ref.get r : MetaM σ) mctx mref cctx cref w v s ∧
      (ST.Ref.modify r f : MetaM Unit) mctx mref cctx cref w =
        (ST.Ref.set r (f v) : MetaM Unit) mctx mref cctx cref s := by
    intro v s hg
    refine ⟨?_, ?_, ?_⟩
    · unfold readOf; rw [hg]; try rfl
    · unfold RunsTo
      change (match (ST.Ref.get r : ST IO.RealWorld σ) w with | .mk a s => EST.Out.ok a s) = _
      rw [hg]; try rfl
    · -- (writing-time guess, accepted by build cb2: the lift of a `ST` action into `MetaM`, as in `refModify_runs` /
      -- `refSet_runs`, ShippingChildInv.lean:699-716)
      change (match (ST.Ref.modify r f : ST IO.RealWorld Unit) w with
          | .mk a s => EST.Out.ok a s) =
        (match (ST.Ref.set r (f v) : ST IO.RealWorld Unit) s with
          | .mk a s => EST.Out.ok a s)
      have hst : (ST.Ref.modify r f : ST IO.RealWorld Unit) w =
          (ST.Ref.set r (f v) : ST IO.RealWorld Unit) s := by
        -- (writing-time guess, accepted by build cb2: `ST.Ref.modify` (liftM of `ST.Prim.Ref.modify`, a `def` with
        -- `@[implemented_by]`) and `ST.bind` unfold by `change` in a non-`module` file; if the
        -- module system hides `ST.Prim.Ref.modify`'s body, this step fails and the four modify
        -- fields must move into `RefLawsCore`)
        change (match (ST.Ref.get r : ST IO.RealWorld σ) w with
          | .mk x s' => (ST.Ref.set r (f x) : ST IO.RealWorld Unit) s') = _
        rw [hg]; try rfl
      rw [hst]; try rfl
  cases hg : (ST.Ref.get r : ST IO.RealWorld σ) w with
  | mk v s =>
    obtain ⟨hv, hget, heq⟩ := hm v s hg
    refine ⟨s, by rw [hv]; exact hget, ?_⟩
    rw [hv]
    unfold RunsTo
    rw [← heq]
    exact h

/-! ## The residual structure -/

/-- **The runtime residual of `RefLaws`**: the 14 fields that relate the refs'
contents at two worlds or speak of `quiet`, with the values taken to be the
contents (`cv`, `sv`, `dv`). Field for field the statement of the
`RefLaws` field of the same name with `val := cv`, `sval := sv`,
`dval := dv` (copied from `ShippingChildInv.lean:351-442`). -/
structure RefLawsCore (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) where
  quiet : Void IO.RealWorld → Prop
  diag : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type} (p : MetaM α), Diag p → ∀ w,
    quiet w →
    (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w) ∧ quiet (endW mctx mref cctx cref p w)
  frameT : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type} (p : MetaM α), Throws p → ∀ w,
    (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w) ∧
    (quiet w → quiet (endW mctx mref cctx cref p w))
  excOk : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type} (p : MetaM α), Op p →
    ∀ w e w', quiet w → p mctx mref cctx cref w = .error e w' → OkExc e
  frameQ : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type} (p : MetaM α), Framed p → ∀ w,
    quiet w → quiet (endW mctx mref cctx cref p w)
  cacheSetQ : ∀ {mctx : Meta.Context} {cctx : Core.Context} v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → quiet w → quiet w'
  depthSetQ : ∀ {mctx : Meta.Context} {cctx : Core.Context} v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' →
    quiet w → quiet w'
  frame : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type} (p : MetaM α), Framed p → ∀ w,
    cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w
  cacheSet : ∀ {mctx : Meta.Context} {cctx : Core.Context} v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' →
    cv w' = v ∧ sv w' = sv w ∧ dv w' = dv w
  depthSet : ∀ {mctx : Meta.Context} {cctx : Core.Context} v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' →
    cv w' = cv w ∧ sv w' = sv w ∧ dv w' = v
  telescope : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop),
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (ty : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b,
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.forallTelescopeReducing ty k)
  lamTelescope : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop),
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b,
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup)
  localDecl : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop),
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLocalDeclD n ty k)
  letDecl : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop),
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty v : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLetDecl n ty v k)

namespace RefLawsCore
variable (C : RefLawsCore mref cref)

/-- The cache's `modify`, from the read's frame and the write. -/
theorem cacheModify' (C : RefLawsCore mref cref) (f : Std.HashMap Name Res → Std.HashMap Name Res) {w : Void IO.RealWorld}
    {u : Unit} {w' : Void IO.RealWorld}
    (h : RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w') :
    cv w' = f (cv w) ∧ sv w' = sv w ∧ dv w' = dv w := by
  obtain ⟨w1, hg, hs⟩ := modify_split sparkleChildCache f h
  have h1 := C.frame (mctx := mctx) (cctx := cctx) _ Framed.cacheGet w
  rw [endW_of_runs hg] at h1
  have h2 := C.cacheSet _ _ _ _ hs
  exact ⟨h2.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem cacheModifyQ' (f : Std.HashMap Name Res → Std.HashMap Name Res) {w : Void IO.RealWorld}
    {u : Unit} {w' : Void IO.RealWorld}
    (h : RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w')
    (hq : C.quiet w) : C.quiet w' := by
  obtain ⟨w1, hg, hs⟩ := modify_split sparkleChildCache f h
  have h1 := C.frameQ (mctx := mctx) (cctx := cctx) _ Framed.cacheGet w hq
  rw [endW_of_runs hg] at h1
  exact C.cacheSetQ _ _ _ _ hs h1

/-- The depth's `modify`, from the read's frame and the write. -/
theorem depthModify' (C : RefLawsCore mref cref) (f : Nat → Nat) {w : Void IO.RealWorld} {u : Unit} {w' : Void IO.RealWorld}
    (h : RunsTo (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) mctx mref cctx cref w u w') :
    cv w' = cv w ∧ sv w' = sv w ∧ dv w' = f (dv w) := by
  obtain ⟨w1, hg, hs⟩ := modify_split sparkleSynthDepth f h
  have h1 := C.frame (mctx := mctx) (cctx := cctx) _ Framed.depthGet w
  rw [endW_of_runs hg] at h1
  have h2 := C.depthSet _ _ _ _ hs
  exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2⟩

theorem depthModifyQ' (f : Nat → Nat) {w : Void IO.RealWorld} {u : Unit} {w' : Void IO.RealWorld}
    (h : RunsTo (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) mctx mref cctx cref w u w')
    (hq : C.quiet w) : C.quiet w' := by
  obtain ⟨w1, hg, hs⟩ := modify_split sparkleSynthDepth f h
  have h1 := C.frameQ (mctx := mctx) (cctx := cctx) _ Framed.depthGet w hq
  rw [endW_of_runs hg] at h1
  exact C.depthSetQ _ _ _ _ hs h1

/-- **A `RefLaws` witness from the residual** (values := contents, `aux := True`). -/
def toRefLaws : RefLaws mref cref where
  val := cv
  sval := sv
  dval := dv
  aux := fun _ => True
  auxInsert := fun _ _ _ _ _ _ _ => trivial
  quiet := C.quiet
  diag := C.diag
  frameT := C.frameT
  excOk := C.excOk
  frameQ := C.frameQ
  cacheSetQ := C.cacheSetQ
  cacheModifyQ := fun f _ _ _ h hq => C.cacheModifyQ' f h hq
  depthSetQ := C.depthSetQ
  depthModifyQ := fun f _ _ _ h hq => C.depthModifyQ' f h hq
  frame := C.frame
  -- (writing-time guess, accepted by build cb2: `m = cv w` is accepted for `m = readOf sparkleChildCache w` by unfolding `cv`)
  cacheGet := fun _ _ _ h => runsTo_get_readOf sparkleChildCache h
  cacheSet := C.cacheSet
  cacheModify := fun f _ _ _ h => C.cacheModify' f h
  synthGet := fun _ _ _ h => runsTo_get_readOf sparkleChildSynth h
  depthGet := fun _ _ _ h => runsTo_get_readOf sparkleSynthDepth h
  depthSet := C.depthSet
  depthModify := fun f _ _ _ h => C.depthModify' f h
  telescope := C.telescope
  lamTelescope := C.lamTelescope
  localDecl := C.localDecl
  letDecl := C.letDecl

theorem toRefLaws_quiet : C.toRefLaws.quiet = C.quiet := rfl

end RefLawsCore

/-- **The converse: a `RefLaws` witness gives the residual** (its values are
the contents, `refLaws_val_eq` …; the contexts only run the reads). So
`RefLawsCore` asks nothing `RefLaws` does not. -/
def RefLawsCore.ofRefLaws (mctx0 : Meta.Context) (cctx0 : Core.Context) (L : RefLaws mref cref) :
    RefLawsCore mref cref :=
  have hv : L.val = cv := funext fun w => refLaws_val_eq L mctx0 cctx0 w
  have hs : L.sval = sv := funext fun w => refLaws_sval_eq L mctx0 cctx0 w
  have hd : L.dval = dv := funext fun w => refLaws_dval_eq L mctx0 cctx0 w
  { quiet := L.quiet
    -- (writing-time guess, accepted by build cb2: `rw [← hv, ← hs, ← hd]` rewrites the constants `cv`/`sv`/`dv` under the
    -- field's binders (no bound variable in the pattern) back to `L.val`/`L.sval`/`L.dval`)
    diag := by rw [← hv, ← hs, ← hd]; exact L.diag
    frameT := by rw [← hv, ← hs, ← hd]; exact L.frameT
    excOk := L.excOk
    frameQ := L.frameQ
    cacheSetQ := L.cacheSetQ
    depthSetQ := L.depthSetQ
    frame := by rw [← hv, ← hs, ← hd]; exact L.frame
    cacheSet := by rw [← hv, ← hs, ← hd]; exact L.cacheSet
    depthSet := by rw [← hv, ← hs, ← hd]; exact L.depthSet
    telescope := by rw [← hv, ← hs, ← hd]; exact L.telescope
    lamTelescope := by rw [← hv, ← hs, ← hd]; exact L.lamTelescope
    localDecl := by rw [← hv, ← hs, ← hd]; exact L.localDecl
    letDecl := by rw [← hv, ← hs, ← hd]; exact L.letDecl }

theorem RefLawsCore.ofRefLaws_quiet (mctx0 : Meta.Context) (cctx0 : Core.Context)
    (L : RefLaws mref cref) : (RefLawsCore.ofRefLaws mctx0 cctx0 L).quiet = L.quiet := rfl

/-! ## The boundary, by the residual -/

/-- **`ChildBnd` from the residual and the start contents** — no contexts, no
`RefLaws`: the witness is built (`toRefLaws`), and its `StartV` IS the
start-contents condition (values := contents). -/
theorem childBnd_of_core {w : Void IO.RealWorld} (C : RefLawsCore mref cref) (hq : C.quiet w)
    (hs : readOf sparkleChildSynth w = some synthesizeChild)
    (hd : readOf sparkleSynthDepth w = 0 ∨ CacheInv mref cref (readOf sparkleChildCache w)) :
    ChildBnd mref cref w :=
  -- (writing-time guess, accepted by build cb2: `StartV C.toRefLaws w` unfolds to the two hypotheses' conjunction by `cv`/`sv`/`dv`)
  ⟨C.toRefLaws, ⟨hs, hd⟩, hq⟩

/-- The outermost form: the residual, the synthesis ref installed, depth 0. -/
theorem childBnd_of_core_init {w : Void IO.RealWorld} (C : RefLawsCore mref cref) (hq : C.quiet w)
    (hs : readOf sparkleChildSynth w = some synthesizeChild)
    (hd : readOf sparkleSynthDepth w = 0) : ChildBnd mref cref w :=
  childBnd_of_core C hq hs (Or.inl hd)

/-- **The split is exact**: `ChildBnd` is the residual's existence at a quiet
`w` together with the start contents. -/
theorem childBnd_iff_core (mctx0 : Meta.Context) (cctx0 : Core.Context) {w : Void IO.RealWorld} :
    ChildBnd mref cref w ↔
      (∃ C : RefLawsCore mref cref, C.quiet w) ∧
        readOf sparkleChildSynth w = some synthesizeChild ∧
        (readOf sparkleSynthDepth w = 0 ∨ CacheInv mref cref (readOf sparkleChildCache w)) := by
  constructor
  · intro h
    obtain ⟨L, hsV, hq⟩ := h
    exact ⟨⟨RefLawsCore.ofRefLaws mctx0 cctx0 L, hq⟩,
      readOf_of_startW mctx0 cctx0 (startW_of_startV L hsV)⟩
  · rintro ⟨⟨C, hq⟩, hs, hd⟩
    exact childBnd_of_core C hq hs hd

end Tools.ShippingChildBndCore

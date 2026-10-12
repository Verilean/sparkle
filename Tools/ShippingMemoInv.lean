import Tools.ShippingMemoLaws

/-! # The memo's content invariant — STATEMENTS for the nested hit

`Tools/ShippingLegacySemMemoWalk.lean` removes the memo disjunct at the
OUTERMOST entry by deriving a miss from the reset. A NESTED run does not
start with a reset: a hit there returns what an earlier synthesis of the same
depth-0 run stored. Nothing about that is derived from the reset-miss; it
needs an invariant of what the memo holds.

**The key is the declaration NAME only** (`Sparkle/Compiler/Elab.lean`: the
four writes `sparkleSubModuleCache.modify (·.insert declName result)` at
lines 5272, 5279, 5298, 5363; the read at 5310–5311). It ignores the
parameters, `symbolicMode`, `certifiedFrontEnd`, the translator, the constant
handed over and the instance predicate. So "every entry `n ↦ r` satisfies the
entry theorem's conclusion" is not a well-formed invariant: the conclusion
is about a constant (and, through the mixed gate, an instance predicate), and
a stored entry is about the constant its STORING run was handed. The
invariant below therefore says what is true: an entry satisfies the meaning
`Ψ` for SOME constant and instance predicate (`stored Ψ`).

**Proved here** (generic, from the memo's laws only): the invariant holds of
an empty memo and after the reset (`memoInv_of_empty`, `memoInv_reset`), is
carried by the enumerated frame operations and by the read
(`memoInv_frame`, `memoInv_read`), and is kept by a write of a result that
satisfies the predicate (`memoInv_write`); a hit under the invariant gives
the predicate (`memoInv_hit`).

**NOT proved — statements only**: `ArmObligations` (what each of the four
writing arms has to establish, and that the arms' bodies keep the invariant)
and `MemoSound` (the function keeps the invariant on every outcome). No
theorem in the development uses them. The missing link from `stored Ψ` to the
READER's constant is in `docs/parallel/B-memo.md` §5. -/
namespace Tools.ShippingMemo
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingChildInv
open Sparkle.Compiler.Elab

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- Every entry of the memo in world `w` satisfies `Φ`. -/
def MemoInv (L : RefLawsM mref cref) (Φ : Name → Res → Prop) (w : Void IO.RealWorld) : Prop :=
  ∀ (n : Name) (r : Res), (L.mval w).get? n = some r → Φ n r

theorem memoInv_of_empty (L : RefLawsM mref cref) (Φ : Name → Res → Prop)
    {w : Void IO.RealWorld} (h : L.mval w = {}) : MemoInv L Φ w := by
  intro n r hn
  rw [h] at hn
  rw [get?_empty] at hn
  cases hn

/-- The invariant depends on the memo's map only. -/
theorem memoInv_same (L : RefLawsM mref cref) (Φ : Name → Res → Prop)
    {w w' : Void IO.RealWorld} (h : L.mval w' = L.mval w) (hw : MemoInv L Φ w) :
    MemoInv L Φ w' := by
  intro n r hn
  rw [h] at hn
  exact hw n r hn

/-- The reset establishes the invariant, whatever the memo held. -/
theorem memoInv_reset (L : RefLawsM mref cref) (Φ : Name → Res → Prop)
    {w w' : Void IO.RealWorld} {u : Unit}
    (h : RunsTo (sparkleSubModuleCache.set {} : MetaM Unit) mctx mref cctx cref w u w') :
    MemoInv L Φ w' :=
  memoInv_of_empty L Φ (L.memoSet _ _ _ _ h)

/-- An enumerated frame operation carries the invariant. -/
theorem memoInv_frame (L : RefLawsM mref cref) (Φ : Name → Res → Prop) {α : Type}
    {p : MetaM α} (hp : MemoFrameOp p) {w w' : Void IO.RealWorld} {a : α}
    (h : RunsTo p mctx mref cctx cref w a w') (hw : MemoInv L Φ w) : MemoInv L Φ w' :=
  memoInv_same L Φ (L.memoFrame p hp w a w' h) hw

/-- The read carries the invariant, and what it returns satisfies it. -/
theorem memoInv_read (L : RefLawsM mref cref) (Φ : Name → Res → Prop)
    {w w' : Void IO.RealWorld} {memo : Std.HashMap Name Res}
    (h : RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref w memo w')
    (hw : MemoInv L Φ w) :
    MemoInv L Φ w' ∧ ∀ (n : Name) (r : Res), memo.get? n = some r → Φ n r := by
  obtain ⟨e, hs⟩ := L.memoGet w memo w' h
  refine ⟨memoInv_same L Φ hs hw, ?_⟩
  intro n r hn
  rw [e] at hn
  exact hw n r hn

/-- A hit under the invariant. -/
theorem memoInv_hit (L : RefLawsM mref cref) (Φ : Name → Res → Prop)
    {w : Void IO.RealWorld} {n : Name} {r : Res}
    (hw : MemoInv L Φ w) (h : (L.mval w).get? n = some r) : Φ n r :=
  hw n r h

/-- **A write keeps the invariant if the result written satisfies the
predicate** — the write of each of the four arms is this operation. -/
theorem memoInv_write (L : RefLawsM mref cref) (Φ : Name → Res → Prop)
    {n : Name} {r : Res} {w w' : Void IO.RealWorld} {u : Unit}
    (h : RunsTo (sparkleSubModuleCache.modify (fun x => x.insert n r) : MetaM Unit)
      mctx mref cctx cref w u w')
    (hw : MemoInv L Φ w) (hr : Φ n r) : MemoInv L Φ w' := by
  have hm : L.mval w' = (L.mval w).insert n r := L.memoModify _ _ _ _ h
  intro c' r' h'
  rw [hm] at h'
  rw [Std.HashMap.get?_insert] at h'
  split at h'
  · rename_i heq
    have : n = c' := by simpa using heq
    subst this
    cases h'
    exact hr
  · exact hw c' r' h'

/-! ## Statements only: the meaning of a stored result, and the obligations -/

/-- The meaning of a result: a predicate of the declaration's name, the
constant and the instance predicate the STORING run was handed, and the
result. (For the projection class: "for every binder list, field and leaf
function satisfying the premises of `proj_entry_output` for this constant
and predicate, the module's `out` carries the field's input".) -/
abbrev Meaning : Type :=
  Name → ConstantInfo → (Lean.Expr → Bool) → Res → Prop

/-- What the name-keyed memo can know of an entry: the meaning holds for SOME
constant and instance predicate. -/
def stored (Ψ : Meaning) : Name → Res → Prop :=
  fun n r => ∃ (ci : ConstantInfo) (isInst : Lean.Expr → Bool), Ψ n ci isInst r

/-- `p` keeps a predicate of the memo's content on EVERY outcome (a failed
nested synthesis that a `catch` recovers from has already written its own
children). -/
def KeepsMemo (L : RefLawsM mref cref) (Φ : Name → Res → Prop) {α : Type} (p : MetaM α) :
    Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld),
    MemoInv L Φ w → MemoInv L Φ (endW mctx mref cctx cref p w)

/-- **The preservation obligations, arm by arm** (statements; none is
proved). For the nested configuration — no parameters, not symbolic, the
certified front end on, the real translator, the entry's own logger — which
is the only configuration in which a run of `synthesizeFromConst` is ever
nested (`synthesizeChild` → `synthesizeCombinational`), and also the
shipping entry's.

* `certified`, `mixed`, `machine` — the arm's harness, run from an invariant
  world on a constant its gate accepts, returns a result with the meaning
  and ends in an invariant world (its nested syntheses kept it);
* `machineNone` — the machine arm declining AFTER its harness ran: the
  invariant still holds when the run falls through to the memo's read;
* `legacy` — on a constant the three gates decline, a run that started with
  NO entry under its name (so it compiled) returns a result with the
  meaning. (The legacy arm's body is inline in `synthesizeFromConst`; it has
  no name of its own to state this about.)
* `legacyKeeps` — the same run ends in an invariant world. -/
structure ArmObligations (L : RefLawsM mref cref) (Ψ : Meaning) : Prop where
  certified : ∀ (b : Bool) (n : Name) (ci : ConstantInfo) (isInst : Lean.Expr → Bool)
    (bs : List (Name × GateBinder)) (body : Lean.Expr)
    (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
    certifiedShape? false [] ci = some (bs, body) →
    MemoInv L (stored Ψ) w →
    RunsTo (synthesizeCertified (fun e h t nm => translateExprToWire e h t nm) (profLogIO b)
      n bs body) mctx mref cctx cref w r w' →
    Ψ n ci isInst r ∧ MemoInv L (stored Ψ) w'
  mixed : ∀ (b : Bool) (n : Name) (ci : ConstantInfo) (isInst : Lean.Expr → Bool)
    (bs : List (Name × MixedGateBinder)) (body : Lean.Expr)
    (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
    certifiedShape? false [] ci = none →
    mixedCertifiedShape? false [] ci isInst = some (bs, body) →
    MemoInv L (stored Ψ) w →
    RunsTo (synthesizeMixedCertified (fun e h t nm => translateExprToWire e h t nm)
      (profLogIO b) n bs body) mctx mref cctx cref w r w' →
    Ψ n ci isInst r ∧ MemoInv L (stored Ψ) w'
  machine : ∀ (b : Bool) (n : Name) (ci : ConstantInfo) (isInst : Lean.Expr → Bool)
    (projs : StructEnv) (shape : MachineShape)
    (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
    certifiedShape? false [] ci = none →
    mixedCertifiedShape? false [] ci isInst = none →
    machineShape? false [] ci projs = some shape →
    MemoInv L (stored Ψ) w →
    RunsTo (synthesizeMachineCertified (fun e h t nm => translateExprToWire e h t nm)
      (profLogIO b) n shape) mctx mref cctx cref w (some r) w' →
    Ψ n ci isInst r ∧ MemoInv L (stored Ψ) w'
  machineNone : ∀ (b : Bool) (n : Name) (shape : MachineShape)
    (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld),
    MemoInv L (stored Ψ) w →
    RunsTo (synthesizeMachineCertified (fun e h t nm => translateExprToWire e h t nm)
      (profLogIO b) n shape) mctx mref cctx cref w none w' →
    MemoInv L (stored Ψ) w'
  legacy : ∀ (b : Bool) (n : Name) (ci : ConstantInfo) (isInst : Lean.Expr → Bool)
    (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
    certifiedShape? false [] ci = none →
    mixedCertifiedShape? false [] ci isInst = none →
    (∀ projs : StructEnv, machineShape? false [] ci projs = none) →
    (L.mval w).get? n = none →
    MemoInv L (stored Ψ) w →
    RunsTo (synthesizeFromConst (fun e h t nm => translateExprToWire e h t nm) (profLogIO b)
      n [] false true ci isInst) mctx mref cctx cref w r w' →
    Ψ n ci isInst r
  legacyKeeps : ∀ (b : Bool) (n : Name) (ci : ConstantInfo) (isInst : Lean.Expr → Bool)
    (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
    certifiedShape? false [] ci = none →
    mixedCertifiedShape? false [] ci isInst = none →
    (∀ projs : StructEnv, machineShape? false [] ci projs = none) →
    MemoInv L (stored Ψ) w →
    RunsTo (synthesizeFromConst (fun e h t nm => translateExprToWire e h t nm) (profLogIO b)
      n [] false true ci isInst) mctx mref cctx cref w r w' →
    MemoInv L (stored Ψ) w'

/-- **The invariant's goal** (a statement; not proved): in the nested
configuration `synthesizeFromConst` keeps "every entry has the meaning for
some constant" on every outcome. -/
def MemoSound (L : RefLawsM mref cref) (Ψ : Meaning) : Prop :=
  ∀ (b : Bool) (n : Name) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
    KeepsMemo L (stored Ψ)
      (synthesizeFromConst (fun e h t nm => translateExprToWire e h t nm) (profLogIO b)
        n [] false true ci isInst)

end Tools.ShippingMemo

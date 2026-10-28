import Tools.ShippingChildTranslatePathA
import Tools.ShippingChildCoreC
-- BUILT (unit E, par/u-e, base 0054b6b2): e2 exit 0 (first try); audit e3 exit 0.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field. Law witness:
-- `O : RefLawsAOps MkRefd mref cref` at `hA : AdmCtx O.quiet mctx cctx` only. ShippingChildCacheA /
-- ShippingChildCoreC state their lemmas for a generic boundary predicate `Fresh`; here it is
-- instantiated to `MkRefd` (what DepthA / FallbackA use), so the two families line up without
-- any new law.
-- Writing-time guesses (marked `-- guess: En`):
--  E1 `core0_tripleAC_aux`: a copy of CoreC's `core_tripleAC` outermost branch whose prefix (seven
--     pures, four framed sets) runs under `JQ`/`EQ` (macros `apure`/`aset` of VertA) and the clear
--     `tripleC_clear` (JQ → JQC) is followed by a weakening of the exception class to `EQC`;
--  E2 `subst hd` with `hd : d = D` and `hD0 : D = 0` leaves `hD0 : d = 0`; `h0` by `simp [hD0]`;
--  E3 `childEntryA_of_childKeepsC` copies `childEntryA_of_childKeeps` with `.1` inserted.

/-! # The cache-coherent depth induction (`JQC`)

PROVED here:
* `ChildKeepsC O D` / `BodyKeepsC O D` / `BodyStepC O` (the `JQC` analogues of DepthA's);
* `childKeepsC_of_body`, **`childKeepsC_all`** (induction on `limit - D`), from `core_tripleAC`
  (CoreC) and `synthesizeChild_tripleC'` (CoreC); `childEntryA_of_childKeepsC`;
* the OUTERMOST entry from `JQ` (no cache half): `core0_tripleAC` / `full0_tripleAC`
  — exceptions before the clear are `EQ` (= `JQ ∧ OkExc`: `ioEnv`/`profLog`/`depthGet`/the sets
  run with NO `CacheInvA`), the clear (`tripleC_clear`) establishes `CacheInvA`, from there the
  invariant is `JQC`, and the exception class is weakened `EQC → EQ` at the end;
  `core_tripleAC_of_bodies` / `full_tripleAC_of_bodies` discharge CoreC's `hbodyC` from `BodyStepC`;
* the endpoint `closeInstsM_realC`: a `RealChildA` for every child the run returned, cache hits
  included, from `BodyStepC` alone;
* `bodyStepC_certified` (certified-shape constants, generic-I `fromConst_certified_keepsAP` +
  `translate_keepsA` at `I := JQC O D`) and [removed at integration: `bodyStepC_of_generic`, superseded by ComposeC `bodyStepC_of_tele`] (the body from unit D's generic-I
  front-end lemma, taken as a HYPOTHESIS `hgen`).

NOT proved here (PREMISE/OPEN): `BodyStepC O` itself — the mixed / machine branches await unit D's
restricted FrontA (generic in `I`), the legacy tail (`hlegacy`) and the five handler premises
`LegacyImplA LegacyCachedA CanonKeyA ProjFieldNameA` (at `JQC O D`). `RealChildA` is a HISTORY of
past synthesis results, not semantic correctness in the current environment. -/

namespace Tools.ShippingChildDepthC
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildVertA
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildFallbackA
open Tools.ShippingChildTranslatePathA
open Tools.ShippingChildCacheA
open Tools.ShippingChildCoreC

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## The `JQC` analogues of DepthA's definitions -/

/-- **The memoised child entry at depth `D`** keeps `JQC` in every admissible context. -/
def ChildKeepsC (O : RefLawsAOps MkRefd mref cref) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ c, Keeps mctx mref cctx cref (JQC O D) (synthesizeChild c)

/-- The body at depth `D` keeps `JQC` (every admissible context, declaration and constant). -/
def BodyKeepsC (O : RefLawsAOps MkRefd mref cref) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ (declName : Name) (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo)
      (isInst : Lean.Expr → Bool),
    Keeps mctx mref cctx cref (JQC O D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false true ci isInst)

/-- **The remaining lemma at `JQC`** (PREMISE): at every depth `D ≥ 1` the body keeps `JQC`
given the child entry does at `D`. -/
def BodyStepC (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ D, 1 ≤ D → ChildKeepsC O D → BodyKeepsC O D

/-! ## The depth induction -/

/-- One step: the child entry at `D` from the body at `D + 1`. -/
theorem childKeepsC_of_body (O : RefLawsAOps MkRefd mref cref) (D : Nat)
    (hB : D < sparkleSynthDepthLimit → BodyKeepsC O (D + 1)) : ChildKeepsC O D := by
  intro mctx cctx hA c
  rw [keeps_iff]
  refine Triple.conseq (synthesizeChild_tripleC' O hA (D := D) (n := c) ?_)
    (fun _ h => h) (fun _ _ h => h.2) (fun _ _ h => h)
  intro tenv hl b ci isInst
  exact hB hl mctx cctx hA c tenv b ci isInst

/-- **The depth induction at `JQC`** (on `sparkleSynthDepthLimit - D`). -/
theorem childKeepsC_all (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepC O) :
    ∀ D, 1 ≤ D → ChildKeepsC O D := by
  have key : ∀ k D, sparkleSynthDepthLimit - D = k → 1 ≤ D → ChildKeepsC O D := by
    intro k
    induction k with
    | zero =>
      intro D hk hD
      exact childKeepsC_of_body O D (fun hl => absurd hl (by omega))
    | succ k ih =>
      intro D hk hD
      exact childKeepsC_of_body O D
        (fun _ => hB (D + 1) (by omega) (ih (D + 1) (by omega) (by omega)))
  intro D hD
  exact key _ D rfl hD

/-- The synthesis ref's read under `JQC`: it returns `some synthesizeChild`. -/
theorem tripleC_synthRead (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) :
    Triple mctx mref cctx cref (JQC O D) (sparkleChildSynth.get : MetaM _)
      (fun s w => JQC O D w ∧ s = some synthesizeChild)
      (fun e w => JQC O D w ∧ OkExc e) := by
  intro w hw
  have hK := keeps_iff.mp (keepsA_framed O hA (stableA_JQC O D) FramedA.synthGet) w hw
  cases hm : (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w with
  | ok a w1 =>
    rw [hm] at hK
    exact ⟨hK, (runsTo_get_readOf _ hm).trans hw.1.2.1⟩  -- guess: E3
  | error e w1 => rw [hm] at hK; exact hK

/-- **`ChildEntryA` at `JQC O D` from `ChildKeepsC O D`.** -/
theorem childEntryA_of_childKeepsC (O : RefLawsAOps MkRefd mref cref) (D : Nat)
    (hC : ChildKeepsC O D) : ChildEntryA O (JQC O D) := by
  intro mctx cctx hA c
  rw [keeps_iff]
  unfold childSynthEntry
  refine Triple.bindQ (tripleC_synthRead O hA D) ?_
  intro s hs
  subst hs
  exact keeps_iff.mp (hC mctx cctx hA c)

/-! ## The outermost entry: `JQ` in, `JQC` after the clear -/

/-- **The outermost core entry from `JQ`** (depth `D = 0`, stated with `hD0` so the proof can
copy CoreC's walk): exceptions are `EQ` — raised before the clear, with no `CacheInvA` — or weakened
from `EQC` after it. -/
theorem core0_tripleAC_aux (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) (hD0 : D = 0) (declName : Name)
    (hbodyC : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQC O (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)) :
    Triple mctx mref cctx cref (JQ O.quiet D) (synthesizeCombinationalCore declName [] false)
      (fun _ => JQC O D) (EQ O.quiet D) := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQ _ D) (FramedA.ioEnv _))) ?_
  intro prof
  refine Triple.bind (keeps_iff.mp (keepsA_diag O hA (stableA_JQ _ D)
    (Diag.profLog prof.isSome _))) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = D)
    (Triple.conseq (tripleA_depthGet O hA (stableA_JQ _ D)) (fun _ h => h)
      (Q' := fun d w => JQ O.quiet D w ∧ d = D)
      (fun _ _ h => ⟨h.1, h.2.trans h.1.2.2⟩) (fun _ _ h => h)) ?_
  intro d hd
  subst hd  -- guess: E2
  refine Triple.ite (fun _ => ?_) (fun hlt => ?_)
  · refine Triple.bind (Q := fun _ _ => False)
      (tripleA_throwErr O hA (stableA_JQ _ d) _ (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · have hlt : d < sparkleSynthDepthLimit := Nat.lt_of_not_ge hlt
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (JQC O (d + 1))
          (_root_.tryFinally
            (do
              let constInfo ← getConstInfo declName
              let env ← getEnv
              synthesizeFromConst (fun e h t n => translateExprToWire env e h t n)
                (profLogIO prof.isSome) declName [] false true
                (entryConst true false [] constInfo (instancePredicate env) (userInliner env)
                  (structEnv env))
                (instancePredicate env))
            (do
              ST.Ref.modify sparkleSynthDepth fun x => x - 1
              if (d != 0) = true then do
                  ST.Ref.set sparkleFvarValueMap m1
                  ST.Ref.set sparkleWireWidthCache m2
                  ST.Ref.set sparkleLetWireCache m3
                  ST.Ref.set sparkleLoopWireCache m4
                  ST.Ref.set sparkleWireCanon m5
                  ST.Ref.set sparkleSubInstanceOutputs m6
                  ST.Ref.set sparkleSingleOutInstanceCache m7
                else pure () : MetaM Unit))
          (fun _ => JQC O d) (EQC O d) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine Triple.tryFinally (M := JQC O (d + 1)) (E := OkExc) ?_
        (finC O hA d m1 m2 m3 m4 m5 m6 m7)
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (d + 1))
        (FramedA.constInfo _))) ?_
      intro ci
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (d + 1))
        FramedA.env)) ?_
      intro env
      exact keeps_iff.mp (hbodyC hlt prof.isSome _ _)
    have h0 : (d == 0) = true := by simp [hD0]
    simp only [h0, ↓reduceIte]
    -- before the clear there is no cache half: `JQ`, exceptions `EQ`
    apure O.quiet d; apure O.quiet d; apure O.quiet d; apure O.quiet d; apure O.quiet d
    apure O.quiet d; apure O.quiet d
    aset O hA d; aset O hA d; aset O hA d; aset O hA d
    refine Triple.bind (tripleC_clear O hA d (R := EQ O.quiet d)) ?_
    intro _
    refine Triple.conseq (P := JQC O d) (R := EQC O d) ?_ (fun _ h => h) (fun _ _ h => h)
      (fun _ _ h => ⟨h.1.1, h.2⟩)
    cset O hA d; cset O hA d; cset O hA d; cset O hA d; cset O hA d; cset O hA d; cset O hA d
    refine Triple.bind (tripleC_depthSet O hA d (d + 1)) ?_
    intro _
    exact body _ _ _ _ _ _ _

/-- **The outermost core entry from `JQ O.quiet 0`** (= `OutQ`): success `JQC O 0`, exceptions
`EQ O.quiet 0`. The only premise: `hbodyC` (the body at depth 1 under `JQC`). -/
theorem core0_tripleAC (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (declName : Name)
    (hbodyC : ∀ {tenv : Lean.Environment}, 0 < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQC O 1)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)) :
    Triple mctx mref cctx cref (JQ O.quiet 0) (synthesizeCombinationalCore declName [] false)
      (fun _ => JQC O 0) (EQ O.quiet 0) :=
  core0_tripleAC_aux O hA 0 rfl declName @hbodyC

/-- The full outermost entry: the core, one environment read, pure post-processing. -/
theorem full0_tripleAC (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {declName : Name}
    (hcore : Triple mctx mref cctx cref (JQ O.quiet 0)
      (synthesizeCombinationalCore declName [] false) (fun _ => JQC O 0) (EQ O.quiet 0)) :
    Triple mctx mref cctx cref (JQ O.quiet 0) (synthesizeCombinational declName)
      (fun _ => JQC O 0) (EQ O.quiet 0) := by
  unfold synthesizeCombinational synthesizeCombinationalWith
  refine Triple.bind hcore ?_
  rintro ⟨m, dd⟩
  dsimp only
  refine Triple.bind (Triple.conseq
    (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O 0) (FramedA.ioEnv _)))
    (fun _ h => h) (fun _ _ h => h) (fun _ _ h => ⟨h.1.1, h.2⟩)) ?_
  intro x
  exact Triple.ite (fun _ => Triple.pure fun w hw => hw) (fun _ => Triple.pure fun w hw => hw)

/-! ## Discharging `hbodyC` from `BodyStepC` -/

/-- CoreC's `hbodyC` at depth `D`, for every declaration, from `BodyStepC`. -/
theorem hbodyC_of_step (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepC O)
    (hA : AdmCtx O.quiet mctx cctx) (D : Nat) (c : Name) :
    ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQC O (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          c [] false true ci isInst) :=
  fun {tenv} _ b ci isInst =>
    hB (D + 1) (by omega) (childKeepsC_all O hB (D + 1) (by omega)) mctx cctx hA c tenv b ci isInst

/-- **The outermost core entry from `BodyStepC` alone**: `OutQ`-state in, success `JQC O 0`,
exceptions `EQ O.quiet 0`. -/
theorem core_tripleAC_of_bodies (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (declName : Name) (hB : BodyStepC O) :
    Triple mctx mref cctx cref (JQ O.quiet 0) (synthesizeCombinationalCore declName [] false)
      (fun _ => JQC O 0) (EQ O.quiet 0) :=
  core0_tripleAC O hA declName (hbodyC_of_step O hB hA 0 declName)

/-- **The outermost full entry from `BodyStepC` alone.** -/
theorem full_tripleAC_of_bodies (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (declName : Name) (hB : BodyStepC O) :
    Triple mctx mref cctx cref (JQ O.quiet 0) (synthesizeCombinational declName)
      (fun _ => JQC O 0) (EQ O.quiet 0) :=
  full0_tripleAC O hA (core_tripleAC_of_bodies O hA declName hB)

/-! ## The endpoint: every returned child is a `RealChildA` -/

/-- `synthesizeChild` under `JQC`, cache hit included, from `BodyStepC` alone. -/
theorem synthesizeChild_realC (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepC O)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat} {n : Name}
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O D w)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w') :
    RealChildA O n y ∧ JQC O D w' :=
  synthesizeChild_realA' O hA (hbodyC_of_step O hB hA D n) hw h

/-- **The one-output closing's children, cache hits included, from `BodyStepC` alone.** -/
theorem closeInstsM_realC (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepC O)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat}
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (hw : JQC O D w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) = some (m, d) ∧
      children.length = shape.insts.length ∧
      (∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
        RealChildA O (shape.insts[k]).1 y) ∧
      JQC O D w' :=
  closeInstsM_realA' O hA (fun c => hbodyC_of_step O hB hA D c) hw hr

/-! ## The body at `JQC`: what is proved of `BodyStepC` -/

/-- **Certified-shape constants at `JQC O D`**, from the generic-I `fromConst_certified_keepsAP`
and `translate_keepsA` (NOT the JQ-specific `fromConst_certified_of_handlers`), given the five
handler premises at `JQC O D`; the child entry through `ChildKeepsC O D`. -/
theorem bodyStepC_certified (O : RefLawsAOps MkRefd mref cref) (D : Nat)
    (hImpl : LegacyImplA O (JQC O D)) (hCached : LegacyCachedA O (JQC O D))
    (hcanon : CanonKeyA O (JQC O D)) (hpf : ProjFieldNameA O (JQC O D))
    (hC : ChildKeepsC O D) (mctx : Meta.Context) (cctx : Core.Context)
    (hA : AdmCtx O.quiet mctx cctx) (declName : Name) (tenv : Lean.Environment) (b : Bool)
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool) {bs : List (Name × GateBinder)}
    {body : Lean.Expr} (hshape : certifiedShape? false [] ci = some (bs, body)) :
    Keeps mctx mref cctx cref (JQC O D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false true ci isInst) :=
  fromConst_certified_keepsAP O hA (stableA_JQC O D) _ b declName ci isInst hshape
    (fun e h t n => translate_keepsA O (stableA_JQC O D) tenv hImpl hCached hcanon hpf
      (childEntryA_of_childKeepsC O D hC) mctx cctx hA e h t n)


end Tools.ShippingChildDepthC

import Tools.ShippingChildTranslatePathA
-- NOT BUILT (worker par/tr, base 6a231b89). Isolated: no existing file uses it.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field. Law witness:
-- `O : RefLawsAOps MkRefd mref cref` at `hA : AdmCtx O.quiet mctx cctx` only.
-- `coreN_keepsA` COPIES the built `core_tripleA` (ShippingChildVertA.lean, vt3 exit 0) for a NESTED
-- depth `D ≥ 1`: the same prefix, the depth guard, then the depth-≠0 branches (seven framed reads of
-- the saved maps instead of seven `pure {}`, seven framed resets instead of the twelve-reset clear),
-- the bump to `D + 1`, the body, the `finally` (`finA`, whose `d ≠ 0` branch restores the maps).
-- Writing-time guesses (marked `-- guess: Dn`):
--  D1 `coreN_keepsA`: after `unfold synthesizeCombinationalCoreWith` and
--     `simp only [Bool.false_eq_true, ↓reduceIte]` the goal has core_tripleA's shape (VertA W1);
--  D2 `simp only [h0, Bool.false_eq_true, ↓reduceIte]` with `h0 : (d == 0) = false` selects the
--     `else` of the seven `if depth == 0 then pure {} else ref.get` and of the reset block, and
--     leaves the `finally`'s `(d != 0) = true` test (no `bne` lemma given) — `finA` matches it;
--  D3 `agetJ` (copy of VertA's `aset`): `FramedA.sideGet ?s` with `case s => constructor`;
--  D4 `synthesizeChild_keepsA`: after `unfold` + `dsimp only` the entry is
--     `sparkleChildCache.get >>= fun m => match m.get? n with | some r => pure r | _ => …`;
--  D5 `synthesizeCombinationalWith_keepsA`: `obtain ⟨m, d⟩` + `dsimp only` reduce the
--     `let (m, d) ← …` match and the local `let`s; the env test is `ite` of two `pure`s;
--  D6 `body` (inside `coreN_keepsA`) is stated as in core_tripleA with `d`; `exact body …` passes
--     the seven read maps as `_` (NOT forced: the vt1 OOM).

/-! # The child recursion by depth induction (new boundary)

The translator's instance arm calls the memoised child entry `synthesizeChild`
at the CURRENT depth `D` (`ChildKeepsA O D`, premise of `translate_keepsJQ`).
`synthesizeChild c` at depth `D`: the child-cache read (hit: return), else the
entry `synthesizeCombinational c` — the core entry at depth `D` (nested,
`D ≥ 1`), whose body runs at depth `D + 1` with the translator at `D + 1`,
whose instance arms need `ChildKeepsA O (D + 1)` — then the post-processing and
the child-cache insert. The recursion is bounded by the depth guard
(`sparkleSynthDepthLimit`): at `D ≥ limit` the core throws before the body.

Proved:
* `keepsJ_cacheModify` (the child-cache insert under `JQ`: `O.cacheModify'`,
  `O.frameQ`, `O.cacheSetQ`), `synthesizeChild_keepsA`,
  `synthesizeCombinationalWith_keepsA`;
* `coreN_keepsA`: the NESTED core entry at depth `D ≥ 1` keeps `JQ O.quiet D`,
  given the body at `D + 1` (only needed below the limit);
* `childKeepsA_of_body`: `ChildKeepsA O D` from the body at `D + 1`;
* **`childKeepsA_all`** (the depth induction, on `limit - D`): if at every
  depth `D ≥ 1` the body keeps `JQ O.quiet D` whenever the child entry does at
  `D` (`hB`), then `ChildKeepsA O D` for every `D ≥ 1`;
* `core_tripleA_of_bodies`: `core_tripleA` with its `hbody` discharged from
  `hB` (at depth 1 the child entry comes from `childKeepsA_all`).

**The exact remaining lemma** (`hB`, `BodyStepA O`):
`∀ D, 1 ≤ D → ChildKeepsA O D → BodyKeepsA O D`, i.e. at every depth the body
`synthesizeFromConst (translateExprToWire tenv) …` keeps `JQ O.quiet D` given the
child entry does. What is proved of it: for a constant whose CERTIFIED shape
matches, `fromConst_certified_of_handlers` gives it from the four handler
premises at `JQ O.quiet D` (`LegacyImplA`, `LegacyCachedA`, `CanonKeyA`,
`ProjFieldNameA`) — `bodyStepA_certified` below. OPEN: the mixed branch
(`synthesizeMixedCertified`), the machine branch (`machineShape?`,
`synthesizeMachineCertified`), the legacy tail of `synthesizeFromConst`
(telescopes: `RefLawsATele`), and the four handler premises themselves. -/

namespace Tools.ShippingChildDepthA
open Lean Meta
open Tools.ShippingEntrySoundness
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

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- A read of another per-synthesis ref under `JQ` (a `FramedA.sideGet`). -/
macro "agetJ " O:term:max hA:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsA_framed $O $hA (stableA_JQ _ $D)
      (FramedA.sideGet ?s))) ?_
   case s => constructor
   intro _))

/-! ## The memoised entry and its post-processing -/

/-- The child-cache insert keeps `JQ` (it cannot fail). -/
theorem keepsJ_cacheModify (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) (f : Std.HashMap Name Res → Std.HashMap Name Res) :
    Keeps mctx mref cctx cref (JQ O.quiet D) (ST.Ref.modify sparkleChildCache f : MetaM Unit) :=
  keeps_iff.mpr (Triple.of_runs (refModify_runs _ _) fun w u w' hw h => by
    have hk := O.cacheModify' hA f hw.1 h
    have hq' : O.quiet w' := by
      obtain ⟨w1, hg, hs⟩ := modify_split sparkleChildCache f h
      have hq1 := O.frameQ hA _ FramedA.cacheGet w hw.1
      rw [endW_of_runs hg] at hq1
      exact O.cacheSetQ hA _ _ _ _ hs hq1
    exact ⟨hq', hk.2.1.trans hw.2.1, hk.2.2.trans hw.2.2⟩)

/-- `synthesizeChild`: the cache read, a hit returned, else the entry and the
cache insert. -/
theorem synthesizeChild_keepsA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) (c : Name)
    (hcomb : Keeps mctx mref cctx cref (JQ O.quiet D) (synthesizeCombinational c)) :
    Keeps mctx mref cctx cref (JQ O.quiet D) (synthesizeChild c) := by
  unfold synthesizeChild
  try dsimp only  -- guess: D4
  refine Keeps.bind (keepsA_framed O hA (stableA_JQ _ D) FramedA.cacheGet) (fun _ => ?_)
  split
  · exact Keeps.pure _
  · refine Keeps.bind hcomb (fun _ => ?_)
    refine Keeps.bind (keepsJ_cacheModify O hA D _) (fun _ => ?_)
    exact Keeps.pure _

/-- `synthesizeCombinational`: the core entry, then pure post-processing and
one environment-variable read. -/
theorem synthesizeCombinationalWith_keepsA (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (D : Nat) (c : Name)
    (hcore : Keeps mctx mref cctx cref (JQ O.quiet D)
      (synthesizeCombinationalCoreWith (fun env e h t n => translateExprToWire env e h t n) c [] false)) :
    Keeps mctx mref cctx cref (JQ O.quiet D) (synthesizeCombinational c) := by
  unfold synthesizeCombinational synthesizeCombinationalWith
  refine Keeps.bind hcore (fun p => ?_)
  obtain ⟨m, d⟩ := p
  try dsimp only  -- guess: D5
  refine Keeps.bind (keepsA_framed O hA (stableA_JQ _ D) (FramedA.ioEnv _)) (fun _ => ?_)
  first
    | exact Keeps.ite (fun _ => Keeps.pure _) (fun _ => Keeps.pure _)
    | exact Keeps.pure _

/-! ## The nested core entry -/

/-- **The core entry at a NESTED depth `D ≥ 1`** keeps `JQ O.quiet D` on every
outcome, given the body at `D + 1` (needed only below the depth limit). -/
theorem coreN_keepsA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) (hD : 1 ≤ D) (declName : Name)
    (hbody : D < sparkleSynthDepthLimit → ∀ (tenv : Lean.Environment) (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQ O.quiet (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)) :
    Keeps mctx mref cctx cref (JQ O.quiet D)
      (synthesizeCombinationalCoreWith (fun env e h t n => translateExprToWire env e h t n)
        declName [] false) := by
  rw [keeps_iff]
  unfold synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]  -- guess: D1
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
  refine Triple.ite (fun _ => ?_) (fun hlt => ?_)
  · -- at the limit: the entry throws before touching the depth
    refine Triple.bind (Q := fun _ _ => False)
      (tripleA_throwErr O hA (stableA_JQ _ D) _ (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · have hl : D < sparkleSynthDepthLimit := by omega
    have hd0 : d ≠ 0 := by omega
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (JQ O.quiet (d + 1))
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
          (fun _ => JQ O.quiet d) (EQ O.quiet d) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine Triple.tryFinally (M := JQ O.quiet (d + 1)) (E := OkExc) ?_
        (finA O hA d m1 m2 m3 m4 m5 m6 m7)
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQ _ (d + 1))
        (FramedA.constInfo _))) ?_
      intro ci
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQ _ (d + 1))
        FramedA.env)) ?_
      intro env
      subst hd
      exact keeps_iff.mp (hbody hl env prof.isSome _ _)
    have h0 : (d == 0) = false := by
      first
        | exact beq_false_of_ne hd0
        | simp [hd0]
        | (cases d with
           | zero => exact absurd rfl hd0
           | succ n => rfl)
    simp only [h0, Bool.false_eq_true, ↓reduceIte]  -- guess: D2
    agetJ O hA D; agetJ O hA D; agetJ O hA D; agetJ O hA D; agetJ O hA D  -- guess: D3
    agetJ O hA D; agetJ O hA D
    aset O hA D; aset O hA D; aset O hA D; aset O hA D; aset O hA D; aset O hA D; aset O hA D
    refine Triple.bind (tripleJ_depthSet O hA D (d + 1)) ?_
    intro _
    subst hd
    exact body _ _ _ _ _ _ _  -- guess: D6

/-! ## The depth induction -/

/-- The body at depth `D` (every admissible context, every declaration and
constant): the analogue of `core_tripleA`'s `hbody` at depth `D`. -/
def BodyKeepsA (O : RefLawsAOps MkRefd mref cref) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ (declName : Name) (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo)
      (isInst : Lean.Expr → Bool),
    Keeps mctx mref cctx cref (JQ O.quiet D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false true ci isInst)

/-- **The remaining lemma**: at every depth `D ≥ 1`, the body keeps `JQ` given
the child entry does at `D`. -/
def BodyStepA (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ D, 1 ≤ D → ChildKeepsA O D → BodyKeepsA O D

/-- One step: the child entry at `D ≥ 1` from the body at `D + 1`. -/
theorem childKeepsA_of_body (O : RefLawsAOps MkRefd mref cref) (D : Nat) (hD : 1 ≤ D)
    (hB : D < sparkleSynthDepthLimit → BodyKeepsA O (D + 1)) : ChildKeepsA O D := by
  intro mctx cctx hA c
  refine synthesizeChild_keepsA O hA D c ?_
  refine synthesizeCombinationalWith_keepsA O hA D c ?_
  refine coreN_keepsA O hA D hD c ?_
  intro hl tenv b ci isInst
  exact hB hl mctx cctx hA c tenv b ci isInst

/-- **The depth induction** (on `sparkleSynthDepthLimit - D`): from the
remaining lemma, the child entry keeps `JQ` at every depth `D ≥ 1`. -/
theorem childKeepsA_all (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepA O) :
    ∀ D, 1 ≤ D → ChildKeepsA O D := by
  have key : ∀ k D, sparkleSynthDepthLimit - D = k → 1 ≤ D → ChildKeepsA O D := by
    intro k
    induction k with
    | zero =>
      intro D hk hD
      exact childKeepsA_of_body O D hD (fun hl => absurd hl (by omega))
    | succ k ih =>
      intro D hk hD
      exact childKeepsA_of_body O D hD
        (fun _ => hB (D + 1) (by omega) (ih (D + 1) (by omega) (by omega)))
  intro D hD
  exact key _ D rfl hD

/-- **`core_tripleA` with its `hbody` discharged from the remaining lemma.** -/
theorem core_tripleA_of_bodies (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (declName : Name) (hB : BodyStepA O) :
    Triple mctx mref cctx cref (OutQ O.quiet) (synthesizeCombinationalCore declName [] false)
      (fun _ => OutQ O.quiet) (fun e w => OutQ O.quiet w ∧ OkExc e) := by
  refine core_tripleA O hA declName ?_
  intro tenv b ci isInst
  exact hB 1 (Nat.le_refl 1) (childKeepsA_all O hB 1 (Nat.le_refl 1)) mctx cctx hA declName tenv b
    ci isInst

/-- **What is proved of the remaining lemma**: its certified-shape instances,
from the four handler premises at `JQ O.quiet D`. -/
theorem bodyStepA_certified (O : RefLawsAOps MkRefd mref cref) (D : Nat)
    (hImpl : LegacyImplA O (JQ O.quiet D)) (hCached : LegacyCachedA O (JQ O.quiet D))
    (hcanon : CanonKeyA O (JQ O.quiet D)) (hpf : ProjFieldNameA O (JQ O.quiet D))
    (hC : ChildKeepsA O D) (mctx : Meta.Context) (cctx : Core.Context)
    (hA : AdmCtx O.quiet mctx cctx) (declName : Name) (tenv : Lean.Environment) (b : Bool)
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool) {bs : List (Name × GateBinder)}
    {body : Lean.Expr} (hshape : certifiedShape? false [] ci = some (bs, body)) :
    Keeps mctx mref cctx cref (JQ O.quiet D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false true ci isInst) :=
  fromConst_certified_of_handlers O hA D declName tenv b ci isInst hshape hImpl hCached hcanon
    hpf hC

end Tools.ShippingChildDepthA

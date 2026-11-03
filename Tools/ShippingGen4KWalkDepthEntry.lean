import Tools.ShippingGen4KWalkDepthArms
import Tools.ShippingGen4KWalkEnv
-- NOT BUILT. S6 (depth induction, part 3) of scripts/gen4/KWALK_PLAN.md (frozen in scripts/gen4/KWALK_S6_FREEZE.md): the entry of a NESTED run, `synthesizeCombinationalWith` and `synthesizeChild` at a
-- PINNED depth (`KWD O K D = KW O K ∧ dv = D`): a nested run gives the depth back; the entry throws at `D ≥ sparkleSynthDepthLimit`.
-- The arm `hbody` is asked only for `D < sparkleSynthDepthLimit`, at depth `D + 1`. Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. DIAG-PENDING hypothesis `LogMvK`.
-- No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkDepthEntry
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4KWalkEntry
open Tools.ShippingGen4KWalkEntryCore
open Tools.ShippingGen4KWalkDepth

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option hygiene false in
macro "kgetD" : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O MemoKeysInChild D)
      (FramedNM.sideGet ?s))) ?_
   case s => constructor
   intro _))
set_option hygiene false in
macro "ksetD" : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O MemoKeysInChild D)
      (FramedNM.sideSet _ ?s))) ?_
   case s => constructor
   intro _))

section Entry
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
include M hA

/-- **The entry for a nested run at depth `D ≠ 0`**: from `KWD K D` to `KWD K_n D` (a failure leaves `KWD K D`). The body (`hbody`) is
asked at depth `D + 1`, and only when `D < sparkleSynthDepthLimit` (the entry throws otherwise). -/
theorem entryNested_windowD (hlog : LogMvK O) (translate : Lean.Environment → TranslateFn) (declName : Name)
    (D : Nat) (hD : D ≠ 0)
    (hbody : D < sparkleSynthDepthLimit → ∀ (b : Bool) (env : Lean.Environment) (ci : ConstantInfo)
        (isInst : Lean.Expr → Bool),
      Triple mctx mref cctx cref (KWD O MemoKeysInChild (D + 1))
        (synthesizeFromConst (translate env) (profLogIO b) declName [] false true ci isInst)
        (fun _ => KWD O (MemoKeysExc declName) (D + 1)) (fun e w => KWD O MemoKeysInChild (D + 1) w ∧ OkExc e)) :
    Triple mctx mref cctx cref (KWD O MemoKeysInChild D)
      (synthesizeCombinationalCoreWith translate declName [] false true)
      (fun _ => KWD O (MemoKeysExc declName) D) (fun e w => KWD O MemoKeysInChild D w ∧ OkExc e) := by
  unfold synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O MemoKeysInChild D) (FramedNM.ioEnv _))) ?_
  intro prof
  refine Triple.bind (keeps_iff.mp (keepsK_profLog M hA (stableK_KWD O MemoKeysInChild D) hlog prof.isSome _)) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = D) (tripleK_depthGetD M hA MemoKeysInChild D) ?_
  intro d hd
  subst d
  refine Triple.ite (fun hc => ?_) (fun hc => ?_)
  · refine Triple.bind (Q := fun _ _ => False)
      (tripleK_throwErr M hA (stableK_KWD O MemoKeysInChild D) _
        (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · have hlt : D < sparkleSynthDepthLimit := Nat.not_le.mp hc
    have h0 : (D == 0) = false := by simpa using hD
    simp only [h0, Bool.false_eq_true, ↓reduceIte]
    kgetD; kgetD; kgetD; kgetD; kgetD; kgetD; kgetD
    ksetD; ksetD; ksetD; ksetD; ksetD; ksetD; ksetD
    refine Triple.bind (triple_depthSetD M hA MemoKeysInChild D (D + 1)) ?_
    intro _
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (KWD O MemoKeysInChild (D + 1))
          (_root_.tryFinally
            (do
              let constInfo ← getConstInfo declName
              let env ← getEnv
              synthesizeFromConst (translate env) (profLogIO prof.isSome) declName [] false true
                (entryConst true false [] constInfo (instancePredicate env) (userInliner env)
                  (structEnv env))
                (instancePredicate env))
            (do
              ST.Ref.modify sparkleSynthDepth fun x => x - 1
              if (D != 0) = true then do
                  ST.Ref.set sparkleFvarValueMap m1
                  ST.Ref.set sparkleWireWidthCache m2
                  ST.Ref.set sparkleLetWireCache m3
                  ST.Ref.set sparkleLoopWireCache m4
                  ST.Ref.set sparkleWireCanon m5
                  ST.Ref.set sparkleSubInstanceOutputs m6
                  ST.Ref.set sparkleSingleOutInstanceCache m7
                else pure () : MetaM Unit))
          (fun _ => KWD O (MemoKeysExc declName) D) (fun e w => KWD O MemoKeysInChild D w ∧ OkExc e) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine tryFinallySplit2 (Mo := KWD O (MemoKeysExc declName) (D + 1)) (Me := KWD O MemoKeysInChild (D + 1))
        (E := OkExc) ?_
        (fin_totalD M hA (MemoKeysExc declName) D m1 m2 m3 m4 m5 m6 m7)
        (fin_totalD M hA MemoKeysInChild D m1 m2 m3 m4 m5 m6 m7)
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O MemoKeysInChild (D + 1))
        (FramedNM.constInfo _))) ?_
      intro ci
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O MemoKeysInChild (D + 1))
        FramedNM.env)) ?_
      intro env
      exact hbody hlt prof.isSome env _ _
    exact body _ _ _ _ _ _ _

/-- `synthesizeCombinationalWith` for a nested run at depth `D`: the entry, the `IO.getEnv`, the pure post-processing. -/
theorem combWith_nestedD (hlog : LogMvK O) (translate : Lean.Environment → TranslateFn) (declName : Name)
    (D : Nat) (hD : D ≠ 0)
    (hbody : D < sparkleSynthDepthLimit → ∀ (b : Bool) (env : Lean.Environment) (ci : ConstantInfo)
        (isInst : Lean.Expr → Bool),
      Triple mctx mref cctx cref (KWD O MemoKeysInChild (D + 1))
        (synthesizeFromConst (translate env) (profLogIO b) declName [] false true ci isInst)
        (fun _ => KWD O (MemoKeysExc declName) (D + 1)) (fun e w => KWD O MemoKeysInChild (D + 1) w ∧ OkExc e)) :
    Triple mctx mref cctx cref (KWD O MemoKeysInChild D)
      (synthesizeCombinationalWith translate declName)
      (fun _ => KWD O (MemoKeysExc declName) D) (fun e w => KWD O MemoKeysInChild D w ∧ OkExc e) := by
  unfold synthesizeCombinationalWith
  refine Triple.bind (entryNested_windowD M hA hlog translate declName D hD hbody) ?_
  rintro ⟨m, d⟩
  dsimp only
  refine Triple.bind (triple_framedNM_totalD M hA (MemoKeysExc declName) D (FramedNM.ioEnv _)
    (fun w => Tools.ShippingGen4KWalkEnv.ioEnv_runs _ w)) ?_
  intro x
  exact Triple.ite (fun _ => Triple.pure fun w hw => hw) (fun _ => Triple.pure fun w hw => hw)

/-- **`synthesizeChild` at depth `D`: the window is closed.** From the entry for a nested run (`hcomb`), the memoised child entry
returns in `KWD K D` and fails in `KWD K D`. -/
theorem synthesizeChild_windowD (D : Nat)
    (hcomb : ∀ n, Triple mctx mref cctx cref (KWD O MemoKeysInChild D) (synthesizeCombinational n)
      (fun _ => KWD O (MemoKeysExc n) D) (fun e w => KWD O MemoKeysInChild D w ∧ OkExc e)) (n : Name) :
    Triple mctx mref cctx cref (KWD O MemoKeysInChild D) (synthesizeChild n)
      (fun _ => KWD O MemoKeysInChild D) (fun e w => KWD O MemoKeysInChild D w ∧ OkExc e) := by
  unfold synthesizeChild
  refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O MemoKeysInChild D) FramedNM.cacheGet)) ?_
  intro cache
  split
  · exact Triple.pure fun w hw => hw
  · refine Triple.bind (hcomb n) ?_
    intro r
    refine Triple.bind (triple_childInsertD M hA D n r) ?_
    intro _
    exact Triple.pure fun w hw => hw

end Entry

end Tools.ShippingGen4KWalkDepthEntry

#print axioms Tools.ShippingGen4KWalkDepthEntry.entryNested_windowD
#print axioms Tools.ShippingGen4KWalkDepthEntry.combWith_nestedD
#print axioms Tools.ShippingGen4KWalkDepthEntry.synthesizeChild_windowD

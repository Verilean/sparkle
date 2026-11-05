import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4KWalkEntry
import Tools.ShippingGen4FKidsEntry
import Tools.ShippingGen4FKidsDepth
import Tools.ShippingGen4FKidsEntryArms
import Tools.ShippingGen4FKidsDepthArms
import Tools.ShippingGen4KWalkDepthEntry
import Tools.ShippingGen4FKidsEntryCore
namespace Tools.ShippingGen4FKidsDepthEntry
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
open Tools.ShippingChildFrontA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4KWalkEntry
open Tools.ShippingGen4FKidsEntry

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele

open Tools.ShippingGen4KWalkDepth
open Tools.Assume.FramedACases
open Tools.ShippingGen4FKidsDepth
open Tools.ShippingGen4FKidsEntryArms

open Tools.ShippingGen4FKidsDepthArms
open Tools.ShippingGen4KWalkEntryCore
open Tools.ShippingGen4KWalkDepth
open Tools.ShippingGen4KWalkDepthEntry
open Tools.ShippingGen4FKidsEntryCore

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

theorem dropZero_pf (m : Sparkle.IR.AST.Module) : (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).parameters = m.parameters := by
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
  dsimp only
  split <;> rfl
theorem mergeDup_pf (m : Sparkle.IR.AST.Module) : (Sparkle.IR.RegDedup.mergeDuplicates m).parameters = m.parameters := by
  unfold Sparkle.IR.RegDedup.mergeDuplicates Sparkle.IR.RegDedup.mergeDuplicatesRaw
  dsimp only
  split
  · split <;> rfl
  · rfl
theorem mergeChecked_pf (m : Sparkle.IR.AST.Module) : (Sparkle.IR.RefineCheck.mergeChecked m).parameters = m.parameters := by
  rcases Sparkle.IR.RefineCheck.mergeChecked_cases m with h | h
  · rw [h]; exact mergeDup_pf m
  · rw [h]
theorem designPF_top (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) (hf : ∀ x, ParamFree x → ParamFree (f x)) {d : Sparkle.IR.AST.Design} (m : Sparkle.IR.AST.Module)
    (hd : DesignPF d) :
    DesignPF { d with modules := d.modules.map fun x => if x.name == m.name then f x else x } := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  split
  · exact hf y (hd y hy)
  · exact hd y hy

/-- `try x finally fin`, with a different post-condition for each of the two `fin` runs (after a return, after a throw). -/
theorem tryFinallySplit2Q {α β : Type} {P Me Me' : Void IO.RealWorld → Prop} {Q1 Q2 : α → Void IO.RealWorld → Prop} {E : Exception → Prop}
    {x : MetaM α} {fin : MetaM β}
    (hx : Triple mctx mref cctx cref P x Q1 (fun e w => Me w ∧ E e))
    (hfo : ∀ a, Triple mctx mref cctx cref (Q1 a) fin (fun _ => Q2 a) (fun _ _ => False))
    (hfe : Triple mctx mref cctx cref Me fin (fun _ => Me') (fun _ _ => False)) :
    Triple mctx mref cctx cref P (_root_.tryFinally x fin) Q2 (fun e w => Me' w ∧ E e) := by
  intro w hw
  have h1 := hx w hw
  change match (EST.bind (@MonadFinally.tryFinally' (EST Exception IO.RealWorld) _ _ _
      (x mctx mref cctx cref) (fun _ => fin mctx mref cctx cref)) (fun p => EST.pure p.1)) w with
    | .ok a w' => Q2 a w' | .error e w' => Me' w' ∧ E e
  unfold EST.bind
  simp only [MonadFinally.tryFinally']
  cases hxw : x mctx mref cctx cref w with
  | ok a w1 =>
    rw [hxw] at h1
    have h2 := hfo a w1 h1
    dsimp only
    cases hfw : fin mctx mref cctx cref w1 with
    | ok b w2 => rw [hfw] at h2; simpa [EST.pure] using h2
    | error e' w2 => rw [hfw] at h2; exact h2.elim
  | error e w1 =>
    rw [hxw] at h1
    have h2 := hfe w1 h1.1
    dsimp only
    cases hfw : fin mctx mref cctx cref w1 with
    | ok b w2 => rw [hfw] at h2; simpa [EST.pure] using ⟨h2, h1.2⟩
    | error e' w2 => rw [hfw] at h2; exact h2.elim


set_option hygiene false in
macro "kgetDP" : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O PPF D)
      (FramedNM.sideGet ?s))) ?_
   case s => constructor
   intro _))
set_option hygiene false in
macro "ksetDP" : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O PPF D)
      (FramedNM.sideSet _ ?s))) ?_
   case s => constructor
   intro _))

section Entry
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
include M hA

/-- **The entry for a nested run at depth `D ≠ 0`**: from `KWD K D` to `KWD K_n D` (a failure leaves `KWD K D`). The body (`hbody`) is
asked at depth `D + 1`, and only when `D < sparkleSynthDepthLimit` (the entry throws otherwise). -/
theorem entryNested_windowDP (hlog : LogMvKS O) (translate : Lean.Environment → TranslateFn) (declName : Name)
    (D : Nat) (hD : D ≠ 0)
    (hbody : D < sparkleSynthDepthLimit → ∀ (b : Bool) (env : Lean.Environment) (ci : ConstantInfo)
        (isInst : Lean.Expr → Bool),
      Triple mctx mref cctx cref (WPF O (D + 1))
        (synthesizeFromConst (translate env) (profLogIO b) declName [] false true ci isInst)
        (fun r w => WPFX O declName (D + 1) w ∧ PairPF r) (fun e w => WPF O (D + 1) w ∧ OkExc e)) :
    Triple mctx mref cctx cref (WPF O D)
      (synthesizeCombinationalCoreWith translate declName [] false true)
      (fun r w => WPFX O declName D w ∧ PairPF r) (fun e w => WPF O D w ∧ OkExc e) := by
  unfold synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O PPF D) (FramedNM.ioEnv _))) ?_
  intro prof
  refine Triple.bind (keeps_iff.mp (keepsK_profLogS M hA (stableK_KWD O PPF D) hlog prof.isSome _)) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = D) (tripleK_depthGetD M hA PPF D) ?_
  intro d hd
  subst d
  refine Triple.ite (fun hc => ?_) (fun hc => ?_)
  · refine Triple.bind (Q := fun _ _ => False)
      (tripleK_throwErr M hA (stableK_KWD O PPF D) _
        (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · have hlt : D < sparkleSynthDepthLimit := Nat.not_le.mp hc
    have h0 : (D == 0) = false := by simpa using hD
    simp only [h0, Bool.false_eq_true, ↓reduceIte]
    kgetDP; kgetDP; kgetDP; kgetDP; kgetDP; kgetDP; kgetDP
    ksetDP; ksetDP; ksetDP; ksetDP; ksetDP; ksetDP; ksetDP
    refine Triple.bind (triple_depthSetD M hA PPF D (D + 1)) ?_
    intro _
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (WPF O (D + 1))
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
          (fun r w => WPFX O declName D w ∧ PairPF r) (fun e w => WPF O D w ∧ OkExc e) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine tryFinallySplit2Q (Q1 := fun r w => WPFX O declName (D + 1) w ∧ PairPF r)
        (Q2 := fun r w => WPFX O declName D w ∧ PairPF r) (Me := WPF O (D + 1)) (E := OkExc) ?_
        (fun a => triple_constConj (PairPF a) (fin_totalD M hA (PPFX declName) D m1 m2 m3 m4 m5 m6 m7))
        (fin_totalD M hA PPF D m1 m2 m3 m4 m5 m6 m7)
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O PPF (D + 1))
        (FramedNM.constInfo _))) ?_
      intro ci
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KWD O PPF (D + 1))
        FramedNM.env)) ?_
      intro env
      exact hbody hlt prof.isSome env _ _
    exact body _ _ _ _ _ _ _


/-- `synthesizeCombinationalWith` for a nested run at depth `D`: the entry, the `IO.getEnv`, the pure post-processing
(`dropZeroWidthModule`, `mergeChecked`), which keep `ParamFree`. -/
theorem combWith_nestedDP (hlog : LogMvKS O) (translate : Lean.Environment → TranslateFn) (declName : Name)
    (D : Nat) (hD : D ≠ 0)
    (hbody : D < sparkleSynthDepthLimit → ∀ (b : Bool) (env : Lean.Environment) (ci : ConstantInfo)
        (isInst : Lean.Expr → Bool),
      Triple mctx mref cctx cref (WPF O (D + 1))
        (synthesizeFromConst (translate env) (profLogIO b) declName [] false true ci isInst)
        (fun r w => WPFX O declName (D + 1) w ∧ PairPF r) (fun e w => WPF O (D + 1) w ∧ OkExc e)) :
    Triple mctx mref cctx cref (WPF O D)
      (synthesizeCombinationalWith translate declName)
      (fun r w => WPFX O declName D w ∧ PairPF r) (fun e w => WPF O D w ∧ OkExc e) := by
  unfold synthesizeCombinationalWith
  refine Triple.bindQ (P' := WPFX O declName D) (φ := PairPF) (entryNested_windowDP M hA hlog translate declName D hD hbody) ?_
  rintro ⟨m, d⟩ hp
  dsimp only
  refine Triple.bind (triple_framedNM_totalD M hA (PPFX declName) D (FramedNM.ioEnv _)
    (fun w => Tools.ShippingGen4KWalkEnv.ioEnv_runs _ w)) ?_
  intro x
  have hdz : ∀ x, ParamFree x → ParamFree (Sparkle.IR.ZeroWidth.dropZeroWidthModule x) := fun x hx => by
    unfold ParamFree at *; rw [dropZero_pf]; exact hx
  have hmc : ∀ x, ParamFree x → ParamFree (Sparkle.IR.RefineCheck.mergeChecked x) := fun x hx => by
    unfold ParamFree at *; rw [mergeChecked_pf]; exact hx
  have hm1 : ParamFree (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) := hdz m hp.1
  have hd1 := designPF_top _ hdz m hp.2
  exact Triple.ite (fun _ => Triple.pure fun w hw => ⟨hw, hm1, hd1⟩)
    (fun _ => Triple.pure fun w hw => ⟨hw, hmc _ hm1, designPF_top _ hmc m hd1⟩)

/-- The child-cache read, under the PF world: returns the child cache itself. -/
theorem tripleK_cacheGetD (D : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (WPF O D) (sparkleChildCache.get : MetaM (Std.HashMap Name Res))
      (fun c w => WPF O D w ∧ c = cv w) R :=
  Triple.of_runs (refGet_runs _) fun w a w' hw h => by
    have hK := keepsK_framedNM M hA (stableK_KWD O PPF D) FramedNM.cacheGet w hw
    have hp : FramedA MkRefd (sparkleChildCache.get : MetaM (Std.HashMap Name Res)) := FramedA.cacheGet
    obtain ⟨_, hc, _, _⟩ := framedA_ctx hA hp hw.1.1
    rw [endW_of_runs h] at hK hc
    have ha : a = cv w := runsTo_get_readOf _ h
    exact ⟨hK.1, ha.trans hc.symm⟩

/-- **`synthesizeChild` at depth `D`: the window is closed, and the result is `PairPF`.** A child-cache hit hands back a
`PairPF` pair (`CachePF` of the child cache); a miss runs the entry (`hcomb`) and records its `PairPF` result. -/
theorem synthesizeChild_windowDP (D : Nat)
    (hcomb : ∀ n, Triple mctx mref cctx cref (WPF O D) (synthesizeCombinational n)
      (fun r w => WPFX O n D w ∧ PairPF r) (fun e w => WPF O D w ∧ OkExc e)) (n : Name) :
    Triple mctx mref cctx cref (WPF O D) (synthesizeChild n)
      (fun r w => WPF O D w ∧ PairPF r) (fun e w => WPF O D w ∧ OkExc e) := by
  unfold synthesizeChild
  refine Triple.bind (tripleK_cacheGetD M hA D) ?_
  intro cache
  split
  · next r heq =>
    exact Triple.pure fun w hw => ⟨hw.1, hw.1.1.2.2.2.2 n r (by rw [hw.2] at heq; exact heq)⟩
  · refine Triple.bindQ (P' := WPFX O n D) (φ := PairPF)
      (Triple.conseq (hcomb n) (fun w hw => hw.1) (fun _ _ h => h) (fun _ _ h => h)) ?_
    intro r hr
    refine Triple.bind (triple_childInsertDP M hA D n r hr) ?_
    intro _
    exact Triple.pure fun w hw => ⟨hw, hr⟩

end Entry

end Tools.ShippingGen4FKidsDepthEntry

#print axioms Tools.ShippingGen4FKidsDepthEntry.entryNested_windowDP
#print axioms Tools.ShippingGen4FKidsDepthEntry.combWith_nestedDP
#print axioms Tools.ShippingGen4FKidsDepthEntry.synthesizeChild_windowDP

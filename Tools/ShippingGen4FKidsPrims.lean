import Tools.ShippingGen4FKidsCalc
import Tools.ShippingGen4KWalkPrims
set_option autoImplicit false
-- F-kids StatePF walk, part 2: the circuit-state primitives for `KeepsCS` (copies of Tools/ShippingGen4KWalkPrims.lean and
-- ShippingChildTranslateA.lean, with the state tracked). Takes `MemoFamily` as a HYPOTHESIS `M`; adds no premise. No sorry.

namespace Tools.ShippingGen4FKidsPrims
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Sparkle.IR.Builder (CircuitState)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- an operation that keeps the view relates the state it was run on to the state it produced -/
theorem good_of_eq {α : Type} {f : CircuitState → α × CircuitState} {cs cs' : CircuitState} {a : α}
    (h : f cs = (a, cs')) (hs : StatePF cs) (hf : ∀ c, View (f c).2 = View c) : GoodS cs cs' := by
  refine GoodS.of_view hs ?_
  have := hf cs
  rw [h] at this
  exact this

macro "good_tac" : tactic => `(tactic| (refine good_of_eq ‹_› ‹_› (fun c => ?_) <;>
  first
  | with_reducible exact view_makeWire c _ _ _
  | with_reducible exact view_freshName c _ _
  | with_reducible exact view_emitAssign c _ _
  | with_reducible exact view_addInput c _ _
  | with_reducible exact view_addOutput c _ _
  | with_reducible exact view_emitRegister c _ _ _ _ _ _ _ _
  | with_reducible exact view_emitRegisterStmt c _ _ _ _ _ _
  | with_reducible exact view_emitMemory c _ _ _ _ _ _ _ _ _
  | with_reducible exact view_emitMemoryComboRead c _ _ _ _ _ _ _ _ _
  | with_reducible exact view_emitInstance c _ _ _
  | with_reducible exact view_bindSourceVariable c _ _))

section Prims
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I)
include M hA hS

theorem wireWidthKS (f : Std.HashMap String Nat → Std.HashMap String Nat) :
    Keeps mctx mref cctx cref I (ST.Ref.modify sparkleWireWidthCache f : MetaM Unit) :=
  keepsK_framedNM M hA hS (FramedNM.sideModify _ .wireWidth)

theorem makeWirePS (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    KeepsCS mctx mref cctx cref I (CompilerM.makeWire hint ty named) := by
  intro st
  unfold CompilerM.makeWire
  refine KCS.bindGet ?_
  split
  next name cs' heq =>
    refine KCS.bind (KCS.set _ (fun _ => by good_tac)) (fun _ st' _ => ?_)
    dsimp only
    split
    · exact KCS.bind (KCS.lift (wireWidthKS M hA hS _)) (fun _ _ _ => KCS.pure _)
    · exact KCS.pure _

theorem addInputPS (name : String) (ty : Sparkle.IR.Type.HWType) :
    KeepsCS mctx mref cctx cref I (CompilerM.addInput name ty) := by
  intro st
  unfold CompilerM.addInput
  refine KCS.bindGet ?_
  split
  next u cs' heq =>
    refine KCS.bind (KCS.set _ (fun _ => by good_tac)) (fun _ st' _ => ?_)
    split
    · exact KCS.lift (wireWidthKS M hA hS _)
    · exact KCS.pure _

theorem addOutputPS (name : String) (ty : Sparkle.IR.Type.HWType) :
    KeepsCS mctx mref cctx cref I (CompilerM.addOutput name ty) := by
  intro st
  unfold CompilerM.addOutput
  refine KCS.bindGet ?_
  split
  next u cs' heq =>
    refine KCS.bind (KCS.set _ (fun _ => by good_tac)) (fun _ st' _ => ?_)
    split
    · exact KCS.lift (wireWidthKS M hA hS _)
    · exact KCS.pure _

theorem emitRegisterPS (hint clk rst : String) (input : Sparkle.IR.AST.Expr) (initVal : Nat)
    (ty : Sparkle.IR.Type.HWType) (named : Bool) (rk : Sparkle.IR.Type.ResetKind) :
    KeepsCS mctx mref cctx cref I (CompilerM.emitRegister hint clk rst input initVal ty named rk) := by
  intro st
  unfold CompilerM.emitRegister
  refine KCS.bindGet ?_
  split
  next name cs' heq =>
    refine KCS.bind (KCS.set _ (fun _ => by good_tac)) (fun _ st' _ => ?_)
    dsimp only
    split
    · exact KCS.bind (KCS.lift (wireWidthKS M hA hS _)) (fun _ _ _ => KCS.pure _)
    · exact KCS.pure _

theorem emitMemoryPS (hint : String) (aw dw : Nat) (clk : String)
    (wa wd we ra : Sparkle.IR.AST.Expr) (named : Bool) :
    KeepsCS mctx mref cctx cref I (CompilerM.emitMemory hint aw dw clk wa wd we ra named) := by
  intro st
  unfold CompilerM.emitMemory
  refine KCS.bindGet ?_
  split
  next name cs' heq =>
    refine KCS.bind (KCS.set _ (fun _ => by good_tac)) (fun _ st' _ => ?_)
    exact KCS.bind (KCS.lift (wireWidthKS M hA hS _)) (fun _ _ _ => KCS.pure _)

omit M hA hS in
theorem freshNamePS (hint : String) (named : Bool) :
    KeepsCS mctx mref cctx cref I (CompilerM.freshName hint named) := by
  intro st
  unfold CompilerM.freshName
  refine KCS.bindGet ?_
  split
  next name cs' heq =>
    refine KCS.bind (KCS.set _ (fun _ => by good_tac)) (fun _ st' _ => ?_)
    exact KCS.pure _

omit M hA hS in
theorem emitAssignPS (lhs : String) (rhs : Sparkle.IR.AST.Expr) :
    KeepsCS mctx mref cctx cref I (CompilerM.emitAssign lhs rhs) := by
  intro st
  unfold CompilerM.emitAssign
  refine KCS.bindGet ?_
  split
  next u cs' heq =>
    exact KCS.set _ (fun _ => by good_tac)

omit M hA hS in
theorem emitRegisterStmtPS (out clk rst : String) (input : Sparkle.IR.AST.Expr) (initVal : Nat)
    (rk : Sparkle.IR.Type.ResetKind) :
    KeepsCS mctx mref cctx cref I (CompilerM.emitRegisterStmt out clk rst input initVal rk) := by
  intro st
  unfold CompilerM.emitRegisterStmt
  refine KCS.bindGet ?_
  split
  next u cs' heq =>
    exact KCS.set _ (fun _ => by good_tac)

omit M hA hS in
theorem emitInstancePS (mn instName : String) (conns : List (String × Sparkle.IR.AST.Expr)) :
    KeepsCS mctx mref cctx cref I (CompilerM.emitInstance mn instName conns) := by
  intro st
  unfold CompilerM.emitInstance
  refine KCS.bindGet ?_
  split
  next u cs' heq =>
    exact KCS.set _ (fun _ => by good_tac)

omit M hA hS in
/-- the one operation that adds a module to the design: the module must be `ParamFree` -/
theorem addModuleToDesignPS (m : Sparkle.IR.AST.Module) (hm : ParamFree m) :
    KeepsCS mctx mref cctx cref I (CompilerM.addModuleToDesign m) := by
  intro st
  unfold CompilerM.addModuleToDesign
  refine KCS.bindGet ?_
  split
  next u cs' heq =>
    refine KCS.set _ (fun hs => ?_)
    have h1 : cs'.design = st.design.addModule m := by
      have := design_addModuleToDesign st m
      rw [heq] at this
      exact this
    have h2 : cs'.module.parameters = st.module.parameters := by
      have := params_addModuleToDesign st m
      rw [heq] at this
      exact this
    refine ⟨hs, ?_, by rw [h2]⟩
    unfold StatePF
    rw [h1]
    exact designPF_addModule hs hm

omit M hA hS in
theorem lookupVarPS (id : FVarId) : KeepsCS mctx mref cctx cref I (CompilerM.lookupVar id) := by
  intro st ctx _ hs
  unfold CompilerM.lookupVar
  exact Triple.pure (a := Sparkle.IR.Builder.CircuitM.lookupSourceBinding (ctx.varMap.lookup id) id.name st)
    (fun _ hw => ⟨hw, GoodS.refl hs⟩)

omit M hA hS in
theorem bindSourceVariablePS (id : FVarId) (w : String) :
    KeepsCS mctx mref cctx cref I (CompilerM.bindSourceVariable id w) := by
  intro st ctx _ hs
  unfold CompilerM.bindSourceVariable
  exact Triple.pure (a := Sparkle.IR.Builder.CircuitM.bindSourceVariable id.name w st)
    (fun _ hw => ⟨hw, GoodS.of_view hs rfl⟩)

theorem cacheLookupValidatedKS (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (cacheLookupValidated e) := by
  intro st
  unfold cacheLookupValidated
  refine KCS.bindCtx (fun cs hcs => ?_)
  try dsimp only
  cases hc : cs.exprCache with
  | none => exact KCS.pure _
  | some r =>
    have hr := hcs r hc
    refine KCS.bind (KCS.lift ?_) (fun hit st' _ => ?_)
    · first
        | exact Keeps.bind (keepsK_framedNM M hA hS (FramedNM.exprCacheGetIO r hr)) fun _ => Keeps.pure _
        | exact Keeps.bind (keepsK_framedNM M hA hS (FramedNM.exprCacheGet r hr)) fun _ => Keeps.pure _
    · cases hit with
      | none => exact KCS.pure _
      | some w =>
        refine KCS.bindGet ?_
        split <;> exact KCS.pure _

theorem recordTranslationKS (e : Lean.Expr) (w : String) (cacheable : Bool) :
    KeepsCS mctx mref cctx cref I (recordTranslation e w cacheable) := by
  intro st
  unfold recordTranslation
  refine KCS.bind (KCS.modify _ (fun hs => GoodS.of_view hs rfl)) (fun _ st' _ => ?_)
  refine KCS.ite (fun _ => ?_) (fun _ => KCS.pure _)
  refine KCS.bindCtx (fun cs hcs => ?_)
  try dsimp only
  cases hc : cs.exprCache with
  | none => exact KCS.pure _
  | some r => exact KCS.lift (keepsK_framedNM M hA hS (FramedNM.exprCacheModify r _ (hcs r hc)))

end Prims

end Tools.ShippingGen4FKidsPrims

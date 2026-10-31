import Tools.ShippingShapeDecomp
import Tools.ShippingGen5RunReads
import Tools.ShippingGen5ReadKinds
set_option autoImplicit false
-- Built: kjob lake build Tests.Gen5.ReadKindsU5Check exit 0 (756 jobs) in pod on 6e343e997fdbf0ce8cff741ce57f7de45cc68790 (not a clean issue-linked build; that is the coder's). No sorry / axiom / native_decide.

/-! # DG-READKINDS U5: `RootFactsAt` (existence) as a corollary of the peel

`RootFactsAt E` quantifies `entryBody` existentially; it follows from the peel with `entryBody := rootFloat b0`
(`float` by `rfl`; no unfolding of the `partial` `rootFloat`, no `readMachine` run). `RootFactsTie E body` ties `E` to an
EXTERNALLY fixed `body`; it is NOT supplied here (nor `hentry`, nor `hq`). Not a real-run tie, coverage, or FG. -/
namespace Tools.ShippingGen5ReadKindsU5
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingShapeDecomp Tools.ShippingGen5ReadKinds
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Tools.ShippingChildRunA

/-- EXISTENCE version. entryBody is existential. -/
def RootFactsAt (E : Lean.ConstantInfo) : Prop :=
  ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (entryBody₀ entryBody : Lean.Expr),
    E.value? = some entryV ∧ RootFacts entryV bsIn entryBody₀ entryBody

/-- TIE to an externally fixed body. -/
def RootFactsTie (E : Lean.ConstantInfo) (entryBody : Lean.Expr) : Prop :=
  ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (entryBody₀ : Lean.Expr),
    E.value? = some entryV ∧ RootFacts entryV bsIn entryBody₀ entryBody

theorem peel_of_machineShape {sym : Bool} {params : List (String × Nat)} {ci : Lean.ConstantInfo}
    {senv : Sparkle.Compiler.Elab.StructEnv} {allow : Bool} {sp : MachineShape}
    (h : Sparkle.Compiler.Elab.machineShape? sym params ci senv allow = some sp) :
    ∃ (d : Lean.DefinitionVal) (bs : List (Lean.Name × MixedGateBinder)) (e : Lean.Expr),
      ci = .defnInfo d ∧ ci.value? = some d.value ∧
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) := by
  cases ci with
  | defnInfo d =>
    obtain ⟨bs, e, _, _, _, _, _, _, hd⟩ := machineShape?_decomp h
    exact ⟨d, bs, e, rfl, rfl, hd.peel⟩
  | axiomInfo _ => simp [machineShape?] at h
  | thmInfo _ => simp [machineShape?] at h
  | opaqueInfo _ => simp [machineShape?] at h
  | quotInfo _ => simp [machineShape?] at h
  | inductInfo _ => simp [machineShape?] at h
  | ctorInfo _ => simp [machineShape?] at h
  | recInfo _ => simp [machineShape?] at h

theorem rootFacts_of_peel {entryV : Lean.Expr} {bsIn : List (Lean.Name × MixedGateBinder)}
    {entryBody₀ : Lean.Expr}
    (h : mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, entryBody₀)) :
    RootFacts entryV bsIn entryBody₀ (Sparkle.Compiler.MachRawSurface.rootFloat entryBody₀) :=
  ⟨h, rfl⟩

theorem rootFactsAt_of_machineShape {sym : Bool} {params : List (String × Nat)} {ci : Lean.ConstantInfo}
    {senv : Sparkle.Compiler.Elab.StructEnv} {allow : Bool} {sp : MachineShape}
    (h : Sparkle.Compiler.Elab.machineShape? sym params ci senv allow = some sp) :
    RootFactsAt ci := by
  obtain ⟨d, bs, e, _, hv, hp⟩ := peel_of_machineShape h
  exact ⟨d.value, bs, e, _, hv, rootFacts_of_peel hp⟩

theorem rootFactsAt_of_runReads
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {X : Lean.Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    {b : Bool} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    {w5 w6 : Void IO.RealWorld}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6) :
    RootFactsAt (Sparkle.Compiler.Elab.entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
      (Sparkle.Compiler.Elab.userInliner envR) (Sparkle.Compiler.Elab.structEnv envR)) :=
  rootFactsAt_of_machineShape R.shapeEq

theorem rootFacts_unique {entryV : Lean.Expr} {bsIn bsIn' : List (Lean.Name × MixedGateBinder)}
    {b₀ b₀' b b' : Lean.Expr}
    (h : RootFacts entryV bsIn b₀ b) (h' : RootFacts entryV bsIn' b₀' b') :
    bsIn = bsIn' ∧ b₀ = b₀' ∧ b = b' := by
  have e := Option.some.inj (h.pack.symm.trans h'.pack)
  have e1 : bsIn = bsIn' := congrArg Prod.fst e
  have e2 : b₀ = b₀' := congrArg Prod.snd e
  exact ⟨e1, e2, by rw [h.float, h'.float, e2]⟩

theorem rootFactsTie_unique {E : Lean.ConstantInfo} {b b' : Lean.Expr}
    (h : RootFactsTie E b) (h' : RootFactsTie E b') : b = b' := by
  obtain ⟨v, bs, b0, hv, hf⟩ := h
  obtain ⟨v', bs', b0', hv', hf'⟩ := h'
  have : v = v' := Option.some.inj (hv.symm.trans hv')
  subst this
  exact (rootFacts_unique hf hf').2.2

theorem rootFactsAt_iff_tie {E : Lean.ConstantInfo} :
    RootFactsAt E ↔ ∃ body : Lean.Expr, RootFactsTie E body :=
  ⟨fun ⟨v, bs, b0, body, hv, hf⟩ => ⟨body, v, bs, b0, hv, hf⟩,
   fun ⟨body, v, bs, b0, hv, hf⟩ => ⟨v, bs, b0, body, hv, hf⟩⟩

end Tools.ShippingGen5ReadKindsU5

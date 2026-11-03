import Tools.Assume.MemoFamily
-- BUILT: kjob lake build Tools.Assume.FramedACases exit 0 (313 jobs, rt163); axioms standard only. Clean build is the coder's. Pure lemma, takes NO `MemoFamily` hypothesis: classifies `FramedA` (scripts/gen4/MEMO_FAMILY_FREEZE.md
-- section 2.2, MEMO_FAMILY_PROPOSAL section 2). `MemoAccess` / `MemoRef` are defined here (new, not part of the frozen family).
-- No `sorry`, no `axiom`, no `native_decide`, no new law.

namespace Tools.Assume.FramedACases
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildInvA
open Tools.Assume.MemoFamily

/-- The memo cell, as a reference. -/
inductive MemoRef : {σ : Type} → IO.Ref σ → Prop
  | memo : MemoRef sparkleSubModuleCache

/-- A direct access (get / set / modify / modifyGet, in `MetaM` or lifted from `IO`) of the memo cell. -/
inductive MemoAccess : {α : Type} → MetaM α → Prop
  | get : MemoAccess (ST.Ref.get sparkleSubModuleCache : MetaM _)
  | set (v : Std.HashMap Name Res) : MemoAccess (ST.Ref.set sparkleSubModuleCache v : MetaM Unit)
  | modify (f : Std.HashMap Name Res → Std.HashMap Name Res) :
      MemoAccess (ST.Ref.modify sparkleSubModuleCache f : MetaM Unit)
  | modifyGet {β : Type} (f : Std.HashMap Name Res → β × Std.HashMap Name Res) :
      MemoAccess (ST.Ref.modifyGet sparkleSubModuleCache f : MetaM β)
  | modifyGetIO {β : Type} (f : Std.HashMap Name Res → β × Std.HashMap Name Res) :
      MemoAccess (liftM (ST.Ref.modifyGet sparkleSubModuleCache f : IO β) : MetaM β)
  | getIO : MemoAccess (liftM (ST.Ref.get sparkleSubModuleCache : IO (Std.HashMap Name Res)) : MetaM _)
  | setIO (v : Std.HashMap Name Res) :
      MemoAccess (liftM (ST.Ref.set sparkleSubModuleCache v : IO Unit) : MetaM Unit)
  | modifyIO (f : Std.HashMap Name Res → Std.HashMap Name Res) :
      MemoAccess (liftM (ST.Ref.modify sparkleSubModuleCache f : IO Unit) : MetaM Unit)

theorem sideRef_cases {σ : Type} {r : IO.Ref σ} (h : SideRef r) : SideRefNM r ∨ MemoRef r := by
  cases h <;> first | exact Or.inl (by constructor) | exact Or.inr (by constructor)

theorem framedA_cases {Fresh : (σ : Type) → IO.Ref σ → Prop} {α : Type} {p : MetaM α}
    (h : FramedA Fresh p) : FramedNM Fresh p ∨ MemoAccess p := by
  cases h
  case cacheGet => exact Or.inl (by apply FramedNM.cacheGet <;> assumption)
  case synthGet => exact Or.inl (by apply FramedNM.synthGet <;> assumption)
  case depthGet => exact Or.inl (by apply FramedNM.depthGet <;> assumption)
  case sideGet =>
    rcases sideRef_cases ‹SideRef _› with h1 | h1
    · exact Or.inl (by apply FramedNM.sideGet; exact h1)
    · cases h1; exact Or.inr (by apply MemoAccess.get)
  case sideSet =>
    rcases sideRef_cases ‹SideRef _› with h1 | h1
    · exact Or.inl (by apply FramedNM.sideSet; exact h1)
    · cases h1; exact Or.inr (by apply MemoAccess.set)
  case sideModify =>
    rcases sideRef_cases ‹SideRef _› with h1 | h1
    · exact Or.inl (by apply FramedNM.sideModify; exact h1)
    · cases h1; exact Or.inr (by apply MemoAccess.modify)
  case sideModifyGet =>
    rcases sideRef_cases ‹SideRef _› with h1 | h1
    · exact Or.inl (by apply FramedNM.sideModifyGet; exact h1)
    · cases h1; exact Or.inr (by apply MemoAccess.modifyGet)
  case sideModifyGetIO =>
    rcases sideRef_cases ‹SideRef _› with h1 | h1
    · exact Or.inl (by apply FramedNM.sideModifyGetIO; exact h1)
    · cases h1; exact Or.inr (by apply MemoAccess.modifyGetIO)
  case sideGetIO =>
    rcases sideRef_cases ‹SideRef _› with h1 | h1
    · exact Or.inl (by apply FramedNM.sideGetIO; exact h1)
    · cases h1; exact Or.inr (by apply MemoAccess.getIO)
  case sideSetIO =>
    rcases sideRef_cases ‹SideRef _› with h1 | h1
    · exact Or.inl (by apply FramedNM.sideSetIO; exact h1)
    · cases h1; exact Or.inr (by apply MemoAccess.setIO)
  case sideModifyIO =>
    rcases sideRef_cases ‹SideRef _› with h1 | h1
    · exact Or.inl (by apply FramedNM.sideModifyIO; exact h1)
    · cases h1; exact Or.inr (by apply MemoAccess.modifyIO)
  case ioEnv => exact Or.inl (by apply FramedNM.ioEnv <;> assumption)
  case constInfo => exact Or.inl (by apply FramedNM.constInfo <;> assumption)
  case env => exact Or.inl (by apply FramedNM.env <;> assumption)
  case fvarThrowUnknown => exact Or.inl (by apply FramedNM.fvarThrowUnknown <;> assumption)
  case whnf => exact Or.inl (by apply FramedNM.whnf <;> assumption)
  case inferType => exact Or.inl (by apply FramedNM.inferType <;> assumption)
  case isClass? => exact Or.inl (by apply FramedNM.isClass? <;> assumption)
  case whnfUntil => exact Or.inl (by apply FramedNM.whnfUntil <;> assumption)
  case instantiateForall => exact Or.inl (by apply FramedNM.instantiateForall <;> assumption)
  case mkLambdaFVars => exact Or.inl (by apply FramedNM.mkLambdaFVars <;> assumption)
  case mkAppM => exact Or.inl (by apply FramedNM.mkAppM <;> assumption)
  case unfoldDefinition? => exact Or.inl (by apply FramedNM.unfoldDefinition? <;> assumption)
  case reduce => exact Or.inl (by apply FramedNM.reduce <;> assumption)
  case metaGet => exact Or.inl (by apply FramedNM.metaGet <;> assumption)
  case coreModifyTrace => exact Or.inl (by apply FramedNM.coreModifyTrace <;> assumption)
  case metaModify => exact Or.inl (by apply FramedNM.metaModify <;> assumption)
  case freshFVar => exact Or.inl (by apply FramedNM.freshFVar <;> assumption)
  case monoMs => exact Or.inl (by apply FramedNM.monoMs <;> assumption)
  case mkExprCache => exact Or.inl (by apply FramedNM.mkExprCache <;> assumption)
  case exprCacheGet => exact Or.inl (by apply FramedNM.exprCacheGet <;> assumption)
  case exprCacheGetIO => exact Or.inl (by apply FramedNM.exprCacheGetIO <;> assumption)
  case localMk => exact Or.inl (by apply FramedNM.localMk <;> assumption)
  case localGet => exact Or.inl (by apply FramedNM.localGet <;> assumption)
  case localSet => exact Or.inl (by apply FramedNM.localSet <;> assumption)
  case localModify => exact Or.inl (by apply FramedNM.localModify <;> assumption)
  case localGetIO => exact Or.inl (by apply FramedNM.localGetIO <;> assumption)
  case localSetIO => exact Or.inl (by apply FramedNM.localSetIO <;> assumption)
  case localModifyIO => exact Or.inl (by apply FramedNM.localModifyIO <;> assumption)
  case exprCacheModify => exact Or.inl (by apply FramedNM.exprCacheModify <;> assumption)

#print axioms sideRef_cases
#print axioms framedA_cases

end Tools.Assume.FramedACases

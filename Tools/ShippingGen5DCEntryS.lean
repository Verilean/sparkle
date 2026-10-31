import Tools.ShippingGen5DCEntryR
import Tools.ShippingChildServe
set_option autoImplicit false
-- NOT BUILT: U-NORAW, scripts/gen5/DC_CONNECT_NORAW_FREEZE.md §3 (freeze 7a6cb5af approved). Issue-linked clean build dc19v-716d342b exit 0 (750 jobs); approved at 716d342b as a conditional supply unit (not FG).

/-! # DC-CONNECT U-NORAW: `NoRawBelow` from the closing's acyclicity facts

CONDITIONAL on a `closeInsts` / `closeInstsG` equation. Does NOT link a given core run's `(raw, D)` to that equation, does not transport
the run (a2.4c), does not supply `EntryWitness`/`ReflectsAll`, does not adopt `Post`, is not FG. -/

namespace Tools.ShippingGen5DCEntryS

theorem noRawBelow_of_noInstOf {D : Sparkle.IR.AST.Design} {rn : String}
    (hD : ∀ g ∈ D.modules, Tools.ShippingHierMono.NoInstOf rn g.body) :
    ∀ (n : Nat) (mc : Sparkle.IR.AST.Module),
      Tools.ShippingHierMono.NoInstOf rn mc.body → Tools.ShippingGen5DCEntryR.NoRawBelow D rn n mc := by
  intro n
  induction n with
  | zero => intro mc _; exact trivial
  | succ k ih =>
    intro mc hmc
    refine ⟨hmc, ?_⟩
    intro mn iname conns mc' _ hl
    have hmem : mc' ∈ D.modules := List.mem_of_find?_eq_some hl
    exact ih mc' (hD mc' hmem)

theorem noRawBelow_of_closeInsts {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : List (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    {m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)) :
    ∀ k : Nat, Tools.ShippingGen5DCEntryR.NoRawBelow d m.name k m := by
  obtain ⟨-, h1, h2, -⟩ := Tools.ShippingChildServe.closeInsts_acyclic h
  exact fun k => noRawBelow_of_noInstOf h2 k m h1

theorem noRawBelow_of_closeInstsG {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {fields : List String}
    {children : List (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    {m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : Sparkle.IR.Machine.closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d)) :
    ∀ k : Nat, Tools.ShippingGen5DCEntryR.NoRawBelow d m.name k m := by
  obtain ⟨-, h1, h2⟩ := Tools.ShippingChildServe.closeInstsG_acyclic h
  exact fun k => noRawBelow_of_noInstOf h2 k m h1

end Tools.ShippingGen5DCEntryS

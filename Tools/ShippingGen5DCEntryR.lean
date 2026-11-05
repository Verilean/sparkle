import Tools.ShippingGen5DCEntryN
import Tools.ShippingMachineShipsDepth
set_option autoImplicit false
-- NOT BUILT: U-RESETN, scripts/gen5/DC_CONNECT_RESETN_FREEZE.md §3 (freeze 4ccaa035 approved; wording fixes 6c0c96c4). Issue-linked clean build dc17v-1c948e47 exit 0 (749 jobs); approved at 1c948e47 as a conditional transport unit (not FG).

/-! # DC-CONNECT U-RESETN: conditional `ResetNk` transport `D → D'`

CONDITIONAL on `NoRawBelow`, a STRONG sufficient condition (every instance statement of the module has `mn ≠ rn`, also one whose
lookup in `D` fails). Nothing in this tree derives it for compiler output (this investigation found no route). Does NOT transport the
run (a2.4c), does not give `TopShips` on `D'`, does not supply `EntryWitness`/`ReflectsAll`, does not adopt `Post`, is not FG. -/

namespace Tools.ShippingGen5DCEntryR

def NoRawBelow (D : Sparkle.IR.AST.Design) (rn : String) : Nat → Sparkle.IR.AST.Module → Prop
  | 0, _ => True
  | k + 1, mc =>
    (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body → mn ≠ rn) ∧
    (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) (mc' : Sparkle.IR.AST.Module),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body →
        Sparkle.IR.Machine.moduleByName D.modules mn = some mc' → NoRawBelow D rn k mc')

theorem resetN_transport {D D' : Sparkle.IR.AST.Design} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn) :
    ∀ (n : Nat) (mc : Sparkle.IR.AST.Module) (s : Tools.ShippingHierStateG.KT n),
      NoRawBelow D rn n mc →
      (Tools.ShippingMachineDepth.ResetN D n mc s ↔ Tools.ShippingMachineDepth.ResetN D' n mc s) := by
  intro n
  induction n with
  | zero =>
    intro mc s _
    unfold Tools.ShippingMachineDepth.ResetN
    exact Iff.rfl
  | succ k ih =>
    intro mc s hno
    obtain ⟨hnm, hrec⟩ := hno
    unfold Tools.ShippingMachineDepth.ResetN
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
    refine forall_congr' fun mn => forall_congr' fun iname => forall_congr' fun conns => forall_congr' fun mc' => ?_
    constructor
    · intro H hmem hl
      rw [hlk mn (hnm mn iname conns hmem)] at hl
      exact (ih mc' _ (hrec mn iname conns mc' hmem hl)).1 (H hmem hl)
    · intro H hmem hl
      have hl' : Sparkle.IR.Machine.moduleByName D'.modules mn = some mc' := by
        rw [hlk mn (hnm mn iname conns hmem)]; exact hl
      exact (ih mc' _ (hrec mn iname conns mc' hmem hl)).2 (H hmem hl')

theorem resetNk_transport {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design}
    (h : Tools.ShippingGen5DCEntryD.PostEntry b raw D D') (n : Nat)
    (kids : String → Tools.ShippingHierStateG.KT n)
    (hno : NoRawBelow D raw.name (n + 1) raw) :
    Tools.ShippingMachineShipsDepth.ResetNk n raw D kids ↔ Tools.ShippingMachineShipsDepth.ResetNk n raw D' kids := by
  obtain ⟨hnm, hrec⟩ := hno
  have hlk : ∀ mn : String, mn ≠ raw.name →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn :=
    fun mn hne => (Tools.ShippingGen5DCEntryN.postEntry_lookup_ne h hne).1
  unfold Tools.ShippingMachineShipsDepth.ResetNk
  refine forall_congr' fun iname => forall_congr' fun mc => ?_
  constructor
  · rintro H ⟨conns, hmem⟩ hl
    have hne := hnm mc.name iname conns hmem
    rw [hlk mc.name hne] at hl
    exact (resetN_transport hlk n mc _ (hrec mc.name iname conns mc hmem hl)).1 (H ⟨conns, hmem⟩ hl)
  · rintro H ⟨conns, hmem⟩ hl
    have hne := hnm mc.name iname conns hmem
    have hl' : Sparkle.IR.Machine.moduleByName D'.modules mc.name = some mc := by
      rw [hlk mc.name hne]; exact hl
    exact (resetN_transport hlk n mc _ (hrec mc.name iname conns mc hmem hl)).2 (H ⟨conns, hmem⟩ hl')

end Tools.ShippingGen5DCEntryR

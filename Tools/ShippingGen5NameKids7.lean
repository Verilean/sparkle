import Tools.ShippingGen5NameKids3
set_option autoImplicit false
-- NOT BUILT. 1 theorem, 0 new definitions. Written against freeze BOUNDARY_AUDIT_FREEZE_U7.md §2 + §5.
-- Conditional on `hg : GraphAgrees g (OrdPath g top) S`; no instance of `hg` is constructed, so this is NOT evidence of non-vacuity. The production Reach / GraphAgrees / hnd / hr / hfo / ReachSpans / FG are unsupplied.
-- No sorry / axiom / native_decide.

/-! # BOUNDARY-AUDIT U7: `ReachClosed (OrdPath g top) S` from `GraphAgrees`

Under `hg`, closure and the identity `ReachSpans g top (OrdPath g top)` hold for the same set. -/

namespace Tools.ShippingGen5NameKids7
open Lean (Name)
open Sparkle.Compiler.Elab (MachineShape)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingSrm7Rank (CallGraph callees)
open Tools.ShippingMemCloses (memKey)
open Tools.ShippingInstTagged (originAt instTagged_getElem)
open Tools.ShippingGen5NameKids3 (GraphAgrees ReachClosed OrdPath OrdEdge)

theorem reachClosed_ordPath {g : CallGraph} {top : Name} {S : Name → Option MachineShape}
    (hg : GraphAgrees g (OrdPath g top) S) :
    ReachClosed (OrdPath g top) S := by
  intro c hc sp hS k hk hch
  have hgc : callees g c = some sp.instTagged := by rw [hg c hc, hS]; rfl
  have hk' : k < sp.instTagged.length := by simpa [MachineShape.instTagged] using hk
  have hmem : ((sp.insts[k]'hk).1, originAt sp k) ∈ sp.instTagged := by
    rw [← instTagged_getElem sp hk']
    exact List.getElem_mem hk'
  have hm : memKey (originAt sp k) = none := by
    change (originAt sp k).child? = none at hch
    generalize originAt sp k = o at hch ⊢
    cases o with
    | ord => rfl
    | field i => rfl
    | mem cb aw dw => simp [InstOrigin.child?] at hch
  exact OrdPath.step hc ⟨sp.instTagged, originAt sp k, hgc, hmem, hm⟩

end Tools.ShippingGen5NameKids7

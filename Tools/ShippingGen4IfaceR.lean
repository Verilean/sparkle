import Tools.ShippingGen2Defs
set_option autoImplicit false
-- NOT BUILT. U-GC0 (scripts/gen2/GATE_GC0_FREEZE.md): transfer of kjob/g4gate-g6 to base 15cd9d1f. No sorry / axiom / native_decide.

/-! # M4 gate supply, U-G1: the route-agnostic CHILD interface (scripts/gen4/GATE_SUPPLY_FREEZE.md rev1 §3.0)

`ChildIface` is the four things `ChildShips` reads from a `Pkg`; `ChildShipsI` / `ShipsResI` are `ChildShips` / `ShipsRes`
with the package replaced by the record; `Pkgs.iface` and the equivalence lemmas connect them. Definitions and
compatibility lemmas only: no route semantics is supplied, and the Top side (`TopIface`, U-G1T), `GateLeaf`, `ifaceOf`
(uses the noncomputable `gateS`) and the §3.3 theorems are NOT here. The new file does not edit any shared definition. -/

namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildInv (Res)
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth

variable {ι : Type} {dom : ι → DomainConfig}

structure ChildIface (ι : Type) where
  decl  : Name
  bsC   : List (Name × MixedGateBinder)
  outsC : List OutField
  S     : ι → (Nat → List Nat) → List (Nat → Nat)

def ChildIface.ports (I : ChildIface ι) : List (Name × MixedGateBinder) :=
  I.bsC.filter fun b => b.2 != .domain

noncomputable def ChildIface.ofPkg (q : Pkg ι dom) : ChildIface ι :=
  ⟨q.decl, q.d.bsIn.take q.kD, q.d.shape.layout.outs, q.S⟩

theorem ChildIface.ports_ofPkg (q : Pkg ι dom) : (ChildIface.ofPkg q).ports = q.ports := rfl

/-- The S3 port-width conjunct at the interface record (moved here from the old GatePortW). -/
def ChildPortWidthsI (I : ChildIface ι) (mc : Sparkle.IR.AST.Module) : Prop :=
  (Tools.ShippingMachineCompose.argPorts mc).map (fun p => p.ty.bitWidth) =
    I.ports.map (fun b => (Tools.ShippingMachineEntry.kindTy b.2).bitWidth)

theorem childPortWidthsI_ofPkg (q : Pkg ι dom) (mc : Sparkle.IR.AST.Module) :
    ChildPortWidthsI (ChildIface.ofPkg q) mc ↔ ChildPortWidths q mc :=
  Iff.rfl

def ChildShipsI (I : ChildIface ι) (n : Nat) (mc : Sparkle.IR.AST.Module) (Dc : Design) : Prop :=
  ChildPortWidthsI I mc ∧
  ∀ (dsn : Design), (∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g) →
    moduleByName dsn.modules mc.name = some mc →
    ∀ (i : ι), ChildRunN (childMap dsn.modules) dsn n mc I.bsC I.outsC (I.S i)

theorem childShipsI_ofPkg (q : Pkg ι dom) (n : Nat) (mc : Sparkle.IR.AST.Module) (Dc : Design) :
    ChildShipsI (ChildIface.ofPkg q) n mc Dc ↔ ChildShips q n mc Dc := Iff.rfl

abbrev IfaceMap (ι : Type) := Name → Option (ChildIface ι)

noncomputable def Pkgs.iface (P : Pkgs ι dom) : IfaceMap ι := fun c => (P c).map ChildIface.ofPkg

def ShipsResI {mref cref} (L : Laws mref cref) (Q : IfaceMap ι) (c : Name) (r : Res) : Prop :=
  RealChildA L.O c r ∧ (∃ (I : ChildIface ι) (n : Nat), Q c = some I ∧ I.decl = c ∧ ChildShipsI I n r.1 r.2) ∧
    InstClosed r

theorem shipsResI_iface {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (c : Name) (r : Res) :
    ShipsResI L P.iface c r ↔ ShipsRes L P c r := by
  unfold ShipsResI ShipsRes Pkgs.iface
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  constructor
  · rintro ⟨I, n, h, hd, hs⟩
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨q, n, hq, hd, hs⟩
  · rintro ⟨q, n, hq, hd, hs⟩
    exact ⟨ChildIface.ofPkg q, n, by simp [hq], hd, hs⟩

end Tools.ShippingGen2

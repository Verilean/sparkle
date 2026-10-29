import Tools.ShippingGen2CallDec
import Tools.ShippingSrm4Core6
set_option autoImplicit false

/-! # M2-a C5: the output-width premise `hkidW` of `core_runFacts_ranAM` for memory entries
(scripts/gen2/MEMPARENT_FREEZE.md rev1; its hypothesis is the `MemOrigin` shape of the proposed amendment A4, §7) -/
namespace Tools.ShippingGen2
open Lean hiding Module Expr
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMachineEntry (kindTy)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingChildInv (Res)
open Sparkle.Compiler.MachMemory (memModule)

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **C5**: for entries with a memory origin whose declared result binder is `.bits dw`, the kid's output `out` has
the binder's width. -/
theorem hkidW_of_memOrigin (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (d : MachineData) (nDecl : Nat) (hco : d.callsOk nDecl = true)
    (hmem : ∀ (k : Nat) (hk : k < d.shape.insts.length), ∃ (cb : Bool) (aw dw : Nat),
      (originAt d.shape k).child? = some (memModule cb aw dw) ∧
      ((d.bsIn.drop nDecl)[k]?.map (·.2)) = some (.bits dw)) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some p.ty.bitWidth := by
  intro k hk y hy p hp _
  obtain ⟨cb, aw, dw, ho, hb⟩ := hmem k hk
  have hy' : y = memModule cb aw dw := Tools.ShippingSrm4Core6.KidTA.mem' hy ho
  subst hy'
  have hpo : p = ⟨"out", .bitVector dw⟩ := by
    simpa [memModule] using hp
  subst hpo
  have hnIn := callsOk_nIn d nDecl hco
  have hlt : nDecl + k < d.nIn := by omega
  have hdrop : (d.bsIn.drop nDecl)[k]? = d.shape.binders[nDecl + k]? := by
    rw [List.getElem?_drop]
    unfold Tools.ShippingMachineAuto.MachineData.bsIn
    rw [List.getElem?_take_of_lt hlt]
  rw [hdrop] at hb
  cases hbn : d.shape.binders[nDecl + k]? with
  | none => rw [hbn] at hb; cases hb
  | some bn =>
    rw [hbn] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    simp [hb, kindTy, Sparkle.IR.Type.HWType.bitWidth]

/-- `MemOrigin` from `MemDec` when the index type is inhabited (for `ι = Unit` the case premise is redundant). -/
theorem memOrigin_of_memDec {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} [Nonempty ι]
    (p : SrcPkg ι dom) (h : ∀ (k : Nat) (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1) :
    ∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ (cb : Bool) (aw dw : Nat),
      (originAt p.d.shape k).child? = some (memModule cb aw dw) ∧
      ((p.d.bsIn.drop p.kD)[k]?.map (·.2)) = some (.bits dw) := by
  intro k hk
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨cb, aw, dw, A, Dd, E, R, l0, l1, l2, l3, ho, -, -, -, -, -, -, -, -, -, hb, -⟩ :=
    h k hk i (fun _ => Sparkle.Core.Signal.Signal.pure false) (fun _ n => Sparkle.Core.Signal.Signal.pure 0)
  exact ⟨cb, aw, dw, ho, hb⟩

end Tools.ShippingGen2

import Tools.ShippingChildCacheA
import Tools.ShippingCallWidthsChildReal
-- BUILT (unit K, par/u-k): k2 exit 0 (Tools.ShippingChildLinkA); audit k3 exit 0 (Tests.Compiler.ChildVertAuditTest:
-- no RefLaws/RefLawsCore/toAOps/toA in the closure; axioms propext, Classical.choice, Quot.sound).
-- No `sorry`, no `axiom`, no `native_decide`, no new law.
-- Scope: the conclusion is EXISTENCE of the callee's machine shape and result kind only
-- (`machineShape? … = some sc`, `machResultKind? … = some res`); it says nothing about the MEANING
-- of the recorded result `y` or of its ports.
/-! # `childLink_real` on `RealChildA` (L6/L7 of docs/parallel/main-theorem-connection.md)

The old `childLink_real` takes `RealChild mref cref c y` and uses ONLY the run of the callee:
`hy.inv` gives the run, `synthesizeCombinational_parts` the core run, and the two READS of that
core run (`getConstInfo c`, `getEnv`) are what `link_of_defines` / `resC_entry` consume.
The old proof extracted those reads with `core_reads_inv L` (needs an old `RefLaws` witness `L`),
but the reads are also given by the LAW-FREE `synthesizeCombinationalCore_reads`
(ShippingEntrySoundness) from the core run alone. So the minimal read witness is exactly that
lemma's output, it needs no premise, and `childLink_realA` takes `RealChildA O c y` and nothing
beyond the old premises `MachineDefines`, `ResDeclAt`, `P5At` (kept unchanged).

Honesty: `RealChildA` is a HISTORY of a past synthesis run (some admissible context, some
quiet world); the link it gives is to the entry constant of THAT run, read there. No claim that
this is the current environment. Conditional connection only; not runtime fit. -/
namespace Tools.ShippingChildLinkA
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingCallWidthsEntry
open Tools.ShippingCallWidthsChildReal

variable {Fresh : (σ : Type) → IO.Ref σ → Prop} {mref : ST.Ref IO.RealWorld Meta.State}
  {cref : ST.Ref IO.RealWorld Core.State} {mctx : Meta.Context} {cctx : Core.Context}

/-- **`childLink_real` for `RealChildA`.** Same conclusion and same remaining premises
(`entry`, `ResD`, `P5`); the child record is the new-boundary history `RealChildA O c y`. -/
theorem childLink_realA {O : RefLawsAOps Fresh mref cref} {c : Name} {sc : MachineShape}
    {res : MixedGateBinder} {y : Res}
    (entry : MachineDefines mctx mref cctx cref c sc)
    (ResD : ResDeclAt mref cref c res) (P5 : P5At mref cref c res)
    (hy : RealChildA O c y) :
    ∃ (dE : DefinitionVal) (senv : StructEnv),
      machineShape? false [] (.defnInfo dE) senv = some sc ∧
      machResultKind? dE.type = some res := by
  cases hy with
  | run mctx' cctx' w w' _ _ _ _ hr =>
    obtain ⟨M', D'⟩ := y
    obtain ⟨M, D, w1, hcore, -, -⟩ := Tools.ShippingGateChildComb.synthesizeCombinational_parts hr
    obtain ⟨_, envR, ci, w1', w2', _, _, w5', w6', get, henv, _⟩ :=
      synthesizeCombinationalCore_reads hcore
    have entry' : MachineDefines mctx' mref cctx' cref c sc :=
      Tools.ShippingReflectCtx.MachineDefines.ctx entry
    obtain ⟨dE, hE, hshape⟩ := link_of_defines entry' get henv henv
    exact ⟨dE, _, hshape,
      resC_entry hE (fun dD hci => ResD mctx' cctx' w1' ci w2' dD get hci)
        (fun dD hci hne => P5 mctx' cctx' w1' ci w2' w5' envR w6' dD get henv hci hne)⟩

end Tools.ShippingChildLinkA

import Tools.ShippingGen2SlotlessLeaf
import Sparkle
import Tools.ShippingMachineLinkedCommand
set_option autoImplicit false

/-! # M2-step S2: the CONDITIONAL instance of `slotlessLeaf_ships` on `combLeaf`

`combLeaf` (below): a `circuit do` with a `let` and no register — a slotless, call-free machine-route module; its
generated `machine_*` facts come from `#machine_endpoint`. (The corpus' `pickByteH` is a plain `let` expression, whose endpoint
has no `machineBody`/`machine_writes`, so it cannot be a `.gen` package; failed diagnostic g2st-s2i-bf7d963e.) The package and every data / case premise of `SlotlessLeafStmt` are SUPPLIED
here; without calls the extension is the inputs themselves (`ext := bits`, `extB := bools`), so `ExtInS` is `rfl`.
The compiler-run premises stay hypotheses: package/data satisfiability, NOT evidence that a run exists. -/
set_option maxHeartbeats 4000000

namespace Tests.Gen2.SlotlessLeafInstance
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

@[hardware_module] def combLeaf (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let s := x + y
    return s ^^^ x

#machine_endpoint combLeaf

open Tools.ShippingGen2

abbrev U := fun _ : Unit => defaultDomain

noncomputable instance cl_inh : Inhabited (Sparkle.Core.HList (Tools.ShippingMachineDenote.tys combLeaf.machineData.ss)) :=
  ⟨combLeaf.machineInits⟩

theorem cl_gen : Tools.ShippingQuadComposed.GenFacts combLeaf.machineData U
    combLeaf.machineInits combLeaf.machineBody combLeaf.machineResult
    (fun _ _ bits _ => bits) (fun _ bools _ _ => bools) combLeaf.machineSource :=
  ⟨combLeaf.machine_ok, combLeaf.machine_body, combLeaf.machine_inits, combLeaf.machine_writes,
   combLeaf.machine_result, combLeaf.machine_source, fun _ _ _ _ _ _ _ => ⟨fun _ _ => rfl, fun _ => rfl⟩⟩

noncomputable def clSrc : SrcPkg Unit U :=
  { decl := ``combLeaf, d := combLeaf.machineData, kD := combLeaf.machineData.bsIn.length, ρ := _,
    inh := inferInstance, inits := combLeaf.machineInits, body := combLeaf.machineBody,
    obsR := combLeaf.machineResult, ext := fun _ _ bits _ => bits, extB := fun _ bools _ _ => bools,
    src := combLeaf.machineSource, gen := cl_gen }

noncomputable abbrev clPkg : Pkg Unit U := .gen clSrc

theorem cl_dataOk : LeafDataOk clPkg := by
  unfold LeafDataOk LeafDataOkB; first | decide | decide +kernel

theorem cl_extInS : ExtInS clPkg := ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

theorem cl_noI : clPkg.d.shape.insts = [] := by decide

theorem cl_slots0 : clPkg.d.shape.layout.slots = [] := by decide

/-- **The conditional instance**: every compiler run of `combLeaf` meeting the run premises ships at every height
(top and as a combinational child). -/
theorem cl_ships {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design)
    (hA : Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx)
    (hjqc : Tools.ShippingChildCacheA.JQC L.O (Tools.ShippingChildBndCore.dv w) w)
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore clPkg.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref clPkg.decl clPkg.d.shape)
    (ran : MachineTaken L mctx cctx (Tools.ShippingChildBndCore.dv w + 1) clPkg.decl clPkg.d.shape raw D)
    (n : Nat) :
    TopShips clPkg n clPkg.decl b raw D ∧ ChildShips clPkg n b D :=
  slotlessLeaf_ships L clPkg mctx cctx w w1 raw b D cl_dataOk cl_extInS cl_noI cl_slots0
    hA hjqc hcore hpost entry ran n

#print axioms cl_dataOk
#print axioms cl_ships

end Tests.Gen2.SlotlessLeafInstance

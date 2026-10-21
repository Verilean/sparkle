import Tools.ShippingChildTeleLocalA
import Tools.ShippingChildMainA
import Tools.ShippingChildRunAMain
-- BUILT (unit T2): t2b exit 0 (module), t2c exit 0 (audit test). No `sorry`, no `axiom`, no `native_decide`,
-- no new law / field.

/-! # The main endpoints with `T` replaced by its two remaining fields (unit T2)

`RefLawsATele.ofTeleLam O htel hlam` builds the whole bundle from `O` and the two laws that are
still premises: `htel : ForallTelescopeLawA O.quiet mref cref` (the `telescope` field's statement)
and `hlam : LamTelescopeLawA O.quiet mref cref` (the `lamTelescope` field's statement). The two
`def`s (Tools/ShippingChildWalkA.lean) are the field types verbatim (checked here by using them as
the fields); `localDecl`/`letDecl` are `localDecl_of_O` / `letDecl_of_O` (PROVED from `O`).

The `*_tl` theorems are NOT equivalent wrappers of the `T` versions: they have strictly fewer
premises.
  before: `O`, `hA`, `T : RefLawsATele` (4 fields), + the theorem's other premises
  after : `O`, `hA`, `htel`, `hlam` (2 fields)        + the same other premises
So `localDecl` and `letDecl` are removed from THESE endpoints (and only these: the `T`-taking
theorems are unchanged). `telescope`/`lamTelescope` remain an ADDED, UNPROVED boundary (their
workers are `opaque`); nothing here is a runtime-fit proof or a joint-satisfiability proof. -/

namespace Tools.ShippingChildTeleMainA
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildWalkA
open Tools.ShippingChildDepthC
open Tools.ShippingChildRunAKids
open Tools.ShippingChildFresh
open Tools.ShippingChildTeleLocalA
open Tools.ShippingChildInv
open Tools.ShippingChildFallbackA
open Tools.ShippingChildFrontCP
open Tools.ShippingChildCacheA
open Tools.ShippingChildTranslateA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The telescope bundle from `O` and the two telescope laws.** `localDecl`, `letDecl` PROVED. -/
theorem RefLawsATele.ofTeleLam (O : RefLawsAOps MkRefd mref cref)
    (htel : ForallTelescopeLawA O.quiet mref cref) (hlam : LamTelescopeLawA O.quiet mref cref) :
    RefLawsATele O.quiet mref cref where
  telescope := htel
  lamTelescope := hlam
  localDecl := fun _ hA hIq hI n ty k hk => localDecl_of_O O hA hIq hI n ty k hk
  letDecl := fun _ hA hIq hI n ty v k hk => letDecl_of_O O hA hIq hI n ty v k hk

/-- `MainA.core_tripleA_main` with premises `O`, `hA`, `htel`, `hlam`. -/
theorem core_tripleA_main_tl (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (htel : ForallTelescopeLawA O.quiet mref cref) (hlam : LamTelescopeLawA O.quiet mref cref)
    (declName : Name) :
    Triple mctx mref cctx cref (OutQ O.quiet) (synthesizeCombinationalCore declName [] false)
      (fun _ => OutQ O.quiet) (fun e w => OutQ O.quiet w ∧ OkExc e) :=
  Tools.ShippingChildMainA.core_tripleA_main O hA (RefLawsATele.ofTeleLam O htel hlam) declName

/-- `ComposeC.core_tripleAC_of_tele` with premises `O`, `hA`, `htel`, `hlam`. -/
theorem core_tripleAC_of_tele_tl (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (htel : ForallTelescopeLawA O.quiet mref cref) (hlam : LamTelescopeLawA O.quiet mref cref)
    (declName : Name) :
    Triple mctx mref cctx cref (JQ O.quiet 0) (synthesizeCombinationalCore declName [] false)
      (fun _ => JQC O 0) (EQ O.quiet 0) :=
  Tools.ShippingChildComposeC.core_tripleAC_of_tele O hA (RefLawsATele.ofTeleLam O htel hlam)
    declName

/-- `ComposeC.full_tripleAC_of_tele` with premises `O`, `hA`, `htel`, `hlam`. -/
theorem full_tripleAC_of_tele_tl (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (htel : ForallTelescopeLawA O.quiet mref cref) (hlam : LamTelescopeLawA O.quiet mref cref)
    (declName : Name) :
    Triple mctx mref cctx cref (JQ O.quiet 0) (synthesizeCombinational declName)
      (fun _ => JQC O 0) (EQ O.quiet 0) :=
  Tools.ShippingChildComposeC.full_tripleAC_of_tele O hA (RefLawsATele.ofTeleLam O htel hlam)
    declName

/-- `RunAMain.htr_of_tele` with premises `O`, `hA`, `htel`, `hlam`. -/
theorem htr_of_tele_tl (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (htel : ForallTelescopeLawA O.quiet mref cref) (hlam : LamTelescopeLawA O.quiet mref cref)
    (D : Nat) :
    ∀ (tenv : Lean.Environment) e hint top named, KeepsCP mctx mref cctx cref (JQC O (D + 1))
      (translateExprToWire tenv e hint top named) :=
  Tools.ShippingChildRunAMain.htr_of_tele O hA (RefLawsATele.ofTeleLam O htel hlam) D

/-- `RunAMain.machine_children_realA_main` with premises `O`, `hA`, `htel`, `hlam` (others
unchanged: start world, `MachineDefines`, `MachineClosesAtA` (UNRESOLVED), `shape.insts ≠ []`). -/
theorem machine_children_realA_main_tl (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (htel : ForallTelescopeLawA O.quiet mref cref) (hlam : LamTelescopeLawA O.quiet mref cref)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName shape)
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w)) (hi : shape.insts ≠ []) :
    ∃ t t' d₀ children,
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children m d ∧
      ChildrenRealA O shape children :=
  Tools.ShippingChildRunAMain.machine_children_realA_main O hA (RefLawsATele.ofTeleLam O htel hlam)
    hr entry closes hw hc hi

end Tools.ShippingChildTeleMainA

#print axioms Tools.ShippingChildTeleMainA.core_tripleA_main_tl
#print axioms Tools.ShippingChildTeleMainA.core_tripleAC_of_tele_tl
#print axioms Tools.ShippingChildTeleMainA.full_tripleAC_of_tele_tl
#print axioms Tools.ShippingChildTeleMainA.machine_children_realA_main_tl

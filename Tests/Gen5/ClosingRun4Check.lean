import Tools.ShippingGen5ClosingRun4
import Tests.Gen5.ClosingRun3Check
set_option autoImplicit false
-- No sorry / axiom / native_decide.

/-! # hIH / hKI from the T1 rows (Tools/ShippingGen5ClosingRun4.lean; scripts/gen5/HORD_RUN_FREEZE.md §6)

Expected statements are written from freeze §6 (the `…R` statements of §2 with `hIH` / `hKI` deleted and `hT : T1HypND`
replaced by `hT : T1Hyp` followed by `hrows`, `hStep`). Same comparator as `ClosingRun2Check`. Mutants are rejected by
signature / defeq, NOT semantic counterexamples. Not evidence of non-vacuity. -/

namespace Tests.Gen5.ClosingRun4Check
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC
open Tools.ShippingGen2 Tools.ShippingGen5RunReads Tools.ShippingGen5ClosingRun Tools.ShippingGen5ClosingRun2
open Tools.ShippingGen5ClosingRun3 Tools.ShippingGen5ClosingRun4
open Tests.Gen3.ExpectedType (stmtOf checkAxioms)
open Tests.Gen5.ClosingRun2Check (checkExpectedR checkMutantR reach)
open Tests.Gen5.ClosingRun3Check (propBinders)

def ExpIhKI : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hT : T1Hyp L P Reach DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L P DataOk),
    ∀ D, 1 ≤ D → IHAt L P Reach D ∧ ChildKeepsInv L P Reach D
def ExpRun0T1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hT : T1Hyp L P Reach DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L P DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D
def ExpConnT1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hT : T1Hyp L P Reach DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L P DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun L P Reach mctx cctx X p Gen w w' raw D

/-- mutant: T1HypND in place of T1Hyp (the `dec` field is needed by `StepStmt`'s use in `ih_allPF`) -/
def MutRun0ND : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L P DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D
/-- mutant: without hrows -/
def MutRun0NoRows : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hT : T1Hyp L P Reach DataOk)
    (hStep : StepStmt L P DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D
/-- mutant: the IH from depth 0 -/
def MutIhKI0 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hT : T1Hyp L P Reach DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L P DataOk),
    ∀ D, IHAt L P Reach D ∧ ChildKeepsInv L P Reach D

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpectedR ``ihKI_of_rows ``ExpIhKI
  checkExpectedR ``closingRun0_of_runT1 ``ExpRun0T1
  checkExpectedR ``closingRun_of_runT1 ``ExpConnT1
  logInfo m!"HORD RUN T1 TYPE: 3 theorems against Expected"
  checkMutantR ``closingRun0_of_runT1 ``Tests.Gen5.ClosingRun3Check.ExpRun0R
  checkMutantR ``closingRun_of_runT1 ``Tests.Gen5.ClosingRun3Check.ExpConnR
  checkMutantR ``closingRun0_of_runT1 ``MutRun0ND
  checkMutantR ``closingRun0_of_runT1 ``MutRun0NoRows
  checkMutantR ``ihKI_of_rows ``MutIhKI0
  logInfo m!"HORD RUN T1 MUTANT: 5 rejected (2 statements with hIH/hKI, 3 one-point; signature/defeq, not semantic)"

run_cmd Lean.Elab.Command.liftTermElabM do
  for (newT, oldT) in [(``closingRun0_of_runT1, ``closingRun0_of_runR), (``closingRun_of_runT1, ``closingRun_of_runR)] do
    let got ← propBinders newT
    let old ← propBinders oldT
    let exp := [`hT, `hrows, `hStep] ++ ((old.erase `hT).erase `hIH).erase `hKI
    unless old.contains `hIH && old.contains `hKI do throwError "HORD RUN T1 BINDERS CONTROL {oldT}"
    unless got == exp do throwError "HORD RUN T1 BINDERS FAILED {newT}: expected {exp}, got {got}"
    for n in [`hIH, `hKI, `hord, `hrow] do
      if got.contains n then throwError "HORD RUN T1 BINDERS FAILED {newT}: unexpected premise {n}"
    logInfo m!"HORD RUN T1 BINDERS {newT}: {got} = binders of {oldT} with hIH/hKI removed, hT : T1Hyp, hrows, hStep"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``ihKI_of_rows, ``closingRun0_of_runT1, ``closingRun_of_runT1] do
    checkAxioms n
  logInfo m!"HORD RUN T1 COUNTS: TYPE 3, MUTANT 5, BINDERS 2, AXIOMS 3"

end Tests.Gen5.ClosingRun4Check

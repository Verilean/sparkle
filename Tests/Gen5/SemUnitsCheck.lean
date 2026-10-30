import Tools.ShippingGen5SemRef
import Tools.ShippingGen5SemPkg
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in g5sm-r2 at d5492921 (Pod `kjob lake build`, exit 0; SemUnitsCheck: TYPE 6, MUTANT 5, AXIOMS standard). No sorry / axiom / native_decide.

/-! # DG-SEM units P1 / P2 / P8 checks (Tools/ShippingGen5SemRef.lean, Tools/ShippingGen5SemPkg.lean)

TYPE: each theorem's statement is compared (`Tests.Gen3.ExpectedType.checkExpected`) with an independently written
`Expected…` statement (scripts/gen5/DG_SEM_FREEZE_REV2.md §6, §2.2). MUTANT: a meaning-changing variant must be rejected
(`checkMutant`) — a signature / defeq rejection, NOT a semantic counterexample. AXIOMS / closure: the standard axioms only
(`Lean.collectAxioms`; `sorryAx` would be reported). Nothing here supplies a DG-DATAOF / DG-WFCOVER / DG-ACC obligation. -/

namespace Tests.Gen5.SemUnitsCheck
open Tools.ShippingGen5Sem Tests.Gen3.ExpectedType
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineSource (valsAt)
open Tools.ShippingGen2 (Pkg)

section Expected

def ExpectedValsAtSigListOfFn : Prop :=
  ∀ {dom : DomainConfig} (αs : List Type) (f : Nat → HList αs) (t : Nat),
    valsAt αs (sigListOfFn (dom := dom) αs f) t = f t
def ExpectedValsAtMkHolds : Prop :=
  ∀ {dom : DomainConfig} (αs : List Type) (S : Signal dom (HList αs)) (t : Nat),
    valsAt αs (mkHolds αs S) t = S.val t
def ExpectedReconMkHolds : Prop :=
  ∀ {dom : DomainConfig} (αs : List Type) (S : Signal dom (HList αs)), reconState αs (mkHolds αs S) = S
def ExpectedToSemGenPkg : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (s : SemPkg ι dom) (hF : FactsOf s), (genPkg s hF).toSem = s
def ExpectedPkgEqOfToSem : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {p p' : Pkg ι dom}, p.toSem = p'.toSem → p = p'
def ExpectedExtSGenPkg : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (s : SemPkg ι dom) (hF : FactsOf s), (genPkg s hF).extS = s.extS

/-- Mutant: a different time. -/
def MutValsAtSigListOfFnShift : Prop :=
  ∀ {dom : DomainConfig} (αs : List Type) (f : Nat → HList αs) (t : Nat),
    valsAt αs (sigListOfFn (dom := dom) αs f) t = f (t + 1)
/-- Mutant: the seed read one cycle late. -/
def MutValsAtMkHoldsShift : Prop :=
  ∀ {dom : DomainConfig} (αs : List Type) (S : Signal dom (HList αs)) (t : Nat),
    valsAt αs (mkHolds αs S) (t + 1) = S.val t
/-- Mutant: `toSem` determined by the decl name only. -/
def MutToSemGenPkgDecl : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (s : SemPkg ι dom) (hF : FactsOf s), (genPkg s hF).toSem.decl = s.decl
/-- Mutant: every two packages equal (no hypothesis). -/
def MutPkgEqNoHyp : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {p p' : Pkg ι dom}, p = p'
/-- Mutant: the forgotten state is not the package's own. -/
def MutExtSGenPkgBS : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (s : SemPkg ι dom) (hF : FactsOf s), (genPkg s hF).extBS = s.extBS

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``valsAt_sigListOfFn ``ExpectedValsAtSigListOfFn
  checkExpected ``valsAt_mkHolds ``ExpectedValsAtMkHolds
  checkExpected ``reconState_mkHolds ``ExpectedReconMkHolds
  checkExpected ``toSem_genPkg ``ExpectedToSemGenPkg
  checkExpected ``pkg_eq_of_toSem ``ExpectedPkgEqOfToSem
  checkExpected ``extS_genPkg ``ExpectedExtSGenPkg
  checkMutant ``valsAt_sigListOfFn ``MutValsAtSigListOfFnShift
  checkMutant ``valsAt_mkHolds ``MutValsAtMkHoldsShift
  checkMutant ``toSem_genPkg ``MutToSemGenPkgDecl
  checkMutant ``pkg_eq_of_toSem ``MutPkgEqNoHyp
  checkMutant ``extS_genPkg ``MutExtSGenPkgBS

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``valsAt_sigListOfFn, ``valsAt_mkHolds, ``reconState_mkHolds, ``valsAt_mkHolds_reconState,
      ``toSem_genPkg, ``pkg_eq_of_toSem, ``Tools.ShippingGen2.Pkg.factsOf_toSem, ``extS_genPkg, ``extBS_genPkg,
      ``lsrc_genPkg, ``src_genPkg, ``d_genPkg, ``kD_genPkg, ``decl_genPkg, ``S_genPkg,
      ``decl_toSem, ``d_toSem, ``kD_toSem, ``src_toSem, ``extS_toSem, ``extBS_toSem, ``lsrc_toSem, ``S_toSem] do
    checkAxioms n

#print axioms pkg_eq_of_toSem
#print axioms reconState_mkHolds

end Tests.Gen5.SemUnitsCheck

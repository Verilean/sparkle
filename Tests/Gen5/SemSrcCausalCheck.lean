import Tools.ShippingGen5SemSrcCausal
import Tests.Gen5.SemFactsCheck
set_option autoImplicit false
-- Clean issue-linked build smu13v-343faecd exit 0 (716 jobs), approved at 343faecd (U6C; conditional on hQ : CalleesCausal Q g.d): TYPE 4 / MUTANT 9 / AXIOMS 7 standard / CLOSURE 4233 consts (4 roots) / REACH 10. No sorry/axiom/native_decide.
/-! # DG-SEM U6C check (Tools/ShippingGen5SemSrcCausal.lean; scripts/gen5/DG_SEM_FREEZE_P6E.md §3.1, §5)

* TYPE    — `extJoint_of_genSem`, `genSemGen_srcCausal`, `genSemComb_srcCausal`, `genSemI_srcCausal` by statement against `Exp*` written
            here from the sentences of §3 (`Ctx`/`CtxAgree` by their names), with the same reducible comparer `checkExpected`/`cmpTele`.
* MUTANT  — well-typed single-change mutants rejected by the same comparer: signature/defeq rejection, NOT a semantic counterexample.
            Counting rule: each mutant is ONE well-typed change of ONE theorem's statement; an extra unused hypothesis would make the
            proposition weaker and is not a mutant; ill-typed proposals are not counted.
* AXIOMS / CLOSURE / REACH — as in `Tests/Gen5/SemFactsCheck.lean`; fixtures live only inside `withoutModifyingEnv`. REACH of the `.gen`
            arm is to the actual suppliers (direct construction), not to `genFacts_gen`. -/
namespace Tests.Gen5.SemSrcCausalCheck
open Lean Meta Elab
open Tools.ShippingGen5Sem Tests.Gen3.ExpectedType Tests.Gen5.SemGenCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Compiler.Elab Sparkle.Compiler.MachInstOrigin Tools.ShippingMachineAuto Tools.ShippingMachineDenote
open Tools.ShippingMachineCausal (Ctx CtxAgree)

/-! ## Expected (from the sentences of the freeze, not from the implementation) -/
def ExpExtJoint : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (g : GenIn)
    (hQ : CalleesCausal Q g.d) (i : ι) (x x' : Ctx (dom i) (HList (tys g.d.ss))) (t : Nat), CtxAgree x x' t →
    (∀ p w, (extOf Q g i x.B x.V x.S p w).val t = (extOf Q g i x'.B x'.V x'.S p w).val t) ∧
    (∀ p, (extBOf Q g i x.B x.V x.S p).val t = (extBOf Q g i x'.B x'.V x'.S p).val t)

def ExpGenSrc : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (hQ : CalleesCausal Q g.d), SrcCausal (SemPkg.gen (genSemGen Q X g))

def ExpCombSrc : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (X : Name) (g : GenIn),
    SrcCausal (SemPkg.comb (genSemComb (ι := ι) (dom := dom) X g))

def ExpISrc : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (hQ : CalleesCausal Q g.d), SrcCausal (genSemI Q X g)

/-! ## Mutants (each one well-typed single change) -/
-- M1-M3: drop hQ
def MutJointNoHQ : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (g : GenIn)
    (i : ι) (x x' : Ctx (dom i) (HList (tys g.d.ss))) (t : Nat), CtxAgree x x' t →
    (∀ p w, (extOf Q g i x.B x.V x.S p w).val t = (extOf Q g i x'.B x'.V x'.S p w).val t) ∧
    (∀ p, (extBOf Q g i x.B x.V x.S p).val t = (extBOf Q g i x'.B x'.V x'.S p).val t)
def MutGenSrcNoHQ : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn),
    SrcCausal (SemPkg.gen (genSemGen Q X g))
def MutISrcNoHQ : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn),
    SrcCausal (genSemI Q X g)
-- M4: extJoint, right side one cycle later
def MutJointLate : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (g : GenIn)
    (hQ : CalleesCausal Q g.d) (i : ι) (x x' : Ctx (dom i) (HList (tys g.d.ss))) (t : Nat), CtxAgree x x' t →
    (∀ p w, (extOf Q g i x.B x.V x.S p w).val t = (extOf Q g i x'.B x'.V x'.S p w).val (t + 1)) ∧
    (∀ p, (extBOf Q g i x.B x.V x.S p).val t = (extBOf Q g i x'.B x'.V x'.S p).val t)
-- M5: extJoint, agreement hypothesis one cycle later
def MutJointAgreeLate : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (g : GenIn)
    (hQ : CalleesCausal Q g.d) (i : ι) (x x' : Ctx (dom i) (HList (tys g.d.ss))) (t : Nat), CtxAgree x x' (t + 1) →
    (∀ p w, (extOf Q g i x.B x.V x.S p w).val t = (extOf Q g i x'.B x'.V x'.S p w).val t) ∧
    (∀ p, (extBOf Q g i x.B x.V x.S p).val t = (extBOf Q g i x'.B x'.V x'.S p).val t)
-- M6: genSemI_srcCausal for the gen package only
def MutIWrongPkg : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (hQ : CalleesCausal Q g.d), SrcCausal (SemPkg.gen (genSemGen Q X g))
-- M7: genSemGen_srcCausal for the comb package
def MutGenWrongArm : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (hQ : CalleesCausal Q g.d), SrcCausal (SemPkg.comb (genSemComb (ι := ι) (dom := dom) X g))
-- M8-M9: extJoint, one conjunct of the conclusion dropped
def MutJointOnlyExt : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (g : GenIn)
    (hQ : CalleesCausal Q g.d) (i : ι) (x x' : Ctx (dom i) (HList (tys g.d.ss))) (t : Nat), CtxAgree x x' t →
    (∀ p w, (extOf Q g i x.B x.V x.S p w).val t = (extOf Q g i x'.B x'.V x'.S p w).val t)
def MutJointOnlyExtB : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (g : GenIn)
    (hQ : CalleesCausal Q g.d) (i : ι) (x x' : Ctx (dom i) (HList (tys g.d.ss))) (t : Nat), CtxAgree x x' t →
    (∀ p, (extBOf Q g i x.B x.V x.S p).val t = (extBOf Q g i x'.B x'.V x'.S p).val t)

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``extJoint_of_genSem ``ExpExtJoint
  checkExpected ``genSemGen_srcCausal ``ExpGenSrc
  checkExpected ``genSemComb_srcCausal ``ExpCombSrc
  checkExpected ``genSemI_srcCausal ``ExpISrc
  logInfo m!"GEN5 SRCCAUSAL TYPE OK 4 theorems (extJoint_of_genSem, genSemGen_srcCausal, genSemComb_srcCausal, genSemI_srcCausal) against ExpExtJoint, ExpGenSrc, ExpCombSrc, ExpISrc"
  let mutants : List (Name × Name) :=
    [(``extJoint_of_genSem, ``MutJointNoHQ), (``genSemGen_srcCausal, ``MutGenSrcNoHQ), (``genSemI_srcCausal, ``MutISrcNoHQ),
     (``extJoint_of_genSem, ``MutJointLate), (``extJoint_of_genSem, ``MutJointAgreeLate),
     (``genSemI_srcCausal, ``MutIWrongPkg), (``genSemGen_srcCausal, ``MutGenWrongArm),
     (``extJoint_of_genSem, ``MutJointOnlyExt), (``extJoint_of_genSem, ``MutJointOnlyExtB)]
  for (t, m) in mutants do checkMutant t m
  logInfo m!"GEN5 SRCCAUSAL COUNTS: TYPE 4 theorems; MUTANT {mutants.length} total on theorems \
    (hypothesis dropped 3: hQ in extJoint, genSemGen, genSemI; conclusion time changed 1; agreement hypothesis time changed 1; \
    wrong package 1; wrong arm 1; conclusion conjunct dropped 2: ext only, extB only); each is one well-typed change, \
    signature/defeq rejection, NOT a semantic counterexample. Unused extra hypotheses (weaker statements) and ill-typed proposals are not counted."

run_cmd Lean.Elab.Command.liftTermElabM do
  let ns : List Name := [``extJoint_of_genSem, ``genSemGen_srcCausal, ``genSemComb_srcCausal, ``genSemI_srcCausal,
    ``ExtStage_causal2, ``map_apply_eq_of_getElem, ``genSemGen_src_length]
  for n in ns do checkAxioms n
  logInfo m!"GEN5 SRCCAUSAL AXIOMS OK: {ns.length} theorems (4 frozen + 3 helpers), standard axioms only"

run_cmd Lean.Elab.Command.liftTermElabM do
  let roots : List Name := [``genSemI_srcCausal, ``genSemGen_srcCausal, ``genSemComb_srcCausal, ``extJoint_of_genSem]
  let c ← closureRun roots
  let f := forbiddenIn c
  unless f.isEmpty do throwError "GEN5 SRCCAUSAL CLOSURE FAILED: forbidden constants {f}"
  let t1 ← (do let _ ← closureRun [`Tests.Gen5.SemSrcCausalCheck.NoSuchConstant]; pure false) <|> pure true
  unless t1 do throwError "GEN5 SRCCAUSAL CONTROL FAILED: unknown root did not throw"
  for r in [``Lean.ofReduceBool, ``sorryAx] do
    let f ← detect [r]
    unless f.contains r do throwError "GEN5 SRCCAUSAL CONTROL FAILED: forbidden root {r} not flagged (got {f})"
  Tests.Gen5.SemExtCheck.withFixtures fun r3 r4 rc mv mt hv4 => do
    let env ← getEnv
    let t3 ← (do let _ ← closureRun [r3]; pure false) <|> pure true
    unless t3 do throwError "GEN5 SRCCAUSAL CONTROL FAILED: unknown helper value did not throw"
    let (_, c3) ← (closureOf env r3).run {}
    unless c3.missing == #[mv] do throwError "GEN5 SRCCAUSAL CONTROL FAILED: helper-value case reported {c3.missing}, intended {mv}"
    let t4 ← (do let _ ← closureRun [r4]; pure false) <|> pure true
    unless t4 do throwError "GEN5 SRCCAUSAL CONTROL FAILED: unknown helper type did not throw"
    let (_, c4) ← (closureOf env r4).run {}
    unless c4.missing == #[mt] do throwError "GEN5 SRCCAUSAL CONTROL FAILED: helper-type case reported {c4.missing}, intended {mt}"
    unless c4.seen.contains hv4 do throwError "GEN5 SRCCAUSAL CONTROL FAILED: helper-type path does not pass through Hv4"
    let cc ← closureRun [rc]
    unless cc.missing.isEmpty && (forbiddenIn cc).isEmpty do throwError "GEN5 SRCCAUSAL CONTROL FAILED: clean fixture flagged"
  logInfo m!"GEN5 SRCCAUSAL CLOSURE OK: {c.seen.toList.length} constants over {roots.length} roots, no forbidden constant; controls: unknown root throws, \
    2 forbidden roots flagged, unknown helper VALUE names Mv, unknown helper TYPE names Mt via Hv4, clean fixture passes (fixtures inside withoutModifyingEnv)"

run_cmd Lean.Elab.Command.liftTermElabM do
  let reach (root : Name) (need : List Name) : MetaM Nat := do
    let c ← closureRun [root]
    for n in need do
      unless c.seen.contains n do throwError "GEN5 SRCCAUSAL REACH FAILED: {root} does not reach {n}"
    pure need.length
  let a ← reach ``genSemI_srcCausal [``genSemGen_srcCausal, ``genSemComb_srcCausal]
  let b ← reach ``genSemGen_srcCausal [``Tools.ShippingMachineCausal.src_causal_of_data_causal, ``extJoint_of_genSem,
    ``extCausal_of_genSem, ``genSemGenE_writes, ``genSemGenE_result, ``genSemGenE_source]
  let c ← reach ``extJoint_of_genSem [``callOut_causal]
  let d ← reach ``genSemComb_srcCausal [``Tools.ShippingMachineCausal.typedVal_congrB]
  logInfo m!"GEN5 SRCCAUSAL REACH OK: {a + b + c + d} required constants reached over 4 roots (genSemGen_srcCausal reaches the real suppliers directly, not genFacts_gen)"

#print axioms genSemI_srcCausal

end Tests.Gen5.SemSrcCausalCheck

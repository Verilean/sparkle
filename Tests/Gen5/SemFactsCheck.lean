import Tools.ShippingGen5SemFacts
import Tests.Gen5.SemCausalCheck
set_option autoImplicit false
-- NOT BUILT yet (U6B check). No sorry/axiom/native_decide.
/-! # DG-SEM U6B check (Tools/ShippingGen5SemFacts.lean; scripts/gen5/DG_SEM_FREEZE_P6D.md §3.1)

* TYPE    — `genFacts_gen`, `genFacts_comb`, `genFacts` by statement against `Exp*` written here from the sentences of §3
            (the `GenFacts`/`CombFacts` instances with an explicit `@`-telescope), same reducible comparer `checkExpected`/`cmpTele`.
* MUTANT  — well-typed single-change mutants rejected by the same comparer: signature/defeq rejection, NOT a semantic counterexample.
            (Replacing `s.inits` by `g.inits`, or a `gen`/`comb` `s` by the other constructor, is ill-typed and is NOT counted.)
* AXIOMS / CLOSURE / REACH — as in `Tests/Gen5/SemCausalCheck.lean`; fixtures live only inside `withoutModifyingEnv`. -/
namespace Tests.Gen5.SemFactsCheck
open Lean Meta Elab
open Tools.ShippingGen5Sem Tests.Gen3.ExpectedType Tests.Gen5.SemGenCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Compiler.Elab Sparkle.Compiler.MachInstOrigin Tools.ShippingMachineAuto Tools.ShippingMachineDenote

/-! ## Expected (from the sentences of the freeze, not from the implementation) -/
def ExpGen : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (hQ : CalleesCausal Q g.d) (s : SrcSem ι dom) (hs : genSemI Q X g = SemPkg.gen s),
    @Tools.ShippingQuadComposed.GenFacts s.d ι dom s.ρ s.inh s.inits s.body s.obsR s.ext s.extB s.src

def ExpComb : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (s : CombSem ι dom) (hs : genSemI Q X g = SemPkg.comb s),
    Tools.ShippingGen2.CombFacts s.d dom s.inits s.src

def ExpFacts : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (hQ : CalleesCausal Q g.d), FactsOf (genSemI Q X g)

/-! ## Mutants (each one well-typed single change) -/
-- M1: drop hQ from the gen arm
def MutGenNoHQ : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (s : SrcSem ι dom) (hs : genSemI Q X g = SemPkg.gen s),
    @Tools.ShippingQuadComposed.GenFacts s.d ι dom s.ρ s.inh s.inits s.body s.obsR s.ext s.extB s.src
-- M2: drop hQ from genFacts
def MutFactsNoHQ : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn),
    FactsOf (genSemI Q X g)
-- M3: drop hs from the gen arm (s free)
def MutGenNoHs : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (hQ : CalleesCausal Q g.d) (s : SrcSem ι dom),
    @Tools.ShippingQuadComposed.GenFacts s.d ι dom s.ρ s.inh s.inits s.body s.obsR s.ext s.extB s.src
-- M4: drop hs from the comb arm (s free)
def MutCombNoHs : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (s : CombSem ι dom), Tools.ShippingGen2.CombFacts s.d dom s.inits s.src
-- M5: gen arm, hs about genSemGen (the arm's own constructor-free equation) instead of genSemI
def MutGenHsViaGenSemGen : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (hQ : CalleesCausal Q g.d) (s : SrcSem ι dom) (hs : genSemGen Q X g = s),
    @Tools.ShippingQuadComposed.GenFacts s.d ι dom s.ρ s.inh s.inits s.body s.obsR s.ext s.extB s.src
-- M6: gen arm, src of the conclusion replaced by another src of the same type
def MutGenOtherSrc : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (hQ : CalleesCausal Q g.d) (s : SrcSem ι dom) (hs : genSemI Q X g = SemPkg.gen s),
    @Tools.ShippingQuadComposed.GenFacts s.d ι dom s.ρ s.inh s.inits s.body s.obsR s.ext s.extB (genSemGen Q X g).src
-- M7: comb arm, src of the conclusion replaced by another src of the same type
def MutCombOtherSrc : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (s : CombSem ι dom) (hs : genSemI Q X g = SemPkg.comb s),
    Tools.ShippingGen2.CombFacts s.d dom s.inits (genSemComb X g).src
-- M8: genFacts for the wrong package (always the gen arm)
def MutFactsWrongPkg : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (hQ : CalleesCausal Q g.d), FactsOf (SemPkg.gen (genSemGen Q X g))
-- M9: hQ about a different machine data (the table Q against s.d instead of g.d), gen arm
def MutGenHQOnS : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (s : SrcSem ι dom) (hQ : CalleesCausal Q s.d) (hs : genSemI Q X g = SemPkg.gen s),
    @Tools.ShippingQuadComposed.GenFacts s.d ι dom s.ρ s.inh s.inits s.body s.obsR s.ext s.extB s.src

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``genFacts_gen ``ExpGen
  checkExpected ``genFacts_comb ``ExpComb
  checkExpected ``genFacts ``ExpFacts
  logInfo m!"GEN5 FACTS TYPE OK 3 theorems (genFacts_gen, genFacts_comb, genFacts) against ExpGen, ExpComb, ExpFacts"
  let mutants : List (Name × Name) :=
    [(``genFacts_gen, ``MutGenNoHQ), (``genFacts, ``MutFactsNoHQ),
     (``genFacts_gen, ``MutGenNoHs), (``genFacts_comb, ``MutCombNoHs),
     (``genFacts_gen, ``MutGenHsViaGenSemGen),
     (``genFacts_gen, ``MutGenOtherSrc), (``genFacts_comb, ``MutCombOtherSrc),
     (``genFacts, ``MutFactsWrongPkg), (``genFacts_gen, ``MutGenHQOnS)]
  for (t, m) in mutants do checkMutant t m
  logInfo m!"GEN5 FACTS COUNTS: TYPE 3 theorems; MUTANT {mutants.length} total on theorems \
    (hypothesis dropped 4: hQ in gen, hQ in genFacts, hs in gen, hs in comb; hypothesis changed 2: hs via genSemGen, hQ on s.d; \
    conclusion src changed to a same-typed src 2: gen, comb; wrong package 1); conclusion-conjunct-dropped 0 (the conclusions are structures, not conjunctions); \
    signature/defeq rejections of well-typed statements, NOT semantic counterexamples. Ill-typed proposals (g.inits for s.inits; other constructor for s) are not counted."

run_cmd Lean.Elab.Command.liftTermElabM do
  let ns : List Name := [``genFacts_gen, ``genFacts_comb, ``genFacts, ``hlist_nil_subsingleton]
  for n in ns do checkAxioms n
  logInfo m!"GEN5 FACTS AXIOMS OK: {ns.length} theorems (3 frozen + 1 helper), standard axioms only"

run_cmd Lean.Elab.Command.liftTermElabM do
  let roots : List Name := [``genFacts, ``genFacts_gen, ``genFacts_comb]
  let c ← closureRun roots
  let f := forbiddenIn c
  unless f.isEmpty do throwError "GEN5 FACTS CLOSURE FAILED: forbidden constants {f}"
  let t1 ← (do let _ ← closureRun [`Tests.Gen5.SemFactsCheck.NoSuchConstant]; pure false) <|> pure true
  unless t1 do throwError "GEN5 FACTS CONTROL FAILED: unknown root did not throw"
  for r in [``Lean.ofReduceBool, ``sorryAx] do
    let f ← detect [r]
    unless f.contains r do throwError "GEN5 FACTS CONTROL FAILED: forbidden root {r} not flagged (got {f})"
  Tests.Gen5.SemExtCheck.withFixtures fun r3 r4 rc mv mt hv4 => do
    let env ← getEnv
    let t3 ← (do let _ ← closureRun [r3]; pure false) <|> pure true
    unless t3 do throwError "GEN5 FACTS CONTROL FAILED: unknown helper value did not throw"
    let (_, c3) ← (closureOf env r3).run {}
    unless c3.missing == #[mv] do throwError "GEN5 FACTS CONTROL FAILED: helper-value case reported {c3.missing}, intended {mv}"
    let t4 ← (do let _ ← closureRun [r4]; pure false) <|> pure true
    unless t4 do throwError "GEN5 FACTS CONTROL FAILED: unknown helper type did not throw"
    let (_, c4) ← (closureOf env r4).run {}
    unless c4.missing == #[mt] do throwError "GEN5 FACTS CONTROL FAILED: helper-type case reported {c4.missing}, intended {mt}"
    unless c4.seen.contains hv4 do throwError "GEN5 FACTS CONTROL FAILED: helper-type path does not pass through Hv4"
    let cc ← closureRun [rc]
    unless cc.missing.isEmpty && (forbiddenIn cc).isEmpty do throwError "GEN5 FACTS CONTROL FAILED: clean fixture flagged"
  logInfo m!"GEN5 FACTS CLOSURE OK: {c.seen.toList.length} constants over {roots.length} roots, no forbidden constant; controls: unknown root throws, \
    2 forbidden roots flagged, unknown helper VALUE names Mv, unknown helper TYPE names Mt via Hv4, clean fixture passes (fixtures inside withoutModifyingEnv)"

run_cmd Lean.Elab.Command.liftTermElabM do
  let reach (root : Name) (need : List Name) : MetaM Nat := do
    let c ← closureRun [root]
    for n in need do
      unless c.seen.contains n do throwError "GEN5 FACTS REACH FAILED: {root} does not reach {n}"
    pure need.length
  let a ← reach ``genFacts [``genFacts_gen, ``genFacts_comb]
  let b ← reach ``genFacts_gen [``genSemGenE_writes, ``genSemGenE_result, ``genSemGenE_source, ``extCausal_of_genSem]
  logInfo m!"GEN5 FACTS REACH OK: {a + b} required constants reached over 2 roots"

#print axioms genFacts

end Tests.Gen5.SemFactsCheck

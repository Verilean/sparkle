import Tools.ShippingGen5SemAccStep
import Tests.Gen5.SemFactsCheck
set_option autoImplicit false
-- NOT BUILT HERE (U6D check; built clean as smu15v-f7d72d28, exit 0, approved at f7d72d28; header/comment sync only). No sorry/axiom/native_decide.
/-! # DG-SEM U6D check (Tools/ShippingGen5SemAccStep.lean; scripts/gen5/DG_SEM_FREEZE_P6F.md §3.1)

* TYPE    — three theorems by statement against `Exp*` written here from the sentences of §3, same reducible comparer `checkExpected`/`cmpTele`.
* MUTANT  — well-typed single-change mutants rejected by the same comparer: signature/defeq rejection, NOT a semantic counterexample.
            Counting rule: each mutant is ONE well-typed change of ONE theorem's statement; an unused extra hypothesis makes the
            proposition weaker and is not a mutant; ill-typed proposals are not counted. (No conjunctive conclusion exists here, so no
            conclusion-conjunct mutant.)
* AXIOMS / CLOSURE / REACH — as in `Tests/Gen5/SemSrcCausalCheck.lean`; fixtures live only inside `withoutModifyingEnv`. -/
namespace Tests.Gen5.SemAccStepCheck
open Lean Meta Elab
open Tools.ShippingGen5Sem Tests.Gen3.ExpectedType Tests.Gen5.SemGenCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Compiler.Elab Sparkle.Compiler.MachInstOrigin Tools.ShippingMachineAuto Tools.ShippingMachineDenote

/-! ## Expected (from the sentences of the freeze, not from the implementation) -/
def ExpSrc : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y)
    (X : Name) (hX : Acc R X) (s : SemPkg ι dom) (hs : G X = some s),
    SrcCausal s
def ExpFacts : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y)
    (X : Name) (hX : Acc R X) (s : SemPkg ι dom) (hs : G X = some s),
    FactsOf s
def ExpAll : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y)
    (hacc : ∀ (Y : Name) (s : SemPkg ι dom), G Y = some s → Acc R Y),
    ∀ (X : Name) (s : SemPkg ι dom), G X = some s → FactsOf s

/-! ## Mutants (each one well-typed single change) -/
-- M1-M2: edge conjunct of hunf dropped (theorems 1, 2)
def MutSrcNoEdge : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g)
    (X : Name) (hX : Acc R X) (s : SemPkg ι dom) (hs : G X = some s),
    SrcCausal s
def MutFactsNoEdge : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g)
    (X : Name) (hX : Acc R X) (s : SemPkg ι dom) (hs : G X = some s),
    FactsOf s
-- M3: drop hX
def MutSrcNoAcc : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y)
    (X : Name) (s : SemPkg ι dom) (hs : G X = some s),
    SrcCausal s
-- M4: drop hacc
def MutAllNoAcc : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y),
    ∀ (X : Name) (s : SemPkg ι dom), G X = some s → FactsOf s
-- M5: wrong target in theorem 1
def MutSrcWrongConcl : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y)
    (X : Name) (hX : Acc R X) (s : SemPkg ι dom) (hs : G X = some s),
    FactsOf s
-- M6: wrong target in theorem 2
def MutFactsWrongConcl : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y)
    (X : Name) (hX : Acc R X) (s : SemPkg ι dom) (hs : G X = some s),
    SrcCausal s
-- M7: equation against the empty table
def MutSrcWrongG : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI (fun _ => none) Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y)
    (X : Name) (hX : Acc R X) (s : SemPkg ι dom) (hs : G X = some s),
    SrcCausal s
-- M8: R argument order flipped in the edge conjunct
def MutSrcFlip : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R Y ((g.d.shape.insts[k]).1))
    (X : Name) (hX : Acc R X) (s : SemPkg ι dom) (hs : G X = some s),
    SrcCausal s

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``srcCausal_of_acc_unfold ``ExpSrc
  checkExpected ``factsOf_of_acc_unfold ``ExpFacts
  checkExpected ``factsOf_all_of_acc_unfold ``ExpAll
  logInfo m!"GEN5 ACCSTEP TYPE OK 3 theorems against ExpSrc, ExpFacts, ExpAll"
  let mutants : List (Name × Name) :=
    [(``srcCausal_of_acc_unfold, ``MutSrcNoEdge), (``factsOf_of_acc_unfold, ``MutFactsNoEdge),
     (``srcCausal_of_acc_unfold, ``MutSrcNoAcc), (``factsOf_all_of_acc_unfold, ``MutAllNoAcc),
     (``srcCausal_of_acc_unfold, ``MutSrcWrongConcl), (``factsOf_of_acc_unfold, ``MutFactsWrongConcl),
     (``srcCausal_of_acc_unfold, ``MutSrcWrongG), (``srcCausal_of_acc_unfold, ``MutSrcFlip)]
  for (t, m) in mutants do checkMutant t m
  logInfo m!"GEN5 ACCSTEP COUNTS: TYPE 3 theorems; MUTANT {mutants.length} total (edge conjunct of hunf dropped 2; hX dropped 1; hacc dropped 1; \
    conclusion changed 2; equation against empty table 1; R argument order flipped 1); each is one well-typed change, \
    signature/defeq rejection, NOT a semantic counterexample. Unused extra hypotheses (weaker) and ill-typed proposals are not counted."

run_cmd Lean.Elab.Command.liftTermElabM do
  let ns : List Name := [``srcCausal_of_acc_unfold, ``factsOf_of_acc_unfold, ``factsOf_all_of_acc_unfold]
  for n in ns do checkAxioms n
  logInfo m!"GEN5 ACCSTEP AXIOMS OK: {ns.length} theorems, standard axioms only"

run_cmd Lean.Elab.Command.liftTermElabM do
  let roots : List Name := [``srcCausal_of_acc_unfold, ``factsOf_of_acc_unfold, ``factsOf_all_of_acc_unfold]
  let c ← closureRun roots
  let f := forbiddenIn c
  unless f.isEmpty do throwError "GEN5 ACCSTEP CLOSURE FAILED: forbidden constants {f}"
  let t1 ← (do let _ ← closureRun [`Tests.Gen5.SemAccStepCheck.NoSuchConstant]; pure false) <|> pure true
  unless t1 do throwError "GEN5 ACCSTEP CONTROL FAILED: unknown root did not throw"
  for r in [``Lean.ofReduceBool, ``sorryAx] do
    let f ← detect [r]
    unless f.contains r do throwError "GEN5 ACCSTEP CONTROL FAILED: forbidden root {r} not flagged (got {f})"
  Tests.Gen5.SemExtCheck.withFixtures fun r3 r4 rc mv mt hv4 => do
    let env ← getEnv
    let t3 ← (do let _ ← closureRun [r3]; pure false) <|> pure true
    unless t3 do throwError "GEN5 ACCSTEP CONTROL FAILED: unknown helper value did not throw"
    let (_, c3) ← (closureOf env r3).run {}
    unless c3.missing == #[mv] do throwError "GEN5 ACCSTEP CONTROL FAILED: helper-value case reported {c3.missing}, intended {mv}"
    let t4 ← (do let _ ← closureRun [r4]; pure false) <|> pure true
    unless t4 do throwError "GEN5 ACCSTEP CONTROL FAILED: unknown helper type did not throw"
    let (_, c4) ← (closureOf env r4).run {}
    unless c4.missing == #[mt] do throwError "GEN5 ACCSTEP CONTROL FAILED: helper-type case reported {c4.missing}, intended {mt}"
    unless c4.seen.contains hv4 do throwError "GEN5 ACCSTEP CONTROL FAILED: helper-type path does not pass through Hv4"
    let cc ← closureRun [rc]
    unless cc.missing.isEmpty && (forbiddenIn cc).isEmpty do throwError "GEN5 ACCSTEP CONTROL FAILED: clean fixture flagged"
  logInfo m!"GEN5 ACCSTEP CLOSURE OK: {c.seen.toList.length} constants over {roots.length} roots, no forbidden constant; controls: unknown root throws, \
    2 forbidden roots flagged, unknown helper VALUE names Mv, unknown helper TYPE names Mt via Hv4, clean fixture passes (fixtures inside withoutModifyingEnv)"

run_cmd Lean.Elab.Command.liftTermElabM do
  let reach (root : Name) (need : List Name) : MetaM Nat := do
    let c ← closureRun [root]
    for n in need do
      unless c.seen.contains n do throwError "GEN5 ACCSTEP REACH FAILED: {root} does not reach {n}"
    pure need.length
  let a ← reach ``srcCausal_of_acc_unfold [``genSemI_srcCausal]
  let b ← reach ``factsOf_of_acc_unfold [``genFacts, ``srcCausal_of_acc_unfold]
  let c ← reach ``factsOf_all_of_acc_unfold [``factsOf_of_acc_unfold]
  logInfo m!"GEN5 ACCSTEP REACH OK: {a + b + c} required constants reached over 3 roots"

#print axioms factsOf_all_of_acc_unfold

end Tests.Gen5.SemAccStepCheck

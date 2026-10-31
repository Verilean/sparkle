import Tools.ShippingGen5SemKitInv
import Tests.Gen5.SemFactsCheck
set_option autoImplicit false
-- NOT BUILT HERE (U7 check, scripts/gen5/DG_SEM_FREEZE_P7.md §3.2). No sorry/axiom/native_decide.
/-! # DG-SEM U7 check (Tools/ShippingGen5SemKitInv.lean)

* TYPE    — `hunf_of_kitInv`, `factsOf_all_of_kitInv` (and helper `ordCallees_transport`) by statement against `Exp*` written here
            from the sentences of freeze §3.1, same reducible comparer `checkExpected`/`cmpTele`.
* MUTANT  — well-typed single-change mutants rejected by the same comparer: signature/defeq rejection, NOT a semantic counterexample.
            Each is ONE well-typed change of ONE theorem's statement; unused extra hypotheses (weaker) and ill-typed proposals are not counted.
* AXIOMS / CLOSURE / REACH — as in `Tests/Gen5/SemAccStepCheck.lean`; fixtures live only inside `withoutModifyingEnv`. -/
namespace Tests.Gen5.SemKitInvCheck
open Lean Meta Elab
open Tools.ShippingGen5Sem Tests.Gen3.ExpectedType Tests.Gen5.SemGenCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Compiler.Elab Sparkle.Compiler.MachInstOrigin Tools.ShippingMachineAuto Tools.ShippingMachineDenote
open Sparkle.IR.Semantics Sparkle.IR.Machine

/-! ## Expected -/
def ExpHunf : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    (GD : ConstantInfo → Type) (toIn : {E : ConstantInfo} → GD E → GenIn)
    (dOf : {E : ConstantInfo} → GD E → MachineData)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSemK : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hsem : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (gd : GD E),
      genSemK Q X gd = genSemVia GD toIn Q X gd)
    (hd : ∀ {E : ConstantInfo} (gd : GD E), (toIn gd).d = dOf gd)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GD E), Acc R X ∧
        (∀ k ∈ ordC (dOf gd), R (((dOf gd).shape.insts[k]).1) X) ∧ s = genSemK G X gd),
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y
def ExpAll : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    (GD : ConstantInfo → Type) (toIn : {E : ConstantInfo} → GD E → GenIn)
    (dOf : {E : ConstantInfo} → GD E → MachineData)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSemK : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hsem : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (gd : GD E),
      genSemK Q X gd = genSemVia GD toIn Q X gd)
    (hd : ∀ {E : ConstantInfo} (gd : GD E), (toIn gd).d = dOf gd)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GD E), Acc R X ∧
        (∀ k ∈ ordC (dOf gd), R (((dOf gd).shape.insts[k]).1) X) ∧ s = genSemK G X gd),
    ∀ (X : Name) (s : SemPkg ι dom), G X = some s → FactsOf s
def ExpTrans : Prop := ∀ (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (d d' : MachineData) (h : d = d') (k : Fin d.shape.insts.length) (hk : k ∈ ordCallees d),
    ∃ k' : Fin d'.shape.insts.length, k' ∈ ordC d' ∧ (d.shape.insts[k]).1 = (d'.shape.insts[k']).1

/-! ## Mutants (each one well-typed single change) -/
def MutHsem : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    (GD : ConstantInfo → Type) (toIn : {E : ConstantInfo} → GD E → GenIn)
    (dOf : {E : ConstantInfo} → GD E → MachineData)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSemK : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hsem : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (gd : GD E),
      genSemK Q X gd = genSemI (fun _ => none) X (toIn gd))
    (hd : ∀ {E : ConstantInfo} (gd : GD E), (toIn gd).d = dOf gd)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GD E), Acc R X ∧
        (∀ k ∈ ordC (dOf gd), R (((dOf gd).shape.insts[k]).1) X) ∧ s = genSemK G X gd),
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y
def MutNoHd : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    (GD : ConstantInfo → Type) (toIn : {E : ConstantInfo} → GD E → GenIn)
    (dOf : {E : ConstantInfo} → GD E → MachineData)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSemK : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hsem : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (gd : GD E),
      genSemK Q X gd = genSemVia GD toIn Q X gd)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GD E), Acc R X ∧
        (∀ k ∈ ordC (dOf gd), R (((dOf gd).shape.insts[k]).1) X) ∧ s = genSemK G X gd),
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y
def MutHmem : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    (GD : ConstantInfo → Type) (toIn : {E : ConstantInfo} → GD E → GenIn)
    (dOf : {E : ConstantInfo} → GD E → MachineData)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSemK : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hsem : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (gd : GD E),
      genSemK Q X gd = genSemVia GD toIn Q X gd)
    (hd : ∀ {E : ConstantInfo} (gd : GD E), (toIn gd).d = dOf gd)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? ≠ none)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GD E), Acc R X ∧
        (∀ k ∈ ordC (dOf gd), R (((dOf gd).shape.insts[k]).1) X) ∧ s = genSemK G X gd),
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y
def MutEdgeFlip : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    (GD : ConstantInfo → Type) (toIn : {E : ConstantInfo} → GD E → GenIn)
    (dOf : {E : ConstantInfo} → GD E → MachineData)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSemK : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hsem : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (gd : GD E),
      genSemK Q X gd = genSemVia GD toIn Q X gd)
    (hd : ∀ {E : ConstantInfo} (gd : GD E), (toIn gd).d = dOf gd)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GD E), Acc R X ∧
        (∀ k ∈ ordC (dOf gd), R X (((dOf gd).shape.insts[k]).1)) ∧ s = genSemK G X gd),
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y
def MutEqEmpty : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    (GD : ConstantInfo → Type) (toIn : {E : ConstantInfo} → GD E → GenIn)
    (dOf : {E : ConstantInfo} → GD E → MachineData)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSemK : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hsem : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (gd : GD E),
      genSemK Q X gd = genSemVia GD toIn Q X gd)
    (hd : ∀ {E : ConstantInfo} (gd : GD E), (toIn gd).d = dOf gd)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GD E), Acc R X ∧
        (∀ k ∈ ordC (dOf gd), R (((dOf gd).shape.insts[k]).1) X) ∧ s = genSemK (fun _ => none) X gd),
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y
def MutConclFlip : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    (GD : ConstantInfo → Type) (toIn : {E : ConstantInfo} → GD E → GenIn)
    (dOf : {E : ConstantInfo} → GD E → MachineData)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSemK : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hsem : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (gd : GD E),
      genSemK Q X gd = genSemVia GD toIn Q X gd)
    (hd : ∀ {E : ConstantInfo} (gd : GD E), (toIn gd).d = dOf gd)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GD E), Acc R X ∧
        (∀ k ∈ ordC (dOf gd), R (((dOf gd).shape.insts[k]).1) X) ∧ s = genSemK G X gd),
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R Y ((g.d.shape.insts[k]).1)
def MutAllConcl : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    (GD : ConstantInfo → Type) (toIn : {E : ConstantInfo} → GD E → GenIn)
    (dOf : {E : ConstantInfo} → GD E → MachineData)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSemK : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hsem : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (gd : GD E),
      genSemK Q X gd = genSemVia GD toIn Q X gd)
    (hd : ∀ {E : ConstantInfo} (gd : GD E), (toIn gd).d = dOf gd)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GD E), Acc R X ∧
        (∀ k ∈ ordC (dOf gd), R (((dOf gd).shape.insts[k]).1) X) ∧ s = genSemK G X gd),
    ∀ (X : Name) (s : SemPkg ι dom), G X = some s → SrcCausal s
def MutAllNoAcc : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    (GD : ConstantInfo → Type) (toIn : {E : ConstantInfo} → GD E → GenIn)
    (dOf : {E : ConstantInfo} → GD E → MachineData)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSemK : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hsem : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (gd : GD E),
      genSemK Q X gd = genSemVia GD toIn Q X gd)
    (hd : ∀ {E : ConstantInfo} (gd : GD E), (toIn gd).d = dOf gd)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GD E), True ∧
        (∀ k ∈ ordC (dOf gd), R (((dOf gd).shape.insts[k]).1) X) ∧ s = genSemK G X gd),
    ∀ (X : Name) (s : SemPkg ι dom), G X = some s → FactsOf s

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``hunf_of_kitInv ``ExpHunf
  checkExpected ``factsOf_all_of_kitInv ``ExpAll
  checkExpected ``ordCallees_transport ``ExpTrans
  logInfo m!"GEN5 KITINV TYPE OK 3 theorems against ExpHunf, ExpAll, ExpTrans"
  let mutants : List (Name × Name) :=
    [(``hunf_of_kitInv, ``MutHsem),
     (``hunf_of_kitInv, ``MutNoHd),
     (``hunf_of_kitInv, ``MutHmem),
     (``hunf_of_kitInv, ``MutEdgeFlip),
     (``hunf_of_kitInv, ``MutEqEmpty),
     (``hunf_of_kitInv, ``MutConclFlip),
     (``factsOf_all_of_kitInv, ``MutAllConcl),
     (``factsOf_all_of_kitInv, ``MutAllNoAcc)]
  for (t, m) in mutants do checkMutant t m
  logInfo m!"GEN5 KITINV COUNTS: TYPE 3 theorems; MUTANT {mutants.length} total (hsem target 1; hd dropped 1; hmem = to ≠ 1; hinv edge flipped 1; \
    hinv equation against empty table 1; hunf conclusion edge flipped 1; whole-table conclusion changed 1; Acc conjunct of hinv replaced by True 1); \
    each is one well-typed change, signature/defeq rejection, NOT a semantic counterexample. Unused extra hypotheses (weaker) and ill-typed proposals are not counted."

run_cmd Lean.Elab.Command.liftTermElabM do
  let ns : List Name := [``hunf_of_kitInv, ``factsOf_all_of_kitInv, ``ordCallees_transport]
  for n in ns do checkAxioms n
  logInfo m!"GEN5 KITINV AXIOMS OK: {ns.length} theorems, standard axioms only"

run_cmd Lean.Elab.Command.liftTermElabM do
  let roots : List Name := [``hunf_of_kitInv, ``factsOf_all_of_kitInv, ``ordCallees_transport]
  let c ← closureRun roots
  let f := forbiddenIn c
  unless f.isEmpty do throwError "GEN5 KITINV CLOSURE FAILED: forbidden constants {f}"
  let t1 ← (do let _ ← closureRun [`Tests.Gen5.SemKitInvCheck.NoSuchConstant]; pure false) <|> pure true
  unless t1 do throwError "GEN5 KITINV CONTROL FAILED: unknown root did not throw"
  for r in [``Lean.ofReduceBool, ``sorryAx] do
    let f ← detect [r]
    unless f.contains r do throwError "GEN5 KITINV CONTROL FAILED: forbidden root {r} not flagged (got {f})"
  Tests.Gen5.SemExtCheck.withFixtures fun r3 r4 rc mv mt hv4 => do
    let env ← getEnv
    let t3 ← (do let _ ← closureRun [r3]; pure false) <|> pure true
    unless t3 do throwError "GEN5 KITINV CONTROL FAILED: unknown helper value did not throw"
    let (_, c3) ← (closureOf env r3).run {}
    unless c3.missing == #[mv] do throwError "GEN5 KITINV CONTROL FAILED: helper-value case reported {c3.missing}, intended {mv}"
    let t4 ← (do let _ ← closureRun [r4]; pure false) <|> pure true
    unless t4 do throwError "GEN5 KITINV CONTROL FAILED: unknown helper type did not throw"
    let (_, c4) ← (closureOf env r4).run {}
    unless c4.missing == #[mt] do throwError "GEN5 KITINV CONTROL FAILED: helper-type case reported {c4.missing}, intended {mt}"
    unless c4.seen.contains hv4 do throwError "GEN5 KITINV CONTROL FAILED: helper-type path does not pass through Hv4"
    let cc ← closureRun [rc]
    unless cc.missing.isEmpty && (forbiddenIn cc).isEmpty do throwError "GEN5 KITINV CONTROL FAILED: clean fixture flagged"
  logInfo m!"GEN5 KITINV CLOSURE OK: {c.seen.toList.length} constants over {roots.length} roots, no forbidden constant; controls: unknown root throws, \
    2 forbidden roots flagged, unknown helper VALUE names Mv, unknown helper TYPE names Mt via Hv4, clean fixture passes (fixtures inside withoutModifyingEnv)"

run_cmd Lean.Elab.Command.liftTermElabM do
  let reach (root : Name) (need : List Name) : MetaM Nat := do
    let c ← closureRun [root]
    for n in need do
      unless c.seen.contains n do throwError "GEN5 KITINV REACH FAILED: {root} does not reach {n}"
    pure need.length
  let a ← reach ``hunf_of_kitInv [``genSemVia, ``genSemI, ``mem_ordCallees, ``ordCallees_transport]
  let b ← reach ``factsOf_all_of_kitInv [``factsOf_all_of_acc_unfold, ``hunf_of_kitInv]
  logInfo m!"GEN5 KITINV REACH OK: {a + b} required constants reached over 2 roots"

#print axioms factsOf_all_of_kitInv

end Tests.Gen5.SemKitInvCheck

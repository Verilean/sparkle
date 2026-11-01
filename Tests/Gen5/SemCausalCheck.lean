import Tools.ShippingGen5SemCausal
import Tests.Gen5.SemExtCheck
set_option autoImplicit false
-- Pod incremental build (kjob lake build Tests.Gen5.SemCausalCheck) exit 0 on this content before commit (712 jobs); clean issue-linked build smu9v-c0d18b96 exit 0 (712 jobs), approved at c0d18b96. No sorry/axiom/native_decide.
/-! # DG-SEM U6A check (Tools/ShippingGen5SemCausal.lean; scripts/gen5/DG_SEM_FREEZE_P6C.md §3.3)

* TYPE    — `SrcCausal`/`CalleesCausal` compared BY BODY and the three theorems by statement against `Exp*`, written here from the
            sentences of §3.1-§3.2 (`HCausalOf` is written out in its unfolded `∀`-form), with the same comparer `checkExpected`/`cmpTele`.
* MUTANT  — well-typed single-change mutants rejected by the same comparer: signature/defeq rejection, NOT a semantic counterexample.
* AXIOMS / CLOSURE / REACH — as in `Tests/Gen5/SemExtPkgCheck.lean`; fixtures (`withFixtures`) live only inside `withoutModifyingEnv`. -/
namespace Tests.Gen5.SemCausalCheck
open Lean Meta Elab
open Tools.ShippingGen5Sem Tests.Gen3.ExpectedType Tests.Gen5.SemGenCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Compiler.Elab Sparkle.Compiler.MachInstOrigin Tools.ShippingMachineAuto Tools.ShippingMachineDenote

/-! ## Expected (from the sentences of the freeze, not from the implementation) -/
noncomputable def ExpSrcCausal := fun {ι : Type} {dom : ι → DomainConfig} (s : SemPkg ι dom) =>
  ∀ (i : ι) (A A' : Nat → Signal (dom i) Bool) (B B' : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
    (∀ c, c ≤ t → (∀ j, (A j).val c = (A' j).val c) ∧ ∀ j n, (B j n).val c = (B' j n).val c) →
    (s.src i A B).map (fun f => f t) = (s.src i A' B').map (fun f => f t)

noncomputable def ExpCalleesCausal := fun {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (d : MachineData) =>
  ∀ k ∈ ordCallees d, ∀ s, Q (d.shape.insts[k]).1 = some s → SrcCausal s

def ExpMemRead : Prop := ∀ {D : DomainConfig} {aw dw : Nat} (cb : Bool)
    (A A' : Signal D (BitVec aw)) (Dd Dd' : Signal D (BitVec dw)) (E E' : Signal D Bool) (R R' : Signal D (BitVec aw)) (t : Nat)
    (hA : ∀ c, c ≤ t → A.val c = A'.val c) (hD : ∀ c, c ≤ t → Dd.val c = Dd'.val c)
    (hE : ∀ c, c ≤ t → E.val c = E'.val c) (hR : ∀ c, c ≤ t → R.val c = R'.val c),
    (Tools.ShippingMachineMemLinked.memRead cb A Dd E R).val t =
      (Tools.ShippingMachineMemLinked.memRead cb A' Dd' E' R').val t

def ExpExtStage : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (g : GenIn)
    (hQ : CalleesCausal Q g.d) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S S' : Signal (dom i) (HList (tys g.d.ss))) (n : Nat) (t : Nat)
    (hS : ∀ c, c ≤ t → S.val c = S'.val c),
    (∀ p, ((ExtStage Q g i bools bits S n).1 p).val t = ((ExtStage Q g i bools bits S' n).1 p).val t) ∧
    (∀ p w, ((ExtStage Q g i bools bits S n).2 p w).val t = ((ExtStage Q g i bools bits S' n).2 p w).val t)

def ExpExtCausal : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (g : GenIn)
    (hQ : CalleesCausal Q g.d) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S S' : Signal (dom i) (HList (tys g.d.ss))) (t : Nat),
    (∀ c, c ≤ t → S.val c = S'.val c) →
    (∀ p w, (extOf Q g i bools bits S p w).val t = (extOf Q g i bools bits S' p w).val t) ∧
    (∀ p, (extBOf Q g i bools bits S p).val t = (extBOf Q g i bools bits S' p).val t)

/-- the statement in the folded form (binder telescope), `ExpExtCausal` above is its unfolded `∀`-form (checked by `isDefEq` below) -/
def ExpExtCausalFolded : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (g : GenIn)
    (hQ : CalleesCausal Q g.d), Tools.ShippingSeqParentLemmas.HCausalOf g.d dom (extOf Q g) (extBOf Q g)

/-! ## Mutants (each one well-typed single change) -/
noncomputable def MutSrcLt := fun {ι : Type} {dom : ι → DomainConfig} (s : SemPkg ι dom) =>
  ∀ (i : ι) (A A' : Nat → Signal (dom i) Bool) (B B' : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
    (∀ c, c < t → (∀ j, (A j).val c = (A' j).val c) ∧ ∀ j n, (B j n).val c = (B' j n).val c) →
    (s.src i A B).map (fun f => f t) = (s.src i A' B').map (fun f => f t)
noncomputable def MutCalleesAllFin := fun {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (d : MachineData) =>
  ∀ k : Fin d.shape.insts.length, ∀ s, Q (d.shape.insts[k]).1 = some s → SrcCausal s
def MutMemRlt : Prop := ∀ {D : DomainConfig} {aw dw : Nat} (cb : Bool)
    (A A' : Signal D (BitVec aw)) (Dd Dd' : Signal D (BitVec dw)) (E E' : Signal D Bool) (R R' : Signal D (BitVec aw)) (t : Nat)
    (hA : ∀ c, c ≤ t → A.val c = A'.val c) (hD : ∀ c, c ≤ t → Dd.val c = Dd'.val c)
    (hE : ∀ c, c ≤ t → E.val c = E'.val c) (hR : ∀ c, c < t → R.val c = R'.val c),
    (Tools.ShippingMachineMemLinked.memRead cb A Dd E R).val t =
      (Tools.ShippingMachineMemLinked.memRead cb A' Dd' E' R').val t
def MutMemNoHR : Prop := ∀ {D : DomainConfig} {aw dw : Nat} (cb : Bool)
    (A A' : Signal D (BitVec aw)) (Dd Dd' : Signal D (BitVec dw)) (E E' : Signal D Bool) (R R' : Signal D (BitVec aw)) (t : Nat)
    (hA : ∀ c, c ≤ t → A.val c = A'.val c) (hD : ∀ c, c ≤ t → Dd.val c = Dd'.val c)
    (hE : ∀ c, c ≤ t → E.val c = E'.val c),
    (Tools.ShippingMachineMemLinked.memRead cb A Dd E R).val t =
      (Tools.ShippingMachineMemLinked.memRead cb A' Dd' E' R').val t
def MutStageHSlt : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (g : GenIn)
    (hQ : CalleesCausal Q g.d) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S S' : Signal (dom i) (HList (tys g.d.ss))) (n : Nat) (t : Nat)
    (hS : ∀ c, c < t → S.val c = S'.val c),
    (∀ p, ((ExtStage Q g i bools bits S n).1 p).val t = ((ExtStage Q g i bools bits S' n).1 p).val t) ∧
    (∀ p w, ((ExtStage Q g i bools bits S n).2 p w).val t = ((ExtStage Q g i bools bits S' n).2 p w).val t)
def MutStageNoHQ : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S S' : Signal (dom i) (HList (tys g.d.ss))) (n : Nat) (t : Nat)
    (hS : ∀ c, c ≤ t → S.val c = S'.val c),
    (∀ p, ((ExtStage Q g i bools bits S n).1 p).val t = ((ExtStage Q g i bools bits S' n).1 p).val t) ∧
    (∀ p w, ((ExtStage Q g i bools bits S n).2 p w).val t = ((ExtStage Q g i bools bits S' n).2 p w).val t)
def MutStageDropBits : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (g : GenIn)
    (hQ : CalleesCausal Q g.d) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S S' : Signal (dom i) (HList (tys g.d.ss))) (n : Nat) (t : Nat)
    (hS : ∀ c, c ≤ t → S.val c = S'.val c),
    (∀ p, ((ExtStage Q g i bools bits S n).1 p).val t = ((ExtStage Q g i bools bits S' n).1 p).val t)
def MutExtNoHQ : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (g : GenIn)
    (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S S' : Signal (dom i) (HList (tys g.d.ss))) (t : Nat),
    (∀ c, c ≤ t → S.val c = S'.val c) →
    (∀ p w, (extOf Q g i bools bits S p w).val t = (extOf Q g i bools bits S' p w).val t) ∧
    (∀ p, (extBOf Q g i bools bits S p).val t = (extBOf Q g i bools bits S' p).val t)
def MutExtDropBools : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (g : GenIn)
    (hQ : CalleesCausal Q g.d) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S S' : Signal (dom i) (HList (tys g.d.ss))) (t : Nat),
    (∀ c, c ≤ t → S.val c = S'.val c) →
    (∀ p w, (extOf Q g i bools bits S p w).val t = (extOf Q g i bools bits S' p w).val t)

run_cmd Lean.Elab.Command.liftTermElabM do
  let a1 ← stmtOf ``SrcCausal
  cmpTele "SrcCausal (body)" a1 (← stmtOf ``ExpSrcCausal)
  let a2 ← stmtOf ``CalleesCausal
  cmpTele "CalleesCausal (body)" a2 (← stmtOf ``ExpCalleesCausal)
  logInfo m!"GEN5 CAUSAL DEFBODY OK 2 definitions (SrcCausal, CalleesCausal) against ExpSrcCausal, ExpCalleesCausal (bodies compared)"
  checkExpected ``memRead_causal ``ExpMemRead
  checkExpected ``ExtStage_causal ``ExpExtStage
  checkExpected ``extCausal_of_genSem ``ExpExtCausalFolded
  unless (← isDefEq (← stmtOf ``extCausal_of_genSem) (← stmtOf ``ExpExtCausal)) do
    throwError "GEN5 CAUSAL CHECK FAILED: extCausal_of_genSem is not defeq to the unfolded ∀-form ExpExtCausal"
  logInfo m!"GEN5 CAUSAL TYPE OK extCausal_of_genSem defeq to the unfolded HCausalOf ∀-form (ExpExtCausal)"
  let mutants : List (Name × Name) :=
    [(``SrcCausal, ``MutSrcLt), (``CalleesCausal, ``MutCalleesAllFin),
     (``memRead_causal, ``MutMemRlt), (``memRead_causal, ``MutMemNoHR),
     (``ExtStage_causal, ``MutStageHSlt), (``ExtStage_causal, ``MutStageNoHQ), (``ExtStage_causal, ``MutStageDropBits),
     (``extCausal_of_genSem, ``MutExtNoHQ), (``extCausal_of_genSem, ``MutExtDropBools)]
  for (t, m) in mutants do checkMutant t m
  logInfo m!"GEN5 CAUSAL COUNTS: TYPE 3 theorems + DEFBODY 2 definitions; MUTANT {mutants.length} total \
    (2 on definitions: c<t, Fin-all instead of ordCallees; 7 on theorems: bound ≤→< 2, hypothesis dropped 3 (hR, hQ in ExtStage, hQ in extCausal), \
    conclusion conjunct dropped 2 (ExtStage bits, HCausalOf bools)); signature/defeq rejections, NOT semantic counterexamples."

run_cmd Lean.Elab.Command.liftTermElabM do
  let ns : List Name := [``SrcCausal, ``CalleesCausal, ``memRead_causal, ``ExtStage_causal, ``extCausal_of_genSem]
  for n in ns do checkAxioms n
  logInfo m!"GEN5 CAUSAL AXIOMS OK: {ns.length} constants (2 definitions, 3 theorems), standard axioms only"

run_cmd Lean.Elab.Command.liftTermElabM do
  let roots : List Name := [``extCausal_of_genSem, ``ExtStage_causal, ``memRead_causal]
  let c ← closureRun roots
  let f := forbiddenIn c
  unless f.isEmpty do throwError "GEN5 CAUSAL CLOSURE FAILED: forbidden constants {f}"
  let t1 ← (do let _ ← closureRun [`Tests.Gen5.SemCausalCheck.NoSuchConstant]; pure false) <|> pure true
  unless t1 do throwError "GEN5 CAUSAL CONTROL FAILED: unknown root did not throw"
  for r in [``Lean.ofReduceBool, ``sorryAx] do
    let f ← detect [r]
    unless f.contains r do throwError "GEN5 CAUSAL CONTROL FAILED: forbidden root {r} not flagged (got {f})"
  Tests.Gen5.SemExtCheck.withFixtures fun r3 r4 rc mv mt hv4 => do
    let env ← getEnv
    let t3 ← (do let _ ← closureRun [r3]; pure false) <|> pure true
    unless t3 do throwError "GEN5 CAUSAL CONTROL FAILED: unknown helper value did not throw"
    let (_, c3) ← (closureOf env r3).run {}
    unless c3.missing == #[mv] do throwError "GEN5 CAUSAL CONTROL FAILED: helper-value case reported {c3.missing}, intended {mv}"
    let t4 ← (do let _ ← closureRun [r4]; pure false) <|> pure true
    unless t4 do throwError "GEN5 CAUSAL CONTROL FAILED: unknown helper type did not throw"
    let (_, c4) ← (closureOf env r4).run {}
    unless c4.missing == #[mt] do throwError "GEN5 CAUSAL CONTROL FAILED: helper-type case reported {c4.missing}, intended {mt}"
    unless c4.seen.contains hv4 do throwError "GEN5 CAUSAL CONTROL FAILED: helper-type path does not pass through Hv4"
    let cc ← closureRun [rc]
    unless cc.missing.isEmpty && (forbiddenIn cc).isEmpty do throwError "GEN5 CAUSAL CONTROL FAILED: clean fixture flagged"
  logInfo m!"GEN5 CAUSAL CLOSURE OK: {c.seen.toList.length} constants over {roots.length} roots, no forbidden constant; controls: unknown root throws, \
    2 forbidden roots flagged, unknown helper VALUE names Mv, unknown helper TYPE names Mt via Hv4, clean fixture passes (fixtures inside withoutModifyingEnv)"

run_cmd Lean.Elab.Command.liftTermElabM do
  let reach (root : Name) (need : List Name) : MetaM Nat := do
    let c ← closureRun [root]
    for n in need do
      unless c.seen.contains n do throwError "GEN5 CAUSAL REACH FAILED: {root} does not reach {n}"
    pure need.length
  let a ← reach ``extCausal_of_genSem [``ExtStage_causal, ``CalleesCausal]
  let b ← reach ``ExtStage_causal [``memRead_causal, ``calleeOut, ``callOut]
  let d ← reach ``memRead_causal [``Tools.ShippingMachineCausal.memState_congr]
  logInfo m!"GEN5 CAUSAL REACH OK: {a + b + d} required constants reached over 3 roots"

#print axioms extCausal_of_genSem

end Tests.Gen5.SemCausalCheck

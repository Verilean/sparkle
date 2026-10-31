import Lean
import Tools.ShippingGen5DCEntry
import Tests.Gen3.ExpectedType
import Tests.Gen5.DeclConnectCheck
set_option autoImplicit false
-- Built at 160ba5d174b3b055a526917964cf358a7d9a019f (agent build `kjob lake build Tests.Gen5.DCEntryCheck` exit 0, 746 jobs; NOT clean-built, clean build by coder pending). Counts by category: TYPE 3 (statements; 2 self-comparison positive controls not counted), MUTANT 13 (PostT1 3, run 5, o1 5), CONJ 5 (PostT1 2, run 2, o1 1), AXIOMS 3, CLOSURE 3 + 1 missing-owner control + 1 forbidden-mention control + 1 clean control. All signature/defeq rejections under withReducible, NOT semantic counterexamples.

/-! # DC-CONNECT U-POST: checks (scripts/gen5/DC_CONNECT_SUPPLY_SURVEY.md §4, §5)

TYPE: `Exp*` written from the prose of §4 (not copied from the Lean statement), compared by `Tests.Gen3.ExpectedType.checkExpected`
(`PostT1` is pinned by its own check and used as a constant elsewhere). MUTANT: well-typed ONE-change variants rejected by the SAME comparator
(`checkMutant`), both run under `withReducible` (reducible transparency; abbrevs unfold, definitions such as `RunsTo`/`PostT1` do not) -- signature/defeq rejections, NOT semantic counterexamples. CONJ: variants that drop one conjunct of the conclusion, counted
separately. A variant that is not well-typed is not counted. AXIOMS. CLOSURE: reuses the `DeclConnectCheck` walker (an unknown name FAILS). -/
open Lean Meta Tests.Gen3.ExpectedType Sparkle.Compiler.Elab Tools.ShippingGen5DCEntry
open Tools.ShippingEntrySoundness (RunsTo)

namespace Tests.Gen5.DCEntryCheck

abbrev Mod := Sparkle.IR.AST.Module
abbrev Dsg := Sparkle.IR.AST.Design
abbrev drop := Sparkle.IR.ZeroWidth.dropZeroWidthModule

/-! ## PostT1: the two-way post-processing relation of `T1Stmt`'s hypothesis -/
def ExpPostT1 := fun (b raw : Mod) => b = drop raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked (drop raw)
/-- MUTANT: `mergeChecked` -> `mergeDuplicates` (the form of `synthesizeCombinational_reads`). -/
def MutPostMerge := fun (b raw : Mod) => b = drop raw ∨ b = Sparkle.IR.RegDedup.mergeDuplicates (drop raw)
/-- MUTANT: the merge without the cleanup. -/
def MutPostNoDrop := fun (b raw : Mod) => b = drop raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked raw
/-- CONJ-like (disjunct dropped): only the cleanup. -/
def MutPostOnlyDrop := fun (b raw : Mod) => b = drop raw
/-- CONJ-like (disjunct dropped): only the merge. -/
def MutPostOnlyMerge := fun (b raw : Mod) => b = Sparkle.IR.RefineCheck.mergeChecked (drop raw)
/-- MUTANT: arguments swapped (the module is the argument that gets cleaned). -/
def MutPostSwap := fun (b raw : Mod) => raw = drop b ∨ raw = Sparkle.IR.RefineCheck.mergeChecked (drop b)

/-! ## the run statement: a successful default run has a core run of the same declaration and its raw module relates by `PostT1` -/
def ExpPostRun : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostT1 b raw
/-- CONJ: the `PostT1` conjunct dropped. -/
def ConjPostRunNoPost : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1
/-- CONJ: the core-run conjunct dropped. -/
def ConjPostRunNoCore : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    ∃ (raw : Mod) (_D : Dsg) (_w1 : Void IO.RealWorld), PostT1 b raw
/-- MUTANT: `∃ raw` -> `∀ raw`. -/
def MutPostRunForall : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    ∀ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostT1 b raw
/-- MUTANT: the core run with the gate flag `true`. -/
def MutPostRunFlag : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] true) mctx mref cctx cref w (raw, D) w1 ∧ PostT1 b raw
/-- MUTANT: `PostT1` arguments swapped. -/
def MutPostRunSwap : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostT1 raw b
/-- MUTANT: the core run starts at the end world `w'`. -/
def MutPostRunWorld : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w' (raw, D) w1 ∧ PostT1 b raw
/-- MUTANT: the premise is the parametric route (a claim this unit does not prove). -/
def MutPostRunParam : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinationalWithParameters declName []) mctx mref cctx cref w (b, D') w'),
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostT1 b raw

/-! ## O1 on the default route (no `ReflectsAll` / `Laws` / `parameters` binder) -/
def ExpO1 : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {declName : Name} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w'),
    ∃ raw, PostT1 b raw
/-- MUTANT: `∃ raw` -> `∀ raw`. -/
def MutO1Forall : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {declName : Name} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w'),
    ∀ raw, PostT1 b raw
/-- MUTANT: arguments swapped. -/
def MutO1Swap : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {declName : Name} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w'),
    ∃ raw, PostT1 raw b
/-- MUTANT: parametric route premise. -/
def MutO1Param : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {declName : Name} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D : Dsg}
    (h : RunsTo (synthesizeCombinationalWithParameters declName []) mctx mref cctx cref w (b, D) w'),
    ∃ raw, PostT1 b raw
/-- MUTANT: the premise is the core run, not the default entry. -/
def MutO1Core : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {declName : Name} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D : Dsg}
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (b, D) w'),
    ∃ raw, PostT1 b raw
/-- CONJ-like: the conclusion weakened to `True` (the `PostT1` content dropped). -/
def ConjO1NoPost : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {declName : Name} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w'),
    ∃ _raw : Mod, True
/-- MUTANT: with the unused `ReflectsAll`-style extra premise reintroduced (a different binder list, as in the pre-cleanup freeze). -/
def MutO1ExtraBinder : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {parameters : List (String × Nat)}
    {declName : Name} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w'),
    ∃ raw, PostT1 b raw

/-- (target, expected, mutants) -/
def table : List (Name × Name × List Name) :=
  [(``PostT1, ``ExpPostT1, [``MutPostMerge, ``MutPostNoDrop, ``MutPostSwap]),
   (``synthesizeCombinational_postT1, ``ExpPostRun,
     [``MutPostRunForall, ``MutPostRunFlag, ``MutPostRunSwap, ``MutPostRunWorld, ``MutPostRunParam]),
   (``o1_default, ``ExpO1, [``MutO1Forall, ``MutO1Swap, ``MutO1Param, ``MutO1Core, ``MutO1ExtraBinder])]

/-- conjunct/disjunct-drop variants, counted as category CONJ -/
def conjTable : List (Name × List Name) :=
  [(``PostT1, [``MutPostOnlyDrop, ``MutPostOnlyMerge]),
   (``synthesizeCombinational_postT1, [``ConjPostRunNoPost, ``ConjPostRunNoCore]),
   (``o1_default, [``ConjO1NoPost])]

/-! ## closure -/
open Tests.Gen5.DeclConnectCheck (reach violations)

def required : List Name :=
  [``synthesizeCombinational, ``synthesizeCombinationalCore, ``Sparkle.IR.RefineCheck.mergeChecked,
   ``Sparkle.IR.ZeroWidth.dropZeroWidthModule, ``RunsTo]

def missing (r : Tests.Gen5.DeclConnectCheck.Reach) : List Name := required.filter (!r.seen.contains ·)

/-- negative control: the relation without the merge disjunct (owner constant `mergeChecked` must be missing) -/
def negNoMerge (b raw : Mod) : Prop := b = drop raw
/-- clean control: the relation itself -/
def cleanPost (b raw : Mod) : Prop := PostT1 b raw

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut nType : Nat := 0
  let mut nMut : Nat := 0
  let mut nConj : Nat := 0
  -- positive control: the comparator accepts a copy of the expected statement
  withReducible <| checkExpected ``ExpPostT1 ``ExpPostT1
  withReducible <| checkExpected ``ExpO1 ``ExpO1
  for (thm, e, ms) in table do
    withReducible <| checkExpected thm e
    nType := nType + 1
    for m in ms do
      withReducible <| checkMutant thm m
      nMut := nMut + 1
  for (thm, ms) in conjTable do
    let some (_, e, _) := table.find? (·.1 == thm) | throwError "no expected for {thm}"
    withReducible <| checkExpected thm e
    for m in ms do
      withReducible <| checkMutant thm m
      nConj := nConj + 1
  for n in [``PostT1, ``synthesizeCombinational_postT1, ``o1_default] do checkAxioms n
  -- CLOSURE
  for n in [``PostT1, ``synthesizeCombinational_postT1, ``o1_default] do
    let r ← reach env n
    unless r.axioms.isEmpty do throwError "CLOSURE FAILED {n}: axiom constants {r.axioms}"
    let v := violations env r
    unless v.isEmpty do throwError "CLOSURE FAILED {n}: forbidden {v}"
    logInfo m!"CLOSURE OK {n}: reached {r.seen.size}, opaque {r.opaques}, owner constants missing {missing r}"
  let rt ← reach env ``synthesizeCombinational_postT1
  unless (missing rt).isEmpty do throwError "CLOSURE FAILED synthesizeCombinational_postT1: owner constants not reached {missing rt}"
  let rp ← reach env ``PostT1
  if (missing rp).contains ``Sparkle.IR.RefineCheck.mergeChecked then
    throwError "CLOSURE FAILED PostT1: mergeChecked not reached"
  let rn ← reach env ``negNoMerge
  unless (missing rn).contains ``Sparkle.IR.RefineCheck.mergeChecked do throwError "CLOSURE CONTROL NOT DETECTED negNoMerge"
  logInfo m!"CLOSURE CONTROL DETECTED negNoMerge: missing {missing rn}"
  let rc ← reach env ``cleanPost
  unless (violations env rc).isEmpty && (rc.seen.contains ``Sparkle.IR.RefineCheck.mergeChecked) do throwError "CLOSURE CLEAN CONTROL FAILED"
  logInfo m!"CLOSURE CLEAN CONTROL OK cleanPost"
  for c in [``Tests.Gen5.DeclConnectCheck.negDirect] do
    if (violations env (← reach env c)).isEmpty then throwError "CLOSURE CONTROL NOT DETECTED {c} (forbidden mention)"
    logInfo m!"CLOSURE CONTROL DETECTED {c} (forbidden mention)"
  logInfo m!"COUNTS: TYPE {nType} (one per statement: PostT1, synthesizeCombinational_postT1, o1_default; plus 2 positive-control self-comparisons not counted), MUTANT {nMut} (well-typed single change, signature/defeq rejection, not semantic counterexamples), CONJ {nConj} (conjunct/disjunct drops), AXIOMS 3, CLOSURE 3 + 2 controls + 1 clean control"
  logInfo m!"STATUS: NOT supplied by this unit: S3 parametric route, S7 EnvFrame/coreHead, S9 reader/core tie, S10-S14 (O2, O3, DeclConnect rows, DCF, ReflectsAll), D/D' transport, O3 arbitrary raw vs core-witness raw, NV-witness"

end Tests.Gen5.DCEntryCheck

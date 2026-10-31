import Lean
import Tools.ShippingGen5DCEntryD
import Tests.Gen3.ExpectedType
import Tests.Gen5.DeclConnectCheck
set_option autoImplicit false
-- Built: issue-linked build dc11v-4523f2e9 `kjob lake build Tests.Gen5.DCEntryDCheck` exit 0, 747 jobs, approved at 4523f2e9 (incremental build). Counts by category: TYPE 4 (statements; 2 self-comparison positive controls not counted), MUTANT 16 (topMap 3, PostEntry 6, run 5, projection 2), CONJ 6 (PostEntry 3, run 2, projection 1), AXIOMS 4, CLOSURE 4 roots + 1 missing-owner control + 1 forbidden-mention control + 1 clean control + unknown-name fixture (1 detect + 1 clean). All signature/defeq rejections under withReducible, NOT semantic counterexamples.

/-! # DC-CONNECT U-POSTD: checks (scripts/gen5/DC_CONNECT_SUPPLY_SURVEY.md §9, §10)

TYPE: `Exp*` written from the prose of §9 (the top module is rewritten by name; `b` and `D'` are tied to the same branch of the
entry), not copied from the Lean statements, compared by `Tests.Gen3.ExpectedType.checkExpected`. MUTANT: well-typed ONE-change
variants rejected by the SAME comparator (`checkMutant`), both under `withReducible` -- signature/defeq rejections, NOT semantic
counterexamples. CONJ: variants that drop a conjunct/disjunct of a statement, counted separately. A variant that is not well-typed
is not counted. AXIOMS. CLOSURE: the `DeclConnectCheck` walker (an unknown name FAILS; the root is judged itself); each root has only
the reach requirement it needs; new fixture for a helper whose TYPE alone mentions an unknown name. -/
open Lean Meta Tests.Gen3.ExpectedType Sparkle.Compiler.Elab Tools.ShippingGen5DCEntryD
open Tools.ShippingEntrySoundness (RunsTo)

namespace Tests.Gen5.DCEntryDCheck

abbrev Mod := Sparkle.IR.AST.Module
abbrev Dsg := Sparkle.IR.AST.Design
abbrev drop := Sparkle.IR.ZeroWidth.dropZeroWidthModule
abbrev mchk := Sparkle.IR.RefineCheck.mergeChecked

/-! ## topMap: only the modules named like `m` are rewritten -/
def ExpTopMap := fun (f : Mod → Mod) (m : Mod) (d : Dsg) =>
  ({ d with modules := d.modules.map fun x => if x.name == m.name then f x else x } : Dsg)
/-- MUTANT: the key test negated (the OTHER modules are rewritten). -/
def MutTopNeg := fun (f : Mod → Mod) (m : Mod) (d : Dsg) =>
  ({ d with modules := d.modules.map fun x => if x.name != m.name then f x else x } : Dsg)
/-- MUTANT: every module is rewritten (the key compares `x` with itself). -/
def MutTopAll := fun (f : Mod → Mod) (m : Mod) (d : Dsg) =>
  ({ d with modules := d.modules.map fun x => if x.name == x.name then f x else x } : Dsg)
/-- MUTANT: the rewriting function is ignored. -/
def MutTopNoF := fun (_f : Mod → Mod) (m : Mod) (d : Dsg) =>
  ({ d with modules := d.modules.map fun x => if x.name == m.name then x else x } : Dsg)

/-! ## PostEntry: module and design in the SAME branch -/
def ExpPostEntry := fun (b raw : Mod) (D D' : Dsg) =>
  (b = drop raw ∧ D' = topMap drop raw D) ∨
  (b = mchk (drop raw) ∧ D' = topMap mchk raw (topMap drop raw D))
/-- MUTANT: `mergeChecked` -> `mergeDuplicates` (both `Module → Module`). -/
def MutPEMerge := fun (b raw : Mod) (D D' : Dsg) =>
  (b = drop raw ∧ D' = topMap drop raw D) ∨
  (b = Sparkle.IR.RegDedup.mergeDuplicates (drop raw) ∧ D' = topMap Sparkle.IR.RegDedup.mergeDuplicates raw (topMap drop raw D))
/-- MUTANT: the inner `topMap drop` dropped in the merge branch. -/
def MutPENoInner := fun (b raw : Mod) (D D' : Dsg) =>
  (b = drop raw ∧ D' = topMap drop raw D) ∨
  (b = mchk (drop raw) ∧ D' = topMap mchk raw D)
/-- MUTANT: `D` and `D'` swapped. -/
def MutPESwapD := fun (b raw : Mod) (D D' : Dsg) =>
  (b = drop raw ∧ D = topMap drop raw D') ∨
  (b = mchk (drop raw) ∧ D = topMap mchk raw (topMap drop raw D'))
/-- MUTANT: the first branch joins `b` and `D'` by `∨` (the joint branch dropped there). -/
def MutPEOr1 := fun (b raw : Mod) (D D' : Dsg) =>
  (b = drop raw ∨ D' = topMap drop raw D) ∨
  (b = mchk (drop raw) ∧ D' = topMap mchk raw (topMap drop raw D))
/-- MUTANT: the second branch joins `b` and `D'` by `∨`. -/
def MutPEOr2 := fun (b raw : Mod) (D D' : Dsg) =>
  (b = drop raw ∧ D' = topMap drop raw D) ∨
  (b = mchk (drop raw) ∨ D' = topMap mchk raw (topMap drop raw D))
/-- MUTANT: the top module is identified by `b` instead of `raw`. -/
def MutPEKey := fun (b raw : Mod) (D D' : Dsg) =>
  (b = drop raw ∧ D' = topMap drop b D) ∨
  (b = mchk (drop raw) ∧ D' = topMap mchk b (topMap drop b D))
/-- CONJ: the design conjunct dropped in both branches (= `PostT1`). -/
def ConjPENoD := fun (b raw : Mod) (_D _D' : Dsg) => b = drop raw ∨ b = mchk (drop raw)
/-- CONJ: only the cleanup branch. -/
def ConjPEOnlyDrop := fun (b raw : Mod) (D D' : Dsg) => b = drop raw ∧ D' = topMap drop raw D
/-- CONJ: only the merge branch. -/
def ConjPEOnlyMerge := fun (b raw : Mod) (D D' : Dsg) =>
  b = mchk (drop raw) ∧ D' = topMap mchk raw (topMap drop raw D)

/-! ## the run statement -/
def ExpPostEntryRun : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D'
/-- MUTANT: the core run with the gate flag `true`. -/
def MutRunFlag : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] true) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D'
/-- MUTANT: `D` and `D'` swapped in the relation. -/
def MutRunSwapD : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D' D
/-- MUTANT: the core run starts at the end world. -/
def MutRunWorld : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w' (raw, D) w1 ∧ PostEntry b raw D D'
/-- MUTANT: `∃ raw` -> `∀ raw`. -/
def MutRunForall : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    ∀ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D'
/-- MUTANT: the premise is the parametric route (a claim this unit does not prove). -/
def MutRunParam : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinationalWithParameters declName []) mctx mref cctx cref w (b, D') w'),
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D'
/-- CONJ: the relation conjunct dropped. -/
def ConjRunNoPE : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1
/-- CONJ: the core-run conjunct dropped. -/
def ConjRunNoCore : Prop := ∀ {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Mod} {D' : Dsg}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    ∃ (raw : Mod) (D : Dsg) (_w1 : Void IO.RealWorld), PostEntry b raw D D'

/-! ## PostEntry implies the U-POST relation -/
def ExpPEPostT1 : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    (h : PostEntry b raw D D'), Tools.ShippingGen5DCEntry.PostT1 b raw
/-- MUTANT: the arguments of `PostT1` swapped. -/
def MutPEPostT1Swap : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    (h : PostEntry b raw D D'), Tools.ShippingGen5DCEntry.PostT1 raw b
/-- MUTANT: the premise is the design-only reading (`D` and `D'` swapped in the hypothesis). -/
def MutPEPostT1SwapD : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    (h : PostEntry b raw D' D), Tools.ShippingGen5DCEntry.PostT1 b raw
/-- CONJ: the conclusion weakened to `True`. -/
def ConjPEPostT1True : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    (h : PostEntry b raw D D'), True

/-- (target, expected, mutants) -/
def table : List (Name × Name × List Name) :=
  [(``topMap, ``ExpTopMap, [``MutTopNeg, ``MutTopAll, ``MutTopNoF]),
   (``PostEntry, ``ExpPostEntry, [``MutPEMerge, ``MutPENoInner, ``MutPESwapD, ``MutPEOr1, ``MutPEOr2, ``MutPEKey]),
   (``synthesizeCombinational_postEntry, ``ExpPostEntryRun,
     [``MutRunFlag, ``MutRunSwapD, ``MutRunWorld, ``MutRunForall, ``MutRunParam]),
   (``postEntry_postT1, ``ExpPEPostT1, [``MutPEPostT1Swap, ``MutPEPostT1SwapD])]

/-- conjunct/disjunct-drop variants, counted as category CONJ -/
def conjTable : List (Name × List Name) :=
  [(``PostEntry, [``ConjPENoD, ``ConjPEOnlyDrop, ``ConjPEOnlyMerge]),
   (``synthesizeCombinational_postEntry, [``ConjRunNoPE, ``ConjRunNoCore]),
   (``postEntry_postT1, [``ConjPEPostT1True])]

/-! ## closure -/
open Tests.Gen5.DeclConnectCheck (reach reachRaw violations)

/-- per root: ONLY the owner constants that root needs to reach -/
def requiredOf : List (Name × List Name) :=
  [(``topMap, [``Sparkle.IR.AST.Design]),
   (``PostEntry, [``topMap, ``Sparkle.IR.RefineCheck.mergeChecked, ``Sparkle.IR.ZeroWidth.dropZeroWidthModule]),
   (``synthesizeCombinational_postEntry, [``synthesizeCombinational, ``synthesizeCombinationalCore, ``RunsTo, ``PostEntry]),
   (``postEntry_postT1, [``PostEntry, ``Tools.ShippingGen5DCEntry.PostT1])]

def missingOf (r : Tests.Gen5.DeclConnectCheck.Reach) (req : List Name) : List Name := req.filter (!r.seen.contains ·)

/-- negative control: a relation that never mentions the merge (the requirement `mergeChecked` of `PostEntry`'s kind must be detected as missing) -/
def negNoMerge (b raw : Mod) (D D' : Dsg) : Prop := b = drop raw ∧ D' = topMap drop raw D
/-- clean control: the relation itself, through a helper -/
def cleanPE (b raw : Mod) (D D' : Dsg) : Prop := PostEntry b raw D D'

/-- unknown-name fixture: ONLY the helper's TYPE mentions a name known to no environment -/
def ghostTy : Name := `Tests.Gen5.DCEntryDCheck.ghost_unknown_in_type
def fixEnv (env : Environment) : MetaM Environment := do
  let add (env : Environment) (n : Name) (ty v : Lean.Expr) : MetaM Environment :=
    match env.addDeclCore 0 (.defnDecl { name := n, levelParams := [], type := ty, value := v, hints := .abbrev, safety := .safe }) none (doCheck := false) with
    | .ok e => pure e
    | .error _ => throwError "fixture environment: could not add {n}"
  let nat := Lean.mkConst ``Nat
  let env ← add env `fixHelperTy (Lean.mkConst ghostTy) (Lean.mkConst ``Nat.zero)
  let env ← add env `fixRootUsesHelper nat (Lean.mkApp (Lean.mkConst ``id [1]) (Lean.mkConst `fixHelperTy))
  add env `fixRootClean nat (Lean.mkConst ``Nat.zero)

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut nType : Nat := 0
  let mut nMut : Nat := 0
  let mut nConj : Nat := 0
  -- positive controls: the comparator accepts a copy of the expected statement
  withReducible <| checkExpected ``ExpTopMap ``ExpTopMap
  withReducible <| checkExpected ``ExpPostEntry ``ExpPostEntry
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
  let targets := [``topMap, ``PostEntry, ``synthesizeCombinational_postEntry, ``postEntry_postT1]
  for n in targets do checkAxioms n
  -- CLOSURE
  let mut nClosure : Nat := 0
  for (n, req) in requiredOf do
    let r ← reach env n
    unless r.axioms.isEmpty do throwError "CLOSURE FAILED {n}: axiom constants {r.axioms}"
    let v := violations env r
    unless v.isEmpty do throwError "CLOSURE FAILED {n}: forbidden {v}"
    let miss := missingOf r req
    unless miss.isEmpty do throwError "CLOSURE FAILED {n}: required constants not reached {miss}"
    nClosure := nClosure + 1
    logInfo m!"CLOSURE OK {n}: reached {r.seen.size}, opaque {r.opaques}, required {req}"
  let rn ← reach env ``negNoMerge
  unless (missingOf rn [``Sparkle.IR.RefineCheck.mergeChecked]).contains ``Sparkle.IR.RefineCheck.mergeChecked do
    throwError "CLOSURE CONTROL NOT DETECTED negNoMerge"
  logInfo m!"CLOSURE CONTROL DETECTED negNoMerge (mergeChecked not reached)"
  let rc ← reach env ``cleanPE
  unless (violations env rc).isEmpty && (missingOf rc [``Sparkle.IR.RefineCheck.mergeChecked, ``topMap]).isEmpty do
    throwError "CLOSURE CLEAN CONTROL FAILED"
  logInfo m!"CLOSURE CLEAN CONTROL OK cleanPE"
  unless (violations env (← reach env ``Tests.Gen5.DeclConnectCheck.negDirect)).isEmpty == false do
    throwError "CLOSURE CONTROL NOT DETECTED negDirect (forbidden mention)"
  logInfo m!"CLOSURE CONTROL DETECTED negDirect (forbidden mention)"
  -- unknown-name fixture, in a scratch environment (the real one is restored by withoutModifyingEnv)
  withoutModifyingEnv do
    setEnv (← fixEnv env)
    let envF ← getEnv
    let raw ← reachRaw envF `fixRootUsesHelper
    unless raw.unknown == #[ghostTy] do
      throwError "UNKNOWN-NAME FIXTURE: expected exactly {ghostTy} unknown (the helper's TYPE), got {raw.unknown}"
    let failed ← try let _ ← reach envF `fixRootUsesHelper; pure false catch _ => pure true
    unless failed do throwError "UNKNOWN-NAME FIXTURE: `reach` did not fail"
    logInfo m!"UNKNOWN-NAME FIXTURE DETECTED fixRootUsesHelper (only fixHelperTy's type is unknown: {raw.unknown}), reach fails"
    let rcl ← reach envF `fixRootClean
    unless rcl.unknown.isEmpty do throwError "UNKNOWN-NAME FIXTURE CLEAN CONTROL FAILED"
    logInfo m!"UNKNOWN-NAME FIXTURE CLEAN CONTROL OK fixRootClean"
  unless (env.find? `fixHelperTy).isNone do throwError "fixture leaked into the environment"
  logInfo m!"COUNTS: TYPE {nType} (one per statement: topMap, PostEntry, synthesizeCombinational_postEntry, postEntry_postT1; plus 2 positive-control self-comparisons not counted), MUTANT {nMut} (well-typed single change, signature/defeq rejection under withReducible, not semantic counterexamples), CONJ {nConj} (conjunct/disjunct/conclusion drops), AXIOMS {targets.length}, CLOSURE {nClosure} roots + 1 missing-owner control + 1 forbidden-mention control + 1 clean control + unknown-name fixture (1 detect + 1 clean)"
  logInfo m!"STATUS: NOT supplied by this unit: (a2) TopShips D->D' transport, (a3) post-processed top semantics, (b1) O3 arbitrary raw identification, (b2) O3 restatement, (c5) reader/core tie, (c6) hall/ReadsAt at later worlds, (c7) O2/DeclConnect rows, S3 parametric route, S12 DCF, S14 ReflectsAll"

end Tests.Gen5.DCEntryDCheck

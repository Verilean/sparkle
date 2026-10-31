import Lean
import Tools.ShippingGen5DCEntryN
import Tests.Gen3.ExpectedType
import Tests.Gen5.DeclConnectCheck
set_option autoImplicit false
-- NOT BUILT: U-TOPNAME checks (scripts/gen5/DC_CONNECT_SUPPLY_SURVEY.md §15). No clean issue-linked build yet.

/-! # DC-CONNECT U-TOPNAME: checks (survey §13, §15)

TYPE: `Exp*` written from the prose of §13 (each post-processor keeps the module name; a lookup at a name other than the rewritten one
is unchanged; the lookup at the rewritten name is the `map f` of the old one), compared by `checkExpected` under `withReducible`.
MUTANT: well-typed ONE-change variants rejected by the SAME comparator -- signature/defeq rejections, NOT semantic counterexamples.
CONJ: variants dropping a conjunct of `postEntry_lookup_ne`. A variant that is not well-typed is not counted. AXIOMS. CLOSURE: the
`DeclConnectCheck` walker (unknown name FAILS; root judged itself); each root requires only what it needs; unknown-name fixture. -/
open Lean Meta Tests.Gen3.ExpectedType Tools.ShippingGen5DCEntryN
open Tools.ShippingGen5DCEntryD (topMap PostEntry)

namespace Tests.Gen5.DCEntryNCheck

abbrev Mod := Sparkle.IR.AST.Module
abbrev Dsg := Sparkle.IR.AST.Design
abbrev drop := Sparkle.IR.ZeroWidth.dropZeroWidthModule
abbrev mchk := Sparkle.IR.RefineCheck.mergeChecked
abbrev mdup := Sparkle.IR.RegDedup.mergeDuplicates
abbrev byName := Sparkle.IR.Machine.moduleByName
abbrev cmap := Tools.ShippingMachineLinked.childMap

/-! ## name preservation -/
def ExpDropName : Prop := ∀ (m : Mod), (drop m).name = m.name
def MutDropNameMdup : Prop := ∀ (m : Mod), (drop m).name = (mdup m).name
def ExpDupName : Prop := ∀ (m : Mod), (mdup m).name = m.name
def MutDupNameChk : Prop := ∀ (m : Mod), (mdup m).name = (mchk m).name
def ExpChkName : Prop := ∀ (m : Mod), (mchk m).name = m.name
def MutChkNameDrop : Prop := ∀ (m : Mod), (mchk m).name = (drop m).name

/-! ## lookups -/
def ExpNe : Prop := ∀ {f : Mod → Mod} {m : Mod} {d : Dsg} {mn : String},
  ∀ (hf : ∀ x, (f x).name = x.name) (hne : mn ≠ m.name), byName (topMap f m d).modules mn = byName d.modules mn
/-- MUTANT: the hypothesis `mn ≠ m.name` dropped (an unconditional claim). -/
def MutNeNoHne : Prop := ∀ {f : Mod → Mod} {m : Mod} {d : Dsg} {mn : String},
  (∀ x, (f x).name = x.name) → byName (topMap f m d).modules mn = byName d.modules mn
/-- MUTANT: `mn ≠ m.name` replaced by `mn = m.name`. -/
def MutNeHneEq : Prop := ∀ {f : Mod → Mod} {m : Mod} {d : Dsg} {mn : String},
  (∀ x, (f x).name = x.name) → mn = m.name → byName (topMap f m d).modules mn = byName d.modules mn
/-- MUTANT: the name-preservation hypothesis `hf` dropped. -/
def MutNeNoHf : Prop := ∀ {f : Mod → Mod} {m : Mod} {d : Dsg} {mn : String},
  mn ≠ m.name → byName (topMap f m d).modules mn = byName d.modules mn

def ExpSelf : Prop := ∀ {f : Mod → Mod} {m : Mod} {d : Dsg},
  ∀ (hf : ∀ x, (f x).name = x.name), byName (topMap f m d).modules m.name = (byName d.modules m.name).map f
/-- MUTANT: `.map f` dropped. -/
def MutSelfNoMap : Prop := ∀ {f : Mod → Mod} {m : Mod} {d : Dsg},
  (∀ x, (f x).name = x.name) → byName (topMap f m d).modules m.name = byName d.modules m.name
/-- MUTANT: `hf` dropped. -/
def MutSelfNoHf : Prop := ∀ {f : Mod → Mod} {m : Mod} {d : Dsg},
  byName (topMap f m d).modules m.name = (byName d.modules m.name).map f

def ExpChildNe : Prop := ∀ {f : Mod → Mod} {m : Mod} {d : Dsg} {mn : String},
  ∀ (hf : ∀ x, (f x).name = x.name) (hne : mn ≠ m.name), cmap (topMap f m d).modules mn = cmap d.modules mn
/-- MUTANT: `hne` dropped. -/
def MutChildNoHne : Prop := ∀ {f : Mod → Mod} {m : Mod} {d : Dsg} {mn : String},
  (∀ x, (f x).name = x.name) → cmap (topMap f m d).modules mn = cmap d.modules mn
/-- MUTANT: `childMap` replaced by `moduleByName` (the lookup lemma's statement). -/
def MutChildAsLookup : Prop := ∀ {f : Mod → Mod} {m : Mod} {d : Dsg} {mn : String},
  (∀ x, (f x).name = x.name) → mn ≠ m.name → byName (topMap f m d).modules mn = byName d.modules mn
/-- MUTANT: `hf` dropped. -/
def MutChildNoHf : Prop := ∀ {f : Mod → Mod} {m : Mod} {d : Dsg} {mn : String},
  mn ≠ m.name → cmap (topMap f m d).modules mn = cmap d.modules mn

def ExpEntryNe : Prop := ∀ {b raw : Mod} {D D' : Dsg} {mn : String},
  ∀ (h : PostEntry b raw D D') (hne : mn ≠ raw.name),
    byName D'.modules mn = byName D.modules mn ∧ cmap D'.modules mn = cmap D.modules mn
/-- MUTANT: `D` and `D'` swapped in the conclusion. -/
def MutEntrySwap : Prop := ∀ {b raw : Mod} {D D' : Dsg} {mn : String},
  PostEntry b raw D D' → mn ≠ raw.name →
    byName D.modules mn = byName D'.modules mn ∧ cmap D.modules mn = cmap D'.modules mn
/-- MUTANT: `hne` dropped. -/
def MutEntryNoHne : Prop := ∀ {b raw : Mod} {D D' : Dsg} {mn : String},
  PostEntry b raw D D' →
    byName D'.modules mn = byName D.modules mn ∧ cmap D'.modules mn = cmap D.modules mn
/-- MUTANT: the `PostEntry` hypothesis dropped. -/
def MutEntryNoPE : Prop := ∀ {raw : Mod} {D D' : Dsg} {mn : String},
  mn ≠ raw.name →
    byName D'.modules mn = byName D.modules mn ∧ cmap D'.modules mn = cmap D.modules mn
/-- MUTANT: the key is `b.name` instead of `raw.name`. -/
def MutEntryKeyB : Prop := ∀ {b raw : Mod} {D D' : Dsg} {mn : String},
  PostEntry b raw D D' → mn ≠ b.name →
    byName D'.modules mn = byName D.modules mn ∧ cmap D'.modules mn = cmap D.modules mn
/-- CONJ: only the `moduleByName` conjunct. -/
def ConjEntryLookup : Prop := ∀ {b raw : Mod} {D D' : Dsg} {mn : String},
  PostEntry b raw D D' → mn ≠ raw.name → byName D'.modules mn = byName D.modules mn
/-- CONJ: only the `childMap` conjunct. -/
def ConjEntryChild : Prop := ∀ {b raw : Mod} {D D' : Dsg} {mn : String},
  PostEntry b raw D D' → mn ≠ raw.name → cmap D'.modules mn = cmap D.modules mn

/-- (target, expected, mutants) -/
def table : List (Name × Name × List Name) :=
  [(``dropZeroWidthModule_name, ``ExpDropName, [``MutDropNameMdup]),
   (``mergeDuplicates_name, ``ExpDupName, [``MutDupNameChk]),
   (``mergeChecked_name, ``ExpChkName, [``MutChkNameDrop]),
   (``moduleByName_topMap_ne, ``ExpNe, [``MutNeNoHne, ``MutNeHneEq, ``MutNeNoHf]),
   (``moduleByName_topMap_self, ``ExpSelf, [``MutSelfNoMap, ``MutSelfNoHf]),
   (``childMap_topMap_ne, ``ExpChildNe, [``MutChildNoHne, ``MutChildAsLookup, ``MutChildNoHf]),
   (``postEntry_lookup_ne, ``ExpEntryNe, [``MutEntrySwap, ``MutEntryNoHne, ``MutEntryNoPE, ``MutEntryKeyB])]

def conjTable : List (Name × List Name) :=
  [(``postEntry_lookup_ne, [``ConjEntryLookup, ``ConjEntryChild])]

/-! ## closure -/
open Tests.Gen5.DeclConnectCheck (reach reachRaw violations)

/-- per root: ONLY the constants that root needs to reach -/
def requiredOf : List (Name × List Name) :=
  [(``dropZeroWidthModule_name, [``Sparkle.IR.ZeroWidth.dropZeroWidthModule]),
   (``mergeDuplicates_name, [``Sparkle.IR.RegDedup.mergeDuplicates]),
   (``mergeChecked_name, [``Sparkle.IR.RefineCheck.mergeChecked]),
   (``moduleByName_topMap_ne, [``topMap, ``Sparkle.IR.Machine.moduleByName]),
   (``moduleByName_topMap_self, [``topMap, ``Sparkle.IR.Machine.moduleByName]),
   (``childMap_topMap_ne, [``topMap, ``Tools.ShippingMachineLinked.childMap]),
   (``postEntry_lookup_ne, [``PostEntry, ``topMap])]

def missingOf (r : Tests.Gen5.DeclConnectCheck.Reach) (req : List Name) : List Name := req.filter (!r.seen.contains ·)

/-- negative control: a statement that never mentions `topMap` (the requirement must be detected as missing) -/
def negNoTop (d : Dsg) (mn : String) : Prop := byName d.modules mn = byName d.modules mn
/-- clean control: the lookup lemma's statement through a helper -/
def cleanNe (f : Mod → Mod) (m : Mod) (d : Dsg) (mn : String) : Prop :=
  byName (topMap f m d).modules mn = byName d.modules mn

/-- unknown-name fixture: ONLY the helper's TYPE mentions a name known to no environment -/
def ghostTy : Name := `Tests.Gen5.DCEntryNCheck.ghost_unknown_in_type
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
  withReducible <| checkExpected ``ExpNe ``ExpNe
  withReducible <| checkExpected ``ExpEntryNe ``ExpEntryNe
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
  let targets := table.map (·.1)
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
  let rn ← reach env ``negNoTop
  unless (missingOf rn [``topMap]).contains ``topMap do
    throwError "CLOSURE CONTROL NOT DETECTED negNoTop"
  logInfo m!"CLOSURE CONTROL DETECTED negNoTop (topMap not reached)"
  let rc ← reach env ``cleanNe
  unless (violations env rc).isEmpty && (missingOf rc [``topMap, ``Sparkle.IR.Machine.moduleByName]).isEmpty do
    throwError "CLOSURE CLEAN CONTROL FAILED"
  logInfo m!"CLOSURE CLEAN CONTROL OK cleanNe"
  unless (violations env (← reach env ``Tests.Gen5.DeclConnectCheck.negDirect)).isEmpty == false do
    throwError "CLOSURE CONTROL NOT DETECTED negDirect (forbidden mention)"
  logInfo m!"CLOSURE CONTROL DETECTED negDirect (forbidden mention)"
  -- unknown-name fixture, in a scratch environment (restored by withoutModifyingEnv)
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
  -- inspect the CURRENT environment (after `withoutModifyingEnv`)
  unless ((← getEnv).find? `fixHelperTy).isNone && ((← getEnv).find? `fixRootUsesHelper).isNone && ((← getEnv).find? `fixRootClean).isNone do
    throwError "fixture leaked into the environment"
  logInfo m!"COUNTS: TYPE {nType} (one per statement; plus 2 positive-control self-comparisons not counted), MUTANT {nMut} (well-typed single change, signature/defeq rejection under withReducible, not semantic counterexamples), CONJ {nConj} (conjunct drops of postEntry_lookup_ne), AXIOMS {targets.length}, CLOSURE {nClosure} roots + 1 missing-owner control + 1 forbidden-mention control + 1 clean control + unknown-name fixture (1 detect + 1 clean)"
  logInfo m!"STATUS: NOT supplied by this unit: (a2.4) TopShips/ResetNk D->D' transport (needs a no-descendant premise, not derived), (a3), (b1), (b2), (c4 import), (c5), (c6), (c7), S3, S12, S14"

end Tests.Gen5.DCEntryNCheck

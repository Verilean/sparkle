import Lean
import Tools.ShippingGen5DCEntryR
import Tests.Gen3.ExpectedType
import Tests.Gen5.DeclConnectCheck
set_option autoImplicit false
-- U-RESETN checks (scripts/gen5/DC_CONNECT_RESETN_FREEZE.md §4). Issue-linked clean build dc17v-1c948e47 exit 0 (749 jobs); approved at 1c948e47.
-- Counts: TYPE 3 (2 theorems + definition-equation pin) + 3 self-comparisons, MUT 15 + CONJ 2, AX 3.

/-! # DC-CONNECT U-RESETN: checks

TYPE: `ExpR1`/`ExpR2` written from the prose of §3 and `ExpPin` (the two equations of `NoRawBelow`) compared by
`Tests.Gen3.ExpectedType.checkExpected` under `withReducible`; the equation pin theorem `pinEq` is proved by `rfl`.
MUTANT: well-typed single-change variants rejected by the SAME comparator (`checkMutant`) -- signature/defeq rejections, NOT semantic
counterexamples; every variant below changes ONE component (none is a block change). CONJ: the two conjuncts of the `k+1` clause dropped
(counted separately). AXIOMS. CLOSURE: `DeclConnectCheck` walker (root judged itself, unknown name FAILS) and unknown-name fixtures. -/
open Lean Meta Tests.Gen3.ExpectedType
open Tools.ShippingGen5DCEntryR
open Tools.ShippingGen5DCEntryD (PostEntry)

namespace Tests.Gen5.DCEntryRCheck

abbrev Mod := Sparkle.IR.AST.Module
abbrev Dsg := Sparkle.IR.AST.Design

/-- EXPECTED: with lookup agreement away from rn and NoRawBelow at depth n, ResetN at depth n is the same on D and D'. -/
def ExpR1 : Prop := ∀ {D D' : Dsg} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (s : Tools.ShippingHierStateG.KT n),
      NoRawBelow D rn n mc →
      (Tools.ShippingMachineDepth.ResetN D n mc s ↔ Tools.ShippingMachineDepth.ResetN D' n mc s)

/-- MUTANT: lookup agreement premise dropped. -/
def MutR1NoHlk : Prop := ∀ {D D' : Dsg} {rn : String},
    ∀ (n : Nat) (mc : Mod) (s : Tools.ShippingHierStateG.KT n),
      NoRawBelow D rn n mc →
      (Tools.ShippingMachineDepth.ResetN D n mc s ↔ Tools.ShippingMachineDepth.ResetN D' n mc s)

/-- MUTANT: NoRawBelow hypothesis dropped. -/
def MutR1NoHno : Prop := ∀ {D D' : Dsg} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (s : Tools.ShippingHierStateG.KT n),
      (Tools.ShippingMachineDepth.ResetN D n mc s ↔ Tools.ShippingMachineDepth.ResetN D' n mc s)

/-- MUTANT: NoRawBelow at depth n+1. -/
def MutR1Depth : Prop := ∀ {D D' : Dsg} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (s : Tools.ShippingHierStateG.KT n),
      NoRawBelow D rn (n + 1) mc →
      (Tools.ShippingMachineDepth.ResetN D n mc s ↔ Tools.ShippingMachineDepth.ResetN D' n mc s)

/-- MUTANT: iff replaced by implication. -/
def MutR1Imp : Prop := ∀ {D D' : Dsg} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (s : Tools.ShippingHierStateG.KT n),
      NoRawBelow D rn n mc →
      (Tools.ShippingMachineDepth.ResetN D n mc s → Tools.ShippingMachineDepth.ResetN D' n mc s)

/-- MUTANT: D and D' swapped in the conclusion. -/
def MutR1Swap : Prop := ∀ {D D' : Dsg} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (s : Tools.ShippingHierStateG.KT n),
      NoRawBelow D rn n mc →
      (Tools.ShippingMachineDepth.ResetN D' n mc s ↔ Tools.ShippingMachineDepth.ResetN D n mc s)

/-- MUTANT: hlk for mn = rn instead of mn ≠ rn. -/
def MutR1Eq : Prop := ∀ {D D' : Dsg} {rn : String}
    (hlk : ∀ mn : String, mn = rn →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (s : Tools.ShippingHierStateG.KT n),
      NoRawBelow D rn n mc →
      (Tools.ShippingMachineDepth.ResetN D n mc s ↔ Tools.ShippingMachineDepth.ResetN D' n mc s)

/-- EXPECTED: for a PostEntry pair and NoRawBelow at depth n+1 for the raw top, ResetNk at depth n is the same on D and D'. -/
def ExpR2 : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    (h : PostEntry b raw D D') (n : Nat)
    (kids : String → Tools.ShippingHierStateG.KT n)
    (hno : NoRawBelow D raw.name (n + 1) raw),
    Tools.ShippingMachineShipsDepth.ResetNk n raw D kids ↔ Tools.ShippingMachineShipsDepth.ResetNk n raw D' kids

/-- MUTANT: NoRawBelow dropped. -/
def MutR2NoHno : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    (h : PostEntry b raw D D') (n : Nat)
    (kids : String → Tools.ShippingHierStateG.KT n),
    Tools.ShippingMachineShipsDepth.ResetNk n raw D kids ↔ Tools.ShippingMachineShipsDepth.ResetNk n raw D' kids

/-- MUTANT: NoRawBelow at depth n. -/
def MutR2Depth : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    (h : PostEntry b raw D D') (n : Nat)
    (kids : String → Tools.ShippingHierStateG.KT n)
    (hno : NoRawBelow D raw.name n raw),
    Tools.ShippingMachineShipsDepth.ResetNk n raw D kids ↔ Tools.ShippingMachineShipsDepth.ResetNk n raw D' kids

/-- MUTANT: iff replaced by implication. -/
def MutR2Imp : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    (h : PostEntry b raw D D') (n : Nat)
    (kids : String → Tools.ShippingHierStateG.KT n)
    (hno : NoRawBelow D raw.name (n + 1) raw),
    Tools.ShippingMachineShipsDepth.ResetNk n raw D kids → Tools.ShippingMachineShipsDepth.ResetNk n raw D' kids

/-- MUTANT: D and D' swapped in the conclusion. -/
def MutR2Swap : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    (h : PostEntry b raw D D') (n : Nat)
    (kids : String → Tools.ShippingHierStateG.KT n)
    (hno : NoRawBelow D raw.name (n + 1) raw),
    Tools.ShippingMachineShipsDepth.ResetNk n raw D' kids ↔ Tools.ShippingMachineShipsDepth.ResetNk n raw D kids

/-- MUTANT: raw.name replaced by b.name in hno. -/
def MutR2B : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    (h : PostEntry b raw D D') (n : Nat)
    (kids : String → Tools.ShippingHierStateG.KT n)
    (hno : NoRawBelow D b.name (n + 1) raw),
    Tools.ShippingMachineShipsDepth.ResetNk n raw D kids ↔ Tools.ShippingMachineShipsDepth.ResetNk n raw D' kids

/-- MUTANT: PostEntry b raw D' D. -/
def MutR2PE : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    (h : PostEntry b raw D' D) (n : Nat)
    (kids : String → Tools.ShippingHierStateG.KT n)
    (hno : NoRawBelow D raw.name (n + 1) raw),
    Tools.ShippingMachineShipsDepth.ResetNk n raw D kids ↔ Tools.ShippingMachineShipsDepth.ResetNk n raw D' kids

/-- EXPECTED (definition equations from the prose): depth 0 reads nothing; depth k+1 asks every instance in the body to have mn ≠ rn, and every instance whose lookup in D succeeds to satisfy depth k. -/
def ExpPin : Prop := ∀ (D : Dsg) (rn : String) (mc : Mod),
    NoRawBelow D rn 0 mc = True ∧
    ∀ (k : Nat), NoRawBelow D rn (k + 1) mc =
      ((∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body → mn ≠ rn) ∧
      (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) (mc' : Mod),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body →
        Sparkle.IR.Machine.moduleByName D.modules mn = some mc' → NoRawBelow D rn k mc'))
/-- MUTANT (definition): mn = rn. -/
def MutPinEq : Prop := ∀ (D : Dsg) (rn : String) (mc : Mod),
    NoRawBelow D rn 0 mc = True ∧
    ∀ (k : Nat), NoRawBelow D rn (k + 1) mc =
      ((∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body → mn = rn) ∧
      (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) (mc' : Mod),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body →
        Sparkle.IR.Machine.moduleByName D.modules mn = some mc' → NoRawBelow D rn k mc'))
/-- MUTANT (definition): recursion at depth k+1. -/
def MutPinDepth : Prop := ∀ (D : Dsg) (rn : String) (mc : Mod),
    NoRawBelow D rn 0 mc = True ∧
    ∀ (k : Nat), NoRawBelow D rn (k + 1) mc =
      ((∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body → mn ≠ rn) ∧
      (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) (mc' : Mod),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body →
        Sparkle.IR.Machine.moduleByName D.modules mn = some mc' → NoRawBelow D rn (k + 1) mc'))
/-- MUTANT (definition): depth 0 is False. -/
def MutPinZero : Prop := ∀ (D : Dsg) (rn : String) (mc : Mod),
    NoRawBelow D rn 0 mc = False ∧
    ∀ (k : Nat), NoRawBelow D rn (k + 1) mc =
      ((∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body → mn ≠ rn) ∧
      (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) (mc' : Mod),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body →
        Sparkle.IR.Machine.moduleByName D.modules mn = some mc' → NoRawBelow D rn k mc'))
/-- CONJ (definition): first conjunct dropped. -/
def ConjPinNoNe : Prop := ∀ (D : Dsg) (rn : String) (mc : Mod),
    NoRawBelow D rn 0 mc = True ∧
    ∀ (k : Nat), NoRawBelow D rn (k + 1) mc =
      ((∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) (mc' : Mod),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body →
        Sparkle.IR.Machine.moduleByName D.modules mn = some mc' → NoRawBelow D rn k mc'))
/-- CONJ (definition): second conjunct dropped. -/
def ConjPinNoRec : Prop := ∀ (D : Dsg) (rn : String) (mc : Mod),
    NoRawBelow D rn 0 mc = True ∧
    ∀ (k : Nat), NoRawBelow D rn (k + 1) mc =
      ((∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body → mn ≠ rn))

/-- the two defining equations of `NoRawBelow`, by `rfl` -/
theorem pinEq : ∀ (D : Dsg) (rn : String) (mc : Mod),
    NoRawBelow D rn 0 mc = True ∧
    ∀ (k : Nat), NoRawBelow D rn (k + 1) mc =
      ((∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body → mn ≠ rn) ∧
      (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) (mc' : Mod),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body →
        Sparkle.IR.Machine.moduleByName D.modules mn = some mc' → NoRawBelow D rn k mc')) :=
  fun _ _ _ => ⟨rfl, fun _ => rfl⟩

/-- (target, expected, mutants) -/
def table : List (Name × Name × List Name) :=
  [(``resetN_transport, ``ExpR1, [``MutR1NoHlk, ``MutR1NoHno, ``MutR1Depth, ``MutR1Imp, ``MutR1Swap, ``MutR1Eq]),
   (``resetNk_transport, ``ExpR2, [``MutR2NoHno, ``MutR2Depth, ``MutR2Imp, ``MutR2Swap, ``MutR2B, ``MutR2PE]),
   (``pinEq, ``ExpPin, [``MutPinEq, ``MutPinDepth, ``MutPinZero, ``ConjPinNoNe, ``ConjPinNoRec])]

/-! ## closure -/
open Tests.Gen5.DeclConnectCheck (reach reachRaw violations)

def requiredOf : List (Name × List Name) :=
  [(``resetN_transport, [``Tools.ShippingMachineDepth.ResetN, ``NoRawBelow, ``Sparkle.IR.Machine.moduleByName]),
   (``resetNk_transport, [``Tools.ShippingMachineShipsDepth.ResetNk, ``PostEntry,
      ``Tools.ShippingGen5DCEntryN.postEntry_lookup_ne, ``NoRawBelow])]

def missingOf (r : Tests.Gen5.DeclConnectCheck.Reach) (req : List Name) : List Name := req.filter (!r.seen.contains ·)

/-- negative control: mentions `ResetNk` but never the lookup lemma -/
def negNoLemma (n : Nat) (m : Mod) (D : Dsg) (kids : String → Tools.ShippingHierStateG.KT n) : Prop :=
  Tools.ShippingMachineShipsDepth.ResetNk n m D kids
/-- clean control: `resetN_transport` through a helper -/
theorem cleanR {D D' : Dsg} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn → Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn)
    (n : Nat) (mc : Mod) (s : Tools.ShippingHierStateG.KT n) (h : NoRawBelow D rn n mc) :
    Tools.ShippingMachineDepth.ResetN D n mc s ↔ Tools.ShippingMachineDepth.ResetN D' n mc s := resetN_transport hlk n mc s h

def ghostTy : Name := `Tests.Gen5.DCEntryRCheck.ghost_unknown_in_type
def ghostVal : Name := `Tests.Gen5.DCEntryRCheck.ghost_unknown_in_value
def fixEnv (env : Environment) : MetaM Environment := do
  let add (env : Environment) (n : Name) (ty v : Lean.Expr) : MetaM Environment :=
    match env.addDeclCore 0 (.defnDecl { name := n, levelParams := [], type := ty, value := v, hints := .abbrev, safety := .safe }) none (doCheck := false) with
    | .ok e => pure e
    | .error _ => throwError "fixture environment: could not add {n}"
  let nat := Lean.mkConst ``Nat
  let env ← add env `fixHelperTy (Lean.mkConst ghostTy) (Lean.mkConst ``Nat.zero)
  let env ← add env `fixHelperVal nat (Lean.mkConst ghostVal)
  let env ← add env `fixRootUsesTy nat (Lean.mkApp (Lean.mkConst ``id [1]) (Lean.mkConst `fixHelperTy))
  let env ← add env `fixRootUsesVal nat (Lean.mkApp (Lean.mkConst ``id [1]) (Lean.mkConst `fixHelperVal))
  add env `fixRootClean nat (Lean.mkConst ``Nat.zero)

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut nType : Nat := 0
  let mut nMut : Nat := 0
  let mut nConj : Nat := 0
  -- positive controls (self-comparison, not counted)
  withReducible <| checkExpected ``ExpR1 ``ExpR1
  withReducible <| checkExpected ``ExpR2 ``ExpR2
  withReducible <| checkExpected ``ExpPin ``ExpPin
  for (thm, e, ms) in table do
    withReducible <| checkExpected thm e
    nType := nType + 1
    for m in ms do
      withReducible <| checkMutant thm m
      if (m.toString.startsWith "Tests.Gen5.DCEntryRCheck.Conj") then nConj := nConj + 1 else nMut := nMut + 1
  let targets := [``resetN_transport, ``resetNk_transport, ``pinEq]
  for n in targets do checkAxioms n
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
  let lemmaN := ``Tools.ShippingGen5DCEntryN.postEntry_lookup_ne
  let rn ← reach env ``negNoLemma
  unless (missingOf rn [lemmaN]).contains lemmaN do
    throwError "CLOSURE CONTROL NOT DETECTED negNoLemma"
  logInfo m!"CLOSURE CONTROL DETECTED negNoLemma (lookup lemma not reached)"
  let rc ← reach env ``cleanR
  unless (violations env rc).isEmpty && (missingOf rc [``NoRawBelow, ``Tools.ShippingMachineDepth.ResetN]).isEmpty do
    throwError "CLOSURE CLEAN CONTROL FAILED"
  logInfo m!"CLOSURE CLEAN CONTROL OK cleanR"
  unless (violations env (← reach env ``Tests.Gen5.DeclConnectCheck.negDirect)).isEmpty == false do
    throwError "CLOSURE CONTROL NOT DETECTED negDirect (forbidden mention)"
  logInfo m!"CLOSURE CONTROL DETECTED negDirect (forbidden mention)"
  withoutModifyingEnv do
    setEnv (← fixEnv env)
    let envF ← getEnv
    for (root, ghost, what) in [(`fixRootUsesTy, ghostTy, "TYPE"), (`fixRootUsesVal, ghostVal, "VALUE")] do
      let raw ← reachRaw envF root
      unless raw.unknown == #[ghost] do
        throwError "UNKNOWN-NAME FIXTURE: expected exactly {ghost} unknown (the helper's {what}), got {raw.unknown}"
      let failed ← try let _ ← reach envF root; pure false catch _ => pure true
      unless failed do throwError "UNKNOWN-NAME FIXTURE: `reach` did not fail for {root}"
      logInfo m!"UNKNOWN-NAME FIXTURE DETECTED {root} (only the helper's {what} is unknown: {raw.unknown}), reach fails"
    let rcl ← reach envF `fixRootClean
    unless rcl.unknown.isEmpty do throwError "UNKNOWN-NAME FIXTURE CLEAN CONTROL FAILED"
    logInfo m!"UNKNOWN-NAME FIXTURE CLEAN CONTROL OK fixRootClean"
  let cur ← getEnv
  unless [`fixHelperTy, `fixHelperVal, `fixRootUsesTy, `fixRootUsesVal, `fixRootClean].all (cur.find? · |>.isNone) do
    throwError "fixture leaked into the environment"
  logInfo m!"COUNTS: TYPE {nType} (2 theorems + 1 definition-equation pin; plus 3 self-comparisons not counted), MUTANT {nMut} (well-typed single change, signature/defeq rejection under withReducible, not semantic counterexamples; no block changes), CONJ {nConj} (conjunct drops of the definition), AXIOMS {targets.length}, CLOSURE {nClosure} roots + 1 missing-requirement control + 1 forbidden-mention control + 1 clean control + unknown-name fixtures (2 detect: type-only, value-only; 1 clean)"
  logInfo m!"STATUS: NOT supplied by this unit: (a2.4b) the NoRawBelow premise (a strong sufficient condition, not derived), (a2.4c) run transport, TopShips on D', (a3), (b1), (b2), (c4 import), (c5), (c6), (c7), real EntryWitness, ReflectsAll, parametrised-route post-processing, Post adoption, FG"

end Tests.Gen5.DCEntryRCheck

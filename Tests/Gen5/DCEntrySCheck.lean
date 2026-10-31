import Lean
import Tools.ShippingGen5DCEntryS
import Tests.Gen3.ExpectedType
import Tests.Gen5.DeclConnectCheck
set_option autoImplicit false
-- U-NORAW checks (scripts/gen5/DC_CONNECT_NORAW_FREEZE.md §4). NOT BUILT (clean): agent incremental build only; base clean build dc17v-1c948e47 exit 0 (U-RESETN).
-- Counts (agent incremental build, 750 jobs): TYPE 5 (3 theorems + 2 source pins) + 3 self-comparisons, MUT 17 (single change) + BLOCK 1 + CONJ 2, AX 3, CLOSURE 3 roots.

/-! # DC-CONNECT U-NORAW: checks

TYPE: `ExpN1`/`ExpC1`/`ExpG1` written from the prose of §3, plus Expected types of the two source theorems (`closeInsts_acyclic`,
`closeInstsG_acyclic`) so a source drift is detected; compared by `checkExpected` under `withReducible`.
MUTANT: well-typed single-change variants rejected by the SAME comparator -- signature/defeq rejections, NOT semantic counterexamples.
The `rn -> mc.name` change inside `hD` of the freeze is NOT well-typed (`mc` is a later binder) and is not counted; the nearest well-typed
change (`rn -> g.name`, the binder of `hD` itself) is used. BLOCK: one variant changes two components at once and is counted separately. -/
open Lean Meta Tests.Gen3.ExpectedType
open Tools.ShippingGen5DCEntryR (NoRawBelow)
open Tools.ShippingHierMono (NoInstOf)

namespace Tests.Gen5.DCEntrySCheck

abbrev Mod := Sparkle.IR.AST.Module
abbrev Dsg := Sparkle.IR.AST.Design
abbrev Ch := List (Mod × Dsg)

/-- EXPECTED: if no module of D instantiates rn, and mc itself does not, then NoRawBelow D rn n mc for every depth n. -/
def ExpN1 : Prop := ∀ {D : Dsg} {rn : String}
    (hD : ∀ g ∈ D.modules, NoInstOf rn g.body),
    ∀ (n : Nat) (mc : Mod), NoInstOf rn mc.body → NoRawBelow D rn n mc
/-- MUTANT: hD dropped. -/
def MutN1NoHD : Prop := ∀ {D : Dsg} {rn : String},
    ∀ (n : Nat) (mc : Mod), NoInstOf rn mc.body → NoRawBelow D rn n mc
/-- MUTANT: hypothesis on mc.body dropped. -/
def MutN1NoHmc : Prop := ∀ {D : Dsg} {rn : String}
    (hD : ∀ g ∈ D.modules, NoInstOf rn g.body),
    ∀ (n : Nat) (mc : Mod), NoRawBelow D rn n mc
/-- MUTANT: in hD, rn replaced by g.name. -/
def MutN1GName : Prop := ∀ {D : Dsg} {rn : String}
    (hD : ∀ g ∈ D.modules, NoInstOf g.name g.body),
    ∀ (n : Nat) (mc : Mod), NoInstOf rn mc.body → NoRawBelow D rn n mc
/-- MUTANT: the mc.body hypothesis names "" instead of rn. -/
def MutN1Empty : Prop := ∀ {D : Dsg} {rn : String}
    (hD : ∀ g ∈ D.modules, NoInstOf rn g.body),
    ∀ (n : Nat) (mc : Mod), NoInstOf "" mc.body → NoRawBelow D rn n mc
/-- MUTANT: fixed depth 0. -/
def MutN1Depth0 : Prop := ∀ {D : Dsg} {rn : String}
    (hD : ∀ g ∈ D.modules, NoInstOf rn g.body),
    ∀ (n : Nat) (mc : Mod), NoInstOf rn mc.body → NoRawBelow D rn 0 mc
/-- MUTANT: conclusion NoInstOf only. -/
def MutN1Weak : Prop := ∀ {D : Dsg} {rn : String}
    (hD : ∀ g ∈ D.modules, NoInstOf rn g.body),
    ∀ (n : Nat) (mc : Mod), NoInstOf rn mc.body → NoInstOf rn mc.body

/-- EXPECTED: the closing's result module has NoRawBelow in its design at every depth. -/
def ExpC1 : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)),
    ∀ k : Nat, NoRawBelow d m.name k m
/-- MUTANT: m.name replaced by m₀.name. -/
def MutC1M0 : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)),
    ∀ k : Nat, NoRawBelow d m₀.name k m
/-- MUTANT: d replaced by d₀ in the conclusion. -/
def MutC1D0 : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)),
    ∀ k : Nat, NoRawBelow d₀ m.name k m
/-- MUTANT: closing result (m₀, d₀). -/
def MutC1Res : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m₀, d₀)),
    ∀ k : Nat, NoRawBelow d m.name k m
/-- MUTANT: fixed depth 0. -/
def MutC1Depth0 : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)),
    NoRawBelow d m.name 0 m
/-- MUTANT: conclusion NoInstOf only. -/
def MutC1Weak : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)),
    NoInstOf m.name m.body
/-- MUTANT: module argument m₀ in NoRawBelow. -/
def MutC1Mod0 : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)),
    ∀ k : Nat, NoRawBelow d m.name k m₀
/-- BLOCK MUTANT (two components): m.name -> m₀.name and d -> d₀. -/
def BlockC1 : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)),
    ∀ k : Nat, NoRawBelow d₀ m₀.name k m
/-- EXPECTED (general closing): same conclusion. -/
def ExpG1 : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)} {fields : List String}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d)),
    ∀ k : Nat, NoRawBelow d m.name k m
/-- MUTANT: m.name replaced by m₀.name. -/
def MutG1M0 : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)} {fields : List String}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d)),
    ∀ k : Nat, NoRawBelow d m₀.name k m
/-- MUTANT: d replaced by d₀. -/
def MutG1D0 : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)} {fields : List String}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d)),
    ∀ k : Nat, NoRawBelow d₀ m.name k m
/-- MUTANT: closing result (m₀, d₀). -/
def MutG1Res : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)} {fields : List String}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m₀, d₀)),
    ∀ k : Nat, NoRawBelow d m.name k m
/-- MUTANT: fixed depth 0. -/
def MutG1Depth0 : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)} {fields : List String}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d)),
    NoRawBelow d m.name 0 m
/-- MUTANT: conclusion NoInstOf only. -/
def MutG1Weak : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)} {fields : List String}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d)),
    NoInstOf m.name m.body
/-- EXPECTED (source, from the prose): the one-output closing keeps the module name, the result module does not instantiate itself, no module of the
result design instantiates the result module's name, and every module of every child design is found under its own name in the result design. -/
def ExpSrcC : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)),
    m.name = m₀.name ∧ NoInstOf m.name m.body ∧ (∀ g ∈ d.modules, NoInstOf m.name g.body) ∧
      ∀ c ∈ children, ∀ g ∈ c.2.modules, Sparkle.IR.Machine.moduleByName d.modules g.name = some g
/-- MUTANT (source): the child-consistency conjunct dropped. -/
def ConjSrcC : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)),
    m.name = m₀.name ∧ NoInstOf m.name m.body ∧ (∀ g ∈ d.modules, NoInstOf m.name g.body)
/-- EXPECTED (source, general closing): name kept, result module acyclic, no module of the result design instantiates its name. -/
def ExpSrcG : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)} {fields : List String}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d)),
    m.name = m₀.name ∧ NoInstOf m.name m.body ∧ (∀ g ∈ d.modules, NoInstOf m.name g.body)
/-- MUTANT (source): the design conjunct dropped. -/
def ConjSrcG : Prop := ∀ {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)} {fields : List String}
    {children : Ch} {m₀ : Mod} {d₀ : Dsg} {m : Mod} {d : Dsg}
    (h : Sparkle.IR.Machine.closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d)),
    m.name = m₀.name ∧ NoInstOf m.name m.body

/-- (target, expected, mutants, block mutants). Names starting `Conj` are counted as CONJ, `Block` as BLOCK. -/
def table : List (Name × Name × List Name) :=
  [(``Tools.ShippingGen5DCEntryS.noRawBelow_of_noInstOf, ``ExpN1,
      [``MutN1NoHD, ``MutN1NoHmc, ``MutN1GName, ``MutN1Empty, ``MutN1Depth0, ``MutN1Weak]),
   (``Tools.ShippingGen5DCEntryS.noRawBelow_of_closeInsts, ``ExpC1,
      [``MutC1M0, ``MutC1D0, ``MutC1Res, ``MutC1Depth0, ``MutC1Weak, ``MutC1Mod0, ``BlockC1]),
   (``Tools.ShippingGen5DCEntryS.noRawBelow_of_closeInstsG, ``ExpG1,
      [``MutG1M0, ``MutG1D0, ``MutG1Res, ``MutG1Depth0, ``MutG1Weak]),
   (``Tools.ShippingChildServe.closeInsts_acyclic, ``ExpSrcC, [``ConjSrcC]),
   (``Tools.ShippingChildServe.closeInstsG_acyclic, ``ExpSrcG, [``ConjSrcG])]

/-! ## closure -/
open Tests.Gen5.DeclConnectCheck (reach reachRaw violations)

def requiredOf : List (Name × List Name) :=
  [(``Tools.ShippingGen5DCEntryS.noRawBelow_of_noInstOf,
      [``NoRawBelow, ``NoInstOf, ``Sparkle.IR.Machine.moduleByName]),
   (``Tools.ShippingGen5DCEntryS.noRawBelow_of_closeInsts,
      [``Sparkle.IR.Machine.closeInsts, ``Tools.ShippingChildServe.closeInsts_acyclic,
       ``Tools.ShippingGen5DCEntryS.noRawBelow_of_noInstOf]),
   (``Tools.ShippingGen5DCEntryS.noRawBelow_of_closeInstsG,
      [``Sparkle.IR.Machine.closeInstsG, ``Tools.ShippingChildServe.closeInstsG_acyclic,
       ``Tools.ShippingGen5DCEntryS.noRawBelow_of_noInstOf])]

def missingOf (r : Tests.Gen5.DeclConnectCheck.Reach) (req : List Name) : List Name := req.filter (!r.seen.contains ·)

/-- negative control: mentions `closeInsts` but never the acyclicity lemma -/
def negNoLemma (nIn kI n : Nat) (portNames : List String) (insts : List (List Nat)) (children : Ch) (md : Mod × Dsg) :
    Option (Mod × Dsg) := Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children md
/-- clean control: `noRawBelow_of_noInstOf` through a helper -/
theorem cleanS {D : Dsg} {rn : String} (hD : ∀ g ∈ D.modules, NoInstOf rn g.body) (n : Nat) (mc : Mod)
    (h : NoInstOf rn mc.body) : NoRawBelow D rn n mc := Tools.ShippingGen5DCEntryS.noRawBelow_of_noInstOf hD n mc h

def ghostTy : Name := `Tests.Gen5.DCEntrySCheck.ghost_unknown_in_type
def ghostVal : Name := `Tests.Gen5.DCEntrySCheck.ghost_unknown_in_value
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
  let mut nBlock : Nat := 0
  let mut nConj : Nat := 0
  -- positive controls (self-comparison, not counted)
  withReducible <| checkExpected ``ExpN1 ``ExpN1
  withReducible <| checkExpected ``ExpC1 ``ExpC1
  withReducible <| checkExpected ``ExpG1 ``ExpG1
  for (thm, e, ms) in table do
    withReducible <| checkExpected thm e
    nType := nType + 1
    for m in ms do
      withReducible <| checkMutant thm m
      let s := m.toString
      if s.startsWith "Tests.Gen5.DCEntrySCheck.Conj" then nConj := nConj + 1
      else if s.startsWith "Tests.Gen5.DCEntrySCheck.Block" then nBlock := nBlock + 1
      else nMut := nMut + 1
  let targets := [``Tools.ShippingGen5DCEntryS.noRawBelow_of_noInstOf, ``Tools.ShippingGen5DCEntryS.noRawBelow_of_closeInsts,
    ``Tools.ShippingGen5DCEntryS.noRawBelow_of_closeInstsG]
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
  let lemmaN := ``Tools.ShippingChildServe.closeInsts_acyclic
  let rn ← reach env ``negNoLemma
  unless (missingOf rn [lemmaN]).contains lemmaN do
    throwError "CLOSURE CONTROL NOT DETECTED negNoLemma"
  logInfo m!"CLOSURE CONTROL DETECTED negNoLemma (acyclicity lemma not reached)"
  let rc ← reach env ``cleanS
  unless (violations env rc).isEmpty && (missingOf rc [``NoRawBelow, ``NoInstOf]).isEmpty do
    throwError "CLOSURE CLEAN CONTROL FAILED"
  logInfo m!"CLOSURE CLEAN CONTROL OK cleanS"
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
  logInfo m!"COUNTS: TYPE {nType} (3 theorems + 2 source-theorem type pins; plus 3 self-comparisons not counted), MUTANT {nMut} (well-typed single change, signature/defeq rejection under withReducible, not semantic counterexamples), BLOCK {nBlock} (two-component change, counted separately), CONJ {nConj} (conjunct drops of the source-theorem pins), AXIOMS {targets.length}, CLOSURE {nClosure} roots + 1 missing-requirement control + 1 forbidden-mention control + 1 clean control + unknown-name fixtures (2 detect: type-only, value-only; 1 clean)"
  logInfo m!"STATUS: NOT supplied by this unit: linking a core run's (raw, D) to the closeInsts/closeInstsG equation, (a2.4c) run transport, (a3), (b1), (b2), (c4 import), (c5), (c6), (c7), real EntryWitness, ReflectsAll, parametrised-route post-processing, Post adoption, FG"

end Tests.Gen5.DCEntrySCheck

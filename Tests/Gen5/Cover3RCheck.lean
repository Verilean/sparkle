import Tools.ShippingGen5Cover3R
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT by a clean build (agent build exit 0: Tests.Gen5.Cover3RCheck, TYPE 2+1 control, MUTANT 3, BINDERS 1, AXIOMS 2; clean build is the coder's). No sorry / axiom / native_decide.
/-! # C.CV-6 checks (Tools/ShippingGen5Cover3R.lean; scripts/gen5/CV6_FREEZE.md)

TYPE: Expected statements are written from the freeze text (`FullInv` / `ShapeAgree` are shared definitions, as in the old statement).
MUTANT: the OLD statement (with `hcb`) and one-point variants; rejection is by signature / defeq, NOT a semantic counterexample.
BINDERS: Prop binders of `rowB1_of_data` = those of `rowB1_of_inv` minus `hcb`, plus the input facts `hms hd`, compared mechanically.
AXIOMS: standard only. -/
namespace Tests.Gen5.Cover3RCheck
open Lean Meta
open Sparkle.Compiler.Elab Tools.ShippingMachineAuto Tools.ShippingGen5Cover3 Tools.ShippingGen5Sem
open Tools.ShippingGen5Cover3R Tests.Gen3.ExpectedType

def ExpHcb : Prop :=
  ∀ {sym : Bool} {params : List (String × Nat)} {dd : DefinitionVal} {senv senv' : StructEnv}
    {allow : Bool} {sp : MachineShape} {lvl : Lean.Expr → Nat} {d : MachineData}
    (hms : machineShape? sym params (.defnInfo dd) senv allow = some sp)
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl (.defnInfo dd) senv' sp = some d),
    ∀ k (hk : k < d.shape.insts.length),
      (d.shape.binders[kDOf d + k]?).map (·.2) = some (d.shape.insts[k]'hk).2.2

def ExpRowB1 : Prop :=
  ∀ {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv nDecl st)
    {sym : Bool} {params : List (String × Nat)} {dd : DefinitionVal} {senv senv' : StructEnv}
    {allow : Bool} {sp : MachineShape} {lvl : Lean.Expr → Nat}
    (hms : machineShape? sym params (.defnInfo dd) senv allow = some sp)
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl (.defnInfo dd) senv' sp = some d),
    ∀ k, k < d.shape.insts.length → callKind d k ≠ .domain

/-- Mutant: `hms` dropped (nothing ties `sp` to `dd`'s peel). -/
def MutNoHms : Prop :=
  ∀ {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv nDecl st)
    {dd : DefinitionVal} {senv' : StructEnv} {sp : MachineShape} {lvl : Lean.Expr → Nat}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl (.defnInfo dd) senv' sp = some d),
    ∀ k, k < d.shape.insts.length → callKind d k ≠ .domain

/-- Mutant: the old statement, `hcb` back and no input facts. -/
def MutOld : Prop :=
  ∀ {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv nDecl st)
    (hcb : ∀ k (hk : k < d.shape.insts.length), (d.shape.binders[kDOf d + k]?).map (·.2) = some (d.shape.insts[k]'hk).2.2),
    ∀ k, k < d.shape.insts.length → callKind d k ≠ .domain

/-- Mutant: conclusion `= .domain`. -/
def MutConcl : Prop :=
  ∀ {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv nDecl st)
    {sym : Bool} {params : List (String × Nat)} {dd : DefinitionVal} {senv senv' : StructEnv}
    {allow : Bool} {sp : MachineShape} {lvl : Lean.Expr → Nat}
    (hms : machineShape? sym params (.defnInfo dd) senv allow = some sp)
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl (.defnInfo dd) senv' sp = some d),
    ∀ k, k < d.shape.insts.length → callKind d k = .domain

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``hcb_of_data ``ExpHcb
  checkExpected ``rowB1_of_data ``ExpRowB1
  checkExpected ``Tools.ShippingGen5Cover3.rowB1_of_inv ``MutOld  -- control: comparator accepts the old statement for the old theorem
  logInfo m!"CV6 TYPE: 2 theorems against Expected; 1 control"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutant ``rowB1_of_data ``MutNoHms
  checkMutant ``rowB1_of_data ``MutOld
  checkMutant ``rowB1_of_data ``MutConcl
  logInfo m!"CV6 MUTANT: 3 rejected (signature/defeq, not semantic)"

def propBinders (thm : Name) : MetaM (List Name) := do
  forallTelescope (← stmtOf thm) fun xs _ => do
    let mut out := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if ← isProp d.type then out := out ++ [d.userName.eraseMacroScopes]
    pure out

run_cmd Lean.Elab.Command.liftTermElabM do
  let got ← propBinders ``rowB1_of_data
  let old ← propBinders ``Tools.ShippingGen5Cover3.rowB1_of_inv
  unless old.contains `hcb do throwError "CV6 BINDERS CONTROL: rowB1_of_inv has no hcb"
  -- the anonymous `k < …` binder of the conclusion (`a`) stays last; the input facts go before it
  let o := old.erase `hcb
  let exp := o.filter (· != `a) ++ [`hms, `hd] ++ o.filter (· == `a)
  unless got == exp do
    throwError "CV6 BINDERS FAILED: expected {exp}, got {got}"
  if got.contains `hcb then throwError "CV6 BINDERS FAILED: hcb present"
  logInfo m!"CV6 BINDERS: {got} = rowB1_of_inv binders {old} minus hcb plus [hms, hd]"
  for n in [``hcb_of_data, ``rowB1_of_data] do checkAxioms n
  logInfo m!"CV6 COUNTS: TYPE 2 (+1 control), MUTANT 3, BINDERS 1, AXIOMS 2"
end Tests.Gen5.Cover3RCheck

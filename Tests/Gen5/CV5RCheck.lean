import Tools.ShippingGen5Cover5R
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT by a clean build (agent target build `Tests.Gen5.CV5RCheck` exit 0, 737 jobs; clean build is the coder's). No sorry / axiom / native_decide.
/-! # C.CV-5 checks (Tools/ShippingGen5Cover5R.lean; scripts/gen5/AC9CV5_FREEZE.md §2)

TYPE: Expected statements are written from the freeze text. MUTANT: signature / defeq rejection, NOT a semantic counterexample.
BINDERS: Prop binders of `shapeAgree_of_sidesR` = those of `shapeAgree_of_sides` minus `hsp hss hls hn`, plus `hd`, compared mechanically.
AXIOMS: standard only. -/
namespace Tests.Gen5.CV5RCheck
open Lean Meta
open Sparkle.Compiler.Elab Tools.ShippingMachineAuto Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover5R Tools.ShippingGen5GDCover1
open Tools.ShippingReaderFuel Tools.ShippingReaderLenOk Tools.ShippingReaderFuelShapeR5 Tools.ShippingShapeDecomp
open Tests.Gen3.ExpectedType

def ExpSidesR : Prop :=
  ∀ {d : MachineData} {st : MachRead} {sp : MachineShape}
    (hs : sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
          sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size)
    {lvl : Lean.Expr → Nat} {E : ConstantInfo} {senv : StructEnv}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d),
    ShapeAgree d st

def ExpWitness : Prop :=
  ∀ {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape} {n : Nat}
    {p : ShapePre} {en : Lean.Expr} {st0 : MachRead} {env : List MachVal}
    {st1 st : MachRead} {v : Lean.Expr}
    (w : StateSideWitness E senv sp n p en st0 env st1 st v)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d),
    ShapeAgree d st

/-- Mutant: `hd` dropped. -/
def MutNoHd : Prop :=
  ∀ {d : MachineData} {st : MachRead} {sp : MachineShape}
    (hs : sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
          sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size),
    ShapeAgree d st

/-- Mutant: `hs` dropped. -/
def MutNoHs : Prop :=
  ∀ {d : MachineData} {st : MachRead} {sp : MachineShape}
    {lvl : Lean.Expr → Nat} {E : ConstantInfo} {senv : StructEnv}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d),
    ShapeAgree d st

/-- Mutant: `hd` replaced by the data-side shape equation only. -/
def MutWeakHd : Prop :=
  ∀ {d : MachineData} {st : MachRead} {sp : MachineShape}
    (hs : sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
          sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size)
    (hsp : d.shape = sp),
    ShapeAgree d st

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``shapeAgree_of_sidesR ``ExpSidesR
  checkExpected ``shapeAgree_of_witness ``ExpWitness
  logInfo m!"CV5 TYPE: 2 theorems against Expected"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutant ``shapeAgree_of_sidesR ``MutNoHd
  checkMutant ``shapeAgree_of_sidesR ``MutNoHs
  checkMutant ``shapeAgree_of_sidesR ``MutWeakHd
  logInfo m!"CV5 MUTANT: 3 rejected (signature/defeq, not semantic)"

def propBinders (thm : Name) : MetaM (List Name) := do
  forallTelescope (← stmtOf thm) fun xs _ => do
    let mut out := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if ← isProp d.type then out := out ++ [d.userName.eraseMacroScopes]
    pure out

run_cmd Lean.Elab.Command.liftTermElabM do
  let got ← propBinders ``shapeAgree_of_sidesR
  let old ← propBinders ``Tools.ShippingGen5Cover5.shapeAgree_of_sides
  for b in [`hs, `hsp, `hss, `hls, `hn] do
    unless old.contains b do throwError "CV5 BINDERS CONTROL: old statement lacks {b}"
  let exp := (old.filter fun b => ![`hsp, `hss, `hls, `hn].contains b) ++ [`hd]
  unless got == exp do throwError "CV5 BINDERS FAILED: expected {exp}, got {got}"
  logInfo m!"CV5 BINDERS: {got} = old {old} minus [hsp, hss, hls, hn] plus [hd]"
  for n in [``shapeAgree_of_sidesR, ``shapeAgree_of_witness] do checkAxioms n
  logInfo m!"CV5 COUNTS: TYPE 2, MUTANT 3, BINDERS 1, AXIOMS 2"
end Tests.Gen5.CV5RCheck

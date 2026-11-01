import Tools.ShippingGen5GDCover2
import Tests.Gen5.AccCheck
set_option autoImplicit false
-- Pod target build OK at 7fc1a6ba (`kjob lake build Tests.Gen5.GDCover2Check`, exit 0, 779 jobs): TYPE 4 / MUTANT 9 (single 7 + compound 2; signature/defeq rejection, not semantic) / POSITIVE 1 / AXIOMS 4 standard / CLOSURE 4939 consts, unknown 0. 3 intended sorry warnings = walker negatives. Clean build is the coder's.

/-! # G2 checks (Tools/ShippingGen5GDCover2.lean; freeze scripts/gen5/GD_G2_FREEZE.md)

TYPE: `checkExpected` against independent `Exp…` statements written from the freeze text. POSITIVE control: the production theorem's conclusion yields the
`dataOfFront` guard `shape.binders.length == p.1.length + insts + slots + lets` (a compiled `example`). MUTANT: signature / defeq rejection only, NOT a
semantic counterexample (single and compound counted apart). AXIOMS: standard three only. CLOSURE: explicit-value walker of `AccCheck`. -/
namespace Tests.Gen5.GDCover2Check
open Lean Meta Elab
open Sparkle.Compiler.Elab Tests.Gen3.ExpectedType
open Tools.ShippingGen5Cover3 Tools.ShippingReaderFuel Tools.ShippingReaderLenOk Tools.ShippingReaderFuelShapeR5 Tools.ShippingShapeDecomp Tools.ShippingMachineAuto

section Expected

def Cv4 : Prop :=
  ∀ (E : Lean.ConstantInfo) (senv : StructEnv) (sp : MachineShape),
    machineShape? false [] E senv = some sp → ∃ n, machineShapeF n false [] E senv true = some (some sp)

def ExpPostLen : Prop :=
  ∀ {allowInsts : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr} {sp : MachineShape},
    ∀ (h : shapePost allowInsts p m st v = some sp) (hl : st.LenOk),
    sp.binders.length = p.bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets

def ExpWitLen : Prop :=
  ∀ {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape} {n : Nat} {p : ShapePre} {en : Lean.Expr}
    {st0 : MachRead} {env : List MachVal} {st1 st : MachRead} {v : Lean.Expr},
    ∀ (w : Tools.ShippingGen5GDCover1.StateSideWitness E senv sp n p en st0 env st1 st v),
    sp.binders.length = p.bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets

def ExpProdLen : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape},
    ∀ (h : machineShape? false [] E senv = some sp),
    ∃ (d : Lean.DefinitionVal) (bs : List (Lean.Name × MixedGateBinder)) (e : Lean.Expr),
      E = .defnInfo d ∧
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
      sp.binders.length = bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets

def ExpPrePeel : Prop :=
  ∀ {E : Lean.ConstantInfo} {senv : StructEnv} {p : ShapePre} (h : shapePre false [] E senv = some p),
    E = .defnInfo p.d ∧
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs p.d.value) = some (p.bs, p.e)

/-- (a) no `LenOk` -/
def MutPostNoLenOk : Prop :=
  ∀ {allowInsts : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr} {sp : MachineShape},
    ∀ (h : shapePost allowInsts p m st v = some sp),
    sp.binders.length = p.bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets

/-- (b) slots term dropped -/
def MutWitNoSlots : Prop :=
  ∀ {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape} {n : Nat} {p : ShapePre} {en : Lean.Expr}
    {st0 : MachRead} {env : List MachVal} {st1 st : MachRead} {v : Lean.Expr},
    ∀ (w : Tools.ShippingGen5GDCover1.StateSideWitness E senv sp n p en st0 env st1 st v),
    sp.binders.length = p.bs.length + sp.insts.length + sp.layout.lets

/-- (c) lets off by one -/
def MutWitPlusOne : Prop :=
  ∀ {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape} {n : Nat} {p : ShapePre} {en : Lean.Expr}
    {st0 : MachRead} {env : List MachVal} {st1 st : MachRead} {v : Lean.Expr},
    ∀ (w : Tools.ShippingGen5GDCover1.StateSideWitness E senv sp n p en st0 env st1 st v),
    sp.binders.length = p.bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets + 1

/-- (d) peel length replaced by 0 -/
def MutProdNoPeelLen : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape},
    ∀ (h : machineShape? false [] E senv = some sp),
    ∃ (d : Lean.DefinitionVal) (bs : List (Lean.Name × MixedGateBinder)) (e : Lean.Expr),
      E = .defnInfo d ∧
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
      sp.binders.length = 0 + sp.insts.length + sp.layout.slots.length + sp.layout.lets

/-- (e) peel equation dropped (bs unconstrained) -/
def MutProdNoPeel : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape},
    ∀ (h : machineShape? false [] E senv = some sp),
    ∃ (bs : List (Lean.Name × MixedGateBinder)),
      sp.binders.length = bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets

/-- (f) no `hbr` -/
def MutProdNoHbr : Prop :=
  ∀ {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape},
    ∀ (h : machineShape? false [] E senv = some sp),
    ∃ (d : Lean.DefinitionVal) (bs : List (Lean.Name × MixedGateBinder)) (e : Lean.Expr),
      E = .defnInfo d ∧
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
      sp.binders.length = bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets

/-- (g) `defnInfo` conjunct dropped -/
def MutProdNoDefn : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape},
    ∀ (h : machineShape? false [] E senv = some sp),
    ∃ (d : Lean.DefinitionVal) (bs : List (Lean.Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
      sp.binders.length = bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets

/-- (h) compound: no `LenOk` and slots term dropped -/
def MutPostNoLenOkNoSlots : Prop :=
  ∀ {allowInsts : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr} {sp : MachineShape},
    ∀ (h : shapePost allowInsts p m st v = some sp),
    sp.binders.length = p.bs.length + sp.insts.length + sp.layout.lets

/-- (i) compound: `+1` and no peel equation -/
def MutProdPlusOneNoPeel : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape},
    ∀ (h : machineShape? false [] E senv = some sp),
    ∃ (bs : List (Lean.Name × MixedGateBinder)),
      sp.binders.length = bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets + 1

end Expected

-- POSITIVE control: the conclusion gives exactly the guard of `dataOfFront` (`DataOf.lean:69`).
open Tools.ShippingGen5GDCover2 in
example (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp) :
    ∃ (d : Lean.DefinitionVal) (bs : List (Lean.Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
      (sp.binders.length == bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets) = true := by
  obtain ⟨d, bs, e, _, hp, hl⟩ := dataOfFront_len_of_production hbr h
  exact ⟨d, bs, e, hp, beq_iff_eq.2 hl⟩

open Tools.ShippingGen5GDCover2 in
run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``shapePost_binders_len ``ExpPostLen
  checkExpected ``dataOfFront_len_of_witness ``ExpWitLen
  checkExpected ``dataOfFront_len_of_production ``ExpProdLen
  checkExpected ``shapePre_peel ``ExpPrePeel
  checkMutant ``shapePost_binders_len ``MutPostNoLenOk
  checkMutant ``dataOfFront_len_of_witness ``MutWitNoSlots
  checkMutant ``dataOfFront_len_of_witness ``MutWitPlusOne
  checkMutant ``dataOfFront_len_of_production ``MutProdNoPeelLen
  checkMutant ``dataOfFront_len_of_production ``MutProdNoPeel
  checkMutant ``dataOfFront_len_of_production ``MutProdNoHbr
  checkMutant ``dataOfFront_len_of_production ``MutProdNoDefn
  checkMutant ``shapePost_binders_len ``MutPostNoLenOkNoSlots
  checkMutant ``dataOfFront_len_of_production ``MutProdPlusOneNoPeel
  logInfo m!"GEN5 GDCOVER2 COUNTS: TYPE 4 / MUTANT 9 (single 7 + compound 2; signature/defeq rejection, not semantic) / POSITIVE 1"

open Tools.ShippingGen5GDCover2 in
run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``shapePost_binders_len
  checkAxioms ``dataOfFront_len_of_witness
  checkAxioms ``dataOfFront_len_of_production
  checkAxioms ``shapePre_peel

run_cmd Lean.Elab.Command.liftTermElabM Tests.Gen5.AccCheck.walkerControls

open Tools.ShippingGen5GDCover2 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let roots := [``shapePost_binders_len, ``dataOfFront_len_of_witness, ``dataOfFront_len_of_production,
    ``shapePre_peel]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in roots do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: root {n} is not in the seen set"
  let suppliers := [``Tools.ShippingGen5GDCover1.stateSide_of_production, ``Tools.ShippingGen5Cover5.machineShapeF_state_side,
    ``Tools.ShippingGen5GDCover1.StateSideWitness, ``Tools.ShippingReaderFuel.shapePost]
  for n in suppliers do
    if roots.contains n then throwError "GEN5 CLOSURE FAILED: expected supplier {n} must differ from the roots"
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: expected supplier {n} is not reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants: {unk}"
  logInfo m!"GEN5 CLOSURE OK (G2): {seen.toList.length} constants, no forbidden constant, expected suppliers reached, no unknown constant"

end Tests.Gen5.GDCover2Check

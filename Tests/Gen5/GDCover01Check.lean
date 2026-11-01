import Tools.ShippingGen5GDCover0
import Tools.ShippingGen5GDCover1
import Tests.Gen5.AccCheck
set_option autoImplicit false
-- Pod target build OK at f6ba6a98 (`kjob lake build Tests.Gen5.GDCover01Check`, exit 0): TYPE 8 / BODY 2 / MUTANT 17 (single 15 + compound 2; signature/defeq rejection, not semantic) / AXIOMS 8 standard / CLOSURE 8537 consts, unknown 0. 3 intended sorry warnings = walker negatives. Clean build is the coder's. No sorry / axiom / native_decide in source.

/-! # G0 / G1 / W1 checks (Tools/ShippingGen5GDCover0.lean, Tools/ShippingGen5GDCover1.lean)

TYPE (Pi path): `getConstInfo c .type` against an independently written Pi type (`genDataC`, `StateSideWitness`). TYPE (theorems): `checkExpected` against
independent `Exp…` statements written from the freeze text. BODY (value path, counted apart): the VALUES of `genDataC` and `StateSideWitness` against independently
written lambdas. MUTANT: single and compound counted apart; signature / defeq rejection only, NOT a semantic counterexample.
AXIOMS: standard three only (`genDataC` uses `Classical.choice`). CLOSURE: the explicit-value walker of `AccCheck`; forbidden `sorryAx / ofReduceBool / trustCompiler`;
expected suppliers fixed (distinct from the roots). Positive/negative controls: `AccCheck.walkerControls` and the unknown-name controls below. -/
namespace Tests.Gen5.GDCover01Check
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGen2 Tests.Gen3.ExpectedType
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingGen5Cover3 Tools.ShippingReaderFuel Tools.ShippingReaderLenOk Tools.ShippingReaderFuelShapeR5 Tools.ShippingShapeDecomp Tools.ShippingMachineAuto

section Expected

-- the C.CV-4 text, written once here
def Cv4 : Prop :=
  ∀ (E : Lean.ConstantInfo) (senv : StructEnv) (sp : MachineShape),
    machineShape? false [] E senv = some sp → ∃ n, machineShapeF n false [] E senv true = some (some sp)

def ExpGenDataCType : Type :=
  (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) → (env₀ : Lean.Environment) →
    (E : Lean.ConstantInfo) → Option (GenData dataOf E (structEnv env₀))

open Classical in
noncomputable def ExpGenDataCBody : (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) →
    (env₀ : Lean.Environment) → (E : Lean.ConstantInfo) → Option (GenData dataOf E (structEnv env₀)) :=
  fun dataOf env₀ E =>
    if h : ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape ∧
        dataOf E (structEnv env₀) d.shape = some d ∧ GenWF d = true
    then some ⟨h.choose, h.choose_spec.2.2, h.choose_spec.1, h.choose_spec.2.1⟩ else none

def ExpIsSomeIff : Prop :=
  ∀ (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Lean.Environment)
    (E : Lean.ConstantInfo),
    (genDataC dataOf env₀ E).isSome = true ↔
      ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape ∧
        dataOf E (structEnv env₀) d.shape = some d ∧ GenWF d = true

def ExpReachSdw : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}
    (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Lean.Name → Option (SemPkg ι dom)) → Lean.Name → {E : Lean.ConstantInfo} →
      GenData dataOf E (structEnv env₀) → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀)
    (hloc : ∀ (Q Q' : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) {E : Lean.ConstantInfo}
      (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) {E : Lean.ConstantInfo}
      (g : GenData dataOf E (structEnv env₀)), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) {E : Lean.ConstantInfo}
      (g : GenData dataOf E (structEnv env₀)), (genSem Q X g).d = g.d)
    (Reach : Lean.Name → Prop),
    ReachCover (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d)
        (genDataC dataOf env₀) ordCallees genSem hmem hev hloc hdecl hd) Reach ↔
      ∀ c, Reach c → ∃ E : Lean.ConstantInfo, entry₀ env₀ c = some E ∧
        ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape ∧
          dataOf E (structEnv env₀) d.shape = some d ∧ GenWF d = true

def ExpPeel : Prop :=
  ∀ {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp),
    ∃ d : Lean.DefinitionVal, E = .defnInfo d ∧
      ∃ (bs : List (Lean.Name × MixedGateBinder)) (e : Lean.Expr),
        mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e)

def ExpSswType : Type :=
  ∀ (E : Lean.ConstantInfo) (senv : StructEnv) (sp : MachineShape) (n : Nat) (p : ShapePre) (en : Lean.Expr)
    (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr), Prop
-- (a `def … : Type 1`-style Pi check is done on the value of this `def`; see checkSswPi)

def ExpSswBody : (E : Lean.ConstantInfo) → (senv : StructEnv) → (sp : MachineShape) → (n : Nat) → (p : ShapePre) →
    (en : Lean.Expr) → (st0 : MachRead) → (env : List MachVal) → (st1 st : MachRead) → (v : Lean.Expr) → Prop :=
  fun E senv sp n p en st0 env st1 st v =>
    shapePre false [] E senv = some p ∧
    machNormF n senv p.e = some en ∧
    (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
    (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n)
        = some (some (env, st1)) ∧
    (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
    shapePost true p (shapeMid senv p en) st v = some sp ∧
    st.LenOk ∧
    sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
    sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size

def ExpSideOfProd : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      shapePre false [] E senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n)
          = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost true p (shapeMid senv p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size

def ExpWitness : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      (shapePre false [] E senv = some p ∧
       machNormF n senv p.e = some en ∧
       (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
       (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n)
           = some (some (env, st1)) ∧
       (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
       shapePost true p (shapeMid senv p en) st v = some sp ∧
       st.LenOk ∧
       sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
       sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size) ∧ ShapeAgree d st

def ExpWitnessFrom : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfFrom lvl E senv sp tin fl = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      (shapePre false [] E senv = some p ∧
       machNormF n senv p.e = some en ∧
       (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
       (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n)
           = some (some (env, st1)) ∧
       (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
       shapePost true p (shapeMid senv p en) st v = some sp ∧
       st.LenOk ∧
       sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
       sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size) ∧ ShapeAgree d st

/-! ### single mutants (signature / defeq rejection, not semantic counterexamples) -/

/-- (a) `GenWF d = true` dropped from the right-hand side -/
def MutIffNoWf : Prop :=
  ∀ (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Lean.Environment)
    (E : Lean.ConstantInfo),
    (genDataC dataOf env₀ E).isSome = true ↔
      ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape ∧
        dataOf E (structEnv env₀) d.shape = some d

/-- (b) forward direction only -/
def MutIffFwd : Prop :=
  ∀ (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Lean.Environment)
    (E : Lean.ConstantInfo),
    (genDataC dataOf env₀ E).isSome = true →
      ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape ∧
        dataOf E (structEnv env₀) d.shape = some d ∧ GenWF d = true

/-- (c) the `dataOf` clause dropped -/
def MutIffNoDataOf : Prop :=
  ∀ (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Lean.Environment)
    (E : Lean.ConstantInfo),
    (genDataC dataOf env₀ E).isSome = true ↔
      ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape ∧ GenWF d = true

/-- (d) `ReachCover` iff with the `entry₀` clause dropped -/
def MutReachNoEntry : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}
    (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Lean.Name → Option (SemPkg ι dom)) → Lean.Name → {E : Lean.ConstantInfo} →
      GenData dataOf E (structEnv env₀) → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀)
    (hloc : ∀ (Q Q' : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) {E : Lean.ConstantInfo}
      (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) {E : Lean.ConstantInfo}
      (g : GenData dataOf E (structEnv env₀)), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) {E : Lean.ConstantInfo}
      (g : GenData dataOf E (structEnv env₀)), (genSem Q X g).d = g.d)
    (Reach : Lean.Name → Prop),
    ReachCover (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d)
        (genDataC dataOf env₀) ordCallees genSem hmem hev hloc hdecl hd) Reach ↔
      ∀ c, Reach c → ∃ E : Lean.ConstantInfo,
        ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape ∧
          dataOf E (structEnv env₀) d.shape = some d ∧ GenWF d = true

/-- (e) `ReachCover` iff, forward direction only -/
def MutReachFwd : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Lean.Environment}
    (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Lean.Name → Option (SemPkg ι dom)) → Lean.Name → {E : Lean.ConstantInfo} →
      GenData dataOf E (structEnv env₀) → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀)
    (hloc : ∀ (Q Q' : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) {E : Lean.ConstantInfo}
      (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      genSem Q X g = genSem Q' X g)
    (hdecl : ∀ (Q : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) {E : Lean.ConstantInfo}
      (g : GenData dataOf E (structEnv env₀)), (genSem Q X g).decl = X)
    (hd : ∀ (Q : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) {E : Lean.ConstantInfo}
      (g : GenData dataOf E (structEnv env₀)), (genSem Q X g).d = g.d)
    (Reach : Lean.Name → Prop),
    ReachCover (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d)
        (genDataC dataOf env₀) ordCallees genSem hmem hev hloc hdecl hd) Reach →
      ∀ c, Reach c → ∃ E : Lean.ConstantInfo, entry₀ env₀ c = some E ∧
        ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape ∧
          dataOf E (structEnv env₀) d.shape = some d ∧ GenWF d = true

/-- (f) the `E = .defnInfo d` conjunct dropped -/
def MutPeelNoDefn : Prop :=
  ∀ {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp),
    ∃ d : Lean.DefinitionVal,
      ∃ (bs : List (Lean.Name × MixedGateBinder)) (e : Lean.Expr),
        mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e)

/-- (g) `packTupleInputs` dropped -/
def MutPeelNoPack : Prop :=
  ∀ {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp),
    ∃ d : Lean.DefinitionVal, E = .defnInfo d ∧
      ∃ (bs : List (Lean.Name × MixedGateBinder)) (e : Lean.Expr),
        mixedGatePeel d.value = some (bs, e)

/-- (h) `hbr` dropped -/
def MutSideNoHbr : Prop :=
  ∀ {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr), ExpSswBody E senv sp n p en st0 env st1 st v

/-- (i) the run is forgotten: only `∃ st, st.LenOk` (the T5/T6 shape) -/
def MutSideForget : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp),
    ∃ st : MachRead, st.LenOk

/-- (j) `ShapeAgree d st'` with a FRESH `st'` instead of the witness `st` -/
def MutWitFreshSt : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d),
    (∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr), ExpSswBody E senv sp n p en st0 env st1 st v) ∧
    ∃ st' : MachRead, ShapeAgree d st'

/-- (k) `hd` dropped -/
def MutWitNoHd : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData},
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      ExpSswBody E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st

/-- (l) the witness conjunct dropped: only `∃ st, ShapeAgree d st` -/
def MutWitNoWitness : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d),
    ∃ st : MachRead, ShapeAgree d st

/-- (m) `_from` with `hd` for `dataOfAt` instead of `dataOfFrom` (the carrier is fixed) -/
def MutFromFixedCarrier : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      ExpSswBody E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st

-- compound mutants (two changes)
/-- (n) (j) AND (k) -/
def MutWitFreshNoHd : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData},
    (∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr), ExpSswBody E senv sp n p en st0 env st1 st v) ∧
    ∃ st' : MachRead, ShapeAgree d st'

/-- (o) (a) AND (c) -/
def MutIffNoWfNoDataOf : Prop :=
  ∀ (dataOf : Lean.ConstantInfo → StructEnv → MachineShape → Option MachineData) (env₀ : Lean.Environment)
    (E : Lean.ConstantInfo),
    (genDataC dataOf env₀ E).isSome = true ↔
      ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape

-- body mutants
/-- body (p): `st.LenOk` clause dropped from `StateSideWitness` -/
def MutSswBodyNoLenOk : (E : Lean.ConstantInfo) → (senv : StructEnv) → (sp : MachineShape) → (n : Nat) → (p : ShapePre) →
    (en : Lean.Expr) → (st0 : MachRead) → (env : List MachVal) → (st1 st : MachRead) → (v : Lean.Expr) → Prop :=
  fun E senv sp n p en st0 env st1 st v =>
    shapePre false [] E senv = some p ∧
    machNormF n senv p.e = some en ∧
    (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
    (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n)
        = some (some (env, st1)) ∧
    (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
    shapePost true p (shapeMid senv p en) st v = some sp ∧
    sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
    sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size

/-- body (q): `ai := false` in `shapePost` -/
def MutSswBodyAiFalse : (E : Lean.ConstantInfo) → (senv : StructEnv) → (sp : MachineShape) → (n : Nat) → (p : ShapePre) →
    (en : Lean.Expr) → (st0 : MachRead) → (env : List MachVal) → (st1 st : MachRead) → (v : Lean.Expr) → Prop :=
  fun E senv sp n p en st0 env st1 st v =>
    shapePre false [] E senv = some p ∧
    machNormF n senv p.e = some en ∧
    (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
    (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n)
        = some (some (env, st1)) ∧
    (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
    shapePost false p (shapeMid senv p en) st v = some sp ∧
    st.LenOk ∧
    sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
    sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size

end Expected

/-- Compare the TYPE (Pi type) of a constant with the VALUE of an independent `def ... : Type`. -/
def checkTypeOfConst (c exp : Name) : MetaM Unit := do
  let a := (← getConstInfo c).type
  let e ← stmtOf exp
  cmpTele s!"{c} (Pi type)" a e
  logInfo m!"GEN5 TYPE(Pi) OK {c} against {exp}"

/-- BODY: the VALUE of `c` against the VALUE of the independent definition. -/
def checkBody (c exp : Name) : MetaM Unit := do
  cmpTele s!"{c} (body)" (← stmtOf c) (← stmtOf exp)
  logInfo m!"GEN5 BODY OK {c} against {exp}"

/-- BODY mutant: the value of `c` must NOT match the mutant's value (signature/defeq rejection). -/
def checkBodyMutant (c mt : Name) : MetaM Unit := do
  let a ← stmtOf c
  let e ← stmtOf mt
  let accepted ← withoutModifyingState do
    try cmpTele s!"{c} vs body mutant {mt}" a e; pure true catch _ => pure false
  if accepted then throwError "GEN5 MUTANT ACCEPTED: {mt} matches the body of {c}"
  if (← withoutModifyingState (isDefEq a e)) then throwError "GEN5 MUTANT ACCEPTED (isDefEq): {mt} vs the body of {c}"
  logInfo m!"GEN5 MUTANT(BODY path) REJECTED {mt} (against the value of {c})"

open Tools.ShippingGen5GDCover1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- TYPE: 2 Pi + 6 theorems
  checkTypeOfConst ``genDataC ``ExpGenDataCType
  -- `StateSideWitness : … → Prop`: its Pi type is the telescope of `ExpSswBody`'s binders ending in `Prop`
  cmpTele "StateSideWitness (Pi type)" (← getConstInfo ``StateSideWitness).type (← stmtOf ``ExpSswType)
  logInfo m!"GEN5 TYPE(Pi) OK StateSideWitness against ExpSswType"
  checkExpected ``genDataC_isSome_iff ``ExpIsSomeIff
  checkExpected ``reachCover_iff_sdw ``ExpReachSdw
  checkExpected ``peel_of_machineShape ``ExpPeel
  checkExpected ``stateSide_of_production ``ExpSideOfProd
  checkExpected ``shapeAgree_witness ``ExpWitness
  checkExpected ``shapeAgree_witness_from ``ExpWitnessFrom
  -- BODY: 2
  checkBody ``genDataC ``ExpGenDataCBody
  checkBody ``StateSideWitness ``ExpSswBody
  -- MUTANT single: 13 theorem + 2 body = 15
  checkMutant ``genDataC_isSome_iff ``MutIffNoWf
  checkMutant ``genDataC_isSome_iff ``MutIffFwd
  checkMutant ``genDataC_isSome_iff ``MutIffNoDataOf
  checkMutant ``reachCover_iff_sdw ``MutReachNoEntry
  checkMutant ``reachCover_iff_sdw ``MutReachFwd
  checkMutant ``peel_of_machineShape ``MutPeelNoDefn
  checkMutant ``peel_of_machineShape ``MutPeelNoPack
  checkMutant ``stateSide_of_production ``MutSideNoHbr
  checkMutant ``stateSide_of_production ``MutSideForget
  checkMutant ``shapeAgree_witness ``MutWitFreshSt
  checkMutant ``shapeAgree_witness ``MutWitNoHd
  checkMutant ``shapeAgree_witness ``MutWitNoWitness
  checkMutant ``shapeAgree_witness_from ``MutFromFixedCarrier
  checkBodyMutant ``StateSideWitness ``MutSswBodyNoLenOk
  checkBodyMutant ``StateSideWitness ``MutSswBodyAiFalse
  -- MUTANT compound: 2
  checkMutant ``shapeAgree_witness ``MutWitFreshNoHd
  checkMutant ``genDataC_isSome_iff ``MutIffNoWfNoDataOf
  logInfo m!"GEN5 GDCOVER01 COUNTS: TYPE 8 (Pi 2 + theorems 6) / BODY 2 / MUTANT 17 (single 15 + compound 2)"

open Tools.ShippingGen5GDCover1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``genDataC
  checkAxioms ``genDataC_isSome_iff
  checkAxioms ``reachCover_iff_sdw
  checkAxioms ``peel_of_machineShape
  checkAxioms ``StateSideWitness
  checkAxioms ``stateSide_of_production
  checkAxioms ``shapeAgree_witness
  checkAxioms ``shapeAgree_witness_from

run_cmd Lean.Elab.Command.liftTermElabM Tests.Gen5.AccCheck.walkerControls

/-- Unknown-name controls through the same `closureReport` path: root / helper value / helper type naming an absent constant MUST be
reported; a clean chain MUST NOT. -/
def unknownControls : MetaM Unit := do
  let ghost := `Ghost.Absent.name
  let addU (n : Name) (type value : Expr) : MetaM Unit :=
    withOptions (fun o => debug.skipKernelTC.set o true) do
      addDecl (.thmDecl { name := n, levelParams := [], type := type, value := value })
  let unk (roots : List Name) : MetaM (Array Name) := do
    let (_, u, _) ← Tests.Gen5.AccCheck.closureReport (← getEnv) roots
    pure u
  let u1 ← unk [ghost]
  unless u1 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: unknown root not reported ({u1})"
  let u2 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.HelperVal (mkConst ``True) (mkConst ghost)
    addU `Tests.Gen5.UnkCtl.RootVal (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.HelperVal)
    unk [`Tests.Gen5.UnkCtl.RootVal]
  unless u2 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: helper value naming an unknown constant not reported ({u2})"
  let u3 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.HelperTy (mkConst ghost) (mkConst ``True.intro)
    addU `Tests.Gen5.UnkCtl.RootTy (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.HelperTy)
    unk [`Tests.Gen5.UnkCtl.RootTy]
  unless u3 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: helper type naming an unknown constant not reported ({u3})"
  let u4 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.CleanHelper (mkConst ``True) (mkConst ``True.intro)
    addU `Tests.Gen5.UnkCtl.CleanRoot (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.CleanHelper)
    unk [`Tests.Gen5.UnkCtl.CleanRoot]
  unless u4.isEmpty do throwError "GEN5 UNKNOWN CONTROL FAILED: clean control reported unknown ({u4})"
  logInfo m!"GEN5 UNKNOWN CONTROLS OK: 3 negatives reported unknown (root / helper value / helper type), clean control not reported"

run_cmd Lean.Elab.Command.liftTermElabM unknownControls

open Tools.ShippingGen5GDCover1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let roots := [``genDataC, ``genDataC_isSome_iff, ``reachCover_iff_sdw, ``peel_of_machineShape,
    ``StateSideWitness, ``stateSide_of_production, ``shapeAgree_witness, ``shapeAgree_witness_from]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in roots do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: root {n} is not in the seen set"
  let suppliers := [``Tools.ShippingGen5Sem.GenData, ``Tools.ShippingGen5Sem.GenWF, ``Tools.ShippingGen5Acc.mkKit,
    ``Tools.ShippingGen5Cover5.machineShapeF_state_side, ``Tools.ShippingGen5Cover5.shapeAgree_of_sides,
    ``Tools.ShippingGen5DataOf.dataOfFrom_dims]
  for n in suppliers do
    if roots.contains n then throwError "GEN5 CLOSURE FAILED: expected supplier {n} must differ from the roots"
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: expected supplier {n} is not reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (G0/G1/W1): {seen.toList.length} constants, no forbidden constant, expected suppliers reached (distinct from the 8 roots), no unknown constant"

end Tests.Gen5.GDCover01Check

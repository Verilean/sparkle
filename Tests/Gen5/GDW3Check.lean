import Tools.ShippingGen5GDW3
import Tests.Gen5.AccCheck
set_option autoImplicit false
set_option linter.unusedVariables false
-- NOT BUILT (draft). Freeze scripts/gen5/GD_W3_WITNESS.md.

/-! # W3 checks (Tools/ShippingGen5GDW3.lean)

TYPE: `checkExpected` against independent `Exp…` statements written here from the freeze text (`LetQuoteEqC` is re-spelled; `ShapeAgree` and `StateSideWitness` are
shared interface defs, and `StateSideWitness` is re-spelled once in `ExpSswBody`, checked by `sswBody_iff`).
MUTANT: one-place changes, well-typed, rejected by the same comparer: signature / defeq rejection, NOT a semantic counterexample.
POSITIVE / NEGATIVE: `LetQuoteEqC` is `Iff.rfl` to its re-spelling; the OLD `LetQuoteEq` (no `machCanonAp`) is rejected as the conclusion of the witness.
AXIOMS: standard three only. CLOSURE: the explicit-value walker of `AccCheck` with its controls and the unknown-name controls. -/
namespace Tests.Gen5.GDW3Check
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGen2 Tests.Gen3.ExpectedType
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingGen5Cover3 Tools.ShippingReaderFuel Tools.ShippingReaderLenOk Tools.ShippingReaderFuelShapeR5 Tools.ShippingShapeDecomp
  Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge Tools.ShippingUnifiedSource Tools.ShippingGen5Cover3Canon
  Tools.ShippingMachineDenote

section Expected

def Cv4 : Prop :=
  ∀ (E : Lean.ConstantInfo) (senv : StructEnv) (sp : MachineShape),
    machineShape? false [] E senv = some sp → ∃ n, machineShapeF n false [] E senv true = some (some sp)

def ExpLetQuoteEqC (d : MachineData) (st : MachRead) : Prop :=
  ∀ (j : Nat) (hj : j < d.ls.length) (nm : Lean.Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) →
    quote d.dom (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.bpos i))
                (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.vpos i)) (d.ls[j]'hj).2
      = machCanonAp (machClose st.insts.size st.kinds.size st.lets.size 0 v)

def ExpLetQuoteEqOld (d : MachineData) (st : MachRead) : Prop :=
  ∀ (j : Nat) (hj : j < d.ls.length) (nm : Lean.Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) →
    quote d.dom (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.bpos i))
                (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.vpos i)) (d.ls[j]'hj).2
      = machClose st.insts.size st.kinds.size st.lets.size 0 v

def ExpSswBody (E : Lean.ConstantInfo) (senv : StructEnv) (sp : MachineShape) (n : Nat) (p : ShapePre)
    (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr) : Prop :=
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

def ExpBinders : Prop :=
  ∀ {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr} {sp : MachineShape}
    (h : shapePost ai p m st v = some sp),
    ∃ A : List (Lean.Name × MixedGateBinder), sp.binders = A ++ st.lets.toList.map (fun l => (l.1, l.2.1))

def ExpLetsTypedGet : Prop :=
  ∀ {bpos vpos : Nat → Nat} {kb kv : Nat} {vw : Nat → Nat} {K : Nat → Option SType}
    (ls : List (Σ s : SType, Term s)) (p j : Nat) (l : Σ s : SType, Term s),
    LetsTyped bpos vpos kb kv vw K p ls → ls[j]? = some l → K (p + j) = some l.1

def ExpBoolBits : Prop :=
  ∀ (dom e : Lean.Expr), machCanonAp (machBoolBits dom e) = machBoolBits (machCanonAp dom) (machCanonAp e)

def ExpOfPost : Prop :=
  ∀ {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v0 : Lean.Expr} {sp : MachineShape}
    (hne : p.outs ≠ []) (hpost : shapePost ai p m st v0 = some sp)
    {d : MachineData} (hs : d.shape = sp) (hok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hag : ShapeAgree d st), ExpLetQuoteEqC d st

def ExpWitnessFrom : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfFrom lvl E senv sp tin fl = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      ExpSswBody E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st ∧ ExpLetQuoteEqC d st

def ExpWitness : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      ExpSswBody E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st ∧ ExpLetQuoteEqC d st

/-! ### mutants (signature / defeq rejection, not semantic counterexamples) -/

/-- (a) the OLD `LetQuoteEq` as the conclusion -/
def MutWitOld : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      ExpSswBody E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st ∧ ExpLetQuoteEqOld d st

/-- (b) `LetQuoteEqC` for a FRESH `st'` instead of the witness `st` -/
def MutWitFreshSt : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d),
    (∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr), ExpSswBody E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st) ∧
    ∃ st' : MachRead, ExpLetQuoteEqC d st'

/-- (c) `hd` dropped -/
def MutWitNoHd : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData},
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      ExpSswBody E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st ∧ ExpLetQuoteEqC d st

/-- (d) `ShapeAgree` conjunct dropped -/
def MutWitNoAgree : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      ExpSswBody E senv sp n p en st0 env st1 st v ∧ ExpLetQuoteEqC d st

/-- (e) `hbr` dropped -/
def MutWitNoHbr : Prop :=
  ∀ {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      ExpSswBody E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st ∧ ExpLetQuoteEqC d st

/-- (f) `_from` with `dataOfAt` as the carrier -/
def MutFromFixedCarrier : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      ExpSswBody E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st ∧ ExpLetQuoteEqC d st

/-- (g) `of_post` without the `p.outs ≠ []` premise -/
def MutOfPostNoOuts : Prop :=
  ∀ {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v0 : Lean.Expr} {sp : MachineShape}
    (hpost : shapePost ai p m st v0 = some sp)
    {d : MachineData} (hs : d.shape = sp) (hok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hag : ShapeAgree d st), ExpLetQuoteEqC d st

/-- (h) `of_post` without `d.ok` -/
def MutOfPostNoOk : Prop :=
  ∀ {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v0 : Lean.Expr} {sp : MachineShape}
    (hne : p.outs ≠ []) (hpost : shapePost ai p m st v0 = some sp)
    {d : MachineData} (hs : d.shape = sp)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hag : ShapeAgree d st), ExpLetQuoteEqC d st

/-- (i) bool-bits lemma without the `machCanonAp dom` on the right (the `dom` is not moved) -/
def MutBoolBitsDomFixed : Prop :=
  ∀ (dom e : Lean.Expr), machCanonAp (machBoolBits dom e) = machBoolBits dom (machCanonAp e)

/-- (j) binders lemma: the `let` binders at the FRONT instead of the end -/
def MutBindersFront : Prop :=
  ∀ {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr} {sp : MachineShape}
    (h : shapePost ai p m st v = some sp),
    ∃ A : List (Lean.Name × MixedGateBinder), sp.binders = st.lets.toList.map (fun l => (l.1, l.2.1)) ++ A

/-- (k) letsTyped_get: offset `p` instead of `p + j` -/
def MutLetsTypedGetOffset : Prop :=
  ∀ {bpos vpos : Nat → Nat} {kb kv : Nat} {vw : Nat → Nat} {K : Nat → Option SType}
    (ls : List (Σ s : SType, Term s)) (p j : Nat) (l : Σ s : SType, Term s),
    LetsTyped bpos vpos kb kv vw K p ls → ls[j]? = some l → K p = some l.1

-- compound (two changes)
/-- (l) (a) AND (c) -/
def MutWitOldNoHd : Prop :=
  ∀ (hbr : Cv4) {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData},
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      ExpSswBody E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st ∧ ExpLetQuoteEqOld d st

/-- (m) (b) AND (e) -/
def MutWitFreshNoHbr : Prop :=
  ∀ {E : Lean.ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d),
    (∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr), ExpSswBody E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st) ∧
    ∃ st' : MachRead, ExpLetQuoteEqC d st'

end Expected

open Tools.ShippingGen5GDW3 in
theorem letQuoteEqC_iff (d : MachineData) (st : MachRead) : LetQuoteEqC d st ↔ ExpLetQuoteEqC d st := Iff.rfl

open Tools.ShippingGen5GDCover1 in
theorem sswBody_iff (E : Lean.ConstantInfo) (senv : StructEnv) (sp : MachineShape) (n : Nat) (p : ShapePre)
    (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr) :
    StateSideWitness E senv sp n p en st0 env st1 st v ↔ ExpSswBody E senv sp n p en st0 env st1 st v := Iff.rfl

open Tools.ShippingGen5GDW3 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- POSITIVE / NEGATIVE statement controls: the witness' conclusion is `LetQuoteEqC`'s re-spelling, not the OLD statement
  checkExpected ``shapePost_binders ``ExpBinders
  checkExpected ``letsTyped_get ``ExpLetsTypedGet
  checkExpected ``machCanonAp_machBoolBits' ``ExpBoolBits
  checkExpected ``letQuoteEqC_of_post ``ExpOfPost
  checkExpected ``letQuoteEqC_witness_from ``ExpWitnessFrom
  checkExpected ``letQuoteEqC_witness ``ExpWitness
  checkMutant ``letQuoteEqC_witness ``MutWitOld
  checkMutant ``letQuoteEqC_witness ``MutWitFreshSt
  checkMutant ``letQuoteEqC_witness ``MutWitNoHd
  checkMutant ``letQuoteEqC_witness ``MutWitNoAgree
  checkMutant ``letQuoteEqC_witness ``MutWitNoHbr
  checkMutant ``letQuoteEqC_witness_from ``MutFromFixedCarrier
  checkMutant ``letQuoteEqC_of_post ``MutOfPostNoOuts
  checkMutant ``letQuoteEqC_of_post ``MutOfPostNoOk
  checkMutant ``machCanonAp_machBoolBits' ``MutBoolBitsDomFixed
  checkMutant ``shapePost_binders ``MutBindersFront
  checkMutant ``letsTyped_get ``MutLetsTypedGetOffset
  -- compound
  checkMutant ``letQuoteEqC_witness ``MutWitOldNoHd
  checkMutant ``letQuoteEqC_witness ``MutWitFreshNoHbr
  logInfo m!"GEN5 GDW3 COUNTS: TYPE 6 / MUTANT 13 (single 11 + compound 2; signature/defeq rejections, not semantic counterexamples) / AXIOMS 6 / CLOSURE controls via AccCheck / UNKNOWN controls 3 negative / 1 clean"

open Tools.ShippingGen5GDW3 in
run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``shapePost_binders
  checkAxioms ``letsTyped_get
  checkAxioms ``machCanonAp_machBoolBits'
  checkAxioms ``letQuoteEqC_of_post
  checkAxioms ``letQuoteEqC_witness_from
  checkAxioms ``letQuoteEqC_witness

run_cmd Lean.Elab.Command.liftTermElabM Tests.Gen5.AccCheck.walkerControls

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
    addU `Tests.Gen5.UnkCtlW3.HelperVal (mkConst ``True) (mkConst ghost)
    addU `Tests.Gen5.UnkCtlW3.RootVal (mkConst ``True) (mkConst `Tests.Gen5.UnkCtlW3.HelperVal)
    unk [`Tests.Gen5.UnkCtlW3.RootVal]
  unless u2 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: helper value naming an unknown constant not reported ({u2})"
  let u3 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtlW3.HelperTy (mkConst ghost) (mkConst ``True.intro)
    addU `Tests.Gen5.UnkCtlW3.RootTy (mkConst ``True) (mkConst `Tests.Gen5.UnkCtlW3.HelperTy)
    unk [`Tests.Gen5.UnkCtlW3.RootTy]
  unless u3 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: helper type naming an unknown constant not reported ({u3})"
  let u4 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtlW3.CleanHelper (mkConst ``True) (mkConst ``True.intro)
    addU `Tests.Gen5.UnkCtlW3.CleanRoot (mkConst ``True) (mkConst `Tests.Gen5.UnkCtlW3.CleanHelper)
    unk [`Tests.Gen5.UnkCtlW3.CleanRoot]
  unless u4.isEmpty do throwError "GEN5 UNKNOWN CONTROL FAILED: clean control reported unknown ({u4})"
  logInfo m!"GEN5 UNKNOWN CONTROLS OK: 3 negatives reported unknown (root / helper value / helper type), clean control not reported"

run_cmd Lean.Elab.Command.liftTermElabM unknownControls

open Tools.ShippingGen5GDW3 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let roots := [``shapePost_binders, ``letsTyped_get, ``machCanonAp_machBoolBits', ``letQuoteEqC_of_post,
    ``letQuoteEqC_witness_from, ``letQuoteEqC_witness]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in roots do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: root {n} is not in the seen set"
  let suppliers := [``Tools.Prototype.ReaderTyped.shapePost_pack, ``Tools.Prototype.ReaderTyped.peel,
    ``Tools.Prototype.ReaderTyped.mapM_get, ``Tools.Prototype.ReaderTyped.shapePre_outs_ne,
    ``Tools.ShippingGen5DataOf.dataOfFrom_sound, ``Tools.ShippingGen5DataOfPure2.ok_letsTyped,
    ``Tools.ShippingGen5GDCover1.shapeAgree_witness_from, ``Tools.ShippingGen5Cover3Canon.LetQuoteEqC]
  for n in suppliers do
    if roots.contains n then throwError "GEN5 CLOSURE FAILED: expected supplier {n} must differ from the roots"
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: expected supplier {n} is not reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (W3): {seen.toList.length} constants, no forbidden constant, expected suppliers reached (distinct from the 6 roots), no unknown constant"

end Tests.Gen5.GDW3Check

import Tools.ShippingGen5Cover
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT (written in g5cv-r2; the SHA of the first successful Pod build is recorded here by a comment-only commit). Clean build is the coder's. No sorry / axiom / native_decide.

/-! # DG-COVER pure core (U-C1 … U-C5) checks (Tools/ShippingGen5Cover.lean; scripts/gen5/DG_COVER_FREEZE.md §4, §10)

TYPE: every theorem is compared (`checkExpected`) with an independently written `Expected…` statement. MUTANT: one-place changes, well-typed,
rejected by `checkMutant` — a signature / defeq rejection, NOT a semantic counterexample. AXIOMS: standard axioms only. CLOSURE: a walk over the
constants the unit mentions (types, and the explicit values of theorem / definition / opaque constants), rejecting `sorryAx` and the native-reduction
axioms. The walk itself is exercised on negative controls built in memory (a direct use, a use through a helper in another namespace, an opaque with
an explicit value) and on unrelated clean controls; an unknown constant is only logged. -/

namespace Tests.Gen5.CoverCheck
open Lean Meta Elab
open Tools.ShippingGen5Sem Tools.ShippingGen5Cover Tests.Gen3.ExpectedType
open Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge Tools.ShippingUnifiedSource Sparkle.Compiler.Elab Sparkle.Compiler.MachInstOrigin
open Tools.ShippingMachineRef (reads)

section Expected

def ExpectedRowAIff : Prop := ∀ d : MachineData, RowA d = true ↔
  (d.shape.insts.length ≤ d.nIn ∧ d.shape.instOrigins.length = d.shape.insts.length ∧
   ∀ k < d.shape.insts.length, (∀ l ∈ callArgs d k, l < d.ls.length) ∧
     ∀ cb aw dw, originOf d k = InstOrigin.mem cb aw dw → (callArgs d k).length = 4)

def ExpectedRowBIff : Prop := ∀ d : MachineData, RowB d = true ↔
  ∀ k < d.shape.insts.length, callKind d k ≠ MixedGateBinder.domain ∧
    ∀ cb aw dw, originOf d k = InstOrigin.mem cb aw dw →
      ∃ l0 l1 l2 l3, callArgs d k = [l0, l1, l2, l3] ∧ callKind d k = MixedGateBinder.bits dw ∧
        letSort d l0 = some (SType.bits aw) ∧ letSort d l1 = some (SType.bits dw) ∧
        letSort d l2 = some SType.bool ∧ letSort d l3 = some (SType.bits aw)

def ExpectedRowCIff : Prop := ∀ d : MachineData, RowC d = true ↔
  ∀ k < d.shape.insts.length, ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true

def ExpectedGenWFIff : Prop := ∀ d : MachineData, GenWF d = true ↔ (RowA d = true ∧ (RowB d = true ∧ RowC d = true))

def ExpectedOfRows : Prop := ∀ {d : MachineData} (h : GenWFRows d), GenWF d = true

def ExpectedToRows : Prop := ∀ {d : MachineData} (h : GenWF d = true), GenWFRows d

def ExpectedRowsIff : Prop := ∀ d : MachineData, GenWFRows d ↔
  (d.shape.insts.length ≤ d.nIn ∧ d.shape.instOrigins.length = d.shape.insts.length ∧
   (∀ k < d.shape.insts.length, ∀ l ∈ callArgs d k, l < d.ls.length) ∧
   (∀ k < d.shape.insts.length, ∀ cb aw dw, originOf d k = InstOrigin.mem cb aw dw → (callArgs d k).length = 4) ∧
   (∀ k < d.shape.insts.length, callKind d k ≠ MixedGateBinder.domain) ∧
   (∀ k < d.shape.insts.length, ∀ cb aw dw, originOf d k = InstOrigin.mem cb aw dw →
      ∃ l0 l1 l2 l3, callArgs d k = [l0, l1, l2, l3] ∧ callKind d k = MixedGateBinder.bits dw ∧
        letSort d l0 = some (SType.bits aw) ∧ letSort d l1 = some (SType.bits dw) ∧
        letSort d l2 = some SType.bool ∧ letSort d l3 = some (SType.bits aw)) ∧
   (∀ k < d.shape.insts.length, ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true))

def ExpectedCleanLen : Prop := ∀ (d : MachineData) (k : Nat), (cleanLets d k).length = d.ls.length

def ExpectedReadsMono : Prop :=
  ∀ {okB okV okB' okV' : Nat → Bool} (hb : ∀ j, okB j = true → okB' j = true) (hv : ∀ j, okV j = true → okV' j = true),
    ∀ {s : SType} (t : Term s), reads okB okV t = true → reads okB' okV' t = true

def ExpectedPosOkMono : Prop :=
  ∀ (d : MachineData) {k k' : Nat} (hk : k ≤ k') {clean clean' : List Bool}
    (hc : ∀ i, clean.getD i false = true → clean'.getD i false = true) (p : Nat),
      posOk d k clean p = true → posOk d k' clean' p = true

def ExpectedCleanMono : Prop :=
  ∀ (d : MachineData) {k k' : Nat} (hk : k ≤ k') (l : Nat),
    (cleanLets d k)[l]? = some true → (cleanLets d k')[l]? = some true

def ExpectedCloseIn : Prop := ∀ (nDecl kI n k i : Nat) (hi : i < nDecl),
  machClose kI n k 0 (machIn i) = Expr.bvar (nDecl + kI + n + k - 1 - (nDecl - 1 - i))

def ExpectedCloseInst : Prop := ∀ (nDecl kI n k j : Nat) (hj : j < kI),
  machClose kI n k 0 (machInstOut j) = Expr.bvar (nDecl + kI + n + k - 1 - (nDecl + j))

def ExpectedCloseSlot : Prop := ∀ (nDecl kI n k i : Nat) (hi : i < n),
  machClose kI n k 0 (machSlot i) = Expr.bvar (nDecl + kI + n + k - 1 - (nDecl + kI + i))

def ExpectedCloseLet : Prop := ∀ (nDecl kI n k j : Nat) (hj : j < k),
  machClose kI n k 0 (machLet j) = Expr.bvar (nDecl + kI + n + k - 1 - (nDecl + kI + n + j))

def ExpectedKD : Prop := ∀ (d : MachineData) (h : d.shape.insts.length ≤ d.nIn),
  d.nIn - d.shape.insts.length + d.shape.insts.length = d.nIn

def ExpectedCallKind : Prop := ∀ (d : MachineData) {k : Nat} (hk : k < d.shape.insts.length),
  ∀ (hn : d.shape.insts.length ≤ d.nIn)
    (hb : (d.shape.binders[d.nIn - d.shape.insts.length + k]?).map (·.2) = some (d.shape.insts[k]'hk).2.2),
  callKind d k = (d.shape.insts[k]'hk).2.2

/-- Mutant: RowA's memory-arity conjunct dropped. -/
def MutRowADropA4 : Prop := ∀ d : MachineData, RowA d = true ↔
  (d.shape.insts.length ≤ d.nIn ∧ d.shape.instOrigins.length = d.shape.insts.length ∧
   ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, l < d.ls.length)

/-- Mutant: RowB with `.domain` replaced by `.bool`. -/
def MutRowBBool : Prop := ∀ d : MachineData, RowB d = true ↔
  ∀ k, k < d.shape.insts.length → callKind d k ≠ .bool ∧
    ∀ cb aw dw, originOf d k = .mem cb aw dw →
      ∃ l0 l1 l2 l3, callArgs d k = [l0, l1, l2, l3] ∧ callKind d k = .bits dw ∧
        letSort d l0 = some (.bits aw) ∧ letSort d l1 = some (.bits dw) ∧
        letSort d l2 = some .bool ∧ letSort d l3 = some (.bits aw)

/-- Mutant: `cleanLets_mono` with the call order reversed (`k' ≤ k`). -/
def MutCleanMonoRev : Prop :=
  ∀ (d : MachineData) {k k' : Nat} (hk : k' ≤ k) (l : Nat),
    (cleanLets d k)[l]? = some true → (cleanLets d k')[l]? = some true

/-- Mutant: the instance-output position shifted by one. -/
def MutCloseInstShift : Prop := ∀ (nDecl kI n k j : Nat) (hj : j < kI),
  machClose kI n k 0 (machInstOut j) = inputExpr (nDecl + kI + n + k) (nDecl + j + 1)

/-- Mutant: `GenWFRows` unfolded with the RowC conjunct replaced by `True`. -/
def MutRowsIffNoC : Prop := ∀ d : MachineData, GenWFRows d ↔
  (d.shape.insts.length ≤ d.nIn ∧ d.shape.instOrigins.length = d.shape.insts.length ∧
   (∀ k < d.shape.insts.length, ∀ l ∈ callArgs d k, l < d.ls.length) ∧
   (∀ k < d.shape.insts.length, ∀ cb aw dw, originOf d k = InstOrigin.mem cb aw dw → (callArgs d k).length = 4) ∧
   (∀ k < d.shape.insts.length, callKind d k ≠ MixedGateBinder.domain) ∧
   (∀ k < d.shape.insts.length, ∀ cb aw dw, originOf d k = InstOrigin.mem cb aw dw →
      ∃ l0 l1 l2 l3, callArgs d k = [l0, l1, l2, l3] ∧ callKind d k = MixedGateBinder.bits dw ∧
        letSort d l0 = some (SType.bits aw) ∧ letSort d l1 = some (SType.bits dw) ∧
        letSort d l2 = some SType.bool ∧ letSort d l3 = some (SType.bits aw)) ∧
   True)

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``rowA_iff ``ExpectedRowAIff
  checkExpected ``rowB_iff ``ExpectedRowBIff
  checkExpected ``rowC_iff ``ExpectedRowCIff
  checkExpected ``genWF_iff ``ExpectedGenWFIff
  checkExpected ``genWF_of_rows ``ExpectedOfRows
  checkExpected ``genWFRows_of_genWF ``ExpectedToRows
  checkExpected ``genWFRows_iff ``ExpectedRowsIff
  checkExpected ``cleanLets_length ``ExpectedCleanLen
  checkExpected ``reads_mono ``ExpectedReadsMono
  checkExpected ``posOk_mono ``ExpectedPosOkMono
  checkExpected ``cleanLets_mono ``ExpectedCleanMono
  checkExpected ``machClose_machIn ``ExpectedCloseIn
  checkExpected ``machClose_machInstOut ``ExpectedCloseInst
  checkExpected ``machClose_machSlot ``ExpectedCloseSlot
  checkExpected ``machClose_machLet ``ExpectedCloseLet
  checkExpected ``kDOf_add_len ``ExpectedKD
  checkExpected ``callKind_eq_inst ``ExpectedCallKind
  checkMutant ``rowA_iff ``MutRowADropA4
  checkMutant ``rowB_iff ``MutRowBBool
  checkMutant ``cleanLets_mono ``MutCleanMonoRev
  checkMutant ``machClose_machInstOut ``MutCloseInstShift
  checkMutant ``genWFRows_iff ``MutRowsIffNoC

-- Axiom audit (standard axioms only).
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``rowA_iff, ``rowB_iff, ``rowC_iff, ``genWF_iff, ``genWF_of_rows, ``genWFRows_of_genWF, ``genWFRows_iff, ``cleanLets_length,
      ``reads_mono, ``posOk_mono, ``cleanLets_mono, ``machClose_machIn, ``machClose_machInstOut, ``machClose_machSlot,
      ``machClose_machLet, ``kDOf_add_len, ``callKind_eq_inst] do
    checkAxioms n

/-! ## Closure audit -/

/-- The value of a constant, for theorem / definition / opaque constants alike (`ConstantInfo.value?` skips opaques). -/
def valueOfCI : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- Walk the constants mentioned by `root`'s type and explicit value; unknown constants are recorded in the second component, not failed. -/
partial def closureOf (env : Environment) (root : Name) : StateT (NameSet × NameSet) MetaM Unit := do
  if (← get).1.contains root then return
  modify fun (s, u) => (s.insert root, u)
  match env.find? root with
  | none => modify fun (s, u) => (s, u.insert root)
  | some ci =>
    for c in ci.type.getUsedConstants do closureOf env c
    match valueOfCI ci with
    | some v => for c in v.getUsedConstants do closureOf env c
    | none => pure ()
    match ci with
    | .inductInfo v => for c in v.ctors do closureOf env c
    | _ => pure ()

def forbiddenConsts : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler]

def closureHits (env : Environment) (roots : List Name) : MetaM (NameSet × NameSet × List Name) := do
  let (_, (seen, unk)) ← (roots.forM (closureOf env)).run ({}, {})
  pure (seen, unk, forbiddenConsts.filter seen.contains)

-- Negative controls (built in memory, no `sorry` token in this file): each must be detected; clean controls must not be.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let bad := mkApp2 (mkConst ``sorryAx [Level.zero]) tru (mkConst ``Bool.false)
    let ok := mkConst ``True.intro
    addDecl (.thmDecl { name := `CoverCtl.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `CoverCtl.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `CoverCtl.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `CoverCtl.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`CoverCtl.direct, `CoverCtl.viaHelper, `CoverCtl.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 COVER CLOSURE CONTROL FAILED: {n} not detected"
    for n in [`CoverCtl.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 COVER CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 COVER CLOSURE CONTROLS OK: 3 negative controls detected, 2 unrelated clean controls clean"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let roots := [``rowA_iff, ``rowB_iff, ``rowC_iff, ``genWF_iff, ``genWF_of_rows, ``genWFRows_of_genWF, ``genWFRows_iff, ``cleanLets_length,
      ``reads_mono, ``posOk_mono, ``cleanLets_mono, ``machClose_machIn, ``machClose_machInstOut, ``machClose_machSlot,
      ``machClose_machLet, ``kDOf_add_len, ``callKind_eq_inst]
  let (seen, unk, hits) ← closureHits env roots
  unless hits.isEmpty do throwError "GEN5 COVER CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "dataOf").length > 1 || (s.splitOn "native").length > 1 then
      throwError "GEN5 COVER CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do logInfo m!"GEN5 COVER CLOSURE: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 COVER CLOSURE OK: {seen.toList.length} constants, no forbidden constant"

#print axioms rowA_iff
#print axioms cleanLets_mono
#print axioms genWFRows_of_genWF

end Tests.Gen5.CoverCheck

import Tools.ShippingGen5Cover3
import Tests.Gen5.CoverNegCheck
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT (g5cv-r6 work in progress). No sorry / axiom / native_decide in source.

/-! # DG-COVER rev4 (Tools/ShippingGen5Cover3.lean) checks

TYPE: every theorem (and the `FStep` constructors, and `ShapeAgree` field-wise) is compared by the SAME comparer (`checkExpected`: binder names / binder info /
`==` then `isDefEq` fallback, logged) with an `Exp…` statement written here from the freeze text `scripts/gen5/DG_COVER_FREEZE_REV4.md`, spelled out without the
invariant definitions of `Tools.ShippingGen5Cover3` (`FullInv`, `RangeInv`, … are re-spelled; only the scanner primitives `MentionsPh` / `LetReach` / `LetEdge` of
Cover2, `FStep`/`FReach` and the data-structure projections are shared). `readsOfQuoteStmt` is compared with `Tests.Gen5.CoverNegCheck.ReadsOfQuoteStmt`.
MUTANT: one-place changes, each well-typed, rejected by the same comparer — a signature / defeq rejection, NOT a semantic counterexample.
AXIOMS: standard axioms only. CLOSURE: explicit value-closure walk over `getUsedConstants`; negative controls are built in memory inside `withoutModifyingEnv`
(they print "declaration uses `sorry`" warnings: 意図した負例 3 件) and unrelated clean controls must not be flagged. The closure is of explicit bodies, not a claim
about `extern` implementations or raw projections. -/

namespace Tests.Gen5.Cover3Check
open Lean Meta Elab
open Tools.ShippingGen5Cover3 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingMixedSourceBridge Tools.ShippingUnifiedSource Tools.ShippingMachineAuto
open Sparkle.Compiler.MachInstOrigin
open Tools.ShippingGen5Cover2 (MentionsPh LetReach LetEdge)
open Tools.ShippingGen5Sem (kDOf callArgs callKind originOf cleanLets posOk)

section Expected

def ExpPh (nDecl kI n k : Nat) (v : Lean.Expr) : Prop :=
  (∀ i, MentionsPh "_machIn" i v → i < nDecl) ∧ (∀ j, MentionsPh "_machInst" j v → j < kI) ∧
  (∀ i, MentionsPh "_machSlot" i v → i < n) ∧ (∀ j, MentionsPh "_machLet" j v → j < k)

def ExpCOI (st : MachRead) : Prop :=
  (∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ i, MentionsPh "_machLet" i v → i < j) ∧
  (∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ m, MentionsPh "_machInst" m v → m < st.insts.size) ∧
  (∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) → ∀ a ∈ js, a < st.lets.size) ∧
  (∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) → ∀ a ∈ js, ∀ i, LetReach st.lets a i →
    ∀ (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[i]? = some (nm, kd, v) → ∀ m, MentionsPh "_machInst" m v → m < k)

def ExpRange (nDecl : Nat) (st : MachRead) : Prop :=
  (∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) →
    ExpPh nDecl st.insts.size st.kinds.size j v) ∧
  (∀ w ∈ st.ws, w.1 < st.kinds.size ∧ ExpPh nDecl st.insts.size st.kinds.size st.lets.size w.2)

def ExpFull (nDecl : Nat) (st : MachRead) : Prop :=
  ExpCOI st ∧ ExpRange nDecl st ∧ st.instOrigins.size = st.insts.size ∧
  ((∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) → r ≠ .domain) ∧
   (∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) →
     ∀ cb aw dw, st.instOrigins[k]? = some (.mem cb aw dw) → js.length = 4 ∧ r = .bits dw))

/-! ### U-D1 -/

def ExpLooseMachClose : Prop := ∀ (nDecl kI n k : Nat),
    ∀ (d : Nat) (v : Lean.Expr) (b : Nat), (∀ b', ¬ LooseOcc d v b') →
      Tools.ShippingGen5Cover2.PhInRange nDecl kI n k v →
      LooseOcc d (machClose kI n k d v) b →
      ∃ p, MentionPos nDecl kI n k v p ∧ b = nDecl + kI + n + k - 1 - p

def MutLooseMachClose : Prop := ∀ (nDecl kI n k : Nat),
    ∀ (d : Nat) (v : Lean.Expr) (b : Nat), (∀ b', ¬ LooseOcc d v b') →
      Tools.ShippingGen5Cover2.PhInRange nDecl kI n k v →
      LooseOcc d (machClose kI n k d v) b →
      ∃ p, MentionPos nDecl kI n k v p ∧ b = nDecl + kI + n + k - p

def ExpReadsOfQuoteStmt : Prop :=
  ∀ (dom : Lean.Expr) (nDecl kI n k : Nat) (bpos vpos : Nat → Nat) (okP : Nat → Bool)
    {s : SType} (t : Term s) (v : Lean.Expr),
    Tools.ShippingGen5Cover2.PhInRange nDecl kI n k v →
    (∀ j, bpos j < nDecl + kI + n + k) → (∀ j, vpos j < nDecl + kI + n + k) →
    (∀ b, ¬ LooseOcc 0 v b) →
    quote dom (fun j => inputExpr (nDecl + kI + n + k) (bpos j))
      (fun j => inputExpr (nDecl + kI + n + k) (vpos j)) t = machClose kI n k 0 v →
    (∀ p, MentionPos nDecl kI n k v p → okP p = true) →
    Tools.ShippingMachineRef.reads (fun j => okP (bpos j)) (fun j => okP (vpos j)) t = true

/-- Mutant: the rev1 statement (no `PhInRange` premise). -/
def MutReadsOfQuoteStmtRev1 : Prop :=
  ∀ (dom : Lean.Expr) (nDecl kI n k : Nat) (bpos vpos : Nat → Nat) (okP : Nat → Bool)
    {s : SType} (t : Term s) (v : Lean.Expr),
    (∀ j, bpos j < nDecl + kI + n + k) → (∀ j, vpos j < nDecl + kI + n + k) →
    (∀ b, ¬ LooseOcc 0 v b) →
    quote dom (fun j => inputExpr (nDecl + kI + n + k) (bpos j))
      (fun j => inputExpr (nDecl + kI + n + k) (vpos j)) t = machClose kI n k 0 v →
    (∀ p, MentionPos nDecl kI n k v p → okP p = true) →
    Tools.ShippingMachineRef.reads (fun j => okP (bpos j)) (fun j => okP (vpos j)) t = true

def ExpReadsQuoteLoose : Prop := ∀ (dom : Lean.Expr) (bb vv : Nat → Nat) (P : Nat → Bool) {s : SType} (t : Term s)
    (h : ∀ b, LooseOcc 0 (quote dom (fun j => Lean.Expr.bvar (bb j)) (fun j => Lean.Expr.bvar (vv j)) t) b → P b = true),
    Tools.ShippingMachineRef.reads (fun j => P (bb j)) (fun j => P (vv j)) t = true

/-! ### U-D2 -/

def ExpFullEmpty : Prop := ∀ (nDecl : Nat) (st : MachRead) (hl : st.lets = #[]) (hi : st.insts = #[]) (ho : st.instOrigins = #[]) (hw : st.ws = #[]),
    ExpFull nDecl st

def ExpFullStep : Prop := ∀ {nDecl : Nat} {st st' : MachRead} (h : ExpFull nDecl st) (hs : FStep nDecl st st'), ExpFull nDecl st'

def ExpFullReach : Prop := ∀ {nDecl : Nat} {st0 st : MachRead} (h : ExpFull nDecl st0) (hr : FReach nDecl st0 st), ExpFull nDecl st

def ExpSizesMono : Prop := ∀ {nDecl : Nat} {a b : MachRead} (hr : FReach nDecl a b),
    a.lets.size ≤ b.lets.size ∧ a.insts.size ≤ b.insts.size ∧ a.kinds.size ≤ b.kinds.size

def ExpGroupCOI : Prop := ∀ (st : MachRead) (c : Name) (js : List Nat) (rs : List MixedGateBinder) (os : List InstOrigin)
    (h : ExpCOI st) (hj : ∀ a ∈ js, a < st.lets.size),
    ExpCOI { st with insts := st.insts ++ (rs.map fun r => (c, js, r)).toArray, instOrigins := st.instOrigins ++ os.toArray }

def ExpLetRange : Prop := ∀ {nDecl : Nat} {st0 st : MachRead} (h0 : ExpFull nDecl st0) (hr : FReach nDecl st0 st)
    {j : Nat} {nm : Name} {kd : MixedGateBinder} {v : Lean.Expr} (hj : st.lets[j]? = some (nm, kd, v)),
    ExpPh nDecl st.insts.size st.kinds.size st.lets.size v

def MutLetRange : Prop := ∀ {nDecl : Nat} {st0 st : MachRead} (h0 : ExpFull nDecl st0) (hr : FReach nDecl st0 st)
    {j : Nat} {nm : Name} {kd : MixedGateBinder} {v : Lean.Expr} (hj : st.lets[j]? = some (nm, kd, v)),
    (∀ i, MentionsPh "_machIn" i v → i < nDecl) ∧ (∀ j, MentionsPh "_machInst" j v → j < st.insts.size) ∧
    (∀ i, MentionsPh "_machSlot" i v → i < st.kinds.size) ∧ (∀ j, MentionsPh "_machLet" j v → j ≤ st.lets.size)

def ExpWriteRange : Prop := ∀ {nDecl : Nat} {st0 st : MachRead} (h0 : ExpFull nDecl st0) (hr : FReach nDecl st0 st)
    {w : Nat × Lean.Expr} (hw : w ∈ st.ws),
    w.1 < st.kinds.size ∧ ExpPh nDecl st.insts.size st.kinds.size st.lets.size w.2

def ExpResultRange : Prop := ∀ {nDecl : Nat} {st1 st : MachRead} (hr : FReach nDecl st1 st) {v : Lean.Expr}
    (hv : ExpPh nDecl st1.insts.size st1.kinds.size st1.lets.size v),
    ExpPh nDecl st.insts.size st.kinds.size st.lets.size v

def ExpMachNext : Prop := ∀ {nDecl : Nat} {st : MachRead} (h : ExpRange nDecl st) {i : Nat} (hi : i < st.kinds.size),
    ExpPh nDecl st.insts.size st.kinds.size st.lets.size (machNext i st.ws.toList)

def ExpBundleParts : Prop := ∀ {nDecl kI n k : Nat},
    ∀ (m : Nat) (e : Lean.Expr) (ps : List Lean.Expr), machBundleParts? m e = some ps → ExpPh nDecl kI n k e →
      ∀ p ∈ ps, ExpPh nDecl kI n k p

def ExpResults : Prop := ∀ {nDecl kI n k : Nat} (sel : Option (Name × Nat × Nat)) (ctor? : Option Name) (m : Nat) (v : Lean.Expr)
    (es : List Lean.Expr) (h : machResults? sel ctor? m v = some es) (hv : ExpPh nDecl kI n k v),
    ∀ e ∈ es, ExpPh nDecl kI n k e

/-- constructors of `FStep`, spelled out. -/
def ExpFStepLetv : Prop := ∀ {nDecl : Nat} (st : MachRead) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr),
    ExpPh nDecl st.insts.size st.kinds.size st.lets.size v → FStep nDecl st { st with lets := st.lets.push (nm, kd, v) }

def ExpFStepInst : Prop := ∀ {nDecl : Nat} (st : MachRead) (c : Name) (js : List Nat) (r : MixedGateBinder) (o : InstOrigin),
    (∀ a ∈ js, a < st.lets.size) → r ≠ .domain → (∀ cb aw dw, o = .mem cb aw dw → js.length = 4 ∧ r = .bits dw) →
    FStep nDecl st { st with insts := st.insts.push (c, js, r), instOrigins := st.instOrigins.push o }

def ExpFStepGroup : Prop := ∀ {nDecl : Nat} (st : MachRead) (c : Name) (js : List Nat) (rs : List MixedGateBinder) (os : List InstOrigin),
    rs.length = os.length → (∀ a ∈ js, a < st.lets.size) → (∀ r ∈ rs, r ≠ .domain) →
    (∀ o ∈ os, ∀ cb aw dw, o ≠ .mem cb aw dw) →
    FStep nDecl st { st with insts := st.insts ++ (rs.map fun r => (c, js, r)).toArray, instOrigins := st.instOrigins ++ os.toArray }

def MutFStepGroup : Prop := ∀ {nDecl : Nat} (st : MachRead) (c : Name) (js : List Nat) (rs : List MixedGateBinder) (os : List InstOrigin),
    (∀ a ∈ js, a < st.lets.size) → (∀ r ∈ rs, r ≠ .domain) →
    (∀ o ∈ os, ∀ cb aw dw, o ≠ .mem cb aw dw) →
    FStep nDecl st { st with insts := st.insts ++ (rs.map fun r => (c, js, r)).toArray, instOrigins := st.instOrigins ++ os.toArray }

def ExpFStepSlot : Prop := ∀ {nDecl : Nat} (st : MachRead) (kd : MixedGateBinder) (i : Nat) (nm : Name),
    FStep nDecl st { st with kinds := st.kinds.push kd, inits := st.inits.push i, names := st.names.push nm }

def ExpFStepSlots : Prop := ∀ {nDecl : Nat} (st : MachRead) (ks : List MixedGateBinder) (is : List Nat) (ns : List Name),
    FStep nDecl st { st with kinds := st.kinds ++ ks.toArray, inits := st.inits ++ is.toArray, names := st.names ++ ns.toArray }

def ExpFStepWs : Prop := ∀ {nDecl : Nat} (st : MachRead) (ws' : Array (Nat × Lean.Expr)),
    (∀ w ∈ ws', w.1 < st.kinds.size ∧ ExpPh nDecl st.insts.size st.kinds.size st.lets.size w.2) → FStep nDecl st { st with ws := ws' }

/-! ### U-D3 -/

def ExpLetQuoteEq (d : MachineData) (st : MachRead) : Prop :=
  ∀ (j : Nat) (hj : j < d.ls.length) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) →
    quote d.dom (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.bpos i))
                (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.vpos i)) (d.ls[j]'hj).2
      = machClose st.insts.size st.kinds.size st.lets.size 0 v

def ExpLetsNoLoose (st : MachRead) : Prop :=
  ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ b, ¬ LooseOcc 0 v b

def ExpShapeAgree (d : MachineData) (st : MachRead) : Prop :=
  d.shape.insts = st.insts.toList ∧ d.shape.instOrigins = st.instOrigins.toList ∧ d.ss.length = st.kinds.size ∧
  d.ls.length = st.lets.size ∧ d.shape.insts.length ≤ d.nIn

def ExpCleanGet : Prop := ∀ (d : MachineData) (k l : Nat) (hl : l < d.ls.length),
    (cleanLets d k)[l]? = some (Tools.ShippingMachineRef.reads
      (fun j => posOk d k ((cleanLets d k).take l) (d.bpos j)) (fun j => posOk d k ((cleanLets d k).take l) (d.vpos j)) (d.ls[l]'hl).2)

def ExpLetReachEdge : Prop := ∀ {lets : MachLets} {a l j : Nat} (h : LetReach lets a l) (e : LetEdge lets l j), LetReach lets a j

def ExpRowA2 : Prop := ∀ {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) (hi : st.instOrigins.size = st.insts.size),
    d.shape.instOrigins.length = d.shape.insts.length

def ExpRowA3 : Prop := ∀ {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : ExpFull nDecl st),
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, l < d.ls.length

def MutRowA3 : Prop := ∀ {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : ExpFull nDecl st),
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, l ≤ d.ls.length

def ExpRowA4B23 : Prop := ∀ {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : ExpFull nDecl st),
    ∀ k, k < d.shape.insts.length → ∀ cb aw dw, originOf d k = .mem cb aw dw →
      (callArgs d k).length = 4 ∧ (d.shape.insts[k]?).map (·.2.2) = some (.bits dw)

def ExpRowB1 : Prop := ∀ {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : ExpFull nDecl st)
    (hcb : ∀ k (hk : k < d.shape.insts.length), (d.shape.binders[kDOf d + k]?).map (·.2) = some (d.shape.insts[k]'hk).2.2),
    ∀ k, k < d.shape.insts.length → callKind d k ≠ .domain

def ExpRowC : Prop := ∀ {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) (hi : ExpFull (kDOf d) st)
    (hq : ExpLetQuoteEq d st) (hnl : ExpLetsNoLoose st)
    (hb : ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length) (hv : ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length),
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true

def MutRowCNoNL : Prop := ∀ {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) (hi : ExpFull (kDOf d) st)
    (hq : ExpLetQuoteEq d st)
    (hb : ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length) (hv : ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length),
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true

end Expected

theorem shapeAgree_fields (d : MachineData) (st : MachRead) : ShapeAgree d st ↔ ExpShapeAgree d st :=
  ⟨fun h => ⟨h.insts, h.origins, h.slots, h.lets, h.nIn⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩
theorem letQuoteEq_iff (d : MachineData) (st : MachRead) : LetQuoteEq d st ↔ ExpLetQuoteEq d st := Iff.rfl
theorem letsNoLoose_iff (st : MachRead) : LetsNoLoose st ↔ ExpLetsNoLoose st := Iff.rfl

/-- `thm`'s type is a definition (a `Prop` statement such as `ReadsOfQuoteStmt`): unfold the head constant, then compare binder by binder. -/
def checkExpectedUnf (thm exp : Name) : MetaM Unit := do
  let ci ← getConstInfo thm
  let a ← whnfD ci.type
  let e ← stmtOf exp
  cmpTele s!"{thm}" a e
  logInfo m!"GEN3 TYPE OK (unfolded) {thm} against {exp}"

/-- any constant's type (constructors included) against an `Exp…` def. -/
def checkExpectedC (thm exp : Name) : MetaM Unit := do
  let ci ← getConstInfo thm
  let e ← stmtOf exp
  cmpTele s!"{thm}" ci.type e
  logInfo m!"GEN3 TYPE OK (constant type) {thm} against {exp}"

def checkMutantC (thm mt : Name) : MetaM Unit := do
  let ci ← getConstInfo thm
  let e ← stmtOf mt
  let accepted ← withoutModifyingState do
    try
      cmpTele s!"{thm} vs mutant {mt}" ci.type e
      pure true
    catch _ => pure false
  if accepted then throwError "GEN3 MUTANT ACCEPTED: {mt} matches {thm}"
  logInfo m!"GEN3 MUTANT REJECTED {mt} (against {thm})"

def checkMutantUnf (thm mt : Name) : MetaM Unit := do
  let ci ← getConstInfo thm
  let a ← whnfD ci.type
  let e ← stmtOf mt
  let accepted ← withoutModifyingState do
    try
      cmpTele s!"{thm} vs mutant {mt}" a e
      pure true
    catch _ => pure false
  if accepted then throwError "GEN3 MUTANT ACCEPTED: {mt} matches {thm}"
  logInfo m!"GEN3 MUTANT REJECTED {mt} (against {thm})"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``looseOcc_machClose ``ExpLooseMachClose
  checkExpected ``reads_of_quote_loose ``ExpReadsQuoteLoose
  checkExpectedUnf ``readsOfQuoteStmt ``ExpReadsOfQuoteStmt
  checkExpected ``fullInv_of_empty ``ExpFullEmpty
  checkExpected ``fullInv_step ``ExpFullStep
  checkExpected ``fullInv_reach ``ExpFullReach
  checkExpected ``reach_sizes_mono ``ExpSizesMono
  checkExpected ``callOrderInv_group ``ExpGroupCOI
  checkExpected ``letRange_final ``ExpLetRange
  checkExpected ``writeRange_final ``ExpWriteRange
  checkExpected ``resultRange_final ``ExpResultRange
  checkExpected ``machNext_range ``ExpMachNext
  checkExpected ``machBundleParts_range ``ExpBundleParts
  checkExpected ``machResults_range ``ExpResults
  checkExpectedC ``FStep.letv ``ExpFStepLetv
  checkExpectedC ``FStep.inst ``ExpFStepInst
  checkExpectedC ``FStep.group ``ExpFStepGroup
  checkExpectedC ``FStep.slot ``ExpFStepSlot
  checkExpectedC ``FStep.slots ``ExpFStepSlots
  checkExpectedC ``FStep.ws ``ExpFStepWs
  checkExpected ``cleanLets_getElem ``ExpCleanGet
  checkExpected ``letReach_edge ``ExpLetReachEdge
  checkExpected ``rowA2_of_inv ``ExpRowA2
  checkExpected ``rowA3_of_inv ``ExpRowA3
  checkExpected ``rowA4B23_mem_of_inv ``ExpRowA4B23
  checkExpected ``rowB1_of_inv ``ExpRowB1
  checkExpected ``rowC_of_reader ``ExpRowC
  -- mutants (same comparer; signature / defeq rejection, not semantic counterexamples)
  checkMutant ``looseOcc_machClose ``MutLooseMachClose
  checkMutantUnf ``readsOfQuoteStmt ``MutReadsOfQuoteStmtRev1
  checkMutant ``letRange_final ``MutLetRange
  checkMutant ``rowC_of_reader ``MutRowCNoNL
  checkMutantC ``FStep.group ``MutFStepGroup
  checkMutant ``rowA3_of_inv ``MutRowA3

/-! ## `readsOfQuoteStmt` against `Tests.Gen5.CoverNegCheck.ReadsOfQuoteStmt`

The comparer does NOT identify the separately defined recursive scanners of the two files (first attempt: `GEN3 CHECK FAILED … LooseOcc`: `CoverNegCheck.LooseOcc`
vs `Tools.ShippingGen5Cover3.LooseOcc` are not `isDefEq` on an fvar argument). So the freeze's "compare with `CoverNegCheck.ReadsOfQuoteStmt` by defeq" is replaced by
a proved equivalence of the scanners and a derivation of the CoverNegCheck statement from `readsOfQuoteStmt`. -/

theorem mentionsPh_iff (tag : String) (i : Nat) : ∀ e : Lean.Expr,
    Tests.Gen5.CoverNegCheck.MentionsPh tag i e ↔ MentionsPh tag i e := by
  intro e
  induction e with
  | app f a ihf iha => simp only [Tests.Gen5.CoverNegCheck.MentionsPh, MentionsPh, ihf, iha]
  | lam nm t b bi iht ihb => simp only [Tests.Gen5.CoverNegCheck.MentionsPh, MentionsPh, iht, ihb]
  | forallE nm t b bi iht ihb => simp only [Tests.Gen5.CoverNegCheck.MentionsPh, MentionsPh, iht, ihb]
  | fvar id =>
    rcases id with ⟨nm⟩
    match nm with
    | .num (.str .anonymous t) j => exact Iff.rfl
    | .anonymous => exact Iff.rfl
    | .str _ _ => exact Iff.rfl
    | .num .anonymous _ => exact Iff.rfl
    | .num (.str (.str _ _) _) _ => exact Iff.rfl
    | .num (.str (.num _ _) _) _ => exact Iff.rfl
    | .num (.num _ _) _ => exact Iff.rfl
  | _ => exact Iff.rfl

theorem looseOcc_iff : ∀ (e : Lean.Expr) (d b : Nat), Tests.Gen5.CoverNegCheck.LooseOcc d e b ↔ LooseOcc d e b := by
  intro e
  induction e with
  | app f a ihf iha => intro d b; simp only [Tests.Gen5.CoverNegCheck.LooseOcc, LooseOcc, ihf, iha]
  | lam nm t b' bi iht ihb => intro d b; simp only [Tests.Gen5.CoverNegCheck.LooseOcc, LooseOcc, iht, ihb]
  | forallE nm t b' bi iht ihb => intro d b; simp only [Tests.Gen5.CoverNegCheck.LooseOcc, LooseOcc, iht, ihb]
  | _ => intro d b; exact Iff.rfl

theorem negcheck_readsOfQuoteStmt : Tests.Gen5.CoverNegCheck.ReadsOfQuoteStmt := by
  intro dom nDecl kI n k bpos vpos okP s t v hr hb hv hn hq hm
  refine readsOfQuoteStmt dom nDecl kI n k bpos vpos okP t v ?_ hb hv ?_ hq ?_
  · exact ⟨fun i hi => hr.1 i ((mentionsPh_iff _ _ v).2 hi), fun i hi => hr.2.1 i ((mentionsPh_iff _ _ v).2 hi),
      fun i hi => hr.2.2.1 i ((mentionsPh_iff _ _ v).2 hi), fun i hi => hr.2.2.2 i ((mentionsPh_iff _ _ v).2 hi)⟩
  · exact fun b h => hn b ((looseOcc_iff v 0 b).2 h)
  · intro p hp
    apply hm
    rcases hp with ⟨i, hi, h, e⟩ | ⟨i, hi, h, e⟩ | ⟨i, hi, h, e⟩ | ⟨i, hi, h, e⟩
    · exact Or.inl ⟨i, hi, (mentionsPh_iff _ _ v).2 h, e⟩
    · exact Or.inr (Or.inl ⟨i, hi, (mentionsPh_iff _ _ v).2 h, e⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, (mentionsPh_iff _ _ v).2 h, e⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hi, (mentionsPh_iff _ _ v).2 h, e⟩))

/-! ## Kernel negative kept: `readsOfQuoteStmt` is not applicable to the rev1 refutation instance -/

theorem c3_example_not_in_range : ¬ Tools.ShippingGen5Cover2.PhInRange 0 0 0 1 (machLet 1) := by
  intro h
  have := h.2.2.2 1 (by simp [machLet, Tools.ShippingGen5Cover2.MentionsPh])
  omega

theorem c3_example_not_applicable :
    ¬ (Tools.ShippingGen5Cover2.PhInRange 0 0 0 1 (machLet 1) ∧ (∀ j, (fun _ : Nat => 0) j < 0 + 0 + 0 + 1)) := fun h => c3_example_not_in_range h.1

#print axioms Tests.Gen5.CoverNegCheck.r2_example_not_in_range

-- Axiom audit (standard axioms only).
def allThms : List Name :=
  [``looseOcc_machClose, ``reads_of_quote_loose, ``readsOfQuoteStmt, ``fullInv_of_empty, ``fullInv_step, ``fullInv_reach, ``reach_sizes_mono,
   ``callOrderInv_group, ``letRange_final, ``writeRange_final, ``resultRange_final, ``machNext_range, ``machBundleParts_range, ``machResults_range,
   ``cleanLets_getElem, ``letReach_edge, ``rowA2_of_inv, ``rowA3_of_inv, ``rowA4B23_mem_of_inv, ``rowB1_of_inv, ``rowC_of_reader,
   ``mentionsPh_iff, ``looseOcc_iff, ``negcheck_readsOfQuoteStmt, ``shapeAgree_fields, ``letQuoteEq_iff, ``letsNoLoose_iff, ``c3_example_not_in_range, ``c3_example_not_applicable]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in allThms do checkAxioms n

/-! ## Closure audit -/

def valueOfCI : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

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
    addDecl (.thmDecl { name := `Cover3Ctl.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `Cover3Ctl.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `Cover3Ctl.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `Cover3Ctl.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`Cover3Ctl.direct, `Cover3Ctl.viaHelper, `Cover3Ctl.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 COVER3 CLOSURE CONTROL FAILED: {n} not detected"
    for n in [`Cover3Ctl.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 COVER3 CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 COVER3 CLOSURE CONTROLS OK: 3 negative controls detected, 2 unrelated clean controls clean"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env allThms
  unless hits.isEmpty do throwError "GEN5 COVER3 CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "dataOf").length > 1 || (s.splitOn "native").length > 1 then
      throwError "GEN5 COVER3 CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do logInfo m!"GEN5 COVER3 CLOSURE: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 COVER3 CLOSURE OK: {seen.toList.length} constants, no forbidden constant"

#print axioms readsOfQuoteStmt
#print axioms fullInv_step
#print axioms rowC_of_reader

end Tests.Gen5.Cover3Check

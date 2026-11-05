# DG-COVER freeze rev4 — input/slot/write/result range suppliers, `ReadsOfQuoteStmt` proof, RowC glue, row mapping (Issue sparkle-gen5-dg-cover)

**FOR REVIEW — docs only. No Lean file was edited or elaborated for this document; every Lean text below is an unelaborated proposal, written against the
definitions read in this tree.** Base `3eb663df` (Cover2, scoped approved), branch `kjob/g5cv-r5`. Nothing here completes the Issue, M5 or FG. No guarantee, law, TRUSTED
boundary, FG scope or shared definition is changed or proposed to be changed; `GenWF` is not strengthened. No decision is requested.

Wording rule (as rev0–rev3): "not found" = *this investigation found no supplier or route*, never "impossible / not derivable". A mutant is a rejection of a changed statement
by signature / defeq, not a semantic counterexample. Conditional results are INTERMEDIATE. `PushReach`/`FReach` below are closure statements for abstract push sequences, **not** a
trace of the real reader.

## 0. Scope of this freeze (full types: §1–§3; everything else is the table of §4 and carries no type)

New files (phase 2, after approval): `Tools/ShippingGen5Cover3.lean` (imports `Tools.ShippingGen5Cover2`, `Tools.ShippingGen5Cover`; `namespace Tools.ShippingGen5Cover3`,
`set_option autoImplicit false`), `Tests/Gen5/Cover3Check.lean`; `lakefile.lean`: two `lean_lib` additions. Opens
`Lean Sparkle.Compiler.Elab Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Tools.ShippingGen5Cover2 Tools.ShippingGen5Sem Tools.ShippingGen5Cover Sparkle.Compiler.MachInstOrigin`.
Units: **U-D1** (`ReadsOfQuoteStmt` proved: §1), **U-D2** (range invariant, steps, hin/hsl/write/result suppliers: §2), **U-D3** (RowA/B/C glue from named interface premises: §3).
Edits to the compiler, `ShippingGen2Defs`, `T1Hyp`, `T1HypND`, `Elab*.lean`, `ShippingGen5SemGen.lean`, Cover/Cover2/CoverNegCheck: none.

Reader facts used (all read in this tree, Elab.lean):
- `machClose kI n k d` (:4255) rewrites exactly the four placeholder tags under `app`/`lam`/`forallE`; every other constructor is returned unchanged (rev3 §3 still applies).
- Placeholders enter an expression only through `machIn (j - d - env.length)` (:3914), `machSlot b` / `machSlot i` guarded by `i < st.kinds.size` (:3939, :3963) or `base = kinds.size` before the push (:3932-3936), `machLet j`/`machLetIndex` (:3743), `machInstOut k` (:4078).
- The fields of `MachRead` that the result record reads are `lets`, `ws`, `kinds`, `inits`, `names`, `insts`, `instOrigins`, `dom`; they change only by: let push (`machBindLet*`, `machLetIndex`, :3619-3670, :3743), one instance push with its origin (:4078-4080), a **group** append of `fields.length` entries sharing one `js` with origins `.field i` (`machInstanceS`, :4119-4126), slot reservation (`machReserve` append :3713, bare register push :3932), `ws` append (:4043, :4197, :5141) and **`ws` restore** (`{ st' with ws := st.ws }`, :4223), `dom := some _` (:3716, :3933, :4068, :4107, :4235). rev3's `PushStep` has neither the group arm nor slot/write arms; §2 adds them.

## 1. U-D1 — `ReadsOfQuoteStmt` proved (item 3)

Statement, kept verbatim from `Tests/Gen5/CoverNegCheck.lean` (rev2; re-stated because the test file is not importable from `Tools`):
```lean
def MentionPos (nDecl kI n k : Nat) (v : Lean.Expr) (p : Nat) : Prop :=
  (∃ i, i < nDecl ∧ MentionsPh "_machIn" i v ∧ p = nDecl - 1 - i) ∨
  (∃ j, j < kI ∧ MentionsPh "_machInst" j v ∧ p = nDecl + j) ∨
  (∃ i, i < n ∧ MentionsPh "_machSlot" i v ∧ p = nDecl + kI + i) ∨
  (∃ j, j < k ∧ MentionsPh "_machLet" j v ∧ p = nDecl + kI + n + j)
def LooseOcc : Nat → Lean.Expr → Nat → Prop
  | d, .bvar i, b => i = b + d
  | d, .app f a, b => LooseOcc d f b ∨ LooseOcc d a b
  | d, .lam _ t e _, b => LooseOcc d t b ∨ LooseOcc (d + 1) e b
  | d, .forallE _ t e _, b => LooseOcc d t b ∨ LooseOcc (d + 1) e b
  | _, _, _ => False
def ReadsOfQuoteStmt : Prop :=
  ∀ (dom : Lean.Expr) (nDecl kI n k : Nat) (bpos vpos : Nat → Nat) (okP : Nat → Bool)
    {s : SType} (t : Term s) (v : Lean.Expr),
    PhInRange nDecl kI n k v →
    (∀ j, bpos j < nDecl + kI + n + k) → (∀ j, vpos j < nDecl + kI + n + k) →
    (∀ b, ¬ LooseOcc 0 v b) →
    quote dom (fun j => inputExpr (nDecl + kI + n + k) (bpos j))
      (fun j => inputExpr (nDecl + kI + n + k) (vpos j)) t = machClose kI n k 0 v →
    (∀ p, MentionPos nDecl kI n k v p → okP p = true) →
    Tools.ShippingMachineRef.reads (fun j => okP (bpos j)) (fun j => okP (vpos j)) t = true
```
Proof lemmas (full types):
```lean
/-- a loose index of the closed expression comes from a mentioned placeholder, at position-from-end `c - 1 - p`. -/
theorem looseOcc_machClose (nDecl kI n k : Nat) :
    ∀ (d : Nat) (v : Lean.Expr) (b : Nat), (∀ b', ¬ LooseOcc d v b') → PhInRange nDecl kI n k v →
      LooseOcc d (machClose kI n k d v) b →
      ∃ p, MentionPos nDecl kI n k v p ∧ b = nDecl + kI + n + k - 1 - p

/-- the quote-side occurrence lemma: every input of `t` puts `bvar (bb j)` / `bvar (vv j)` as a loose occurrence (at depth 0) into the quotation. -/
theorem reads_of_quote_loose (dom : Lean.Expr) (bb vv : Nat → Nat) (P : Nat → Bool) {s : SType} (t : Term s)
    (h : ∀ b, LooseOcc 0 (quote dom (fun j => Lean.Expr.bvar (bb j)) (fun j => Lean.Expr.bvar (vv j)) t) b → P b = true) :
    Tools.ShippingMachineRef.reads (fun j => P (bb j)) (fun j => P (vv j)) t = true

theorem readsOfQuoteStmt : ReadsOfQuoteStmt
```
Proof plan. `looseOcc_machClose`: induction on `v` (generalising `d`); the four placeholder arms are the four equalities `kI+n+k+i`, `kI-1-j+n+k`, `n-1-i+k`, `k-1-j` against `c-1-p` for `p = nDecl-1-i`, `nDecl+j`, `nDecl+kI+i`, `nDecl+kI+n+j` (the same arithmetic as `machClose_mach*` of Cover.lean, using `PhInRange` for the bounds, i.e. exactly the saturation case that refuted rev1); `bvar`/other constructors: the `¬LooseOcc d v` premise closes `bvar`, the rest are `False`. `reads_of_quote_loose`: induction on `t`; for `boolInput j`/`bitsInput _ j` the quotation is `bvar (bb j)`/`bvar (vv j)` and `LooseOcc 0 (bvar x) x`; all other arms need "every operand of the helper (`binE`, `compareE`, `boolBinE`, `boolNotE`, `boolEqE`, `muxE`, `setwE`, `appE`, `sliceE`, `concatE`, `concatLitHiE/LoE`, `zextMapE`, `sliceFE`) is an application argument at binder depth 0". Read in this tree for `binE`, `compareE`, `boolBinE`, `boolNotE`, `boolEqE`, `muxE`, `appE`, `setwE`, `sliceE`: yes (operands are `mkApp*` arguments; the `lam` bodies contain only `bvar 0/1` and constants). `concatE`, `concatLitHiE/LoE`, `zextMapE`, `sliceFE`: `mkApp*` arguments, lambdas are over constants. **If a helper turns out to bury an operand under a binder, `letE`, `proj` or `mdata` (the last three are not seen by `LooseOcc`), `reads_of_quote_loose` is false as stated; that is reported and the statement revised in a new freeze, not weakened silently.** `readsOfQuoteStmt` combines them with `bb j := c-1-bpos j`, `P b := okP (c-1-b)` and the premise bounds (`bpos j < c` gives `c-1-(c-1-bpos j) = bpos j`; `MentionPos` positions are `< c` by the four range bounds).

Consistency with the rev1 kernel negatives (`CoverNegCheck`: `r2_rev1_false`, `r2_quote_eq`, `r2_mentionPos_empty`, `r2_example_not_in_range`): the proved statement is the rev2 one, which has the extra `PhInRange` premise; the rev1 example violates it (`r2_example_not_in_range`). Cover3Check compares the type of `readsOfQuoteStmt` with `Tests.Gen5.CoverNegCheck.ReadsOfQuoteStmt` by defeq (independent Expected), and re-uses `r2_example_not_in_range` to show the proved statement does not contradict the negative.
This unit supplies the **transport** only; its premise `quote … t = machClose … v` is Q-wit for that let and is not supplied here (§4).

## 2. U-D2 — range invariant, steps, hin/hsl/write/result suppliers (items 1, 2)

```lean
/-- `v` is in range of the state `st`, with `k` the number of lets closed against. -/
def InRange (nDecl : Nat) (st : MachRead) (k : Nat) (v : Lean.Expr) : Prop :=
  PhInRange nDecl st.insts.size st.kinds.size k v

def RangeInv (nDecl : Nat) (st : MachRead) : Prop :=
  (∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → InRange nDecl st j v) ∧
  (∀ w ∈ st.ws, w.1 < st.kinds.size ∧ InRange nDecl st st.lets.size w.2)

/-- origins are pushed with the entries. -/
def OrigAligned (st : MachRead) : Prop := st.instOrigins.size = st.insts.size

/-- the result kind of an entry is not `.domain`; a memory entry has four argument lets and result `.bits dw`. -/
def EntryKinds (st : MachRead) : Prop :=
  (∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) → r ≠ .domain) ∧
  (∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) →
     ∀ cb aw dw, st.instOrigins[k]? = some (.mem cb aw dw) → js.length = 4 ∧ r = .bits dw)

def FullInv (nDecl : Nat) (st : MachRead) : Prop :=
  CallOrderInv st ∧ RangeInv nDecl st ∧ OrigAligned st ∧ EntryKinds st

inductive FStep (nDecl : Nat) : MachRead → MachRead → Prop
  | letv (st : MachRead) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr) :
      InRange nDecl st st.lets.size v → FStep nDecl st { st with lets := st.lets.push (nm, kd, v) }
  | inst (st : MachRead) (c : Name) (js : List Nat) (r : MixedGateBinder) (o : InstOrigin) :
      (∀ a ∈ js, a < st.lets.size) → r ≠ .domain →
      (∀ cb aw dw, o = .mem cb aw dw → js.length = 4 ∧ r = .bits dw) →
      FStep nDecl st { st with insts := st.insts.push (c, js, r), instOrigins := st.instOrigins.push o }
  | group (st : MachRead) (c : Name) (js : List Nat) (rs : List MixedGateBinder) (os : List InstOrigin) :
      rs.length = os.length → (∀ a ∈ js, a < st.lets.size) → (∀ r ∈ rs, r ≠ .domain) →
      (∀ o ∈ os, ∀ cb aw dw, o ≠ .mem cb aw dw) →
      FStep nDecl st { st with insts := st.insts ++ (rs.map fun r => (c, js, r)).toArray, instOrigins := st.instOrigins ++ os.toArray }
  | slot (st : MachRead) (kd : MixedGateBinder) (i : Nat) (nm : Name) :
      FStep nDecl st { st with kinds := st.kinds.push kd, inits := st.inits.push i, names := st.names.push nm }
  | slots (st : MachRead) (ks : List MixedGateBinder) (is : List Nat) (ns : List Name) :
      FStep nDecl st { st with kinds := st.kinds ++ ks.toArray, inits := st.inits ++ is.toArray, names := st.names ++ ns.toArray }
  | ws (st : MachRead) (ws' : Array (Nat × Lean.Expr)) :
      (∀ w ∈ ws', w.1 < st.kinds.size ∧ InRange nDecl st st.lets.size w.2) → FStep nDecl st { st with ws := ws' }

inductive FReach (nDecl : Nat) : MachRead → MachRead → Prop
  | refl (st : MachRead) : FReach nDecl st st
  | tail {a b c : MachRead} : FReach nDecl a b → FStep nDecl b c → FReach nDecl a c
```
(The `ws` arm covers append and restore: the premise is that the *new* array is in range at the current state; the old entries get it from `RangeInv` and monotonicity. `dom` is not a field of `FullInv`: see §4 row R-dom. `inits`/`names` carry no range content here; their lengths are `LenOk`'s.)

Theorems (full types):
```lean
theorem fullInv_of_empty (nDecl : Nat) (st : MachRead) (hl : st.lets = #[]) (hi : st.insts = #[]) (ho : st.instOrigins = #[]) (hw : st.ws = #[]) :
    FullInv nDecl st
theorem fullInv_step {nDecl : Nat} {st st' : MachRead} (h : FullInv nDecl st) (hs : FStep nDecl st st') : FullInv nDecl st'
theorem fullInv_reach {nDecl : Nat} {st0 st : MachRead} (h : FullInv nDecl st0) (hr : FReach nDecl st0 st) : FullInv nDecl st
theorem reach_sizes_mono {nDecl : Nat} {a b : MachRead} (hr : FReach nDecl a b) :
    a.lets.size ≤ b.lets.size ∧ a.insts.size ≤ b.insts.size ∧ a.kinds.size ≤ b.kinds.size
theorem callOrderInv_group (st : MachRead) (c : Name) (js : List Nat) (rs : List MixedGateBinder) (os : List InstOrigin)
    (h : CallOrderInv st) (hj : ∀ a ∈ js, a < st.lets.size) :
    CallOrderInv { st with insts := st.insts ++ (rs.map fun r => (c, js, r)).toArray, instOrigins := st.instOrigins ++ os.toArray }
```
`fullInv_step` reuses `pushInst_preserves`/`pushLet_preserves` of Cover2 (the `CallOrderInv` clauses mention only `lets`/`insts`, so the added `instOrigins`/`kinds`/`ws` fields are rewritten away); `callOrderInv_group` is induction on `rs` with `pushInst_preserves` (the group arm is not covered by Cover2's `PushStep`).

**Suppliers** (the `hin`/`hsl` of `phInRange_of_inv`, and write / result), all at the final state `st` of `FReach nDecl st0 st` from a `FullInv` start:
```lean
/-- hin/hsl and the let/instance clauses together, for every stored let value, at the closing sizes. -/
theorem letRange_final {nDecl : Nat} {st0 st : MachRead} (h0 : FullInv nDecl st0) (hr : FReach nDecl st0 st)
    {j : Nat} {nm : Name} {kd : MixedGateBinder} {v : Lean.Expr} (hj : st.lets[j]? = some (nm, kd, v)) :
    PhInRange nDecl st.insts.size st.kinds.size st.lets.size v
theorem writeRange_final {nDecl : Nat} {st0 st : MachRead} (h0 : FullInv nDecl st0) (hr : FReach nDecl st0 st)
    {w : Nat × Lean.Expr} (hw : w ∈ st.ws) :
    w.1 < st.kinds.size ∧ PhInRange nDecl st.insts.size st.kinds.size st.lets.size w.2
/-- a result expression that was in range when returned stays in range at the closing sizes. -/
theorem resultRange_final {nDecl : Nat} {st1 st : MachRead} (hr : FReach nDecl st1 st) {v : Lean.Expr}
    (hv : InRange nDecl st1 st1.lets.size v) : PhInRange nDecl st.insts.size st.kinds.size st.lets.size v
theorem machNext_range {nDecl : Nat} {st : MachRead} (h : RangeInv nDecl st) {i : Nat} (hi : i < st.kinds.size) :
    PhInRange nDecl st.insts.size st.kinds.size st.lets.size (machNext i st.ws.toList)
theorem machBundleParts_range {nDecl kI n k : Nat} :
    ∀ (m : Nat) (e : Lean.Expr) (ps : List Lean.Expr), machBundleParts? m e = some ps → PhInRange nDecl kI n k e →
      ∀ p ∈ ps, PhInRange nDecl kI n k p
theorem machResults_range {nDecl kI n k : Nat} (sel : Option (Name × Nat × Nat)) (ctor? : Option Name) (m : Nat) (v : Lean.Expr)
    (es : List Lean.Expr) (h : machResults? sel ctor? m v = some es) (hv : PhInRange nDecl kI n k v) :
    ∀ e ∈ es, PhInRange nDecl kI n k e
```
`machNext_range`: the value is the last write to `i` (in range by `RangeInv.2`) or `machSlot i` (slot clause `i < kinds.size`; the other three clauses are vacuous since `machSlot i` mentions only itself). `machBundleParts_range`/`machResults_range` need only that the components are application arguments of the input (`inlSpine` arguments: auxiliary `inlSpine_mentions`, one-line statement: every placeholder mentioned by an element of `(inlSpine e acc).2` is mentioned by `e` or by an element of `acc`). `PhInRange`'s four clauses use `MentionsPh`, which does not look under `letE`/`mdata`/`proj` (rev3 §3): these suppliers say nothing about a placeholder under such a constructor, and no claim is made that the reader never produces one.

What these suppliers do and do not give. They give: **if** the reader's actual state evolution is an `FReach` from a `FullInv` start and each step meets its premise, then every let value, write, next-slot expression and (given its range at return time) result part is in `PhInRange` at the closing `kI = insts.size`, `n = kinds.size`, `k = lets.size`, which is the first hypothesis of `readsOfQuoteStmt`. They do **not** give: that the reader's steps are `FStep`s (§4 R-trace), nor the premises of each step on a real run: for `letv` the premise `InRange nDecl st st.lets.size v` is exactly "the converted value only mentions inputs `< nDecl`, instances `< insts.size`, slots `< kinds.size`, lets `< lets.size`"; for the **input** clause this is the loose-bvar bound of the entry body (`machIn (j - d - env.length)` has index `< nDecl` iff `j < nDecl + env.length + d`), i.e. a statement about the body of the entry constant (no loose bvar beyond the peeled binders). This investigation found no supplier of that closedness in `RunReadsAt` or in the fuel-twin files (`ShippingLetsReaderInvMain.lean` lists the loose-bvar condition as OPEN), and it is **not** moved into a premise of any final theorem; it stays a named row (R-in).

## 3. U-D3 — RowA/B/C from the invariants, with the interface premises named (item 4, the mapping part that is a theorem)

```lean
/-- how the reader state and the `MachineData` line up: the interface of DATAOF D3/D7/D9 and the result record (M11). Premises, owned by DATAOF/ShapeDecomp; not supplied here. -/
structure ShapeAgree (d : MachineData) (st : MachRead) : Prop where
  insts   : d.shape.insts = st.insts.toList
  origins : d.shape.instOrigins = st.instOrigins.toList
  slots   : d.ss.length = st.kinds.size
  lets    : d.ls.length = st.lets.size
  nIn     : d.shape.insts.length ≤ d.nIn

/-- the per-let quotation equation (Q-wit for the let fields; owner DATAOF D9 / READKINDS U4). Premise; not supplied here. -/
def LetQuoteEq (d : MachineData) (st : MachRead) : Prop :=
  ∀ (j : Nat) (hj : j < d.ls.length) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) →
    quote d.dom (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.bpos i))
                (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.vpos i)) (d.ls[j]'hj).2
      = machClose st.insts.size st.kinds.size st.lets.size 0 v

/-- stored let values have no loose bvar (reader row R-nl; open in `ShippingLetsReaderInvMain.lean`). Premise; not supplied here. -/
def LetsNoLoose (st : MachRead) : Prop :=
  ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ b, ¬ LooseOcc 0 v b

theorem cleanLets_getElem (d : MachineData) (k l : Nat) (hl : l < d.ls.length) :
    (cleanLets d k)[l]? = some (Tools.ShippingMachineRef.reads
      (fun j => posOk d k ((cleanLets d k).take l) (d.bpos j)) (fun j => posOk d k ((cleanLets d k).take l) (d.vpos j)) (d.ls[l]'hl).2)

theorem letReach_edge {lets : MachLets} {a l j : Nat} (h : LetReach lets a l) (e : LetEdge lets l j) : LetReach lets a j

theorem rowA2_of_inv {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : OrigAligned st) :
    d.shape.instOrigins.length = d.shape.insts.length
theorem rowA3_of_inv {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv nDecl st) :
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, l < d.ls.length
theorem rowA4B23_mem_of_inv {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv nDecl st) :
    ∀ k, k < d.shape.insts.length → ∀ cb aw dw, originOf d k = .mem cb aw dw →
      (callArgs d k).length = 4 ∧ (d.shape.insts[k]?).map (·.2.2) = some (.bits dw)
theorem rowB1_of_inv {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv nDecl st)
    (hcb : ∀ k (hk : k < d.shape.insts.length), (d.shape.binders[kDOf d + k]?).map (·.2) = some (d.shape.insts[k]'hk).2.2) :
    ∀ k, k < d.shape.insts.length → callKind d k ≠ .domain

theorem rowC_of_reader {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv (kDOf d) st)
    (hq : LetQuoteEq d st) (hnl : LetsNoLoose st)
    (hb : ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length) (hv : ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length) :
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true
```
`rowC_of_reader` proof plan: for entry `k` and `a ∈ callArgs d k` (exists by `ShapeAgree.insts`), prove by strong induction on `l` that `LetReach st.lets a l → (cleanLets d k)[l]? = some true`. At `l`: `cleanLets_getElem` turns the goal into `reads … = true` with `okP := posOk d k ((cleanLets d k).take l)`; apply `readsOfQuoteStmt` with `PhInRange` from `letRange_final`-style monotonicity of `RangeInv.1` (`PhInRange … l v` weakened to the closing sizes by `phInRange_mono`), `hq`, `hnl`, `hb/hv` (`kDOf d + kI + n + k = nIn + ss.length + ls.length` by `kDOf_add_len`). The `MentionPos` obligations: input `p = nDecl-1-i < kDOf d ≤ kDOf d + k`; instance `p = nDecl + m` with `m < k` from `ArgsInstBounded` at `(k, a, reach l)`, so `p < kDOf d + k`; slot `p ∈ [nIn, nIn+ss.length)`; let `p = nDecl+kI+n+j` with `LetEdge l j`, `j < l` by `LetValuesEarlier`, `LetReach a j` by `letReach_edge`, so the induction hypothesis gives `(cleanLets d k)[j]? = some true`, i.e. `(take l …).getD j false = true`, third disjunct of `posOk`. `cleanLets_mono` (Cover.lean) is not needed here (the group entries share `js`; the statement is per `k`).

`rowA3_of_inv`: `ArgsExist` + `ShapeAgree.lets`. `rowA2_of_inv`: `OrigAligned` + `ShapeAgree.origins/insts`. `rowA4B23_mem_of_inv`: `EntryKinds.2` (the lets' *sorts* `letSort d l0 = some (.bits aw)` etc. of RowB are **not** included: row B3, §4). `rowB1_of_inv`: `EntryKinds.1` + Cover.lean `callKind_eq_inst`; `hcb` is the `ShapeDecomp.callBinder_bs`-shaped binder fact (premise, as in `callKind_eq_inst`).

## 4. Item 4 — mapping of the GenWF rows (and the dataOf rows they touch) to suppliers

"Supplier" = a theorem of this freeze (conditional on the stated premises); "premise" = an interface fact owned by the named Issue; "route not found" = this investigation found no supplier or route.

| GenWF row | supplier in this freeze | remaining premise (owner) / status |
|---|---|---|
| A1 `insts.length ≤ nIn` | none needed beyond `ShapeAgree.nIn` | R4 `nIn := nDecl + insts.length` in `dataOf` (DATAOF D3) |
| A2 origins aligned | `rowA2_of_inv` (needs `OrigAligned` ⇐ `FStep.inst/group`) | `ShapeAgree.origins/insts` (DATAOF/M11); trace R-trace |
| A3 arg index `< ls.length` | `rowA3_of_inv` (`ArgsExist`) | `ShapeAgree.lets` (DATAOF D7/D9); R-trace |
| A4 memory: 4 args | `rowA4B23_mem_of_inv` (`EntryKinds.2`) | the memory arm's push really meets the `inst` premise (Elab.lean:3954-3963 read; not proved); R-trace |
| B1 `callKind ≠ .domain` | `rowB1_of_inv` | `hcb` (`ShapeDecomp.callBinder_bs`, build status of that file to be reported in phase 2); R-trace |
| B2 memory result `.bits dw` | `rowA4B23_mem_of_inv` | as A4 |
| B3 memory arg sorts | **route not found** | agreement of an existing let's kind with the passed kind (typing, SRC-ARGW `MemSrcKinds`/`ReadTyped` unsupplied); not touched |
| C call order | `rowC_of_reader` (with `readsOfQuoteStmt`, `fullInv_reach`, `letRange_final`) | `LetQuoteEq` (Q-wit per let), `LetsNoLoose` (R-nl), `ShapeAgree`, `hb/hv` (O10/O11), R-in (input clause of `InRange` for each pushed let), R-trace |

Rows deliberately **not** typed or proved here (unchanged, no overlap with DATAOF/SEM):
- **Q-cmp / Q-snd / Q-wit**: not touched. DATAOF/SEM own `genSem_local`, `dataOf_sound`, `bitsBeq_eq`; SRC-ARGW/READKINDS own `ShapeFuelBridge` (not redefined) and `readTot_of_quote_body`. `LetQuoteEq` is the *per-let projection* of the quotation fact (`GenIn.bodyEq` is the whole-body form); no supplier for it is found here, and `readsOfQuoteStmt` takes it only as the hypothesis it already was.
- **R-trace** (the main open link): that the real reader's state evolution from `{}` is an `FReach` with every step premise met. This investigation found no existing lemma; the only mechanised range facts about the twin are `LetOk` (lets only) in `ShippingLetsReaderInvBase/Main` (`machConvF_post`), conditional on `PureFacts` (`RootFloatRange`, `LiftRange`, `Inst1Range`, `SigTyRange`, `BundleIotaRange`: NOT PROVED) and on `TwinCoverAt` (twin → real, OPEN). A real-run statement would be `∃ n, machineShapeF n … = some (some sp)` (ShapeFuelBridge, SRC-ARGW) followed by a fuel induction producing `FReach`; neither is available, and neither is claimed. Also not a run object: `RunReadsAt` contains no execution of `readMachine`, so `dataOf` success is not a run fact either (rev0 §0).
- **R-in** (input clause: loose-bvar bound of the entry body), **R-nl** (`LetsNoLoose`), **R-dom** (the domain `st.dom`/`dom'` in range and equal to the R5-R6 composition, rev0 D4): route not found.
- dataOf rows D0–D11 and `MachineData.ok` rows O1–O20 (rev0 §1-§2): unchanged; this freeze touches only O10/O11 as the premises `hb/hv`. The statuses of rev0 §6 stand.
- Fallback successes, `ClosingRun`, DG-ENV, DG-ACC, DG-MEASURE (evidence only, no number exists).

## 5. Checks planned for `Tests/Gen5/Cover3Check.lean` (form of `Cover2Check.lean`)

- **TYPE**: every theorem and `FStep`/`FullInv` unfolding against an independently spelled `Exp…` statement with `checkExpected`/`isDefEq` on fully bound types; `readsOfQuoteStmt` against `Tests.Gen5.CoverNegCheck.ReadsOfQuoteStmt`.
- **MUTANT** (signature/defeq rejection, **not** semantic counterexamples), each well-typed and rejected by the same comparer: `looseOcc_machClose` with `b = c - p` instead of `c - 1 - p`; `readsOfQuoteStmt` without the `PhInRange` premise (this is the rev1 statement); `letRange_final` with the let clause `< lets.size` replaced by `≤`; `rowC_of_reader` without `hnl`; `FStep.group` with `rs.length = os.length` dropped.
- **AXIOMS**: `collectAxioms` per theorem, standard axioms only.
- **CLOSURE**: explicit value-closure walk over `getUsedConstants` (as Cover2Check: no `sorryAx`, no native-reduction axiom), with the same 3 negative / 2 clean controls. As in `CoverCheck`/`Cover2Check`, the negative controls are added in memory inside `withoutModifyingEnv`, so the build prints "declaration uses `sorry`" warnings; the header of `Cover3Check.lean` will say **"意図した負例 N 件"** with `N` the count observed in the Pod build (Cover2Check printed 3), and the source contains no `sorry`, axiom or `native_decide`. The closure is of the explicit bodies / `getUsedConstants`; it is not a claim about `extern` implementations or raw projections.
- **Kernel negatives kept**: Cover3Check re-states `r2_example_not_in_range` via the imported CoverNegCheck and checks that `readsOfQuoteStmt` is not applicable to that instance (its `PhInRange` premise fails).
- Build: `kjob lake build Tools.ShippingGen5Cover3`, then `Tests.Gen5.Cover3Check`, one at a time in the Pod, logs outside the tree; success SHA recorded by a comment-only commit. The Lean commit is left at `doing` with "clean build は coder".

## 6. Not claimed

- No Lean exists for this revision; no theorem of §1-§3 is proved; the text may fail to elaborate (it will be reported, not hidden).
- Nothing about any successful run, `dataOf` success, `GenWF` on real data, the corpus, M5 or FG. §4 lists which premises remain; "route not found" rows are not claimed false or impossible.
- `FReach` is a closure of abstract steps, not the reader trace; `FullInv` is stated for a start state and says nothing until R-trace is supplied.
- `LooseOcc`, `MentionsPh`, `PhInRange` look only at `app`/`lam`/`forallE` (rev3 §3); nothing is claimed about placeholders under `letE`/`mdata`/`proj`.
- No new law, TRUSTED boundary, FG/guarantee change, compiler change or shared-definition change; `GenWF` is not strengthened.

# DG-COVER freeze rev1 — §4 pure core as implemented; R1 corrected call-order invariant and `reads` transport; R2 roadmap; R3 split of the body-quotation row (Issue sparkle-gen5-dg-cover)

**FOR REVIEW — docs only.** Answers the three requests of the rev0 review (`changes_requested`, R1-R3). Base `ec2fbda8` (`DG_COVER_FREEZE.md` rev0, kept as the survey;
this document replaces its §3, §5 W-C and §7 C1 where they differ and says so). Nothing here completes the Issue, M5 or FG. No guarantee, law, TRUSTED boundary,
FG scope or shared definition is changed or proposed to be changed.

Wording rule (as rev0): "not found" = *this survey found no supplier or route*; never "impossible"/"not derivable". A "mutant" is a rejection of a changed statement by
signature / defeq, not a semantic counterexample. Conditional results are INTERMEDIATE.

## 0. Scope of this freeze (R2)

The full-type freeze of this revision is **exactly**: (A) the unit §4 U-C1…U-C5 of rev0 as implemented in `Tools/ShippingGen5Cover.lean` (§1 below lists every type);
(B) the R1 definitions and statements of §2 below, written out completely (no placeholder). **Everything else of rev0 — `CoverRows`, `cover_of_run`,
`dataOf_some_of_rows`, the W-rows A2/A3/A4/B1/B2/B3, DATAOF/READKINDS-dependent rows — is roadmap (§4), carries no Lean type in this revision, and is not part of the
freeze.** rev0 §3's `CoverRows`/`<§7 C…>` text is withdrawn as a type; it was never a type.

## 1. (A) §4 as implemented — types (no change of mathematics from rev0 §4)

Implemented in commits `7e2b90ac` (Lean) and `a54446a1` (header-only), branch `kjob/g5cv-r2`; Pod build of `Tools.ShippingGen5Cover` and `Tests.Gen5.CoverCheck` exit 0
(TYPE 17, MUTANT 5, AXIOMS standard, CLOSURE OK). **The clean build is the coder's; nothing here is recorded as the clean-build result.** The authoritative types are
those of the Lean file; differences from rev0 §4 are only these:
- `genWFRows_iff` added (the structure `GenWFRows` ↔ the 7-fold conjunction), so the independent TYPE check can state the conjunction without the structure.
- `genWF_of_rows`/`genWFRows_of_genWF` take `d` implicit (`{d : MachineData}`).
- `callKind_eq_inst` is restated with hypotheses `hn : d.shape.insts.length ≤ d.nIn` and `hb : (d.shape.binders[kDOf d + k]?).map (·.2) = some (d.shape.insts[k]'hk).2.2`
  (the binder fact on `shape.binders`; `ShapeDecomp.callBinder_bs` is the intended source of `hb`, it is not imported). rev0's `hn : d.nIn = kDOf d + insts.length` is replaced by the weaker `≤`.
- `kDOf_add_len`, `machClose_mach{In,InstOut,Slot,Let}` as in rev0 with the bound hypotheses named `h`/`hi`/`hj`.

Full list (statement = the Lean file): `rowA_iff rowB_iff rowC_iff genWF_iff GenWFRows genWF_of_rows genWFRows_iff genWFRows_of_genWF cleanLets_length reads_mono posOk_mono
cleanLets_mono machClose_machIn machClose_machInstOut machClose_machSlot machClose_machLet kDOf_add_len callKind_eq_inst`.

**Which §4 lemmas change type because of R1: none.** R1 concerns the Expr-level invariant (rev0 §5 W-C) and the Expr→Term transport; the §4 lemmas are about the Term-level
`cleanLets`/`posOk`/`reads` and `machClose`. `cleanLets_mono` in particular is unaffected (it says: an argument let clean for call `k` is clean for later `k'`; whether the
argument let is clean for `k` in the first place is what R1's invariant must supply).

CoverCheck control note: the negative closure controls are declarations added in memory (`addDecl` of a value that mentions `sorryAx`), so the build prints three
"declaration uses `sorry`" warnings from `Tests/Gen5/CoverCheck.lean`; the file contains no `sorry` token, axiom or `native_decide`.

## 2. (B) R1 — the indirect-let gap, the corrected invariant, and the `reads` transport

### 2.1 The gap (an abstract premise gap, NOT a counterexample from a successful source)

rev0 §5 `ArgsEarlier` constrained, for an argument let `a` of entry `k`, only the value `v` of `a` itself (its instance mentions `< k`, its let mentions exist). It does not
constrain the lets that `v` mentions. Abstract state `gapState`: let 0 mentions instance 5; let 1 mentions let 0; entry 2 takes let 1 as its argument. rev0's `ArgsEarlier` holds
there (let 1's value mentions no instance; let 0 exists), while the argument let 1 depends, through let 0, on instance 5 ≥ 2. Then `RowC` at call 2 can fail (let 0 reads the
position of instance 5, which is not `< kDOf d + 2`, so it is not clean, hence let 1 is not clean). **This says rev0's stated invariant was too weak to give `RowC`; it makes
no claim that any successful source has such a state.** Both facts about `gapState` are proved in the scratch probe below (`gap_rev0_holds`, `gap_new_fails`).

### 2.2 Corrected invariant (transitive call bound) — full types

Fixed invariant, three clauses over the reader state `MachRead` (all fields as in `Sparkle/Compiler/Elab.lean:3563`):
`LetValuesEarlier` (a let mentions only earlier lets), `LetsInstRange` (every instance mentioned by any let is already pushed: `< insts.size`) and `ArgsInstBounded` (**the
transitive bound**: for entry `k`, every let in the dependency closure of every argument let mentions only instances `< k`). The preservation obligations are stated per
push (`machLetIndex` pushes a let at the end, entries are pushed after their arguments were converted, Elab.lean:3743, 4062-4068, 4096-4112); that the reader's actual steps are
instances of them is the fuel-twin induction (rev0 W-C), **not proved here**.

### 2.3 Transport `reads` ← Expr placeholders — full type

`ReadsOfQuoteStmt` is the corrected type of rev0's `reads_of_quote`. Its premise `quote … t = machClose kI n k 0 v` is the quotation witness **for that let** and is not supplied
(see R3 below); `MentionPos` turns the placeholders mentioned by `v` into the closed positions fixed by `machClose_machIn/InstOut/Slot/Let` (§1); `LooseOcc` is the depth-aware
loose-bvar occurrence used for the "`v` has no loose bvar" premise. What this statement needs and does not have: the quote-side lemma "an input `boolInput j`/`bitsInput w j` of
`t` puts `inputExpr count (bpos j)` (resp. `vpos j`) as a loose occurrence into `quote … t`", from the `quote` equations (`ShippingUnifiedSource.lean:370`) — **no supplier found by
this survey**; the premise `hb`/`hv` (positions in range) is the other input. Using it for `RowC`: apply with `okP := posOk d k clean` and the clean prefix of the let preceding.

### 2.4 The Lean text (elaborated; see status)

```lean
namespace Tools.ShippingGen5CoverR1
open Lean Sparkle.Compiler.Elab Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge

/-- Occurrence of the placeholder `fvar ⟨.num (.str .anonymous tag) i⟩`, along exactly the constructors `machClose` traverses. -/
def MentionsPh (tag : String) (i : Nat) : Lean.Expr → Prop
  | .fvar ⟨.num (.str .anonymous t) j⟩ => t = tag ∧ j = i
  | .app f a => MentionsPh tag i f ∨ MentionsPh tag i a
  | .lam _ t b _ => MentionsPh tag i t ∨ MentionsPh tag i b
  | .forallE _ t b _ => MentionsPh tag i t ∨ MentionsPh tag i b
  | _ => False

abbrev MentionsLet (i : Nat) (e : Lean.Expr) : Prop := MentionsPh "_machLet" i e
abbrev MentionsInst (i : Nat) (e : Lean.Expr) : Prop := MentionsPh "_machInst" i e

/-- Direct dependency: the value of let `a` mentions let `i`. -/
def LetEdge (lets : MachLets) (a i : Nat) : Prop :=
  ∃ (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), lets[a]? = some (nm, kd, v) ∧ MentionsLet i v

/-- Reflexive-transitive closure of the direct dependency. -/
inductive LetReach (lets : MachLets) : Nat → Nat → Prop
  | refl (a : Nat) : LetReach lets a a
  | step {a i j : Nat} : LetEdge lets a i → LetReach lets i j → LetReach lets a j

/-- Every let value mentions only strictly earlier lets. -/
def LetValuesEarlier (st : MachRead) : Prop :=
  ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ i, MentionsLet i v → i < j

/-- Every instance placeholder in any let value is below the number of instance entries pushed so far. -/
def LetsInstRange (st : MachRead) : Prop :=
  ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ m, MentionsInst m v → m < st.insts.size

/-- R1-corrected: for entry `k`, every let in the dependency closure of every argument let mentions only instances `< k`. -/
def ArgsInstBounded (st : MachRead) : Prop :=
  ∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) → ∀ a ∈ js, ∀ i, LetReach st.lets a i →
    ∀ (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[i]? = some (nm, kd, v) → ∀ m, MentionsInst m v → m < k

def CallOrderInv (st : MachRead) : Prop :=
  LetValuesEarlier st ∧ LetsInstRange st ∧ ArgsInstBounded st

/-- Pushing an instance entry whose argument lets exist preserves the invariant. -/
def PushInstPreserves : Prop :=
  ∀ (st st' : MachRead) (c : Name) (js : List Nat) (r : MixedGateBinder),
    CallOrderInv st → (∀ a ∈ js, a < st.lets.size) →
    st' = { st with insts := st.insts.push (c, js, r) } → CallOrderInv st'

/-- Pushing a let whose value mentions only existing lets and existing instances preserves the invariant. -/
def PushLetPreserves : Prop :=
  ∀ (st st' : MachRead) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr),
    CallOrderInv st → (∀ i, MentionsLet i v → i < st.lets.size) → (∀ m, MentionsInst m v → m < st.insts.size) →
    st' = { st with lets := st.lets.push (nm, kd, v) } → CallOrderInv st'

/-- Closed position of a placeholder mentioned by `v`, in the telescope `machClose kI n k` closes against (positions as in `machClose_mach*`). -/
def MentionPos (nDecl kI n k : Nat) (v : Lean.Expr) (p : Nat) : Prop :=
  (∃ i, i < nDecl ∧ MentionsPh "_machIn" i v ∧ p = nDecl - 1 - i) ∨
  (∃ j, j < kI ∧ MentionsPh "_machInst" j v ∧ p = nDecl + j) ∨
  (∃ i, i < n ∧ MentionsPh "_machSlot" i v ∧ p = nDecl + kI + i) ∨
  (∃ j, j < k ∧ MentionsPh "_machLet" j v ∧ p = nDecl + kI + n + j)

/-- Loose de Bruijn occurrence at binder depth `d`. -/
def LooseOcc : Nat → Lean.Expr → Nat → Prop
  | d, .bvar i, b => i = b + d
  | d, .app f a, b => LooseOcc d f b ∨ LooseOcc d a b
  | d, .lam _ t e _, b => LooseOcc d t b ∨ LooseOcc (d + 1) e b
  | d, .forallE _ t e _, b => LooseOcc d t b ∨ LooseOcc (d + 1) e b
  | _, _, _ => False

/-- The Expr → Term `reads` transport (statement only; premise `hq` is the quotation witness for this let, NOT supplied). -/
def ReadsOfQuoteStmt : Prop :=
  ∀ (dom : Lean.Expr) (nDecl kI n k : Nat) (bpos vpos : Nat → Nat) (okP : Nat → Bool)
    {s : SType} (t : Term s) (v : Lean.Expr),
    (∀ j, bpos j < nDecl + kI + n + k) → (∀ j, vpos j < nDecl + kI + n + k) →
    (∀ b, ¬ LooseOcc 0 v b) →
    quote dom (fun j => inputExpr (nDecl + kI + n + k) (bpos j))
      (fun j => inputExpr (nDecl + kI + n + k) (vpos j)) t = machClose kI n k 0 v →
    (∀ p, MentionPos nDecl kI n k v p → okP p = true) →
    Tools.ShippingMachineRef.reads (fun j => okP (bpos j)) (fun j => okP (vpos j)) t = true

/-- rev0's `ArgsEarlier` (kept only to exhibit the gap). -/
def ArgsEarlierRev0 (st : MachRead) : Prop :=
  ∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder), st.insts[k]? = some (c, js, r) → ∀ a ∈ js,
    ∀ (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[a]? = some (nm, kd, v) →
    (∀ i, MentionsInst i v → i < k) ∧
    (∀ i, MentionsLet i v → ∃ (nm' : Name) (kd' : MixedGateBinder) (v' : Lean.Expr), st.lets[i]? = some (nm', kd', v'))

/-- Abstract state (not a source of any run): let 0 mentions instance 5, let 1 mentions let 0, entry 2 takes let 1 as its argument. -/
def gapState : MachRead :=
  { lets := #[(`a, .bool, machInstOut 5), (`b, .bool, machLet 0)],
    insts := #[(`m, [], .bool), (`m, [], .bool), (`m, [1], .bool)] }

theorem gap_rev0_holds : ArgsEarlierRev0 gapState := by
  intro k c js r hk a ha nm kd v hv
  match k, hk with
  | 0, hk => simp [gapState] at hk; obtain ⟨-, rfl, -⟩ := hk; simp at ha
  | 1, hk => simp [gapState] at hk; obtain ⟨-, rfl, -⟩ := hk; simp at ha
  | 2, hk =>
    simp [gapState] at hk; obtain ⟨-, rfl, -⟩ := hk
    simp at ha; subst ha
    simp [gapState] at hv; obtain ⟨-, -, rfl⟩ := hv
    refine ⟨?_, ?_⟩
    · intro i hi; simp [MentionsInst, MentionsPh, machLet] at hi
    · intro i hi
      simp [MentionsLet, MentionsPh, machLet] at hi
      subst hi
      exact ⟨`a, .bool, machInstOut 5, by simp [gapState]⟩
  | k + 3, hk => simp [gapState] at hk

theorem gap_new_fails : ¬ ArgsInstBounded gapState := by
  intro h
  have := h 2 `m [1] .bool (by simp [gapState]) 1 (by simp) 0
    (.step ⟨`b, .bool, machLet 0, by simp [gapState], by simp [MentionsLet, MentionsPh, machLet]⟩ (.refl 0))
    `a .bool (machInstOut 5) (by simp [gapState]) 5 (by simp [MentionsInst, MentionsPh, machInstOut])
  omega

end Tools.ShippingGen5CoverR1
```
Status: the text above (with `import Tools.ShippingGen5Cover`, `set_option autoImplicit false`) elaborated with Pod `kjob lake build` exit 0 and no `sorry` in a **throwaway file that is
not committed** (this document is the only record; per the process, no further Lean is committed before the freeze is approved). `PushInstPreserves`, `PushLetPreserves`
and `ReadsOfQuoteStmt` are `Prop` definitions (statements), not theorems; none is proved.

## 3. Rows for `RowC` after R1

| id | proposition | status |
|---|---|---|
| C-i | `LetValuesEarlier` of the final state | statement §2.2; push-step `PushLetPreserves`; reader induction not proved |
| C-ii | `ArgsInstBounded` of the final state | statement §2.2; `PushInstPreserves`; not proved |
| C-iii | `ReadsOfQuoteStmt` per let | statement §2.3; needs the quote-side occurrence lemma and the let's quotation witness; not supplied |
| C-iv | assembly: C-i..iii + §4 `cleanLets_*` ⇒ `GenWFRows.c` | roadmap (§4), no type frozen |

## 4. Roadmap (R2) — not frozen, no types

Not part of this freeze: `CoverRows`, `cover_of_run`, `dataOf_some_of_rows`, `CoverAt`, `runEntry`; the fuel-premise lemmas for A2/A3/A4/B1/B2/B3; the DG-DATAOF /
DG-READKINDS / SRC-ARGW-dependent rows. They are listed in rev0 §1/§2/§5 with their dependency; each gets a full type in its own freeze when it is scheduled. The assembly
order is: (1) §4 core (done, awaiting clean build); (2) C-i/C-ii with the fuel twin; (3) the other W-rows; (4) quotation witness (R3); (5) `cover_of_run`. rev0 §3's "THE FINAL
SHAPE" is withdrawn as a frozen type.

## 5. R3 — body-is-quotation split into separate rows with their suppliers

rev0 D6 conflated two propositions. They are separated here. `readMachine` (`Tools/ShippingMachineCommand.lean:529-534`, [B]) builds `q := quote … packed` from the terms it
**read** and throws unless `q.equal shape.body`.

| row | proposition | supplier search (this survey) |
|---|---|---|
| Q-cmp | the Boolean check `Expr.equal q shape.body = true` succeeds | `Expr.equal` is `opaque` `@[extern]` (`Tools/ShippingCacheSoundness.lean:26`, `Tools/ShippingInlTypeFacts.lean:19` record that nothing reduces it). `RunReadsAt` contains no execution of `readMachine` (rev0 §0), so no run-level fact gives the check's success. The Lean-written decision procedure `exprDecEq` (`Sparkle/Compiler/ExprDecEq.lean`) is what the **readers** use (`eqE`); this survey found no lemma relating it to the extern. **Unsupplied** |
| Q-snd | `Expr.equal a b = true → a = b` (soundness of the comparison) | a statement about the opaque extern; no lemma found; adding it would be a law (READKINDS B1). **Unsupplied.** Even if it were supplied it would turn Q-cmp's success into `q = body` **only after** Q-cmp holds — it does not provide a quotation by itself |
| Q-wit | there is a `Term` `t` with `body = quote dom bools bits t` (the premise `hq` of `Tools.ShippingGen5ReadKinds.readTot_of_quote_body`, kjob/g5rk-impl 8781ec44, line 702) | the **consumer** side is built: `readN_quote` (completeness on all 21 kinds, line 401), `readN_expr_quote`, `readTot_quote`, `quote_injective`, `machine_wf_of_readN`, `readTot_of_quote_body` (`hq` as premise). They take a witness and return the read; **they do not produce the witness** (the DG-READKINDS freeze §3 says so; agent g5rk-aud audits that branch, no result is used here). Producers: none found for a run-produced body. Leads examined and not adopted: a fuel-twin invariant that every `machConvF` output is in quotation form (not attempted; pass-through arms Elab.lean:3957-3975 make its truth unclear); a Term-level reference producer per reader arm (not found); per-declaration `machine_body` by `Eq.refl` (a per-declaration kernel check, not a run fact). **Unsupplied** |

Dependencies between the rows: `dataOf` success (D6-D10) needs Q-wit (to run `readN`) and then Q-cmp (the repack check); Q-snd is needed only if one wants to *use* a successful check to
extract a witness — the coverage direction needs the witness before the check, so Q-snd is **not** a substitute for Q-wit. rev0 §7 C1 is revised accordingly: its options (a)-(d)
are options for Q-wit / Q-cmp / Q-snd separately; **this revision does not ask for any decision**. The rows stay unsupplied and the survey continues (next: the fuel-twin arm
survey for Q-wit, and the relation between `exprDecEq` and the extern for Q-cmp); the absence of a supplier found so far is not offered as a reason to change a guarantee or add a law.

## 6. Not claimed

- Nothing about any successful run, corpus, `dataOf`, `GenWF` on real data, M5 or FG.
- §2.2 invariants and `ReadsOfQuoteStmt` are statements; none is proved; `gap_*` are facts about an abstract state only.
- The Pod build of §1 is not the clean build; the §2.4 text is not in the tree.

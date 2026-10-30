# DG-SEM freeze rev3 — ONE fully typed unit (P3), complete `callOut` with a bounds branch, corrected MemFacts/houtTy wording

**FOR REVIEW — design only (docs-only commit, no Lean edited).** Answers the `changes_requested` on rev2 (`ff6cea11`,
`scripts/gen5/DG_SEM_FREEZE_REV2.md`) items R1–R3. Branch `kjob/g5sm-r3`, forked from `kjob/g5sm-r2` `1cc605ef`.

**Scope of this file.** Rev2 stays as written except where this file says so (the "supersedes" lists below). Already accepted
(scoped acceptance, clean build `g5smv-1cc605ef`, not redone): P1, P2, `SemPkg`/`Pkg.toSem`/`genPkg`/accessors `[B]`.
`[S]` = source read in this worktree; `[B]` = built text (`Tools/ShippingGen5SemRef.lean`, `Tools/ShippingGen5SemPkg.lean`).
Everything marked PROPOSAL is not elaborated. No new TRUSTED boundary, law, FG/guarantee change, shared-definition or compiler edit;
no `sorry`/`axiom`/`native_decide`.

## 0. Structure: what is frozen with full types, and what is not

| part | status |
|---|---|
| **§1 Unit U3 = P3** (definitions `valAtE`, `nextFnE`, `resultFnE`, `refBodyE`, `genSemGenE`; theorems `genSemGenE_writes`, `genSemGenE_result`, `genSemGenE_source`) | **FROZEN WITH FULL TYPES.** Every binder, every implicit, every instance is written; nothing is elided with `…`. The next Lean implementation is exactly this unit. |
| **§2 `callOut` and the staged families** | Full definitions (R2). They are *definitions* (total); none of their lemmas (P4a–P4e) is frozen here. U3 does **not** depend on them (§1 is abstract in the extension families). |
| **§4 Roadmap** (P4a, P4d, P4e, P5, P6, P6', P7, P11, P12, GenIn-dependent wrappers) | **ROADMAP — NOT full types.** Statements there are sketches; each is to be re-frozen with a complete telescope *before* it is implemented. They are not part of what this revision asks to approve. |

Rev2 §6's claim "every P-unit with a full statement, nothing elided" is **withdrawn** for P3's successors: only U3 (and the
already built P1/P2/P8) is claimed complete. Rev2 §4 (`refBody`/`genSemGen`, over `Q`) is replaced by §1 + §2.3 below.

## 1. Unit U3 = P3 — complete types

`namespace Tools.ShippingGen5Sem`; `open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingMachineDenote Tools.ShippingMachineSource Tools.ShippingQuadComposed (GenFacts)`;
`variable {ι : Type} {dom : ι → DomainConfig}`. `GenIn` is rev1 §1 (fields `d wf inits ok bodyEq init`), where `GenWF` is rev2 §1.

### 1.1 The extension families as an explicit pair of arguments
The reference body is abstract in the call-result families `eb`/`ev`; §2 instantiates them with `extBOf Q g`/`extOf Q g`. (Same types as the
`extB`/`ext` fields of `SrcSem` `[B]`.)
```lean
abbrev ExtB (ι : Type) (dom : ι → DomainConfig) (ss : List SType) : Type :=
  (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (HList (tys ss)) → Nat → Signal (dom i) Bool
abbrev ExtV (ι : Type) (dom : ι → DomainConfig) (ss : List SType) : Type :=
  (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (HList (tys ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)
```

### 1.2 Definitions
```lean
/-- the typed valuation of cycle `t` under extension families `eb ev` and state `S` -/
noncomputable def valAtE (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (t : Nat) : TVal :=
  typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)

noncomputable def nextFnE (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (t : Nat) : HList (tys g.d.ss) :=
  evalTerms (fun j => (valAtE g eb ev i bools bits S t).b (g.d.bpos j))
            (fun j w => (valAtE g eb ev i bools bits S t).v (g.d.vpos j) w) g.d.nexts

noncomputable def resultFnE (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) : List (Nat → Nat) :=
  g.d.outs.map fun o t => enc o.1 (eval (fun j => (valAtE g eb ev i bools bits S t).b (g.d.bpos j))
                                        (fun j w => (valAtE g eb ev i bools bits S t).v (g.d.vpos j) w) o.2)

/-- `ρ i := List (Nat → Nat)`; the state is rebuilt from `holds` (P2); the pending writes are packed (P1). -/
noncomputable def refBodyE (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    RegList (dom i) (HList (tys g.d.ss)) (Circuit.SigList (dom i) (tys g.d.ss)) (tys g.d.ss) →
    Circuit.SigList (dom i) (tys g.d.ss) →
    Circuit (dom i) (Circuit.SigList (dom i) (tys g.d.ss)) (List (Nat → Nat)) :=
  fun _regs holds =>
    let S := reconState (tys g.d.ss) holds
    (resultFnE g eb ev i bools bits S, sigListOfFn (tys g.d.ss) (nextFnE g eb ev i bools bits S))

noncomputable def genSemGenE (X : Name) (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) : SrcSem ι dom :=
  { decl := X, d := g.d, kD := kDOf g.d, ρ := fun _ => List (Nat → Nat), inh := ⟨g.inits⟩, inits := g.inits,
    body := refBodyE g eb ev, obsR := fun _ r => r, ext := ev, extB := eb,
    src := fun i bools bits =>
      (refBodyE g eb ev i bools bits
        (mkRegList (@stateLoop _ _ _ ⟨g.inits⟩ g.inits (refBodyE g eb ev i bools bits)) (tys g.d.ss) (fun s => s) (fun f => f))
        (mkHolds (tys g.d.ss) (@stateLoop _ _ _ ⟨g.inits⟩ g.inits (refBodyE g eb ev i bools bits)))).fst }
```
Checks against `[S]`: `refBodyE`'s type is the `body` field type of `SrcSem` `[B]` (`RegList … → Circuit …`; `Circuit.SigList … → Circuit … (ρ i)` is
the unfolded form of the `Circuit` function type used by `GenFacts` `[S]` `ShippingQuadComposed.lean:106`, where the `holds` is the second
argument of `body` as applied in `GenFacts.writes`: `body i bools bits (mkRegList …) (mkHolds …)`). `stateLoop` takes
`[Inhabited (HList αs)]`; the Lean text uses `letI : Inhabited (HList (tys g.d.ss)) := ⟨g.inits⟩` (the `inh` field), written `@stateLoop _ _ _ ⟨g.inits⟩`
above for definiteness — the elaborated text may use `letI` instead, which is the same term.

### 1.3 Theorems (the exact `GenFacts` instances; `letI` as above)
Let `F := genSemGenE X g eb ev` and `inh := ⟨g.inits⟩`.
```lean
theorem genSemGenE_writes (X : Name) (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (t : Nat) :
    valsAt (tys g.d.ss) (refBodyE g eb ev i bools bits
        (mkRegList S (tys g.d.ss) (fun s => s) (fun f => f)) (mkHolds (tys g.d.ss) S)).snd t =
      evalTerms
        (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)).b (g.d.bpos j))
        (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)).v (g.d.vpos j) w)
        g.d.nexts

theorem genSemGenE_result (X : Name) (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (t : Nat) :
    ((refBodyE g eb ev i bools bits (mkRegList S (tys g.d.ss) (fun s => s) (fun f => f))
        (mkHolds (tys g.d.ss) S)).fst).map (fun f => f t) =
      g.d.outs.map fun o => enc o.1 (eval
        (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)).b (g.d.bpos j))
        (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)).v (g.d.vpos j) w) o.2)

theorem genSemGenE_source (X : Name) (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    (genSemGenE X g eb ev).src i bools bits =
      (genSemGenE X g eb ev).obsR i
        ((genSemGenE X g eb ev).body i bools bits
          (mkRegList (@stateLoop _ _ _ ⟨g.inits⟩ g.inits ((genSemGenE X g eb ev).body i bools bits))
            (tys g.d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys g.d.ss) (@stateLoop _ _ _ ⟨g.inits⟩ g.inits ((genSemGenE X g eb ev).body i bools bits)))).fst
```
(`source` is `Eq.refl` after unfolding `genSemGenE`; the two hypotheses `S`-dependence are exactly `GenFacts.source`'s.) Proof plan:
`writes`: unfold `refBodyE`, `(a, b).snd = b`, `valsAt_sigListOfFn` P1 `[B]` with `f := nextFnE …`, then `reconState_mkHolds` P2 `[B]` rewrites the rebuilt state to `S`; the result is `nextFnE g eb ev i bools bits S t` which unfolds to the right side (`valAtE` is `typedVal … (S.val t)`).
`result`: `(a, b).fst = a`, `List.map_map`, `reconState_mkHolds`, unfold `resultFnE`/`valAtE`.

What U3 does **not** state (stays in the roadmap): `GenFacts.ok/body_eq/init` (from `GenIn.ok/bodyEq/init`, trivially `g.ok` etc. — carried
by the later `genSemGen_facts`), and `GenFacts.causal` (`HCausalOf`, P6'). **`FactsOf (.gen s)` contains `causal`** (`GenFacts` has a seventh
field `causal : HCausalOf d dom ext extB`, `[S]` `QuadComposed.lean:151`); rev2 §6 P3 listed only `writes/result/source`, so the
packaging `genPkg (.gen F) _` needs the causality lemma P6' as well and is *not* a consequence of U3 alone.

### 1.4 Checks planned for U3 (after approval)
`SemUnitsCheck`-style: TYPE (each of the 3 theorems compared with an independently written statement by `Eq`/defeq), MUTANT (signature/defeq
rejection only — **not** semantic counterexamples): (m1) `refBodyE` returns `(…, sigListOfFn _ (fun _ => g.inits))`; (m2) `genSemGenE` with
`obsR := fun _ _ => []`; (m3) `valAtE` reading `S.val (t+1)`; AXIOMS (`Lean.collectAxioms`, standard axioms only — this is an *axiom* audit, not
a closure audit for forbidden constants; the forbidden-constant closure audit is a separate check over the same list and is named separately in the report).

## 2. `callOut`, `withCall`, `memOut`, `ExtStage`: complete definitions (R2)
Definitions only, total. They instantiate `eb`/`ev` of §1 by `extBOf Q g`/`extOf Q g`. No lemma about them is frozen here (§4).
`variable (Q : Name → Option (SemPkg ι dom)) (g : GenIn)`; `kD := kDOf g.d`. Helpers `callArgs`, `callKind`, `originOf`, `lsrcAt` are rev2 §1/§2.1
(`lsrcAt d bs vs S` takes the *stage* families `bs vs` and the state `S`).

### 2.1 The bounds branch
Rev2's `calleeOut` looked `Q` up at `(insts[k]?.map (·.1)).getD .anonymous` when `k ≥ insts.length`; if `Q .anonymous` happened to be `some`, the
result was *not* the zero stream (the reviewer's point). Rev3 branches on the bounds first, so the out-of-range value does not consult `Q`:
```lean
/-- ordinary / field entry `k`, stage pair `(bs, vs)`, state `S`. -/
noncomputable def calleeOut (i : ι) (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (k : Nat) : Nat → Nat :=
  match g.d.shape.insts[k]? with
  | none => fun _ => 0                                   -- D1a: k ≥ insts.length. Q is NOT consulted
  | some (c, _) =>
    match Q c with
    | none => fun _ => 0                                 -- D1b: valid k, callee absent from Q
    | some q =>
      let vals : Nat → List Nat := valsOf (lsrcAt g.d bs vs S) (callArgs g.d k)
      let A := boolsOf (D := dom i) (q.d.bsIn.take q.kD) vals
      let B := bitsOf  (D := dom i) (q.d.bsIn.take q.kD) vals
      match selIdx g.d q k with
      | none => fun _ => 0                               -- D2a: no selected output
      | some k' => ((q.src i A B)[k']?).getD (fun _ => 0)  -- D2b: src list shorter than the layout

def selIdx (d : MachineData) (q : SemPkg ι dom) (k : Nat) : Option Nat :=
  if d.shape.instFields = [] then (if q.d.shape.layout.outs.length = 1 then some 0 else none)
  else q.d.shape.layout.outs.findIdx? (·.name = d.shape.instFields.getD k "")
```
(`valsOf` is `Tools.ShippingMachineCallsLinkedT.valsOf` `[S]` line 27; `boolsOf/bitsOf` `[S]` `ShippingMachineSeqChild.lean:24,29`. `findIdx?`
returns `none` when there is no match, so "`findIdx? = some k'`" has `k' < outs.length`; the `getD` on `src` covers a list shorter than the layout.)

Two theorems (statements are the roadmap, but the *case split* is now by construction):
- **out of range:** `g.d.shape.insts[k]? = none → calleeOut Q g i S bs vs k = fun _ => 0` — true for *every* `Q`, including `Q .anonymous = some _`.
- **valid index:** `g.d.shape.insts[k]? = some (c, a) → calleeOut Q g i S bs vs k` is the `Q c` branch (zero only when `Q c = none` or `selIdx = none`).
So "zero because `k` is out of range" and "zero because `Q c = none`" are different cases with different premises (`k < insts.length` is not a
premise of the first; `Q c = some q` is a premise only of the valid-index non-default branch).

### 2.2 Decoding by binder kind, the memory entry
```lean
noncomputable def withCall (i : ι) (k : Nat) (κ : MixedGateBinder) (f : Nat → Nat)
    (bs : Nat → Signal (dom i) Bool) (vs : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    (Nat → Signal (dom i) Bool) × ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :=
  match κ with
  | .bool   => (fun p => if p = kDOf g.d + k then ⟨fun τ => f τ != 0⟩ else bs p, vs)
  | .bits _ => (bs, fun p n => if p = kDOf g.d + k then ⟨fun τ => BitVec.ofNat n (f τ)⟩ else vs p n)   -- D3 truncating ofNat
  | .domain => (bs, vs)

def lsrcGet (L : List (Nat → Nat)) (l : Nat) (j : Nat) : Nat := ((L[l]?).map (· j)).getD 0       -- same default as `valsOf`

/-- the observation list of the lets under stage families `bs vs` and state `S` (the term of `letObsB`'s body, `[S]` SeqLinked:217) -/
noncomputable def lsrcAt (d : MachineData) {D : DomainConfig} (bs : Nat → Signal D Bool)
    (vs : (j n : Nat) → Signal D (BitVec n)) (S : Signal D (HList (tys d.ss))) : List (Nat → Nat) :=
  d.ls.map fun l t => enc l.1 (eval
    (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bs vs t (S.val t)).b (d.bpos j))
    (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bs vs t (S.val t)).v (d.vpos j) w) l.2)

noncomputable def memOut (cb : Bool) (aw dw l0 l1 l2 l3 : Nat) (i : ι) (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) : Signal (dom i) (BitVec dw) :=
  memRead (D := dom i) (aw := aw) (dw := dw) cb
    ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d bs vs S) l0 j)⟩
    ⟨fun j => BitVec.ofNat dw (lsrcGet (lsrcAt g.d bs vs S) l1 j)⟩
    ⟨fun j => lsrcGet (lsrcAt g.d bs vs S) l2 j != 0⟩
    ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d bs vs S) l3 j)⟩
```
`lsrcAt`/`lsrcGet` are new definitions of this revision (not in the tree; rev2 used `lsrcAt` as a name only). `memRead` is
`Tools.ShippingMachineMemLinked.memRead` `[S]` line 33 (`{D} {aw dw} cb A Dd E R`).

```lean
noncomputable def callOut (i : ι) (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))) :
    (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)) :=
  match g.d.shape.insts[k]? with
  | none => st                                                     -- D0: k ≥ insts.length: stage unchanged (bounds branch)
  | some _ =>
    match originOf g.d k with
    | .mem cb aw dw =>
      match callArgs g.d k with
      | [l0, l1, l2, l3] =>
          (st.1, fun p n => if p = kDOf g.d + k then
                              (if h : dw = n then h ▸ memOut g cb aw dw l0 l1 l2 l3 i S st.1 st.2 else ⟨fun _ => 0⟩)
                            else st.2 p n)
      | _ => st                                                    -- D4: not a 4-list: stage unchanged
    | _ => withCall g i k (callKind g.d k) (calleeOut Q g i S st.1 st.2 k) st.1 st.2   -- ordinary and `.field _`
```
(`originOf` is `InstOrigin`; the case `| _ =>` covers `.ord` and `.field _` exactly as `MemFacts`' `getD k .ord` and `CallField` do; the
`.mem` pattern's arity is that of `InstOrigin.mem` `[S]` (`.mem _ aw dw` with the first argument `cb`) — if `InstOrigin.mem` has a different
field order the implementation corrects the pattern and reports it; the meaning ("`cb aw dw`") is that of `MemFacts` line `child? = some (memModule cb aw dw)`.)

### 2.3 Staged families and the final families
```lean
noncomputable def ExtStage (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j n : Nat) → Signal (dom i) (BitVec n)) (S : Signal (dom i) (HList (tys g.d.ss))) :
    Nat → (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))
  | 0 => (bools, bits)
  | n + 1 => callOut Q g i S n (ExtStage Q g i bools bits S n)

noncomputable def extBOf (Q) (g : GenIn) : ExtB ι dom g.d.ss := fun i bools bits S => (ExtStage Q g i bools bits S g.d.shape.insts.length).1
noncomputable def extOf  (Q) (g : GenIn) : ExtV ι dom g.d.ss := fun i bools bits S => (ExtStage Q g i bools bits S g.d.shape.insts.length).2
noncomputable def genSemGen (Q) (X : Name) (g : GenIn) : SrcSem ι dom := genSemGenE X g (extBOf Q g) (extOf Q g)
```
**One state stream (R1, the P6 point).** In `ExtStage … S`, the same `S` is passed to every stage's `callOut` *and* is the state in
`lsrcAt g.d bs vs S` at every stage. In the source's `lsrc` (`letObsB`, `[S]` `ShippingMachineSeqLinked.lean:203`) the families are applied at
`S* := stateLoop inits (body i bools bits)` and the state read is `S*.val j`. The final-families `lsrc` of the generated package is therefore
```lean
-- S* := @stateLoop _ _ _ ⟨g.inits⟩ g.inits ((genSemGen Q X g).body i bools bits)   (the SAME S* in both places)
lsrcAt g.d (extBOf Q g i bools bits S*) (extOf Q g i bools bits S*) S*  =  (SemPkg.gen (genSemGen Q X g)).lsrc i bools bits
```
i.e. the `S` consumed by `callOut` in building `extBOf … S*`/`extOf … S*` **and** the `S` in the last `lsrcAt` (the observation `MemFacts`
refers to) is that one `S*`. (`SemPkg.lsrc` `[B]` for `.gen` is `letObsB` at `stateLoop`; the displayed equality is the P4c obligation, roadmap.)
No second stream is introduced: P6 below is stated at `S*` for both.

### 2.4 Defaults (total, never assumed) vs. success conditions (rev2 §5.2, corrected)
| code | situation | value (default) | success condition (not assumed by the definition) |
|---|---|---|---|
| D0/D1a | `k ≥ insts.length` | `callOut`: stage unchanged; `calleeOut`: zero | none needed; **no `Q` lookup** (bounds branch) |
| D1b | `k` valid, `Q c = none` | zero stream | S1 `Q c = some q` (a `genS` strictness property, DG-ACC/DG-SEM §7) |
| D2 | `selIdx = none`, or `src` shorter than layout | zero stream | S2 `CallField p q k o` (T2-FIELD, other issue) |
| D3 | `f τ ≥ 2^w` | `ofNat` truncation / `!= 0` | S3 `CallOutRange` (§3) |
| D4 | memory entry not a 4-list | stage unchanged | A4 (a literal `MemFacts` conjunct) |
| D5 | argument `let` index out of range | observation `0` (`valsOf`, `lsrcGet`) | A3 |
| D6 | `instOrigins` shorter than `insts` | `getD k .ord` ⇒ ordinary | A2 |
| D7 | memory result width `n ≠ dw` | zero `BitVec n` | B2 (`callKind = .bits dw`) |
`CallOut`/`GenExtAtCall`/`MemFacts` are theorems under the success conditions and `GenWF`, never the definitions.

## 3. Corrections to rev2 §1.4–§1.5 and §5.3 (R3)

### 3.1 `MemFacts` conjuncts: which rows are literal, which are sufficient (R3-a)
Rev2 §1.5 closed with "Without A4, B2, B3 the first conjunct that fails is …, so they are necessary rows". That is **corrected**:
| row | relation to `MemFacts shape lsrc nL bsI kD ext k c` `[S]` `ShippingMachineCallsLinkedT.lean:31` |
|---|---|
| A3 (`l_i < d.ls.length`) | literal: the four `l_i < nL` conjuncts, with `nL = d.ls.length` |
| A4 (4 arguments) | literal: `(insts.map (·.2.1))[k]? = some [l0,l1,l2,l3]` is a list equality, so it forces exactly 4 entries |
| B2 (`callKind = .bits dw`) | literal: `bsI[k]?.map (·.2) = some (.bits dw)` (`bsI = d.bsIn.drop kD`) |
| **B3** (`letSort l0 = bits aw`, `l1 = bits dw`, `l2 = bool`, `l3 = bits aw`) | **sufficient condition for this construction only.** It yields the four `lsrc[l]? = some (fun j => (X.val j).toNat)` / `if E.val j then 1 else 0` conjuncts through `enc_lt` and `BitVec.toNat_ofNat`, with `X := ⟨fun j => BitVec.ofNat w (lsrc l j)⟩`. **That `MemFacts` implies B3, i.e. that the sorts must match, is not proved in this study**: `MemFacts` only constrains the observation *values* (`lsrc[l]` is a `toNat` of some `BitVec`/the indicator of some `Bool`); a `let` of another sort whose encoded values happen to stay in range would also satisfy the conjunct. B3 is retained as the row that makes the existing proof route go through, not as a derived necessity. |
| last conjunct `ext (kD+k) dw = memRead …` | by construction of `callOut`'s memory branch (§2.2) + stage preservation (roadmap P4a/P4d) |
| first conjunct (`child? = some (memModule cb aw dw)`) | `originOf d k = .mem cb aw dw` |
"Necessary" is therefore claimed only for A3/A4/B2 as literal conjuncts; A1, A2 are definedness rows (so that `kDOf` and the `getD` defaults are not
taken), also not derived from `MemFacts`; B3 and RowC are sufficient-for-the-route rows.

### 3.2 `GenWF` REV rows (R3 / item 4)
REV-1…REV-4 (rev2 §1.4) are written as an **explicitly conditional core**: they are the rows that the *proof route of this unit chain* uses (A3/A4/B2 literal,
A1/A2 definedness, B3/RowC sufficient). They are a text of `GenWF` **as defined by this unit**, not a strengthening of an accepted definition and not an
FG/coverage change. **What remains open and is NOT discharged by writing the rows down:** DG-WFCOVER must still supply every row on every real run that
`dataOf` accepts (this study found no supplier for A4/B2/B3/RowC at `9d26005c`: "not found", not "impossible"). No premise is added to FG, no coverage
is narrowed, and `GenWF` is not strengthened beyond these rows; if a reviewer or the user holds otherwise, §7 of rev1 applies (decision document, stop).

### 3.3 `houtTy`: base time vs. later suppliers (R3-b)
Rev2 §5.3 said `houtTy` "has no current supplier". Refined, with the time of each statement:
- **At the base of this branch** (`Tools/ShippingGen5T2Range.lean`, `par/gen5-t2` e57eb431 / comment sync 314c2119, present in this worktree): `callOutRange_of_widths`
  takes `houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width` as an explicit hypothesis; the file header states `T1Hyp`'s `DataOk` is an abstract parameter,
  so *at that commit* no field gives `houtTy` for the callee (this study found no supplier there).
- **Later suppliers (conditional, not available as built results here):** the T2-OUTTY and T2-ND work items are the intended later suppliers of the output-type/
  width row (`houtTy`) and of the `Nodup`-of-output-names row used by `selIdx`/`callField_unique_of_ok`. This study did **not** inspect their definitions
  or build state; whatever they provide will be conditional on their own premises. They are recorded here as *named future suppliers*, not as a supply:
  S3 (`CallOutRange`) and `houtTy` stay **UNSUPPLIED intermediate premises** of P4e, exactly as in rev2, until those items are accepted *and* their
  premises are themselves supplied. `CallOutWidthAt` stays G-ONEOUT-WID / `hkidW`.
The sync is therefore: base time = abstract hypothesis; OUTTY/ND = later, conditional suppliers; neither is counted as supplied by U3.

## 4. ROADMAP — NOT FULL TYPES (separate from §1; approval of this revision does not freeze these)
Sketches only; each will be re-frozen with a complete telescope before implementation (in the order U3 → P4a/P4d → P6 → …). Items referencing
`lsrc`, `S`, `c` below are *placeholders* in the roadmap and are bound only when re-frozen.
| id | content (sketch) | binds/obligation to fix when promoted |
|---|---|---|
| P4a | `typedVal_let_congr` and `lsrcAt_congr` (rev2 §2.1), with `cleanLets` | statement exists in rev2 §2.1 with full hypotheses; to be re-checked with the bounds-branch `callOut` |
| P4c | `lsrcAt g.d (extBOf …S*) (extOf …S*) S* = (genSemGen …).lsrc …` (§2.3) | `S*` fixed as in §2.3 |
| P4d | `ExtStage_agree` (stage `m ≥ n` agrees with stage `n` below `kD+n`) | proved with D0 (out-of-range stage unchanged) |
| P4e | `genExtAtCall_of_genSem` (ordinary) under S1–S3 | S3 = unsupplied (§3.3) |
| P5 | `.comb` arm facts | |
| P6 | `memFacts_of_genSem`: `MemFacts` at `lsrc := lsrcAt g.d (extBOf…S*) (extOf…S*) S*`, `ext := extOf Q g i bools bits S*`, the **same `S*`** as in §2.3; premises `GenWF g.d`, `originOf g.d k = .mem cb aw dw`, `k < insts.length`, a name `c` for the `MemFacts` argument (`c` is bound by `insts[k]? = some (c,_)`) | **`c` and `S*` were unbound in rev2 §6 P6; they are bound here in intent and become a binder in the re-freeze** |
| P6' | `GenFacts.causal` (`HCausalOf`) from callee causality | memory-lemma location "not located yet" in rev2; remains so |
| P7 | `genSemI_local` | |
| P11/P12 | `genFacts_gen`, `genSemI`, `genSem`, `GenData.toIn`, `genS_some_inv_of_unfold` | P12 needs DG-DATAOF output (premise) |
Ownership of `genS` / `genSem_local` / `GenIn.wf` coverage: unchanged from rev2 §7.

## 5. Not claimed
- Nothing in §1 or §2 is elaborated; no Lean is edited in this revision. U3's checks (§1.4) are planned.
- No supplier is claimed for `GenIn`, `GenWF` coverage (DG-WFCOVER), `houtTy`, `CallOutWidthAt`, S1–S3, `Acc`, or `GenExtAtCall`/`HPointG`.
- MUTANT results elsewhere in this issue are signature/defeq rejections, not semantic counterexamples.
- No FG/M5 completion; no change to FG, a shared definition, the compiler, or any law; no coverage narrowing.
- Other agents' in-flight work (SRC-ARGW `kjob/g3aw-impl`, READKINDS `kjob/g5rk-impl`, M4) was not touched or duplicated.

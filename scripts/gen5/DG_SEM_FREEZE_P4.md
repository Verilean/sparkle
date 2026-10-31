# DG-SEM freeze P4 — the `Q`-version of `genSem`, `genSemI_local`, the memory-entry `ext`, staged families (docs only)

**FOR REVIEW — design only (docs-only commit, no Lean edited, nothing elaborated).** Independent of the U3 audit fix. Branch `kjob/g5sm-aud`, base U3
`kjob/g5sm-u3` `309a33a9` (U3 = `Tools/ShippingGen5SemGen.lean`, scoped-accepted). Supersedes, for the units listed in §0, the *sketches* of
`DG_SEM_FREEZE_REV3.md` §2 and §4 (rev3 §2 had definitions only, rev3 §4 was roadmap). Everything here is a PROPOSAL until approved; "`[B]`" = built text,
"`[S]`" = source read in this worktree, "`[N]`" = new in this document. No new TRUSTED boundary, law, FG/guarantee change, shared-definition
or compiler edit; no `sorry`/`axiom`/`native_decide`; no `GenWF` strengthening; no FG shrinking.

**rev1 (this revision; docs + one scratch check file, answers the `changes_requested` on 30efb522).** R1: instance entries are triples `(c, a, κ)` — `callOut_local`, `callOut_mem_val`, `ext_mem_final`, `memFacts_of_genSem` and the §0/§5 text now bind `κ` (`some (c, a, κ)`). R2: `calleeOut_of_none` is excluded (same statement as `calleeOut_none`); the common `variable` block is Lean text (§2.0); the types are elaborated in `Tests/Gen5/SemP4FreezeTypes.lean` (§2.0). ACC Q1 (`genSem_decl`, `genSem_d`) is supplied in §1/§3 below. U4E/U4F stay conditional on `d.ok`/`GenWF`; coverage, causality, `dataOf`, ACC, M5, FG remain unsupplied.

## 0. What is frozen with a complete telescope here, and what is not

| unit | content | status in this document |
|---|---|---|
| **U4A** | definitions: `ordCallees`, `lsrcGet`, `lsrcAt`, `selIdx`, `calleeOut`, `withCall`, `memOut`, `callOut`, `ExtStage`, `extBOf`, `extOf`, `genSemGen`, `genSemComb`, `genSemI`, `genSemVia` | **full types** (§2) |
| **U4B** | `genSemI_local` (+ `ExtStage_local`, `callOut_local`), `genSemI_decl`, `genSemI_d`, `genSemI_not_loop` | **full types** (§3) |
| **U4C** | `callOut_none`, `callOut_frame`, `ExtStage_succ`, `ExtStage_agree` (P4d), `calleeOut_none` (rev0 also listed a name `calleeOut_of_none`; it is **excluded**: it would be the same statement as `calleeOut_none` — `insts[k]? = none → calleeOut … = fun _ => 0` — so one name is kept, see §4) | **full types** (§4) |
| **U4D** | memory-entry `ext` at its own stage: `callOut_mem_val` | **full type** (§5.1) |
| **U4E** | `typedVal_let_congr`, `lsrcAt_congr` (P4a/P4b) | **full types** (§5.2); the proof is the hard part, class I |
| **U4F** | `ext_mem_final`, `lsrcAt_genSemGen` (P4c), `memFacts_of_genSem` (P6) | **full types** (§5.3); depend on U4C, U4E |
| not here | `GenFacts.causal` (P6'), `genFacts_gen`/`genFacts` (P11), `genExtAtCall_of_genSem` (P4e, needs S3), `GenData.toIn`/`dataOf` | roadmap (§8); P6' and P4e are not designed here |

Implementation order: U4A → U4B ∥ U4C → U4E → U4D → U4F. U4A/U4B/U4C do **not** need `d.ok`, `GenWF`, `dataOf` (class I, definitional / structural);
U4E needs `d.ok`; U4F needs `GenWF` (rows RowC/A4/B2/B3, already built as `[B]` `GenWF` in `Tools/ShippingGen5SemGen.lean`).

## 1. Interface for DG-ACC (names and argument order — fixed here)

DG-ACC (`kjob/g5ac-309a33a9`, `scripts/gen5/DG_ACC_FREEZE.md` §2.1) takes `genSem`/`genSem_local`/`genSem_decl`/`genSem_d`/`ordCallees` as **fields of one structure** (a
kit); these are the exact types the kit fields can be instantiated with. Variables throughout (new file `Tools/ShippingGen5SemCall.lean`, namespace
`Tools.ShippingGen5Sem`, `set_option autoImplicit false`; same `open`s as `Tools/ShippingGen5SemGen.lean` `[B]`):
`{ι : Type} {dom : ι → DomainConfig}`. **Argument order convention: callee table `Q` first, then declaration name `X`, then the reader data `g`; per-run
arguments `i bools bits` and then `S` last.** `U3`'s `genSemGenE X g eb ev` keeps its built order (no `Q`).

| name | type | DG-ACC kit field | note |
|---|---|---|---|
| `ordCallees` | `(d : MachineData) → List (Fin d.shape.insts.length)` | `ordCallees` | `(List.finRange _).filter fun k => (d.shape.instOrigins.getD k .ord).child? = none` (DGEN §2.1 text) |
| `genSemI` | `(Q : Name → Option (SemPkg ι dom)) → (X : Name) → (g : GenIn) → SemPkg ι dom` | the body of `genSem` | the real definition; over `GenIn` |
| `genSemVia` | `(GD : ConstantInfo → Type) → (toIn : {E : ConstantInfo} → GD E → GenIn) → (Q : Name → Option (SemPkg ι dom)) → (X : Name) → {E : ConstantInfo} → GD E → SemPkg ι dom` | `genSem` (with `GD`, `toIn` instantiated) | `genSemVia GD toIn Q X gd := genSemI Q X (toIn gd)`; `toIn` is DG-DATAOF's `GenData.toIn` when built (premise, **not supplied here**) |
| `genSemI_local` | §3 | `genSem_local` | the statement over `genSemI` (§3); the kit field's statement follows by `congrArg` with `toIn` |
| `genSemI_decl` | `∀ Q X g, (genSemI Q X g).decl = X` | `genSem_decl` | by cases on the arm test (§3) |
| `genSemI_d` | `∀ Q X g, (genSemI Q X g).d = g.d` | `genSem_d` (`dOf g = g.d`) | by cases on the arm test (§3) |

This answers DG-ACC freeze §9 Q1 (request for `genSem_decl`/`genSem_d`): both are in U4B. `mem_ordCallees` (DG-ACC Q2 default: proved in DG-ACC's A1) stays
as DG-ACC has it; here it is `Iff.rfl`-level on the filter (`List.mem_filter`, `List.mem_finRange`) and is **not** part of these units. `GenData`/`dataOf`/`GenData.toIn` are not
defined here.

## 2. U4A — definitions with complete telescopes

### 2.0 Common declarations (Lean text, used by every statement of §2–§5)
```lean
set_option autoImplicit false
namespace Tools.ShippingGen5Sem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingMachineRef (reads)
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Sparkle.Compiler.MachInstOrigin

variable {ι : Type} {dom : ι → DomainConfig}
-- the next block is the binder context of the statements of §3–§5 (a statement mentions only the ones it uses)
variable (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (i : ι)
  (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
  (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
  (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
  (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n))
```
**Instance entries.** `g.d.shape.insts : List (Name × List Nat × MixedGateBinder)` `[S]` `Sparkle/Compiler/Elab.lean:5039` — an entry is `(callee name c, argument lets a, binder kind κ)`, a
**triple** `(c, a, κ) = (c, (a, κ))`. Every `insts[k]? = some _` hypothesis below binds all three: `some (c, a, κ)` (rev0 wrote `some (c, a)` with `a : List Nat`, a type mismatch; fixed). Where `κ`
is not used it is still bound in the statement (a binder, not a premise). `callArgs d k` is the `a` component and `callKind d k` reads `bsIn`, not `κ`; their relation to `κ` is not asserted here.

**Elaboration check (rev1, new).** `Tests/Gen5/SemP4FreezeTypes.lean` (scratch, lean_lib `Tests.Gen5.SemP4FreezeTypes`) holds the §2 definitions and, for every statement of §3–§5, a
`def S_<name> : Prop := …` with the same telescope and **no proof, no `sorry`**; Pod `kjob lake build Tests.Gen5.SemP4FreezeTypes` exit 0. This check found one error in rev0 beyond the reviewed
ones: `boolsOf`/`bitsOf` live in `Tools.ShippingMachineChild` (`Tools/ShippingMachineSeqChild.lean:24,29`), not opened — the §2 text now qualifies them. Statements are checked in the
`Prop`-def form (hypotheses as arrows, `∀` after the colon); the `theorem` form below has the same binder types, but a `theorem` header itself was not elaborated. `ordCallees` elaborates with the
`child? = none` filter as written (decidability found), so the `isNone` fallback of the note below is not needed. That check shows the **types** elaborate; it proves nothing about any lemma.

```lean
-- ordinary callees: entries whose origin builds no child (`.ord`, `.field _`); memory entries are excluded
def ordCallees (d : MachineData) : List (Fin d.shape.insts.length) :=
  (List.finRange d.shape.insts.length).filter fun k => (d.shape.instOrigins.getD k .ord).child? = none
```
(The filter predicate is a `Prop` coerced through `decide`; `InstOrigin.child?` returns `Option (Module × Design)` `[S]` `Sparkle/Compiler/MachInstOrigin.lean:28`. Whether
`DecidableEq` for that `Option` exists is checked at implementation; if not, the equivalent `(d.shape.instOrigins.getD k .ord).child?.isNone` is used and the equivalence
`child? = none ↔ isNone = true` is a one-line lemma — reported, not silently changed.)

```lean
def lsrcGet (L : List (Nat → Nat)) (l : Nat) (j : Nat) : Nat := ((L[l]?).map (· j)).getD 0

/-- observation list of the lets under stage families `bs vs` and state `S` (the term of `letObsB`'s body, `[S]` Tools/ShippingMachineSeqLinked.lean:217) -/
noncomputable def lsrcAt (d : MachineData) {D : DomainConfig} (bs : Nat → Signal D Bool)
    (vs : (j n : Nat) → Signal D (BitVec n)) (S : Signal D (HList (tys d.ss))) : List (Nat → Nat) :=
  d.ls.map fun l t => enc l.1 (eval
    (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bs vs t (S.val t)).b (d.bpos j))
    (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bs vs t (S.val t)).v (d.vpos j) w) l.2)

def selIdx (d : MachineData) (q : SemPkg ι dom) (k : Nat) : Option Nat :=
  if d.shape.instFields = [] then (if q.d.shape.layout.outs.length = 1 then some 0 else none)
  else q.d.shape.layout.outs.findIdx? (·.name = d.shape.instFields.getD k "")
```
`(j n : Nat) → …` is `(j : Nat) → (n : Nat) → …`. In the `.field` rows `instFields` is the shape's own list; `selIdx` implements `CallField p q k o` as an index (rev2 §5.1 text; **the
index of the first match** is *the* match when the callee's output names are `Nodup`, which comes from the callee's `Pkg.ok`, not from `GenWF`).

```lean
noncomputable def calleeOut (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat) : Nat → Nat :=
  match g.d.shape.insts[k]? with
  | none => fun _ => 0                                  -- D1a: k out of range; `Q` is NOT consulted
  | some (c, _, _) =>                                   -- shape.insts entry = (callee name, argument lets, binder kind κ)
    match Q c with
    | none => fun _ => 0                                -- D1b
    | some q =>
      let vals : Nat → List Nat := ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) (callArgs g.d k)
      let A := Tools.ShippingMachineChild.boolsOf (D := dom i) (q.d.bsIn.take q.kD) vals
      let B := Tools.ShippingMachineChild.bitsOf (D := dom i) (q.d.bsIn.take q.kD) vals
      match selIdx g.d q k with
      | none => fun _ => 0                              -- D2a
      | some k' => ((q.src i A B)[k']?).getD (fun _ => 0)   -- D2b

noncomputable def withCall (g : GenIn) (i : ι) (k : Nat) (κ : MixedGateBinder) (f : Nat → Nat)
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) :
    (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)) :=
  match κ with
  | .bool   => (fun p => if p = kDOf g.d + k then ⟨fun τ => f τ != 0⟩ else bs p, vs)
  | .bits _ => (bs, fun p n => if p = kDOf g.d + k then ⟨fun τ => BitVec.ofNat n (f τ)⟩ else vs p n)   -- D3 truncating ofNat
  | .domain => (bs, vs)

noncomputable def memOut (g : GenIn) (cb : Bool) (aw dw l0 l1 l2 l3 : Nat) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) : Signal (dom i) (BitVec dw) :=
  Tools.ShippingMachineMemLinked.memRead (D := dom i) (aw := aw) (dw := dw) cb
    ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d bs vs S) l0 j)⟩
    ⟨fun j => BitVec.ofNat dw (lsrcGet (lsrcAt g.d bs vs S) l1 j)⟩
    ⟨fun j => lsrcGet (lsrcAt g.d bs vs S) l2 j != 0⟩
    ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d bs vs S) l3 j)⟩

noncomputable def callOut (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))) :
    (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)) :=
  match g.d.shape.insts[k]? with
  | none => st                                                     -- D0: stage unchanged (bounds branch)
  | some _ =>
    match originOf g.d k with
    | .mem cb aw dw =>
      match callArgs g.d k with
      | [l0, l1, l2, l3] =>
          (st.1, fun p n => if p = kDOf g.d + k then
                              (if h : dw = n then h ▸ memOut g cb aw dw l0 l1 l2 l3 i S st.1 st.2 else ⟨fun _ => 0⟩)
                            else st.2 p n)
      | _ => st                                                    -- D4
    | _ => withCall g i k (callKind g.d k) (calleeOut Q g i S st.1 st.2 k) st.1 st.2   -- `.ord` and `.field _`

noncomputable def ExtStage (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j n : Nat) → Signal (dom i) (BitVec n)) (S : Signal (dom i) (HList (tys g.d.ss))) :
    Nat → (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))
  | 0 => (bools, bits)
  | n + 1 => callOut Q g i S n (ExtStage Q g i bools bits S n)

noncomputable def extBOf (Q : Name → Option (SemPkg ι dom)) (g : GenIn) : ExtB ι dom g.d.ss :=
  fun i bools bits S => (ExtStage Q g i bools bits S g.d.shape.insts.length).1
noncomputable def extOf (Q : Name → Option (SemPkg ι dom)) (g : GenIn) : ExtV ι dom g.d.ss :=
  fun i bools bits S => (ExtStage Q g i bools bits S g.d.shape.insts.length).2

noncomputable def genSemGen (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) : SrcSem ι dom :=
  genSemGenE X g (extBOf Q g) (extOf Q g)

noncomputable def genSemComb (X : Name) (g : GenIn) : CombSem ι dom :=
  ⟨X, g.d, kDOf g.d, g.inits,
    fun _ bools bits =>
      g.d.outs.map fun o t => enc o.1 (eval
        (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls bools bits t g.inits).b (g.d.bpos j))
        (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls bools bits t g.inits).v (g.d.vpos j) w) o.2)⟩

noncomputable def genSemI (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) : SemPkg ι dom :=
  if g.d.ss.isEmpty && g.d.shape.insts.isEmpty then .comb (genSemComb X g) else .gen (genSemGen Q X g)

noncomputable def genSemVia (GD : Lean.ConstantInfo → Type) (toIn : {E : Lean.ConstantInfo} → GD E → GenIn)
    (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (gd : GD E) : SemPkg ι dom :=
  genSemI Q X (toIn gd)
```
Notes on what is and is not asserted by the definitions:
- **Corrections to rev3 §2** (all are binder/typing completions, none is a semantic change): `calleeOut`/`withCall`/`memOut`/`callOut` now take `g : GenIn` as an *explicit* argument
  (rev3 wrote it as an ambient `variable`; with `variable (g)` the order would have been implicit); `memRead` and `valsOf` are written with their qualified names; `genSemComb` gets
  the `fun _ bools bits` binder for the unused `i`. `genSemGenE X g eb ev` is U3's built order.
- `genSemComb`'s `hres` is the right side of `CombFacts.hres` `[S]` `Tools/ShippingGen2CombPkg.lean:54-58` (so `hres` is `List.map_map`/`rfl`); `hnext` is a **separate** unit (P5, roadmap): it needs `g.d.ss = []` and `HList []` being a subsingleton.
- The arm test is a `Bool`, so no `Decidable` instance on `List` equality is used. If a call-free but state-carrying declaration (`ss ≠ []`, `insts = []`) exists it takes `.gen` with `ExtStage … 0 = (bools, bits)`.
- `.loop` is never produced (rev1 §2.5, unchanged).
- The Lean may need `@stateLoop` instance spelling as in U3; no semantic effect.
- Defaults vs. success conditions are as rev3 §2.4 (D0–D7 / S1–S4), not repeated; **none of S1–S4 is assumed by any definition here**.

## 3. U4B — locality and arm accessors

```lean
theorem genSemI_decl (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) : (genSemI Q X g).decl = X
theorem genSemI_d (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) : (genSemI Q X g).d = g.d
theorem genSemI_not_loop (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) :
    ∀ s : LoopSem ι dom, genSemI Q X g ≠ .loop s
```
Proof: `unfold genSemI; split <;> simp [SemPkg.decl/SemPkg.d, genSemComb, genSemGen, genSemGenE]` (each arm is a structure literal with `decl := X`, `d := g.d`).

```lean
theorem callOut_local (Q Q' : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (hQ : ∀ (c : Name) (a : List Nat) (κ : MixedGateBinder), g.d.shape.insts[k]? = some (c, a, κ) →
            (originOf g.d k).child? = none → Q c = Q' c) :
    callOut Q g i S k st = callOut Q' g i S k st

theorem ExtStage_local (Q Q' : Name → Option (SemPkg ι dom)) (g : GenIn)
    (hQ : ∀ k ∈ ordCallees g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1)
    (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (n : Nat) :
    ExtStage Q g i bools bits S n = ExtStage Q' g i bools bits S n

theorem genSemI_local (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (hQ : ∀ k ∈ ordCallees g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) :
    genSemI Q X g = genSemI Q' X g
```
The hypothesis of `genSemI_local` is exactly DGEN §2.1 `genSem_local` / DG-ACC kit field `genSem_local` (`k ∈ ordCallees (dOf g)`, `Q (insts[k]).1 = Q' (insts[k]).1`).
Proof plan: `callOut_local` — `D0`/mem arms/`.domain` do not mention `Q`; the `| _ =>` arm reads `Q c` only inside `calleeOut` (`match Q c`), at `c := (insts[k]).1` with `child? = none`;
`ExtStage_local` by induction on `n` for **all** `n` (for `n > insts.length` the extra `k ≥ insts.length` stages are `D0`, again `Q`-free — so no bound on `n` is needed);
the hypothesis for the induction step at `k < insts.length` is `hQ ⟨k, hk⟩` after `List.mem_filter` (membership in `ordCallees` ↔ `child? = none` for `k < n`); `genSemI_local`: the arm test mentions only `g`, the `.gen` arm is `genSemGenE X g (extBOf Q g) (extOf Q g)` and `extBOf/extOf` are `funext` over `ExtStage_local`.
Not claimed: `genSemI_local` does not say the facts of `genSemI Q X g` and `genSemI Q' X g` agree (it is an equality of the data, which makes any fact about one a fact about the other).

## 4. U4C — structural lemmas on `callOut`/`ExtStage` (class I; no `GenWF`, no `d.ok`)

```lean
theorem ExtStage_zero (Q) (g : GenIn) (i : ι) (bools) (bits) (S) : ExtStage Q g i bools bits S 0 = (bools, bits)        -- rfl
theorem ExtStage_succ (Q) (g : GenIn) (i : ι) (bools) (bits) (S) (n : Nat) :
    ExtStage Q g i bools bits S (n + 1) = callOut Q g i S n (ExtStage Q g i bools bits S n)                           -- rfl

theorem callOut_none (Q) (g : GenIn) (i : ι) (S) (k : Nat) (st)
    (hk : g.d.shape.insts[k]? = none) : callOut Q g i S k st = st                                                      -- D0
theorem calleeOut_none (Q) (g : GenIn) (i : ι) (S) (bs) (vs) (k : Nat)
    (hk : g.d.shape.insts[k]? = none) : calleeOut Q g i S bs vs k = fun _ => 0                                         -- D1a, for EVERY Q

/-- `callOut k` changes only position `kDOf g.d + k` (Bool family and BitVec family, every width) -/
theorem callOut_frame (Q) (g : GenIn) (i : ι) (S) (k : Nat) (st) :
    (∀ p, p ≠ kDOf g.d + k → (callOut Q g i S k st).1 p = st.1 p) ∧
    (∀ p n, p ≠ kDOf g.d + k → (callOut Q g i S k st).2 p n = st.2 p n)

/-- P4d: stage `m ≥ n` agrees with stage `n` on every position `< kDOf g.d + n` -/
theorem ExtStage_agree (Q) (g : GenIn) (i : ι) (bools) (bits) (S) {n m : Nat} (h : n ≤ m) :
    ∀ p, p < kDOf g.d + n →
      (ExtStage Q g i bools bits S m).1 p = (ExtStage Q g i bools bits S n).1 p ∧
      ∀ w, (ExtStage Q g i bools bits S m).2 p w = (ExtStage Q g i bools bits S n).2 p w
```
(Binders: every theorem of §3–§5 is stated under the common `variable` block of §2.0; where a theorem writes a binder explicitly it is the same type.)
Proof of `ExtStage_agree`: `Nat.le_induction` on `m`; step `m ↦ m+1` uses `callOut_frame` with `p < kD + n ≤ kD + m` so `p ≠ kD + m`.
`callOut_frame`: `unfold callOut`, `split` on the `insts[k]?`, `originOf`, `callArgs` matches; `withCall` by `split` on `κ`; the `if p = kD + k` branches rewrite by the hypothesis `p ≠ kD + k` (`if_neg`).
The `h ▸` in the memory arm is eliminated by `split` on `dw = n` (`dite`) — the only place with a cast; both branches are `if_neg` at `p ≠ kD + k`.

## 5. U4D/U4E/U4F — memory-entry `ext` and stage preservation

### 5.1 U4D: the memory entry at its own stage
```lean
theorem callOut_mem_val (Q) (g : GenIn) (i : ι) (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat) (st)
    (cb : Bool) (aw dw l0 l1 l2 l3 : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (ho : originOf g.d k = .mem cb aw dw)
    (ha : callArgs g.d k = [l0, l1, l2, l3]) :
    (callOut Q g i S k st).2 (kDOf g.d + k) dw = memOut g cb aw dw l0 l1 l2 l3 i S st.1 st.2
```
Proof: `unfold callOut; rw [hk, ho, ha]` (with the `match` reducing), `if_pos rfl`, `dif_pos rfl`; the `h ▸` with `h = rfl : dw = dw` reduces by `rfl`/`Eq.mpr_rfl`.
`Q` does not occur on the right side: **a memory entry does not read `Q`** (this is the premise-shape the DG-ACC locality needs).

### 5.2 U4E: stage preservation through `let`s (P4a/P4b, rev2 §2.1)
```lean
theorem typedVal_let_congr (d : MachineData) (hok : d.ok = true) (k : Nat) {D : DomainConfig}
    (bools bools' : Nat → Signal D Bool)
    (bits bits' : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (t : Nat) (x : HList (tys d.ss))
    (hb : ∀ p, p < kDOf d + k → (bools p).val t = (bools' p).val t)
    (hv : ∀ p w, p < kDOf d + k → (bits p w).val t = (bits' p w).val t) :
    ∀ q, (cleanLets d k)[q]? = some true →
      (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).b (d.nIn + d.ss.length + q) =
        (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools' bits' t x).b (d.nIn + d.ss.length + q) ∧
      ∀ w, (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).v (d.nIn + d.ss.length + q) w =
        (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools' bits' t x).v (d.nIn + d.ss.length + q) w

theorem lsrcAt_congr (d : MachineData) (hok : d.ok = true) (k : Nat) {D : DomainConfig}
    (bs bs' : Nat → Signal D Bool) (vs vs' : (j n : Nat) → Signal D (BitVec n))
    (S : Signal D (HList (tys d.ss))) (t : Nat)
    (hb : ∀ p, p < kDOf d + k → (bs p).val t = (bs' p).val t)
    (hv : ∀ p w, p < kDOf d + k → (vs p w).val t = (vs' p w).val t) :
    ∀ l, (cleanLets d k)[l]? = some true → lsrcGet (lsrcAt d bs vs S) l t = lsrcGet (lsrcAt d bs' vs' S) l t
```
`cleanLets`/`posOk`/`RowC` are `[B]` in `Tools/ShippingGen5SemGen.lean:24-45`. The hypotheses shape matches `ExtStage_agree` (`k := n`). Proof plan (not tried): induction over `d.ls` generalising the
accumulated clean list (the let valuation is `letVal`'s left fold, `Tools/ShippingMachineDenote.lean:91`), `eval_congr_wf` (`:202`) with `okB j := posOk d k clean (d.bpos j)` — which needs `Term.WF` of each
`let`, taken from `d.ok` through `LetsTyped` (`:360`; `d.ok` unfolds to `decide (LetsTyped …) && …`, `Tools/ShippingMachineAuto.lean:242`) — **whether `d.ok = true` is enough, or the `LetsTyped` conjunct must be
extracted as its own premise, is a point to be checked when this unit starts; if the latter, the premise is `LetsTyped d.bpos d.vpos d.kb d.kv d.vw d.K (d.nIn + d.ss.length) d.ls` (a conjunct of `d.ok`), not a new assumption.**
This is the largest proof of the plan (class I, induction with an accumulator); it can be delivered after U4A–U4D.

### 5.3 U4F: final-stage equation and `MemFacts`
```lean
theorem ext_mem_final (Q) (g : GenIn) (i : ι) (bools) (bits) (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (cb : Bool) (aw dw l0 l1 l2 l3 : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (ho : originOf g.d k = .mem cb aw dw)
    (ha : callArgs g.d k = [l0, l1, l2, l3]) (hwf : GenWF g.d = true) (hok : g.d.ok = true) :
    extOf Q g i bools bits S (kDOf g.d + k) dw =
      Tools.ShippingMachineMemLinked.memRead (D := dom i) (aw := aw) (dw := dw) cb
        ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l0 j)⟩
        ⟨fun j => BitVec.ofNat dw (lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l1 j)⟩
        ⟨fun j => lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l2 j != 0⟩
        ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l3 j)⟩
```
Proof plan: (1) position `kD + k` of stage `k+1` is `memOut … st_k` (`callOut_mem_val`, `ExtStage_succ`); (2) later stages do not change it (`ExtStage_agree` with `n := k+1`, `p := kD + k < kD + (k+1)`, `m := insts.length`, needs `k+1 ≤ insts.length` from `hk`); (3) for each `lₓ ∈ callArgs g.d k` the four lets are clean at stage `k`
(`RowC`, from `hwf` by `List.all_eq_true` and `(callArgs d k).all …`) so `lsrcAt_congr` (with `bs := (ExtStage … k).1`, `bs' := final`, hypotheses from `ExtStage_agree`) rewrites the four observation streams from stage-`k` to final families; (4) `Signal` extensionality.

```lean
theorem lsrcAt_genSemGen (Q) (X : Name) (g : GenIn) (i : ι) (bools) (bits) :
    let Sst := @stateLoop _ _ _ ⟨g.inits⟩ g.inits ((genSemGen Q X g).body i bools bits)
    lsrcAt g.d (extBOf Q g i bools bits Sst) (extOf Q g i bools bits Sst) Sst =
      (SemPkg.gen (genSemGen Q X g)).lsrc i bools bits
```
(`Sst` is the stream written `S*` in rev3 §2.3; a `let` inside the statement.) P4c. Claimed `rfl` after unfolding `SrcSem.lsrc`/`letObsB` (`Tools/ShippingMachineCausal.lean`); **this has not been checked against `letObsB`'s exact text** — if the observation term differs from `lsrcAt`'s (e.g. an `obsR`-composition), the unit states the equality it can prove and the difference is reported, not hidden.

```lean
theorem memFacts_of_genSem (Q) (X : Name) (g : GenIn) (hok : g.d.ok = true) (i : ι) (bools) (bits)
    (k : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder) (hk : g.d.shape.insts[k]? = some (c, a, κ))
    (cb : Bool) (aw dw : Nat) (ho : originOf g.d k = .mem cb aw dw) :
    let Sst := @stateLoop _ _ _ ⟨g.inits⟩ g.inits ((genSemGen Q X g).body i bools bits)
    Tools.ShippingMachineCallsLinkedT.MemFacts (D := dom i) g.d.shape
      ((SemPkg.gen (genSemGen Q X g)).lsrc i bools bits) g.d.ls.length (g.d.bsIn.drop (kDOf g.d)) (kDOf g.d)
      (extOf Q g i bools bits Sst) k c
```
`GenWF g.d = true` is `g.wf`. The same `Sst` is used for the stage families and for the observation list (R1 of the rev3 review, "one state stream"). Proof plan: `MemFacts`'s witnesses from §rev2 1.5: `cb aw dw` from `ho`; `A := ⟨fun j => BitVec.ofNat aw (lsrc l0 j)⟩`, … with `l0..l3` from RowA's A4 (`callArgs` is a 4-list); range facts `enc_lt` (`letObsB_hl`) with B3's sorts, `BitVec.toNat_ofNat`+`Nat.mod_eq_of_lt`;
`bsI[k]?` from B2; the last conjunct is `ext_mem_final`. **B3 is the sufficient condition of this construction** (rev3 §3.1), not a derived necessity of `MemFacts`.

## 6. Supplier table (what supplies each premise; "not found" = this study found no supplier on this route, not "impossible")

| premise / obligation | supplier | status | used by |
|---|---|---|---|
| `GenIn` (`ok/bodyEq/init/inits`) | DG-DATAOF `dataOf_sound` via `GenData.toIn` | open (dep. issue `doing`); a premise | `genSemVia`, anything over a real run; **not** U4A–U4D |
| `GenIn.wf : GenWF d = true` coverage on real runs | DG-WFCOVER | open, unsupplied | U4F (as `g.wf`), P6 |
| `d.ok` ⇒ `LetsTyped` / `Term.WF` of each `let` | existing `MachineData.ok` and `LetsTyped` (`Tools/ShippingMachineAuto.lean`, `ShippingMachineDenote.lean`) | existing definitions; whether `d.ok` alone suffices is checked at U4E | U4E |
| `eval_congr_wf`, `letVal`, `reads`, `typedVal` | existing (`Tools/ShippingMachineDenote.lean`, `ShippingMachineRef.lean`) | supplied | U4E |
| `memRead` and its causality | existing `Tools/ShippingMachineMemLinked.lean:33`; **causality lemma location not found** | `memRead` supplied; causality lemma open | U4F only through the definition; **P6' needs the causality lemma** |
| `MemFacts`, `valsOf`, `boolsOf/bitsOf` | existing (`CallsLinkedT`, `SeqChild`) | supplied | U4A, U4F |
| `enc_lt`, `letObsB_hl`, `BitVec.toNat_ofNat` | existing (`QuadCalls` etc.; `Init`) | supplied (names re-checked at U4F start) | U4F |
| `S1` `Q c = some q` at every ordinary call (strictness) | `genS` (DG-ACC) | open | none of U4A–U4F (D1b is a total default) |
| `S2` `CallField` | T2-FIELD | open (other issue) | none (D2 default) |
| `S3` `CallOutRange` (`houtTy`, `CallOutWidthAt`) | T2-OUTTY (later, conditional), G-ONEOUT-WID | **unsupplied intermediate** | P4e only (not in this document) |
| Callee output-name `Nodup` for `selIdx` | callee `Pkg.ok` | open as a premise of P4e | P4e only |
| `GenFacts.causal` (`HCausalOf`) | P6' | **not designed here** | P11 |

Nothing in this document supplies any of these; none is counted as supplied by U4A–U4F.

## 7. Audit plan (after approval, per unit; the same shape as U3's `SemGenCheck` after the closure-audit fix)

For each new check file (`Tests/Gen5/SemCallCheck.lean`, etc.):
- **TYPE** (`checkExpected`, isDefEq): each theorem of §3–§5 against an independently written `Expected…` statement (accessor/unfolded forms, not the definitions under test).
- **MUTANT** (`checkMutant`) — signature/defeq rejections of a well-typed one-place change, **not** semantic counterexamples. Planned (≥1 per unit): U4B: `genSemI_local` with the hypothesis ranging over *all* entries instead of `ordCallees` (a stronger premise, a different type), and with `ordCallees g.d` replaced by `[]` (a vacuous premise, a different type); `callOut_local` without the `child? = none` premise; U4C: `callOut_frame` with `p ≤ kD + k`, `ExtStage_agree` with `p < kD + n + 1`, `callOut_none` with `st` replaced by `(bools, bits)`; U4D: `callOut_mem_val` at `kDOf g.d + k + 1`, or returning the stage-`k+1` families; U4E: drop the `cleanLets` premise, read `t + 1`; U4F: `ext_mem_final` with the stage-`k` families on the right side (the stage mismatch), `memFacts_of_genSem` with the observation list at a different state stream than `Sst`.
- **AXIOMS** (`Lean.collectAxioms`, standard only) for every theorem and definition of the units.
- **CLOSURE** with the *explicit* `thmInfo/defnInfo/opaqueInfo` walk of `Tests/Gen5/SemGenCheck.lean` (`closureOf`/`closureRun`, see `DG_SEM_FREEZE_REV3.md` §6; unresolved names are failures, opaque and body-less kinds are logged), the same forbidden list (`sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, `Lean.reduceBool`, `Lean.reduceNat`), with its **negative and clean controls** re-asserted in each check file that uses the detector (or moved to a shared test helper — reported if so).
- **REACH** (the freeze's stated dependencies are actually reached from the proofs' bodies): `callOut_local` reaches `calleeOut`; `genSemI_local` reaches `ExtStage_local`; `ExtStage_agree` reaches `callOut_frame`; `ext_mem_final` reaches `callOut_mem_val`, `ExtStage_agree`, `lsrcAt_congr`; `memFacts_of_genSem` reaches `ext_mem_final`.
- Builds: Pod `kjob lake build Tests.Gen5.<Check>` one at a time; **the clean focused build is the coder's**; built SHA in the header by a comment-only commit.

## 8. Roadmap items not frozen here
P5 (`genFacts_comb`, the `hnext` conjunct of `CombFacts`), P6' (`GenFacts.causal`; the `memRead` causality lemma is **not located**), P4e (`genExtAtCall_of_genSem` under S1–S3), P11 (`genFacts_gen`, `genFacts`, `genSemI_srcCausal`, `trace_of_genSem`), P12 (`GenData.toIn` consumer, `genSem`, `GeneratedAt`, `genS_some_inv_of_unfold`) —
each will be re-frozen with a complete telescope before implementation. Ownership (rev2 §7, unchanged): `genS`/`genS_unfold`/`Acc` are DG-ACC's; `genSemI_local` is stated and proved here and consumed by DG-ACC; `GenIn.wf` coverage is DG-WFCOVER's.

## 9. Not claimed
- Nothing in this document is elaborated; every definition is a proposal whose elaboration (instances, coercions, `InstOrigin` constructor patterns, the `Option`-equality decidability in `ordCallees`, the exact form of `letObsB`) is checked when implemented and reported where it differs.
- No supplier is claimed for `GenIn`, `GenWF` coverage, `S1`–`S3`, `houtTy`, `CallOutWidthAt`, callee causality, `Acc`, `GenExtAtCall`/`HPointG`.
- MUTANT results are signature/defeq rejections, not semantic counterexamples. The closure audit is a constant-reference walk (kernel terms, current environment), not a semantic or compiled-code audit; the axiom audit is separate.
- No FG/M5 completion; no change to FG, a shared definition, the compiler, or any law; no coverage narrowing, no `GenWF` strengthening.

## 10. Implementation addendum (g5sm-u4)
`typedVal_let_congr` (§5.2) was not provable as stated (its off-sort conjunct is not implied by `hb`/`hv`); see `scripts/gen5/DG_SEM_FREEZE_P4_U4E_ADDENDUM.md`. All other statements of §3–§5 are implemented as frozen (U4A–U4F); `lsrcAt_congr` is proved with the frozen statement via the internal sort-aware `typedVal_let_agree`.

## 11. Sync after the U4A-F scoped approval (g5sm-u5; 1258f07e, clean build smu4v-1258f07e exit 0, 709 jobs)
- **§5.2 U4E amendment (approved by the reviewer, no re-freeze):** `typedVal_let_congr` is removed from the required deliverables. The sort-aware `typedVal_let_agree` (`Tools/ShippingGen5SemCongr.lean`) is adopted as an *internal* lemma. The frozen types of `lsrcAt_congr`, `ext_mem_final`, `memFacts_of_genSem` are unchanged, so no existing consumer changes. Limit kept as is: a formal refutation of the old `typedVal_let_congr` statement has **not** been presented (the addendum is a reading-of-the-definitions argument; no concrete counterexample was constructed or machine-checked).
- **Audit limits (SemCallCheck at 1258f07e):** the 15 definition checks compare *signatures only*; definition bodies were compared by the reviewer's read-through, not mechanically. The `unknown`-name negative control covers the *root* only (no helper-value / helper-type unknown).
- **Audit improvement for units after U4:** a new Check also compares definition *bodies* against an independently written Expected, and uses three unknown-name negatives (root / helper value / helper type) plus a clean control. See §12 `Check`.

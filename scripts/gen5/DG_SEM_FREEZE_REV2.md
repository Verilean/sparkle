# DG-SEM freeze rev2 — RowA/B/C, MemFacts rows, staged call order, `SemPkg` and the remaining types, defaults vs. success conditions, ownership

**FOR REVIEW — design.** Answers the `changes_requested` on rev1 (`5b0a5eed`, `scripts/gen5/DG_SEM_FREEZE.md`) items R1–R3.
Rev1 stays as written; **rev2 replaces rev1 §2.1 (GenWF), §2.2 (SemPkg), §2.3 (reference body), §2.4 (ext/extB), §4 (supplier
table) and §5 (pure-lemma units)**; rev1 §0, §1 (`GenIn`), §2.5 (no `.loop` arm), §3 (connection to `Pkg.trace`) and §7/§8 stay in
force except where this file says otherwise. Base `par/gen3-combined` 9d26005c; `[S]` = read in this worktree; `[R]` =
`Tools/ShippingGen5T2Range.lean` at `par/gen5-t2` e57eb431 (comment sync 314c2119), i.e. also present in this worktree.

**Implemented and built in this issue (commit d5492921, Pod build `kjob lake build` exit 0 for `Tools.ShippingGen5SemRef`,
`Tools.ShippingGen5SemPkg`, `Tests.Gen5.SemUnitsCheck`):** the Lean text for P1, P2 and `SemPkg`/`Pkg.toSem`/`genPkg` below is
the *built* text (cited as `[B]`); everything else is a PROPOSAL, not elaborated. No `sorry`/`axiom`/`native_decide`; no new
TRUSTED boundary, law, FG/guarantee change, shared-definition or compiler edit. The clean build (evidence build) is the coder's.

## 0. Revision log (what is new relative to rev1)

| id | rev1 gap | rev2 |
|---|---|---|
| R1 | RowA/B/C undefined; `MemFacts` needs exactly 4 args, aw/dw/bool/aw observation equalities and ranges, not derivable from "index range + result bits dw" | §1: RowA/B/C defined as decidable `Bool`s; **explicit revision rows REV-1…REV-4** added for the memory entry (§1.4); table §1.5 maps every `MemFacts` conjunct to its source; supply rows for `ok`/`wf` in §1.6 |
| R2 | RowC ignored an argument `let` reaching a call result through other `let`s; no `reads`/`typedVal`-faithful form; no stage-preservation type | §2: `cleanLets` (a left fold in `typedVal`'s own `let` order), RowC, `typedVal_let_congr` (P4a), `ExtStage`, `callOut` equations |
| R3 | `SemPkg` fields, `ExtStage`, `callOut`, `refBody`, `FactsOf`, P3+ elided / unbound arguments; no defaults separated from success conditions | §3 `[B]` types; §4 `refBody`/`genSemGen`; §5 `callOut` with defaults (D1–D6) separate from success conditions (S1–S4); §6 every P-unit with a full statement |
| own. | `genS` overlap with DG-ACC | §7 |
| range | stale | §5.3 synced to `Tools/ShippingGen5T2Range.lean` `[R]` |

## 1. `GenWF`: RowA / RowB / RowC (R1)

`namespace Tools.ShippingGen5Sem`, `d : MachineData`, `n d := d.shape.insts.length`. Helpers (all total, over `MachineData`):
```lean
def kDOf (d : MachineData) : Nat := d.nIn - d.shape.insts.length
def callArgs (d : MachineData) (k : Nat) : List Nat := ((d.shape.insts.map (·.2.1))[k]?).getD []      -- as MemFacts reads it
def callKind (d : MachineData) (k : Nat) : MixedGateBinder := (((d.bsIn.drop (kDOf d))[k]?).map (·.2)).getD .domain   -- as CallFactF / CallOutRange [R]
def letSort (d : MachineData) (l : Nat) : Option SType := (d.ls[l]?).map (·.1)
def originOf (d : MachineData) (k : Nat) : InstOrigin := d.shape.instOrigins.getD k .ord             -- as MemFacts reads it
```

### 1.1 RowA — arities and index ranges
```lean
def RowA (d : MachineData) : Bool :=
  decide (d.shape.insts.length ≤ d.nIn) &&                                          -- A1  kDOf is the true declared count
  decide (d.shape.instOrigins.length = d.shape.insts.length) &&                    -- A2  an origin per entry (no `getD` default is ever taken)
  (List.range d.shape.insts.length).all fun k =>
    (callArgs d k).all (· < d.ls.length) &&                                        -- A3  every argument is a `let` index
    (match originOf d k with
     | .mem _ _ _ => decide ((callArgs d k).length = 4)                            -- A4  REV-1: a memory entry has EXACTLY 4 arguments
     | _ => true)
```
`A1` is what makes `d.nIn = kDOf d + insts.length`. `A2`/`A3` are the "index range" of rev1; `A4` is the arity `MemFacts` needs
(`insts.map (·.2.1))[k]? = some [l0,l1,l2,l3]`).

### 1.2 RowB — kinds, including the memory observation sorts
```lean
def RowB (d : MachineData) : Bool :=
  (List.range d.shape.insts.length).all fun k =>
    (match callKind d k with | .domain => false | _ => true) &&                    -- B1  the binder of call k has a Bool/BitVec sort (sortOf defined)
    (match originOf d k, callArgs d k with
     | .mem _ aw dw, [l0, l1, l2, l3] =>
         decide (callKind d k = .bits dw) &&                                       -- B2  REV-2: the result binder is .bits dw (MemFacts: bsI[k] = .bits dw)
         decide (letSort d l0 = some (.bits aw)) && decide (letSort d l1 = some (.bits dw)) &&   -- B3  REV-3: A : aw, Dd : dw
         decide (letSort d l2 = some .bool) && decide (letSort d l3 = some (.bits aw))            --      E : Bool, R : aw
     | .mem _ _ _, _ => false                                                      -- (excluded by A4; kept so the Bool is total)
     | _, _ => true)
```
Ordinary and `.field` entries get **no** callee-dependent row here: whether the callee's output fits the binder is the range /
width hypothesis (`CallOutRange`, `CallOutWidthAt`, §5.3), which concerns the callee and is not a property of `d`.

### 1.3 RowC — call order, through `let`s (R2)
Position layout (`ok` + `typedVal`, `MachineDenote.lean:459`): declared inputs `p < kD`; call `k` is at `kD + k`; slot `i` at
`d.nIn + i`; `let q` at `d.nIn + d.ss.length + q`. `reads okB okV t` ([S] `MachineRef.lean:31`) tests which **term input
indices** `j` a term uses; the position read is `d.bpos j` / `d.vpos j`. A `let` is *clean at stage `k`* when every position it
reads is a declared input, a call result `< kD + k`, a state slot, or an **earlier `let` that is itself clean at stage `k`**
— this is the transitive case (an argument `let` that reaches a call result through another `let`):
```lean
/-- `clean[q]` = whether `let q'<q` (the accumulated list) are clean; position `p` allowed at stage `k`. -/
def posOk (d : MachineData) (k : Nat) (clean : List Bool) (p : Nat) : Bool :=
  decide (p < kDOf d + k) ||                                                       -- declared inputs and call results of calls < k
  (decide (d.nIn ≤ p) && decide (p < d.nIn + d.ss.length)) ||                      -- state slots (same value at every stage)
  (decide (d.nIn + d.ss.length ≤ p) && clean.getD (p - (d.nIn + d.ss.length)) false)   -- an EARLIER clean let; later/self/missing => false

/-- Left fold in `letVal`'s order (letVal evaluates `l :: ls` in sequence, each under the valuation so far). -/
def cleanLets (d : MachineData) (k : Nat) : List Bool :=
  d.ls.foldl (fun clean l =>
    clean ++ [reads (fun j => posOk d k clean (d.bpos j)) (fun j => posOk d k clean (d.vpos j)) l.2]) []

def RowC (d : MachineData) : Bool :=
  (List.range d.shape.insts.length).all fun k => (callArgs d k).all fun l => (cleanLets d k)[l]? == some true
```
`cleanLets d k` has length `d.ls.length` (P4-len). RowC covers memory entries too (their four arguments are `callArgs d k`).
Call results `≥ kD + k` (and so `kD + k` itself) are never allowed, so an argument cannot read its own result or a later call.

### 1.4 `GenWF`
```lean
def GenWF (d : MachineData) : Bool := RowA d && RowB d && RowC d
def GenWFP (d : MachineData) : Prop := RowA d = true ∧ RowB d = true ∧ RowC d = true
theorem genWF_iff (d) : GenWF d = true ↔ GenWFP d
```
**Explicit revision rows (rev2 vs rev1): REV-1 = A4, REV-2 = B2, REV-3 = B3, REV-4 = A2 (origins/entries length) and A1.**
Rev1 had "arities, kinds, order" without text; these are the rows the text of `MemFacts` forces (§1.5). They are *rows of the
`GenWF` introduced by this unit* (rev1 §2.1: "`GenWF` defined here"), not a strengthening of an accepted definition elsewhere; but
the reviewer should note this is the first time the rows have text, and the coverage of every one of them on real runs is
**DG-WFCOVER's**, not DG-DATAOF's and not this unit's (§1.6). If the reviewer holds that adding REV-1…REV-4 is a `GenWF`
strengthening in the sense of the prohibition, this unit stops and writes a decision document instead (rev1 §7).

### 1.5 `MemFacts` conjunct ↔ source (the check the reviewer asked for)
`MemFacts shape lsrc nL bsI kD ext k c` ([S] `ShippingMachineCallsLinkedT.lean:31`), at `shape := d.shape`, `lsrc := lsrc`
(`letObsB`), `nL := d.ls.length`, `bsI := d.bsIn.drop kD`, `kD := kDOf d`:

| conjunct | source |
|---|---|
| `∃ cb aw dw`, `(instOrigins.getD k .ord).child? = some (memModule cb aw dw)` | `originOf d k = .mem cb aw dw` (the case split of `callOut`); `child?` of `.mem` is `rfl` |
| `(insts.map (·.2.1))[k]? = some [l0,l1,l2,l3]` | A4 (+ `k < n`) |
| `l0..l3 < nL` and `lsrc[l_i]? = some …` | A3 and `List.length_map` of `letObsB` (`lsrc.length = d.ls.length`) |
| `lsrc[l0]? = some (fun j => (A.val j).toNat)` with `A : Signal D (BitVec aw)` | B3 `letSort l0 = .bits aw`, `A := ⟨fun j => BitVec.ofNat aw (lsrc l0 j)⟩`, range `lsrc l0 j < 2^aw` from `enc_lt` (`letObsB_hl`, [S] QuadCalls), `BitVec.toNat_ofNat`+`Nat.mod_eq_of_lt` |
| `lsrc[l1]?` (`Dd : BitVec dw`) | B3 `.bits dw`, as above |
| `lsrc[l2]? = some (fun j => if E.val j then 1 else 0)` | B3 `.bool`, `E := ⟨fun j => lsrc l2 j != 0⟩`, `encodeBool_bne_of_lt` (T2Tie) from `enc .bool < 2` |
| `lsrc[l3]?` (`R : BitVec aw`) | B3 `.bits aw` |
| `bsI[k]?.map (·.2) = some (.bits dw)` | B2 (`(d.bsIn.drop kD)[k]` is `callKind`'s definition) |
| `∀ j, (ext (kD+k) dw).val j = (memRead cb A Dd E R).val j` | **by construction** of `callOut`'s memory branch **plus P4a** (the arguments are read at stage `k`, `MemFacts` is stated at the final `lsrc`; RowC makes them agree) |

Without A4, B2, B3 the first conjunct that fails is the 4-list / the sort equation, so they are necessary rows, not conveniences.
The rev1 "RowA index range" (A3) and "RowB result bits dw" (B2) alone do not give lines 2, 4–8.

### 1.6 Supply rows for `ok` and `GenWF` (who provides each premise of `GenIn`)
| premise | supplier | status |
|---|---|---|
| `GenIn.ok` (`d.ok = true`), `bodyEq`, `init`, `inits` | DG-DATAOF `dataOf_sound` via `GenData.toIn` (rev1 §1) | **open**; premise of every class-D unit |
| `GenIn.wf` : `GenWF d = true` = A1–A4, B1–B3, RowC | **DG-WFCOVER** (coverage on real runs: each row must be shown for the `d` that `dataOf` returns for a successful source). *This study found no supplier for A4/B2/B3/RowC on this route in the tree at 9d26005c; that is "not found", not "impossible".* | **open, unsupplied** |
| callee `Q c = some q` at every ordinary call | `genS` strictness (DG-ACC/DG-SEM, §7) | open |
| callee output range / width | `[R]` (§5.3) | partly supplied, conditional |
Nothing in this file supplies any of these; no new unsupplied assumption is counted as supplied.

## 2. Stage preservation (P4a) and the staged families (R2)

### 2.1 `typedVal` faithful preservation (P4a — pure, class I)
`typedVal kIn bpos vpos ss ls bools bits t x = letVal bpos vpos ls (kIn + ss.length) (slotVal … ⟨fun p => (bools p).val t, fun p w => (bits p w).val t⟩)`
(`MachineDenote.lean:459`). Statement (`d.ok = true` supplies `LetsTyped`, hence `Term.WF` of each `let`):
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
```
Proof plan: induction over `ls` with the accumulated valuation (generalised over the accumulator `clean`/position prefix), using
`eval_congr_wf` ([S] Ref:201) with `okB j := posOk … (bpos j)` and `hb/hv` for `p < kD+k`, the slot positions (`x` is the same) and
the induction hypothesis for earlier clean `let`s. Corollary (P4b), the observation form:
```lean
theorem lsrcAt_congr … : (cleanLets d k)[l]? = some true → lsrcAt d bools bits S l t = lsrcAt d bools' bits' S l t   -- same hypotheses
```
with `lsrcAt d bs vs S : List (Nat → Nat) := d.ls.map fun l t => enc l.1 (eval (fun j => (typedVal … bs vs t (S.val t)).b (d.bpos j)) (fun j w => (…).v (d.vpos j) w) l.2)`
— the *same term* as `letObsB`'s body ([S] `Tools/ShippingMachineSeqLinked.lean:217`), so `lsrcAt d (extBOf …) (extOf …) (stateLoop …) = (genSemGen …).lsrc i bools bits` is `rfl` up to the `stateLoop` argument (P4c).
Note `cleanLets` is *not* "reads only positions `< kD+k`": a `let` may read an earlier `let`, which reads an earlier call result; this
is handled by the clean-list recursion, which is the transitive closure demanded by R2.

### 2.2 Staged families
```lean
/-- Stage n: calls k < n filled in; every other position is the input `bools/bits`. -/
noncomputable def ExtStage (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) :
    Nat → (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))
  | 0 => (bools, bits)
  | n + 1 => callOut Q g i S n (ExtStage Q g i bools bits S n)          -- §5; returns the stage n+1 pair
noncomputable def extBOf Q g i bools bits S := (ExtStage Q g i bools bits S g.d.shape.insts.length).1
noncomputable def extOf  Q g i bools bits S := (ExtStage Q g i bools bits S g.d.shape.insts.length).2
```
`callOut Q g i S k (bs, vs) : (Nat → Signal Bool) × ((j n) → Signal (BitVec n))` changes **only** position `kD + k` (Bool family if
`callKind = .bool`, BitVec family if `.bits _`, unchanged for `.domain`). So stage `n` and stage `m ≥ n` agree on every position
`< kDOf g.d + n` (P4d, by induction on `m - n`), the hypothesis shape of `typedVal_let_congr` with `k := n`.

## 3. `SemPkg` and relatives `[B]` (R3: fields, no omissions)
Built text in `Tools/ShippingGen5SemPkg.lean` (namespace `Tools.ShippingGen5Sem`):
- `SrcSem ι dom` = `SrcPkg` without `gen`: `decl d kD ρ inh inits body obsR ext extB src`, same order and types.
- `CombSem ι dom` = `CombPkg` without `facts`: `decl d kD inits src`.
- `LoopSem ι dom` = `SrcPkgL` without `facts`: `decl d kD α inh ρ σ inits f res obsR ext extB src` (never produced by `genSem`, rev1 §2.5).
- `inductive SemPkg | gen (s : SrcSem) | loop (s : LoopSem) | comb (s : CombSem)` (order of `Pkg`).
- Accessors by cases: `SemPkg.decl/.d/.kD/.src/.ports/.S/.extS/.extBS/.lsrc`; per arm `SrcSem.extS/extBS/lsrc` (same terms as `SrcPkg`'s: `stateLoop`, `letObsB`),
  `LoopSem.extS/extBS/lsrc` (`Signal.loop`, `letObsLoop`), `CombSem.extS/extBS/lsrc` (identity, `letObsComb`).
- `FactsOf : SemPkg ι dom → Prop` — `.gen s ↦ @GenFacts s.d ι dom s.ρ s.inh s.inits s.body s.obsR s.ext s.extB s.src`,
  `.loop s ↦ @LoopFacts s.d ι dom s.α s.inh s.ρ s.σ s.inits s.f s.res s.obsR s.ext s.extB s.src`, `.comb s ↦ CombFacts s.d dom s.inits s.src`.
- `Pkg.toSem` (declared as `Tools.ShippingGen2.Pkg.toSem`), `genPkg : (s : SemPkg ι dom) → FactsOf s → Pkg ι dom`,
  `semOf (P : Name → Option (Pkg ι dom)) : Name → Option (SemPkg ι dom)`, `Pkg.factsOf_toSem : ∀ p, FactsOf p.toSem`.
- Theorems `[B]`: `toSem_genPkg`, `pkg_eq_of_toSem` (injective), and the agreement lemmas `decl/d/kD/src/extS/extBS/lsrc/S` for
  `toSem` and for `genPkg` (all `by cases; rfl`). `#print axioms`: standard only; the Check file compares P1, P2, `toSem_genPkg`,
  `pkg_eq_of_toSem`, `extS_genPkg` with independently written statements and rejects 5 mutants (signature/defeq rejections, **not**
  semantic counterexamples).
- P1/P2 `[B]` (`Tools/ShippingGen5SemRef.lean`, any slot list `αs`, any `dom : DomainConfig`):
  `sigListOfFn αs f`, `valsAt_sigListOfFn : valsAt αs (sigListOfFn αs f) t = f t`,
  `reconState αs ws := ⟨fun t => valsAt αs ws t⟩`, `valsAt_mkHolds : valsAt αs (mkHolds αs S) t = S.val t`,
  `reconState_mkHolds : reconState αs (mkHolds αs S) = S`.

## 4. The `.gen` arm over `GenIn`, with every argument bound
`variable {ι : Type} {dom : ι → DomainConfig} (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)`. `d := g.d`.
```lean
/-- the typed valuation of a cycle under the final families -/
noncomputable def valAt (i) (bools) (bits) (S : Signal (dom i) (HList (tys g.d.ss))) (t : Nat) : TVal :=
  typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (extBOf Q g i bools bits S) (extOf Q g i bools bits S) t (S.val t)
noncomputable def nextFn  (i) (bools) (bits) (S) (t : Nat) : HList (tys g.d.ss) :=
  evalTerms (fun j => (valAt Q g i bools bits S t).b (g.d.bpos j)) (fun j w => (valAt Q g i bools bits S t).v (g.d.vpos j) w) g.d.nexts
noncomputable def resultFn (i) (bools) (bits) (S) : List (Nat → Nat) :=
  g.d.outs.map fun o t => enc o.1 (eval (fun j => (valAt Q g i bools bits S t).b (g.d.bpos j))
                                         (fun j w => (valAt Q g i bools bits S t).v (g.d.vpos j) w) o.2)

/-- `ρ i := List (Nat → Nat)`, `obsR := fun _ r => r`.  The state is rebuilt from `holds` (P2). -/
noncomputable def refBody (i) (bools) (bits) :
    RegList (dom i) (HList (tys g.d.ss)) (Circuit.SigList (dom i) (tys g.d.ss)) (tys g.d.ss) →
    Circuit (dom i) (Circuit.SigList (dom i) (tys g.d.ss)) (List (Nat → Nat)) :=
  fun _regs holds =>
    let S := reconState (tys g.d.ss) holds
    (resultFn Q g i bools bits S, sigListOfFn (tys g.d.ss) (nextFn Q g i bools bits S))

noncomputable def genSemGen : SrcSem ι dom :=
  { decl := X, d := g.d, kD := kDOf g.d, ρ := fun _ => List (Nat → Nat), inh := ⟨g.inits⟩, inits := g.inits,
    body := refBody Q g, obsR := fun _ r => r, ext := extOf Q g, extB := extBOf Q g,
    src := fun i bools bits =>
      (refBody Q g i bools bits (mkRegList (@stateLoop _ _ _ ⟨g.inits⟩ g.inits (refBody Q g i bools bits)) (tys g.d.ss) (fun s => s) (fun f => f))
        (mkHolds (tys g.d.ss) (@stateLoop _ _ _ ⟨g.inits⟩ g.inits (refBody Q g i bools bits)))).fst }
```
(`stateLoop` has the instance argument written as `⟨g.inits⟩`; in the file it is a `letI`.) `GenFacts.source` is then `Eq.refl`;
`writes` is `valsAt_sigListOfFn` + `reconState_mkHolds` + `rfl` (P3); `result` is `List.map_map` + `rfl` (P3). `ok/body_eq/init := g.ok/g.bodyEq/g.init`.

`.comb` arm (`g.d.ss = [] ∧ g.d.shape.insts = []`): `genSemComb X g : CombSem := ⟨X, g.d, kDOf g.d, g.inits, srcComb⟩` with
`srcComb i bools bits := g.d.outs.map fun o t => enc o.1 (eval (fun j => (typedVal … bools bits t g.inits).b (g.d.bpos j)) (fun j w => (…).v (g.d.vpos j) w) o.2)`
(the right side of `CombFacts.hres`, so `hres` is `List.map_map`; `hnext` from `g.d.ss = []`, `HList [] = Unit`, P5).
`genSemI Q X g := if g.d.ss = [] ∧ g.d.shape.insts = [] then .comb (genSemComb X g) else .gen (genSemGen Q X g)` (`Classical.propDecidable`
is not needed: both conjuncts are decidable, `List` equality over `SType`/`Name × …` entries needs `DecidableEq`; to avoid
instances use `g.d.ss.isEmpty && g.d.shape.insts.isEmpty` — a Bool test; chosen).

## 5. `callOut`: definition, defaults (D) and success conditions (S) (R3)
### 5.1 Definition
For call `k`, stage pair `(bs, vs)`, state `S`:
```lean
def argVals (i) (S) (bs vs) (k : Nat) : Nat → List Nat := valsOf (lsrcAt g.d bs vs S) (callArgs g.d k)       -- stage-k observations of the arguments

/-- ordinary / field entry: the selected output stream of the callee, or the zero stream. D1, D2 -/
noncomputable def calleeOut (i) (S) (bs vs) (k : Nat) : Nat → Nat :=
  match Q (g.d.shape.insts[k]?.map (·.1)).getD .anonymous with        -- D1: `Q c = none` or `k ≥ n`  ⇒ zero stream
  | none => fun _ => 0
  | some q =>
    let A := boolsOf (D := dom i) (q.d.bsIn.take q.kD) (argVals … k)
    let B := bitsOf  (D := dom i) (q.d.bsIn.take q.kD) (argVals … k)
    match selIdx g.d q k with                                                -- D2: no such output ⇒ zero stream
    | none => fun _ => 0
    | some k' => ((q.src i A B)[k']?).getD (fun _ => 0)                      -- D2 (list shorter than the layout)
def selIdx (d : MachineData) (q : SemPkg ι dom) (k : Nat) : Option Nat :=
  if d.shape.instFields = [] then (if q.d.shape.layout.outs.length = 1 then some 0 else none)      -- CallField: `outs = [o]`
  else q.d.shape.layout.outs.findIdx? (·.name = d.shape.instFields.getD k "")                    -- CallField: `o.name = instFields.getD k ""`
```
(`selIdx` implements `CallField p q k o` ([S] Defs:94) as an index; for the second branch the *first* match is taken, which is *the*
match by `callField_unique_of_ok` `[R]` from `q.d.ok`'s `outs`-name `Nodup`.)
Decode by the binder kind (the `SigAt` convention `[R]`/T2Tie:47):
```lean
def withCall (k) (κ : MixedGateBinder) (f : Nat → Nat) (bs vs) : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)) :=
  match κ with
  | .bool    => (fun p => if p = kDOf g.d + k then ⟨fun τ => f τ != 0⟩ else bs p, vs)
  | .bits _  => (bs, fun p n => if p = kDOf g.d + k then ⟨fun τ => BitVec.ofNat n (f τ)⟩ else vs p n)    -- D3: truncating `ofNat`
  | .domain  => (bs, vs)
```
Memory entry (`originOf g.d k = .mem cb aw dw`, `callArgs g.d k = [l0,l1,l2,l3]`):
```lean
noncomputable def memOut (cb aw dw l0 l1 l2 l3) (i) (S) (bs vs) : Signal (dom i) (BitVec dw) :=
  memRead cb ⟨fun j => BitVec.ofNat aw (lsrcAt … l0 j)⟩ ⟨fun j => BitVec.ofNat dw (lsrcAt … l1 j)⟩ ⟨fun j => lsrcAt … l2 j != 0⟩ ⟨fun j => BitVec.ofNat aw (lsrcAt … l3 j)⟩
```
with the position `kD + k` receiving `memOut` at width `n = dw` and the zero `BitVec` otherwise (a `cast`-free form: the family
at `p = kD+k` is `if h : n = dw then h ▸ memOut else 0`; the `MemFacts` conjunct is at `n = dw`).
`callOut Q g i S k (bs, vs)` := match `originOf g.d k` with `.mem cb aw dw` ⇒ (`match callArgs g.d k with [l0,l1,l2,l3] ⇒ mem family | _ ⇒ zero family (D4)`), `.ord | .field _` ⇒ `withCall k (callKind g.d k) (calleeOut …) bs vs`. `callArgs` of a
`.ord` call that is out of range (`l ≥ d.ls.length`): `valsOf` returns `0` there (`getD 0`, [S] `valsOf`), D5.

### 5.2 Defaults vs success conditions (separated, R3)
| code | situation | value (**default, total**) | holds when (**success condition**; not assumed by `genSem`) |
|---|---|---|---|
| D1 | callee absent (`Q c = none`) or `k ≥ insts.length` | zero stream | S1: `Q c = some q`; true for every ordinary callee of a `genS` entry (strictness, §7) |
| D2 | no selected output (`selIdx = none`) or `src` list too short | zero stream | S2: `CallField p q k o` for some `layout.outs[k'] = o` — T2-FIELD (other issue) |
| D3 | callee value `f τ ≥ 2^w` (width mismatch) | `ofNat` truncation / `f τ != 0` (Bool) | S3: `CallOutRange p q k hk` (§5.3) ⇒ `SigAt … f` |
| D4 | memory entry whose `callArgs` is not a 4-list, or a `.domain` kind | zero family / position unchanged | S4: A4, B2, B3 (⇒ `MemFacts`, §1.5) |
| D5 | argument `let` index `≥ d.ls.length` | observation `0` (`valsOf`) | A3 |
| D6 | `instOrigins` shorter than `insts` | `getD k .ord`: treated as ordinary | A2 |
`CallOut`/`GenExtAtCall`/`MemFacts` are theorems **under** S1–S4 and `GenWF`, never the *definition*; the definition is total so
`genSemGen` exists for every `GenIn` (including the dead branches), and its `none` branches are unreachable from `genS`.

### 5.3 Range, synced with the latest T2 result `[R]` (`Tools/ShippingGen5T2Range.lean`, built g5tr2-e57eb431)
Used as-is, nothing re-proved or strengthened:
- `Pkg.src_range q : q.d.shape.layout.outs[k']? = some o → (q.src i bools bits)[k']? = some f → ∀ τ, f τ < 2 ^ o.width` — **unconditional, all three arms**.
- `callOutRange_of_widths p q k hk (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width) (hW : CallOutWidthAt p q k) : CallOutRange p q k hk` — **conditional** on `houtTy` and `CallOutWidthAt`; `houtTy` has no current supplier (`[R]` header: "`T1Hyp`'s `DataOk` is an abstract parameter"); `CallOutWidthAt` is G-ONEOUT-WID / `hkidW`.
- Hence S3 is the T2-TIE hypothesis `hDG_SEM_range : CallOutRange p q k hk` and stays an **UNSUPPLIED intermediate**. `genSemI`'s definition and `GenFacts` do not use it (D3 is total); only P4e `genExtAtCall_of_genSem` (the `SigAt` form) uses S3.
- `GenExtAtCall p q k hk` ([S] `T2Tie.lean:237`) is the statement P4e proves for `p := genPkg (genSemI Q X g) _`, `q` with `q.toSem = the callee in Q`: the
  `SigAt (p.extBS …) (p.extS …) (p.kD + k) κ f` conclusion is exactly `withCall`'s definition (Bool `!= 0`, BitVec `ofNat w`) read at the final stage plus P4a/P4d.

## 6. Pure-lemma units with full statements (P3 onward, nothing elided)
All over `(Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)`, `ι dom` implicit. "I" = no `dataOf`; "D" = needs DG-DATAOF output.

| id | statement (Lean text, proposal) | class |
|---|---|---|
| P1 `[B]` | `valsAt_sigListOfFn` (§3) | I |
| P2 `[B]` | `valsAt_mkHolds`, `reconState_mkHolds` (§3) | I |
| P3 | `theorem genSemGen_writes : ∀ i bools bits S t, valsAt (tys g.d.ss) (refBody Q g i bools bits (mkRegList S (tys g.d.ss) (fun s => s) (fun f => f)) (mkHolds (tys g.d.ss) S)).snd t = evalTerms (fun j => (typedVal … (extBOf Q g i bools bits S) (extOf Q g i bools bits S) t (S.val t)).b (g.d.bpos j)) (fun j w => (…).v (g.d.vpos j) w) g.d.nexts` and `genSemGen_result : … ((refBody …).fst).map (fun f => f t) = g.d.outs.map fun o => enc o.1 (eval …)` (the exact `GenFacts.writes/result` instances; by `valsAt_sigListOfFn`, `reconState_mkHolds`, `List.map_map`) and `genSemGen_source` (`rfl`) | I |
| P4a | `typedVal_let_congr` (§2.1) and `lsrcAt_congr` | I (needs `d.ok`) |
| P4d | `ExtStage_agree : n ≤ m → ∀ p < kDOf g.d + n, (ExtStage … m).1 p = (ExtStage … n).1 p ∧ ∀ w, (ExtStage … m).2 p w = (ExtStage … n).2 p w` | I |
| P4e | `ext_call_eq` (ordinary): under `GenWF g.d`, `CalleeCausal`-free S1–S3: `∀ τ, posEnc … (kD+k) κ = f τ`; i.e. `genExtAtCall_of_genSem` | I (conditional on S1–S3) |
| P5 | `genFacts_comb`: `CombFacts g.d dom g.inits (genSemComb X g).src` when `g.d.ss.isEmpty ∧ insts.isEmpty` | I |
| P6 | `memFacts_of_genSem : GenWF g.d = true → originOf g.d k = .mem cb aw dw → MemFacts g.d.shape (lsrc i bools bits) g.d.ls.length (g.d.bsIn.drop (kDOf g.d)) (kDOf g.d) (extOf Q g i bools bits S) k c` — §1.5, by P4a + `enc_lt` | I |
| P6' | causality: `memRead` at `t` reads `A,Dd,E,R` at `≤ t` (locate `Signal.memory`/`memoryComboRead` lemmas in `MachineMemLinked.lean`; *not located yet*) ⇒ `HCausalOf g.d dom (extOf Q g) (extBOf Q g)` given `CalleesCausal Q g.d` | I (given `hQ`) |
| P7 | `genSemI_local : (∀ k, k < n ∧ originOf g.d k is ordinary → Q c_k = Q' c_k) → genSemI Q X g = genSemI Q' X g` | I |
| P8 `[B]` | `toSem_genPkg`, `pkg_eq_of_toSem`, accessor agreement (§3); `genSem_not_loop` | I |
| P9, P10 | abstract `Acc` skeleton and `genS_srcCausal_acc` — **owned by DG-ACC** except the lemma with `hQ`-shape (§7) | I (abstract) |
| P11 | `genFacts_gen`, `genFacts`, `genSemI_srcCausal`, `trace_of_genSem` (rev1 §2.6/§3.1; `trace_of_genSem` is intermediate until `hQ` and `GenIn` are supplied) | I over `GenIn` |
| P12 | `GenData.toIn`, `genSem`, `GeneratedAt`, `generatedAt_unique`, `genS_some_inv` (as `genS_some_inv_of_unfold`, §7) | D |

## 7. Ownership of `genS` / `genSem_local` (DG-SEM vs DG-ACC; wf vs DG-WFCOVER)
DG-ACC's title (`sparkle-gen5-dg-acc`): "Acc construction of P, genSem_local, genS_unfold, self-consistency"; DG-SEM's: "GenData, genSem per arm, callee-restricted causality, genFacts, genS_some_inv". They both name the locality lemma and both depend on a definition of `genS`.

| item | owner | note |
|---|---|---|
| `genSemI`, `genSemGen`, `genSemComb` and their facts (P3–P6, P11) | **DG-SEM** | |
| `genSemI_local` (P7) — a statement about `genSemI` | **DG-SEM** states and proves; **DG-ACC consumes** it (its "genSem_local" bullet becomes a use, not a second proof) | to be written into DG-ACC's note by whoever updates that issue; this unit does not change another issue's state |
| the `Acc` relation, `genS : Name → Option (SemPkg)` by `Acc.rec`, `genS_unfold` | **DG-ACC** | not defined here |
| `genS_some_inv` | **DG-SEM**, as a lemma **abstract in `G : Name → Option (SemPkg)` and in the unfolding equation** `hunf : ∀ X, G X = if (∀ k ∈ ordCallees d, (G (callee k)).isSome) then some (genSem G X g) else none`: `genS_some_inv_of_unfold`. DG-ACC instantiates `G := genS` with its `genS_unfold`. | avoids both a duplicate `genS` and a dependence on DG-ACC for the lemma's proof |
| `genS_srcCausal_acc` (P10) | **DG-ACC** supplies the `Acc` induction; DG-SEM supplies the step `genSemI_srcCausal` (its `hQ` is the IH) | |
| coverage of `GenIn.wf` on real runs | **DG-WFCOVER** (not DG-DATAOF) | §1.6 |
| `dataOf`, `GenData.toIn`, `initsOf`, `dataOf_sound` | DG-DATAOF | premise |

## 8. Checks planned after approval (not run for rev2's new proposals)
Same shape as the Check built for P1/P2/P8: TYPE against independently written statements, MUTANT (signature/defeq rejection only), AXIOMS
(`Lean.collectAxioms`, standard only), closure = no `sorryAx` in any collected axiom list. Planned mutants for the new units:
drop A4 from `memFacts_of_genSem` (⇒ the 4-list conjunct unprovable), drop the `clean.getD` branch of `posOk` (read-through-`let` case lost),
read `Q` at a memory entry (⇒ `genSemI_local` premise too weak), `ρ i := Unit` (⇒ `result` mismatch).

## 9. Not claimed
- Nothing about P3 onward is elaborated; only P1, P2, `SemPkg`/`toSem`/`genPkg`/accessors are built (`[B]`), and their Check ran in the Pod build, not yet a clean evidence build.
- `GenIn` inhabitedness, `GenWF` coverage on real runs, `Acc`, `houtTy`, `CallOutWidthAt`, `GenExtAtCall`/`HPointG`, `DeclConnect` are **not supplied here**; "not supplied" means this study found no supplier on this route, not impossibility.
- REV-1…REV-4 are new rows of the `GenWF` defined here (§1.4); whether the reviewer counts them as a strengthening is flagged, not decided.
- No FG/M5 completion; no change to a shared definition, the compiler, or any law.

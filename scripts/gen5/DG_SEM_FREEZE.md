# DG-SEM freeze rev1 — `genSem`, its boundary to DG-DATAOF, its connection to the existing meaning lemmas, supplier table

**FOR REVIEW — design only.** No Lean file was edited, nothing was elaborated or built by this unit. Every Lean text below
is a PROPOSAL; names, binders and elaboration are unverified (`[S]` = read in this worktree, base `par/gen3-combined`
9d26005c; `[D]` = `git show par/gen5-t2:scripts/gen5/DGEN_FREEZE.md` rev2.x = c398021c; `[R]` = `T2COVER_FREEZE.md` same ref).
Issue: `sparkle-gen5-dg-sem` (DG-SEM / ASSIGN / CAUSAL / FACTS / GENP). Depends on `sparkle-gen5-dg-dataof` (doing, kjob/g5do-*,
no commit yet at the time of writing).

No new TRUSTED boundary, law, FG/guarantee change, shared-definition change or compiler edit is proposed. All new Lean goes in
NEW files (names in §6). Nothing here is a supply of any open obligation: §4 lists what is *not* supplied.

## 0. Scope of this freeze, and what changed relative to [D] §2.1

[D] fixes the shape (`SemPkg`, `genSem`, `genSem_local`, `genFacts`, `genS`, `genS_some_inv`). This document fixes what [D] left
to "DG-SEM's own freeze":

| [D] left open | fixed here |
|---|---|
| exact form of `GenWF` | §2.1 (three row groups, one Prop, a `Bool` that decides it) |
| `.loop` arm or not | §2.5: no `.loop` arm (`genSem_not_loop`); reason and reversal cost stated |
| exact `ext`/`extB` at ordinary calls (call order recursion) | §2.4 (staged families; `ExtStage`) |
| `ext` at memory entries | §2.4: read from `InstOrigin.mem combo aw dw` (`Sparkle/Compiler/MachInstOrigin.lean:21` [S]) and `memRead` |
| how `writes/result/source` hold *by construction* | §2.3 (reference body is `Circuit` built from `evalTerms`; `ρ i := List (Nat → Nat)`, `obsR := id`) |
| `kD` of the `.gen` arm | §2.3 `kDOf` (derived from the `GenWF` arity row, not stored) |
| the abstract boundary to `dataOf` | §1 (`GenIn`; `GenData.toIn` is the only place that changes when DG-DATAOF freezes) |
| connection to the existing meaning lemmas | §3 |
| supplier table, pure-lemma units | §4, §5 |

## 1. Boundary to DG-DATAOF: `dataOf`'s type is a PREMISE, abstracted as `GenIn`

`genSem` and every pure lemma are stated over the *consumed output* of DG-DATAOF, not over `dataOf` itself:

```lean
/-- Everything `genSem` reads from the reader data. Its fields are exactly the conclusions of `dataOf_sound` [D §2.1]
(`ok`, `body_eq`, `init`) plus the `GenWF` row and the register initial values (`initsOf d`). No `dataOf`, no `E`, no `senv`. -/
structure GenIn where
  d      : MachineData
  wf     : GenWF d = true
  inits  : HList (tys d.ss)
  ok     : d.ok = true
  bodyEq : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
                                      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed
  init   : d.initOk inits = true
```
`ok/bodyEq/init` are the field types of `GenFacts.ok/.body_eq/.init` (QuadComposed.lean:120-124 [S]), `CombFacts.ok/.hbody/.hinit`
(CombPkg.lean:43-49 [S]); the premise is the same proposition, so a `GenIn` can be restated without a cast.

**The abstract premise (the ONLY dependence on DG-DATAOF).** DG-DATAOF's final freeze must provide a function
```lean
def GenData.toIn {E senv} (g : GenData E senv) : GenIn   -- d := g.d; wf := g.wf; inits := initsOf g.d; ok/bodyEq/init := dataOf_sound g.hdata
```
The proposed `GenData` / `dataOf_sound` / `initsOf` of [D §2.1] (rev2) are used as the *expected* shape, but nothing below
depends on them except `toIn`. `genSem` is defined on `GenIn`; the [D]-form is a one-line wrapper:
```lean
noncomputable def genSemI (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) : SemPkg ι dom   -- §2.4
noncomputable def genSem  (Q) (X) {E senv} (g : GenData E senv) : SemPkg ι dom := genSemI Q X g.toIn   -- [D]'s name and type
```
Consequences for the order of work:
- Everything in §5 marked **I** (independent) is stated and provable over `GenIn` / any `MachineData` and needs no `dataOf`.
- Items marked **D** consume `GenData.toIn` and are *intermediate* until DG-DATAOF is approved and built; they are written with
  the DG-DATAOF type as an explicit hypothesis/definition, and are not counted as supplied (§4).
- If DG-DATAOF changes `GenData` or `initsOf`, only `toIn` (and the `D` rows) change; `genSemI`, `genSemI_local`, the facts
  lemmas over `GenIn` do not.
- `initsOf`: DG-DATAOF supplies it as the total read of the register initial values. This freeze adds no requirement on how.

## 2. Full types

All under `namespace Tools.ShippingGen5Sem` (new file(s), §6). `variable {ι : Type} {dom : ι → DomainConfig}`.

### 2.1 `GenWF` (rows unchanged from [D]: arities, call-output kinds, call order)
```lean
/-- `d.nIn` splits into the declared binders and one binder per call entry. -/
def kDOf (d : MachineData) : Nat := d.nIn - d.shape.insts.length

/-- Row A (arities):  `d.nIn = kDOf d + insts.length` i.e. `insts.length ≤ d.nIn`; `instOrigins`/`insts` have the same length
    (`instOrigins.length = insts.length`); every call argument `l ∈ (insts[k]).2.1` has `l < d.ls.length`;
    `d.ss.length = d.shape.layout.slots.length` is NOT a row (it is `dataOf_sound`/`ok`'s business). -/
/-- Row B (call-output kinds): the binder of call `k` is a Bool or a BitVec (`d.K (kDOf d + k) = some s`, with
    `sortOf` defined); a memory entry's binder is `.bits dw` for its origin's `dw`. -/
/-- Row C (call order): the `let` terms at the argument positions of call `k` read only call-result positions `kDOf d + j`, `j < k`
    (the reads relation is `reads okB okV` of `Term`, MachineDenote.lean:194 [S]); for a memory entry, its four
    argument lets likewise. -/
def GenWFP (d : MachineData) : Prop := RowA d ∧ RowB d ∧ RowC d
def GenWF (d : MachineData) : Bool := decide (GenWFP d)          -- needs `Decidable (GenWFP d)`: each row is a `List.all`-style bound
theorem genWF_iff : GenWF d = true ↔ GenWFP d
```
*Open point (§7 O1):* the exact `reads`-based form of Row C (which positions are "call results" for `reads`'s `okB/okV`) is
fixed by implementation against MachineDenote's `reads`; the freeze requirement is only: **a decidable Prop with the three
groups above and nothing more.** No `GenWF` strengthening beyond these rows is proposed. Whether the three rows hold on every
successful source is DG-WFCOVER, not this unit.

### 2.2 Per-arm semantic data (the package minus its fact field)
```lean
/-- `SrcPkg` without `gen` (Tools/ShippingGen2SrcPkg.lean:41-56 [S]). Fields in the same order and with the same types. -/
structure SrcSem (ι) (dom) where
  decl : Name;  d : MachineData;  kD : Nat;  ρ : ι → Type;  inh : Inhabited (HList (tys d.ss));  inits : HList (tys d.ss)
  body : …;  obsR : …;  ext : …;  extB : …;  src : …            -- verbatim from SrcPkg
/-- `CombPkg` without `facts` (CombPkg.lean:86-92 [S]): decl d kD inits src. -/
structure CombSem (ι) (dom) where  decl : Name;  d : MachineData;  kD : Nat;  inits : HList (tys d.ss);  src : …
/-- `SrcPkgL` without `facts` (Loop.lean:180-199 [S]). Exists only so `SemPkg` is a faithful image of `Pkg`; never produced by `genSem`. -/
structure LoopSem (ι) (dom) where  decl d kD α inh ρ σ inits f res obsR ext extB src   -- verbatim from SrcPkgL

inductive SemPkg (ι) (dom) | gen (s : SrcSem ι dom) | comb (s : CombSem ι dom) | loop (s : LoopSem ι dom)
-- SemPkg.decl/.d/.kD/.src/.extS/.extBS/.lsrc: by cases, exactly as Pkg's (Gen2Pkg.lean:40-79 [S]).

def FactsOf : SemPkg ι dom → Prop     -- verbatim from [D §2.1]: GenFacts / CombFacts / LoopFacts at the arm's fields
def Pkg.toSem : Pkg ι dom → SemPkg ι dom                                 -- forgets `gen`/`facts`
def semOf (P : Pkgs ι dom) : Name → Option (SemPkg ι dom) := fun c => (P c).map Pkg.toSem
noncomputable def genPkg (s : SemPkg ι dom) (hF : FactsOf s) : Pkg ι dom
theorem toSem_genPkg : (genPkg s hF).toSem = s
theorem pkg_eq_of_toSem {p p' : Pkg ι dom} : p.toSem = p'.toSem → p = p'      -- proof irrelevance of the Prop fact field
```
`SrcSem.extS/.extBS/.lsrc` etc. are the same definitions as `SrcPkg.extS/...` (`stateLoop`, `letObsB`), restated on `SrcSem`;
the identification `(genPkg s hF).extS = s.extS` etc. is `rfl` by cases (§5 P8).

### 2.3 The `.gen` arm built from a `GenIn` (reference body, by construction)
The aim is that `GenFacts.writes/result/source` hold *by definition* (as [D] says "by construction"), without any
generator-term reflection. The construction uses only `MachineData` fields and the existing `evalTerms/typedVal/enc/eval`
(MachineDenote.lean:57-110, :459 [S]).

```lean
/-- Result type and observations: `ρ i := List (Nat → Nat)`, `obsR i r := r` (so `source` is `rfl`-shaped, `result` is on the list). -/
-- ρ i := List (Nat → Nat)   obsR := fun _ r => r

/-- State rebuilt from the register handles/holds of `mkRegList S`/`mkHolds S`; `recon (mkHolds αs S) = S` (pure lemma P2). -/
def reconState : (αs : List Type) → Circuit.SigList dom αs → Signal dom (HList αs)

/-- The call-extended families `ext/extB` for a GIVEN state signal: §2.4. -/
noncomputable def extOf (Q) (g : GenIn) : (i : ι) → … → Signal (dom i) (HList (tys g.d.ss)) → (j n) → Signal (dom i) (BitVec n)
noncomputable def extBOf (Q) (g : GenIn) : …                                                → Nat → Signal (dom i) Bool

/-- Pending writes at state `S`: slot `s` is the signal `fun t => (evalTerms … (typedVal g.d.nIn … (extBOf Q g i bools bits S) (extOf Q g i bools bits S) t (S.val t)) …).s`,
    packed as a `SigList` by `sigListOfFn` (P1: `valsAt αs (sigListOfFn f) t = f t`). -/
def sigListOfFn : (αs : List Type) → (Nat → HList αs) → Circuit.SigList dom αs

/-- The reference body: reads the state from its `holds`, returns the observation list, writes the packed next-state signals. -/
noncomputable def refBody (Q) (g : GenIn) (i) (bools) (bits) : RegList … → Circuit (dom i) (SigList …) (List (Nat → Nat)) :=
  fun regs holds => let S := reconState _ holds; (resultList …S, sigListOfFn _ (nextFn …S))     -- exact term: see P1/P3

noncomputable def genSemGen (Q) (X) (g : GenIn) : SrcSem ι dom :=
  { decl := X, d := g.d, kD := kDOf g.d, ρ := fun _ => List (Nat → Nat), inh := ⟨…default state…⟩, inits := g.inits,
    body := refBody Q g, obsR := fun _ r => r, ext := extOf Q g, extB := extBOf Q g,
    src := fun i bools bits => (refBody Q g i bools bits (mkRegList (stateLoop g.inits (refBody Q g i bools bits)) …) (mkHolds … )).fst }
```
- `inh`: `Inhabited (HList (tys d.ss))` — the default is `inits` itself (`⟨g.inits⟩`); no new axiom.
- `src` is *defined* as `GenFacts.source`'s right-hand side (with `obsR := id`), so `source` is `Eq.refl`.
- `writes` and `result` then reduce to `valsAt_sigListOfFn` (P1) and `reconState (mkHolds S) = S` (P2): lemmas about the Signal
  library only, over arbitrary `MachineData`/`ext`/`extB` — **independent of dataOf** (class I).
- Risk R-RECON (§7 O2): if `reconState (mkHolds _ S) = S` is not available by `Signal` eta, the fallback is to build the body from
  `regs` (each `Reg.mk (headReadSig liveOuter)`) rather than `holds`. Decided when P2 is attempted; both give the same `FactsOf`.

`.comb` arm (slotless **and** call-free): `genSemComb g := ⟨X, g.d, kDOf g.d, g.inits, srcComb⟩` with
`srcComb i bools bits := d.outs.map fun o => (fun t => enc o.1 (eval … (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t g.inits)…))`
(the right side of `CombFacts.hres`, CombPkg.lean:50-55 [S], so `hres` is `rfl`; `hnext` from `d.ss = []`, see P5).

### 2.4 `ext`/`extB`: staged families, ordinary callees and memory entries
Position `p < kD` is the declared input (pass-through); position `kD + k` is call `k`. For one state signal `S` and inputs
`bools bits`, define by structural recursion on a bound `n`:
```lean
/-- `ExtStage Q g i bools bits S n` : families in which calls `k < n` are filled in; calls `≥ n` (and positions `≥ kD + insts.length`)
    are the inputs `bools/bits` unchanged. Stage `n+1` = stage `n` extended at `kD + n` by `callOut … n` (read under stage `n`). -/
noncomputable def ExtStage (Q) (g : GenIn) (i) (bools) (bits) (S) : Nat → (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))
  | 0 => (bools, bits)
  | n+1 => let (bs, bt) := ExtStage … n; callOut Q g i bools bits S bs bt n
def extOf  … := (ExtStage … g.d.shape.insts.length).2
def extBOf … := (ExtStage … g.d.shape.insts.length).1
```
Call `k` is read under stage `k` (calls `< k` only). This is where Row C (call order) is used: the argument lets of call `k` read
only positions `< kD + k`, so they are the same under stage `k` and under the final stage (**lemma P4**, `eval_congr_wf`-style,
MachineDenote.lean:201 [S]). Without Row C the recursion is still total (it is staged), but the *equation* "ext at `kD + k` =
callee `src` on the final let observations" (needed by `CallOutF`, [R] E1) is not provable; that is why it is a `GenWF` row.

`callOut` at call `k`, with `c := (insts[k]).1`, `args := (insts[k]).2.1`:
- **ordinary** (`(instOrigins.getD k .ord).child? = none`): when `Q c = some q`:
  `vals := valsOf lsrcStage args` (the observations of the argument lets under stage `k`, `valsOf` ShippingMachineCallsLinkedT.lean:25 [S]),
  `A := boolsOf (D := dom i) (q.d.bsIn.take q.kD) vals`, `B := bitsOf … vals` (exactly the `Pkg.S` decoding, Gen2Pkg.lean:84-86 [S],
  and `HPointG`'s `A/B`, CallField.lean:77-87 [S]); the output index is
  `k' := if p.instFields = [] then 0 else (index in q.d.shape.layout.outs of the field named instFields[k])`
  (the `CallField` rule, Defs:94-96 [S]); `f := (q.src i A B)[k']`; the extended position receives `f` decoded by the kind of
  binder `kD + k` (Bool: `f τ == 1`; BitVec w: `BitVec.ofNat w (f τ)`), via `extendBools/extendBits` (MachineCausal.lean:618, MachineAuto.lean:377 [S]).
  Inverse of `posEnc` (MachineEntry.lean:293 [S]): `posEnc (extended) (kD+k) kind = f τ` holds when `f τ < 2^w` (Row B + the
  callee's output range). **That range fact is NOT part of this unit** (it is the `hDG_SEM_range` supply, [D §7]).
  When `Q c = none` (never from `genS`, which is strict): the constant-zero family, as [D].
- **memory** (`origin = .mem combo aw dw`): `A,Dd,E,R` are the observations of the four argument lets (`MemFacts`,
  CallsLinkedT.lean:31 [S]) decoded by their kinds; the new signal is `memRead combo A Dd E R` (MachineMemLinked.lean:33 [S]).
  `combo/aw/dw` come from the origin constructor itself, so `Q` is not read, and no module is compared.
  `MemFacts d.shape (lsrc …) … (ext …) k c` is then derived (P6), not assumed.
- `.field i` origin: ordinary (its `child?` is `none`).

`genSemI Q X g := if g.d.ss = [] ∧ g.d.shape.insts = [] then .comb (genSemComb X g) else .gen (genSemGen Q X g)` ( `Classical` split; or `decide`, since both are decidable ).

**Locality** (`genSemI_local`, class I, P7): if `Q` and `Q'` agree on `(insts[k]).1` for every `k ∈ ordCallees g.d`, then
`genSemI Q X g = genSemI Q' X g`. Proof: the only reads of `Q` are in the ordinary branch of `callOut`.
`ordCallees` is as [D §2.1] (`List.finRange`, `child? = none`). The `.comb` branch does not mention `Q`.

### 2.5 `.loop` arm: NOT produced
`genSem_not_loop` as [D]. Reason: `SrcSem` is enough for loop-form declarations when the reference machine is taken as the
`stateLoop` body; `LoopFacts` has a different shape (`σ`, `f`, `res`, `hsrc` via `Signal.loop`) and is not obtained from `GenFacts`.
Reversal cost: a `genFacts_loop` unit of the size of `genFacts_gen` (not started). The relation of the source's `Signal.loop` form to
`stateLoop` is `DeclConnect` row 4 ([D §2.6]), not this unit. No claim is made that `.gen` is the right arm for every loop-form source.

### 2.6 Facts, causality, assignment (the other four sub-units; types as [D], with the §1 boundary)
```lean
def SrcCausal (s : SemPkg ι dom) : Prop                          -- verbatim [D §2.1]
def CalleesCausal (Q) (d : MachineData) : Prop                   -- verbatim, restricted to ordCallees d
theorem genFacts_gen  (Q X) (g : GenIn) (hQ : CalleesCausal Q g.d) (s) (hs : genSemI Q X g = .gen s) : @GenFacts s.d ι dom s.ρ s.inh s.inits s.body s.obsR s.ext s.extB s.src
theorem genFacts_comb (Q X) (g : GenIn) (s) (hs : genSemI Q X g = .comb s) : CombFacts s.d dom s.inits s.src
theorem genFacts (Q X) (g : GenIn) (hQ : CalleesCausal Q g.d) : FactsOf (genSemI Q X g)
theorem genSemI_srcCausal (Q X) (g : GenIn) (hQ : CalleesCausal Q g.d) : SrcCausal (genSemI Q X g)
```
`GenFacts.ok/body_eq/init := g.ok/g.bodyEq/g.init`; `writes/result/source` from §2.3; `causal` (`HCausalOf`) from `hQ` (ordinary: `q.src`
causal in its inputs, which are decoded let observations that read only earlier positions) plus the memory model (`memRead` is
causal: `Signal.memory`/`memoryComboRead` at `t` read only `≤ t`; P6'). `hQ` is exactly what `genS_srcCausal_acc` supplies ([D] C4).
`genS`, `genS_unfold`, `genS_some_inv`, `genS_facts`, `genP`, `semOf_genP`, `genP_generated`: as [D §2.5] C1-C6, with `GenData`
(DG-DATAOF's) and `GenData.toIn`; they are class **D** (they need `entry₀/dataOf₀/genData₀`, which are DG-DATAOF/DG-ENV
outputs) except the purely order-theoretic `Acc.rec` part (P9), which is stated over an abstract `CallEdge`-like relation.

## 3. Connection to the existing meaning lemmas (the TYPES; no new semantic claim)
`genSem` is not a new semantics. The meaning of a generated package is *already* `Pkg.trace`/`Pkg.traceX`; `genSem` only
chooses the package's data. The connection is by construction + three existing facts:

1. **Fact → trace.** `FactsOf s` is by definition the premise of `Pkg.trace`'s per-arm lemma (`genTrace`, QuadComposed.lean:~155 [S];
   `machine_traceL_of_comb_callsRA_ranA`, CombPkg.lean:60-80 [S]; `genTraceL`, Loop.lean [S]). So, for `s := genSemI Q X g` and `hF := genFacts … `:
   ```lean
   theorem trace_of_genSem (O T hA) (g : GenIn) (hQ) {D₀ m design} (ran : MachineRunJQC O mctx cctx (D₀+1) X (genSemI Q X g).d.shape m design) :
     MachineTraceLBX (ServedRealA O X _ m design) X (genSemI Q X g).d m design dom (genSemI Q X g).src (….extS) (….extBS) (….lsrc)
   -- := Pkg.trace O T hA (genPkg (genSemI Q X g) (genFacts Q X g hQ)) ran, rewritten by `toSem_genPkg`/`rfl` on the projections.
   ```
   (and the `traceX` form with `Pkg.traceX`, Served.lean:621 [S], same shape). This is a one-line corollary; it adds no premise
   beyond `ran` (the run) and `hQ` (callee causality). It is **intermediate** until `hQ` is supplied by C4 and `GenIn` by DG-DATAOF.
2. **`MachineDenote` lemmas** (`typedVal`, `eval_typed`, `denote_state`, `denote_out`): used *inside* the existing `genTrace`, not
   re-proved. `genSem`'s `writes/result` are stated in the same `typedVal … (extB…) (ext…) t (S.val t)` form as `GenFacts` so that
   `genTrace` applies unchanged. No `Meaning/Denote/Semantics`-file lemma outside this set is needed by §5's pure lemmas.
3. **Call positions.** At an ordinary call `k`, `ext` at `kD + k` is *by construction* `q.src` on the decoded argument observations
   (§2.4), which is the content `CallOutF`/`HPointG` ask for ([R] E1: "BY CONSTRUCTION"). The remaining obligations there
   (output-index witness `k'`, `posEnc` decoding) are T2-FIELD / DG-HPOINT, not here. This unit provides the equation
   `ext_call_eq : (extOf Q g i bools bits S (kD+k) w) = decode(f)` (P4) as its output to them.
4. **`GeneratedAt`** ([D §2.1]) is unchanged: `∃ g : GenData E senv, p.toSem = genSem (semOf P) X g`.
   `generatedAt_unique` follows from `pkg_eq_of_toSem` + determinism of `genSem` in `g`'s *content* (the `GenData` evidence
   fields are Props), class D.
5. **Not connected here:** the meaning of the *elaborated declaration* `X` (`DeclConnect`, [D §2.6]) — unsupplied by this unit.

## 4. Supplier table (what supplies each premise; "not found" = this study found no supplier on this route, NOT "impossible")

| premise / obligation | supplier | status | used by |
|---|---|---|---|
| `GenIn.ok/bodyEq/init`, `initsOf` | DG-DATAOF `dataOf_sound` via `GenData.toIn` | **open (dep issue doing)**; premise | all D rows |
| `GenIn.wf : GenWF d = true` | DG-WFCOVER (coverage on real runs); `GenWF` itself defined here (§2.1) | def here; coverage **open** | P4, ASSIGN |
| `dataOf₀/genData₀/entry₀/CallEdge` | DG-DATAOF + [D §2.5 C1-C2] (DG-ASSIGN, this issue, class D) | open | `genS` |
| `Acc (flip CallEdge) X` | DG-ACC (needs G-REACH) | **open, unsupplied** | `genS` existence only; not `genSemI` |
| callee `src` causal (`CalleesCausal`) | `genS_srcCausal_acc` by `Acc` induction (this issue, P10) | pure given `Acc` | `genFacts_gen.causal` |
| memory-entry causality | `memRead` causality (`Signal.memory`, `memoryComboRead`; MachineMemLinked.lean [S]) | existing lemmas **to locate** (P6') | `genFacts_gen.causal` |
| `Pkg.trace`/`traceX` per arm | existing, built (Gen2Pkg.lean:115, Served.lean:621 [S]) | **supplied** | §3.1 |
| `typedVal`/`eval`/`denote_*` | existing (MachineDenote.lean [S]) | **supplied** | §2.3, §3.2 |
| `stateLoop`, `valsAt`, `packRegister_val`, `circuit_state` | existing (MachineSource.lean:10-90 [S]) | **supplied** | §2.3, P1-P3 |
| `valsOf`, `MemFacts`, `boolsOf/bitsOf`, `InRange` | existing (CallsLinkedT, MachineChild [S]) | **supplied** | §2.4 |
| `extendBools/extendBits`, `posEnc` | existing (MachineCausal:618, MachineAuto:377, MachineEntry:293 [S]) | **supplied** | §2.4, P4 |
| callee output range `< 2^w` (so `posEnc ∘ decode = id`) | `hDG_SEM_range` supply ([D §7]: T2-SRCRANGE + G-ONEOUT-WID) | **unsupplied intermediate** | only the `posEnc` decoding equation (not `genSem`/facts) |
| `CallField`'s `k'` witness & uniqueness | T2-FIELD / `callField_unique_of_ok` ([D §7.4]) | open (other issue) | DG-HPOINT |
| `HPointG`/`CallDec` from `ext` equation | DG-HPOINT / T2COVER E1 | open (other issue) | consumes P4 |
| `DeclConnect` | decl-bridge | open (other issue) | not used here |
| new TRUSTED / law / guarantee | none proposed | — | — |

No row above is counted as supplied by this freeze; "supplied" means already built at 9d26005c and cited.

## 5. Pure-lemma units (statement-level; each is an own Lean unit, all NEW files)

Class **I** = no `dataOf`/`GenData` mention; stated over `MachineData`/`GenIn`/arbitrary `ext`. Class **D** = needs DG-DATAOF's output.

| id | statement | class | size est. |
|---|---|---|---|
| P1 | `valsAt αs (sigListOfFn αs f) t = f t`; `(sigListOfFn …)` for the `nexts`/`outs` forms | I | 30-80 |
| P2 | `reconState αs (mkHolds αs S) = S` (and the `RegList` variant if used) | I | 40-120 |
| P3 | `GenFacts.writes` and `.result` for `refBody`/`extOf`/`extBOf` over any `Q`,`g` (by P1,P2; `rfl` shapes) | I | 80-200 |
| P4 | staged families: `ExtStage n` agrees with `ExtStage m` at positions `< kD + n`, `n ≤ m`; under Row C the argument observations of call `k` agree between stage `k` and final; **`ext_call_eq`** (ordinary and memory) | I | 200-500 |
| P5 | `.comb`: `CombFacts.hnext` from `d.ss = []` (`HList []` subsingleton) and `hres` by `rfl`; `.comb` is call-free so `extS = id` | I | 40-100 |
| P6 | memory entry: `MemFacts` for `extOf` at a `.mem` origin, from the construction | I | 100-250 |
| P6' | causality of `memRead` and of `extOf` positions in `S` (pointwise `≤ t`); `HCausalOf` for `extOf/extBOf` given `CalleesCausal` | I (given `hQ`) | 150-400 |
| P7 | `genSemI_local` | I | 40-100 |
| P8 | `toSem_genPkg`, `pkg_eq_of_toSem`, `(genPkg s hF).extS = s.extS` etc.; `genSem_not_loop` | I | 100-250 |
| P9 | `Acc.rec` skeleton for `genS`: unfolding lemma over an abstract `R`, with the strict-callee side condition | I (abstract `R`) | 80-200 |
| P10 | `genS_srcCausal_acc` by `Acc` induction, abstract in `genSem`'s `hQ` | I (abstract) | 60-150 |
| P11 | `genFacts_gen`, `genFacts_comb`, `genFacts`, `genSemI_srcCausal`, `trace_of_genSem` (§3.1) | I over `GenIn` | 150-400 |
| P12 | `GenData.toIn`, `genSem`, `GeneratedAt`, `generatedAt_unique`, `entry₀/dataOf₀/genData₀`, `genS_unfold`, `genS_some_inv`, `genS_facts`, `genP`, `semOf_genP`, `genP_generated` | D | 200-500 |

Order: P1 → P2 → P3; P5; P4 → P6; P7; P8; P6' → P11; P9 → P10; P12 last (after DG-DATAOF approval). Only P12 and the `GenIn.wf`
coverage wait for DG-DATAOF / DG-WFCOVER. Estimates are Lean lines, not measurements.

Implementation files (new, `lean_lib`/imports via lakefile only): `Tools/ShippingGen5SemPkg.lean` (§2.2, P8), `Tools/ShippingGen5SemRef.lean`
(P1-P3), `Tools/ShippingGen5SemExt.lean` (P4, P6, P6', P7), `Tools/ShippingGen5SemFacts.lean` (P5, P11), `Tools/ShippingGen5SemAssign.lean` (P9, P10, P12).
Each file is built alone with `kjob lake build <target>`; a clean-build SHA goes in a comment-only commit in a `NOT BUILT` header.

## 6. Checks planned (after approval; not run)
- Expected-type audit: each `FactsOf`-instance theorem is stated with the exact `GenFacts`/`CombFacts` type by `example : T := thm`.
- Closure/axiom audit: `#print axioms` on P3, P4, P11 (expect `propext`, `Classical.choice`, `Quot.sound` only; `Classical` is used for the
  arm split / field-name lookup only if `decide` does not apply).
- Mutants (signature/defeq rejections, **not** semantic counterexamples): (m1) drop Row C from `GenWFP` ⇒ `ext_call_eq` no longer
  typechecks without the missing hypothesis; (m2) read `Q` at a memory entry ⇒ `genSemI_local`'s `hQ` (restricted to `ordCallees`)
  is no longer enough; (m3) `ρ i := Unit` ⇒ `GenFacts.result` mismatch. They show the statements are not trivially satisfiable; they do not show semantic correctness.

## 7. Open points and decision items
- **O1** exact `reads` encoding of Row C (§2.1). Implementation detail; the Prop's content (groups A/B/C) is frozen.
- **O2** `reconState` vs. building from `regs` (§2.3). Both give the same `FactsOf`; chosen when P2 is attempted.
- **O3** `kDOf d := d.nIn - insts.length` relies on Row A. If DG-DATAOF stores `kD` explicitly, `GenIn` gains `kD` and Row A becomes
  `d.nIn = kD + insts.length`; no other change.
- **O4** `.loop` (§2.5): no arm. If review asks for one, it is a new unit (not obtained from `genFacts_gen`).
- **O5** the output-index rule for a group parent (`instFields ≠ []`): `k'` is looked up by name in the callee's `layout.outs`; if the name is
  absent the zero family is used (never reached when `CallOutF` holds). `callField_unique_of_ok` ([D §7.4]) is not required by `genSem`.
- No user decision is needed: no new law, no shared-definition edit, no FG change, no scope reduction, no `GenWF` strengthening.
  If review finds one is needed (e.g. a Row beyond A/B/C), work stops and a decision document is written instead.

## 8. Not claimed
- Nothing here is built, elaborated or proved; all Lean is a proposal; sizes are estimates.
- Not claimed: `GenIn` is inhabited for any real run (DG-COVER/DG-WFCOVER/DG-DATAOF); `Acc` (DG-ACC/G-REACH); the callee output range
  (`hDG_SEM_range`); `HPointG`/`CallDec` (DG-HPOINT); `DeclConnect`; that `genSem`'s `src` is the meaning of the elaborated `X`.
- No claim about `.loop`-form declarations beyond §2.5; no claim that the three `GenWF` rows hold on every successful source.
- "Not supplied" means this study found no supplier on this route; it is not a claim of impossibility.
- Design completion is not DG-SEM completion and not M5 or FG.

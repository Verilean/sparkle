# A: cache coherence, the certified route — round par/a-34

Base: `poc/roundtrip-proof` bfa5f5fe (par/a-33 BUILT and integrated).
Branch `par/a-34`. **NOTHING here was built or run**: every Lean file of
this round is WRITTEN, NOT BUILT; "READ" = read at bfa5f5fe; "PREDICTED" =
concluded from READ lines. Predecessors: `A-cache-coherence.md`,
`A-cache-coherence-2.md`.

## 0. Result in one paragraph

Step (b) is still NOT closed and `mixDeep` stays open. What this round does:
the two unrestricted residuals of par/a-33 (`CoreFresh c` for every `c`;
`HarnessProv` for every body) are replaced, for declarations on the MACHINE
route, by a per-declaration unit `EntryOk L c K` that is DERIVED
(`entryOk_machine`) from: the callees' `EntryOk`, a name condition `¬ K c`
(decidable per declaration), the harness's result facts (a BUILT theorem per
declaration data, `closedBody_kinds_of_run`, put in shape by `hout_of_data`),
and two statements of a smaller kind that are NOT derived — `HarnessStill`
(the harness on THIS transition leaves the cache) and `CoreVia` (route +
frame steps: the core run is the machine synthesis, with the same start and
end cache). "A run does not insert its own key" (H3) is no longer a separate
obligation for such declarations: it follows from a bound on the keys a run
adds (`KeysIn`). Both closings are covered, memory children included. The
consumer `machine_closes_of_entryOk` is written. It cannot be applied to
`mixDeep` yet: §4 says exactly what blocks it. No endpoint changes; no
premise is added to any endpoint.

## 1. Task 1 — H1 on the certified route

### 1.1 What turned out to be the right unit

`CoreFresh L c` asked three things of a core run (result provenance, `Prov`
of the end cache, own key absent). For a machine-route declaration all
three come from the STRUCTURE of the run, which is ordinary code after the
harness:

    core run = prefix (frames) ; harness (translator on the transition)
               ; closing (mapM of the memoised entry over the callees; a pure join)
               ; suffix (frames)

* result provenance: the closing's design is `designWith children d₀`
  (`closeInsts_design`, `closeInstsG_design`, BUILT); `d₀.modules = []` and
  the closed machine's name are the harness's result facts
  (`Tools.ShippingClosedKinds.closedBody_kinds_of_run`, BUILT, per
  declaration data); each child is a memory child or the END cache's entry
  (`mapM_inv` + `child_ok`, written — replaces the par/a-33 lemma that
  needed "no memory child" and covered one closing only);
* `Prov` of the end cache: each insert during the closing is a callee's
  (`synthesizeChild_ok`), given `EntryOk` of THAT callee — not of every
  declaration;
* own key: the keys the run adds are in `K` (`KeysIn`, carried through the
  closing by `PK`), and `¬ K c`.

So the unit is `EntryOk L c K` (full entry, with the key bound). It implies
what `CoreFresh` was used for, and it composes: a parent's `K` is the set of
its descendants; `EntryOk.mono` weakens `K`.

### 1.2 Statements (`Tools/ShippingCacheCoherentCert.lean`)

```lean
def KeysIn (m) (K : Name → Prop) (m') : Prop :=
  ∀ k y, m'.get? k = some y → (∃ y0, m.get? k = some y0) ∨ K k
theorem keysIn_refl / keysIn_trans / keysIn_mono
theorem keysIn_none (hk : KeysIn m K m') (h0 : m.get? c = none) (hK : ¬ K c) : m'.get? c = none
def KidOk (m) (y : Res) : Prop := (∃ cb aw dw, y = memModule cb aw dw) ∨ ∃ c, m.get? c = some y
theorem kidOk_mono (hs : SubMap m m') (h : KidOk m y) : KidOk m' y
theorem memModule_design : (memModule cb aw dw).2.modules = [(memModule cb aw dw).1]
theorem design_prov_of_kids (hp : Prov m) (hk : ∀ c ∈ children, KidOk m c) (hd0 : d₀.modules = []) :
    ∀ a ∈ (designWith children d₀).modules, IsMem a ∨ IsTop m a
theorem closeInsts_name  (h : closeInsts … children (m₀, d₀) = some (m, d)) : m.name = m₀.name
theorem closeInstsG_name (h : closeInstsG … children (m₀, d₀) = some (m, d)) : m.name = m₀.name

def EntryOk (L) (c : Name) (K : Name → Prop) : Prop :=
  ∀ mctx cctx w r w', InvV L w → L.dval w ≠ 0 → Prov (L.val w) → (L.val w).get? c = none →
    RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' →
    Prov (L.val w') ∧ Fresh (L.val w') c r ∧ KeysIn (L.val w) K (L.val w')
theorem EntryOk.mono (h : EntryOk L c K) (hK : ∀ k, K k → K' k) : EntryOk L c K'
def PK (L) (mb) (K) (w) : Prop := InvV L w ∧ L.dval w ≠ 0 ∧ Prov (L.val w) ∧ KeysIn mb K (L.val w)

theorem synthesizeChild_ok (L) (hw : InvV L w) (hd : L.dval w ≠ 0) (hp : Prov (L.val w))
    (hK : K c) (hR : EntryOk L c K) (h : RunsTo (synthesizeChild c) … w y w') :
    Prov (L.val w') ∧ KeysIn (L.val w) K (L.val w')
theorem child_ok (L) (hB) (hK : K c) (hR : EntryOk L c K) (hp : PK L mb K w)
    (hy : RunsTo (synthesizeChild c) … w y w') :
    PK L mb K w' ∧ SubMap (L.val w) (L.val w') ∧ KidOk (L.val w') y
theorem mapM_loop_inv / mapM_inv (G : α → Prop) (L) (P)
    (hf : ∀ x w y w', G x → P w → RunsTo (f x) … w y w' →
      P w' ∧ SubMap (L.val w) (L.val w') ∧ KidOk (L.val w') y)
    (l) (r) (hg : ∀ x ∈ l, G x) (hp : P w) (h : RunsTo (l.mapM f) … w r w') :
    P w' ∧ SubMap (L.val w) (L.val w') ∧ ∀ y ∈ r, KidOk (L.val w') y
theorem closeInstsM_all (L) (hB) (hins : ∀ x ∈ shape.insts, K x.1) (hR : ∀ c, K c → EntryOk L c K)
    (hp : PK L mb K w) (hd0 : d₀.modules = [])
    (hr : RunsTo (closeInstsM shape t m₀ d₀) … w r w') :
    PK L mb K w' ∧ ∀ m d, r = some (m, d) →
      m.name = m₀.name ∧ ∀ a ∈ d.modules, IsMem a ∨ IsTop (L.val w') a
theorem closeInstsGM_all  -- the same; hins : ∀ x ∈ shape.insts, memChild? x.1 = none → K x.1

def HarnessStill (L) (declName) (bs) (body) : Prop :=      -- STATEMENT, not derived
  ∀ mctx cctx b w r w', InvV L w → L.dval w ≠ 0 →
    RunsTo (synthesizeMixedCertified (fun e hint top named => translateExprToWire e hint top named)
      (profLogIO b) declName bs body) mctx mref cctx cref w r w' → L.val w' = L.val w
theorem machine_all (L) (hB) (hH : ∀ L', HarnessRel L')
    (hstill : HarnessStill L declName shape.binders shape.body)
    (hout : ∀ t t' d₀, MReturns (synthesizeMixedCertified … (profLogIO b) declName
        shape.binders shape.body) (t, d₀) → closeLets shape.layout.lets t = some t' →
      (closeMachine shape.layout t').name = ofDecl declName ∧ d₀.modules = [])
    (hinsM : shape.instFields.isEmpty = true → ∀ x ∈ shape.insts, K x.1)
    (hinsG : ∀ x ∈ shape.insts, memChild? x.1 = none → K x.1)
    (hR : ∀ c, K c → EntryOk L c K)
    (hw : InvV L w) (hd : L.dval w ≠ 0) (hp : Prov (L.val w))
    (hr : RunsTo (synthesizeMachineCertified … (profLogIO b) declName shape) … w r w') :
    PK L (L.val w) K w' ∧ ∀ m d, r = some (m, d) →
      m.name = ofDecl declName ∧ ∀ a ∈ d.modules, IsMem a ∨ IsTop (L.val w') a

def CoreVia (L) (c) (shape) : Prop :=                      -- STATEMENT, not derived
  ∀ mctx cctx w M D w', InvV L w → L.dval w ≠ 0 →
    RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w' →
    ∃ b w9 w10, RunsTo (synthesizeMachineCertified … (profLogIO b) c shape)
        mctx mref cctx cref w9 (some (M, D)) w10 ∧
      InvV L w9 ∧ L.dval w9 ≠ 0 ∧ L.val w9 = L.val w ∧ L.val w' = L.val w10
theorem entryOk_machine (L) (hB) (hH) (hvia : CoreVia L c shape)
    (hstill : HarnessStill L c shape.binders shape.body) (hout : ∀ b t t' d₀, …)
    (hinsM) (hinsG) (hR : ∀ c', K c' → EntryOk L c' K) (hc : ¬ K c) : EntryOk L c K

def EntryStill (L) (c) : Prop :=                           -- STATEMENT, not derived
  ∀ mctx cctx w r w', InvV L w → L.dval w ≠ 0 →
    RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' → L.val w' = L.val w
theorem entryOk_leaf (L) (hstill : EntryStill L c)
    (hkid : ∀ y, RealChild mref cref c y → y.1.name = ofDecl c ∧ y.2.modules = []) : EntryOk L c K

theorem machine_closes_of_entryOk (decls) (hS : MachineClosesAtS mctx mref cctx cref declName shape decls)
    (L) (hB) (hH) (hstill) (hout) (hinsM) (hinsG) (hR)
    (hw : InvV L w) (hd : L.dval w ≠ 0) (hp : Prov (L.val w))
    (hr : RunsTo (synthesizeMachineCertified … (profLogIO b) declName shape) … w r w') : r ≠ none
```

`Tools/ShippingCacheCoherentData.lean`:

```lean
theorem hout_of_data (d : MachineData) (ok : d.ok = true) (hbody : d.shape.body = quote …)
    (hC : d.callsOk nDecl = true) (hslots) (hdomB) (b : Bool) :
    ∀ t t' d₀, MReturns (synthesizeMixedCertified … (profLogIO b) declName
        d.shape.binders d.shape.body) (t, d₀) → closeLets d.shape.layout.lets t = some t' →
      (closeMachine d.shape.layout t').name = ofDecl declName ∧ d₀.modules = []
```

(the second half of `closedBody_kinds_of_run`, BUILT; same hypotheses).

Side conditions of `entryOk_machine`, and their kind:

| hypothesis | kind |
|---|---|
| `hout` | DERIVED per declaration data (`hout_of_data`; the endpoints' `MachineData`, `ok`, `hbody`, `callsOk`) |
| `hinsM`, `hinsG` | data: the callees are in `K` — a list membership per shape |
| `hc : ¬ K c` | names: the declaration is not one of its descendants — `Name` inequalities, decidable |
| `hR` | the callees' `EntryOk` (the recursion; leaves by `entryOk_leaf`) |
| `hkid` (leaf) | the last two clauses of `Tools.ShippingCallsGate.ChildIface` on `RealChild` — the form the built kid facts have |
| **`HarnessStill`** | **NOT derived** (§2) |
| **`CoreVia`** | **NOT derived** — route + frames (§3.2) |
| **`EntryStill`** (leaf) | **NOT derived** — the same two for a leaf |

No legacy translator arm is covered: the scope is declarations whose core
run is a machine synthesis (`CoreVia` says so) — and gate / leaf children
through `entryOk_leaf`.

## 2. Task 2 — `HarnessProv`

**Not derived. Reduced to `HarnessStill`** — one transition instead of every
body, an equation of cache values instead of an invariant, and no reference
to `Prov` or to any child (`machine_all` needs nothing else of the harness
except `hout`, which is built).

Why the rest is not derivable today — two independent reasons, both READ:

1. Every built statement about the translator's WORLDS (`translateRel`,
   `legacyRel`, `harnessRel_of`, `bodyRel`; `Tools/ShippingChildHarness.lean`
   304, `ShippingChildLegacy.lean` 224/234, `ShippingChildBody.lean` 150)
   concludes the fixed invariant `J L D` = `InvV ∧ depth ∧ L.aux (L.val w)`.
   The only freedom is `L.aux`, and a `RefLaws` value must PROVE
   `auxInsert : aux m0 → m0.get? n = none → aux m1 → aux (m1.insert n r)` for
   EVERY `r` (`Tools/ShippingChildInv.lean` 342–343). So `aux` can only be a
   predicate that survives the insert of an arbitrary value: "what was there
   stays" (`SubMap`, par/a-33) is one; "nothing was added", "every added
   entry has a provenance", `Prov` are not. The same holds of `quiet`
   (`cacheSetQ` / `cacheModifyQ` are for every written value, 375–379). I
   looked for an encoding (a pinned map, a "poison" disjunct, a key-set
   restriction) and each fails at exactly this field.
2. The certified translation's soundness (`transition_facts`,
   `Tools/ShippingMachineEntry.lean` 301–325, and what
   `closedBody_kinds_of_run` rests on) is stated on `Returns` / `MReturns`:
   a result without worlds. It shows WHAT the harness returns for a quoted
   body, not that it never reached `childSynthEntry`.

What would discharge `HarnessStill` (not done): either the certified walk
re-stated with worlds for bodies of the fragment (the bodies `machineShape?`
accepts pass `unifiedGateRoot`, `Sparkle/Compiler/Elab.lean` 5170, and
contain no call: the calls are binders `inst{j}`, 5166–5169), or ONE change
to a proof parameter that makes history-carrying invariants ride through
the built development: a RUN-AWARE closure condition,

    auxInsert : aux m0 → m0.get? n = none → aux m1 →
      (the inserted r is the result of a returning run of the entry of n
       from a world with cache m0 to a world with cache m1) → aux (m1.insert n r)

which only WEAKENS what a witness must prove (`aux` is "NOT a law of the
runtime: a proof parameter", 335–340); `child_keeps`
(`Tools/ShippingChildKeeps.lean` 282) has that run in hand at its insert.
It is a Tools-only change (no compiler change), touching `RefLaws`,
`withAux` / `plain`, `child_keeps`, `pin_insert`, `sub_insert` and the tests
that build a `RefLaws`. It does NOT by itself give `HarnessStill` ("nothing
was inserted" is a property of one program, not an invariant); it gives the
alternative: `Prov`-like invariants maintained through opaque code from
per-declaration `EntryOk`. Not proposed as done; a decision for the
integrator.

## 3. PROVED (written) vs. NOT shown

| statement | state |
|---|---|
| `design_prov_of_kids`, `closeInsts_name`, `closeInstsG_name`, `keysIn_*`, `kidOk_mono` | PROVED (written), pure |
| `synthesizeChild_ok`, `child_ok` | PROVED (written), relative to `EntryOk` of the one declaration |
| `mapM_loop_inv`, `mapM_inv` | PROVED (written), generic |
| `closeInstsM_all`, `closeInstsGM_all` (memory children included) | PROVED (written), relative to the callees' `EntryOk` |
| `machine_all` | PROVED (written), relative to `HarnessStill` + callees' `EntryOk`; `hout` built |
| `entryOk_machine` | PROVED (written), relative to `CoreVia`, `HarnessStill`, callees' `EntryOk`, `¬ K c` |
| `entryOk_leaf` | PROVED (written), relative to `EntryStill` + built kid facts |
| `machine_closes_of_entryOk` | PROVED (written), relative to `HarnessStill` (parent) + callees' `EntryOk` |
| `hout_of_data` | PROVED (written) from a BUILT theorem |
| **`HarnessStill`** (per transition) | **NOT shown** (§2) |
| **`CoreVia`** (per declaration) | **NOT shown** (§3.2) |
| **`EntryStill`** (per leaf) | **NOT shown** |
| legacy-route declarations, the translator's instance arms | **NOT shown**, not attempted |

### 3.1 What became of the par/a-33 residuals

* H1 (result provenance): for machine-route declarations DERIVED modulo
  `HarnessStill` / `CoreVia` (the result facts themselves are built).
* the recursion: explicit — `hR : ∀ c', K c' → EntryOk L c' K`, discharged
  bottom-up per declaration tree; no `∀ c`.
* H3 (own key): `keysIn_none` from `KeysIn` and `¬ K c`. It rests on
  `HarnessStill` (a harness that inserted something would break the key
  bound) — that is where the environment's acyclicity went: into "the
  transition has no call" plus a name condition.

### 3.2 `CoreVia` — why it is not written, exactly

It is `Tools.ShippingChildInv.machine_run_of_core` (BUILT) plus four
equations of cache values. READ: `core_reads_inv`
(`Tools/ShippingChildRun.lean` 130–190) returns the world `w3` where
`synthesizeFromConst` starts with `InvV L w3` and `L.dval w3 ≠ 0` but not
`L.val w3 = L.val w`; `synthesizeFromConst_machine_inv` (340–377) returns
the machine run with `L.dval w7 = L.dval w` but not the cache values, and
drops the suffix by `peel_bind` on `MReturns`; `RunsTo.try_finally`
(`Tools/ShippingEntrySoundness.lean` 962–) returns the inner run and drops
the world the `finally` ends in. Every step involved is `Framed` / `Diag` /
a depth write (nested branch: no clear), so the equations follow from
`RefLaws.same` / `sameD` / `depthSet` / `depthModify`. What is needed and
unwritten: (i) `core_reads_inv` with the invariant `InvC ∧ L.val w = mb`
(its `peel_inv` tactic hard-codes the step lemmas: a clone of the tactic and
of `inv_pure` / `inv_framed` / `inv_depthSet`); (ii) a `try_finally` lemma
that also returns the run of the `finally` block; (iii) the machine arm of
`synthesizeFromConst` with worlds (`getEnv`, the log, the
`sparkleSubModuleCache` insert); (iv) the closing premise
(`MachineClosesAt c shape`, a built theorem for the callees concerned) to
turn `r` into `some`. About 120 lines against internals (`EST`, a tactic); I
did not write them blind. It is the next unit and has no conceptual content.

## 4. Task 4 — `mixDeep`: not connected, and what blocks it

`mixDeep → {mid2 → midH → rcH, midH → rcH, cnt}`
(`Tests/Compiler/NoPortsMixDeepTest.lean`). With `K = {mid2, midH, rcH,
cnt}` the chain would be: `entryOk_leaf` for `rcH`, `cnt`;
`entryOk_machine` for `midH` (callee `rcH`), `mid2` (callee `midH`);
`machine_closes_of_entryOk` for `mixDeep` with `hS` =
`machineClosesAtS_of_kids` (BUILT) over the callee list.

Blocked by, precisely:

1. `HarnessStill` for the transitions of `mixDeep`, `mid2`, `midH` and
   `EntryStill` for `rcH`, `cnt` — not derivable today (§2);
2. `CoreVia` for `mid2`, `midH` — derivable, unwritten (§3.2);
3. **the consumer's start world.** `machine_closes_of_entryOk` closes from a
   world whose cache satisfies `Prov`. The endpoint's premise is
   `MachineClosesAt mixDeep`: every `InvW` world of positive depth. Its four
   consumers (`Tools.ShippingKidFacts.kids_runFacts`, `kids_outsCheck`,
   `kids_maskedN`, `kids_designCheck`) call it at the machine synthesis's
   start world inside the core run. That world's cache satisfies `Prov` when
   the run is OUTERMOST (the depth-0 clear: `prov_empty`, then frames —
   which needs `CoreVia`'s depth-0 sibling) — not for a nested start world
   with an arbitrary `InvW` cache, where an entry `mid2 ↦ y` may hold a
   `midH` module other than the cache's (nothing built excludes two real
   compiles of `midH` differing; nothing I can run produces them).

So which endpoint would lose which premise: `mixDeep.machine_design_noPortsNR2`
would lose `MachineClosesAt mixDeep` ONLY in a variant whose start condition
is the depth-0 half of `ChildBnd` (`L.dval w = 0`), with the four consumers
re-stated to take "closes from `Prov` worlds". That NARROWS the endpoint's
start worlds (nested starts are no longer covered) — it is not the removal
of a premise at equal scope, and I do not count it as one. For the full
`ChildBnd` scope the missing piece is an invariant about PRE-EXISTING
entries of nested start worlds, i.e. `Prov` (or its restriction to the
descendants' keys) as part of the start condition — a stronger premise,
which the ruling excludes — or as a proved invariant of every reachable
world, which needs the run-aware `auxInsert` of §2. No test and no endpoint
is written for `mixDeep`.

## 5. Task 3 — the probe (`Tests/Compiler/CacheOwnKeyProbe.lean`, revised)

READ again: `Cannot synthesise <h>: not inlinable and not a hardware module`
is thrown only at `Rec.handleDefinitionUnfold` 6563–6564, after
`tryInlineUnfold` (6300–6333) returned no wire and the module synthesis
6553 threw. `tryInlineUnfold` returns no wire either without an attempt
(`eReduced == e`, 6306/6332–6333: the message then has no `Inline expansion
failed with:` part) or after its `catch` (6313–6331: the part is present,
6557–6562). So that message is what the catch-and-retry path produces on
`cyc2` (the helper's module synthesis fails too: its body is on the cycle)
— unless the unfolding of `cycHelp` was a no-op. The integrator's line
decides it by whether the part is there; I could not see it. The revision:

* prints `detail=<T/F>` for every top;
* adds `cyc4` (`help4 (cyc4 x) x`, `help4` untagged non-recursive `unsafe`)
  and `cyc5` (`help5.{0} PUnit.unit (cyc5 x) x`, `help5` safe with a
  universe parameter) — helpers the FRONT END does not unfold
  (`userDefinition?` 3327–3339: `d.safety == .safe`, `d.levelParams.isEmpty`)
  and whose own module synthesis succeeds; with controls `ctl4`, `ctl5`;
* evidence that the path ran on a cycle: the control returns WITHOUT the
  helper in the cache (it was inlined) and the cycle's cache HOLDS the
  helper (inline failed, caught, retried as a module); or `returned=F` with
  `detail=T`;
* keeps START-before-each-operation (standard error, flushed) and the
  assertions, and adds: THROWS if none of `cyc2`, `cyc4`, `cyc5` shows that
  evidence.

PREDICTED:

    CACHEOWN ctl:  returned=T ownKey=F detail=F depthAfter=1018 keys=[…ctlKid]
    CACHEOWN cyc1: returned=F ownKey=F detail=F depthAfter=1018 keys=[] … depth limit
    CACHEOWN cyc2: returned=F ownKey=F detail=T depthAfter=1018 keys=[] Cannot synthesise …cycHelp… Inline expansion failed with: …
    CACHEOWN cyc3: returned=T ownKey=F detail=F depthAfter=1018 keys=[]
    CACHEOWN ctl4: returned=T ownKey=F … keys=[…ctlKid]
    CACHEOWN cyc4: returned=F ownKey=F … keys=[…help4]
    CACHEOWN RETRY cyc4: control returned=T helper in control=F helper in cycle=T exercised=T
    CACHEOWN ctl5: returned=T ownKey=F … keys=[…ctlKid]
    CACHEOWN cyc5: returned=F ownKey=F … keys=[…help5]
    CACHEOWN RETRY cyc5: … exercised=T
    CACHEOWN RETRY cyc2: returned=F detail=T exercised=T
    CACHEOWN RESULT: 0 violations

Least certain: `ctl4` / `cyc4` (whether `unfoldDefinition?` unfolds an
`unsafe` helper; if not, `helper in control=T` and `cyc2`'s `detail=F`
would have the same cause); whether the entry accepts `help5.{0} PUnit.unit
…` as a module (a non-Signal binder) — if not, `cyc5` shows `detail=T`
instead of the helper in the cache, which also counts. If ALL three show no
evidence the command throws `no cycle exercised the inline catch-and-retry
path`.

## 6. Build queue (integrator)

`lakefile.lean` (not edited):

    lean_lib «Tools.ShippingCacheCoherentCert» where
      roots := #[`Tools.ShippingCacheCoherentCert]

    lean_lib «Tools.ShippingCacheCoherentData» where
      roots := #[`Tools.ShippingCacheCoherentData]

`Tests/AllTests.lean`: nothing to add (the probe stays target-only).

Order: (1) `Tools.ShippingCacheCoherentCert` (imports
`Tools.ShippingCacheCoherentClose`, `Tools.ShippingMachineInstG`);
(2) `Tools.ShippingCacheCoherentData` (imports 1 and
`Tools.ShippingClosedKinds`; one term; independent failure);
(3) `Tests.Compiler.CacheOwnKeyProbe`, alone under `cgrun.sh`; read the
`CACHEOWN` lines on standard error.

## 7. UNVERIFIED, in risk order

1. The probe: `help5.{0} PUnit.unit …` (explicit universe, a non-Signal
   binder); `unsafe def` helpers; run time of `cyc4` / `cyc5` (two attempts
   per level, six levels).
2. `closeInstsGM_all` / `closeInstsM_all`: the `mapM_inv` step functions
   (tactic blocks; `G x` arrives as a beta-redex over a tuple; unification
   of `synthesizeChild ?c` with the mapped function, as `closeInstsM_inv`
   relies on); `rw [hwy, hmy]` in the memory branch.
3. `machine_all`: the three `split at hr` and `rename_i` in the order of
   `synthesizeMachineCertified_inv` (BUILT; `machine_prov` of par/a-33 built
   with the same splits); `rw [hmd] at he` then `cases` / `simp only`.
4. `mapM_loop_inv`: the text of `mapM_loop_hoare` (BUILT) with one more
   conjunct; `by simp at hy` for membership in `[]`.
5. `synthesizeChild_ok`: the text of `synthesizeChild_prov` (BUILT) plus the
   key bound (`get?_insert` + `split`).
6. `design_prov_of_kids`: `rw [e, memModule_design] at hac`; `cases` on
   membership in `[]`.
7. `closeInsts_name` / `closeInstsG_name`: the text of `closeInsts_design`
   (BUILT) ending in `rfl` / `withClockFor_same`.
8. `hout_of_data`: name resolution of `quote`, `inputExpr`, `MachineData`
   under the `open`s copied from `Tools/ShippingClosedKinds.lean`.
9. `entryOk_machine`, `entryOk_leaf`, `machine_closes_of_entryOk`:
   compositions.

## Integrator's build record (2026-10-13)

BUILT on tree `d44199076146295121619dabc963943e05cf64f1` (poc e438076a + these files), cgrun 3 GiB swap 0, each first attempt, worker's files
unchanged: `a34-cert` (exit 0, peak 0.85 GB), `a34-data` (exit 0, 0.21 GB), `a34-probe` (target-only,
exit 0, 0.32 GB), `a34-ax`: synthesizeChild_ok, child_ok, closeInstsM_all, closeInstsGM_all, machine_all,
entryOk_machine, entryOk_leaf, machine_closes_of_entryOk, hout_of_data each
`[propext, Classical.choice, Quot.sound]`.

Probe, as predicted: `cyc2 returned=F detail=T` — the inline catch-and-retry path DID run on the cycle
(the integrator's note in A-cache-coherence-2.md that cyc2 "did not exercise" it was wrong: the message is
the one that path produces); `cyc4` / `cyc5`: `returned=F`, helper in the cycle's cache and not in the
control's, `exercised=T`; `cyc1` depth limit; `cyc3 returned=T ownKey=F`; controls return;
`0 violations`. Five cyclic declarations at one start depth: an observation, not a proof.

STATE: step (b) NOT closed. `EntryOk` is derived for machine-route declarations and leaves only UNDER
`HarnessStill`, `CoreVia`, `EntryStill` (statements, not derived). No endpoint uses any of this; no
endpoint premise changed; `mixDeep` not connected (and a connection restricted to outermost start worlds
would narrow the endpoint, so it is not counted as removing a premise).

# U0 (gen2 type connection): result

Issue `sparkle-gen2-u0-types` (milestone `sparkle-gen2`).
- **Plan:** scripts/gen2/GENERAL_SPEC.md §8.1, approved at d622ad71.
- **Branch:** `par/gen2-spec`.
- **Changes:** new proof and test files (Tools/ShippingGen2*.lean, Tests/Gen2/U0Check.lean) plus their lakefile
  registrations. No production change.

## Builds
| job | head = base | result |
|---|---|---|
| `g2u0-conn-aea8b76d` | aea8b76d | exit 0, 697 jobs: Defs, Consumer, Connect |
| `g2u0-chk-6bd02a3a` | 6bd02a3a | **exit 0, 934 jobs**: Keep, Data, `Tests.Gen2.U0Check`. Log SHA-256 prefix `c9f6cdba84bee144` |
| `g2u0-chk-41528d5b` | — | failed diagnostic: an unopened namespace in the test (Keep and Data built) |
| `g2u0-chk-d30e72f6` | — | failed diagnostic: the shape of the `tmPkg_dataOk` proof |

## Axioms (`#print axioms` in `Tests/Gen2/U0Check.lean`, job `g2u0-chk-6bd02a3a`)
Every root depends only on `[propext, Classical.choice, Quot.sound]`:
- `machine_linkedT_callsServed`;
- `seqFactsRN_of_callDec`;
- `stableA_invAt`;
- `servedRealA_of_servedP`;
- `memFacts_of_memDec`;
- `machineTraceLBX_mono`;
- `keepBody`;
- `tmPkg_dataOk`.

No `sorry` in the new files.

## What is proved
- **Connections:**
  - `machine_linkedT_callsServed`: consumer 2 over `ServedP Q`, with no `hrunN`;
  - `seqFactsRN_of_callDec`: every `SeqFactsRN` conjunct, from `CallDec` plus the served `ShipsAt`;
  - `memFacts_of_memDec`;
  - `servedRealA_of_servedP`, `servedP_mono`, `machineTraceLBX_mono`.
- **The invariant interface:** `stableA_invAt`, `invAt_sv`.
- **G-KEEP-BODY is PROVED** (`Tools/ShippingGen2Keep.lean`, `keepBody : KeepBodyStmt L P Reach`). It was not planned
  as part of U0, but it fell out of the §3.4 binder check. For every `D`, `ChildKeepsInv D → BodyKeepsInv D`: the
  all-outcome keep of every synthesis body, on every route, at `InvAt`.
  - `translate_keepsInv_of_tele` is `translate_keepsP_of_tele` at `InvAt`. The JQP-specific row of §3.4 turned out to
    be an instance of the generic `translate_keepsA`.

## §3.4 binder check: done by instantiation, not by reading
Each "generic (to verify)" component was applied at `I := InvAt L P Reach D` in `keepBody`, and the build accepted it.

| component | binder (as stated) | applied with |
|---|---|---|
| `childEntryA_of_childSynthA` (ChildFrontCP:248) | `StableA O.quiet I`, `∀ w, I w → sv w = some synthesizeChild`, `ChildSynthA O I` | `stableA_invAt`, `invAt_sv`, the hook |
| `canonKeyA` (ChildCanonKeyA:90) | `StableA` | `stableA_invAt` |
| `legacyImplA_of_tele` (ChildLegacyImplA:110) | `StableA`, `T`, `CanonKeyA`, `ChildEntryA` | as above |
| `legacyCachedA_of_impl` (ChildLegacyCachedA:86) | `StableA`, `LegacyImplA` | as above |
| `projFieldNameA` (ChildProjFieldA:106) | `T`, `StableA` | as above |
| `fromConst_frontends_of_handlers` (ChildFrontCP:298) | the handlers, `ChildSynthA O I`, `sv` | as above |
| `legacyTailA_generic` (ChildLegacyTailA:194) | `T`, `StableA`, `RecA O I translate` | `translate_keepsInv_of_tele` |
| `translate_keepsA` (used by `translate_keepsP_of_tele`, ChildPinC:314) | `StableA` and the handlers | as above |

**Still NEW** (G-KEEP-CHILD, Issue `sparkle-gen3` scope): the child entry. `synthesizeChild_tripleP`/`hentryT_of_bodyP`
(ChildPinC:255, :292) are JQP-specific, because they keep the pin across the insertion. For `InvAt` the insertion of
a REACHED name's result needs `IHAt D`; that is `KeepChildStmt`.

## §4.4 R? classification (from the sources)
**Source facts:**
- The compiler checks `outNameOk` on outputs in `machineShape?` (Elab.lean:5084).
- `letsAliasOk` (Tools/ShippingMachineClosesData.lean:157) and `callsOk` (Tools/ShippingCallsShape.lean:106) are
  `Tools`-side checks. No `Sparkle/` file mentions them.

| row | class now | reason / supplier |
|---|---|---|
| `d.ok`, `body_eq`, `init` | E | `GenFacts` fields (generated per declaration) |
| `outNameOk` part of `d.ok` | E, plus derivable from the run | checked by the compiler (Elab.lean:5084) |
| `letsAliasOk` | D | not checked by the compiler. Coverage G-DATA, under G3-GEN (generator soundness, M5) |
| `callsOk kD` | D | as above |
| `outHead` (no output name starts with `i`) | D, **coverage risk** | not checked by the compiler. It exists for the separation from instance names `inst{k}_…` (N1 `hfresh`). A real design with an output named `i…` violates it. That is a counterexample to THIS row, not to FG. The covering alternative is the N1 name lemma (separation by encoding) replacing the row. It is planned in M2-a, not a scope change |
| `ss.length = slots.length` | D (candidate: from `d.ok`, unproved) | in `DataOkB` |
| `outTy` | D (candidate: from `d.ok`, unproved) | in `DataOkB` |
| `hkD`, `hIlen`, `hSL`, `hSlen`, `hLlen`, `hNIn`, `domB` | G, derived from `DataOkB` rows | the C4 lemmas `c_parent_*` (C4ComposedTest:136-165) derive them from `ok`, `callsOk` and `slots` with generic proofs. They are restated over `SrcPkg` in M2-a |
| MemCalleeData kid tables (`argsN`, `fieldOut`, `fieldsNd`, `sepK`, `parent`, `parentD`, `disjD`, `nameIn`, `memT`) | run facts | they concern the served children's modules, so they come from the run (`ServedP` / `memModule`), not from `DataOk`. M2-a |
| `insts_ne`, `fne`, `slotsNe` | CASE | leaf / G-ONEOUT / G-SLOTLESS |

## Concrete `DataOk` and its non-vacuity
- **Definition:** `Tools.ShippingGen2.DataOkB p := ok ∧ letsAliasOk ∧ callsOk kD ∧ ss.length = slots.length ∧ outTy ∧
  outHead`, as a Bool, with `DataOk p := DataOkB p = true` (Tools/ShippingGen2Data.lean).
- **Non-vacuity:** `tmPkg_dataOk : DataOk tmPkg`. `tmPkg` is `topshareM`'s generated package (its `GenFacts` from the
  declaration's own `machine_*` theorems). The proof uses `topshareM_parentData`'s fields and `topshareM_outTy`.
  `DataOk` is therefore satisfiable by a real generated package.
- **Coverage accounting:** each D row needs a G-DATA lemma (every successful run ⇒ the check is true) before M2's
  acceptance, or a covering replacement (`outHead` → the N1 lemma).
  - None is proved in U0.
  - Under the approved rule, a D row without coverage BLOCKS M2's acceptance. It does not narrow FG.

## Not claimed
- `KeepChildStmt`, `ServedShipsStmt`, `StepStmt`, `MemParentStmt`, `LeafStmt`, `T1Stmt`, G-CALLDEC, G-LIFT,
  G-TRANSPORT, G-DATA and every other named gap remain unproved.
- FG is not complete.

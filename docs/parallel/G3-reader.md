# G3 — reader soundness: what exists, what was added, what is left

Worker A, branch `par/g3-reader` (base `9a9f812f`). Audit reference:
`docs/ShippingCompiler-GeneralTheorem-Audit.md` §1–§3, §7 (G3, G6).

**Verification status (integrator, 2026-10-12):** build 1 failed (13 errors in
`Tools.ShippingReaderTerm`); build 2 (commit `1b4fe1bb`) built all three
modules through the protected queue with no change. `readTerm_sound`,
`readTerm_expr_sound`, `machine_body_of_read` depend on `propext`,
`Quot.sound` only. The wildcard gap of §3 is CONFIRMED BY A RUN
(`Tests/Compiler/ReaderWildcardTest.lean`): `unifiedGateBoolBody`,
`unifiedGateRoot` and `mixedGateBoolBody` return `true` on
`Signal.pure.{1} (lit 7) Bool Bool.true`, which is not its quotation, and on
a Bool `mux` over four different domain expressions. What this does NOT give:
the compiler does not run `readTerm`; nothing is proved about the compiler's
recognisers or `machineShape?`; ten node kinds are unread; no completeness.

## 1. The readers, and what kind of object each is

| Reader | Where | Kind | Kernel-reducible? |
|---|---|---|---|
| `gatePeel`, `mixedGatePeel` | `Sparkle/Compiler/Elab.lean` | pure, structural on `Lean.Expr` | yes |
| `gateBody`, `mixedGateBoolBody`, `mixedGateVectorBody` | same | pure, structural, **Bool-valued** | yes |
| `unifiedGateBoolBody` / `unifiedGateBitsBody` (mutual), `unifiedGateRoot`, `unifiedRegisterRoot`, `unifiedMemoryRoot`, `hierGate*`, `hierInst*` | same | pure, structural, **Bool-valued** | yes (slow: `rfl` on one node is run with `maxHeartbeats 1000000` in `ShippingUnifiedExecutionSoundness`) |
| `certifiedShape?`, `mixedCertifiedShape?` | same | pure: peel + the recognisers; return `(binders, body)` with `body` the SAME expression | yes |
| `machineShape?` | same | pure in type (`Option MachineShape`), but calls `partial` functions | **no** |
| `entryConst`, `userInliner` | same | pure in type; `userInliner` calls `partial` (`MachRecUnfold.*`) and the `extern` `==` on `Expr` | no |
| `unq` (term reader of the generator) | `Tools/ShippingMachineCommand.lean` | `partial`, unchecked by design | no |

None of them is monadic: the `RunsTo` / `MReturns` layer is NOT needed for
reader soundness. The reads of the environment (`getConstInfo`, `getEnv`)
are already isolated in `EntryDefines` / `MachineDefines`.

`partial` functions on the path of `machineShape?` (each is opaque to the
kernel, no unfolding equation): `MachTupleIn.packTupleInputs`, `machNorm`,
`machBoolMap`, `machLiftScalarN`, `MachRawSurface.rootFloat`, `…zetaAll`,
`…projChain`, `…prodMatcherArity?`, `machConv`, `machNested`,
`machInstance`, `machInstanceS`, `machChain`, `machLoopBody`,
`machLoopRoot`. Non-`partial` on the same path: `mixedGatePeel`,
`inlFoldNat`, `machRoot`, `machReserve`, `machClose`, `machField`,
`machPack`, `machCanonAp`, `machResults?`, `machOuts?`, `machDom?`, and the
final test `unifiedGateRoot`.

## 2. What an endpoint checks per declaration today

`#machine_endpoint f` (`readMachine` + the generated `Eq.refl`s):

1. `machineShape? false [] entry senv = some shape` — evaluated by compiled
   code in the command; enters the theorem as the premise `MachineDefines`
   (reflection, §3 of the audit).
2. `unq c shape.body = some whole`, split into `let` fields / results / next
   values (`splitLets`, `splitFields`, `unField`) — compiled code, unchecked.
3. `f.machine_body : shape.body = quote dom (inputExpr …) (inputExpr …) packed`
   — `Eq.refl`, kernel. **This is the reader check.**
4. `f.machine_ok : d.ok = true` — `Eq.refl`; one conjunct is
   `d.packed.WF d.kb d.kv d.vw`, the others are layout / binder facts.
5. `f.machine_inits`, `f.machine_writes`, `f.machine_result`,
   `f.machine_source` — `Eq.refl`s between the DECLARATION (a Lean value)
   and `denote` / `eval` of the terms. These are the meaning half (§4).

The gate route is the same shape: `#gate_child` generates `f.gate_peel :
mixedGatePeel value = some (binders, quote … e)` by `rfl`.

## 3. Why "the recogniser accepts ⟹ the body is a quotation" is false as stated

The compiler's recognisers are Bool-valued and match with wildcards. For a
node they pin the head constant and the shape of the argument spine; they do
NOT pin

* the universe levels of any constant (`.const ``…Signal.pure _`);
* the domain argument of a node (`_` in every arm);
* most type arguments (the three `Signal dom T` arguments of an operator,
  the instance's domain).

`quote` writes ONE domain expression in every node and fixed levels. So

    unifiedGateBoolBody kinds
      (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure [.succ .zero]) X)
        (.const ``Bool [])) (.const ``Bool.true [])) = true

for every `X` (read off the definition's second arm; not evaluated), while no
`quote dom bools bits t` has level `succ zero` there; likewise a `mux` whose
three sub-nodes mention three different domain expressions is accepted. Such
bodies are ill-typed, so no declaration has them — but "the declaration's
value is well typed" is not a fact available to the proofs (there is no
typing judgment for `Lean.Expr` in the development, and adding one as a
premise would be a new assumption about every declaration).

**Runnable evidence**: `Tests/Compiler/ReaderWildcardTest.lean` (imports
`Tools.ShippingUnifiedSource` only; needs a `lean_lib` entry or a direct
`lake env lean` run by the integrator). Its `#eval` logs, for
`wildPure (junk 7)` = `Signal.pure.{1} (lit 7) Bool Bool.true` and for a Bool
`mux` over four different "domain" expressions, the values of
`unifiedGateBoolBody #[]`, `unifiedGateRoot #[]`, `mixedGateBoolBody #[]`,
and whether the expression equals its quotation `literalE x true`. Expected
from reading the definitions: recognisers `true`, equality `false`, control
(the real quotation) `true`. NOT RUN by me; the design decision in §6 step 4
should wait for the logged lines (`WILDCARD …`).

Three ways out; the third is what the new files prepare:

1. state reader soundness "up to the unpinned positions" (a relation instead
   of `quote … = body`) and generalise every downstream theorem from `quote`
   to that relation — large, touches the whole Unified / Mixed stack;
2. add well-typedness as a use condition — a new premise, not derivable;
3. make the acceptance test pin what `quote` pins: a reader that RETURNS the
   term and is proved sound, run by the compiler next to (later instead of)
   the Bool recogniser. Then "the run took the certified route" gives the
   term and the equation, for every source.

## 4. Reader soundness has two halves; only one is a Lean theorem

* **Syntactic half** — `reader body = some t → quote … t = body ∧ t.WF …`.
  A statement about `Lean.Expr` only. Provable for every body. Written in
  the new files for the node kinds listed in §5.
* **Meaning half** — "the declaration whose value is `quote … t` IS
  `denote … t`" (`f.machine_source`, `f.machine_writes`, `f.machine_result`;
  for a gate, `rfl` between the declaration and `denote`). Inside Lean this
  cannot be a theorem quantified over `t`: there is no semantics of
  `Lean.Expr` in the logic; the link from an `Expr` to the value it
  elaborates to is the kernel itself. It is true by construction of `quote`
  (one library constant per constructor) and can be (a) kept as a kernel
  check per declaration, with a COVERAGE argument that the check cannot fail
  for a `quote` image (a meta-argument: for each `Term` constructor, the
  quoted node is definitionally the denoted one — one schematic `rfl` per
  constructor), or (b) named in the trust base as "quotation reflects
  denotation". It is not reducible further. The audit's G3 item 2 ("the
  shape's `Term` means the source") is this half; item 3 (source ↔
  `MachineData`) additionally needs the `circuit do` reading (`machConv`,
  `machChain`: `partial`).

So the target for G3 that can be reached is: syntactic half as theorems over
all bodies (this work, to be completed), meaning half as per-declaration
kernel checks whose success is argued once, or as a trusted principle.

## 5. What was added

`Tools/ShippingReaderTerm.lean`, namespace `Tools.ShippingReaderTerm`

* `readTerm : Cfg → Lean.Expr → Option AnyTerm` — total, structural
  recursion on the expression (`go`), one constructor at a time; the node
  kinds are in the non-recursive `readNode` (`read3`, `readCompare`, `read5`,
  `read6`, each a chain of `alt`s of single-kind readers). Every position
  `quote` writes is compared: head constant, levels, domain (`Cfg.isDom`),
  type arguments, instance arguments, literal forms.
* `go_induct` / `readTerm_induct` — the reader's induction principle, for
  any `P : AnyTerm → Lean.Expr → Prop` closed under the leaf reader and
  `readNode`. Proved ONCE, by `induction` on the expression.
* `readTerm_reads`, `readTerm_sound`:

      theorem readTerm_sound (cfg : Cfg) (hs : cfg.Sound) (e : Lean.Expr) (r : AnyTerm)
          (h : readTerm cfg e = some r) :
          quote cfg.dom cfg.bools cfg.bits r.2 = e ∧ r.2.WF cfg.kb cfg.kv cfg.vw

  Covered constructors of `Term`: `boolInput`, `bitsInput`, `boolLit`,
  `bitsLit`, `boolNot`, `mux` (Bool and BitVec), `binary` (8 operators),
  `boolBinary` (3), `compare` (`ult ule slt sle eq`), `boolEq`, `concat`.
  Not read yet: `bitsNum`, `setw`, `slice`, `sliceF`, `zextMap`,
  `concatLitHi`, `concatLitLo`, `appCompare`, `appBool`, `appBool2`.

`Tools/ShippingReaderInputs.lean`, namespace `Tools.ShippingReaderInputs`

* `kindsCfg dom isDom ks` — the configuration for a body under binders of
  kinds `ks`, with `MachineData`'s input numbering; `kindsCfg_sound` proves
  `Cfg.Sound` for it (`posB_rankB`, `posV_rankV`, `widV_rankV`: a binder's
  rank among its sort selects its own position / width).
* domain tests with soundness: `isBVar k`, `isConst n`, and `isExpr dom`
  (any expression, by `Sparkle.Compiler.ExprDecEq.exprDecEq`).
* `readTerm_kinds_sound`, `readTerm_kinds_exists`, and

      theorem readTerm_expr_sound (dom : Lean.Expr) (ks : List MixedGateBinder)
          (e : Lean.Expr) (r : AnyTerm)
          (h : readTerm (kindsCfg dom (isExpr dom) ks) e = some r) :
          quote dom (fun j => inputExpr ks.length ((posB 0 ks).getD j 0))
              (fun j => inputExpr ks.length ((posV 0 ks).getD j 0)) r.2 = e ∧
            r.2.WF (posB 0 ks).length (posV 0 ks).length (fun j => (widV ks).getD j 0)

  whose only hypothesis is the reading.

`Tools/ShippingReaderMachine.lean`, namespace `Tools.ShippingReaderMachine`

* `machine_body_of_read`, `machine_wf_of_read`: for every `MachineData`,
  the endpoint's `hbody` and the `packed.WF` conjunct of `ok` from
  `readTerm … d.shape.body = some ⟨_, d.packed⟩` and three list equations
  on the binder kinds.

## 6. How this replaces the per-declaration checks, and what blocks it

Step by step (each step is the integrator's; none is done here):

1. **Build and repair** the three modules (§7).
2. **Finish the node kinds** (ten left). Each is a `readX` + `readX_sound`
   pair in `ShippingReaderTerm` and one `alt` in `read3` / `read5` /
   `read6`; nothing else changes. The lambda-carrying kinds (`slice`,
   `sliceF`, `zextMap`, the `app*` lifts) need exact destructors for their
   lambda bodies, same style as `bitsBEq?`.
3. **Completeness**: `t.WF … → readTerm cfg (quote … t) = some ⟨s, t⟩`
   (induction on `t`, needs the converse table facts
   `inBoolOf ks (L - 1 - posB[j]) = some j`). With it, every body for which
   an endpoint exists today is accepted by the reader, so step 4 cannot
   narrow the route on them.
4. **Shared-definition change (compiler)**: move the reader to a new small
   file under `Sparkle/Compiler/` (it only needs `Lean.Expr`,
   `MixedGateBinder`, the operator name tables and `exprDecEq`; `Term`
   moves with it or the reader returns a compiler-side copy) and make the
   last test of `machineShape?`

       if unifiedGateRoot kinds body && (readTerm cfg body).isSome then some …

   (and the same in `mixedCertifiedShape?` for the unified disjunct). Then
   `MachineDefines` implies `∃ r, readTerm cfg shape.body = some r` for
   every run on the machine route, and `readTerm_kinds_exists` gives the
   term, the body equation and `WF` — a theorem about every accepted source,
   not a generated check. Must be measured on the corpus
   (`scripts/shipping-coverage`): a body the reader refuses would fall back
   to the legacy route (a narrowing — not allowed; fix the reader instead).
5. **`MachineData` from the reading**: define the data as a function of
   `(shape, r)` (`splitLets` / `splitFields` / `unField` are total already)
   and prove `packLets … (packAll …) = r` for the split. Then
   `f.machine_body` and the `packed.WF` conjunct are no longer generated;
   `machine_body_of_read` / `machine_wf_of_read` discharge them.
6. What stays per declaration after 1–5: the meaning half (§4) and the
   layout conjuncts of `ok` (slot widths, reset values, output names — facts
   about `machReserve` / `machOuts?`, which are total and could be next).

**Blocked, needs a refactor first**: anything about how `shape.body` relates
to the declaration's value (`machNorm`, `machConv`, `machChain`, …:
`partial`). Minimal refactor: the same fuel discipline the translator got
(`fuelFix`) — each of the fifteen `partial` functions takes a `Nat` fuel and
returns `none` at zero; `machineShape?` passes a bound from the expression's
size. Without it there is no unfolding equation and the audit's G4(b) remark
applies verbatim. Even with it, the statement would be the meaning half for
`circuit do` sources, i.e. per-declaration by nature (§4) — so the refactor
buys "the reader's output is determined by total functions" (needed for
steps 4–5 to compose into `MachineDefines`), not a semantic theorem.

## 7. Verification to do

Build, in this order (each needs a `lean_lib` entry in `lakefile.lean`, like
its neighbours — not added here, the lakefile is shared):

    Tools.ShippingReaderTerm      (imports Tools.ShippingUnifiedSource)
    Tools.ShippingReaderInputs    (imports ShippingReaderTerm, ShippingMixedSourceBridge)
    Tools.ShippingReaderMachine   (imports ShippingReaderInputs, ShippingMachineAuto)

Then `#print axioms` on `readTerm_sound`, `readTerm_expr_sound`,
`machine_body_of_read` (expected: `propext`, `Quot.sound`,
`Classical.choice` at most), and a compiled-code smoke test
(`#eval (readTerm (kindsCfg …) shape.body).isSome` on a few machine shapes
whose bodies use only the covered kinds).

Build 1 (integrator, commit `20926e5b`): `Tools.ShippingReaderTerm` failed
with 13 errors of two causes, both repaired in the next commit, still
UNVERIFIED:

* `binOf?_sound` / `boolBinOf?_sound`: `List.find?_some h` elaborated under
  an expected type picked the wrong predicate; now `have hp :=
  List.find?_some h; simpa using hp`.
* seven node lemmas (`readBitsLit`, `readCompare`, `readMuxBits`,
  `readBitsEq`, `readBinary`, `readBoolBinary`, `readConcat`): every peeled
  bind was named `h` again; a later `obtain rfl` (a `subst`) reverted and
  re-introduced the OLDER, shadowed `h`s that mention the substituted
  variable, AFTER the current one, so the final `cases h` hit an old bind
  (hence a scrutinee like `bitVecE? (bitVecE w)`). Now every peeled bind has
  its own name (`hb1`, `hb2`, …) and `split` / `cases` name the one meant.
  The lemmas of the same shape whose old `h` does not mention a substituted
  variable (`readBoolNot`, `readMuxBool`, `readBoolEq`, `readBoolLit`) and
  everything else in the module (destructors, `readNode_sound`,
  `go_induct`, `readTerm_sound`) reported no error in build 1; in the seven
  repaired lemmas the steps AFTER the failing `cases` were never reached, so
  they are untested there (they are the steps that passed in the four
  sibling lemmas). Modules 2 and 3 have not been elaborated at all.

Spots most likely to need a touch (same fix pattern each time):

* `split` on a goal after `revert h; unfold f` — relied on for every
  destructor lemma (`natE?_sound`, …, `readNode_sound`); the alternative
  count and the order of pattern variables for `rename_i` in
  `readNode_sound` are as written in the definitions.
* `rename_i g` after `split at h` on an `if`: assumes the condition is the
  newest inaccessible hypothesis.
* closing steps `exact ⟨rfl, …⟩`: the `rfl` unfolds `quote` on one
  constructor and the `mkAppN` wrappers; if one is slow or fails, replace it
  by `show <the quoted node> = _; rfl` or raise `maxHeartbeats` for that
  lemma.
* `posB_rankB` / `posV_rankV` zero cases are `rfl` (`o + 0` and `l[0]?`
  reduce); fallback `by simp [posB, rankB]`.
* `asBits_some`: `subst hw` then `cases h'`; the cast is `castBits`.
* `go_induct`: the `| _ =>` alternative closes the nine other constructors
  by `none_ne`, which needs `(go cfg (.fvar _)).1` to reduce to `none` by
  `whnf`.

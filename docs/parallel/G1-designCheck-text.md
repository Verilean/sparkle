# G1: `designCheck` — the text conjuncts of the PARENT module (round optfb-4)

Continuation of `docs/parallel/G1-designCheck.md` (round optfb-3), which has
the definition and the classification of the conjuncts.

Status: the Lean files of this round (`Tools/ShippingWidthTables.lean`,
`ShippingNamesStable.lean`, `ShippingNamesNext.lean`,
`ShippingSeqCheckTyped.lean`) were NOT built at the time of writing.
Everything proved this round is PURE (no run). **No text conjunct is derived
from a run yet.**

## Outcome in one table

| Conjunct | Case `checkedOptimize b = b` | Case accepted candidate |
|---|---|---|
| 2 `seqCheck` | reduced (pure, `core_text_same`) to `hA`, `hR` below | open: (D) |
| 3 width tables | reduced (pure, `seqNames_widths`) to `hwn`, `hread` | the same lemma applies to `o`; its two hypotheses on `o` are open |
| 7 `portsMatchB` | hypothesis | hypothesis |

Hypotheses of `core_text_same` / `core_designCheck_same`, all on `b`:

    hwn   : ∀ p ∈ b.wires, sanitizeName p.name = p.name
    hread : ∀ x ∈ seqNames b.body, x ∈ b.wires.map name
    hA    : ∀ l r, assign l r ∈ b.body →
              Decl (wofOf b) l ∧ TypedExpr (weS b) r (weS b l) ∧ ∀ x ∈ refsOf r, Decl (wofOf b) x
    hR    : ∀ o c rk i iv, register o c rk i iv ∈ b.body →
              (∃ k, wofOf b o = some k) ∧ TypedExpr (weS b) i (weS b o) ∧ ∀ x ∈ refsOf i, Decl (wofOf b) x
    -- Decl wof x := sanitizeName x = x ∧ ∃ k, wof x = some k

NONE of the four is derived from the core run in this round.

A fact to keep in view: on the census (`HierBindsCensusTest`) the optimizer
changes every measured real parent (`checkedOptimize b == b` on none). The
case proved here is the fallback case; real parents are in the other one.
`Tests/Compiler/DesignTextTest.lean` logs, per candidate, `same` and the
decidable hypotheses on both `b` and the shipped module (compiled evidence,
nothing asserted).

## The width tables (conjunct 3) — proved, pure

`declWidth m x` (`Sparkle/IR/RegDedup.lean` 172) reads ONLY `m.wires`, by
raw name; `weS m x` reads wires ++ inputs ++ outputs by sanitized name. So
the statement proposed in round optfb-3 needs no `Nodup` and no port
clause, but it needs `x` to be a WIRE:

    declWidth_eq_weS : (∀ p ∈ m.wires, sanitizeName p.name = p.name) →
      x ∈ m.wires.map name → declWidth m x = weOf (moduleWof m) x
    moduleWof_wire   : … → (∀ p ∈ m.wires, p.ty = .bit ∨ ∃ n, p.ty = .bitVector n) →
      x ∈ m.wires.map name → ∃ k, moduleWof m x = some k
    seqNames_widths  : hwn → hread → conjunct 3

No duplicate-freeness: both lookups take the FIRST wire of the name. For a
name that is a port and not a wire the two tables DIFFER (`0` against the
port's width), so `hread` is a real hypothesis. Why it is expected to hold
of a closed machine (read, not proved): the transition's inputs are wires
(`PrintBaseAt.inputWires`, `transitionPortTys_of_run`); `clk` / `rst` are
not in `seqNames` (it lists a register's output and the names of its
input); output ports are assignment targets, which `seqNames` does not list.

## (A) names

* PROVED: `sanitizeName_of_allocated : Allocated s → sanitizeName s = s`
  (`Tools/ShippingNamesStable.lean`; one line over the existing
  `Tools.ShippingSVBridge.sanitizeName_of_clean`).
* PROVED: `sanitizeName_nextName : Allocated s → sanitizeName (nextName s) = nextName s`
  (`Tools/ShippingNamesNext.lean`, via `clean_nextName`; a file of its own
  because its proof evaluates the characters of a string literal).
* `outNameOk` does NOT give stability: it tests the first character (not
  `_`), the prefix (not `next`) and `≠ rst`, `≠ clk`
  (`Sparkle/IR/Machine.lean` 62) — nothing about the other characters. The
  test evaluates `"a'b"` (expected: accepted by `outNameOk`, rewritten by
  the sanitizer). So for the OUTPUT port names (`layout.outs`: the result's
  field names) the residual condition is on the data:

      (d.shape.layout.outs.map (·.name)).all cleanB = true     -- cleanB s = s.all charOk

  decidable per declaration, with `sanitizeName_of_cleanB` (PROVED).
* Input port names: `closeMachine`'s inputs are `t.inputs.take …` ++ `clk`,
  `rst` (`Tools/ShippingMachineCleanup.lean`, `hMi`), and the transition's
  inputs are wires with allocated names — so no condition on the source
  binder names is expected. Not proved for the closed module.

## (B), (C) — where the machine route has them, and where the chain stops

* Instance-free register machines: `f.machine_ships_wired`
  (`Tools/ShippingMachineShipsW.lean` 41; generated in
  `Tools/ShippingMachineCommand.lean` 2600–2642). Its statement ends

      ∀ wof, simpleBody b = false →
        seqCheck wof (weOf wof) (checkedOptimize b).body = true →
        (seqNames (checkedOptimize b).body).all (declWidth … == weOf wof …) = true →
        MachineShips …

  The generator discharges by `decide` FOUR structural premises
  (`insts = []`, a slot, the slot count, the output widths); the "gates
  discharged" are the cleanup / merge / optimizer gates (proved inside
  `machine_ships_wired`). `seqCheck` and the width-table agreement are
  NEITHER derived NOR evaluated in the kernel: they stay antecedents of the
  generated theorem. (Tests evaluate such premises with compiled code,
  `Tools/ShippingPremiseEval.lean` — not re-read this round.) So for
  instance-free machines too the honest status is: a premise.
* Producers of typedness. `TypedExpr`
  (`Tools/ShippingTypedExprSoundness.lean` 23) is produced by the unified
  translator's invariants, and for the machine route's TRANSITION module it
  is exported: `transition_closed` (`Tools/ShippingTransitionClosed.lean`)
  concludes `(∃ ow, PrintBaseAt ow m) ∧ TypedPostReady m` for the
  transition of any well-formed term `e`; `transition_calls_facts`
  (`Tools/ShippingCallsRun.lean`) calls it at the packed term
  `(packLets fs core).2`, so the packed term is covered.
  `TypedPostReady.typed` is `TypedStmts (weOf m) m.body`: every statement
  an assignment with `TypedExpr (weOf m) e n ∧ (weOf m l = n ∨ l = "out")`.
  `PrintBaseAt` has `wireNames` (`Allocated`), `wires` (scalar types),
  `inputWires`. `closeLets_typed` (`Tools/ShippingMachineClose.lean` 749)
  carries `TypedStmts` through `closeLets`.
* Where it stops. `closeMachine_fixed` / `closeMachine_cleanup` /
  `closeMachine_noClkRst` (`Tools/ShippingMachineCleanup.lean`) CONSUME
  `typed` and the names; no theorem was found that CONCLUDES typedness or
  declaredness of the closed machine `closeMachine lay t'` (body
  `B ++ nextAssigns ++ registers ++ outAssigns`, wires
  `t'.wires ++ next wires`: both equations are inside those proofs, `hMb`,
  `hMw`), none for the module after `closeInstsG`, and
  `transition_calls_facts`'s conclusion does not export `TypedPostReady`
  (it has it internally, as `ready`).

So the general statement needs ONE new run-level theorem:

    theorem core_closed_typed (… the hypotheses of core_runFacts …)
        (hclean : (d.shape.layout.outs.map (·.name)).all cleanB = true) :
        hwn ∧ hread ∧ hA ∧ hR            -- of core_text_same, on the full entry's b

Its parts: (1) export `TypedPostReady` and `PrintBaseAt` from
`transition_calls_facts`; (2) a `closeMachine_typed` over the four statement
groups of `hMb` — `B` from `typed` (targets allocated wires), `nextAssigns`
(`fieldRhs w lo width`: a `TypedExpr.slice`; target `nextName p` of the
slot's type: `SlotOk`), `registers` (input `.ref (nextName p)`, output the
slot wire), `outAssigns` (a slice; target an OUTPUT PORT: `Decl` by
`hclean` and the port's type, width by `outTy`); (3) the same through
`closeInstsG` (not read this round); (4) from `weOf` to `weS` on wires by
`declWidth_eq_weS` and `TypedExpr.we_congr` (TypedExprSoundness 150). Not
attempted without a build: it is of the size of
`Tools/ShippingClosedMasked.lean`.

## (D) the accepted candidate — does `refineCheck` give the fragment? NO

Read: `Sparkle/IR/RefineCheck.lean` 40–190. `refineCheck m o = true` has,
for `o`, the conjunct

    rNormBody wo insO [] (seqAssigns o) = some dO          (wo = declWidth o)

i.e. every assignment's right-hand side of `o` is in `rNormE`'s domain.
That is not `seqCheck` / `SF4` membership:

| `seqCheck` asks of `l := r` | `refineCheck`'s conjunct | Verdict |
|---|---|---|
| `sanitizeName l = l`, and of every name in `r` | none mentions a name's characters | missing |
| `wof l = some (we l)` (declared in the emitter's map) | none; `rNormE` of `.ref x` without a definition is `some (.ref x)` whatever `x` is | missing |
| `widthOf we r = we l` | only at a USE of `l`: `rNormE` of `.ref l` asks `we l = widthOf we d` for the normal form `d` of its definition. A wire nobody reads, and every OUTPUT (looked up in `dO` without a width test), are not constrained; and it is about `d`, not `r` | partial |
| `sf4Check r`: operand-width side conditions (`wa == max wa wb ∨ immune`), `shl` shapes, constants of positive width, signed-compare width visibility, slice bounds | `rNormE`: operator in `rBinOk` / `rUnOk`, constants `0 ≤ v < 2^w` (`w = 0` allowed), mux branches of equal width, slices of fitting names; no operand-width condition for binary operators | different domains; neither was shown to imply the other |

And for a module with instances the check is run on `openFlat o …`
(instance statements dropped, ports added) with `declWidth`, not on `o`
with the emitter's table. So (D) does not follow from the check itself.

What (D) needs: `seqCheck (wofOf o') (weS o') o'.body = true` (and
`hwn`, `hread` on `o'`) for `o' = deinline b (optimizeModule b)`. Two ways:
a preservation theorem for the optimizer's rewrites on typed statements
(the scalar route has one for its arms: `checkedOptimize_printCheck`,
`Tools/ShippingSVBridge.lean` 383), or a fallback guard in
`checkedOptimize` (ship `b` when the candidate fails `seqCheck` and the
width tables) — a compiler edit; with it the accepted case would hold by
the guard and conjuncts 2, 3 would rest on `core_closed_typed` alone. A
decision for the user; not made here.

## `portsMatchB` (conjunct 7) — unchanged

Still a hypothesis in both cases. OUTPUT connections: `RunFacts.wid` is the
fact over `declWidth` of the parent wire and the child port's TYPE; moving
it to `weS o w == weS child port` needs `declWidth_eq_weS` on the parent
wire and a second small lemma, NOT written: `moduleWof child port` for a
PORT of the child not shadowed by a wire of the same sanitized name. INPUT
connections: (E) of round optfb-3, unchanged.

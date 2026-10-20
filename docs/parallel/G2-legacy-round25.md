# G2 — worker, round 25 (branch `par/g2-legacy-25`, base `fix/cache-rollback` = `96ad1a24`)

Nothing here was built (no Lean run from a worker). To be folded into
`docs/parallel/G2-legacy.md` as §109–§114.

## 109. Rounds 23–24, the integrator's build (recorded)

Both built unchanged. `FST CLASS`: slice-of-input 39 of 39; composed range =
type-derived range (first component high) 39 of 39; 0 not fitting. All 39 are
`Sparkle.IP.RV32.SoC.SoCState.*` over ONE input port `_gen_s : bitVector
1958` (124 leaves, widths summing to 1958; the type oracle on the binder
type: `bitVector 1958`; on the domain binder: THREW). Slice steps from 2
(`fetchPC`) to 122 (`dMissIsStore`), one wire and one assignment per step.

## 110. Item 1 — does the class have the theorem's shape?

Yes for the top node, by the class's own definition and the samples:

* the class is "the leaf's head is `Signal.fst`" (pass 2 groups by head), so
  the TOP node of each of the 39 is `Signal.fst`; no top `Signal.snd` is in
  it;
* the three sampled chains (`dMissIsStore` depth 122, `aiInputReg` depth 59)
  are `fst.snd.snd.….snd` applied to `<fvar>`: field `k` of the right-nested
  product is `fst (snd^k s)` — what `declare_signal_state` generates. The
  smallest emitted module (`fetchPC`: `_tmp_s_0 = _gen_s[1925:0]; _gen_out =
  _tmp_s_0[1925:1894]; out = _gen_out`) is `fst (snd s)`.

That EVERY node of all 39 is a `Signal.fst` / `Signal.snd` constant down to
the variable is what pass 5 checks (§111); the samples show it for two.

The last field of such a state is `snd^k s` — a top `Signal.snd`. It is not
among the 39, but so that no accessor shape is left out the entry theorem is
now stated with either top node: `Tools/ShippingLegacySemTupleEntry.lean`,
`TopNode` (`fst` / `snd` over a `SubChain`), `topSnd_leaf`, `topNode_leaf`,
`topNode_slice`, `tuple_entry_output`. `fst_entry_output` is kept.

## 111. Item 2 — census pass 5 (`TUPLE CLASS`)

`tupleCheck` on each of the 39, first failing observation reported:
gates; lambdas / `instantiateRevRange` form / distinct variables; binders
(the oracle throws exactly on domain binders; ONE hardware binder, bound as
`bitVector N`); the chain (`chainNodes`): per node the head constant, the
last argument is the application's argument, `fallbackKind = other`,
`translateCoreShape = false` (`NotCore.shape`), the variable occurs in the
node, the oracle on the node's inferred type = `hwTypeFromWidth w`, on the
argument's a width `M` (`bitVector M` under a `Signal.fst`), `0 < w ≤ M`,
innermost `M = N`; Signal-headed result; then THE RUN: the entry is run and
the emitted slice steps (from `out` back to the port) are compared node by
node with `[M-1 : M-w]` (fst) / `[w-1 : 0]` (snd).

What the comparison says about the two run premises: `WireWidthReads` — the
width the arm read was the argument's (else the bounds differ, §106);
`ArgRunsBody` — every node was translated by the body (a cache hit would
drop a step). One run: an observation, not the premise.

Not observable and so not checked: `NotCore.core` (a statement about
`translateCore` for every recursive translator), `HasMappedFVar` in the
run's context (only "the variable occurs"), `ExprHW` through the type CACHE
(`inferType` is used), `InfersNoCatch`.

Lines requested:

1. `TUPLE CLASS: fits N of 39`
2. `TUPLE CLASS, slice steps compared node by node …: K`
3. `TUPLE CLASS, fitting, by top | nodes | fst below the top | binder width: …`
4. `TUPLE CLASS, NOT fitting (n), declaration and first failing observation: …`
5. `TUPLE CLASS, PlainHead's observable part …: Signal.fst b, Signal.snd b`

## 112. Item 3 — one real instance: `SoCState_fetchPC_output`

`Tests/Compiler/LegacySemInstanceTest.lean`. The constant by a name literal
(`socFetchPCName`); binders `socBinders n1 n2 = [(n1, .domain), (n2, .bits
1958)]` with the binder NAMES variables of the statement (the real ones are
hygienic). A corollary of `tuple_entry_output` with `TopNode.fst
(SubChain.snd SubChain.var …) …`: memo hit, or
`RawValueAt 32 … (BitVec.extractLsb' 1894 32 (bits id2 1958)).toNat` — bits
`[1925:1894]` of the packed state, the range the census reads off the
emitted module. The two-step value `extractLsb' (1926 - 32) 32 (extractLsb'
0 1926 v)` is composed by `extract_extract`.

Premises: gates, `htel`, `hbody`, `hdom`, `hs` (oracle `bitVector 1958`),
`plainF` / `plainS`, `hlam`, `hres`, the run, and ONE bundle `hnodes` per
prepared setup: the leaf is `f1 (f2 (fvar))`; `TupleNode` of the snd node at
`(1958, 1926)` and of the fst node at `(1926, 32)`; `ExprHW (f2 x)
(bitVector 1926)`; `ArgRunsBody` for the inner node. The closed name tests
are discharged in the file (`fst_tupleHead`, `snd_tupleHead`, `snd_ne_fst`).

## 113. Item 4 — the SEM0 chain bridge (`Tools/ShippingLegacySemPackedField.lean`)

* `Field s s' lo : Type` — a path (`here`, `fst p`, `snd p`) from the shape
  `s` to a sub-shape `s'` with its low offset; DATA, so that
  `Field.get : Field s s' lo → s.Ty → s'.Ty` is a plain recursive function
  (no cast, no sigma).
* `Field.bound`: `lo + s'.width ≤ s.width`.
* `Field.pack_get` (PROVED modulo the build):
  `(s.pack x).extractLsb' lo s'.width = s'.pack (p.get x)` — induction from
  `pack_fst` / `pack_snd` and `extract_extract`.
* `slice_is_field`, `rawValue_is_field` (PROVED): if `g` is the slice at
  `(lo, s'.width)` and the packed input is `s.pack val`, the entry theorem's
  `RawValueAt … (g packed).toNat` is `RawValueAt … (s'.pack (p.get
  val)).toNat`.
* `OutIsField` — the STATEMENT of the link (a definition, not proved for any
  declaration): for every valuation with `bits x s.width = s.pack val`, `out`
  carries `s'.pack (p.get val)`.

What applying it to a declaration still takes (none in the development):
(1) that the offset `lo` of `topNode_slice` is the offset of the `Field` the
source chain denotes — per node, `M` and `w` are the widths of the payload's
shapes (the census compares these numbers: 39 of 39); (2) that the binder's
payload type is `s.Ty` and the result's `s'.Ty` (the oracle's `whnf` at
transparency `all`); (3) the source denotation: the declaration's Signal at
time `t` is `p.get` of the input Signal at `t` (`Signal.fst = map Prod.fst`),
and the valuation's packed input is `s.pack` of it — `RawValueAt` is
combinational, one environment.

## 114. Spots most likely not to elaborate, in order of risk

1. Census pass 5 (compiled code): `chainNodes` (`let some … ← … | return`,
   `partial`), `tupleCheckCore` (the three-way `match` on `Option HWType`
   with nested `if`s and `let mut`), `firstDiff`, the nested `match`es in the
   `for`.
2. `…PackedField.lean`: `Field.get` (dependent pattern matching with
   `Prod.fst x` on `x : (prod a b).Ty`), the inductions on a `Type`-valued
   family, `rw [PShape.pack_fst a b x]` inside `h2`.
3. The instance: `TopNode.fst (SubChain.snd SubChain.var nd2 hsh) nd1 hS`
   against the stated function index (beta), the literal arithmetic
   (`1926 - 32`, `0 + 1894`) by definitional unfolding, `rw [hids] at H`.
4. `…TupleEntry.lean`: `cases h with` on `TopNode` (a function-valued
   index), `top.pos`.

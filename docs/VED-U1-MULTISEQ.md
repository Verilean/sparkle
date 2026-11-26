# U1 packed result with registers (`Signal d (A × B)` over a `Signal.loop`; sparkle-ved-mo-seq)

Scope: a declaration whose result is a product inside ONE `Signal` (the synthesizer packs it into the single
port `out`, docs/VED-U1-PACKED.md §1) and whose body has registers (`Signal.loop` state).  Before this
unit `#ved_u1_packed` refused such a body at `[packed]` ("registers are not supported"), `#ved_u1` at
`[multi-output]`, the hierarchical entries at `multi-output: H3`.  The statement is the existing
`PackedStmt`; it is not widened.

## 1. Statement

`PackedStmt pc m f := PackCover pc ∧ U1Stmt pc.core m (packedF pc.tbl f) ∧ SlicesStmt pc m f`
(Tools/VedU1Packed.lean) is unchanged.  `PContract` gained two fields, both with the old value as default:
`clkRst : Option (String × String) := none` and `inits : List (String × Int) := []`, and
`PContract.core` passes them to the ordinary `Contract` (it used to hard-code `none` / `[]`).

* For a register-free module the entry fills `none` / `[]`: the contract, the statement and the theorem are the
  ones of before (the probe reads `slices`, `port`, `modName`, `wires` by name and still compares
  `PackedStmt <ved_contract> <ved_mod> <decl>` exactly).
* For a module with registers the entry fills them from the RETURNED module exactly as `contractOf` does for the
  single-port entry: `clkRstOf m`, and `(regsOf m.body).map (name, init)`.  `ShapeCore` then requires the
  module's inputs to end with that clock/reset, every register to use them, and the register initial values to be
  the contract's; `OutputsStmt` is about every arrangement of the body from the state `st0` those values define.
* All projections, their order, widths and port slices are still derived from the declaration's TYPE
  (`OTy.slices`) and checked by `PackCover` before the proof; the slice statement `SlicesStmt` says that on every run
  every slice of `out` equals the declaration's own projection.

## 2. Proof (untrusted script; the kernel checks the result)

`Tools/VedU1MultiSeq.lean` `packedLoopScript`: the loop path's invariant ("register `n` of the module is the
`toNat` of the loop-state component it implements, at the same cycle", by induction on the cycle) over
`packedF tbl f`; `srcOf_packed` turns the module's port into `OTy.packNat` of the declaration's own result.
Pieces that were missing for this scope (each is a new definition or an untrusted tactic, no axiom):

| piece | file | why |
|---|---|---|
| state tuples that do not end in `Unit` | `Tools/VedU1MultiSeqLoop.lean` (`ved_loop_R'`, `ved_loop_gen'`) | `DivState = … × Bool` lost its last register in `stateComps` (7 components for 8 registers); single-output rows built on `bundleAll!` hit it too |
| the step side condition of the loop unfolding for a loop body that is a named definition | `ved_loop_unfold'` | `Signal.loop (dividerLoopBody …)` is not a lambda until its definition is unfolded; with no helper constants the list is empty |
| `Signal op BitVec` instances | `Tools/VedU1MultiSeqLemmas.lean` | inside `Signal.loop fun state => …` a literal operand picks `HSub (Signal _) (BitVec n)`, not `a - Signal.pure b`; the value lemmas of `Tools/VedU1Lemmas.lean` do not match it (`rfl` lemmas) |
| `Signal.fst` / `Signal.snd` unfolded | simp lists | `state.fst.val n` stayed folded, so the loop value was not generalised |
| `OTy.packNat` as a sum | `OTy_packNat_pair` | `|||` of the shifted leaves is opaque to `omega`; every leaf is below its power of two, so it is a sum |
| `x ^^^ (2^k - 1)` as `c - x` | `ved_xor_ones`, `xor_ones` | bit-clear (`a &&& ~~~b`) of a register update |
| leaf-wise closing | `ved_leafwise` | the packed equation is closed one leaf at a time (`a + b = c + d`, `k * x = k * y`) instead of splitting every condition of every field at once |
| simp step budget | `ved_core_simp_big` | `maxSteps` 2 000 000 (the default 100 000 is exceeded by one `simp` over all projections) |

The entry also takes the proof budget of the single-port entry (`withProofBudget`, `withEvalBudget`, runtime
limits are `[proof]` / `[kernel]` refusals, not `[checker]`).

A register-free packed body that the old packed script does not cover (comparisons against constants, wide operands:
R11, R21, R50) is retried with `packedCombScript` (same unfolding and closing, no loop invariant).  The first script is
unchanged, so what it accepted is accepted as before.

## 3. Checks

`Tests/Ved/U1MultiSeqCheck.lean` (lakefile lib, `ved.yml` full job):

* positives: two-register loop with `(BitVec 8 × Bool)`, two 8-bit leaves (same width), three leaves nested right, a
  non-zero initial value; the theorem has exactly the type `PackedStmt <ved_contract> <ved_mod> <decl>`, the contract
  (slices, clock/reset, register names, hand-written initial values) equals one written out in the check, std3 axioms;
* controls, each refused at the named stage and leaving no `ved_*` constant: swapped / exchanged / wrongly offset /
  wrongly sized / missing slice (`[packed]`); outputs swapped inside the module (same widths), a same-width different
  value in one output, one output altered through its register's update, an initial value changed in the module of
  another declaration, a missing projection (module of a two-leaf declaration against a three-leaf one), an initial
  value changed in the returned module itself (`[proof]`).

## 4. Not covered / measured obstacles

See the report of the unit: per row, the first obstacle with its measurement.  In short: (a) bit-mask updates that
need reasoning about `&&&` / `|||` inside `% 2^n` (R13, R14: `mstatus` masks); (b) a closing `omega` over
symbolic products of sign-extended operands (R49); (c) kernel `decide` of `OrderOk` on modules of 300+ statements
exceeds 14 GB (R23, R44); (d) `repeat' split` over FSM controllers with many states exceeds the 8·10⁹ heartbeat
proof budget (R41, R46, R47, R55).

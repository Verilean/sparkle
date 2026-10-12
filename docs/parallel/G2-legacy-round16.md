# G2 — worker B2, round 16 (branch `par/g2-legacy-16`, base `fix/cache-rollback` = `3d0ce864`)

Nothing here was built (no Lean run from a worker). To be folded into
`docs/parallel/G2-legacy.md` as §60–§63.

Task: exclude `InputSkipped` at its source (the `try … catch _ => pure false`
around `inferHWTypeFromSignal` in `bindInputsLegacy`, `Elab.lean` 2135–2138).

## 60. A failure predicate and the failure-reporting inversion

`Returns` / `MReturns` cannot express "threw": they are existence of an
`.ok` outcome. `Tools/ShippingLegacySemThrows.lean` (new) defines the
minimal counterpart, with the same world quantification:

`Throws c ctx s ex` — some run of `c` from `(ctx, s)` ended in
`EST.Out.error ex _`.

Proved: `RetPost.tryCatchThrows` (`RetPost.tryCatch`'s proof with the
failing run kept), `returns_tryCatch_throws` (a returning `try x catch e =>
h e` is a returning `x`, OR `Throws x ctx s ex` with `ex` neither an
interrupt nor a runtime exception AND `h ex` returned — same builder state),
`Throws.bind`, `Throws.pure`.

The side condition "not an interrupt, not a runtime exception" is real:
`Core.tryCatch` rethrows those without running the handler, and the built
proof of `RetPost.tryCatch` already splits on it.

## 61. The premise `hinfT`, and why it is "no catchable failure" and not "never throws"

`InfersNoCatch T` (`Tools/ShippingLegacySemBinderBound.lean`, new): every
failing run of `inferHWTypeFromSignal T` ends in an interrupt or a runtime
exception.

* Same class as `InfersBits T n`: the oracle on ONE type; `InfersBits`
  speaks of its returning runs, `InfersNoCatch` of its failing ones. It is
  not a restatement of the conclusion (it mentions neither the walk nor a
  port).
* "Never throws" would be FALSE of some worlds: `whnf` inside the oracle can
  end in an interrupt or in the heartbeat / recursion-depth runtime
  exception in any run. Those two kinds are exactly what `try … catch` does
  not catch, so the weaker premise is all the walk needs, and it is the one
  that can be true.
* Like `hinf`, it quantifies over every run (every environment a run may
  see). The `hinf EVIDENCE` log observes one returning run on the real type.

## 62. The skip excluded

* `bindInputsLegacy_one_bound` (same file): the premises of
  `bindInputsLegacy_one` plus `InfersNoCatch d0.type`; conclusion: the
  certified walk, no second outcome. The built walk with S4 inverted by
  `returns_tryCatch_throws` (body returned ⇒ `isHWArg = true`; handler ran ⇒
  the body `inferHWTypeFromSignal ty >>= fun _ => pure true` threw a
  catchable exception ⇒ by `Throws.bind` / `Throws.pure` the ORACLE did ⇒
  contradiction with the premise) and the `else` of S5 closed by
  `isHWArg = true`.
* `Tools/ShippingLegacySemEntryBound.lean` (new):
  `one_binder_entry_output_bound` — conclusion `MemoHit ∨ (output statement)`.
* Test: the round-15 theorem kept as `useDbl_output_r15`; new
  `useDbl_output` with `hinfT` and the two-outcome conclusion.

Item 3 (is there another step between "inference returned" and "port
bound"?): no. After `isHWArg = true` the walk calls the oracle again (line
2140) and `bindInputPort` unconditionally (2141). A failure of that second
call is a failure of the walk (not a successful run), so it needs no
premise; its returning run is covered by `hinf`.

## 63. Spots most likely not to elaborate, in order of risk

1. `Throws.bind`: the `split` on `EST.bind`'s `match` in the ERROR case
   (`rename_i e1 w1 heq`, then `heq.trans hrun`) — the built `Returns.bind`
   only uses the ok case of that `split`.
2. `RetPost.tryCatchThrows`: the last line
   `exact (RetPost.of_ok (m := h e) (hh e w w1 hxw hc)) w1` against the goal
   left by `rw [if_neg hc]` (in the built proof: `exact hh e w1`).
3. `returns_tryCatch_throws`: the nine-argument handler function and the
   `show Throws x ctx s e from ⟨…, hthrow⟩`.
4. `bindInputsLegacy_one_bound_raw`: `Throws.bind hthrow` must see the
   `try`'s body as `inferHWTypeFromSignal ty >>= fun _ => pure true` (the
   same shape `Returns.bind hbody` already uses in the built proof).

# DG-SEM P4 — U4E addendum (g5sm-u4): `typedVal_let_congr` is not provable as frozen; `lsrcAt_congr` is proved

**Status: report of a stop, for the reviewer.** Base freeze: `scripts/gen5/DG_SEM_FREEZE_P4.md` rev1 (approved 6d596308). Nothing in the freeze is edited; this file records what the implementation found.
Implementation: `Tools/ShippingGen5SemCall.lean` (U4A–U4D), `Tools/ShippingGen5SemCongr.lean` (U4E), `Tools/ShippingGen5SemMem.lean` (U4F), checks `Tests/Gen5/SemCallCheck.lean`.

## 1. What was found
Freeze §5.2 states `typedVal_let_congr` with the conclusion, for every `q` with `(cleanLets d k)[q]? = some true`,
`(typedVal … bools …).b (nIn+ss+q) = (typedVal … bools' …).b (nIn+ss+q) ∧ ∀ w, (typedVal … bools …).v (nIn+ss+q) w = (typedVal … bools' …).v (nIn+ss+q) w`,
under `hb`/`hv` which constrain the input families only at positions `p < kDOf d + k`.

`typedVal` is `letVal` over `slotVal` over `⟨fun p => (bools p).val t, fun p w => (bits p w).val t⟩`, and `TVal.set p s x` writes only the component of sort `s`
(`.bool` writes `.b`, `.bits w` writes `.v … w`; `Tools/ShippingMachineDenote.lean:68-83`). So at the position `P = nIn+ss+q` of a `let`:
for a `bool` `let` the `.v P w` component is still `(bits P w).val t`, for a `bits` `let` the `.b P` component is still `(bools P).val t`. With `k ≤ insts.length` (the only range
U4F uses) `kDOf d + k ≤ nIn ≤ P`, so `hb`/`hv` say nothing about position `P`, and the two families may differ there. The conjunct about the *off-sort* component is then not implied.
This is an argument from the definitions (reading `typedVal`, `letVal`, `TVal.set`); **no concrete `MachineData` counterexample was constructed or machine-checked**, so this is "the statement as frozen has a conjunct the hypotheses do not imply (by this argument)", not a formal refutation.

## 2. What was done instead (no silent type change)
- `typedVal_let_congr` is **not implemented**; it is not in any file and not counted.
- The sort-aware invariant is proved as new internal lemmas: `AgrAt d T T' p := (K p = some .bool → T.b p = T'.b p) ∧ ∀ w, K p = some (.bits w) → T.v p w = T'.v p w`,
  `partial_agr` (induction over the first `m` lets, accumulator `cleanUpTo d k m`), and
  `typedVal_let_agree : posOk d k (cleanLets d k) p = true → AgrAt d (typedVal … bs vs …) (typedVal … bs' vs' …) p` (needs `d.ok = true`: `LetsTyped` and the `K` conjuncts of `ok`).
- `lsrcAt_congr` is proved **with exactly the frozen statement** (§5.2 second theorem), from `typedVal_let_agree` and `eval_congr_wf`. Its consumer `ext_mem_final` (§5.3) uses only `lsrcAt_congr`; so U4F does not need `typedVal_let_congr`.
- Proposal for the reviewer (a freeze change, therefore not made here): replace the frozen `typedVal_let_congr` by `typedVal_let_agree` in §5.2 (or delete it, since nothing consumes it).

## 3. Not claimed
- This does not change any definition, law, TRUSTED boundary, FG or `GenWF`. `lsrcAt_congr`/`ext_mem_final` still take `d.ok` and (for `ext_mem_final`) `GenWF` as premises; no supplier for them on a real run is claimed (DG-WFCOVER, DG-DATAOF open).
- The argument in §1 is informal; the proved fact is the positive one (§2).

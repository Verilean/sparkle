# Open rulings for the user / reviewer (2026-10-14, after the rulings of the same day were worked)

State: poc 0c64c910 + this document. Tests.AllTests 1344 jobs green. GitHub CI: 0 runs.
Census (ONLY the suite population with generated data): 134 declarations, 133 with a check-free
design-level endpoint; open `mixDeep`. Separate tally "outermost starts": 1 (`mixDeep`; premise `Start0`
NOT ALLOWED by the classifier, not added). Outside that population, unfinished: gate-route parents (no
generated data), the legacy route, the reader (4 of 15 partial functions have a total counterpart, none
wired in), `mixDeep` at nested starts.

1. **J1 fix (C backend, one character class).** A regression of the injective-names commit for `private`
   children in the C simulation / JIT path. Candidate verified in isolation
   (verification-j1-fix-isolated.md): suite green, the six failing rows compile and match the source,
   C text of untagged designs byte-identical. Integrate? (compiler-backend change)
2. **J2–J5 (older C-emitter / `#sim` naming collisions; J-tagged-names.md).** J2 `sparkle_<m>_<verb>`
   ambiguity, J3 module named like a C keyword, J4 module named `jit` — compile errors; J5 `#sim` output
   path by last name component — a SILENT overwrite across files. Fix any of them now, or record only?
3. **Environment capture (verification-env-capture-isolated.md).** The capturing entry exists and is
   verified in isolation; no command uses it. Making gate-route parents' run lemma a statement about what
   the commands run needs the commands switched to it = a re-base of the translator-specific theorems
   (195 lines in 76 files). Options: (a) do the re-base; (b) integrate the capturing entry as a parallel,
   non-command entry and prove `gate_parent_run` for it (clearly scoped); (c) leave open.
4. **Threading siblings of the MachineRan split (G-mixdeep-outermost.md).** 17 theorems that only thread
   the closing were copied into new files (~260 proof lines duplicated). Replace by the same in-place,
   statement-preserving split in five more built files?
5. **Depth cell per process (G-mixdeep-outermost.md §5; by reading, not reproduced).** In the language
   server a cancelled elaboration could overlap a new command, which would then start at depth ≥ 1 without
   a cache clear. Investigate (needs the server) / make the depth and caches per-command (compiler change)
   / record only?
6. **Reader: next units (H-reader-units.md).** Continue with `machLiftScalarN` and the (O)-kind leaves
   (recursion through `instantiate1`), or first do a SWITCH-OVER of the smallest one (`projChain`: replace
   the six `tail` lines by the total definition and drop `partial` — a compiler change that by itself
   removes no endpoint premise)?
7. **Still parked / unchanged:** `RefLaws.auxInsert` branch; corpus pilot (held); `mixDeep` at nested
   starts (needs determinism of the shared descendants' compiles).

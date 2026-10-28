# General-theorem gap table refresh: frozen plan (docs only)

Issue `sparkle-gaps-table` (milestone `sparkle-gaps`).
- **Base:** `poc/roundtrip-proof` db931dd48e9da2dd9eea92ad1e05dfbc2503bea3. C4/C5 are integrated; `Tests.AllTests` exit 0 in job
  `c45-poc-all-db931dd4`.
- **Branch:** `par/gap-table`.
- **Scope:** docs only. No Lean, compiler or test change, and no new theorem claim.

## Why
`docs/ShippingCompiler-GeneralTheorem-Audit.md` §0/§7 is the reference "gap" table, but its status is dated 2026-10-12. Since
then three things have landed in poc:
- the two class-generic theorems C4 `memSharedLeaf_ships` (M shape) and C5 `qSharedLeaf_ships` (Q shape);
- the admissible runtime boundary (`RefLawsAOps`/`AdmCtx`/`JQC`);
- the G3 exact-gap settlement.

The ledger `docs/parallel/open-items-by-kind.md` is dated 2026-10-20. Neither document says which gap each premise of C4/C5
still rests on. The refreshed table answers one question: what stands between C4/C5 as proved at db931dd4 and an
unconditional "every accepted source compiles correctly" statement.

## Output (frozen)
1. **New file `docs/ShippingCompiler-Gaps-2026-10-28.md`, with these sections:**
   - §1 The C4/C5 statements and their premises. There is one row per binder or antecedent of the frozen statements
     (scripts/c3/C4_STATEMENT.lean.txt, scripts/c5/C5_STATEMENT.lean.txt). The columns are:
     - binder;
     - kind (CONTRACT-runtime / CONTRACT-reflection / RUN / INPUT-CONDITION / CLASS-SCOPE);
     - the gap ID it rests on;
     - whether it is proved, discharged or open in poc, with evidence.
   - §2 The gap table: one row per gap G1–G7 and N1, plus one new row G8 = class coverage (see the ID rules). The columns
     are:
     - gap;
     - the 2026-10-12 status, quoted from Audit §0/§7;
     - the status at db931dd4;
     - evidence (theorem name + file + accepted SHA/job);
     - what remains open, stated as a Prop or a named premise;
     - whether C4/C5 depend on it.
   - §3 Not claimed: no CI, no production, no completion of any G row unless the row says PROVED with evidence; the `_sat`
     conclusions remain relative to the premises.
   - §4 Sources: every document and job cited.
2. **One edit to `docs/ShippingCompiler-GeneralTheorem-Audit.md`:** a single line under the §0 heading points to the new file
   as the current status. The 2026-10-12 text stays as history and is not rewritten.

## ID rules (to avoid the existing clashes)
- **G1–G7, N1:** exactly the Audit §7 meanings:
  - G1: output checks are obligations;
  - G2: legacy route;
  - G3: reader soundness / source↔MachineData / generator coverage;
  - G4: fuel/depth;
  - G5: runtime laws (`RefLaws`, now `RefLawsAOps`);
  - G6: final statement shape;
  - G7: printer;
  - N1: name separation.
- **G8 (new):** the class coverage of C4/C5, meaning which compiler-accepted sources are members of `MemSharedLeafParent` /
  `QSharedLeafParent`. It is a new row because C4/C5 made this measurable. Its "remaining" includes the unified M+Q
  class that the reviewer noted as a separate unsatisfied scope.
- **Other namespaces, named with a prefix and never merged into Gk:**
  - SRM-G3 (milestone `sparkle-g3`): `SourceRegsKept`, the exact-gap settlement.
  - The C3/C5 GAP_MAP unit names (G-KID, G-CLOSES, Q-MASK, …).
  - The SRM-G3 row is listed under G3 only as a related, separate item, because C4/C5 do not use it (GAP_MAP: "G3 NOT
    needed for this route").

## Evidence rules
- Every name cited as PROVED must exist at db931dd4. It is checked mechanically: the declaration name is grepped at the
  cited file at db931dd4, and the check is recorded in §4 as a command and its output count. An accepted unit not in poc is
  cited by its branch and SHA and marked "not in poc".
- **Status words:** PROVED (kernel theorem, standard axioms, built), CONDITIONAL (proved relative to named premises,
  which are listed), OPEN, REFUTED (counterexample reproduced, with probe and job), TRUSTED (by design, in the TrustBase
  section), CONTRACT (premise by design).
  - A premise is never called discharged unless a theorem removes it from the binder list.
  - "true on the tested declarations" or measured coverage is written as MEASURED, never PROVED.
- Where two sources disagree, the later accepted review record wins. The disagreement itself is listed in a "corrections"
  sub-list, not silently resolved.
- Status claims come only from reviewed records:
  - Audit §0/§7;
  - open-items-by-kind;
  - the docs/parallel unit records;
  - the scripts/c3, c5 and g3 docs;
  - the C45 manifest;
  - manager issue notes (reviewer acceptance text).

  Nothing is claimed from memory or from job names alone.

## Verification of the docs commit
- **Evidence grep:** a script lists every `name @ file` pair cited as PROVED/CONDITIONAL and greps it at db931dd4; the
  result must be 0 missing. The script lives in the review note and is not committed.
- `git diff --check db931dd4..HEAD` is clean.
- The diff touches only `docs/ShippingCompiler-Gaps-2026-10-28.md`, the one-line Audit pointer and this freeze file.
- No Lean build is needed (no `.lean` change). If the reviewer asks for one, it is an exact-head issue-linked kjob.

## Not in scope
- Proving or re-scoping any gap.
- Choosing the next theorem unit. The table ends with the open rows only; recommendations are left to the user.
- Acceptance of `sparkle-gen` at the two-class scope, which is the user's decision.

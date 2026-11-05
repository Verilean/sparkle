# Decision: pass_ph cannot be proved with only DeclValuePh + RecRulePhU

Background (no prior knowledge needed): `MachRecUnfold.pass` rewrites Lean expressions. Its helper steps call Lean core functions (`instantiateLevelParams`, `Expr.beta`, `instantiate1`) that are C++ externs; Lean's logic knows nothing about their results. The statement `PassPh` (fixed in 0e16378b) assumes only `DeclValuePh` and `RecRulePhU`. In this investigation no route was found to prove it from those; details in `scripts/gen5/RT_PASS_PH_PLAN.md` section 0. Also `pass` now returns `Except String Expr`, so the old statement needs adjusting.

Impact: the S2 leaf blocks inline-compose's removal of its `PassPh` hypothesis (-> U2). Nothing else stops.

Options:
A. Add agreement hypotheses to PassPh: `Inst1Agrees` (already T1L-51), `ReplaceAgrees` (U-1 candidate), a beta-with-args agreement (new T1 candidate). Cost: ledger +1..+2 T1 candidates (uncounted); proof ~500-800 lines. Reversible (hypotheses can later be discharged). Recommended.
B. Keep PassPh as an assumption (FG +1, the old U-3) and prove nothing. Cost: FG +1; zero proof work; against the "prove before assuming" policy.
C. Change the compiler to avoid externs in `pass`: compiler change, user decision, large.
Also: result shape `pass = .ok r -> G r` (needed in all options).
If no decision: Issue stays stopped; no Lean written.

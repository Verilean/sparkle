# VED: decomposition and composition as the basic axis (2026-11-23)

> **Development record, not user documentation; not kept current.** The current description is [docs/VED.md](../../docs/VED.md).

> Historical design record. Describes a design rule recorded on 2026-11-23 (no code), merged with PR #167; it is not kept in step with current `main` (file names, line numbers and option defaults may have moved). Index: [notes/README.md](../README.md); current description: [docs/VED.md](../../docs/VED.md).

User direction, recorded by the reviewer on Issue `sparkle-ved-proof-compose` (comment of 2026-11-23). This file states it as the design rule for VED work. It changes no code, no accepted result and no ledger count.

## The rule

Decomposition and composition theorems are the basic axis of VED development. Making module and input/output boundaries work is not an individual performance fix. Every extension of the checker (a new design shape, a new kind of child, a new statement) is designed in four parts:

1. **Local meaning and contract.** The new piece has its own local semantics and a contract that can be checked on its own. Examples: a child's `U1Stmt` / struct-result statement; `connsOkK` for multi-output children; `fuse_run` for wired circuits.
2. **Connection that reuses the real child theorem.** The parent is connected to the child's actual theorem constant, never to an unfolding of the child's body. Examples: `reg_connect` / `out_connect`; `child_rel_outAt`; `bundle_causal_agree`.
3. **Composition that keeps every guarantee.** The composition preserves widths, every output (coverage, no duplicates), time (causality), initial state and per-instance state. Examples: `WOKb`/`tabW`; `HierShapeK`; `srcOf_prefix`; `loop_append`; `kid_seq_multi`.
4. **DAG sharing from generation onwards.** Expressions and proofs stay shared from the moment they are generated. Examples: memoised `innerRuns`; one kernel Bool per arrangement (`RegsOk`, `ChainOkF`); the DAG memory peel.

Large parents are split internally, into local lemmas per internal wire and per state update. **Users are not required to split their source.**

No step may give back what composition saved. Forbidden in particular:
- a full unfolding before the split;
- re-unfolding a child body;
- copying a child's proof script into the parent;
- returning to one large simp.

## How to measure and decide

- **Measure on two kinds of input:** a representative real-IP row, and a small scaling series (toys of growing size, e.g. C8/C12/C24, K = 2/3/9 circuits). Report three things separately: generation time, kernel checking time, proof size.
- **What is not a precondition:** generalising every feature first, and full CI / the full 327-row measurement. Neither is required before local development.
- **When a large simp or a budget increase seems necessary:** first separate the two possible causes and write down which one it is:
  - (a) an unsupplied local theorem, stated as the full proposition;
  - (b) lost sharing: which term was unshared, and where.

  Then pick the next minimal unit. Do not raise budgets in its place.
- **Unchanged:** the final contract, std3 axioms and the same-artifact guarantee.

## How it applies to the open work

- **`sparkle-ved-compose-connect`** (connect units):
  - each new shape so far has been a local lemma plus generator support behind an option: chains, direct ports, multi-circuit fusion, pure-wiring tops;
  - R246 (connect18) follows the same order: name the slow stage, then supply a local lemma or restore sharing, not a bigger budget.
- **`sparkle-ved-multiout`:**
  - the statement is `U2HRStmtK` / `U2HStmtK` (local contract);
  - the child theorem comes through the struct entry (real child theorem);
  - per-output, causal and port-keyed composition comes from `srcOf_prefix`, `kid_seq_multi` and `keyNetI (portKey)`;
  - the R184 child `wMul` is now handled the same way.
- **`sparkle-ved-nested-children`:** depth-2 children and memories in the top get their own local contract first, then reuse the child theorems.
- **`sparkle-ved-mem-s94`** (memory route, a large single parent):
  - this is the "split the parent's interior into local lemmas" case;
  - each stall so far was diagnosed as either a missing local step or lost sharing (the stage-94 instance check, the stage-97 tree peel, the stage-100 Bool split);
  - the remaining budget gap is reported the same way.

# M2-a `MemParentStmt'`: result

Issue `sparkle-gen2-step-mem` (milestone `sparkle-gen2`).
- **Plan:** scripts/gen2/MEMPARENT_FREEZE.md rev1 (approved for implementation 121c09fe) + A4 option (a) (approved
  3535fa85, §7.1).
- **Branch:** `par/gen2-spec`.
- **Changes:** new proof/test files and lakefile registrations. No production change.

## The final theorem
`Tools.ShippingGen2.memParent_ships (L : Laws mref cref) : MemParentStmt' L` (Tools/ShippingGen2MemShips.lean).
`MemParentStmt'` is the approved text (Tools/ShippingGen2MemParent.lean). Its premises in order, with their kinds:

| # | premise | kind | supplier for the leafM instance |
|---|---|---|---|
| 1 | `MemParentDataOk p` | DATA (5 Bool rows; coverage open, G-DATA) | `lm_dataOk` (`decide`) |
| 2 | `ExtInS p` | generator-output functional equality (generic supply D-GEN/M5) | `leafM_hextB`/`leafM_hext` |
| 3 | `MemOrigin p` | CASE: memory origin + declared width. Width-mismatch and empty-index corners are a coverage obligation | `memOrigin_of_memDec` (Unit) |
| 4-6 | `insts ≠ []`, `instFields ≠ []`, `slots ≠ []` | CASE (covering units: `LeafStmt`, G-ONEOUT, G-SLOTLESS) | `leafM_insts_ne`, `leafM_fne`, `leafM_slotsNe` |
| 7-8 | `AdmCtx`, `JQC L.O (dv w) w` | run context / start world | hypotheses |
| 9-10 | the core run, `hpost` | the run | hypotheses |
| 11 | `MachineDefines` | G3-SHAPE | hypothesis |
| 12 | `MachineTaken` | route evidence of THIS run | hypothesis |
| 13 | `∀ k, MemDec p k …` | G-MEMCALLS (generator per declaration) | `leafM_memcalls` |

**Conclusion:** `∀ n, TopShips p (n + 1) p.decl b raw D ∧ ChildShips p (n + 1) b D`. `ChildShips` is unchanged, and no
hypothesis beyond the frozen ones (after A4) was used.

## Units and builds (each issue-linked, head = base)
| unit | lemma(s) | file | job (exit 0) |
|---|---|---|---|
| C1-C3 | `memInvN`, `memModule_instFree`, `kidsMem_child`, `memKSn_boundedIn` (∀ n), `resetNk_memInvN` | Tools/ShippingGen2MemBd.lean | `g2mp-60536019` |
| C4 | `core_kidsMem_ranAM` (A-form `kidsMem` from the run) | Tools/ShippingGen2MemKids.lean | `g2mp-f695789a` |
| C5 | `hkidW_of_memOrigin`, `memOrigin_of_memDec` | Tools/ShippingGen2MemFacts.lean | `g2mp-81a1b440` |
| defs + C8 | `MemParentDataOk(B)`, `ExtInS`, `MemOrigin`, `MemParentStmt'`; `pkg_memComposedNW` | Tools/ShippingGen2MemParent.lean | `g2mp-378de9ef` |
| data | `MemParentDataOk.rows`, `ok_slotLet`, `ok_outNameOk`, `data_hkD/hIlen/hSL/hSlen/hLlen/hNIn` (no row added) | Tools/ShippingGen2MemData.lean | `g2mp-04a4ea78` |
| TopShips | `memParent_topShips` (consumer 1 at `n+1`; `Bnd` pinned to this run) | Tools/ShippingGen2MemTop.lean | `g2mp-f71c85fd` |
| C6 part 1 | `seqChildRunN_of_composedNW_run` (consumer `seqChildRunN_of_composedCA` with its run boundary replaced by this run's `ComposedNW`, `hpost`, `ExtendsAway`, `NoInstOf`; body unchanged) | Tools/ShippingGen2C6.lean | `g2mp-f225ccfe` |
| C6 part 2 + final | `memParent_childShips`, `memParent_ships` | Tools/ShippingGen2MemShips.lean | `g2mp-56fb4f61` |
| instance | `lm_ships` (leafM, conditional) + axioms | Tests/Gen2/MemParentInstance.lean | **`g2mp-f1a4367f`**, 940 jobs, log SHA-256 prefix `ea5dd5c670d05443` |

**Failed diagnostics** (all name, syntax or proof-shape fixes; none changed a statement):
`g2mp-848dc7d4`, `g2mp-00ae1954`, `g2mp-c06679a2`, `g2mp-02fc2ec6`, `g2mp-4ec5efde`.

**Axioms** (`g2mp-f1a4367f`): `memParent_ships`, `memParent_topShips`, `memParent_childShips`, `memKSn_boundedIn`,
`resetNk_memInvN`, `core_kidsMem_ranAM`, `hkidW_of_memOrigin`, `memOrigin_of_memDec`, `pkg_memComposedNW`,
`seqChildRunN_of_composedNW_run` and `lm_ships` each depend only on `[propext, Classical.choice, Quot.sound]`. No `sorry`.
`Tests/Gen2/MemParentInstance.lean` sets `maxHeartbeats 4000000` at file scope, as the other instance tests do.

## How each consumer premise was supplied (no premise renamed into a supplier)
- **`soundL`:** `genTrace` on `MachineTaken`, then `toLB`.
- **`composed`:** C8, `composedNWRegs_of_composedNW` and `hWd_of_wired`, whose `hierGate` comes from `RunFacts.gate`.
- **`facts`:** `core_runFacts_ranAM`, with `hkidP` from `memKidTNC_facts` and `hkidW` from C5.
- **`Bd`/`Inv`/`hBd`/`hRI`:** `kidsMem` / `memInvN` / C2 / C3. The antecedent `Bd b D` is C4.
- **`Bnd`:** equality to this run's contexts, refs, world, module and design, so consumer 1's quantified runs are
  this run.
- **`ChildShips`:** for every extending `dsn`:
  - `ExtendsAway.1` from `ChildShips`' own `Dc ⊆ dsn` hypothesis;
  - `ExtendsAway.2` and `NoInstOf` from the run's `closeInstsG` (`closeInstsG_acyclic`).

## Not claimed
- **The leafM instance is CONDITIONAL.** The compiler-run premises (7-12) stay hypotheses. It shows package/data
  satisfiability, not that an actual successful run exists.
- **The real-IP instance (quantModule)** is NOT here. It is the required successor `sparkle-gen2-loop-pkg`, and its
  failure blocks M2.
- **Open:** G-MEMCALLS (generic `MemDec`), the generic supply of `ExtInS`, the coverage of `MemParentDataOk`/`MemOrigin`,
  G-CLOSES-FRESH (`outHead`), and every other named gap.
- No M2/T1/FG completion.

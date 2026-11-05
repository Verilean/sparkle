# AUD_UA4_HROW: hrow (T1L-04) from the run, for E-3 / B3

Base 769a6b15. No new premise, law or TRUSTED boundary; one existing premise (`hrow`) is removed from the final theorem.

## Where hrow is used
`auditE3B3_of_t1hyp` (Tools/ShippingGen5AuditE3B3.lean:752) → `dataRes3_of_rows` → `machPrem3_of_t1hyp` → third disjunct of `MachPrem3`
(`instFields = []`, needs `∀ x ∈ instTagged, x.2.child?.isNone`) → used in `q_induct3` (`notag_at hnomemO`, `deepChild_ifaceAO`).
In that branch `hy : RealChildA O c y` is in scope: the run exists.

## Types (new file Tools/ShippingGen5AuditE3B3Run.lean; nothing existing is changed)
```lean
theorem nomemO_of_real (O) {c} {sh : MachineShape}
    (entry : MachineDefines mctx mref cctx cref c sh)
    (closes : ∀ mctx' cctx', AdmCtx O.quiet mctx' cctx' → MachineClosesAtA O mctx' cctx' c sh)
    (hf : sh.instFields = []) {y} (h : RealChildA O c y) :
    ∀ x ∈ sh.instTagged, x.2.child?.isNone = true
-- proof: cases h (run) ; synthesizeCombinational_designL ; runReads_of_run (RR3) → shapeEq ;
--        machineShape?_noMemRow (L2) → noMemRowS sh ; unfold with hf.
def MachPrem3R   -- MachPrem3 with 3rd disjunct `d.shape.instFields = []` in place of the origin row
theorem q_induct3R   -- q_induct3 with MachPrem3R; the origin row from nomemO_of_real O entry closes hfe hy
structure DataRes3R   -- DataRes3 without noMemRow
theorem machPrem3R_of_t1hyp
theorem auditE3B3_of_t1hyp_run
    (H : T1Hyp L P Reach DataOk) (hMemRow) (hLeafAlias) (hA : AdmCtx L.O.quiet mctx cctx)
    (hin) (hsp) (hg) : AuditE3 P Reach L ∧ AuditB3 L P Reach
```
Premises: those of `auditE3B3_of_t1hyp` minus `hrow`. Dependence on the compiler: the final gate of `machineShape?` (Elab.lean, option G'),
via `machineShape?_noMemRow` (Tools/ShippingGen3HrowGate.lean:109), as in `servedShips0_run`.

## Ledger
台帳: FG 94 / T1 54 (今回 0/0). 条件付き台帳: hrow なしで受理されれば FG 92 / T1 55 (hrow ありなら T1 56).
Mutants in the Check are rejected by signature/defeq, not by semantic counterexample. Not built at the time of this commit.

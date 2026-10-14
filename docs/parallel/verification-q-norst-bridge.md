# Worker Q (par/q-1, e354f4f0): obstacle (C) without rst — BUILT as written

Integrator, 2026-10-15. Base poc 0cef27d6. Run `q1` (cgrun, 3 GiB, swap 0, `-j 1`):
`Tools.ShippingRefineNoRst`, `Tools.ShippingHierOptRunHNoRst`, `Tools.ShippingGateOptComb`: exit 0, no fix.
Axioms (`#print axioms`): `refineCheck_transfer_noReg`, `hierRefineCheck_linkedH_noRst`,
`checkedOptimize_comb`, `optKeepsOut_comb`, `optKeepsOut_comb_post` [propext, Classical.choice, Quot.sound].

Where rst was used (worker, by reading): only for register updates — in `refineCheck_step_sound` the reset
facts are read in the register pairing and the register-update width bound; outputs and assignments never
read it; `refineCheck_run_sound` / `refineCheck_transfer` / `hierRefineCheck_linkedH` only pass it down.
So for register-free modules it is irrelevant.

What is proved: `refineCheck_transfer_noReg` (any cycles, any start states, `seqRegs m = []`, no rst premise);
`hierRefineCheck_linkedH_noRst`; `checkedOptimize_comb` (from `hierGate b`: the optimizer returns `b` or a
module accepted by the compiler's own `hierRefineCheck` — derived from the returned module, not assumed);
`optKeepsOut_comb` / `optKeepsOut_comb_post` — obstacle (C) `OptKeepsOut ms b "out"` for comb bodies.
Premises outside ALLOWED: `combOptSide ms b = true` (decidable, checker-style, NOT run by the compiler):
`hierGate`, `linkedWF` of `b` and of `checkedOptimize b`, instance-name Nodup in both, `noSelfRead`,
`outsExtracted`, `kidsLocal`, `hierTyped` — the machine route's `shipsHierHCheck` minus `hierBinds` and minus
`rst ∈ inputs`, plus `b`'s `linkedWF` and `hierGate`. Not yet wired into the seven `…_gate_designSV`.

# Open rulings for the user / reviewer (2026-10-13, night)

Nothing below is implemented on `poc/roundtrip-proof` beyond what each item says. Each item names the
record that carries the evidence. GitHub CI has 0 runs for these heads.

## 1. `mixDeep` at its present scope (callees sharing a descendant)

State: `mixDeep_closes_outermost` is built (11a2ee8f): at OUTERMOST starts the closing succeeds, chain
initial → preserved → consumed with no underived hypothesis. The endpoint
`mixDeep.machine_design_noPortsNR2` still carries `MachineClosesAt mixDeep` (every invariant world of
positive depth). That premise reduces to determinism of the shared descendants' compiles
(`machineClosesAt_of_det`, e6f68394); determinism is neither proved nor refuted for `rcH`, `cnt`, `midH`,
`mid2`; the "no repeated subterm" side condition is measured FALSE for `mid2` (202093d6).
Choose (docs/parallel/A-det-decision.md):
* option 1 — a value law for the run-local translation cache (`RefLawsX`, `ChildBndX`): EXTENDS the
  trusted boundary; still needs a relational two-run walk;
* option 3 — a NEW endpoint form at outermost starts; existing endpoint and premise unchanged; nested
  starts stay open (worker's recommendation);
* or leave `mixDeep` open.

## 2. Finding I — stale single-output instance cache (legacy route)

State: measured on a constructed state only (e6f68394, `SingleOutStaleProbe`: the same declaration compiles
to two different modules, instances 1 vs 0). By reading (eight cases, docs/parallel/I-singleout-stale.md
on branch `fix/singleout-nested`) no real compile reaches it. A fix proposal exists on that branch
(reset the cache at nested entries and restore it, the F/G pattern; ~15 lines of `Elab.lean` + three proof
files); it is being built in the isolated worktree only.
Choose: integrate the fix (compiler change) / keep as a recorded finding.

## 3. `RefLaws.auxInsert` run-aware (branch `par/a-35-aux`, 8b266634)

State: written, NOT built, NOT integrated. Adds one premise to a field of the structure under `ChildBnd`
(every old witness still works) and replaces one audit check (`lawAudit`). By the worker's own reading it
does not unblock `mixDeep`. Default: stays parked.

## 4. BOUNDARY FINDING — no law about the environment across one run

State (docs/parallel/B-slotless-parents-2.md on branch `par/b-37`, written, not built): `RefLaws` tracks
the child cache, the synthesis ref, the depth and quietness; it has NO environment component and no law
relating two `getEnv` reads of one run. Every existing reflection (`EntryDefines`, `MachineDefines`, the
S6 `HardwareTagged`) is stated for every world's read, so constancy was never needed. The gate-route
PARENT (a slotless parent of combinational children, e.g. `parentUse`, `parentMix`) is the first place
where a fact read at the entry (the callee is tagged `@[hardware_module]`) is needed at a LATER read (the
instance arm reads the environment again). So the design-level endpoint for that class cannot be derived.
Choose:
* a law `eval : World → Environment` with `getEnv` returning it and every frame law keeping it — a change
  to the trusted law bundle and to ~76 `Keeps` proofs;
* a world-universal reflection of the gate's reading (the gate analogue of `MachineDefines`) — a new
  premise form;
* a compiler change so the instance arm uses the entry's environment;
* or leave the class open.
Also note: the S6 instance theorems assume `SubSynthDefines` (the child synthesis returns one pinned pair
in every world) — not a fact about the run, not ALLOWED, and false in general for the same reason as
Finding I; the class must be re-proved world-aware (calculus written on `par/b-37`, unbuilt).

## 5. The corpus

State: the built test universe is nearly saturated (census of the AllTests environment: 129 declarations
with generated data, 128 with a check-free design-level endpoint; the gate-route parents of item 4 have no
generated data and are NOT in that count). Tooling for running the design-level generators on corpus
files is written (branch `par/b-36`, unbuilt): serial, one cgrun job per file, resumable, mandatory file
list, a two-file self-test. Standing instruction: no full-corpus rerun.
Choose: allow a pilot on 5–10 named corpus files / not yet.

## 6. Injective module names — residual checks (b7dc0ec4)

`$` in identifiers (tagged names: `private` declarations, odd names) is accepted by iverilog; NOT checked
under yosys, the C JIT, Verilator. Emitted text compared on a 28-file sample only.
Choose: which external tools must accept the tagged names before this is considered closed.

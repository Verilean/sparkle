# `GateDefines` — a separate, gate-only reflection class (documentation per ruling 2026-10-15)

Integrator, 2026-10-15, poc after 3b7fc95d. Ruling (reviewer, 2026-10-15): `GateDefines` MAY be adopted as a
SEPARATE gate-only explicit reflection class, with its own tally and audit. The machine-route list
(`MachineDefines`, …) is NOT widened, and no machine-route count changes because of it. Being implied by the
five round-1 premises (`gateDefines_of_entry`) is NOT evidence that it is equivalent to, or no stronger than,
the original boundary. All-input GC stays open. No runtime law and no axiom is added.

## 1. Definition (Tools/ShippingGateDefines.lean:72)

    def GateDefines mctx mref cctx cref declName bs body : Prop :=
      ∀ w1 ci w2 w5 envR w6,
        RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
        RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
        ∃ dv, entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)
                = .defnInfo dv ∧
              certifiedShape? false [] (.defnInfo dv) = none ∧
              mixedCertifiedShape? false [] (.defnInfo dv) (instancePredicate envR) = some (bs, body)

## 2. Quantification range
* Every returning run of `getConstInfo declName` (any start world `w1`, result `ci`) and, INDEPENDENTLY, every
  returning run of `getEnv` (any world `w5`, result `envR`), in the same Meta/Core references. The two reads
  are not tied to each other or to a particular run of the entry: the premise asks the verdict for every
  pair (ci, envR) these reads can return.
* Context independence: `GateDefines.ctx` (the contexts `mctx`, `cctx` do not matter, as for
  `MachineDefines.ctx`).
* What it does NOT say: nothing about the translator, the cache, the emitted module or the source semantics
  (compiler correctness is proved separately, in the cone / design theorems that take it as a binder).

## 3. Captured environment
Since environment capture (a) (c3176ef1) the entry reads the environment ONCE and uses that read for the
instance arm. The gate-parent theorems instantiate `GateDefines` at the entry's own `getConstInfo` / `getEnv`
runs (`gate_pred`, `gate_cone_runG*`); `envR` in their conclusions IS the entry's captured environment.

## 4. Reader verdict
Under `envR`: the entry constant is a definition; the FIRST gate (`certifiedShape?`) refuses it; the MIXED
gate accepts it with the instance predicate `instancePredicate envR`, returning binders `bs` and the peeled
body `body`. The theorems additionally use pure per-declaration facts (`MixedGateSel` / `GateLeafSel` — which
disjunct accepts — decided by `rfl`), not part of the premise.

## 5. Correspondence with the source value
`body` is the reflected constant the theorems are instantiated at (`parentMixBody` etc.). Its relation to the
declaration's value is checked per declaration by kernel `rfl`: `mixedGatePeel <decl>Value = some (bs, body)`
(round 8 test files; `wrapAdd_peel` example), where `<decl>Value` is the reflected declaration value
(`#def_decl_value`). The source meaning of the parent is computed from `body` (`quote` / `Meaning`), and the
observation theorems compare the emitted run with the Lean function's `.val` at each cycle.

## 6. Non-vacuity — MEASURED in a real environment (probe `Tests/Compiler/GateDefinesProbe.lean`)
For the seven gate parents, the probe evaluates the read of §1 once in the probe file's elaboration
environment (`getEnv` / `getConstInfo` of a command there) and compares with the reflected `(bs, body)`:

    GATEDEF …parentUse:      defn=true first=none mixed=some binders==true body==true
    GATEDEF …wrapAdd:        defn=true first=none mixed=some binders==true body==true
    GATEDEF …parentMix:      defn=true first=none mixed=some binders==true body==true
    GATEDEF …parentTwoCalls: defn=true first=none mixed=some binders==true body==true
    GATEDEF …parentRepeat:   defn=true first=none mixed=some binders==true body==true
    GATEDEF …parentCmp:      defn=true first=none mixed=some binders==true body==true
    GATEDEF …parentNested:   defn=true first=none mixed=some binders==true body==true

Run `gdprobe` (cgrun, 3 GiB, swap 0, `-j 1`): exit 0, peak 0.37 GB. This is evidence that the premise is
SATISFIED for that environment (measured, not proved); it says nothing about every environment a `getEnv`
run could return (the premise's quantification), which is the reflection assumption itself.

## 7. Generation range
There is NO generator for `GateDefines` yet (no `#gate_*` command emits it as a binder of a generated
endpoint, unlike `MachineDefines`). The seven parents' theorems carry it as a hand-written binder. Range of
the hand-written theorems: instance-root / cone gate parents whose body uses leaves, literals, binary,
compare, Bool ops, both muxes, and instance calls (also with instance arguments), with ONE first-gate callee
(`childAdd`), domain-carrying calls. Not covered: `wrapPick` (domain-free call; Meaning extension ruled
allowed, in progress), callees that are not first-gate children, setw / slices / concats.

## 8. Tally (separate kind)
Gate-route parents are tallied separately from the machine-route census, with columns: existence-only
design statement / all-run design statement / remaining conditions / target-only vs in suite. Current state:
seven parents EXISTENCE (`…_gate_designSVN3`) and ALL-RUN (`…_gate_designSVall`, 3312f5a4) at the design
level, all target-only; remaining: `GateDefines` (this class), `DesignSideR` (run-level bounds), binder-id
Nodup not stated; differences from `ships_design_svN_all` listed in verification-n-gate-parent-run.md.

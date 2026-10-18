# Memory placeholder names vs. declared hardware modules (`MemR1` audit, reviewer 2026-10-18 item 3)

Integrator, 2026-10-18, poc after 3a1938a3. Compiler UNCHANGED (the proposed fix below needs approval: an
edit of `Sparkle/Compiler/Elab.lean` was refused by the session's permission policy, and no workaround was tried).

## 1. Where the name is made and consumed

* Made: memory arm of `machConv` (Elab.lean ~3950): `machInstance senv env (memChildName combo aw dw)
  [.domain, .bits aw, .bits dw, .bool, .bits aw] (.bits dw) …`, then `instStruct := true`.
  `memChildName combo aw dw = SparkleMem.{combo|sync}.<aw>.<dw>` with two NUMERIC components (MachMemory.lean 42).
* Deduplicated: `machInstance` merges a call with an earlier entry of the same `(c, js)` (name and argument lets).
* Consumed: `closeInstsGM` (Elab.lean 5213–5217): `match memChild? c with | some md => pure md | none => synth c`
  — by NAME, without the environment. `closeInstsM` (used when `instFields = []`) synthesises every entry.
  The choice between them: `synthesizeMachineCertified`, `shape.instFields.isEmpty`.

Source syntax cannot produce a numeric name component; `addDecl` (metaprogramming) can.

## 2. Collision example (MEASURED, `Tests/Compiler/MemNameCollisionProbe.lean`, runs `mc2`, `mc4`, 3 GiB, swap 0, `-j 1`, exit 0)

`fakeSrc` has the memory's interface (`wa wd we ra`, result `BitVec 8`) but computes `wd + 1`. The probe copies it to
`SparkleMem.sync.4.8`, tags it `@[hardware_module]`, and makes parents by replacing `fakeSrc` in a control parent.

| parent | closing | certified route instances | legacy route (`certifiedFrontEnd := false`) |
|---|---|---|---|
| `ctlParent` (combo memory 4/8 + `fakeSrc`) | GM | `SparkleMem_combo_4_8`, `…fakeSrc` | `…fakeSrc` (memory inline) |
| `collParent` (combo memory 4/8 + call of `SparkleMem.sync.4.8`) | GM | `SparkleMem_combo_4_8`, **`SparkleMem_sync_4_8`** | the declaration's own module |
| `ctlPlain` (`fakeSrc` only) | M | `…fakeSrc` | `…fakeSrc` |
| `collPlain` (call of `SparkleMem.sync.4.8` only) | M | the declaration's own module | the same |

`collParent`'s certified output instantiates a synchronous MEMORY where the source calls a function computing `wd + 1`:
a MISCOMPILE on the certified route. Legacy and the M closing are correct.

`MemR1 (structEnv env)` HOLDS in that environment for `SparkleMem.sync.4.8` (result `.bits 8 = .bits dw`): `MemR1` is
not the property that guards the emitted child. It is FALSE in a real environment too: the probe declares
`SparkleMem.sync.4.16` with result `BitVec 8` (signature printed: `([bits 4, bits 8, bool, bits 4], bits 8)`, while
`MemR1` needs `bits 16`). Abstract form: `Tools.ShippingMemDispatch.not_memR1_all` (no axioms). So `MemR1` cannot be
derived for arbitrary environments, and no universal no-collision assumption is added.

## 3. Proposed scoped fix (NOT applied; needs approval)

In `machineShape?`, after `if !allowInsts && !st.insts.isEmpty then none else`:

```lean
    -- a call entry under a memory placeholder name that also names a
    -- `@[hardware_module]` (only metaprogramming can make one): the general
    -- closing would build the memory module for it (`closeInstsGM`), so the
    -- parent is not read (`memSigClash`)
    if st.instStruct && !st.instFields.isEmpty && st.insts.any (fun i => memSigClash senv i.1) then
      none else
```

with, before `machineShape?`,

```lean
def memSigClash (senv : StructEnv) (c : Name) : Bool :=
  (Sparkle.Compiler.MachMemory.memChild? c).isSome && ((senv.inst c).isSome || (senv.instS c).isSome)
```

Effect: only parents closed by `closeInstsGM` that have an entry whose name is a memory placeholder AND has a signature
leave the machine route; they take the legacy route (the existing `none` path of `machineShape?`). On `collParent` the
legacy output is the correct one (table above). Parents closed by `closeInstsM` and every parent without such a name are
untouched. Theorem statements that take `machineShape? … = some sp` keep their meaning; the five proofs that unfold
`machineShape?` (`ShippingShapeDecomp`, `ShippingMachineShapeUnfold`, `ShippingReaderOutNames`, `ShippingReaderOutsInv`,
`ShippingCallWidthsEntry`) walk `if … then none else` lines generically (`ite_none_inv`) and are expected to need no
change; this is unverified until the rebuild. The fuel candidate copies `machineShape?`; its guarded form is
`machineShapeFG` (below) and the drift check would report `machineShape?` as changed.

What it gives up: a GM parent with a REAL memory whose placeholder name collides with a signature-bearing declaration
(metaprogramming only) leaves the machine route as well, although the memory alone was built correctly. That parent is
accepted by legacy in the probe's case; that legacy accepts EVERY such parent is not proved. The alternative without any
route change needs memory provenance in `MachineShape` (a new field read by `closeInstsGM`, and dedup keyed on it) — a
larger compiler change touching the reader copies and `OldEqV`.

## 4. What is proved (about the guarded MODEL; `Tools/ShippingMemDispatch.lean`, run `md1` exit 0, axioms run `ax18`)

* `machineShapeG?` = `machineShape?` then the guard `shapeClash` (the proposed condition on the returned shape:
  `instFields ≠ []` and some entry with `memSigClash`).
* `gmChoice` (= `closeInstsGM`'s per-entry choice), `gmChoice_mem`: a memory-origin entry gets `memModule combo aw dw`.
* `machineShapeG_dispatch`: under the guard, in a GM shape, an entry whose callee has a signature
  (`senv.inst` or `senv.instS` some — ordinary or structure call) gets `synth c`, the declaration's own compile.
* `machineShapeG_mem_noSig`: under the guard, a memory placeholder entry of a GM shape has NO signature, so `R1` holds
  for it without `MemR1`.
* `not_memR1_all` (no axioms); `machineShapeFG`, `machineShapeFG_of`, `machineShapeFG_out` (candidate, OUT preserved).

Axioms: [propext, Classical.choice, Quot.sound] except `not_memR1_all` (none).

Not proved: that the `senv` the reader used is the environment `closeInstsGM` runs in (one `MetaM` run, captured
environment — runtime fact); legacy acceptance of the refused parents; anything about the compiler before the fix is
applied (until then the miscompile stands for GM parents calling a declaration under a placeholder name).

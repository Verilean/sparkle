# S-DISP — child dispatch / cache / output selection audit (reviewer milestone 2)

Worker S-DISP, branch `par/s-disp`, from poc 3a1938a3. WRITTEN, NOT BUILT. Line numbers: `Sparkle/Compiler/Elab.lean`
(E), `Sparkle/IR/Machine.lean` (M), `Sparkle/IR/MachineInstG.lean` (MG) at 3a1938a3.

## 1. Path from a call entry `(c, js, r)` to the child module the closing uses

| step | code | what happens | modelled in Lean (file : theorem) |
|---|---|---|---|
| 1. entry recorded | E 5059 `machineShape?` (insts at 5182, `instFields` 5183) | the parent's reader pushes `(c, js, res)` to `shape.insts`; `instFields` only for a structure result | parent reflection `MachineDefines` (ShippingMachineEntry 2263); decomposition `machineShape?_decomp` (ShippingShapeDecomp 71) |
| 2. closing chosen | E 5231–5245 `synthesizeMachineCertified` | `instFields = []` → `closeInstsM`, otherwise `closeInstsGM` | ShippingChildRun `synthesizeMachineCertified_runs` / `_inv`; `CloseCalls` (ShippingMachineEntry 930) |
| 3. child entry read | E 5195 / 5212 `sparkleChildSynth.get` | the IO ref, set ONCE at E 8913 to `synthesizeChild` | `SynthAt` / `InvV` (ShippingChildInv 443, 504); `synthRead` (ShippingChildRun 265) |
| 4. memory callee | E 5214–5217 (GM only) | `MachMemory.memChild? c = some md` → the child is BUILT, never compiled | `MemChildren` (ShippingMachineEntry 864); `closeInstsGM_inv` (ShippingChildRun 271) |
| 5. cache | E 8908–8912 `synthesizeChild` | hit in `sparkleChildCache` (E 1031, keyed by NAME, cleared at depth 0, E 5520) returns the stored result; miss runs `synthesizeCombinational c` and inserts it | `RealChild` / `CacheInv` (ShippingChildInv 451, 462); `synthesizeChild_inv` (ShippingChildRun 201): a hit or a miss returns a `RealChild c y` |
| 6. full entry of the child | E 5571 `synthesizeCombinationalWith` → `synthesizeCombinationalCoreWith` (E 5402) | depth/caches saved, `doSynth` (E 5545–5552): `getConstInfo c`, `getEnv`, then `synthesizeFromConst … (entryConst … ci (instancePredicate env) (userInliner env) (structEnv env))`; afterwards zero-width cleanup + `mergeChecked` | `synthesizeCombinational_parts` (ShippingGateChildComb 139); `core_reads_inv` (ShippingChildRun 132) |
| 7. WHICH constant is compiled | E 5251–5264 `entryConst` | the declared `ci`, or `inlinedConst (userInliner env) ci` exactly when `ci` misses both certified gates and the unfolding hits one or is a machine shape | `entryConst_cases`, `entryConst_machine` (ShippingEntrySoundness 1065, 1074); `MachineDefines` pins the machine shape OF THE ENTRY CONSTANT |
| 8. the unfolding's type | E 3408–3410 `inlinedConst` | `.defnInfo d ↦ .defnInfo { d with value := inl d.value, type := inl d.type }` — the TYPE is rewritten too | `inlinedConst_defn` (NEW, ShippingCallWidthsChildReal) |
| 9. child's shape / outs | E 5267 `synthesizeFromConst` → machine branch → `synthesizeMachineCertified` → `closeMachine` | the child's module outputs are `closeMachine`'s = the shape's `layout.outs` ports (kept by cleanup / merge) | leaf: `leaf_run_outputs` / `leaf_real_outTys` (ShippingChildIfaceTy 63, 177): `ChildOutTys sc.layout.outs y.1` |
| 10. port selection | `closeInsts` (M 396): `instStmt` (M 272) takes the ONLY output `let [outP] := mc.outputs`; `closeInstsG` (MG 115): `stmtsG` groups identical calls (`callGroups`, key = child module name + args) and connects field `fields.getD k ""` (= `instFields[k]`) of `mc := moduleByName d'.modules children[k0].1.name`; `closeInstsG` checks every child's module is found by its name as itself | `closeInstsG_calls` (ShippingMachineInstG 307), `closeInstsG_design` (ShippingCacheCoherentClose 92); width side: `callWidthsStrict` / `hkidW_strict` (ShippingCallWidthsStrict) |

The closing's `nDecl` is `binders.length - insts.length - slots.length - lets` (E 5202 / 5220) =
`closingNDecl` (ShippingCallWidthsEntry); the entry's binder is `binders[nDecl + k]`.

## 2. What `kidOuts k` must equal

The consumers (`hkidW_strict`, `hkidW_of_data`, `core_portsMatch_raw_leaf`) need `hkidT`: for every `RealChild
(insts[k]).1 y`, `ChildOutTys (kidOuts k) y.1`. For the emitted child that holds with
`kidOuts k = sc.layout.outs` where `sc` is the shape with `MachineDefines (insts[k]).1 sc`, i.e.
`machineShape? false [] (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)) … = some sc`
for the `ci` the callee's own entry read — the possibly UNFOLDED constant. The existing real chain already uses
exactly this (`LeafKid.entry`, `kidOuts := fun k => (kid k).shape.layout.outs`, ShippingPortsMatchRawLeaf), with
`callWidthsOk` decided per pair.

`ChildLinkF` (ShippingCallWidthsEntryFH) instead links SOME `dC` through the candidate `machineShapeF`; `hkid = rfl`
only matches `kidOuts` to that model. Nothing relates `dC` to the entry constant, nor the candidate result to
`MachineDefines`' shape (that is O1 + O2 for the child).

## 3. P5

`ResC` is `machResultKind? dE.type = some res` for the constant the shape was read from. `…FR1._declared`
(`resC_of_declared`) proves it for the DECLARED constant. For the entry constant:

* branch `entryConst … ci … = ci`: the declared kind (`ResDeclAt`, same style as `EnvDefines`);
* branch unfolded: `dE.type = userInliner env dD.type` (`inlinedConst_defn`), NOT `dD.type`, so the declared ResC
  does NOT apply; the needed fact is `machResultKind? (userInliner env dD.type) = some res` — P5 (docs/parallel
  B-callkinds.md 419, B-readerinv.md 169–199). `userInliner` goes through `inlineDefs` / `inlAbbrevs` /
  `MachRecUnfold` with `opaque` `Expr.replace` / `partial` helpers: not provable here. KEPT EXPLICIT (`P5At`), and
  only on the branch where the entry actually unfolds (`entryConst … ≠ ci`).

## 4. Connection made (Tools/ShippingCallWidthsChildReal.lean)

Real reader only, no candidate (so no O1/O2): `childLink_real` (from any `RealChild` of the callee: the link at
THAT run's entry constant, and `ResC` there via `resC_entry`), `callWidthsStrict_real` (kidOuts := the callees'
real shapes, from the children the closing consumes), `children_widths_real` (leaf callees: the module received
for entry `k` has ports `kidOuts k`, and every connected port has the binder's width), `parent_children_widths_real`
(the same for the `children` of ONE parent core run's `CloseCalls`, via `machine_children_realA`).

Remaining premises: callee `MachineDefines` (existing boundary), `ResDeclAt` (declared kind over `getConstInfo`
reads), `P5At` (explicit), parent `PB` (decidable), `memChild? = none` (decidable), `LeafKid` (leaf scope). The cache
is covered by the existing invariant (`CacheInv`) inside `ChildrenReal`; `hkid` is gone.

Not done: non-leaf (calling) callees' `ChildOutTys` (needs the seq/kids interfaces), memory callees, and any
statement about the candidate `machineShapeF` (unchanged: O1/O2).

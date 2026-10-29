# S4 run-local fit consumer (replaces consumer 1's `hKSb`) — freeze rev1, FOR REVIEW

- **Issue:** `sparkle-gen2-step` (S4-BD follow-up; S4_BD_RESULT.md "Next").
- **Base:** par/gen2-spec 4c2953c3. Read-only design; nothing here is built or proved.
- **Design status:** recommended, not shown to be the only design. No compiler mask, no FG premise, no change to `KSBoundedIn`.

## 1. What `hKSb` is and the weakest property that suffices

**Definition** (Tools/ShippingHierOptRun.lean:658-663):
```lean
def KSBoundedIn {σ : Type} (children : String → Option (Module × WEnv)) (KS : KStep σ)
    (body : List Stmt) (Inv : Module → σ → Prop) : Prop :=
  ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe,
  children mn = some (child, cwe) →
  ∀ env s cres s', Inv child s → KS child cwe (inConns child.outputs conns) env s = some (cres, s') →
    (∀ p ∈ child.outputs, cres p.name < 2 ^ p.ty.bitWidth) ∧ Inv child s'
```
It quantifies over EVERY `env` and every `Inv`-state. That is why an unmasked pass-through child can fail it (S4_BD_RESULT.md).

**Consumer 1's two sites** (`machine_ships_hierC_noHstR`, Tools/ShippingSrm33Core.lean:24):
- :124 `have hKSb := hBd b D hBdb`. This uses the design-level `Bd b D` (:89) and no run.
- :176-178 `fitX_of_run _ (childMap D.modules) b Inv hKSb ins hwfB hndB hIW T _ envs hrunB (… hRI raw D kids hreset …) hstX`.
  - Here `envs` is the run from `composed`'s `H` (:145), restated on `b` as `hrunB` (:147-149). Its state is `⟨st0, mems, kids⟩` and its seed is `seedIn b ins`.
  - Its result is `hierRefineCheck_linked`'s `hfitX` (HierOptRun:545-546).

**Inside `fitX_of_run`** (HierOptRun:668-763), `hKSb` is used twice:
- `.1` at :735. This is the child-port bound of the instance-output wire at step 0. It is turned into `declWidth m x` by `instOutWidthsOk_at hIW` (:734; HierOpen:556-561).
- `.2` at :751. This only carries `Inv` to the next state, so that `.1` can be used again.

So the only content that is consumed is this: **on this one run, every instance-output wire fits its child port.** Wires not driven by an instance are handled by the frame (:736-739, :752-761, from `hstX`).

**Weakest run-local property** (MISSING, new definition in Tools/ShippingHierOptRun.lean). It is `.1` restricted to the values the actual run puts on the wires. It has no `Inv` and no "every env".
```lean
def KSBoundedRun (children : String → Option (Module × WEnv)) (body : List Stmt) (envs : List Env) : Prop :=
  ∀ j (hj : j < envs.length), ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe,
    children mn = some (child, cwe) → ∀ p ∈ child.outputs, ∀ x,
      conns.lookup p.name = some (.ref x) → (envs[j]'hj) x < 2 ^ p.ty.bitWidth
```
- Given `hIW` plus the frame, this is exactly what `hfitX` needs on the instance-output wires.
- In the opposite direction, `KSBoundedIn` together with `ResetImpliesInv` implies it (`ksBoundedRun_of_In`, MISSING; its proof is `fitX_of_run`'s induction). So mem parents (`memKSn_boundedIn`, Tools/ShippingGen2MemBd.lean:54) can still use the new consumer.

**Frame lemma** (MISSING; a copy of `fitX_of_run`):
```lean
theorem fitX_of_runR {σ : Type} (KS : KStep σ) (children : String → Option (Module × WEnv)) (m : Module)
    (ins : Nat → String → Nat) (hwf : linkedWF children m.body = true)
    (hIW : instOutWidthsOk children (declWidth m) m.body = true) :
    ∀ (T : Nat) (s : KState σ) (envs : List Env),
      runModuleTG KS (declWidth m) children m.body (seedIn m ins) T s = some envs →
      KSBoundedRun children m.body envs →
      (∀ x ∈ (openIns m).map (·.name), x ∉ bodyInstOuts children m.body → s.st x < 2 ^ declWidth m x) →
      ∀ j (hj : j < envs.length), ∀ x ∈ (openIns m).map (·.name), (envs[j]'hj) x < 2 ^ declWidth m x
```
Differences from `fitX_of_run`:
- **Dropped:** `Inv`, `hKSb`, `hnd` and the kids-invariant premise.
- **Zero case** (:722-735): after `bodyInstOuts_mem` and the lookup step (:723-732), rewrite `envs[0] = envF'`. Then use `instOutWidthsOk_at hIW` and the hypothesis at `j = 0` in place of `linked_consistentKG` and `.1`.
- **Successor case:** the recursive call gets `KSBoundedRun … rest` by shifting the index (`envs = envF' :: rest`). The `.2` block (:744-751) is deleted.

**Joint binder** (MISSING): `ComposedNWRegsF`. It is `ComposedNWRegs` (Tools/ShippingSrm28Regs.lean:41-75) with the run conjunct extended to:
```lean
      ∃ envs, runModuleTG (KSn (childMap dsn.modules) n) (Tools.ShippingEntrySoundness.weOf m)
          (childMap dsn.modules) m.body seed T ⟨st0, mems, kids⟩ = some envs ∧
        envs.length = T ∧
        (∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f → (envs[j]'hj) o.name = f j) ∧
        Tools.ShippingHierOptRun.KSBoundedRun (childMap dsn.modules) m.body envs
```
The fit sits on the SAME `envs` and the SAME witness, so no determinism argument is needed.

**Replacement consumer `machine_ships_hierC_run`** (MISSING; new file Tools/ShippingSrm33Run.lean). It is a copy of Srm33Core:24-189 with these changes:

| Srm33Core | change |
|---|---|
| :28 `Bd`, `Inv`; :29 `hBd`; :30 `hRI` | removed |
| :68 `ComposedNWRegs` | `ComposedNWRegsF` (same arguments) |
| :89 `Bd b D →` | removed. The conclusion after `Bnd … →` is then `TopShips`' body (Tools/ShippingGen2Defs.lean:273-295) |
| :115 `intro hBnd hBdb` | `intro hBnd` |
| :124 | deleted |
| :145 `obtain ⟨envs, hrun, hlen, hobs⟩` | `⟨envs, hrun, hlen, hobs, hfitI⟩`, plus `have hfitB : KSBoundedRun (childMap D.modules) b.body envs := by rw [hbB]; exact hfitI` |
| :176-178 | `(fitX_of_runR _ (childMap D.modules) b ins hwfB hIW T _ envs hrunB hfitB hstX)` |

Every other line is unchanged. `hIW` (:120, `RunFacts.wid`) is still used. `hreset` is still used, at :146.

## 2. The supply chain, ordered to avoid circularity

The bound comes from the **source**, never from the parent's fit. On the run, the instance-output wire of call `k` carries `posEnc` of the parent's call-result binder, which is a `BitVec` value. The child's meaning is what makes the instance actually output that value.

| # | fact | status | exact type / site |
|---|---|---|---|
| a | input fit `hinsFit`, `hstX` | EXISTING (TopShips antecedents, Defs:287-290; Srm33:105-107) | NOT on the instance-output chain. The inputs are pinned to `BitVec` source values by `SourceInputs` (hsrc). `hinsFit` is used only by `hierRefineCheck_linked` (:175); `hstX` only by the frame |
| b1 | let range | EXISTING `Pkg.lsrc_hl` (Tools/ShippingGen2Pkg.lean:102-105) | `∀ a l, p.d.ls[a]? = some l → ∃ v, (p.lsrc i bools bits)[a]? = some v ∧ ∀ τ, v τ < 2 ^ l.1.width` |
| b2 | argument `InRange` (width correspondence) | EXISTING. The conjunct of `CallDec` (Defs:110) / `OneOutCall` (Tools/ShippingGen2CallField.lean:171); supplied by `call_inRange_at` (Tools/ShippingGen2Adapt.lean:106) from `callArgsOkAt p.d p.kD k q.portWidths` (Adapt:73, :80) + b1 | `∀ τ, InRange (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1 τ) q.ports` |
| b3 | argument wires = source lets on the run | EXISTING. The trace's let clause (Tools/ShippingMachineTraceX.lean:409-411); `hargVals` inside `machine_linked_ofB` (Tools/ShippingMachineExtB.lean:321-342) | — |
| c1 | child meaning | EXISTING. `ChildFn` (Tools/ShippingMachineCompose.lean:241-245); `childFn_of_combRun` (Tools/ShippingGen2CombKid.lean:174); `hserve` gives `CombChildRunN` (Tools/ShippingGen2OneOut.lean:183-206; Defs:60-74) | `ChildFn mc (oneP P p k) (oneF P p i k)` (OneOut:212-231) |
| c2 | child source output = parent's call-result value | EXISTING. `combS_pointwise` (CombKid:205) + `CallDec`'s `posEnc` conjunct (Defs:112-113); combined at OneOut:236-252 | `oneF P p i k (valsOf … j) = posEnc (…val j) (…val j) (p.kD + k) κk`, where `κk := ((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain` |
| c3 | wire value on the run | MISSING (copy). Already proved INSIDE `machine_linked_ofB`: `V` :235, `seed'` :238, `hon` :242, `hframe` :349, `hseedv` :357. It is not exposed | `machine_linked_ofBV` = `machine_linked_ofB` with the extra conclusion conjunct `∀ j (hj : j < envs.length) k outW, k < d.shape.insts.length → ((machPorts declName ids cache d.shape.binders).map (·.name))[machNIn d.shape + k]? = some outW → (envs[j]'hj) outW = posEnc (fun p => (extB i bools bits p).val j) (fun p n => (ext i bools bits p n).val j) (kD + k) (((d.bsIn.drop kD)[k]?.map (·.2)).getD .domain)`. Then the copies `ComposedHBV`, `composedNWn_of_HBV` (`runModuleTG_KSn_of_H`, Tools/ShippingMachineDepthHR.lean:183, returns the same `envs`), `machine_linked_callsServed1V`, `composedNWRegs_of_composedNWV` |
| c4 | range of the value | MISSING, trivial | `theorem posEnc_lt (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (pos : Nat) (κ : MixedGateBinder) : posEnc bools bits pos κ < 2 ^ (kindTy κ).bitWidth` (cases: Entry:293-297, Entry:232-235, `encodeBool_lt` Tools/ShippingMachineChild.lean:491, `BitVec.isLt`) |
| d1 | instance wire is call `k`'s wire | MISSING, small. From `MachineWired`'s one-output `insts` clause (Tools/ShippingMachineEntry.lean:667-669) and `CallStmt`'s conns (Tools/ShippingMachineInst.lean:190-203; the output name is not an argument port, :199) | `oneOut_lookup_callWire : … Stmt.inst mn iname conns ∈ m.body → children mn = some (child, cwe) → p ∈ child.outputs → conns.lookup p.name = some (.ref x) → ∃ k args mc outP, k < insts.length ∧ CallStmt … k args mc (.inst mn iname conns) ∧ child = mc ∧ mc.outputs = [outP] ∧ p = outP ∧ names[machNIn d.shape + k]? = some x` |
| d2 | binder width = child port width | EXISTING definition, NO supplier. `OneOutWidth P p k` (S4_CONSUMER_FREEZE.md §5) gives `(p.d.shape.binders[p.kD + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some o.ty.bitWidth`. With `CombChildRunN`'s first conjunct (Defs:65): `outP.ty = o.ty`. Small index lemma `binders[p.kD+k]? = (p.d.bsIn.drop p.kD)[k]?` from `callsOk_nIn` (Tools/ShippingGen2CallDec.lean:42) and `bsIn` (Tools/ShippingMachineAuto.lean:195), MISSING | — |
| e | `KSBoundedRun` on the composed run | MISSING. `oneOut_ksBoundedRun`: d1 → c3 → c4 → d2 on the witness's `wired`, under `hdec`, `hW` | gives `ComposedNWRegsF` from the `…V` copies |
| f | parent fit `hfitX` | MISSING `fitX_of_runR` (§1), with `hIW = RunFacts.wid` | — |

**Order:** b1 → b2 → b3 → c1 → c2 → c3 → c4 → d1/d2 → e → f.
- Neither c1 nor c3 uses the parent's fit or a range of the child's output. `ChildFn`'s premise is b2, which comes from the source (b1).
- The parent's fit (f) is a CONSEQUENCE and is never assumed.
- The child's own fit (its `TopShips` antecedents) is not used. `CombChildRunN` (Defs:71) takes only argument `InRange`.

**Alternative source-output range for (c), not recommended.** It would be `Pkg.src_lt : ∀ v, InRange v q.ports → ∀ k o f, q.d.shape.layout.outs[k]? = some o → (q.S i (fun _ => v))[k]? = some f → ∀ τ, f τ < 2 ^ o.width`. None exists: `Pkg.src_length` / `Pkg.src_get` (CombKid:56/:79) give only the shape. The `posEnc` route (c2+c4) needs no new source fact.

**Rejected variant (records a stop).** Stating `KSBoundedRun` against `declWidth b x` would drop `hIW`/`hW`. It would need `declWidth b x = (kindTy (binders[kD+k]).2).bitWidth` keyed on the SAME `k`. The only supplier pattern is `core_callPorts_ranA` (Tools/ShippingParentRunFactsA.lean:410-437, :557-562). It requires `hfne : instFields ≠ []` (:418), and it is stated over the `ran` witness, not over the trace's `ids`/`cache`. Matching `k` across the two witnesses has no supplier.

## 3. Interaction with stage A and with group parents

- **Stage A.** `machine_linked_callsServed1` (OneOut:158) and `composedNWn_of_HB` (ExtB:455) stay as they are. Stage B uses the `…V` copies:
  - `machine_linked_callsServed1V` has the same proof, but refines into `machine_linked_ofBV` (c3).
  - `composedNWn_of_HBV` passes the extra conjunct through on the same `envs` (ExtB:477-478).
  - The identity checks (ExtB:74, :481-494) get `…V` analogues. The extra conjunct is dropped by `And.left`.
- **`oneOut_topShips`** (freeze §3 stage B) then calls `machine_ships_hierC_run`. Its `hBd` premise disappears; `hW` (S4-WID) stays, because it is used by d2 and by `RunFacts.wid` (`core_instOutWidthsOk_oneA`, still MISSING, freeze §5).
- **Group parents (`closeInstsG`, `instFields ≠ []`).** The same chain applies with group copies:
  - `machine_linkedTG_of` (Tools/ShippingMachineLinkedTG.lean:30) builds the same `V`/`seed'` (LinkedTG:185-189). Its copy `machine_linkedTG_ofV` exposes the c3 conjunct for ANY `KS` (seq, comb or memory children). It is reached through `machine_linkedT_callsRNA` (Tools/ShippingMachineDepthRunRA.lean:142, :214) and `machine_linkedT_callsServed` (Tools/ShippingGen2Consumer.lean:30).
  - **d1 for groups:** `connsG` connects only the read fields (Tools/ShippingMachineLinkedT.lean:28-34), and `MachineWired`'s `CallStmtG` clause (Entry, `instFields ≠ []` clauses) maps each `(k, field)` to call `k`'s wire. Unread ports have `lookup = none`, so they are vacuous. Small lemma `group_lookup_callWire`, MISSING.
  - **d2 for groups** is the existing non-vacuous `hkidW` form (ParentRunFactsA:587-591; `hkidW_of_dataA` :612).
  - So, yes: the same chain covers `closeInstsG` children, sequential ones included, because the value is pinned by `V` and not by the child's state invariant. Memory-only parents may keep `memKSn_boundedIn` through `ksBoundedRun_of_In`.

## 4. Stop conditions and coverage obligations

- **G-ONEOUT-WID (unchanged):** `∀ k, OneOutWidth P p k` has no supplier (freeze §5). It is needed twice: by d2 and by `RunFacts.wid`. The only real instance on hand is `callerL_strict` (Tests/Compiler/OneOutCallerLTest.lean:275-278), and the generator emits only the vacuous row.
- **G-SERVED (unchanged):** `h` / `ServedP (ShipsRes L P)` (Defs:251, not built).
- **S4-MEM case restriction (unchanged):** `hnomem` and `hdec` in the `CallDec`-only form.
- **Cross-witness width (stop for the rejected variant only):** see §2.
- **No new stop for S4-BD.** On this design every fact on the chain is either EXISTING or MISSING-but-derivable: c3 by copy, c4 by cases, d1 and e by short proofs. None was checked by a build.

## 5. Not claimed

- Nothing is built. The MISSING items above are designs, not proofs.
- `KSBoundedIn` is neither refuted nor proved for any real child.
- That `KSBoundedRun` is the unique weakest form is not claimed. It is the weakest at Srm33Core:176 among properties that keep `hIW`.

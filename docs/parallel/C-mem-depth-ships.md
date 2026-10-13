# C — the ship-level depth generator for a parent of a memory-only kid (round par/c-2)

Branch `par/c-2` from poc `12e8147b`. **WRITTEN, NOT BUILT.** No `lean`,
`lake` or `iverilog` was started; nothing below is proved-and-built. Marks:
[R] read (file:line at 12e8147b), [M] measured by the integrator (the c-1
probe), [P] PREDICTED, [?] not known.

How far it got:

* steps 0–3 written. No new THEOREM was needed for step 1 and no built file
  was edited for step 2 (§2, §3): one new command file.
* step 4: the closing of `memParent` is read down to the blocking premise;
  ONE unit of it is written (`Tools/ShippingKidsChildIfaceM.lean`, the
  child interface over children that may be memories); the generator for it
  is NOT written — exact next statements in §7.

## 1. What was read

| what | where [R] |
|---|---|
| `generateRunOfR`, `generateCoreNR` (whole: families, `PC`, the refusal at 693, the grouped loop, the memory branch 738 / 820–827, `hrunN` 861–915, the boundary 916–926), `generateShipsNR`, `generateDesignNR`, `closingCandidates`, `preClose`, the command; `bndOfComposed`, `generateCombNR`, `closingThm?`, `closesAtNames`, `closesAtProof`, the `Grouped` helpers | `Tools/ShippingMachineDepthCommandR.lean` 60–1049 (the file except its header comment 13–52) |
| `SeqFactsRN`, `calls_hchildRN` (statement AND proof), `machine_linkedT_callsRN` (statement and proof) | `Tools/ShippingMachineCallsLinkedTNR.lean` (whole file) |
| `ComposedNW` | `Tools/ShippingMachineDepthRun.lean` 33–65 |
| `MachineRunNC`, `seqChildRunN_of_composedC` (statement, first proof lines), `machineRunNC_of_real` (statement) | `Tools/ShippingMachineDepthRunR.lean` 37–50, 114–160, 243–271 |
| `machine_linkedT_mem` (statement, first proof lines); `#machine_composedT`'s generator; `memWidths?` | `Tools/ShippingMachineMemLinked.lean` 190–255; `Tools/ShippingMachineMemCommand.lean` 20–113 |
| `KT`, `KSn`, `KSn_local`, `stOf`; `ResetN` | `Tools/ShippingHierStateG.lean` 619–640; `Tools/ShippingMachineDepth.lean` 44–60 |
| `endpointParts`, `nameCases`, `findCall`, `sigAtPos`, `memTactic`, `rangeSyntax`, `proveByTacticT`, `generateSeqChild` (head) | `Tools/ShippingMachineSeqCommand.lean` 20–176 |
| `extTactic`, `extBTactic` | `Tools/ShippingMachineDepthCommand.lean` 91–106 |
| `conj`, `projs`; `proveByTactic`, `addTheorem` | `Tools/ShippingMachineShipsHierCommand.lean` 16–28; `Tools/ShippingMachineLinkedCommand.lean` 27–41 |
| `machine_traceL_of_loop_causalRA` (binders) | `Tools/ShippingMachineSeqLinkedR.lean` 23–60 |
| `#machine_no_ports_mem`: header, scope table, what it builds on (`finish0`, 630–712) | `Tools/ShippingNoPortsMemCommand.lean` 1–75, grep of 189–241, 577–712 |
| `textCheckI`, `kidsPass`, `designCheck`; `leafCheck`; `seqStmtOkI`; `kidCheck`, `designCheck_eq`; `outsMaskedN`, `kidsMaskedN` | `Tools/ShippingDesignSV.lean` 102–124; `Tools/ShippingDesignSVLeaf.lean` 91–99; `Tools/ShippingHierSVSoundness.lean` 28–34; `Tools/ShippingChecksDesign.lean` 117–129; `Tools/ShippingMachineShipsDepth.lean` 153–168 |
| `compose` (design SV) | `Tools/ShippingShipsDesignSVCommand.lean` 43–72 |
| `closesAtCore`, `closesAtTheorem`; `closesAtCoreG` (scope) | `Tools/ShippingMachineClosesAtGen.lean` 76–116, 228–267; `Tools/ShippingMachineClosesAtGenG.lean` 1–50 |
| `ifaceDeep` (scope and leaf / with-calls branches), header | `Tools/ShippingChildIfaceGen.lean` 1–40, 296–360 |
| `KidNames`, `namesOf`, `kidsChild_iface` (statement AND proof), `kidsChild_of_real` | `Tools/ShippingKidsChildIface.lean` 1–392 (whole file) |
| `ChildIfaceD` | `Tools/ShippingCallsKidsD.lean` 37–51 |
| `ChildIfaceP`, `ChildIfaceD.toP`, `memIface`, `memKid_iface`, `machineClosesAt_of_kidsDM` (statement, first proof lines) | `Tools/ShippingMemClosesKids.lean` 150–260, 419–460 |
| `Kid`, `kid_of`, `Kid.real`, `Kid.mem` | `Tools/ShippingKid.lean` 1–75 |
| `MemChildren`; `closeInstsGM_inv`, `synthesizeMachineCertified_runs`; how a built proof takes `MemChildren` from the closing | `Tools/ShippingMachineEntry.lean` 862–864; `Tools/ShippingChildRun.lean` 262–290, 528–544; `Tools/ShippingChecksCore.lean` 476–492 |
| `memModule`, `memChild?`, `memParams?`; `ofDecl`, `ofMem` | `Sparkle/Compiler/MachMemory.lean` 47–77; `Sparkle/IR/ModuleName.lean` 259–262 |
| `scopeD`, `readKid` | `Tools/ShippingNoPortsDeepCommand.lean` 139–205 |

NOT read: `Tools/ShippingHierState.lean` (`runModuleT`, `KidState` beyond its
line 25), `runModuleTG` / `flatKS` bodies, `machine_ships_hierC`,
`composedG_of_NW`, `ships_design_svN_all`, `closesDeep`'s body (only
`ifaceDeep`), `GenKid`. They turned out not to be needed for steps 1–3 (§2);
they are where the PREDICTIONS for the steps after K1 are weakest (§8).

## 2. Step 0: the three "not read" questions of the c-1 record

**(1) "the equation `runModuleTG flatKS … = runModuleT …`" — NOT NEEDED.**
The depth generator's theorem does not go through `machine_linkedT_mem` /
`runModuleT` at all. `machine_linkedT_callsRN`
[R `ShippingMachineCallsLinkedTNR.lean` 203–291] is stated in the `G` form at
every depth `n` and takes, per call entry,

    MemFacts … k c  ∨  SeqFactsRN … k c                                   (233–235)

Its instance lemma `calls_hchildRN` handles a memory entry directly in the
`G` form [R 120–144]: `runKS_instFree` (the memory module has no instance,
125–129, 133) and `mem_hchild` (134).

**(2) "does `ResetN` give the read latch `out_rdata` zero for a COMBO memory
module?" — YES, for both read kinds.** `memModule combo aw dw`'s body is
`[.memory "mem" aw dw "clk" (.ref "wa") (.ref "wd") (.ref "we") (.ref "ra")
"out_rdata" combo [] [], .assign "out" (.ref "out_rdata")]`
[R `MachMemory.lean` 59–61] — the statement names the latch `out_rdata`
whatever `combo` is. `ResetN`'s third conjunct is about every `Stmt.memory`
of the module [R `ShippingMachineDepth.lean` 55–56], and `calls_hchildRN`
uses exactly that: `hRl "mem" aw dw "clk" … "out_rdata" cb [] [] (by simp
[memModule])` [R 136–137], and the second conjunct for the memories (135).

**(3) "does the `#machine_no_ports_mem` chain already have a
`ComposedNW 0`-shaped intermediate?" — NO.** That chain is the route `.mem`:
`f.machine_ships_hier` with reset `ResetM` and child bound `kidsMem`
[R `ShippingNoPortsMemCommand.lean` 650–653], its composed theorem
`composedG_of_Tmem` on `machine_linkedT_mem` (the flat `runModuleT` form)
[R 700–708] — a `ComposedG`, never a `ComposedNW`. The general theorem in
the `ComposedNW n` form is `machine_linkedT_callsRN` itself; what did not
exist is its APPLICATION to a machine without a sequential child.

**Consequence for step 1.** `composedNW0_of_mem` is not a new theorem and
not a re-export of the memory chain: it is `machine_linkedT_callsRN n h …
bsC outsC S PC hcalls hrunN` with every `hcalls` case the LEFT disjunct and
`hrunN` vacuous (it is asked under `memChild? c = none`, 239). The four
families are read only in `SeqFactsRN` and in `hrunN`'s conclusion `PC c mc`,
so with no sequential child they are arbitrary. The only obstacle was the
generator: `let some (_, pc0) := pcCases.head? | throwError "… no sequential
child"` [R `ShippingMachineDepthCommandR.lean` 693] — `pc0` is merely the
DEFAULT of the name-case function `PC` (694).

## 3. Steps 1–2: `Tools/ShippingMachineDepthMemKidCommand.lean` (new), no built-file edit

`#machine_composed_memNR f n` adds

    f.machine_composedNR{n} :
      ∀ {mctx mref cctx cref} {w w'} {m design},
        RunsTo (synthesizeCombinationalCore f [] false) mctx mref cctx cref w (m, design) w' →
        MachineDefines mctx mref cctx cref f f.machineData.shape →
        MachineClosesAt mctx mref cctx cref f f.machineData.shape →
        ChildBnd mref cref w →
        ∃ ids, ids.Nodup ∧ ids.length = … ∧ ∃ cache regs, … ∧ ∃ lets, … ∧ MachineWired f … ∧
          ∀ i bools bits T seed st0 mems (kids : String → KT n), … →
            (∀ iname mc, (∃ conns, Stmt.inst mc.name iname conns ∈ m.body) →
              moduleByName design.modules mc.name = some mc → ResetN design n mc (kids iname)) →
            ∃ envs, runModuleTG (KSn (childMap design.modules) n) … = some envs ∧ …

i.e. `ComposedNW n f f.machineData nDecl m design dom src ext extB` unfolded
(the conclusion of `machine_linkedT_callsRN`), under the 12 binders of the
wired head `…RA` of `f`'s endpoint (the binder names/implicitness are the
head's; I did not re-read which are implicit [?]), the run boundary —
`ChildBnd` alone, no child premise — last. The statement is `inferType` of
the proof term, as in the built generator.

**Why no built file is edited.** `generateRunOfR c n` gets the kid's composed
theorem from `generateCoreNR c n` [R 517–520], and `generateCoreNR` starts
with `let name := declName ++ machine_composedNR{dep}; if (← getEnv).contains
name then return name` [R 539–540]. So a theorem of that name, added BEFORE
`#machine_design_svNR parent n`, is what the built generator uses; it then
reads the boundary with `bndOfComposed` (12 binders, 62–65) and applies
`seqChildRunN_of_composedC` (525) — both generic. The new command is
`generateCoreNR` specialised to `seqKids = []`, step for step:

| built line [R] | here |
|---|---|
| 546–548 `endpointParts`, `pL := (headL ++ "RA") args` | the same |
| 568–574 telescope, `tyArgs` (11), `hsyn := xs.back!` | the same (+ a test `xs.size == 12`) |
| 587–629 `bsC`, `outsC`, `S` by `nameCases … cases dflt` | `nameCases … [] dflt` (the same defaults) |
| 693–694 `PC := nameCases … pcCases pc0` | `nameCases … [] (fun _ => True)` |
| 702–708 `machine_linkedT_callsRN dep h`, `decide`, `nDecl`, 7 × `decide`, the four families | the same |
| 820–826 a memory entry: `proveByTacticT goalK (memTactic k cb aw dw argsK)` | the same, for every entry |
| 834–855 the chain `forall_getElem?_nil/_cons`, bound at `k c hk` | the same (no group hypotheses) |
| 869–870 `hrunN` for a placeholder: `intro h; first \| cases h \| simp [memChild?] at h` | the same, for every entry |
| 903–915 the `hrunN` chain | the same |
| 917–926 boundary `conj (hsynT :: pTypes)`, `projs`, `addTheorem` | `pTypes = []` |

Refused, with a reason: no call; `instFields = []`; a callee that is not a
placeholder; a transported endpoint; a head without a wired twin
(`endpointParts`). On failure the environment is put back.

**The two-line alternative, NOT taken** (for the integrator's judgement): in
`generateCoreNR` replace the `throwError` at 693 by the default `fun _ =>
True`. Additive in effect (only a path that threw before changes), and it
would make `#machine_design_svNR parent n` work without a pre-step. I did
not do it because the rule allows a built-file edit only where a new file
cannot do the job, and here a new file can.

**A limit, by reading (not a refusal of the command).** The composed theorem
is true at every `n`, but the DESIGN-level check of the SV composition is
`designCheck C (n+1) o = textCheckI C o && kidsPass C (designCheck C n) o.body`
with `designCheck C 0 o = textCheckI C o && kidsPass C leafCheck o.body`
[R `ShippingDesignSV.lean` 122–124], and `textCheckI` asks `body.all
seqStmtOkI` (assign / register / inst only, `ShippingHierSVSoundness.lean`
30–34) while `leafCheck` accepts a memory statement
(`ShippingDesignSVLeaf.lean` 95–99). So a memory module passes as a kid only
at depth index 0, i.e. `memCounterH` must sit at depth index 0 below its
parent: `memParent` at 1 and `memGrand` at 2 are balanced that way. A parent
at depth 2 calling `memCounterH` DIRECTLY would get
`memCounterH.machine_composedNR1` from this command and a
`machine_design_svNR2` whose `designCheck` antecedent is false of the real
design (the memory module would be checked by `designCheck C 0`). The same
fact is recorded in `ShippingNoPortsMemCommand.lean` 201. The probe uses
`n = 0` only.

## 4. Step 4, written unit: `Tools/ShippingKidsChildIfaceM.lean` (new)

    structure KidNamesP (nm : String) (names : List String) (b : Module) (design : Design) : Prop where
      name : b.name = nm
      desNames : ∀ g ∈ design.modules, g.name ∈ names
      closed : ∀ g ∈ b :: design.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body → mn ∈ names

    theorem KidNames.toP (h : KidNames c names b design) : KidNamesP (ModuleName.ofDecl c) names b design

    def namesOfP (d : MachineData) (nameK : Nat → String) (namesK : Nat → List String) : List String :=
      (List.range d.shape.insts.length).map nameK ++ (List.range d.shape.insts.length).flatMap namesK

    theorem memKidNamesP {c cb aw dw} (hc : memChild? c = some (memModule cb aw dw))
        {y : Res} (hy : Kid mref cref c y) :
        KidNamesP (memModule cb aw dw).1.name [(memModule cb aw dw).1.name] y.1 y.2

    theorem kidsChild_ifaceM {c : Name} (d : MachineData) (ok) (hbody) {nDecl} (hC) (hslots) (hdomB)
        (hins) (hsl) (outTy) (kD) (hkD) (hIlen) (hSL) (hSlen) (hLlen) (hNIn)       -- as kidsChild_iface
        (hfne : d.shape.instFields ≠ [])                                             -- NEW
        (nameK : Nat → String) (namesK : Nat → List String)
        (hkid : ∀ k (hk : k < d.shape.insts.length) (y : Res),
          Kid mref cref (d.shape.insts[k]).1 y → KidNamesP (nameK k) (namesK k) y.1 y.2)
        (hself : ModuleName.ofDecl c ∉ namesOfP d nameK namesK)
        {w w' b design} (hw : InvW mref cref w)
        (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
        (entry : MachineDefines mctx mref cctx cref c d.shape)
        (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
        ChildIfaceD c ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length
          (d.shape.layout.outs.map (·.name)) (namesOfP d nameK namesK) b design

    theorem kidsChild_of_realM … (the same premises) (entry) (closes : ∀ mctx' cctx', MachineDefines … → MachineClosesAt …)
        {y : Res} (h : RealChild mref cref c y) : ChildIfaceD c … (namesOfP d nameK namesK) y.1 y.2

Why it is needed: `kidsChild_iface` has `hnomem` and takes its children by
`KidNames`, whose `name` field is `b.name = ModuleName.ofDecl c`; a memory
entry's child is named `ModuleName.ofMem …` [R `MachMemory.lean` 51], so
`KidNames` is FALSE of it and the premise cannot be met. `hnomem` is used
once [R `ShippingKidsChildIface.lean` 262–265].

How it was made (not retyped): the file is generated from the built file's
lines 127–352 and 354–390 by a script with ASSERTED single-occurrence
replacements; the proof text is the built one except

1. inserted before `hcc.some`: `have hMC : MemChildren d.shape children := by
   rcases hcc with ⟨hf0, -⟩ | ⟨-, -, h⟩ …` — verbatim the built lines of
   `ShippingChecksCore.lean` 483–486 (same `hcc`, same position);
2. `hfull`: the two-case split on the witness replaced by `exact ⟨hk, hkid k
   hk y (Tools.ShippingMemKid.kid_of hk hMC hc hor)⟩`;
3. `hnameK`: `nameK k ∈ namesOfP …` by `List.mem_map.mpr ⟨k, List.mem_range.mpr
   hk, rfl⟩`;
4. `namesOf d namesK` → `namesOfP d nameK namesK` in the statements of
   `hnameK`, `hvisN`, `hself`, the conclusion.

The conclusion is the SAME `ChildIfaceD` (so `ChildIfaceD.toP` and the built
`machineClosesAt_of_kidsDM` take it unchanged). No hypothesis renames the
conclusion: `hkid` is the per-child fact the built theorem asks too, in the
`Kid` form the built closing `machineClosesAt_of_kidsDM` uses (430–432).

## 5. Build order, `lean_lib` lines

1. `Tools.ShippingMachineDepthMemKidCommand` (imports the built
   `Tools.ShippingMachineDepthCommandR`).
2. `Tools.ShippingKidsChildIfaceM` (imports the built
   `Tools.ShippingKidsChildIface`, `Tools.ShippingMemClosesKids`) —
   independent of 1; nothing uses it yet.
3. `Tests.Compiler.MemDepthProbeTest` (one more import:
   `Tools.ShippingMachineDepthMemKidCommand`).

    lean_lib «Tools.ShippingMachineDepthMemKidCommand» where
      roots := #[`Tools.ShippingMachineDepthMemKidCommand]

    lean_lib «Tools.ShippingKidsChildIfaceM» where
      roots := #[`Tools.ShippingKidsChildIfaceM]

No built file is edited in this round; nothing for `Tests/AllTests.lean`.

## 6. PREDICTED outcomes of the new probe steps (all [P])

| step | PREDICTED | basis |
|---|---|---|
| K1 `#machine_composed_memNR memCounterH 0` | OK | §3: the built generator's own steps for a memory entry. Weak point: I found NO built test that runs `generateCoreNR` on a parent with a memory entry (grep of `Tests/` for `svNR` with a memory parent: none), so the memory branch of the `RN` generator may be exercised here for the first time; `memTactic` itself is built on the same `MemFacts ∨ …` goal in `generateCoreS` |
| R2.2 `#machine_design_svNR memParent 1` | OK, with ONE warning line "the closing of the child …memCounterH stays a premise of this endpoint" and an information line from `preClose` "the closing of the descendant …memCounterH is NOT derived" | `generateRunOfR memCounterH 0` finds `machine_composedNR0`; `seqChildRunN_of_composedC` + 10 `decide`s + `extBTactic` / `extTactic` on `memCounterH.machineExtB` / `machineExt` (generic in the kid); the grouped loop for `cnt` (leaf) and `memCounterH` (non-leaf, three arguments); `closesAtNames memCounterH` = none (there is no `memCounterH.machine_closes_at` / `closes_deep`) → the `And closesAt bndHere` premise (682, 882). Then `generateShipsNR` / `compose`, NOT read (§8). A warning is not an error for the wrapper |
| RH.2 `#machine_design_svNR memGrand 2` | OK if R2.2 is | `memParent` non-leaf → `generateRunOfR memParent 1` → the existing `memParent.machine_composedNR1` |
| R2.3 `#machine_closes_at memParent` | FAILED — "…machine_closes_at was not generated: …memParent: the machine child …memCounterH has calls of its own (not derived here: B3)" | `closesAtCore` → `instFields ≠ []` → `closesAtCoreG`; kids `cnt` (passes), `memCounterH`: `ShippingMachineClosesAtGenG.lean` 43–44. [M] the c-1 message begins the same way |
| R2.4 `#machine_no_ports_kids memParent 1` | FAILED — "the callee …memCounterH has calls of its own under the GENERAL closing…" | scope test, `ShippingNoPortsKidsCommand.lean` 103; [M] |
| R2.5 `#machine_no_ports_deep memParent 2` | FAILED — "the general-closing callee …memCounterH has no …memCounterH.closes_deep (run #machine_closes_deep on a parent of it first)" | `scopeD`, `ShippingNoPortsDeepCommand.lean` 188–189; [M] the c-1 message |
| RH.3 `#machine_closes_at memGrand` | FAILED — "the machine child …memParent has calls of its own (not derived here: B3)" | as R2.3 |
| RH.5 `#machine_no_ports_deep memGrand 2` | FAILED — "the general-closing callee …memParent has no …memParent.closes_deep…" | as R2.5 |

The earlier steps (C, P, G, J, Q, H) are unchanged.

## 7. Step 4: the next refusals, in order, and the exact next statements

### 7.1 The closing of `memParent`

`#machine_closes_at memParent` stops at `closesAtCoreG` 44 (a kid with calls:
"B3"). The B3 generator is `closesDeep` / `ifaceDeep`
(`Tools/ShippingChildIfaceGen.lean`; `preClose` tries it, 1036–1038). For
`memParent` it goes: kid `memCounterH` has calls and a register →
`closesDeep memCounterH` and, per callee of it, `ifaceDeep g` — which for the
placeholder throws at 311–312: "…: a memory child (not derived here)".

What the closing needs, bottom up:

1. `memCounterH`'s OWN closing, in every context. EXISTS after
   `#machine_no_ports_mem`: `memCounterH.noPortsMem_closes : MachineClosesAt …`
   with no premise [R the header of `ShippingNoPortsMemCommand.lean` 71; its
   binder form not read ?].
2. `memCounterH`'s interface as a kid: `∀ y, RealChild mref cref memCounterH
   y → ChildIfaceD memCounterH nArgs outs names y.1 y.2`. The built
   `kidsChild_of_real` cannot give it (§4). **Written:** `kidsChild_of_realM`.
   The exact instance (NOT generated):

        theorem memCounterH.iface_deepM {mctx mref cctx cref}
            (hR : MachineDefines mctx mref cctx cref ``memCounterH memCounterH.machineData.shape)
            {y : Res} (h : RealChild mref cref ``memCounterH y) :
            ChildIfaceD ``memCounterH 3 ["out"]
              (namesOfP memCounterH.machineData (fun _ => (memModule true 4 8).1.name)
                (fun _ => [(memModule true 4 8).1.name])) y.1 y.2 :=
          kidsChild_of_realM memCounterH.machineData memCounterH.machine_ok memCounterH.machine_body
            (by decide) … (by decide)                    -- hC … hNIn, as ifaceDeep's with-calls branch decides them
            (by decide)                                   -- hfne
            (fun _ => (memModule true 4 8).1.name) (fun _ => [(memModule true 4 8).1.name])
            (fun k hk y hy => memKidNamesP (by <the entry is the placeholder: decide on k>) hy)
            (by <ofDecl memCounterH ∉ [ofMem …, ofMem …]: Tools.ShippingModuleName.ofDecl_ne_ofMem>)
            hR (fun _ _ _ => memCounterH.noPortsMem_closes) h

   (`3`, `["out"]` are what the two list expressions of the conclusion
   evaluate to for `memCounterH`; the generated statement would keep the
   expressions.)
3. `memParent`'s closing: the BUILT `machineClosesAt_of_kidsDM`
   [R `ShippingMemClosesKids.lean` 419–451] at `memParent`'s data, with
   `hkid` per entry — `cnt`: the built leaf interface `(seqChild_of_real
   …).toD.toP` (as `ifaceDeep` 337–340, then `ChildIfaceD.toP`);
   `memCounterH`: `(memCounterH.iface_deepM hR (hy.real rfl)).toP hself` —
   and its name premises `hsep`, `hparent`, `hfresh`, `hparentD`, `hdisjD`.
   NOT written: the name premises now range over a list that contains an
   `ofMem` name, and the built name discharge (`Tools.ShippingNameDischarge`,
   `decide` on `Lean.Name`s of DECLARATIONS, `Node.declsT`) has no entry for
   it [? not read]; the lemma to use is `ofDecl_ne_ofMem` (named in
   `MachMemory.lean` 50).
4. The GENERATOR: `ifaceDeep` / `closesDeep` are `partial def`s of a built
   file that call each other; a memory branch cannot be added from outside.
   Either an additive branch at 311–312 (returning a `Node` for the
   placeholder — `Node.names` is today `(declsT).map ofDecl`, which a memory
   name does not fit, so the `Node` structure would need a second name list:
   NOT a one-line edit), or a new generator for the shape "kid whose calls
   are all placeholders" that produces `k.iface_deepM` + the parent's
   closing by 3. Neither is written; I stop here rather than put a premise
   in its place.

With 1–4, `memParent.machine_closes_at` (or `closes_deep`) exists, and then
the depth endpoint needs, for the KID's closing to stop being a premise
(the warning of R2.2), a closing theorem of `memCounterH` under the name
`closingThm?` looks up (`memCounterH.machine_closes_at` or `.closes_deep`,
108–111) in the form `∀ mctx mref cctx cref, … → MachineClosesAt …` —
`noPortsMem_closes` under another name. A re-export under
`machine_closes_at` was NOT made: `closesAtTheorem` audits an existing
`machine_closes_at` against the statement its own generator would produce
(241–260) and would refuse it; `closes_deep` is read by `scopeD` (188) as
"the GenKid shape", which a memory kid does not have. Which name is safe is
a decision for the integrator [?].

### 7.2 The check-free level

`#machine_no_ports_kids memParent 1` (103) and `#machine_no_ports_deep`
(188, then `readKid` 149 for the placeholder) are behind 7.1: the deep
command asks `memCounterH.closes_deep` first. After it, the block is
`GenKid.nomem` and `KidFacts` of a placeholder at depth 0 only
(`B-mem-depth.md` §4: `memKid_facts_succ`, `kidsM_designCheck_in`, `GenKidM`).
Not started. One thing §3 adds to that plan: `memKid_facts_succ` (a
placeholder's `KidFactsM` at depth `n + 1`) is FALSE as stated there — its
`check` field would be `designCheck C n (memModule …).1 = true`, and
`textCheckI` rejects the memory statement (§3, the limit). `GenKidM` has to
keep the placeholders at depth index 0 (`kidsLo` at 0 is `memKid_facts`;
`kidsHi` at 1 must NOT be asked of a placeholder), i.e. it is a structure
for "a kid at depth index 0 whose kids are placeholders", with `facts :
KidFacts … c … 1` only — not `n + 1` for every `n`.

## 8. Risks, in order

1. **K1: the memory branch of the `RN` goal.** `memTactic` (`left; unfold
   MemFacts; refine ⟨…⟩; case hx{k} => (intro j; rfl); all_goals rfl`) is
   built for `machine_linkedT_calls` goals; on the `callsRN` goal the left
   disjunct is the same `MemFacts` [R 233], but no built run of it there was
   found.
2. **K1: the vacuous `hrunN` tactic** (`intro h; first | cases h | simp
   [memChild?] at h`) on `memChild? SparkleMem.combo.4.8 = none` — copied
   from 870; same remark.
3. **R2.2 after `generateRunOfR`:** `generateShipsNR` (`composedG_of_NW`
   under `memFree m.body` of the PARENT's module, `machine_ships_hierC`, a
   `decide` of the output widths) and `compose` were not read; they are
   generic in the kids, and `memParent`'s own module has no memory
   statement, but a failure there would be new information, not a
   contradiction of §3.
4. **R2.2: the extension tactics on a LOOP kid.** `ext` of the kid's trace is
   `fun i bools bits => memCounterH.machineExt i bools bits (Signal.loop …)`;
   `extTactic` does `delta`, `simp only [extendBits, extendBools]`, `split`.
   For `machineExtB` (= `bools`, no Bool entry) the `simp only` must not fail
   with "no progress" — the same situation as any built kid with bit-vector
   calls only [? not checked which built kid that is].
5. **`ShippingKidsChildIfaceM`:** a copied 220-line proof with three edits;
   the edits use `kid_of`'s exact argument order (`hk hMC hc hor`) and rely
   on `cases hy` keeping `y` (as the built line 265 does). `rcases hcc` is
   the built form of another file with other `open`s.
6. Meta API: `forallBoundedTelescope`, `mkAppOptM`, `mkAdd`, the quotation in
   `proveByTacticT` — all copied from the built generator.
7. The limit of §3 (uneven depth) is not checked by the command.

## 9. Not determined by reading

* Whether K1, R2.2, RH.2 pass (no build); §8 items 1–4.
* The binder form of `f.noPortsMem_closes`; under which name the kid's
  closing may be offered to `closingThm?` (§7.1).
* How `Tools.ShippingNameDischarge` would treat an `ofMem` name (§7.1 item 3).
* `closesDeep`'s body, `GenKid`, `machine_ships_hierC`, `ships_design_svN_all`.
* Whether any built test runs the depth generator on a parent with its own
  memory entry (found none by grep of `Tests/`).

## Integrator's build record (2026-10-13) — MEASURED

BUILT on poc 12e8147b + these files, cgrun 3 GiB swap 0, run `c2` (exit 0, peak 0.81 GB), worker's files
unchanged, first attempt: `Tools.ShippingMachineDepthMemKidCommand`, `Tools.ShippingKidsChildIfaceM`,
`MemDepthProbeTest`.

Probe:
* K1 `#machine_composed_memNR memCounterH 0`: OK (135 ms) — `memCounterH.machine_composedNR0` exists.
* R2.2 `#machine_design_svNR memParent 1`: **FAILED — "child memCounterH: No goals to be solved"**
  (predicted OK). RH.2 `#machine_design_svNR memGrand 2`: FAILED the same way through `memParent`.
  So the pre-step is picked up (the "no sequential child" refusal is gone) and the built generator then
  fails in a tactic on the child `memCounterH` (a step that finds its goal already closed).
* R2.3 / RH.3, R2.4, R2.5 / RH.5: FAILED as predicted (B3 "has calls of its own"; general closing;
  no `closes_deep`).
STATE: no ship-level depth endpoint for `memParent` yet; `kidsChild_ifaceM` / `kidsChild_of_realM` built,
used by nothing. Class OPEN.

---

# Round par/c-3: the failing tactic, the kid's run theorem, the sub-steps, the closing by hand

Branch `par/c-3` from poc `ecddf7d1`. **WRITTEN, NOT BUILT.** Nothing was
run. No built file is edited in this round either.

## 10. The failing line (by reading)

Measured: `#machine_design_svNR memParent 1` → "child …memCounterH: No goals
to be solved". The prefix is the wrapper at
`Tools/ShippingMachineDepthCommandR.lean` 565 around `generateRunOfR c (dep -
1)`. With `memCounterH.machine_composedNR0` present, `generateRunOfR` does
[R 517–536]: `generateCoreNR` (returns at once, 540), `bndOfComposed`,
`mkAppM seqChildRunN_of_composedC`, ten `mkDecideProof`s (terms, no tactic),
and TWO tactic runs: `extBTactic` (529–531) and `extTactic` (533). So the
message comes from one of the two.

`extBTactic` [R `Tools/ShippingMachineDepthCommand.lean` 100–106]:

    intro _ _ _ j hj
    delta memCounterH.machineExtB
    simp only [extendBits, extendBools]
    (repeat' split) <;> first | rfl | (exfalso; omega)        ← line 106

`memCounterH.machineExtB` is `fun i bools bits S => bools`: `loopCalls`
starts both chains at the inputs and extends the Bool chain only for a Bool
entry [R `ShippingMachineCommand.lean`, `extOf`], and the one entry (a memory
read) is a bit-vector. After `delta` (which beta-reduces) the goal is `bools
j = bools j`; `simp only` closes it (`eq_self`); `t <;> s` is `focus (t;
all_goals s)`, and `focus` on an empty goal list throws "No goals to be
solved". **The failing line is 106 of `ShippingMachineDepthCommand.lean`,
reached from 529–531 of `ShippingMachineDepthCommandR.lean`.**

Why no built declaration hit it: the kids with calls that go through
`generateRunOfR` either have a Bool entry (`mid`: `cnt`'s field `hit`
[R `Tests/Compiler/ShippingMachineSeqTest.lean` 52–58]) or no `machineExtB`
constant at all (one-output calls, endpoint by `machine_trace_of_data`: the
generator's other branch `intro _ _ _ _ _; rfl`, 532). A loop or `circuit do`
kid whose entries are ALL bit-vectors has the constant and the trivial
chain — `memCounterH` is the first. (The mirror case, a kid whose entries
are all Bool, would fail the same way in `extTactic`; not the case here: a
memory entry is a bit-vector, so `machineExt` is a real `extendBits` chain,
`simp only` leaves an `if`, and the `split` has goals.)

Every other tactic block on the path, for a memory-only kid:

| block [R] | early close? |
|---|---|
| `extTactic` (533) on `memCounterH.machineExt` | no (above) |
| parent `proveGroup`, fact `b` for a non-leaf kid (417–419: `exact ⟨seqRun idx hrn, by rw […]; decide⟩`) | no `<;>`; generic in the kid |
| facts `l` (`args_facts … (by simp […])`), `r` (`exact rangeS`) | single tactics |
| `tacHb` / `tacHv` (431–444, the same `(repeat' split) <;> …` form) | CAN close early when the kid has no Bool (or no bit-vector) ARGUMENT — but `familyFact` (327–345) catches the failure and uses the absorb chain; built for `cnt` (no bit-vector argument). `memCounterH` has one Bool and two bit-vector arguments: neither is trivial |
| `entryProof` (497–503), `memTactic`, the `hrunN` tactics (870–898) | no `<;>` |
| `generateShipsNR`, `compose` | no tactic at all (`mkAppM`, `mkAppOptM`, `mkDecideProof`) [R 930–994; `ShippingShipsDesignSVCommand.lean` 48–72] |

Theorems read this time: `machine_ships_hierC` (statement, 166–256 of
`Tools/ShippingMachineShipsHier.lean`), `ComposedG` (115–137),
`composedG_of_NW` (statement and proof, `ShippingMachineShipsDepth.lean`
251–266), `ships_design_svN_all` (statement to its line 70,
`ShippingShipsDesignSVAll.lean` 30–70). All are generic in the children: the
only premise that mentions memories is `memFree m.body` of the PARENT's own
raw module (`composed`, 208), and the checks `shipsHierCheck`, `Bd`
(`kidsMaskedN`: `noMem` of each DIRECT kid's body) stay antecedents of the
endpoint. `memCounterH`'s body has an instance of the memory module, not a
memory statement.

## 11. The fix and the sub-step commands: `Tools/ShippingMachineDepthMemKidRunCommand.lean` (new)

`generateRunOfR` returns the existing theorem when `c.seq_child_runN_ofR{n}`
is there [R 522–523]. `#machine_seq_child_memNR f n` adds it first:

    f.seq_child_runN_ofR{n} : ∀ (i : ι) {mc : Module} {dsn : Design},
      MachineRunNC f f.machineData.shape Bnd mc dsn →
      SeqChildRunN (childMap dsn.modules) dsn (n + 1) mc (f.machineData.bsIn.take nDecl)
        f.machineData.shape.layout.outs
        (fun vals => f.machineSource i (boolsOf … vals) (bitsOf … vals))

(the statement is `inferType` of `seqChildRunN_of_composedC n Bnd
f.machine_composedNR{n}` applied to its twelve premises — the built
generator's term, 525–535). The two extension premises: `intro _ _ _ _ _;
rfl` when the value of `f.machineExtB` is its Bool-input binder itself (a
SYNTACTIC test of the definition, `extIsBase`), the built `extBTactic`
otherwise; likewise for `machineExt` (`intro _ _ _ _ _ _; rfl` / the built
`extTactic`). Not "try one, fall back to the other": which tactic runs is
decided before any runs, and each failure is an error carrying the goal. If
the kernel refuses the theorem, each of the ten data premises is reduced and
reported (`data premise j: true / NOT true`). Scope: that of
`#machine_composed_memNR`.

Existing declarations are untouched: no built file changes; the command adds
a theorem only for the declaration it is run on, and the built generator
would have thrown for that declaration.

**Which commands exist for ONE sub-step** (the coordinator's question):

| command | what it runs | on `memCounterH` / `memParent` |
|---|---|---|
| `#machine_composedT f` (built) | the memory route's composed theorem (`machine_linkedT_mem`) | `memCounterH`: OK [M] — not the depth chain's form |
| `#machine_ships_hier f` (built) | the depth-0 shipping theorem, route `.mem` or sequential | `memCounterH`: OK [M] |
| `#machine_design_svR0 f` (built) | depth 0, sequential-children route | `memCounterH`: FAILED "no sequential child" [M] |
| `#machine_design_svNR f n` (built) | the WHOLE chain: `preClose`, core, ships, design | no built command runs one of its steps alone |
| `#machine_composed_memNR f n` (c-2) | the kid's composed theorem | `memCounterH 0`: OK [M] |
| `#machine_seq_child_memNR f n` (new) | the kid's run theorem | |
| `#machine_depth_run_of c n` (new) | the BUILT `generateRunOfR c n` alone | reproduces the failure in isolation |
| `#machine_depth_core f n` (new) | the built `preClose` + `generateCoreNR f n` | children's run theorems, grouped loop, child premises |
| `#machine_depth_ships f n` (new) | the built `preClose` + `generateShipsNR f n` | `machine_ships_hierC` |

Each new sub-step command adds what the step adds, so the next one (and
`#machine_design_svNR`) finds it; `#machine_design_svNR` after the two is
`compose` only.

### PREDICTED outcomes of the new probe steps (all [P])

| step | PREDICTED | if not |
|---|---|---|
| D0 `#machine_depth_run_of memCounterH 0` | FAILED — "No goals to be solved" | OK would mean §10 is wrong about where the message comes from (then K2 says "exists" trivially and S2.a is the informative step); another message would be a second obstacle in `generateRunOfR` |
| K2 `#machine_seq_child_memNR memCounterH 0` | OK | the error names `hextB` or `hext` with its goal, or the data premise the kernel refused |
| S2.a `#machine_depth_core memParent 1` | OK, with a warning "the closing of the child …memCounterH stays a premise of this endpoint" | the built generator's own labels: "seq child cnt: …", "call k: …", "call k (group g): …" with the fact's name (`b`, `l`, `r`, `hb`, `hv`). The least certain point: the entry of `memCounterH` (`instFields.getD k ""` against the kid's output name — "call k: field …" if they differ) |
| S2.b `#machine_depth_ships memParent 1` | OK | a unification failure of `machine_ships_hierC` (no tactic is run) |
| S2.c `#machine_design_svNR memParent 1` | OK | `compose`: "the composition's arguments were not all inferred" |
| SH.a–SH.c `memGrand 2` | OK if S2.a is (the kid `memParent` goes through the BUILT `generateRunOfR memParent 1`: its `machineExtB` has a Bool entry — `cnt`'s `hit` — so line 106 has goals) | as above, one level up |

The earlier steps are unchanged (R2.2 / RH.2 stay FAILED where they are in
the file: they run before K2).

## 12. The closing of `memParent`, by hand

### 12.1 What changed against §7.1

`memParent` itself has NO memory entry — its callees are the declarations
`cnt` and `memCounterH`. So `hnomem` of the BUILT `machineClosesAt_of_kidsD`
[R `Tools/ShippingCallsKidsD.lean` 98–135] is true of it, and the built
theorem applies as it is: `machineClosesAt_of_kidsDM` and `ChildIfaceP` are
not needed at this level. The memory enters only through the kid's
interface (`ChildIfaceD … memNames`, from `kidsChild_of_realM`) and through
the name conditions about that kid's descendants (`hparentD`, `hselfD`,
`hdisjD` over `namesK`), which are about a list of memory-module names.

### 12.2 `Tools/ShippingMemNamesP.lean` (new)

    def AllMem (L : List String) : Prop := ∀ x ∈ L, ∃ cb aw dw, x = ofMem cb aw dw
    theorem allMem_nil : AllMem []
    theorem allMem_singleton (cb aw dw) : AllMem [ofMem cb aw dw]
    theorem ofDecl_not_mem_allMem (c : Name) {L} (h : AllMem L) : ofDecl c ∉ L          -- ofDecl_ne_ofMem
    theorem namesOfP_allMem (d) (nameK) (namesK)
        (hname : ∀ k, k < d.shape.insts.length → ∃ cb aw dw, nameK k = ofMem cb aw dw)
        (hnames : ∀ k, k < d.shape.insts.length → AllMem (namesK k)) : AllMem (namesOfP d nameK namesK)
    theorem namesOfP_const_allMem (d) (cb aw dw) :
        AllMem (namesOfP d (fun _ => ofMem cb aw dw) (fun _ => [ofMem cb aw dw]))

This is the name discharge for an `ofMem` name: no `decide` on names, no
candidate rendering, no premise — whatever the declarations are.

### 12.3 `Tests/Compiler/MemParentClosesTest.lean` (new, target-only, ASSERTING)

Imports the probe (for the declarations and for `machineData`, `machine_ok`,
`machine_body` of `memCounterH` / `memParent` and
`memCounterH.noPortsMem_closes`, which the probe's OK steps leave).

    theorem memParent_calls : memParent.machineData.shape.insts.map (·.1) = [``cnt, ``cnt, ``memCounterH]
    theorem memCounterH_entry : ∀ k (hk : k < memCounterH.machineData.shape.insts.length),
        (memCounterH.machineData.shape.insts[k]).1 = memChildName true 4 8
    theorem mem_isMem : memChild? (memChildName true 4 8) = some (memModule true 4 8)

    def memNames : List String :=
      namesOfP memCounterH.machineData (fun _ => ofMem true 4 8) (fun _ => [ofMem true 4 8])

    theorem memCounterH_iface {mctx mref cctx cref}
        (hR : MachineDefines mctx mref cctx cref ``memCounterH memCounterH.machineData.shape)
        (y : Module × Design) (hy : RealChild mref cref ``memCounterH y) :
        ChildIfaceD ``memCounterH ((memCounterH.machineData.bsIn.take 3).filter (·.2 != .domain)).length
          (memCounterH.machineData.shape.layout.outs.map (·.name)) memNames y.1 y.2

    theorem memParent_closes {mctx mref cctx cref}
        (hRc : MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
        (hRm : MachineDefines mctx mref cctx cref ``memCounterH memCounterH.machineData.shape) :
        MachineClosesAt mctx mref cctx cref ``memParent memParent.machineData.shape

`memCounterH_iface` is `kidsChild_of_realM` with the data premises by
`decide` (the positions `ifaceDeep` decides, `ShippingChildIfaceGen.lean`
411–413, plus `hfne`), `hkid` by `memKidNamesP`, `hself` by
`ofDecl_not_mem_allMem`, the closing `memCounterH.noPortsMem_closes`
(`{mctx mref cctx cref} : MachineClosesAt …`, no premise
[R `ShippingNoPortsMemCommand.lean` 466–470]).

`memParent_closes` is the term `closesDeep` generates (`ShippingChildIfaceGen.lean`
285–300) with tables by pattern matching on the entry index: `cnt`'s
interface by the built leaf route (`seqChild_of_real … |>.toD`, 337–340),
`memCounterH`'s by `memCounterH_iface`; `hnames` / `hparent` / `hfresh` as
the generator writes them; `hparentD`, `hselfD`, `hdisjD` by
`ofDecl_not_mem_allMem` and "only entry 2 has names below it"
(`namesT_two`). Premises: the two reflections, nothing else.

ASSUMED, checked by the file's first theorem: the entries of `memParent` are
`[cnt, cnt, memCounterH]` (one per field of the structure call, then the
one-output call; `callEntriesG`). If `memParent_calls` fails, the tables are
indexed wrongly and the errors after it are consequences.

### 12.4 What is still missing after it

* The GENERATOR (unchanged from §7.1 item 4): `ifaceDeep`'s memory refusal
  (312) sits in a mutual `partial def`; the hand file shows the two terms a
  generator has to emit. With `AllMem` the name side needs no change to
  `Node` for THIS shape (a kid whose descendants are memory modules only):
  the kid's `names` is a `namesOfP … ofMem …` expression and the three
  descendant conditions are `ofDecl_not_mem_allMem` + "which entries have
  names". A kid mixing memory and declaration descendants needs both
  disciplines — not looked at.
* For the depth endpoint to stop asking the closings: a theorem of
  `memCounterH` and one of `memParent` under a name `closingThm?` finds
  (`.machine_closes_at` / `.closes_deep`, 108–111) in the form `∀ mctx mref
  cctx cref, (reflections) → MachineClosesAt …`. `memParent_closes` and
  `memCounterH.noPortsMem_closes` have that form; registering them under
  those names is the integrator's decision (§7.1, last paragraph) and is not
  done here — so S2.a is predicted WITH the warning.
* The check-free level (`GenKidM`, §7.2): not started.

## 13. Build order, `lean_lib` lines (round c-3)

1. `Tools.ShippingMachineDepthMemKidRunCommand` (imports the built
   `Tools.ShippingMachineDepthMemKidCommand`).
2. `Tools.ShippingMemNamesP` (imports the built `Tools.ShippingKidsChildIfaceM`,
   `Tools.ShippingModuleName`) — independent of 1.
3. `Tests.Compiler.MemDepthProbeTest` (one more import).
4. `Tests.Compiler.MemParentClosesTest` (imports 3, 2 and the built
   `Tools.ShippingChildIfaceGen`; it re-reads the probe's `.olean`, it does
   not rerun it).

    lean_lib «Tools.ShippingMachineDepthMemKidRunCommand» where
      roots := #[`Tools.ShippingMachineDepthMemKidRunCommand]

    lean_lib «Tools.ShippingMemNamesP» where
      roots := #[`Tools.ShippingMemNamesP]

Nothing for `Tests/AllTests.lean`.

## 14. Risks (round c-3), in order

1. **§10 is an inference.** I did not find a built kid with a `machineExtB`
   constant and no Bool entry to compare with; D0 measures it.
2. **K2, the `rfl`** for `f.machineExtB i bools bits (Signal.loop …) j =
   bools j`: the definition is added with `hints := .abbrev`
   (`addDef`), so `rfl` should unfold it; the built precedent of the same
   tactic is for a goal WITHOUT the constant.
3. **S2.a past the kid:** the grouped loop on a non-leaf kid with three
   arguments under a parent that also has a leaf kid — every piece is built,
   the combination is new (as `regsParent` was).
4. **`MemParentClosesTest`:** the entry list (`memParent_calls`); whether
   `cnt.machine_closes` exists in the probe's environment (the leaf route
   needs it; `#machine_endpoint parent` of `ShippingMachineSeqTest` should
   have left it [?]); the reduction of the pattern-matching tables at `k + 3`
   in `namesT_two` / `namesT_allMem`; `subst` of `k = 2` under hypotheses
   that mention `k`; name resolution of `memCounterH.machineData` under the
   two `open`s.
5. `ShippingMemNamesP`: `nomatch` on `x ∈ []`; the direction of the equation
   from `List.mem_map`.

## 15. Not determined by reading (round c-3)

* Whether D0 reproduces the message; whether K2, S2.a–c, SH.a–c pass.
* The output name the reader gives a one-output kid under the general
  closing (the `field` test of the grouped loop) — not looked up.
* Whether `cnt.machine_closes` is in the probe's environment.
* `closesDeep`'s body beyond the generated term; `GenKid`.

## Integrator's build record, round c-3 (2026-10-13) — MEASURED

BUILT on poc ecddf7d1 + these files, cgrun 3 GiB swap 0, runs `c3`, `c3b`, `c3c`, `c3ax`.
Integrator fixes (no statement changed): `Tools/ShippingMachineDepthMemKidRunCommand.lean` 125 — a nested
`← ppExpr dv` inside an `if` inside `pure (…)` ("must be nested inside a do expression"), hoisted into a
`let`; `Tests/Compiler/MemParentClosesTest.lean` — five test `def`s over reflected data (`memNames`,
`cntArgs`, `nkT`, `outsT`, `namesT`) crashed Lean's code generator ("unknown join point", ExplicitBoxing
panic) and are now `noncomputable def`. `Tools.ShippingMemNamesP`: as written.

Probe, every prediction confirmed:
* D0 `#machine_depth_run_of memCounterH 0` (the built kid step alone): FAILED "No goals to be solved" —
  the inferred failing line is reproduced in isolation.
* K2 `#machine_seq_child_memNR memCounterH 0`: OK. S2.a `#machine_depth_core memParent 1`: OK (1.4 s),
  S2.b `#machine_depth_ships memParent 1`: OK, S2.c `#machine_design_svNR memParent 1`: OK.
  SH.a–SH.c for `memGrand 2`: OK.
  So `memParent.machine_design_svNR1` and `memGrand.machine_design_svNR2` exist — the depth endpoints WITH
  their check antecedents and with the closing of the kid as a premise (not check-free).
* `MemParentClosesTest` (asserting): `memParent_closes : MachineDefines cnt → MachineDefines memCounterH →
  MachineClosesAt memParent` and `memCounterH_iface`, on `[propext, Classical.choice, Quot.sound]`
  (printed by the integrator). The closing premise of `memParent` is a theorem from two reflections, by
  hand; no generator produces it yet and no endpoint consumes it yet.
STATE: for a parent / grandparent of a memory-machine child, the trace endpoint and the depth endpoint
exist; the check-free design-level endpoint does not. Class OPEN at the check-free level.

# B / G1, unit U4: memory children (round par/b-13)

Branch `par/b-13`, base poc `fcabc921`. NOTHING here was built or run. Every
line about Lean code is "WRITTEN, NOT BUILT"; no premise of any endpoint
counts as removed until the integrator's build. "Read" = the line was read
in the file named; "inferred" = concluded from a neighbouring fact.

## 1. What was read

### 1.1 A certified-route memory is an instance of a memory-only submodule

* The reader: `Sparkle/Compiler/Elab.lean` 3946–3953 — a
  `Signal.memory` / `Signal.memoryComboRead` application
  (`MachMemory.memCall?`, `Sparkle/Compiler/MachMemory.lean` 24–38) is read
  as a CALL (`machInstance`, `Elab.lean` 4042–4069) of the placeholder name
  `memChildName combo aw dw` = `SparkleMem.{combo|sync}.aw.dw`
  (`MachMemory.lean` 41–43) with binder kinds `[.domain, .bits aw, .bits dw,
  .bool, .bits aw]`, result `.bits dw`; its four operands become hardware
  `let`s, the entry's field is `"out"` (`Elab.lean` 4069), and
  `instStruct := true` is set (3953). So a parent with a memory ALWAYS has
  `shape.instFields ≠ []` (`Elab.lean` 5180): the GENERAL closing.
* The module: `MachMemory.memModule combo aw dw` (`MachMemory.lean` 46–58):
  name `SparkleMem_{combo|sync}_{aw}_{dw}`; inputs `wa : aw`, `wd : dw`,
  `we : bit`, `ra : aw`, `clk`, `rst`; output `out : dw`; wire
  `out_rdata : dw`; body `[.memory "mem" aw dw "clk" wa wd we ra "out_rdata"
  combo [] [], .assign "out" (.ref "out_rdata")]`; its design is
  `{ topModule := name, modules := [m] }` — the module ITSELF is in its
  design (a real leaf child's design has no module).
* Where it enters the compile: `closeInstsGM` (`Elab.lean` 5206–5220):
  `match MachMemory.memChild? c with | some md => pure md | none => synth c`
  (`memChild?`: `MachMemory.lean` 61–66). The one-output closing
  `closeInstsM` (5189–5202) has no such case. The pure closing checks
  `memSelf` for every child (`Sparkle/IR/MachineInstG.lean` 137;
  `MachMemory.lean` 94–97).

### 1.2 What the parent's run gives for a memory child (there is no declaration)

* `Tools.ShippingChildInv.ChildrenReal` (`Tools/ShippingChildInv.lean`
  492–496): per entry `k`, `∃ y, children[k]? = some y ∧ (memChild?
  (insts[k]).1 = some y ∨ RealChild mref cref (insts[k]).1 y)`.
* `Tools.ShippingMachineEntry.MemChildren` (`Tools/ShippingMachineEntry.lean`
  862–864): `(insts.map (·.1))[k]? = some c → memChild? c = some md →
  children[k]? = some md`; it is the third conjunct of the GENERAL disjunct
  of `CloseCalls` (928–934).
* Both come out of ONE theorem every `core_*` proof starts from:
  `synthesizeMachineCertified_runs` (`Tools/ShippingChildRun.lean` 528–540),
  which has NO memory hypothesis (`closeInstsGM_run`,
  `Tools/ShippingCallsClose.lean` 58–100, proves the memory case of the
  child list).
* `memChild_eq` (`Tools/ShippingMachineInstG.lean` 437): `memChild? c = some
  md → ∃ cb aw dw, md = memModule cb aw dw`.

So the "RealChild-like fact" of a memory entry is: its child IS
`memModule cb aw dw` (an equation, not a run). Combined: under the general
closing every child `y` of entry `k` satisfies

    Kid mref cref c y := memChild? c = some y ∨ (memChild? c = none ∧ RealChild mref cref c y)

(`Tools.ShippingMemKid.Kid`, `kid_of`; WRITTEN this round).

### 1.3 The endpoints and their check premises

* `seqMem.machine_design_svR0` (`#machine_design_svR0`,
  `Tests/Compiler/ShippingChildBoundaryTest.lean` 72): generator
  `generateDesignR0` (`Tools/ShippingMachineSeqCommandR.lean` 336–338) =
  `ShippingShipsDesignSVCommand.compose f f.machine_ships_hierR
  f.machine_design_svR0 0` (`Tools/ShippingShipsDesignSVCommand.lean` 49–73):
  the head `ships_design_svN_all 0` (`Tools/ShippingShipsDesignSVAll.lean`
  30–98) on `f.machine_ships_hierR` (`generateShipsR`, `…SeqCommandR` 328–332
  → `ShippingMachineShipsHierCommand.generateWith` 48–133, `headA?` set:
  `machine_ships_hierC` with 24 arguments and a decided 25th, 118–127).
  Statement shape, READ off the head (the generated statement itself was not
  printed):

      ∀ {mctx mref cctx cref w w' b design},
        RunsTo (synthesizeCombinational seqMem) … (b, design) w' →
        MachineDefines … seqMem seqMem.machineData.shape →
        MachineClosesAt … seqMem seqMem.machineData.shape →
        ∃ raw D, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
          (shipsHierCheck (childMap D.modules) b = true →
           designCheck (childMap D.modules) 0 (checkedOptimize b) = true →
           outsCheck (childMap D.modules) 0 (checkedOptimize b) = true →
           Bnd raw D →                                  -- ChildBnd mref cref w ∧ MachineDefines … cnt …
           kidsMixed (childMap D.modules) b.body = true →
           ∃ ids …, … DesignSV (childMap D.modules) 0 (checkedOptimize b) … )

  `Bd = kidsMixed`: READ (`generateWith` 86: `Reset1` route ⇒ `kidsMixed`,
  `mixKS_boundedIn`, `mixInv`); the route is `.seq` because not every callee
  is a memory (`hierRoute` 40–43). The boundary: READ (`…SeqCommandR`
  244–259: one conjunct per sequential child; `cnt` has `machine_closes`, so
  only `MachineDefines cnt`; a memory callee is not among `seqKids`, 36–38,
  and its per-entry case is closed by evaluating `memChild?`, 273–274).
  The four checks are evaluated `true` on the shipped design at
  `ShippingChildBoundaryTest` 112–123 (BUILT).
* `memCounter.machine_design_sv0` (`#machine_design_sv0`,
  `Tests/Compiler/ShippingDesignSVMemTest.lean`; `generate0`,
  `…ShipsDesignSVCommand` 81–83): the same head on
  `memCounter.machine_ships_hier` — `machine_ships_hier` (NOT `…C`: 11
  arguments, no closing premise `C`; `generateWith` 123–124), route `.mem`:
  `Reset = ResetM`, `Bd = kidsMem`, `Inv = memInv` (86–98), and `Bnd` is the
  OLD boundary (the premises of `memCounter.machine_composedT` after its
  eleven binders, 60–65). So its check premises are `shipsHierCheck`,
  `designCheck … 0`, `outsCheck … 0`, `kidsMem` (the census's "inferred
  `kidsMixed`" is wrong for the five memory-only parents: it is `kidsMem`).
  No `…_svR0` exists for them (`#machine_design_svR0` was never run on a
  parent whose callees are ALL memories).
* The checks: `kidsMem` / `memInv` / `memKS_boundedIn`, `kidsMixed` /
  `mixInv` / `mixKS_boundedIn` — `Tools/ShippingMachineShipsHier.lean`
  704–879; `kidsMasked` 667–672; `designCheck`, `textCheckI` —
  `Tools/ShippingDesignSV.lean` 103–124; `kidCheck` —
  `Tools/ShippingChecksDesign.lean` 119–122; `leafCheck` —
  `Tools/ShippingDesignSVLeaf.lean` 96–100.

### 1.4 Where `hnomem` is consumed, and why

`grep` over `Tools/`: 34 files mention `hnomem`. By reading every use that
is not a binder or an argument passed on, it is CONSUMED at ten places, all
of ONE form — a child's witness `hor : memChild? c = some y ∨ RealChild …`
is split and the left case refuted (`rw [hnomem …] at hmem; cases hmem`):

| file:line | theorem |
|---|---|
| `Tools/ShippingChecksCore.lean` 216 | `core_kids_facts` |
| `Tools/ShippingChecksRun2.lean` 96, 134 | `kidsDesign_real` |
| `Tools/ShippingChecksWidths.lean` 192 | `core_callPorts` |
| `Tools/ShippingChecksOuts.lean` 175 | `core_outsExtracted` |
| `Tools/ShippingPortsMatchRaw.lean` 341 | `core_callConns` |
| `Tools/ShippingKidsSelf.lean` 135 | `core_kids_self` |
| `Tools/ShippingKidsChildIface.lean` 263 | `kidsChild_iface` |
| `Tools/ShippingCallsGate.lean` 306 | `machineClosesAt_of_gateKids` |
| `Tools/ShippingOneOutConns.lean` 320 | `core_callConns₁` |
| `Tools/ShippingCallsRunG.lean` 79 | `closeInstsGM_run_all` (the only other form: the `mapM` body is rewritten to `synthesizeChild`) |

Why: NOT because a lemma is false with a memory. The per-child facts of
these theorems are HYPOTHESES quantified over `RealChild`; a memory child
has no `RealChild` witness, so with a memory entry the hypotheses say
nothing about that child and the proof has no fact to use for it. Nothing
else in the proofs reads what a child is. `core_clk`
(`Tools/ShippingCoreClk.lean` 57–75) carries `hnomem` as a binder its proof
never uses.

### 1.5 Existing lemmas about memory modules

* `Tools/ShippingDesignSVMem.lean`: `leafCheck_memModule` (37),
  `outsLeaf_memModule` (54), `MemKids` (59), `kidsPass_memKids` (63),
  `designCheck_memKids` (79: `textCheckI C o → MemKids C o.body →
  designCheck C 0 o ∧ outsCheck C 0 o` — for a parent whose instances are
  ALL memories, given the parent's own `textCheckI`).
* `Tools/ShippingMachineShipsHier.lean`: `memKS_boundedIn` (748),
  `mixKS_boundedIn` (855), `kidsMixed_of_masked` (881),
  `memParams_memModule'` (849), `composedG_of_T` (482), `composedG_of_Tmem`
  (534).
* `Tools/ShippingHierMem.lean`: `memChild_run` (34), `memSyncChild_run`
  (100) — the module's stateful run (S5 / F6, `runModuleT`).
* `Tools/ShippingMachineMemLinked.lean`: `machine_linkedT_mem` (196);
  `Tools/ShippingMachineCallsLinkedT.lean` 34 (`MemFacts`), used by
  `#machine_composedT(S|SR)` (`Tools/ShippingMachineSeqCommand.lean`
  `memTactic` 126–138).
* `Tools/ShippingChecksDerived.lean` 105–111: `kidsMem_of_seqOk`,
  `kidsMixed_of_seqOk` (instance-free bodies only).
* The closing generators REFUSE a memory child:
  `Tools/ShippingMachineClosesAtGenG.lean` 33–34,
  `Tools/ShippingChildIfaceGen.lean` 266–267; the check-free generators too:
  `Tools/ShippingNoPortsCommand.lean` 90, `…NoPortsKidsCommand` 89,
  `…ShipsFreeCommand` 61, `…ShipsNoOutsCommand` 61.

## 2. The smallest correct target

### 2.1 `KidFacts` cannot be the interface of a memory child — three findings

`Tools.ShippingKidFacts.KidFacts mref cref c outs ins n`
(`Tools/ShippingKidFacts.lean` 72–99):

1. EVERY field quantifies over `RealChild mref cref c y`. For a memory
   placeholder `c` no `RealChild` witness is produced by the run (§1.2), so
   `KidFacts` of it would be about nothing the parent's proof meets. Not a
   false field — a vacuous interface.
2. `masked : outsMaskedN y.1 = true` is FALSE of `memModule cb aw dw`:
   `outsMaskedN` (`Tools/ShippingMachineShipsDepth.lean` 155–160) asks
   `noMem y.1.body` and every output assigned by a constant or a slice
   (`selfMasked`, `…ShipsHier` 578–581); the module's body is a memory
   statement and `out := out_rdata`. Weakest replacement that feeds the
   consumer of a memory parent (`Bd = kidsMixed`): per kid,

       FlatOk y.1 := (noMem y.1.body ∧ y.1.outputs.all (outMasked (declWidth y.1) y.1.body)) ∨
                     ∃ cb aw dw, y.1 = (memModule cb aw dw).1

   and, on the PARENT side, that no connection of a memory instance names
   `out_rdata` (`kidsMem`'s first conjunct) — a fact about EVERY connection
   of the call group's statement, which `core_callConns` (reference
   connections only) does not state.
3. `check` at `n ≥ 1` is FALSE of the memory module: `kidCheck C (k+1) =
   designCheck C k` asks `textCheckI`, whose first conjunct `seqStmtOkI`
   (`Tools/ShippingHierSVSoundness.lean` 30–33) rejects `.memory`. At
   `n = 0` it is `leafCheck`, TRUE (`leafCheck_memModule`). So a memory child
   has the interface at depth 0 only; this is a limit of the depth
   semantics' check (`levelCheck`, `Tools/ShippingDesignSVBounds.lean`
   161–163), not of this unit.

The other fields (`outsIn`, `outTys`, `kidA`, `kidR`, `portsIn`, `inW`,
`clk`) hold of the memory module, for every read kind and widths, with
`outs = [out : BitVec dw]` and `ins = [aw, dw, 1, aw]`.

### 2.2 The target, as written

    structure KidFactsM mref cref c outs ins n   -- KidFacts' fields over Kid; `masked` ↦ `flat : FlatOk y.1`
    theorem kidFacts_toM  : KidFacts mref cref c outs ins n → memChild? c = none → KidFactsM mref cref c outs ins n
    theorem memKid_facts  : memChild? c = some (memModule cb aw dw) →
                              KidFactsM mref cref c (memOuts dw) (memIns aw dw) 0

and the consumers, same shape as `kids_*` with `hnomem` gone
(`hsl`, `hfne` kept; `hfne` now also carries "the general closing"):

    kidsM_runFacts    : … → RunFacts (childMap D.modules) b
    kidsM_outsCheck   : … → hierGate b = true → outsCheck (childMap D.modules) n (checkedOptimize b) = true
    kidsM_mixed       : … → kidsMixed (childMap D.modules) b.body = true          -- NOT kidsMaskedN
    kidsM_designCheck : … → callWidthsOk … → callArgsOk … → … → designCheck (childMap D.modules) n (checkedOptimize b) = true

The head is the BUILT `Tools.ShippingNoPorts.machine_design_noPorts`
(`Tools/ShippingNoPorts.lean` 42–174), unchanged, at `n = 0`: it is
parametric in `Reset`, `Bnd`, `C`, `Bd`, `Inv`, `hBd`, `hRI`, and
`KSn _ 0 = flatKS` (`Tools/ShippingHierStateG.lean` 628–630), so the depth-0
endpoint's own `Reset1` / `kidsMixed` / `mixInv` / `mixKS_boundedIn` are
passed through (as `compose … 0` already does for `ships_design_svN_all`).

## 3. WRITTEN this round — not built

    Tools/ShippingMemKidCore.lean    Kid, kid_of, Kid.real, Kid.mem; core_kids_factsM, core_raw_factsM,
                                     core_linkedWFM, core_instOuts_not_assignedM, core_outsExtractedM,
                                     core_callPortsM, core_instOutWidthsOkM, core_hierGateM,
                                     core_runFactsM, core_outsCheck_all_gateM
    Tools/ShippingMemKidPorts.lean   core_closed_typedInM, core_clkM, core_callConnsM, core_callStmtM,
                                     core_portsMatch_rawM, core_kids_selfM, core_kidsPass_deepM,
                                     core_designCheck_runM
    Tools/ShippingMemKidFacts.lean   callStmtG_portNames, FlatOk, kidsMixed_of, the memory module's facts
                                     (mem_outsIn, mem_portsIn, mem_weS, mem_inW, mem_conns_noRdata, …),
                                     KidFactsM, kidFacts_toM, memKid_facts, calleeAt, hkidW_of_dataM,
                                     core_kidsMixedM, kidsM_runFacts / _outsCheck / _mixed / _designCheck
    Tests/Compiler/NoPortsMemSeqMemTest.lean   seqMem by hand + audit
    Tests/Compiler/NoPortsMemDataProbe.lean    logs only (the five memory-only parents)

The two `…Core` / `…Ports` files are SCRIPTED COPIES of the BUILT chain
(17 theorems, and `core_callStmtM`; sources named per section). The script's changes, all of
them: the name gets `M`; the `hnomem` binder is dropped (theorem with
`hfne`) or replaced in place by `hfne`; `RealChild mref cref` ↦ `Kid mref
cref`; calls of copies; at the five consuming places of §1.4 that are in
the chain, the three refuting lines become `have hre := kid_of … hMC … hor`,
with `hMC : MemChildren d.shape children` taken from `CloseCalls`' general
disjunct right after the run is opened. `core_callStmtM` is
`core_callConnsM` cut after the resolution of the instance, returning
`CallStmtG`. Nothing of the originals is changed.

Main statements, verbatim:

    def Kid (mref) (cref) (c : Name) (y : Res) : Prop :=
      memChild? c = some y ∨ (memChild? c = none ∧ RealChild mref cref c y)

    theorem kid_of {shape : MachineShape} {children : List Res} {k : Nat}
        (hk : k < shape.insts.length) (hMC : MemChildren shape children) {y : Res}
        (hy : children[k]? = some y)
        (hor : memChild? (shape.insts[k]).1 = some y ∨ RealChild mref cref (shape.insts[k]).1 y) :
        Kid mref cref (shape.insts[k]).1 y

    theorem callStmtG_portNames (h : CallStmtG nIn kI n names args outs mc (Stmt.inst mn iname conns))
        {cn : String × Expr} (hm : cn ∈ conns) :
        (∃ q ∈ inPortsOf mc, q.name = cn.1) ∨ cn.1 = "clk" ∨ cn.1 = "rst" ∨ ∃ p ∈ mc.outputs, p.name = cn.1

    theorem memKid_facts {c : Name} {cb : Bool} {aw dw : Nat}
        (hc : memChild? c = some (memModule cb aw dw)) :
        KidFactsM mref cref c (memOuts dw) (memIns aw dw) 0

    theorem core_kidsMixedM … (hins) (hfne) (outTy)
        (hkidF : ∀ k hk (y : Res), Kid mref cref (d.shape.insts[k]).1 y → FlatOk y.1)
        (hB) (hcore) (hpost) (entry) (closes) :
        kidsMixed (childMap D.modules) b.body = true

    theorem kidsM_designCheck … (hins) (hsl) (hfne) (outTy) (kidOuts) (kidIns) (n : Nat)
        (hkid : ∀ k hk, KidFactsM mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
        (hcw : callWidthsOk d nDecl kidOuts = true) (hargs : callArgsOk d nDecl kidIns = true)
        (hB) (hcore) (hpost) (entry) (closes) (hon) (hoty) :
        designCheck (childMap D.modules) n (checkedOptimize b) = true

## 4. Per declaration

| declaration | endpoint | premise (of the base endpoint) | predicted state |
|---|---|---|---|
| `seqMem` | `seqMem.machine_design_noPortsR0` | `shipsHierCheck (childMap D.modules) b` (of `seqMem.machine_design_svR0`) | WRITTEN — predicted absent, pending build |
| | | `kidsMixed (childMap D.modules) b.body` | predicted absent, pending build |
| | | `designCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | | `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | | `MachineClosesAt seqMem` | STILL A PREMISE (binder). No closed form: nothing derives the closing of a parent with a memory child (§5.1) |
| | | the boundary `ChildBnd ∧ MachineDefines cnt`; `hr`; `MachineDefines seqMem` | stay, unchanged; NO binder added |
| `memCounter`, `twoMems`, `mixedMems`, `memWide`, `syncNarrow` | `f.machine_design_sv0` | `shipsHierCheck`, `kidsMem`, `designCheck 0`, `outsCheck 0`, the old boundary | STILL PREMISES — nothing written (§5.2); the probe logs their data |
| `withMemory` | none design-level | — | not touched |

## 5. Blocked: the exact missing statements

### 5.1 The closing of a parent with a memory child (`MachineClosesAt`)

`machineClosesAt_of_kidsD` (`Tools/ShippingCallsKidsD.lean` 98–320) asks
`hnomem` and uses it through `closeInstsGM_run_all`
(`Tools/ShippingCallsRunG.lean` 56–94), whose proof rewrites the `mapM` body
to `synthesizeChild` and then uses `mapM_loop_all` with `synthesizeChild`'s
post / depth / pin facts. Missing:

    -- (M1) the run of the general closing with memory entries, WITH the pairing clause
    theorem closeInstsGM_run_allM (L : RefLaws mref cref) (hB : ∀ L', BodyRel L')
        {shape t m₀ d₀ r} {w w'} (hw : InvV L w) (hd : L.dval w ≠ 0)
        (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
        ∃ children, r = closeInstsG (machNIn shape) shape.insts.length shape.layout.slots.length
            (t.inputs.map (·.name)) (shape.insts.map (·.2.1)) shape.instFields children (m₀, d₀) ∧
          (children.length = shape.insts.length ∧
            ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
              Kid mref cref (shape.insts[k]).1 y) ∧
          (∀ i j c, i < j → (shape.insts.map (·.1))[i]? = some c →
            (shape.insts.map (·.1))[j]? = some c → children[i]? = children[j]?) ∧ InvV L w'
    -- needs `mapM_loop_all` for a body that is `pure md` on memory names (its per-element
    -- hypothesis as stated — Tools/ShippingCallsSame.lean, not read to the end — is about
    -- synthesizeChild); `closeInstsGM_run` (CallsClose 58) has everything but the pairing.

    -- (M2) the closing itself
    theorem machineClosesAt_of_kidsDM … (hfne) (nk) (outsK) (namesK)
        (hkid : ∀ k hk (y : Res), Kid mref cref (d.shape.insts[k]).1 y →
          ChildIfaceDM (d.shape.insts[k]).1 (nk k) (outsK k) (namesK k) y.1 y.2) … :
        MachineClosesAt mctx mref cctx cref declName d.shape
    -- where ChildIfaceDM is ChildIfaceD (CallsKidsD 38–52) with
    --   `name : b.name = c.toString`  ↦ a printed name per entry (the memory module's name is
    --        `SparkleMem_combo_4_8`, NOT `c.toString = "SparkleMem.combo.4.8"`), and the name
    --        separation premises `hsep` / `hparent` / `hfresh` / `hparentD` / `hselfD` / `hdisjD`
    --        restated over those printed names;
    --   `noMem : memParams? b = none` ↦ `memSelf`-ready: `memParams? b = none ∨ ∃ cb aw dw, b = (memModule cb aw dw).1`
    --        (hdesign's first conjunct of `closeInstsG_of_run`, CallsRunG 131–133, is then
    --        `isMemModule cb aw dw (memModule cb aw dw).1 = true`, decidable per parameter only —
    --        a general proof needs it for all `aw dw`: not read whether one exists);
    --   `desNames` / `closed` / `resolves`: the memory module's design is `[itself]`, so
    --        `hselfD` (`c.toString ∉ namesK k`) must not be asked of a memory entry.
    -- `closeInstsG_of_run` itself (CallsRunG 97–138) has NO memory hypothesis: it is stated
    -- over `children` and can be reused as it is.

Until (M1)/(M2) (and a generator), `seqMem`'s endpoint keeps
`MachineClosesAt seqMem` as a binder, exactly as `…_svR0` does.

### 5.2 The five memory-only parents

1. No derived-boundary shipping theorem: `f.machine_ships_hierR` does not
   exist for them (only `f.machine_ships_hier`, built from
   `machine_ships_hier` — no `C`, old boundary, `Bd = kidsMem`, `Inv =
   memInv`, `Reset = ResetM`). `machine_design_noPorts` needs the `…C` form
   (`soundL` / `composed` under `C` and `Bnd`). Whether `#machine_design_svR0
   memCounter` goes through is NOT read to the end (`generateCoreSR` with
   `seqKids = []`): measured by `NoPortsMemDataProbe`.
2. If it does: its `Bd` is `kidsMem` (route `.mem`), not `kidsMixed`.
   Missing, a few lines over what is written:

       theorem core_kidsMemM … (hkidF : ∀ k hk (y : Res), Kid mref cref (d.shape.insts[k]).1 y →
             ∃ cb aw dw, y.1 = (memModule cb aw dw).1) … :
           kidsMem (childMap D.modules) b.body = true
       -- core_callStmtM + mem_conns_noRdata + a `kidsMem_of` (all-statements form of kidsMem_one)

3. `hsl : d.shape.layout.slots ≠ []` — whether a `Signal.loop` parent's
   registers are `layout.slots` is NOT read; the probe logs
   `slots=…, loops=…`. If they are not, the missing statement is U5's (the
   parent's `clk` / `rst` without a slot: `core_clkM`, `core_raw_factsM`).
4. The closing (§5.1) for a parent ALL of whose children are memories.

### 5.3 Depth ≥ 1 with a memory child

Not derivable under the present check: finding 3 of §2.1. A memory under a
depth parent needs `levelCheck` / `kidCheck` to accept the memory module at
every level (a statement change of `designCheck`, not designed here).

## 6. Build queue (integrator)

`lakefile.lean`:

    lean_lib «Tools.ShippingMemKidCore» where
      roots := #[`Tools.ShippingMemKidCore]

    lean_lib «Tools.ShippingMemKidPorts» where
      roots := #[`Tools.ShippingMemKidPorts]

    lean_lib «Tools.ShippingMemKidFacts» where
      roots := #[`Tools.ShippingMemKidFacts]

`Tests/AllTests.lean`:

    import Tests.Compiler.NoPortsMemSeqMemTest

`Tests.Compiler.NoPortsMemDataProbe`: TARGET-BUILT ONLY (where its second
command succeeds it leaves `memCounter.machine_…R` constants in its own
module).

Order: (1) `Tools.ShippingMemKidCore`; (2) `Tools.ShippingMemKidPorts`
(imports 1); (3) `Tools.ShippingMemKidFacts` (imports 2,
`Tools.ShippingKidFacts`, `Tools.ShippingDesignSVMem`); (4)
`Tests.Compiler.NoPortsMemSeqMemTest` (imports 3, `NoPortsGrandHTest`,
`ShippingChildBoundaryTest`, `Tools.ShippingLeafKidFacts`); independently
(5) `Tests.Compiler.NoPortsMemDataProbe` (imports `ShippingDesignSVMemTest`,
`Tools.ShippingMachineSeqCommandR`). A partial result is usable: (1) alone
gives `core_runFactsM` and `core_outsCheck_all_gateM`.

Name clashes checked by `grep`: no module defines a constant under
`Tools.ShippingMemKid`, `seqMem.machine_design_noPortsR0` or
`Tests.Compiler.NoPortsMemSeqMemTest`; no file of worker A's prefixes is
touched.

## 7. UNVERIFIED, in risk order

1. `Tools/ShippingMemKidFacts.lean`, the memory module's facts: `mem_weS`
   (a `simp` with `decide := true` over `moduleWof` on a module with
   symbolic widths — the set of `leafCheck_memModule`, BUILT, minus what it
   does not need); `mem_inPorts` (`rfl` through a `List.filter` on string
   inequalities, `simp` as the second alternative); `mem_inW` (`match j, hq
   with`, `Option.some.inj h` on a list literal's `[k]?`, `absurd h (by
   simp)` at `j + 4`); `kidsMasked_one` / `kidsMem_one` (`simp` unfolding
   the `match` of `kidsMasked` / `kidsMem` on `.inst`, rewriting `C mn` and
   `conns.any …` by hypotheses); `mem_outsAssigned` (`rfl`, else `simp`);
   the `have hp' : p ∈ [literal] := hp` steps (defeq through `memModule`'s
   `let`s); `decide` on closed string disequalities after `show`.
2. `NoPortsMemSeqMemTest`: nothing about `seqMem`'s reader data was measured
   (`nDecl = 3` asserted first; the hand theorems pass `(nDecl := 3)`);
   `seqMem_entry` (a kernel `decide` of a disjunction of `Name` equalities
   against `memChildName true 4 8`, unfolded by the kernel);
   `seqMem_callWidths` / `seqMem_callArgs` (kernel evaluation through
   `outsOf` / `insOf` / `calleeAt`; the memory entry's field must be `"out"`
   and its four `let` binders of widths 4, 8, 1, 4); `rw [h, outsOf_cnt,
   insOf_cnt]` (the callee's `Name` literal printed by the two ` `` `
   quotations being the same term); `generateR0` — the head
   `machine_design_noPorts` at `n = 0` with the `flatKS` arguments of
   `seqMem.machine_ships_hierR` (`mkAppOptM` must see `KT 0` as `KidState`,
   `KSn _ 0` as `flatKS`; `compose … 0` relies on the same for another head),
   the 25 arguments / 11 binders (READ off `generateWith`, measured only for
   the `NR` family), `dischargeWith … #[]` finding `ChildBnd` and
   `MachineDefines cnt` among the boundary's conjuncts; audit (e): the
   proposition binders printed the same as the base endpoint's.
3. The scripted copies (`…Core`, `…Ports`): the lone `·` after each `have
   hre := kid_of …`; `hMC` by `rcases hcc with ⟨hf0, -⟩ | ⟨-, -, h⟩` before
   the proof's own `rcases hcc`; `open Tools.<Source>` in a `section` giving
   the copied proof its unqualified helpers (no name of a source namespace
   is also in a commonly opened one — checked by a script over the
   declarations, not by elaboration); `Kid` unfolded by `exact Or.inl h` /
   `rcases` in `kid_of`, `Kid.real`, `Kid.mem`; `core_callStmtM`'s final
   `exact ⟨…, _, _, _, _, args, outs, hcs⟩`; unused hypotheses left by the
   cut (linter warnings only).
4. `callStmtG_portNames` (modelled line by line on the BUILT
   `callStmtG_conn`; `List.of_mem_zip`); `core_kidsMixedM` (`rw [hmem] at
   hcs hCm`); `flatOk_of_masked` (`rw [Bool.and_eq_true] at h` taking the
   outer conjunction).
5. `NoPortsMemDataProbe`: `generateDesignR0` on a memory-only parent inside
   `try` (a failure after `generateSR`'s own rollback may leave
   `…composedTRA`); the field `shape.loops`.

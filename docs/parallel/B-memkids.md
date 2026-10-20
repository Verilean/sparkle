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


---

# Round par/b-14 — memory-only parents

Branch `par/b-14` from 4a0d8356. WRITTEN, NOT BUILT: nothing below counts as
removed until the integrator builds it. No Lean was run.

## 8. Memory-only parents: what was read

### 8.1 The probe's real log (MEASURED — corrects §5.2 items 1 and 3)

`docs/parallel/verification-b13.md` 88–92 quotes only the first physical line
of each probe message. The full lines are in the run's log
(`~/sparkle-work/runs/20261013-055644-b13b-alltests/log*`, READ this round):

| declaration | nDecl | binders | call entries | argument lets | instFields | slots | lets | loops |
|---|---|---|---|---|---|---|---|---|
| `memCounter` | 3 | 10 | `[SparkleMem.combo.4.8]` | `[[1,2,3,0]]` | `[out]` | 2 | 4 | 1 |
| `twoMems` | 3 | 12 | `[SparkleMem.combo.4.8, SparkleMem.combo.4.8]` | `[[1,2,3,0],[0,2,3,4]]` | `[out,out]` | 2 | 5 | 1 |
| `mixedMems` | 3 | 12 | `[SparkleMem.combo.4.8, SparkleMem.sync.4.8]` | `[[1,2,3,0],[1,4,3,0]]` | `[out,out]` | 2 | 5 | 1 |
| `memWide` | 3 | 10 | `[SparkleMem.combo.6.16]` | `[[1,2,3,0]]` | `[out]` | 2 | 4 | 1 |
| `syncNarrow` | 3 | 10 | `[SparkleMem.sync.3.5]` | `[[1,2,3,0]]` | `[out]` | 2 | 4 | 1 |

For all five: constants present `[machineData, machine_ok, machine_body,
machine_ships_hier, machine_design_sv0]`; absent `[machine_closes,
machine_ships_hierR, machine_design_svR0]`. And:

    NOPORTS MEM PROBE R0 …memCounter: REFUSED — …memCounter: no sequential child

Consequences (MEASURED):

* the `Signal.loop` registers ARE `layout.slots` (2 each): `hsl :
  d.shape.layout.slots ≠ []` holds; the "parent without a register" axis does
  NOT apply to any of the five;
* `instFields ≠ []`: they are tied by the general closing (`hfne` holds);
* `#machine_design_svR0` does not go through — not for a missing register:
  `generateCoreSR` builds the composed theorem from the sequential children
  (`Tools/ShippingMachineSeqCommandR.lean` 36–38 `seqKids` = the callees that
  are not memories; 93 `let some (_, sh0) := shCases.head? | throwError "…: no
  sequential child"`).

### 8.2 The statement template of `f.machine_design_sv0` for a memory-only parent (READ)

`#machine_design_sv0 f` = `generate0` (`Tools/ShippingShipsDesignSVCommand.lean`
82–84): `compose f f.machine_ships_hier f.machine_design_sv0 0` (48–72), i.e.
`ships_design_svN_all 0 Reset Bnd Bd` (`Tools/ShippingShipsDesignSVAll.lean`
30–98) with `Reset`, `Bnd`, `Bd` read off the proof term of
`f.machine_ships_hier` (57: arguments 3, 4, 5).

`f.machine_ships_hier` = `generateWith` without `headA?`
(`Tools/ShippingMachineShipsHierCommand.lean` 48–133, branch 122–124): the
head `machine_ships_hier` (`Tools/ShippingMachineShipsHier.lean` 324–414),
which is `machine_ships_hierC` at `C := fun … => MachineCloses … declName
d.shape` with the wired endpoint wrapped as `fun hr e c _ => soundL hr e c`
(412–414). On the route `.mem` (40–43: every callee has `memWidths?`):
`Reset = ResetM` (75; def `ShippingMachineShipsHier` 529–530), `Bd = fun b D
=> kidsMem (childMap D.modules) b.body = true` (86–91; def 719–726), `Inv =
memInv` (96; 709–710), `hBd = memKS_boundedIn` (89; 748), `hRI = resetM_inv`
(98; 712), `KS = fun _ => flatKS` (99–100).

So, for `f ∈ {memCounter, twoMems, mixedMems, memWide, syncNarrow}`:

    theorem f.machine_design_sv0 {mctx mref cctx cref w w' b design}
        (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
        (entry : MachineDefines mctx mref cctx cref f f.machineData.shape)
        (closes : MachineCloses mctx mref cctx cref f f.machineData.shape) :
        ∃ raw D, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
          (shipsHierCheck (childMap D.modules) b = true →                    -- (1)
           designCheck (childMap D.modules) 0 (checkedOptimize b) = true →   -- (2)
           outsCheck (childMap D.modules) 0 (checkedOptimize b) = true →     -- (3)
           True →                                                            -- (4) the boundary
           kidsMem (childMap D.modules) b.body = true →                      -- (5)
           ∃ ids …, ∀ i bools bits T ins st0 mems (kids : String → KT 0), … → ResetM raw D kids → … →
             (∃ envsO, DesignSV (childMap D.modules) 0 (checkedOptimize b) … ∧ …) ∧ ∀ envs', …)

Each premise:

* (1) `shipsHierCheck`: antecedent of `machine_ships_hierC`'s conclusion
  (`ShippingMachineShipsHier` 225), kept by `ships_design_svN_all` (77);
* (2) `designCheck … 0`, (3) `outsCheck … 0`: added by `ships_design_svN_all`
  (79, 81);
* (4) **"the old boundary" is `True`** — it is NOT `BoundaryOf` /
  `InstOfCall` / a reflection. READ: `Bnd` is the conjunction of the composed
  theorem's premises after its eleven run binders
  (`ShippingMachineShipsHierCommand` 58–65; `conj [] = True`, 17–18); the
  composed theorem of a memory-only parent is `machine_linkedT_mem` applied to
  the wired head (`Tools/ShippingMachineMemCommand.lean` 56–100), whose run
  binders are `hr`, `entry`, `closes : MachineCloses`
  (`machine_traceL_of_loop_causal`, `Tools/ShippingMachineSeqLinked.lean`
  102–105) and nothing else; `machine_linkedT_mem`'s further hypotheses
  (`Tools/ShippingMachineMemLinked.lean` 208–229) are all discharged by the
  generator. INFERRED (not measured): hence `hBs = []`. The new generator
  ASSERTS it (throws unless the boundary argument is `fun … => True`), and the
  audit asserts an antecedent printed `True` in the old endpoint;
* (5) `kidsMem`: the `Bd` of the route;
* the binder `closes` is **`MachineCloses`** — every world, every logger
  (`Tools/ShippingMachineEntry.lean` 2279–2284) — not `MachineClosesAt`
  (`Tools/ShippingChildRun.lean` 444–449). The comment at
  `ShippingChildRun` 439–443 says "for a shape with calls only this form
  [`MachineClosesAt`] can hold: the calls' closing reads the child-synthesis
  reference". Whether `MachineCloses` holds of a shape all of whose calls are
  memories (whose children are `pure md`, §1.2) was NOT read.

### 8.3 What the R0-style head needs that a memory-only parent lacks (READ + MEASURED)

`seqMem.machine_design_noPortsR0` is `machine_design_noPorts` at `n = 0`
(`Tools/ShippingNoPorts.lean` 42–162) on the arguments of
`seqMem.machine_ships_hierR`, which is `machine_ships_hierC` with `C =
MachineClosesAt`, `Bnd = ChildBnd ∧ reflections` (`generateShipsR`,
`ShippingMachineSeqCommandR` 328–332). What is lacking for a memory-only
parent is ONLY the constant `f.machine_ships_hierR` (its generator refuses,
§8.1). The head itself asks nothing a memory-only parent lacks:

* no register hypothesis in the head; `hsl` is asked by `kidsM_runFacts` and
  `kidsM_designCheck` (`core_clkM`, `core_raw_factsM`) and HOLDS (slots = 2);
* the head is generic in `C`, `Bnd`, `Bd`, `Inv`, `Reset`; `machine_ships_hier`
  is `machine_ships_hierC` at `C := MachineCloses`, so the head applies to the
  arguments of the EXISTING `f.machine_ships_hier` with that `C` — provided the
  boundary is one under which the four run hypotheses can be proved.

The built `kidsM_*` theorems all take `hB : ChildBnd mref cref w` and `closes
: MachineClosesAt` (`Tools/ShippingMemKidFacts.lean` 580, 585; 608, 613; 679,
684; 711, 716). The second follows from `MachineCloses`
(`machineClosesAt_of_closes`, `ShippingChildRun` 452–455). The first does NOT
follow from the old boundary `True`: this is the one thing a memory-only
parent's old endpoint lacks. So the new endpoint's boundary is `ChildBnd mref
cref w` — an antecedent ADDED against `f.machine_design_sv0`.

### 8.4 The hypotheses of the built `kidsM_*` theorems, for `memCounter`

| hypothesis (`kidsM_runFacts` 564–590, `_outsCheck` 594–619, `_designCheck` 694–739) | status for `memCounter` |
|---|---|
| `ok : d.ok = true` | constant `memCounter.machine_ok` present (MEASURED) |
| `hbody` | constant `memCounter.machine_body` present (MEASURED) |
| `hC : d.callsOk nDecl = true`, `nDecl = 3` | `nDecl = 3` MEASURED; `callsOk 3` NOT MEASURED (`Tools/ShippingCallsShape.lean` 106–113: `nDecl + insts.length = d.nIn`, argument lets `< d.ls.length`, `fieldsOkB`, `reads … posOk`) — decided by `memCounter_calls`; no existing theorem of a `Signal.loop` memory parent decides it (`machine_linkedT_mem` asks other data facts, 208–215, decided by its generator) |
| `hslots : d.ss.length = d.shape.layout.slots.length` | NOT MEASURED (slots = 2 MEASURED; `d.ss.length` not) — decided by `memCounter_slots` |
| `hdomB : ∀ b ∈ binders.drop nDecl, b.2 ≠ .domain` | NOT MEASURED — decided by `memCounter_domB` (`machine_linkedT_mem`'s `hI` / `hSL`, 210, 212, say the same of `bsIn.drop kD` and of `slotBs ++ letBs` and ARE decided by the built generator; that these lists make up `binders.drop nDecl` was NOT read) |
| `hins : insts ≠ []` | HOLDS (1 entry, MEASURED) |
| `hsl : layout.slots ≠ []` | HOLDS (slots = 2, MEASURED) |
| `hfne : instFields ≠ []` | HOLDS (`[out]`, MEASURED) |
| `outTy` | decided already inside `memCounter.machine_ships_hier` (`generateWith` 126–127, BUILT) |
| `hkid : ∀ k hk, KidFactsM mref cref insts[k].1 (kidOuts k) (kidIns k) n` | `memKid_facts` at `n = 0` with `kidOuts = fun _ => memOuts 8`, `kidIns = fun _ => memIns 4 8`, from `memChild? insts[k].1 = some (memModule true 4 8)`: the entry name is `SparkleMem.combo.4.8` (MEASURED); that it IS `memChildName true 4 8` is decided by `memCounter_entry`; `memChild? (memChildName true 4 8) = some (memModule true 4 8)` is the BUILT `mem_isMem` of `NoPortsMemSeqMemTest` 165–168 |
| `hcw : callWidthsOk d nDecl kidOuts` | NOT MEASURED: binder `3 + k` must be `.bits 8` for the field `out`. INFERRED from `machine_linkedT_mem`'s `hcalls` clause `((d.bsIn.drop kD)[k]?.map (·.2)) = some (.bits dw)` (228), which the built generator proves by `rfl` with `kD = nDecl` |
| `hargs : callArgsOk d nDecl kidIns` | NOT MEASURED: the binders of the argument lets `[1,2,3,0]` must have widths `[4,8,1,4]` (`Tools/ShippingPortsMatchRaw.lean` 196–202). INFERRED from the source (`wa : BitVec 4`, `wd : BitVec 8`, `we : Bool`, `addr : BitVec 4`) |
| `hon`, `hoty` | output `out : BitVec 8`; decided (`memCounter_outChars`, `memCounter_outScalar`) |
| `hB : ChildBnd mref cref w` | **NOT AVAILABLE from the old endpoint** (its boundary is `True`): becomes the new endpoint's boundary |
| `entry : MachineDefines` | a binder of the old endpoint |
| `closes : MachineClosesAt` | from the old endpoint's binder `MachineCloses` by `machineClosesAt_of_closes` |

No hypothesis fails by reading. `kidsM_mixed` is NOT used: the route's `Bd` is
`kidsMem`, which `kidsMixed` does not give.

## 9. WRITTEN this round — not built

### 9.1 `Tools/ShippingMemOnly.lean` (imports `Tools.ShippingMemKidFacts`)

No scripted copy. The only repeated proof text is eleven lines of
`core_kidsMemM` (the memory branch of the built `core_kidsMixedM`, 647–662,
with `kidsMem_of` in place of `kidsMixed_of`); `kidsMem` does not follow from
`kidsMixed`, so it is not derived from that theorem but from the same built
lemmas (`core_callStmtM`, `kidsMem_one`, `mem_conns_noRdata`).

    theorem kidsMem_of {C} {body : List Stmt}
        (h : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
          kidsMem C [Stmt.inst mn iname conns] = true) :
        kidsMem C body = true

    theorem core_kidsMemM {c : Name} (d : MachineData) (ok : d.ok = true) (hbody : …)
        {nDecl : Nat} (hC : d.callsOk nDecl = true)
        (hslots : d.ss.length = d.shape.layout.slots.length)
        (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
        (hins : d.shape.insts ≠ []) (hfne : d.shape.instFields ≠ [])
        (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
        (hkidF : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
          Kid mref cref (d.shape.insts[k]).1 y → ∃ cb aw dw, y.1 = (memModule cb aw dw).1)
        {w w1 : Void IO.RealWorld} {M b : Module} {D : Design}
        (hB : ChildBnd mref cref w)
        (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
        (hpost : b = dropZeroWidthModule M ∨ b = mergeChecked (dropZeroWidthModule M))
        (entry : MachineDefines mctx mref cctx cref c d.shape)
        (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
        kidsMem (childMap D.modules) b.body = true

    structure MemOnlyData (d : MachineData) (nDecl aw dw : Nat) : Prop where
      ok, body, calls, slots, domB, ins, sl, fne, outTy,
      mem : ∀ (k : Nat) (hk : k < d.shape.insts.length),
        ∃ cb, memChild? (d.shape.insts[k]).1 = some (memModule cb aw dw)
      cw : callWidthsOk d nDecl (fun _ => memOuts dw) = true
      args : callArgsOk d nDecl (fun _ => memIns aw dw) = true
      outNames, outScalar

    theorem memOnly_kids {d} {aw dw} (hmem : …as the field `mem`…) :
        ∀ k hk, KidFactsM mref cref (d.shape.insts[k]).1 (memOuts dw) (memIns aw dw) 0

    theorem memOnly_runFacts    (h : MemOnlyData d nDecl aw dw) (hB) (hcore) (hpost) (entry) (closes) :
        RunFacts (childMap D.modules) b
    theorem memOnly_outsCheck   (h) (hB) (hcore) (hpost) (entry) (closes) (hg : hierGate b = true) :
        outsCheck (childMap D.modules) 0 (checkedOptimize b) = true
    theorem memOnly_kidsMem     (h) (hB) (hcore) (hpost) (entry) (closes) :
        kidsMem (childMap D.modules) b.body = true
    theorem memOnly_designCheck (h) (hB) (hcore) (hpost) (entry) (closes) :
        designCheck (childMap D.modules) 0 (checkedOptimize b) = true

(`closes : MachineClosesAt`, `hB : ChildBnd mref cref w` in all four.) The
widths `aw`, `dw` are the same for every entry; the read kind may differ
(`mixedMems` fits: combo and sync at 4 / 8 — not instantiated this round).

### 9.2 `Tests/Compiler/NoPortsMemOnlyCounterTest.lean`

* first `run_cmd`: LOGS the reader data and the constants present / absent,
  then asserts `nDecl = 3`, every entry `= memChildName true 4 8`,
  `instFields ≠ []`, a slot (the error text names the no-register axis);
* `Tests.Compiler.NoPortsMemOnly.generateM0 f facts outs mem design`: the head
  `machine_design_noPorts` at `n = 0` on the 24 arguments of the EXISTING
  `f.machine_ships_hier`, with `C := MachineCloses …` (the theorem's own
  closing binder, abstracted), `Bnd := fun _ mref _ cref w _ _ => ChildBnd mref
  cref w`, the wired endpoint and the composed theorem wrapped to ignore the
  new boundary (the composed one given `True.intro` for the old). Throws unless
  the route is `.mem` (`ResetM`, `kidsMem`) and the old boundary is `True`.
  The four run hypotheses are discharged by `dischargeWith … #[]` from the
  boundary only: no binder added. Endpoint `f.machine_design_noPorts0`;
* `auditM0`: standard axioms; no checker constant; the old endpoint asks the
  four; both ask `MachineCloses`, neither `MachineClosesAt`; the same three
  proposition binders, printed the same; ONE antecedent, and it is `ChildBnd`,
  which the old endpoint does not ask (and the old one has an antecedent
  printed `True`); antecedent listing before / after and the complete premise
  list with ALLOWED / NOT ALLOWED LOGGED, not hidden;
* by hand: `memCounter_entry`, `_calls`, `_slots`, `_domB`, `_outTy`,
  `_callWidths`, `_callArgs`, `_outChars`, `_outScalar` (one named theorem per
  decided condition, so a failing one is named by the build), `memCounter_data
  : MemOnlyData memCounter.machineData 3 4 8`, and the four run lemmas.

### 9.3 `Tests/Compiler/NoPortsMemOnlySyncTest.lean`, `…TwoTest.lean`

The same text (derived by `sed` from 9.2's per-declaration part) for
`syncNarrow` (`MemOnlyData … 3 3 5`, every entry `memChildName false 3 5`,
`Exists.intro false`) and `twoMems` (`MemOnlyData … 3 4 8`, two entries of one
name). `memKid_facts` is stated for both `cb` (READ, 468–470, its lemmas over a
variable `cb`); `syncNarrow` is the first instance at `cb = false`.

### 9.4 `Tests/Compiler/NoPortsMemOnlyAtProbe.lean` — PROBE, target-built only

`generateM0 … (atForm := true)` inside `try`: the same head with `C :=
MachineClosesAt`, the wired endpoint the `RA` twin of `machine_sound`'s head
(`machine_traceL_of_loop_causalRA`, `ShippingMachineSeqLinkedR` 25–85) through
`MachineTraceLBX.toLB`, the composed theorem `machine_linkedT_mem` on it with
the ten data arguments of the existing `memCounter.machine_composedT`. Logs
`GENERATED memCounter.machine_design_noPortsR0 …` with its premise list, or
`REFUSED — …`. Nothing claimed.

## 10. Per declaration (round par/b-14)

| declaration | endpoint | premise (of `f.machine_design_sv0`) | predicted state |
|---|---|---|---|
| `memCounter` | `memCounter.machine_design_noPorts0` | `shipsHierCheck (childMap D.modules) b` | WRITTEN — predicted absent, pending build |
| | | `designCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | | `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | | `kidsMem (childMap D.modules) b.body` | predicted absent, pending build |
| | | the boundary `True` | REPLACED by `ChildBnd mref cref w` — ADDED antecedent |
| | | `MachineCloses memCounter` (all worlds) | STILL A PREMISE (binder), unchanged |
| | | `hr`, `MachineDefines memCounter` | stay |
| `syncNarrow` | `syncNarrow.machine_design_noPorts0` | the same seven rows | the same |
| `twoMems` | `twoMems.machine_design_noPorts0` | the same seven rows | the same |
| `mixedMems`, `memWide` | none | all | STILL PREMISES — not written (the pattern applies as is: `MemOnlyData … 3 4 8` with a two-way `mem` field, `… 3 6 16`) |
| `memCounter` | `memCounter.machine_design_noPortsR0` (PROBE) | closing in the form `MachineClosesAt` | attempt only, logged |

The new endpoints are NOT strengthenings of the old ones: four decidable
check premises are traded for the runtime boundary `ChildBnd`.

## 11. Blocked / not done (round par/b-14)

1. Nothing in tasks 1–4 stopped on a missing statement by reading. The
   no-register axis does not apply (slots = 2, MEASURED).
2. NOT removable with what exists: the antecedent `ChildBnd` of the new
   endpoints. The exact missing statement, if the old boundary `True` is to be
   kept: the `core_*M` chain from the ALL-WORLDS closing without a start-world
   invariant, e.g.

       theorem core_callStmtM_closes … (hcore) (hpost) (entry)
           (closes : MachineCloses mctx mref cctx cref c d.shape)
           (hmem : ∀ c ∈ d.shape.insts, (memChild? c.1).isSome) : … (the conclusion of core_callStmtM)

   and the same for `core_runFactsM`, `core_outsCheck_all_gateM`,
   `core_portsMatch_rawM`, `core_kidsPass_deepM`, `core_designCheck_runM`,
   `core_clkM`, `core_hierGateM`: each opens the run by `machine_run_of_core
   hcore entry hB` (`ShippingChildRun` 508), which needs `ChildBnd`. That
   would be another copy of the chain — not written.
3. The closing: `MachineCloses f` (all worlds) stays a binder of the three
   endpoints; whether it can hold of these shapes was not read (§8.2). An
   endpoint under `MachineClosesAt` is only probed (9.4). No closing theorem
   was worked on (worker A's area).
4. `mixedMems`, `memWide`: not written. A generator: not written.

## 12. Build queue (integrator), round par/b-14

`lakefile.lean`:

    lean_lib «Tools.ShippingMemOnly» where
      roots := #[`Tools.ShippingMemOnly]

`Tests/AllTests.lean`:

    import Tests.Compiler.NoPortsMemOnlyCounterTest
    import Tests.Compiler.NoPortsMemOnlySyncTest
    import Tests.Compiler.NoPortsMemOnlyTwoTest

`Tests.Compiler.NoPortsMemOnlyAtProbe`: TARGET-BUILT ONLY.

Order: (1) `Tools.ShippingMemOnly` (imports the built
`Tools.ShippingMemKidFacts`); (2) `Tests.Compiler.NoPortsMemOnlyCounterTest`
(imports 1, `NoPortsGrandHTest`, `ShippingDesignSVMemTest`); (3)
`…NoPortsMemOnlySyncTest`, `…NoPortsMemOnlyTwoTest` (each imports 2 only);
independently (4) `…NoPortsMemOnlyAtProbe` (imports 2). A partial result is
usable: (1) alone gives `core_kidsMemM` and the `memOnly_*` theorems; (2)
alone gives `memCounter`'s endpoint.

Name clashes checked by `grep`: no other module defines a constant under
`Tools.ShippingMemOnly`, `Tests.Compiler.NoPortsMemOnly*`, or
`….machine_design_noPorts0`; no file of worker A's prefixes is touched; no
existing file is changed except this append.

## 13. UNVERIFIED, in risk order (round par/b-14)

1. The data conditions never measured for a `Signal.loop` memory parent, each a
   named kernel `decide`: `memCounter_calls` (`callsOk 3`), `memCounter_callArgs`,
   `memCounter_callWidths`, `memCounter_slots`, `memCounter_domB` (and the
   `syncNarrow` / `twoMems` twins). If one is FALSE the chain does not apply to
   that declaration and the build names it.
2. `generateM0`: `mkAppOptM` of the head at `n = 0` with the arguments of
   `machine_ships_hier` (24 arguments, indices READ off the signature, measured
   for the 25-argument `…hierC` form only); `C` as a lambda (`closes : C mctx
   mref cctx cref` against the binder's `MachineCloses …` by beta); `hBd :
   KSBoundedIn … flatKS … memInv` against `KSn _ 0` / `KT 0` (built for
   `mixKS_boundedIn`, not for `memKS_boundedIn`); the wrapped `soundL`
   (`forallTelescope` of the argument's type: 11 binders) and `composed` (13
   binders, the 12th `True`); `lambdaTelescope` of the old boundary giving 7
   binders and the body `True`; `dischargeWith` on a boundary that is not a
   conjunction.
3. `kidsMem_of`: `refine Eq.trans ?_ (h …)` then `exact (Bool.and_true _).symm`
   (defeq of `kidsMem C [st]` with `f st && true` through `List.all`), `simp
   [kidsMem]` as the second alternative; `| _ => rfl` on the other statement
   kinds.
4. `core_kidsMemM` (the built proof's lines; `rw [hmem] at hcs hCm`);
   `memOnly_kidsMem`'s `congrArg Prod.fst (hy.mem hc)`; `MemOnlyData.mk` with
   fourteen positional arguments (field order as declared).
5. `auditM0`: the old endpoint's boundary printed exactly `True`; the binders
   of old and new printed the same.
6. `syncNarrow`: `mem_isMem` at `false 3 5` by `rfl` (the generators' own
   `rfl` for a sync placeholder is BUILT, `ShippingMachineMemCommand` 46);
   every `mem_*` lemma at `cb = false` is built generically, never instantiated.
7. `NoPortsMemOnlyAtProbe` (inside `try`): `…RA` head on the endpoint's data
   arguments, `machine_composedT`'s value being a lambda of 11 binders over
   `machine_linkedT_mem` on 21 arguments.

## 14. Round par/b-15 — the all-worlds closing decided; the At-form endpoints of all five (WRITTEN, NOT BUILT)

### 14.1 Decision: can `MachineCloses` (all worlds) hold of a memory-only parent? — NO (cannot be discharged; conditional refutation written)

READ: `MachineCloses` (`Tools/ShippingMachineEntry.lean` 2279–2284) is "every
run of `synthesizeMachineCertified`, from every world with every logger,
returns `some`". For `insts ≠ []`, `instFields ≠ []` that run ends in
`closeInstsGM` (`Sparkle/Compiler/Elab.lean` 5206–5221), whose FIRST statement
is `let some synth ← sparkleChildSynth.get | return none` (5209). A memory
entry's child is `pure md` (5211–5213): it reads neither the child cache nor
`synth` — but the read above it is unconditional. So a memory-only shape reads
exactly ONE piece of world-dependent state in its closing, and that one is
enough: from a world where the reference reads `none` the result is `none`.
(`closeInstsM`, 5192, the same.)

Counter-world: any world reached by a successful harness run in which
`sparkleChildSynth` holds `none` — the reference is created so
(`initialize … ← IO.mkRef none`, Elab 1037–1039; set at 8850), and
`sparkleChildSynth.set none` gives one at any time.

Formal status:
- WRITTEN (`Tools/ShippingMemOnlyAtAll.lean`): `not_machineCloses_of_synthNone`
  — `insts ≠ []`, one harness run accepted by `closeLets`, a read of the
  reference returning `none` at its end world ⟹ `¬ MachineCloses`.
- NOT a theorem: `¬ MachineCloses` outright. The existence of such a run is
  not derivable (no existence statement for harness runs; worlds opaque).
- NOT provable either: `MachineCloses` of a shape with calls — it needs
  `sval w = some _` of every world; no runtime law gives it.

Consequence: `f.machine_design_sv0` and `f.machine_design_noPorts0` of the
five memory-only parents carry a premise that can only be assumed and is
false of the running compiler (they are not formally vacuous in the model —
their premise is unrefuted there — but nothing can discharge it). They stay
NOT COUNTED. The form a compile supports is `MachineClosesAt`.

### 14.2 The At-form endpoints (new statements; base `f.machine_design_sv0`)

`f.machine_design_noPortsR0`, by the built `generateM0 … (atForm := true)`,
audited by `Tests.Compiler.NoPortsMemOnlyAt.auditAt`
(`Tests/Compiler/NoPortsMemOnlyAtLib.lean`: differences 1–5 against the base).

| declaration | endpoint | premise | predicted state |
|---|---|---|---|
| each of `memCounter`, `syncNarrow`, `twoMems`, `mixedMems`, `memWide` | `f.machine_design_noPortsR0` | `shipsHierCheck`, `designCheck 0`, `outsCheck 0`, `kidsMem` (of the base) | WRITTEN, NOT BUILT — predicted absent |
| | | base boundary `True` | replaced by `ChildBnd mref cref w` (ADDED, allowed) |
| | | base `MachineCloses f` | replaced by `MachineClosesAt f` — STILL A PREMISE, the one NOT ALLOWED |
| | | run, `MachineDefines f` | stay |

`mixedMems`: entries `[SparkleMem.combo.4.8, SparkleMem.sync.4.8]` — the two
memories differ in the read kind only, so `MemOnlyData … 3 4 8` AS BUILT
applies (`mem` is per-entry `∃ cb`); no per-entry-width generalisation is
needed and none is written. `memWide`: `MemOnlyData … 3 6 16`.

### 14.3 Blocked / not done

- The closing (`MachineClosesAt f` of a memory-only parent): worker A's area;
  not touched. For a memory-only shape it reduces, by reading, to the PURE
  success of `closeInstsG` on the built memory modules after the read of the
  reference (which `SynthAt` of `InvW` makes `some`) — the general statement
  is A's `closeInstsGM_run_all` without `hnomem`.
- Nothing stopped on a missing statement.

### 14.4 Build queue (integrator)

`lakefile.lean`:

    lean_lib «Tools.ShippingMemOnlyAtAll» where
      roots := #[`Tools.ShippingMemOnlyAtAll]

`Tests/AllTests.lean`:

    import Tests.Compiler.NoPortsMemOnlyAtMemCounterTest
    import Tests.Compiler.NoPortsMemOnlyAtSyncNarrowTest
    import Tests.Compiler.NoPortsMemOnlyAtTwoMemsTest
    import Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest
    import Tests.Compiler.NoPortsMemOnlyAtMemWideTest
    import Tests.Compiler.NoPortsMemOnlyAtAllTest

NAME CLASH: `Tests.Compiler.NoPortsMemOnlyAtProbe` (par/b-14) creates
`memCounter.machine_design_noPortsR0`. Keep it target-only and never build it
into the same import closure as `NoPortsMemOnlyAtMemCounterTest`, or drop it
(the test supersedes it).

Order: (1) `Tests.Compiler.NoPortsMemOnlyAtLib` (imports the built
`NoPortsMemOnlyCounterTest`); (2) the five `…At<Decl>Test` (independent of
each other; Sync/Two also import the built Sync/Two tests); independently
(3) `Tools.ShippingMemOnlyAtAll` (imports the built `Tools.ShippingClosesSplit`)
then (4) `Tests.Compiler.NoPortsMemOnlyAtAllTest`. (3)/(4) failing does not
affect (1)/(2).

### 14.5 UNVERIFIED, in risk order

1. `generateM0 (atForm := true)` on the four declarations it never ran on:
   the `…RA` head for a sync-read parent, `machine_composedT` being
   `machine_linkedT_mem` on 21 arguments for `syncNarrow` / `twoMems` /
   `mixedMems` / `memWide` (measured for `memCounter` only).
2. New kernel `decide`s: `mixedMems_callArgs` / `_callWidths` / `_calls` /
   `_entry` (two-way `∨`), and the `memWide_*` set at 6 / 16.
3. `auditAt`: `isDefEq (t.getArg! 4) (toExpr f)` on the declaration name;
   the classifier giving exactly one NOT ALLOWED line; the base's boundary
   printing `True`; `innerParts` (log only, behind `<|>`).
4. `Tools.ShippingMemOnlyAtAll`: `RunsTo.bind_intro hget ?_` against the
   unfolded `closeInstsGM` / `closeInstsM` (the `let some … | return none`
   desugaring: `rfl`, else `dsimp only; rfl`); `split` on `closeCalls`' `if`.
5. `logData`: `mems.contains` on `Name`; message interpolation of lists.

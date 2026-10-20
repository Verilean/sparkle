# A / G1: parents of COMBINATIONAL children (classes G and S) — round par/a-5

Branch `par/a-5`, base poc `6a20c9a7`. NOTHING here was built: every file
was written by reading sources. Every "proved" below means "a proof was
written"; all of it is a PREDICTION until the integrator's build returns.

## 0. Result in one screen

Classes of `#machine_no_ports`' refusals treated here:

* (G) the callee is compiled by a combinational GATE (`pick`, `pickD`,
  `rcH`);
* (S) the callee is a MACHINE without calls and without slots
  (`pickByteH`, `httpGetByte`).

Read from the compiler (`Sparkle/Compiler/Elab.lean` 4045–4070, 5134, 5180,
5237): `shape.instFields ≠ []` exactly when the reader set `instStruct`
(a structure result, a `Bool` result, or a memory call). A call whose
result is ONE `Signal (BitVec n)` leaves `instFields = []` and the calls are
tied by the ONE-OUTPUT closing `closeInsts`, which itself checks that the
children are combinational (`kidsCombB`). So **every census parent of
classes G and S (`caller…`, `callerMix`, `callerRep`, `callerABA`, `midH`,
`callerL`, `callerLN`, `hftByte`) is a one-output closing** (predicted by
reading; the sweep's `oneOut` column measures it). What separates them from
an empty-gap endpoint is therefore, first, the ONE-OUTPUT CLOSING (section
4), and only second the child's kind (sections 2, 3).

| piece | state |
|---|---|
| child's `kidCheck` (the children's check), gate child | **proved** `gate_real_kidK` |
| child's `kidCheck`, leaf machine with the one output `out` (slots or not) | **proved** `leaf_real_kidK_out` |
| child's `kidCheck`, slotless leaf with several outputs | **missing**, exact lemma in 2.3; the general `TypedIn`-statement is false |
| child's output ports with types, slotless leaf | **proved** `leaf_real_outTys_any` |
| child has no clock (`hkidClk` vacuous), gate child | **proved** `gate_real_notSeq` |
| child's ports in the emitter's map, gate child (`PortsIn`, argument widths, output type) | **missing**, statements in 3.2 |
| parent: `hierGate b`, either closing | **proved** `core_hierGate_any` |
| parent: `kidsPass … (checkedOptimize b).body`, either closing | **proved** `core_kidsPass_any` |
| parent: conjuncts 2, 3 of `textCheckI` of the shipped module, either closing | **proved** `core_text_shipped_any` |
| parent: `portsMatchB` for slotless leaf children under the GROUP closing | **proved** `core_portsMatch_raw_leaf_any` |
| parent, one-output closing: width fact per child output | **proved** `hkidW_one` |
| parent, one-output closing: distinct instance names, `noSelfRead`, `outsExtracted`, `instOutWidthsOk`, `portsMatchB` | **missing**, statements in 4.2 |
| a head without check premises for the combinational route | **missing**, 1.3 |

## 1. Inventory

### 1.1 What is generated today for `caller` (child `pick`)

`Tests/Compiler/ShippingMachineInstTest.lean`: `#machine_endpoint`,
`#machine_linked`, `#gate_child pick`, `#machine_composed`.
`Tests/Compiler/ShippingCallsCloseTest.lean`: `#machine_closes_at caller`.
`Tests/Compiler/ShippingMachineShipsHierHTest.lean`: `#machine_ships_hierH`.
`Tests/Compiler/ShippingDesignSVTest.lean`: `#machine_design_svH caller`.
`Tests/Compiler/ShippingChildBoundaryTest.lean` 347–375:
`#machine_design_svHR` on nine parents (`caller`, `midH`, `callerNested`,
`callerLN`, `hftByte`, `callerMix`, `callerTwice`, `callerD`, `callerL`).
(`callerRep`, `callerABA`: `#machine_design_svHR` in `ShippingCallsCloseTest`.)

There is NO depth endpoint `machine_ships_hierNR1` / `machine_design_svNR`
for these parents. Their deepest endpoint is

    f.machine_design_svHR  =  ships_design_svH_all  ∘  f.machine_ships_hierHR
    (Tools/ShippingMachineComposeRCommand.lean; Tools/ShippingShipsDesignSVAll.lean 135;
     Tools/ShippingMachineShipsHierH.lean: machine_ships_hierHC)

the COMBINATIONAL head: the shipped module's combinational linked run
(`runModuleH`), turned into the depth-0 run by `runModuleTG_flat_of_H`
under `kidsComb`, then `design_sv_runN` at `n = 0`. Its conclusion is
`DesignSV (childMap D.modules) 0 (checkedOptimize b) …` (existence and every
closed run).

**Its premises** (read off `ships_design_svH_all`'s statement and the
assertions of `ShippingChildBoundaryTest` 380–407):

* the run of the entry, `MachineDefines` of the parent, and the boundary
  `Bnd`: `ChildBnd` plus each child's reflection (`EntryDefines` for a gate
  child, `MachineDefines` for a machine child) — no `GateRun` /
  `MachineRun` / `BoundH` / `ChildFn`;
* FOUR check premises, inside `∃ raw D, … ∧ (… → …)`:

      shipsHierHCheck D.modules b = true
      kidsComb D.modules (checkedOptimize b).body = true
      designCheck (childMap D.modules) 0 (checkedOptimize b) = true
      outsCheck (childMap D.modules) 0 (checkedOptimize b) = true

  with (`Tools/ShippingHierPremises.lean` 18, `ShippingHierPremisesBase.lean` 65)

      shipsHierHCheck ms b = hierCheck (childMap ms) b && kidsLocal ms (checkedOptimize b).body
                              && hierTyped (childMap ms) b
      hierCheck C b = hierBinds b && linkedWF C o.body && Nodup (instNames b.body)
                      && Nodup (instNames o.body) && noSelfRead C o.body
                      && outsExtracted C b && "rst" ∈ b.inputs          (o = checkedOptimize b)

  The test evaluates the four on the real modules and throws if one is
  false: they hold on the nine declarations.
* one data premise decided when `f.machine_ships_hierHR` is generated
  (`houtTy`, "the output-width premise").

So the combinational head asks NO `instOutWidthsOk` (conjunct 8 of the
sequential bundle `shipsHierCheck`) and no `kidsMaskedN`; the only width
statement about a connection is `portsMatchB` inside `designCheck`
(`textCheckI`'s conjunct 7), a check premise. That is the audit's "no width
claim at all today" for one-output parents.

### 1.2 Which parent-side theorems apply as they are

All are stated for the core run `(M, D)` of a machine with calls, with
`b = dropZeroWidthModule M` or its checked merge. `hfne` is
`d.shape.instFields ≠ []`.

**Without `hfne` — apply to one-output parents unchanged:**

| theorem | file | gives |
|---|---|---|
| `core_kids_facts` | `ShippingChecksCore` | `b.body = M.body`, instances resolve in `D`, every module of `D` is a real child's, `outsAssigned b` |
| `core_outsCheck_all`, `core_outsCheck_all_gate` | `ShippingChecksCore`, `ShippingChecksCoreGate` | `outsCheck C n o` from `hkidA` / `hkidR` per child (`gate_kidA` / `gate_kidR` for a gate child; `leaf_real_kidA` / `kidR` for a leaf WITH a register — the slotless forms were not checked this round) |
| `core_kidsMaskedN` | `ShippingChecksMasked` | not asked by the combinational head |
| `core_closed_typedIn`, `core_text_raw` | `ShippingClosedTyped` | `TypedIn b`; conjuncts 2, 3 of `textCheckI` of `b` |
| `core_linkedWF` | `ShippingLinkedFresh` | `linkedWF C b.body` |
| `core_clk` | `ShippingCoreClk` | `weS b "clk" = 1 ∧ weS b "rst" = 1` (parent's `hsl`) |
| `closeInsts_kidsComb` | `ShippingChildServe` | `kidsCombB d.modules m.body` of the raw closed module (the closing RUNS the check) |

**With `hfne`:**

| theorem | file | is `hfne` essential? |
|---|---|---|
| `core_hierGate` | `ShippingChecksWidths` 365 | **inherited.** Used once, to pick the `closeInstsG` disjunct and read the first instance statement off `closeInstsG_calls`; `closeInsts_calls` gives the same. → `core_hierGate_any` |
| `core_kidsPass_leaf` | `ShippingKidsPassLeaf` | **inherited** (only through the gate) → `core_kidsPass_any` |
| `core_text_shipped` | `ShippingTextShipped` 80 | **inherited** (only through the gate) → `core_text_shipped_any` |
| `core_raw_facts` | `ShippingChecksRaw` 131 | **essential as written**: `(instNames b.body).Nodup` and `noSelfRead` are read off `MachineWired`'s clause `instFields ≠ [] → Nodup … ∧ noSelfFeed …` (`ShippingMachineEntry.lean` 723). The one-output clauses (662–667) state the call statements (`CallStmt`) only. `"rst" ∈ inputs` needs `hsl` only |
| `core_outsExtracted` | `ShippingChecksOuts` 86 | essential as written (`closeInstsG_insts`); the one-output analogue is `closeInsts_insts` + `CallStmt` (the driven wire is `portNames[nIn + k]`) |
| `core_callPorts`, `core_instOutWidthsOk` | `ShippingChecksWidths` 104, 271 | essential as written (`CallStmtG`'s output connections); one-output analogue over `CallStmt`'s last connection |
| `core_callConns`, `core_portsMatch_raw` | `ShippingPortsMatchRaw` 247, 441 | essential as written (`callConnsG`); one-output analogue over `CallStmt`'s `zip inPorts argWs ++ [(outP.name, .ref outW)]` |
| `core_runFacts` | `ShippingChecksRunFacts` | a bundle: inherits from the four above |
| `core_designCheck_run` | `ShippingTextShipped` 131 | through `core_runFacts` |
| `core_portsMatch_shipped`, `…_leaf`, `core_portsMatch_raw_leaf` | | through the gate (inherited) and `core_portsMatch_raw` (essential) |
| `core_shipsHier_rest`, `rest3`, `rest3F`, `rest4` | | bundles of the above (superseded by `RunFacts`) |
| `machineClosesAt_of_kidsD`, `machineClosesAt_of_seqKids` | `ShippingCallsKidsD`, `ShippingCallsSeqKids` | by design about `closeInstsG`; the one-output closing has `machineClosesAt_of_gateKids` (`ShippingCallsGate` 240) |

### 1.3 The head

Two heads could carry these parents; neither exists without checks.

(a) **The combinational head** (`ships_design_svH_all`). Needed: a copy of
`machine_ships_hierHC` without `shipsHierHCheck`, as
`machine_ships_hierC_free` (`Tools/ShippingShipsHierFree.lean`) is for the
sequential one — the case split on `checkedOptimize`'s branches
(`checkedOptimize_not_binding`, `checkedOptimize_binding`,
`deinline_guards`) in place of `hierBinds b`; then `kidsLocal` / `kidsComb`
of the shipped body from `closeInsts_kidsComb` and
`checkedOptimize_inst_iff_gate` (the instance statements of the shipped
module are `b`'s); `hierTyped (childMap ms) b` (`kidsTyped`: the body
width-typed off the output ports, the children `childTyped`, the
connections `connsTyped`) from `TypedIn b` and the children's facts — NOT
read this round, no statement proposed.

(b) **The sequential depth head at depth 0** (`machine_ships_hier` /
`machine_design_noPorts` with `n = 0`): `composedNW0_of_H`
(`Tools/ShippingMachineDepthH.lean` 191) turns `ComposedH` into the depth-0
`ComposedNW` under `BoundH` and `kidsComb`. Its bundle `shipsHierCheck` is
what `RunFacts` replaced; it asks conjunct 8 (`instOutWidthsOk`) and
`"rst" ∈ inputs` (true with a register). Whether the generated
`f.machine_ships_hierNR0` exists for a one-output parent was NOT checked;
the sweep's `shipsN` column measures whether `shipsHierCheck` holds on the
real modules. If it does, (b) reuses the whole `#machine_no_ports` chain
and what is missing is exactly section 4.2.

## 2. Class S: slotless leaf MACHINE child

Data of the census parents (predicted): `callerL`, `callerLN`
(`pickByteH : … → Signal (BitVec 8)`), `hftByte` (`httpGetByte`) — one-output
closings, parent with a register. A slotless leaf under the GROUP closing
needs a structure or `Bool` result; no census declaration has one. The
sweep adds `twin` / `twinParent` (two outputs of the SAME value).

### 2.1 (i) `LeafKid` without `slots ≠ []` — proved

`LeafKid.slots` has ONE use in `core_portsMatch_raw_leaf`:
`leaf_real_outTys`. Its proof (`leaf_run_outputs`,
`Tools/ShippingChildIfaceTy.lean` 66–174) uses `hsl` only to derive `hnA`
("the raw module has a register"), which the rest never reads (copied from
`leaf_run_outsAssigned`). `Tools/ShippingPortsMatchRawLeafAny.lean`:

    theorem leaf_run_outputs_any … (hno : d.shape.insts = [])
        (hSS : d.ss.length = d.shape.layout.slots.length) (outTy : …) (hw : InvW mref cref w)
        (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
        (entry : MachineDefines …) (closesM : MachineCloses …) :
        b.outputs = d.shape.layout.outs.map (fun o => ({ name := o.name, ty := o.ty } : Port))

    theorem leaf_real_outTys_any … {y : Res} (h : RealChild mref cref c y) :
        Tools.ShippingChildIfaceTy.ChildOutTys d.shape.layout.outs y.1

    structure LeafKidAny …          -- LeafKid without `slots`
    theorem leafKid_toAny : LeafKid … c dk → LeafKidAny … c dk

    theorem core_portsMatch_raw_leaf_any …      -- statement of core_portsMatch_raw_leaf,
        (hkid : ∀ k hk, LeafKidAny mctx mref cctx cref (d.shape.insts[k]).1 (kid k)) … :
        portsMatchB (childMap D.modules) b = true

`leaf_real_ports` and `leaf_real_portsIn` never asked for slots.

### 2.2 (iii) the clock

`LeafPorts.seq_iff`: a leaf's module has a `clk` / `rst` input exactly when
it has slots; so for a slotless leaf `isSeqChild = false` and `hkidClk` is
vacuous (`LeafPorts.clk` is already conditional). `core_portsMatch_raw`
takes `hclkB : weS b "clk" = 1 ∧ weS b "rst" = 1` UNCONDITIONALLY but uses it
only at a sequential child's `clk` / `rst` connections
(`Tools/ShippingPortsMatchRaw.lean` 506–511). So the parent's `slots ≠ []`
(asked by `core_clk`) is not needed when every child is combinational — but
dropping it means weakening `hclkB` inside `core_portsMatch_raw` to

    hclkB : (∃ k hk y, RealChild mref cref (d.shape.insts[k]).1 y ∧ isSeqChild y.1 = true) →
      weS b "clk" = 1 ∧ weS b "rst" = 1

an edit of an existing file (two lines of its proof). Not done:
`core_portsMatch_raw_leaf_any` keeps the parent's `hsl`.

### 2.3 (ii) the child's `kidCheck`: what the merge does to an assignment-only body

`mergeChecked m` on an assignment-only body returns `mergeDuplicates m`
unguarded; `mergeDuplicates m` (`Sparkle/IR/RegDedup.lean` 305–311) keeps
`mergeDuplicatesRaw m`'s body only if `validateMerge (declWidth m) m.body
r.body`, else returns `m`. `validateStep` accepts, statement by statement
(same left-hand side `l`, in order), either

* `l := renameE (aliasOf S) e` — the old right-hand side with references
  renamed through the aliases so far, or
* `l := y` (a plain alias) when `y ≠ l`, `y` is defined earlier, `y` is not
  itself an alias, the canonical right-hand sides agree
  (`R.lookup y = some (renameE (aliasOf V) e)`), and
  **`wOf l = wOf y`** (equal WIRE-TABLE widths).

`S` only ever maps a name to a name of the same wire-table width. So for a
typed body the renamed expressions stay typed
(`Tools.ShippingTypedPostSoundness.typed_rename`), and an alias `l := y`
between two wires is typed. The one case typing does not survive: `l` an
OUTPUT PORT. Ports are not wires; their wire-table width is 0. `0 = wOf y`
excludes every wire an expression reads (positive width), but not ANOTHER
OUTPUT PORT (`0 = 0`). The merged module would then contain
`assign o₂ = o₁`, which READS an output port: `TypedExpr (weOf m) (.ref o₁) n`
is false (`weOf m o₁ = 0`), and conjunct 3 of `textCheckI` is false
(`declWidth m o₁ = 0`, `weS m o₁ = n`). So

    TypedIn m → m.body.all isAssign → TypedIn (mergeDuplicates m)        -- FALSE in general
    TypedIn m → m.body.all isAssign → printOk (mergeDuplicates m)        -- FALSE in general

as statements about `validateMerge`. (Not a miscompile: the emitted text
`assign o2 = o1;` over two output ports of the same width means the same;
it is the proof-side check that rejects it.)

**Proved** (`Tools/ShippingCombKidText.lean`), the one-output case — where
there is no second output:

    theorem typedIn_mergeDuplicates_out {m} (h : TypedIn m) {ty}
        (hout : m.outputs = [({ name := "out", ty := ty } : Port)])
        (hall : m.body.all Sparkle.IR.RegDedup.isAssign = true) :
        TypedIn (Sparkle.IR.RegDedup.mergeDuplicates m)

    theorem mergeChecked_text_out {m} (h : TypedIn m) {ty} (hout : m.outputs = [out]) :
        seqCheck (wofOf (mergeChecked m)) (weS (mergeChecked m)) (mergeChecked m).body = true ∧
        (seqNames (mergeChecked m).body).all (fun x => declWidth (mergeChecked m) x ==
          weS (mergeChecked m) x) = true

    theorem leaf_real_kidK_out … (hone : d.shape.layout.outs.map (·.name) = ["out"]) …
        {y : Res} (h : RealChild mref cref c y) :
        (∀ C n, kidCheck C n y.1 = true) ∧ ∀ g ∈ y.2.modules, ∀ C n, kidCheck C n g = true

`leaf_real_kidK_out` is `leaf_real_kidK` without `hmergePrint`, for a leaf
with OR without a register (`mergeChecked_print_cases` splits the three
branches). It reuses the gate route's `mergeDuplicates_typed` /
`mergeDuplicates_output` (which hard-code the name `out`): a single-`Signal`
result is named `out` by `machOuts?` (`Elab.lean` 3864–3865, 5066), so
`hone` holds for `pickByteH` and `httpGetByte` (predicted; `decide`).

**Missing — a slotless leaf with several outputs.** For the modules
`closeMachine` builds, an output is never aliased to another: `outAssigns`
drives output `o` with `fieldRhs w o.lo o.width = .slice (.ref w)
(o.lo + o.width - 1) o.lo`, `machOutFields` gives distinct `lo` to outputs of
positive width, and `renameE` keeps slice bounds. The exact lemma:

    theorem validateMerge_typedO {we : WEnv} {O : List String} {old new : List Stmt}
        (hz : ∀ o ∈ O, we o = 0)
        (hs : ∀ st ∈ old, ∃ l e n, st = .assign l e ∧ TypedExpr we e n ∧ (we l = n ∨ l ∈ O))
        -- distinct outputs have right-hand sides no two renamings identify
        (hsep : ∀ o₁ e₁ o₂ e₂, o₁ ∈ O → o₂ ∈ O → o₁ ≠ o₂ →
          Stmt.assign o₁ e₁ ∈ old → Stmt.assign o₂ e₂ ∈ old →
          ∀ σ τ, renameE σ e₁ ≠ renameE τ e₂)
        (h : validateMerge we old new = true) :
        ∀ st ∈ new, ∃ l e n, st = .assign l e ∧ TypedExpr we e n ∧ (we l = n ∨ l ∈ O)

Proof plan: `validateStep_typed` with `"out"` replaced by `l ∈ O`; in the
alias case with `l ∈ O` the name `y` is positive (then `0 = we y`
contradicts) or `y ∈ O`, `y ≠ l`, and `R.lookup y = some (renameE (aliasOf V) e)`
— with the invariant "every entry `(y, c)` of `R` is `renameE τ e_y` for the
statement `y := e_y` of the prefix" (keys of `R` are distinct: `l ∈ defined`
is refused) this contradicts `hsep`. `hsep` for a leaf machine: both
right-hand sides are slices with different `lo`
(`closeMachine_typed` exposes the output assignments; that clause was not
read to the bottom). Estimated 150 lines; not written.

**Would a print guard on the assignment-only branch change emitted text?**
It could only where `printOk (mergeDuplicates m) = false` on a module the
merge changed. For gate children `post_forwardCheck` shows the merged module
passes the forward check, and for one-`out` leaves `typedIn_mergeDuplicates_out`
shows it stays typed — on those a guard never fires. The legacy route's
assignment-only modules have no typing theorem: a guard may fire there and
return the unmerged module (different text, same function by
`mergeDuplicates_sound`). The sweep logs `printOk(merged)` per callee; a
corpus-wide count is `PrintArtifactCensusTest`'s business, not measured
here.

## 3. Class G: gate child

The child's module is the GATE route's (`synthesizeMixedCertified`, the
zero-width cleanup, the checked merge — `synthesizeCombinational_checked`).
`RealChild` + the declaration's reflection (`EntryDefines`, the gate data
`old`, `peel`, `he`, `hb`, `hv` that `#gate_child` already produces) give
`ChildFull c bs y.1 y.2` (`childFull_of_real`): assignments only, reads
closed, the one output `out` driven, distinct allocated input names, the
input port TYPES (`tys`), the name, an empty design.

### 3.1 `kidCheck` — proved

The gate route has the text fact in the print vocabulary:
`transition_closed` gives `PrintBaseAt ow M` and `TypedPostReady M` for the
raw module of ANY well-formed term, and
`Tools.ShippingMixedForwardSoundness.post_forwardCheck` gives
`forwardCheck m' = true` for `m' = dropZeroWidthModule M` or
`mergeDuplicates` of it. `forwardCheck` is `assignsCheck (printWidths
(wires ++ inputs ++ outputs)) (forwardWidths m) m.body` plus the width
tables agreeing on every read name — the same content as conjuncts 2, 3 of
`textCheckI` on an assignment-only body. `Tools/ShippingCombKidText.lean`:

    theorem moduleWof_eq (m) : moduleWof m = printWidths (m.wires ++ m.inputs ++ m.outputs)
    theorem seqCheck_of_assignsCheck : body.all isAssign → assignsCheck wof we body → seqCheck wof we body
    theorem forwardCheck_text (h : forwardCheck m = true) :
        m.body.all isAssign = true ∧ seqCheck (wofOf m) (weS m) m.body = true ∧
        (seqNames m.body).all (fun x => declWidth m x == weS m x) = true
    theorem gate_child_forwardCheck (hr : RunsTo (synthesizeCombinational declName) … (b, design) w')
        (entry : EntryDefines …) (old …) (peel …) (he …) (hb …) (hv …) : forwardCheck b = true
    theorem gate_real_kidK (entry : EntryDefines mctx mref cctx cref c value) (old …) (peel …)
        (he …) (hb …) (hv …) (h : RealChild mref cref c y) :
        (∀ C n, kidCheck C n y.1 = true) ∧ ∀ g ∈ y.2.modules, ∀ C n, kidCheck C n g = true
    theorem gate_real_notSeq … (h : RealChild mref cref c y) : isSeqChild y.1 = false

`gate_real_kidK` is `hkidK` of `core_kidsPass_any` for a gate child, with no
hypothesis about the merge. (`synthesized_forwardCheck` /
`compiled_forwardCheck` of `Tools/ShippingSVBridge.lean` 582, 596 are the
same fact for the uniform-width source fragment through the optimizer —
about `checkedOptimize`, not what a parent's design holds; the child in a
design is the full entry's module, unoptimized, so `post_forwardCheck` is
the one that applies.)

### 3.2 `gate_real_ports` — missing, statements

The analogue of `LeafPorts` + `PortsIn` + `ChildOutTys`:

    structure GatePorts (bs : List (Name × MixedGateBinder)) (res : MixedGateBinder)
        (b : Sparkle.IR.AST.Module) : Prop where
      portsIn : Tools.ShippingLeafTyped.PortsIn b
      notSeq : isSeqChild b = false
      -- the j-th input port's emitted width is the j-th hardware binder's
      inWidths : ∀ (j : Nat) (q : Port), b.inputs[j]? = some q →
        ∃ wd, ((bs.filter fun x => x.2 != .domain).map fun x => (kindTy x.2).bitWidth)[j]? = some wd ∧
          Tools.ShippingDesignSV.weS b q.name = wd
      -- the output port
      out : b.outputs = [({ name := "out", ty := kindTy res } : Port)]

    theorem gate_real_ports (entry …) (old …) (peel …) (he …) (hb …) (hv …)
        (hres : the result kind of `e` is `res`) (h : RealChild mref cref c y) : GatePorts bs res y.1

What exists towards it, and what does not:

* `notSeq`: **proved** (`gate_real_notSeq`).
* `inWidths`: `ChildFull.tys` gives `b.inputs.map (·.ty)`; `PrintBaseAt`
  gives `inputWires : ∀ p ∈ m.inputs, p ∈ m.wires` and
  `declaration_layout` distinct wire names, so `weOf b p.name` is the port
  type's width (`weOf_port`) and `pos_wire` turns it into `weS`. Needs the
  positive binders (`mixedShape_positive`). A recombination of existing
  lemmas along `gate_child_fullFacts`' prelude; not written.
* `portsIn`: `wn` from `declaration_layout`'s `DataName` (as
  `post_forwardCheck`'s `clean`); `ow` / `oi` from "`out` is not an
  allocated name" (the wires and inputs are allocated: `PrintBaseAt.wireNames`,
  `ChildComb.inputAlloc`) — the lemma `¬ Allocated "out"` was not located;
  `ostable`, `ond`, `oty` from `PrintBaseAt.output` / `outputs`.
* `out` with its TYPE: `ChildComb.output` gives `∃ ty, b.outputs = [out]`;
  `PrintBaseAt.outputWidth` gives `ty.bitWidth = ow`. That `ow` is the
  declared result kind's width is NOT a field of `ChildFull` /
  `transition_closed`'s conclusion; `compiled_outputWidth`
  (`ShippingSVBridge` 523) states it for the uniform fragment. Needed for
  the one-output width fact (`hkidT` of `hkidW_one`).

## 4. The one-output closing

### 4.1 Proved

    -- Tools/ShippingHierGateAny.lean  (statements = the originals without hfne)
    theorem core_hierGate_any …  : Sparkle.IR.RefineCheck.hierGate b = true
    theorem core_kidsPass_any … (hkidK : per real child, ∀ C n, kidCheck …) … (n : Nat) :
        kidsPass (childMap D.modules) (kidCheck (childMap D.modules) n) (checkedOptimize b).body = true
    theorem core_text_shipped_any … : seqCheck (wofOf o) (weS o) o.body = true ∧
        (seqNames o.body).all (fun x => declWidth o x == weS o x) = true      -- o = checkedOptimize b

    -- Tools/ShippingPortsMatchRawLeafAny.lean
    theorem hkidW_one (hf : d.shape.instFields = [])
        (hcw : Tools.ShippingCallWidthsStrict.callWidthsStrict d nDecl kidOuts = true)
        (hkidT : ∀ k hk y, RealChild mref cref (d.shape.insts[k]).1 y → ChildOutTys (kidOuts k) y.1) :
        ∀ k hk y, RealChild mref cref (d.shape.insts[k]).1 y → ∀ p ∈ y.1.outputs,
          (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some p.ty.bitWidth

`hkidW_one` is the width half of the one-output connection: with no field
list `callWidthsStrict` compares EVERY output of the child (the vacuity of
`callWidthsOk` at `instFields = []` is gone). With `core_kidsPass_any` +
`gate_real_kidK` / `leaf_real_kidK_out`, the conjunct
`kidsPass C leafCheck o.body` of `designCheck C 0 o` is derived for every
census parent of classes G and S (given the generator instantiates them).

### 4.2 Missing — the one-output forms, in dependency order

All take `core_kids_facts`' hypotheses plus `hf : d.shape.instFields = []`;
all read the run's `closeInsts … = some (M, D)` (first disjunct of
`CloseCalls`) through `closeInsts_insts` / `closeInsts_calls` / `CallStmt`:

    -- (a) every instance statement of b is a call's, with its connections
    theorem core_callStmt₁ … :
        ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
          ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res) (outW : String)
            (argWs : List String) (outP : Port),
            RealChild mref cref (d.shape.insts[k]).1 y ∧ moduleByName D.modules mn = some y.1 ∧
            y.1.outputs = [outP] ∧ isSeqChild y.1 = false ∧
            (t.inputs.map (·.name))[machNIn d.shape + k]? = some outW ∧ outW ∉ argWs ∧
            iname = s!"inst{k}_{y.1.name}" ∧
            conns = ((inPortsOf y.1).zip argWs).map (fun (p, w) => (p.name, .ref w)) ++
              [(outP.name, .ref outW)]

  (`CallStmt` hides `iname` behind an existential; `instStmt` builds
  `s!"inst{k}_{mc.name}"` — `instStmt_some` has to be re-proved keeping it,
  in a new file.)

    -- (b) RunFacts.ndB: needs  s!"inst{k}_{a}" = s!"inst{k'}_{b}" → k = k'
    theorem core_instNames₁ … : (Tools.ShippingHierState.instNames b.body).Nodup

  The string lemma (decimal digits followed by `_`) is NOT in the tree
  (`instName_ne_of_head` of `ShippingCallsGate` 53 is about a different
  clash). `closeInsts` does not check distinct instance names; two calls
  `k ≠ k'` of one child give `inst{k}_c`, `inst{k'}_c`. This is the one
  item that is not a recombination.

    -- (c) RunFacts.self
    theorem core_noSelfRead₁ … : noSelfRead (childMap D.modules) b.body = true
        -- from (a): the input connections read argWs, the driven wire is outW ∉ argWs,
        -- outP.name ∉ the input port names

    -- (d) RunFacts.outs
    theorem core_outsExtracted₁ … : outsExtracted (childMap D.modules) b = true
        -- core_outsExtracted's proof with `hident` from (a)

    -- (e) RunFacts.wid
    theorem core_instOutWidthsOk₁ … (hkidW₁ : the conclusion of hkidW_one) :
        instOutWidthsOk (childMap D.modules) (declWidth b) b.body = true
        -- core_callPorts' `key` (the call port's declared width is its binder kind's:
        -- closedPorts_of_run) + (a) + hkidW₁; "exactly one output" is (a)'s  y.1.outputs = [outP]

    -- (f) the connections
    theorem core_portsMatch_raw₁ … (hkidT) (hargs) (hkidIn) (hkidW₁) :
        portsMatchB (childMap D.modules) b = true
        -- core_portsMatch_raw's proof over (a)'s connection list; no clock connection,
        -- so no hclkB and no parent hsl

With (b)–(e) and `core_hierGate_any`, `core_linkedWF`, and `"rst"` from
`hsl`, `RunFacts (childMap D.modules) b` holds for a one-output parent with
a register, and `core_designCheck_rest2` (which takes `RunFacts` and
`TypedIn b`, no `hfne`) gives `designCheck` from (f) and
`core_kidsPass_any`.

## 5. The sweep (`Tests/Compiler/CombKidsSweepTest.lean`)

Logs only. Over `HierBindsCensusTest.candidates` plus `twinParent`:

    COMBKIDS <parent>: class=… oneOut=… slots=… callees=[…] designCheck0=… designCheck1=…
      kidsPass0=… kidsPass1=… portsMatchB(b)=… portsMatchB(o)=… shipsH=… shipsN=… kidsComb=…
      outsCheck0=… gate=… ndB=… self=… wid=… rst=…
    COMBKIDS   child <module>: printOk=… forwardCheck=… leafCheck=… kidCheck1=… isAssign=… outs=…
    COMBKIDS   callee <c>: mergeChanged=… printOk(merged)=… printOk(unmerged)=… sameAsDesign=…
    COMBKIDS TOTALS: …

Classes are read off the reader's shape (as `readMachine` does). What each
column is the target of: `gate` `core_hierGate_any`; `kidsPass0/1`
`core_kidsPass_any`; `child … forwardCheck` `gate_child_forwardCheck`;
`child … printOk`, `callee … mergeChanged` section 2.3; `ndB` `self` `wid`
`portsMatchB(b)` section 4.2 (b) (c) (e) (f); `shipsN` section 1.3 (b).

Predictions (not measured): all G/S census parents `oneOut=T`, `slots=T`;
`designCheck0`, `shipsH`, `kidsComb`, `outsCheck0` `T` on the nine `hrDecls`.
`twin` / `twinParent`: whether the machine route takes them is unknown; the
row says which route.

## 6. UNVERIFIED, in risk order

1. `Tools/ShippingCombKidText.lean`
   * `forwardCheck_text`: the bridge between `forwardCheck`'s inline
     `match` and the pointwise facts (`hrefs`, by definitional unfolding of
     a matcher at a constructor); `moduleWof_eq` (`rfl` across two
     definitions with different auxiliary matchers, with a `funext`/`cases`
     fallback).
   * `typedIn_mergeDuplicates_out`: the `subst` / `rw` steps on the
     existential witnesses; `hz` through `pos_wire`.
   * `gate_child_forwardCheck`: copied prelude of `gate_child_comb`;
     `post_forwardCheck`'s implicit `outWidth`.
   * namespaces: many `open`s; an ambiguous name would show here first.
2. `Tests/Compiler/CombKidsSweepTest.lean`: `twin` (a combinational
   `@[hardware_module]` with a structure result) may not elaborate as
   Sparkle DSL the way I wrote it, or may fail to compile to hardware (the
   latter is caught and logged; an elaboration error of the definition is
   not). `routeOf` copies `readMachine`'s first lines.
3. `Tools/ShippingPortsMatchRawLeafAny.lean`: script copies; the deleted
   block of `leaf_run_outputs` leaves `hregs`, `rlen`, `hSS` unused (linter
   warnings); `hkidW_one`'s `simp at hf'` on `[][k]? = some f`.
4. `Tools/ShippingHierGateAny.lean`: `core_hierGate_any`'s first disjunct
   (the anonymous-constructor arity of `CallStmt`: four witnesses, ten
   conjuncts); the rest is the original.

No theorem here was applied by a generator: that `hkidK` for a gate child
is instantiable from what `#gate_child` leaves in the environment
(`EntryDefines` in the run's contexts, `old`, `peel`, `he`, `hb`, `hv`) is
read off `childFull_of_real`'s use in `machineClosesAt_of_gateKids`, not
tried.

## 7. Build queue (suggested order)

1. `Tools.ShippingHierGateAny`
2. `Tools.ShippingCombKidText`
3. `Tools.ShippingPortsMatchRawLeafAny`
4. `Tests.Compiler.CombKidsSweepTest`

`lakefile.lean` (integrator):

    lean_lib «Tools.ShippingHierGateAny» where
      roots := #[`Tools.ShippingHierGateAny]

    lean_lib «Tools.ShippingCombKidText» where
      roots := #[`Tools.ShippingCombKidText]

    lean_lib «Tools.ShippingPortsMatchRawLeafAny» where
      roots := #[`Tools.ShippingPortsMatchRawLeafAny]

`Tests/AllTests.lean` (integrator):

    import Tests.Compiler.CombKidsSweepTest

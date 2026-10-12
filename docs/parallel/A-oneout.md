# A / G1: the ONE-OUTPUT closing at ONE endpoint, `caller` — rounds par/a-6, par/a-7, par/a-8

Branch `par/a-8` (base poc a015a6f7). Vocabulary, binding: until the
integrator has built a file its theorems are WRITTEN, not proved; a premise
is REMOVED from an endpoint only after the build, the concrete endpoint,
standard axioms and the complete premise list. A per-declaration `decide`,
`MachineDefines`, `ChildBnd` are not reductions.

BUILT (integrator, poc a015a6f7, `Tests.AllTests` 1164 jobs): all files of
par/a-6 and par/a-7, unchanged — including `caller.machine_design_svH_free`
and the instances `caller_hierTyped`, `caller_portsShipped`,
`caller_designFull`. WRITTEN, NOT BUILT (par/a-8):
`Tools/ShippingOneOutFullCommand.lean`,
`Tests/Compiler/OneOutCallerFullTest.lean`.

## 0. Status of the endpoint

Declaration `Sparkle.Tests.Compiler.ShippingMachineInstTest.caller`: a
`circuit do` WITH a register (two slots, `sel : BitVec 2`, `acc : BitVec 8`),
ONE call entry `pick selS (accS + x)`; child `pick` compiled by the certified
GATE, one output `Signal (BitVec 8)`; `instFields = []`, one-output closing
`closeInsts`. Starting endpoint: `caller.machine_design_svHR` (and
`_closed`), with the run boundary and FOUR check premises under `∃ raw D`.

### Status table: the premises of `caller.machine_design_svHR`

"BUILT" = the derivation is built (a015a6f7). "REMOVED" = absent from a
BUILT endpoint of `caller` whose complete premise list was printed.

| premise of `caller.machine_design_svHR` | what it is | derivation (file) | BUILT | REMOVED from a built endpoint |
|---|---|---|---|---|
| A₂ `kidsComb D.modules (checkedOptimize b).body` | check | `core_runFactsH` (`RunFactsH.comb`), the head | yes | yes — `caller.machine_design_svH_free` (a015a6f7) |
| A₄ `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | check | `core_outsCheck_all_gate` + `gate_kidA` / `gate_kidR` (`caller_outsH`) | yes | yes — `caller.machine_design_svH_free` |
| A₃ `designCheck …` — conjuncts 1–6, 8 of `textCheckI`, `kidsPass` | check | `core_designCheckH`, `caller_designH` | yes | yes — in `_free`, `designCheck` is narrowed to (R2) |
| A₃, conjunct 7: **(R2) `portsMatchB (childMap D.modules) (checkedOptimize b)`** | check — INDEPENDENT CONDITION, still a premise of the built `_free` endpoint | `core_portsMatch_raw₁` + `GateChildPorts` + `portsMatchB_shipped`; `caller_portsShipped`, `caller_designFull` | yes (the derivation) | NO — pending the build of `OneOutCallerFullTest` |
| A₁ `shipsHierHCheck D.modules b` — `hierCheck` (7 conjuncts), `kidsLocal` | check | the head's case split + `RunFactsH` | yes | yes — in `_free`, `shipsHierHCheck` is narrowed to (R1) |
| A₁, third conjunct: **(R1) `hierTyped (childMap D.modules) b`** | check — INDEPENDENT CONDITION, still a premise of the built `_free` endpoint | `core_hierTyped₁` + `typed_widthOk` + `GateChildPorts.childTyped_ok`; `caller_hierTyped` | yes (the derivation) | NO — pending the build of `OneOutCallerFullTest` |
| `hr`, `entry`, `closes`, `ChildBnd ∧ EntryDefines pick` | run boundary | none: they stay premises (no runtime model) | n/a | n/a |

BUILT state, as the integrator's log printed it: `caller.machine_design_svH_free`
— 13 binders and antecedents; not a run / reflection / `ChildBnd`: 2 (the
closing premise and the residual antecedent); the residual antecedent
holds 2 INDEPENDENT check conditions (`hierTyped`; `portsMatchB`); its
`_closed` form: 1 (the residual). `ONEOUT RESIDUAL caller: hierTyped=T
portsMatchB=T (same run)`; the cross-check run agrees.

par/a-8 WIRES the two built derivations into a NEW endpoint,
`caller.machine_design_svH_full` (§9). Until it is built and its premise
list read, (R1) and (R2) are NOT removed.

OPEN whatever the build says: slotless parents (the head needs
`"rst" ∈ b.inputs`, i.e. `slots ≠ []`); machine-route children; several
outputs; every declaration other than `caller` (§10: reading only);
generalisation to all successful inputs.

## 1. What `RunFacts` fields the two consumers really use

* `core_designCheck_rest2` (via `core_designCheck_rest`,
  `Tools/ShippingChecksDesign.lean`) reads `gate`, `wfB`, `ndB`, `outs`
  (through `checkedOptimize_facts`) and `self`. It never reads `rst` or
  `wid`.
* `core_text_shipped_any` reads no `RunFacts` at all (the gate and
  `core_text_raw`).
* The combinational head (`machine_ships_hierHC`) reads, of
  `shipsHierHCheck_sound`: `binds`, `wfO`, `ndB`, `ndO`, `nofb`, `outs`,
  `rst`, `kidsLocal`, `hierTyped`. It never asks `instOutWidthsOk` (`wid`).

So the one-output forms needed BY THIS HEAD are: the gate (existed),
`ndB`, `self`, `outs`, `rst`, the children's combinational check — bundled
as `RunFactsH`. `core_instOutWidthsOk₁` is NOT needed by this head and was
not written (it is the sequential bundle's conjunct 8).

## 2. What replaces `MachineWired`'s clause 14 for `closeInsts`

Clause 14 (`instFields ≠ [] → Nodup (instance names) ∧ noSelfFeed`) records
two checks `closeInstsG` RUNS. `closeInsts` runs neither. For it:

* **distinct names** follow from what `instStmt` builds: the statement of
  call `k` is named `inst{k}_{mc.name}` (`instStmt_name`), the closed body is
  a permutation of the machine's body and those statements in order
  (`closeInsts_stmts`), the machine's body has no instance
  (`closedBody_kinds_of_run`), and `Tools.ShippingInstNames.instName_inj`
  (`s!"inst{a}_{x}" = s!"inst{b}_{y}" → a = b`) — which IS in the tree and
  built (`Tools/ShippingInstNames.lean`, 62a3aa3c, used by
  `Tools/ShippingConnsG.lean`); the previous note's "not in the tree" was
  wrong. → `closeInsts_instNames`, `core_instNames₁`. No `Nat.repr` lemma is
  missing.
* **no self read** follows from `CallStmt` (which `closeInsts_insts` gives
  for every instance statement of the closed body): the input connections
  read argument wires, the output connection drives the call's wire, the
  call's wire is no argument wire, the output port's name is no input
  port's. → `callStmt_parts`, `noSelfRead_of_calls`, `core_noSelfRead₁`.

Both are read off the closing's own result (`core_closeInsts` exposes
`closeInsts … = some (M, D)` of the run), not off `MachineWired`.

`core_outsExtracted₁` is `core_outsExtracted`'s proof with `hident` from
`closeInsts_insts` + `callStmt_parts`; it needs NO per-child premise
(`hkidP`): the one-output closing itself checks that the child has exactly
one output port whose name is no argument port's.

## 3. The two axes

* "The child is combinational": `core_kidsNotSeq₁` — in the one-output
  closing no instance's child has a `clk` / `rst` input, for ANY child kind,
  by the closing's own check (`CallStmt`); `gate_real_notSeq` says the same
  of a gate child from its allocated input names. So the clock / reset
  connection case of the port matching (`hclkB` / `hkidClk` in
  `core_portsMatch_raw`) is vacuous for a one-output parent.
* "The parent has a register": that is a different hypothesis. The
  combinational head asks `"rst" ∈ b.inputs` (`hrstIn`: the reset seeding and
  `hierRefineCheck_linkedH`). `core_rst_any` derives it from
  `d.shape.layout.slots ≠ []` — for either closing (it is `core_raw_facts`'
  first conjunct, which never used `hfne`). A slotless parent of
  combinational children has NO `rst` input (`extra = []`), so
  `RunFactsH.rst` is false for it and `machine_design_svH_free` does not
  apply as it stands. SLOTLESS PARENTS ARE NOT COVERED by anything here.

## 4. The two residual conditions (par/a-7)

### 4.0 What a gate child's run gave, and what was missing (C1)

| source (existing, built) | determines |
|---|---|
| `ChildFull c bs b design` (`gate_child_fullFacts`, `childFull_of_real`; `Tools/ShippingGateChildComb.lean`, `ShippingCallsGate.lean`) | (ii) the input port TYPES: `b.inputs.map (·.ty) = (bs.filter non-domain).map kindTy`; the name; `ChildComb`: assignments only, closed reads, `∃ ty, outputs = [out : ty]`, `out` driven, input names distinct and allocated. NOT the output's type or width; NOT that an input is a wire |
| `transition_closed` (`Tools/ShippingTransitionClosed.lean`): `(∃ ow, PrintBaseAt ow m) ∧ TypedPostReady m` of the RAW module | the output port named `out`, its type printable, `ty.bitWidth = ow`, `inputWires`, `wireNames`, `outputTyped` — but `ow` is existentially hidden |
| `transition_facts` (`Tools/ShippingMachineEntry.lean` 301): `RawValueAt srt.width bs m …`, last conjunct `PositiveBinders bs → PrintBaseAt srt.width m` | (i) `ow = srt.width` (`SType.width`: `1` for `.bool`, `w` for `.bits w`; the gate body is `quote … e` with `e : Term srt`). A BUILT statement; `transition_closed` only dropped the value |
| `gate_child_forwardCheck` (`Tools/ShippingCombKidText.lean`) | conjuncts 2, 3 of `textCheckI` of the child; nothing about a specific port |

So neither `ChildFull` nor `transition_closed` determined (i); `ChildFull.tys`
determined the types of (ii) but not the widths in either table (that needs
"the port is a wire, the only one of its name").

Strengthened: the common PRELUDE of `gate_child_comb` /
`gate_child_fullFacts` / `gate_child_forwardCheck` — one new variant,
`Tools.ShippingGatePorts.gate_child_base`, which ends in `transition_facts`
instead of `transition_closed` and returns the raw module with
`PrintBaseAt srt.width M ∧ TypedPostReady M`. Everything else of this round
is derived from it and from the existing `gate_child_fullFacts`; no
translator run is opened again.

### 4.1 The common facts: `GateChildPorts c bs w m` (C2)

`Tools/ShippingGatePorts.lean`. Fields (of the FULL-entry module `m`):
`name`; `inTys` (= `ChildFull.tys`); `inPrintable`; `inWire` (an input port
is a wire); `inNodup`; `wireAlloc`; `wireUnique`; `out` (`∃ ty, outputs =
[out : ty] ∧ PrintableType ty ∧ ty.bitWidth = w`); `order` (`Acyclic`);
`typed` (`TypedStmts (weOf m) m.body`); `outTyped` (`OutputTypedAt w …`);
`outDriven`. `gate_child_ports` (from a run of the full entry),
`gate_real_ports` (from `RealChild`), with `w = srt.width`. `post_facts`
(pure) carries the raw module's facts through the cleanup and the checked
merge.

### 4.2 The two views (C3)

| statement of §4 of the previous round | now WRITTEN as | from |
|---|---|---|
| (P2) input widths, emitter | `GateChildPorts.inWidths` (2nd conjunct), `.weS_in` | `inWire`, `wireUnique`, `inPrintable` via `declWidth_of_unique`, `declWidth_eq_weS` |
| (P3) `PortsIn y.1` | `GateChildPorts.portsIn` | `wireAlloc`, `inWire`, `out` |
| (P4) output width | `gate_real_outWidth`, `GateChildPorts.outWidth`, `.weS_out` | `out` |
| (T4, child side) input widths, IR | `GateChildPorts.inWidths` (3rd conjunct), `.declWidth_in` | the SAME three facts as (P2) |
| (T3) `childTyped (declWidth y.1) y.1` | `GateChildPorts.childTyped_ok` | `typed`, `outTyped`, `order`, `outDriven`, `out`, `assignTyped_of_typed` |

`inWidths` is ONE statement giving the `j`-th input port's width in BOTH
tables as the width of the type of the `j`-th non-domain binder.

### 4.3 `TypedExpr → widthOk` (C4, T1)

`Tools.ShippingTypedWidthOk.typed_widthOk : TypedExpr we e n → widthOk we e =
true`, by induction on `TypedExpr`. FINDING: none. `widthOk` refuses only a
`mux` whose false arm is wider than its true arm (`muxArmOk`); every other
node is accepted whatever its operator and arity, and `TypedExpr.mux` types
both arms at one width (`TypedExpr.width`). No constructor of `TypedExpr`
is refused. Also there: `assignTyped_of_typed` (T2 and the other two
conjuncts of `assignTyped`), `typedIn_assignTyped` (for a `TypedIn` module),
`kidsTyped_of`, `connsTyped_call`, `lookup_of_forall`.

### 4.4 The parent's two checks (C5)

`Tools/ShippingOneOutConns.lean`:

* `core_callConns₁` — from the core run: each instance statement of `b` is
  a call of a real child `y` (`moduleByName D.modules mn = some y.1`), with
  the connection list of `callStmt_parts`, the output wire a declared wire
  of `b` of the width of the type of `binders[nDecl + k]`, each argument
  wire a declared wire of `b` of the width of the type of the `let` binder
  of `args[j]`, connected to `y.1.inputs[j]`.
* `core_portsMatch_raw₁` (P1) and `core_hierTyped₁` (T2–T5).

PARENT-side facts each needs, by name: derived inside — `TypedIn b`
(`core_closed_typedIn`; uses the data conditions `hon`, `hoty`) and
`core_callConns₁`; kept as a hypothesis — the DATA condition
`callArgsOk d nDecl kidIns` (nothing in the compiler compares an argument's
`let` binder width with the child's port width). Neither asks
`slots ≠ []`.

CHILD-side hypotheses, each about one real child's module: `hkidW` (both),
`hkidT : PortsIn y.1` and `hkidIn` (emitter widths) for `portsMatchB`;
`hkidTy : childTyped …` and `hkidInD` (IR widths) for `hierTyped`. For a
gate child all five come from `GateChildPorts`; `hkidW` then reduces to a
data condition (the parent's result binder's width against `srt.width`).

Instance: `Tests/Compiler/OneOutCallerPortsTest.lean` (`pick_ports`,
`caller_portsRaw`, `caller_portsShipped`, `caller_hierTyped`,
`caller_designFull`).

## 4b. The generator's contract and the same-run check (review points 2, 3)

* `Tools/ShippingOneOutCommand.lean`: every run rebuilds statement and proof
  from the `Extra` and the four theorems given now; an existing
  `f.machine_design_svH_free` must be a theorem with no universe parameter,
  on standard axioms, of a type `isDefEq` the rebuilt one, recorded (doc
  string `usedMarker`) as built from the SAME four theorems — else the
  command throws naming both. Logs: `SVHFREE GENERATED …` (fresh) /
  `SVHFREE PRESENT …: already present, statement verified against the given
  Extra`. The log counts the residual-only checker constants written in the
  statement as INDEPENDENT conditions.
* REFUSE SCAN, its limit: the direct scan walks the constants WRITTEN in the
  statement only. With `def myCheck C m := designCheck C 0 m`, a residual
  `fun b D => myCheck … = true` passes it. Second line implemented
  (`hidden`): for each PREMISE of the statement, descend through `∀`, `→`,
  `∃` (lambda body), `∧`, `∨`, `↔`, `¬`, both sides of `=`, and at each
  leaf delta-expand the HEAD constant (`Lean.Meta.delta?`, whatever the
  reducibility attribute) up to 3 times along a path; a checker constant in
  a term PRODUCED by an expansion is refused. It still cannot see: an alias
  in argument position (not at a premise leaf's head); more than three
  definitions deep; a checker behind a structure field, an instance, a
  recursor / matcher application, an `opaque` constant, a theorem-valued
  term; anything in the final conclusion; an equivalent checker that is not
  one of the eight listed constants. It is an audit of the generation
  contract, not kernel soundness.
* `Tests/Compiler/OneOutCallerTest.lean`: the residual is evaluated on
  `(b, design)` of ONE run of the full entry, after evaluating on that pair
  that no module of `design` is named as `b`; under that condition
  `design.modules = D.modules` for the core run inside the same run
  (`Tools.ShippingOneOutSameRun.fullEntry_sameDesign`). Log:
  `ONEOUT RESIDUAL caller: hierTyped=<T/F> portsMatchB=<T/F> (same run)`.
  A second, separate core run is a labelled cross-check
  (`ONEOUT CROSS-CHECK`) with an agreement assertion (modules `==`, the
  module post-processes to `b`, both values equal).

## 5. The head: why option (a)

(b) "the sequential depth head at n = 0" (`machine_design_noPorts` through
`composedNW0_of_H`) asks `RunFacts.wid` (`instOutWidthsOk`) and
`Bd` (`KSBoundedIn`: the children's outputs within their ports' widths),
which for a gate child (output `out = _gen_out`, an alias, not a mask) is
exactly what `hierTyped` exists for; and its `designCheck` / `outsCheck`
generators ask `LeafKid` (a leaf register machine). It would need MORE than
(a) for a gate child.

(a) `Tools.ShippingOneOutHead.machine_design_svH_free`: `machine_ships_hierHC`'s,
`ships_design_svH`'s and `ships_design_svH_all`'s proofs joined at the run's
own `raw`, `D`, with the checker antecedent replaced by the case split of
`machine_ships_hierC_free` and by `RunFactsH`; one residual antecedent
`Extra b D` (a parameter: `fun _ _ => True` once §4 is closed). ~150 proof
lines, every step an existing lemma. Chosen.

## 6. Scope of "derived" (binding for any later "gap empty" statement)

* per-declaration DATA conditions decided by `decide` / `rfl` in
  `Tests/Compiler/OneOutCallerTest.lean` on `caller.machineData`
  (`callsOk 1`, slots/`ss` lengths, no late domain binder, `insts ≠ []`,
  `instFields = []`, `slots ≠ []`, outputs' `ty.bitWidth = width`, no memory
  callee, output names `charOk`, output types `scalarTy`) and what
  `#gate_child pick` left; plus the earlier generators' conditions;
* the RUNTIME BOUNDARY stays premises: the run of the entry (`RunsTo`),
  `MachineDefines` of `caller`, `ChildBnd` at the start world, `EntryDefines`
  of `pick`; no model of the Lean runtime;
* the conclusion is about `DesignSV (childMap D.modules) 0 (checkedOptimize
  b) …` — the module list of the core run's design — not the SV string, not
  "all successful inputs", not `#sim`;
* the compiler's guards (`checkedOptimize`'s fallback, `deinline`'s guards)
  are part of what is proved about;
* instance: `caller` ONLY. The general theorems are stated for any machine
  with calls, `instFields = []` (and `slots ≠ []` where marked); no other
  declaration was instantiated, none was measured.

## 7. The risk list written BEFORE the build of par/a-6 / par/a-7 (historical: all of it BUILT UNCHANGED at a015a6f7; the open list of par/a-8 is in §9)

par/a-7:

1. `Tools/ShippingOneOutConns.lean` — `core_callConns₁`: the largest blind
   proof. `key` is copied from the built `core_callConns`; new: the
   resolution through `closeInsts_insts` / `closeInsts_names`
   (`hmcc`, `hmcy`), the `rw [← hmcy]` goals, `callStmt_conn` (the `mapM`
   / `zip` positions, mirrored from `callStmtG_conn`), `inPortsOf_of_notSeq`
   (`cases hc : …` on Booleans), the count of the eleven components of
   `callStmt_parts`. It also depends on the UNBUILT
   `ShippingOneOutFacts.core_closeInsts` and `ShippingOneOutClose.callStmt_parts`.
   `core_portsMatch_raw₁` / `core_hierTyped₁`: the `rw` chains ending the
   width equalities.
2. `Tools/ShippingGatePorts.lean` — `gate_child_base`: the nine-component
   destructuring of `RawValueAt` and `admissible_zero` (two theorems of that
   name exist; `Tools.ShippingMachineEntry.admissible_zero` is the one used
   by `transition_closed`); `post_facts` (`rw [h]` on a goal with six
   occurrences); `GateChildPorts.childTyped_ok` (`Nodup.count`, the `show`
   through `childStmtTyped` and through the `any` predicate's `match`);
   `portsIn` (`sanitizeName "out" = "out"` by the `simp` used in
   `ShippingSVBridge`); structure eta in `declWidth_of_unique`'s first
   argument.
3. `Tools/ShippingOneOutCommand.lean` — Meta code written blind (as before:
   16 arguments, binder counts 6/7/7/7, `discharge`); new: `hidden`
   (`forallTelescope` / `lambdaTelescope`, `Lean.Meta.delta?` with a
   predicate), `findDocString?` / `addDocStringCore` on a generated theorem,
   `isDefEq` of two large statements, the tuple returned through
   `liftTermElabM`. RISK OF A FALSE REFUSAL by `hidden`: a legitimate
   premise whose head, expanded three times, mentions one of the eight
   constants (read by hand for `RunsTo`, `MachineDefines`, `MachineClosesAt`,
   `ChildBnd`, `EntryDefines`, `SourceInputs`, `BoundOff`, `InvN`: none
   does at the first step; deeper steps and the premises of
   `caller.machine_closes_at` were not all read).
4. `Tools/ShippingTypedWidthOk.lean` — `typed_widthOk` (`simp` with the
   equation lemmas of the mutual `widthOk` / `widthOkL`; the constructor
   argument names of `TypedExpr`), `lookup_of_forall` (`List.lookup_cons`,
   the `match` on `k == k'`), `kidsTyped_of` (`simp [hc, h1, h2]` through
   the instance arm), `connsTyped_call` (the `show`s through the
   connection `match`).
5. `Tests/Compiler/OneOutCallerPortsTest.lean` — `by decide` on
   `callArgsOk caller.machineData 1 kidIns` (true only if `caller`'s `let`
   binders of the two call arguments have widths 2 and 8 in the order of
   `pick`'s binders; `portsMatchB` evaluating to `true` on the real modules
   supports it but is not the same statement); the result binder's width
   `decide`; `hy`'s type reducing to `RealChild … ``pick y`.
6. `Tools/ShippingOneOutSameRun.lean` — `fullEntry_sameDesign`: the two
   `subst`s leave `hno` about the record update; the `fun y hy hye => hno y
   hy …` arguments rely on `(top f D).modules` reducing to the `map`.
7. `Tests/Compiler/OneOutCallerTest.lean` — the same-run evaluation and the
   cross-check (`==` on module lists; `sparkleChildCache` may serve the
   full entry's result from an earlier synthesis of `caller` in the same
   process: still a result of the full entry).

par/a-6 (unchanged, still unbuilt): `ShippingOneOutHead.lean`,
`ShippingOneOutClose.lean` (`instStmt_name`, `stmts_names`,
`instNames_append`, `Stmt.inst.inj`, `noSelfRead_of_calls`,
`kidsLocal_of_comb`), `ShippingOneOutFacts.lean` (`core_closeInsts`,
`hident`).

## 8. Build queue

Built (a015a6f7): `Tools.ShippingOneOutClose`, `…Facts`, `…Head`,
`…SameRun`, `…Command`, `Tools.ShippingTypedWidthOk`, `Tools.ShippingGatePorts`,
`Tools.ShippingOneOutConns`, `Tests.Compiler.OneOutCallerTest`,
`Tests.Compiler.OneOutCallerPortsTest`.

To build (par/a-8), in this order:

1. `Tools.ShippingOneOutFullCommand`
2. `Tests.Compiler.OneOutCallerFullTest`   (the concrete endpoint)

Dependants affected: none (two new files; nothing existing imports them;
no existing file is edited but this document).

`lakefile.lean` (integrator):

    lean_lib «Tools.ShippingOneOutFullCommand» where
      roots := #[`Tools.ShippingOneOutFullCommand]

`Tests/AllTests.lean` (integrator):

    import Tests.Compiler.OneOutCallerFullTest

## 9. par/a-8: the endpoint without the residual

`Tools/ShippingOneOutFullCommand.lean`: `#machine_design_svH_full f [facts,
typed, design, outs]` — `Tools.ShippingOneOutCommand.build` at the residual
`fun _ _ => True`, then the `True` antecedent DISCHARGED (`strip_true`:
`∃ a b, A a b ∧ (True → R a b)` gives `∃ a b, A a b ∧ R a b`, `trivial` in
the proof) so the stated type is `∀ …, ∃ raw D, hpost ∧ (Bnd → …)`; the
command throws if `True` is still the first antecedent (`trueAntecedent`).
Name `f.machine_design_svH_full` (and `_closed`): a different name from
`_free`, whose contract (a re-run with another residual is refused) is kept.
Same contract here (rebuild on every run; an existing constant is verified
by `isDefEq`, recorded lemma list `fullMarker`, standard axioms; logs
`SVHFULL GENERATED` / `SVHFULL PRESENT`). Both refuse scans run with a
residual that mentions no checker, so all eight checker constants are
refused, on the statement and on the closed form's.

`Tests/Compiler/OneOutCallerFullTest.lean`: the command at `caller` with
`[caller_factsH, caller_hierTyped, caller_designFull, caller_outsH]`;
`#machine_goal_gap_of` on the closed form; and a `run_cmd` that throws
unless: standard axioms; no checker constant written or hidden; `True` is
not an antecedent; every premise of `caller.machine_closes_at` is a run / a
reflection / `ChildBnd` (a name-separation premise is an error, printed);
the premises of class `other` are exactly `MachineClosesAt` on the open form
and NONE on the closed form. Lines `ONEOUT FULL PREMISE <decl>: <class> | …`,
one per binder / conjunct / antecedent. The header and the final log state
the scope (data conditions by name, the remaining runtime boundary, the
compiler guards, the object of the conclusion, ONE declaration).

PREDICTED premise list of `caller.machine_design_svH_full_closed` (to be
compared with the built log):

    data        mctx, mref, cctx, cref, w, w', b, design
    run         hr : RunsTo (synthesizeCombinational caller) mctx mref cctx cref w (b, design) w'
    reflection  entry : MachineDefines mctx mref cctx cref caller caller.machineData.shape
    reflection  the premises of caller.machine_closes_at in these contexts — expected:
                EntryDefines mctx mref cctx cref pick pick.gateValue
                (the built log of `_free_closed` counted no premise of another class there)
    ChildBnd    antecedent under ∃ raw D : ChildBnd mref cref w
    reflection  antecedent under ∃ raw D : EntryDefines mctx mref cctx cref pick pick.gateValue
    other       NONE

UNVERIFIED (par/a-8), in risk order:

1. `ShippingOneOutFullCommand.buildFull` — `mkAppM ``strip_true` must solve
   the two higher-order patterns `?A raw D`, `?R raw D` under the
   existentials; the type hint on `value0 xs`; `Core.betaReduce` leaving no
   `True →`; `build`'s `discharge` finding `ChildBnd` / `EntryDefines` in
   `And.intro hBnd hExtra` when `hExtra : True`.
2. `OneOutCallerFullTest` — the exact binder list of
   `caller.machine_closes_at` (the test THROWS if it has a premise of class
   `other`; the generator's header says name-separation premises exist in
   general — the built `_free_closed` log suggests none for `caller`);
   `#machine_goal_gap_of` on this shape; the classifier's `isAppOf` on
   pretty-printed-equal but `mdata`-wrapped premises.

## 10. The next axis, by READING only: other one-output parents with a register and gate children

No instance was written and nothing was measured. "Chain" = the four
per-declaration theorems (`_factsH`, `_hierTyped`, `_designFull`, `_outsH`)
+ `#machine_design_svH_full`. Its hypotheses: the data conditions
(`callsOk nDecl`, slot lengths, `hdomB`, `insts ≠ []`, `instFields = []`,
`slots ≠ []`, output width / name / scalar, no memory callee), per call
entry `k` the gate child's facts (`gate_real_ports` etc. from what
`#gate_child` left), `hkidW` (result binder width = child's sort width),
`callArgsOk d nDecl kidIns`; the generator needs `f.machine_ships_hierHR`
(`#machine_design_svHR f`) and, for the closed form, `f.machine_closes_at`.
All general theorems quantify over every entry `k`; none assumes one entry
or one callee.

| declaration | register | call entries (children) | `svHR` / `closes_at` exist | hypothesis expected to fail / to check |
|---|---|---|---|---|
| `callerTwice` | yes (`sel`) | 1 (`pick`; the copied `let` is one instance) | yes / yes | none seen. To check: `callArgsOk` — the second argument is the INPUT `x`, not a `let` of an expression; whether its argument index names a `let` binder of the same width |
| `callerNested` | yes (`acc`, + the flattened `counter2`'s) | 1 (`pick`) | yes / yes | none seen. `nDecl = 2` (`x`, `en`); the first argument is a nested machine's result (`s`): same `callArgsOk` question. The nested structure is inside the machine data, not in the lemmas' hypotheses |
| `callerD` | yes (2) | 1 (`pickD`, domain-polymorphic gate child) | yes / yes | none seen. `hdomB` needs the domain binder among the first `nDecl`; the child's `GateChildPorts.inTys` / `kidIns` already filter the domain binder. To check: the per-declaration theorems' statements for a domain-polymorphic `callerD` (the run is of ``callerD`` at its reflected data) |
| `callerRep` | yes (2) | 2 (`pick`, `pick`) | yes / yes | none of the lemmas' hypotheses; per-entry cases `k = 0, 1`. To check: the second call's argument is the FIRST call's result `y` — `core_callConns₁` describes an argument wire as the transition port of a `let`; whether `y` as an argument is such a `let` port is not readable from the test |
| `callerMix` | yes (2) | 2 (`pick`, `pickD`) | yes / yes | the lemmas: as `callerRep`. The CLOSED form: with two called declarations `machine_closes_at` carries NAME-SEPARATION premises (generator's header) — class `other`, so "other = none" fails for `_closed`; the open form is unaffected |
| `callerABA` | yes (2) | 3 (`pick`, `pickD`, `pick`) | yes / yes | as `callerMix` (name separation in the closed form); three per-entry cases |
| `callerInner` | yes (`acc`, + `innerPick`'s) | 2 (`pick` inside the sub-machine `innerPick`, `pick` in the body) | NO / NO (no `#machine_design_svHR`, no `#machine_closes_at` in the tests) | the generator's FIRST step: `callerInner.machine_ships_hierHR` does not exist. Not a hypothesis of the lemmas; the chain cannot start until that endpoint exists |

Summary of the reading: `callerTwice`, `callerNested`, `callerD` look like
instantiation alone (one entry each); `callerRep` adds a second entry of the
same child; `callerMix` / `callerABA` should reach the OPEN form but their
closed forms are expected to keep name-separation premises; `callerInner`
lacks the base endpoint. The one question common to all but `caller`:
whether every call argument is a `let` port with `callArgsOk` true — a
`decide` per declaration, false makes the theorem not exist (nothing false
is proved).

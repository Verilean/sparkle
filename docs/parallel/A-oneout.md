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

## 11. par/a-9: the hand instances as a GENERATOR, and the next four declarations

Branch `par/a-9` (base poc a1aad854, where §9 is BUILT:
`caller.machine_design_svH_full_closed` has no check premise).
WRITTEN, NOT BUILT: `Tools/ShippingOneOutGenCommand.lean`
(`#machine_oneout f`, `#machine_oneout_try f "EXPECTED"`),
`Tests/Compiler/OneOutFamilyTest.lean`. No existing file is edited but this
document. Until the integrator has built the test and its premise lists are
read, NO premise of any endpoint below counts as removed.

### 11.1 What the generator writes

The hand instances of `OneOutCallerTest` / `OneOutCallerPortsTest`, as the
same applications of the same general theorems at `f`'s data:

| hand instance (`caller`) | generated | general theorem |
|---|---|---|
| `pick_full` | `c.gate_full` | `childFull_of_real` |
| `pick_ports` | `c.gate_ports` | `gate_real_ports` |
| (inline in `caller_designH`) | `c.gate_kidK` | `gate_real_kidK` |
| `pick_width` | `c.gate_width : SType.width c.gateSort = W` | `rfl` / `decide` |
| `caller_factsH` | `f.machine_factsH` | `core_runFactsH` |
| `caller_outsH` | `f.machine_outsH` | `core_outsCheck_all_gate`, `gate_kidA` / `gate_kidR` |
| `caller_portsRaw` | `f.machine_portsRawH` | `core_portsMatch_raw₁` |
| `caller_portsShipped` | `f.machine_portsShippedH` | `portsMatchB_shipped`, `core_hierGate_any` |
| `caller_hierTyped` | `f.machine_hierTypedH` | `core_hierTyped₁` |
| `caller_designH` + `caller_designFull` | `f.machine_designFullH` | `core_designCheckH` |
| `#machine_design_svH_full caller [...]` | `buildFull` at the four generated names | the head |

Differences from the hand text, all of form:

* each `by decide` of the hand proofs is a NAMED theorem `f.oneout_*`
  (list in the generator's header), so a failed condition is reported by
  name (`ONEOUT GEN f: FAILED (data condition …)`) and decided once;
* the per-entry `cases k` (one arm per entry, `absurd hk'` at the end) is
  replaced by ONE decided statement `f.oneout_entries : ∀ k (hk : k <
  insts.length), …` and `rw [hc] at hy` — no entry count in a proof; with
  several distinct callees the statement is a disjunction over them
  (written, not exercised in this round);
* `kidIns` is `f.oneout_kidIns`, a list of NUMERALS per entry computed by
  the generator from the widths of the types of `f`'s `let` binders of each
  call's arguments. `f.oneout_callArgs` (`callArgsOk` at these numerals) is
  then true by construction of the numerals; the comparison with the CALLEE
  is `f.oneout_entries`' second conjunct (`f.oneout_kidIns k` = the widths
  of `c`'s declared non-domain binders) — the same content as the hand
  instance's one `decide`, split in two;
* the result binder's width is the numeral `W` of `c.gate_width`, compared
  with `binders[nDecl + k]` in `f.oneout_entries`' third conjunct.

### 11.2 Is a call argument always a `let` port? (the open question of §10)

Read in `Sparkle/Compiler/Elab.lean`: `machInstance` converts every
argument and, for a non-domain kind, calls `machLetIndex nm kind v' lets`
with `kind` THE CALLEE'S binder kind: if the converted argument is already
a `let` placeholder its index is reused; if a `let` with the same value
exists it is reused; otherwise a NEW `let` `inst{k}_arg{j}` of that kind is
pushed. So `args[j]` is always a `let` index, whatever the argument is —
an input (`callerTwice`: `x`), a sub-machine's state (`callerNested`: `s`),
another call's result (`callerRep`: `y`, read as the call output's
transition input inside the new `let`'s value). `core_callConns₁` describes
exactly that (the argument wire is the transition port of the `let`
`args[j]`), for every entry. NO generalisation of `core_callConns₁` is
needed for these four and none was written. `callArgsOk` is expected true:
a new `let` has the callee's kind by construction; a reused one has the
kind it was made with, which is the kind of the same Lean type.
This is a reading of the (partial) reader, not a theorem about it: the
kernel `decide`s on the reflected data are what the endpoints rest on.

### 11.3 Per declaration: endpoint — premise — predicted state

Starting endpoint in every row: `f.machine_design_svHR` (BUILT earlier),
whose four check premises under `∃ raw D` are
A₁ `shipsHierHCheck D.modules b`, A₂ `kidsComb D.modules (checkedOptimize b).body`,
A₃ `designCheck (childMap D.modules) 0 (checkedOptimize b)`,
A₄ `outsCheck (childMap D.modules) 0 (checkedOptimize b)`.
"Predicted" = what `#machine_oneout f` is expected to produce;
"BUILT / REMOVED" is filled by the integrator's build only.

| declaration | new endpoint | A₁ | A₂ | A₃ | A₄ | predicted `ONEOUT GEN` line | BUILT / REMOVED |
|---|---|---|---|---|---|---|---|
| (i) `caller` | `caller.machine_design_svH_full` (exists, BUILT at a1aad854 from hand lemmas) | absent (built) | absent (built) | absent (built) | absent (built) | `PRESENT` — statement rebuilt from the generated lemmas `isDefEq` the existing one; rebuilt proof added as `caller.machine_design_svH_full_gen` | endpoint: BUILT / REMOVED at a1aad854; the generator's reproduction: pending the integrator's build |
| (ii) `callerTwice` | `callerTwice.machine_design_svH_full` (+ `_closed`) | predicted absent | predicted absent | predicted absent | predicted absent | `GENERATED` | pending the integrator's build |
| (iii) `callerD` | `callerD.machine_design_svH_full` (+ `_closed`) | predicted absent | predicted absent | predicted absent | predicted absent | `GENERATED` | pending the integrator's build |
| (iv) `callerNested` | `callerNested.machine_design_svH_full` (+ `_closed`) | predicted absent | predicted absent | predicted absent | predicted absent | `GENERATED` | pending the integrator's build |
| (v) `callerRep` | `callerRep.machine_design_svH_full` (+ `_closed`) | predicted absent | predicted absent | predicted absent | predicted absent | `GENERATED` | pending the integrator's build |

Predicted premises of each `f.machine_design_svH_full_closed`: the data
binders; `hr : RunsTo (synthesizeCombinational f) …`; `MachineDefines f`;
the premises of `f.machine_closes_at` — one `EntryDefines` of the callee
(`ShippingCallsCloseTest` audits exactly 1 premise for each of the four);
under `∃ raw D`: `ChildBnd mref cref w` and `EntryDefines` of the callee.
`other`: none (the test throws otherwise).

Data conditions decided per declaration (kernel `decide` / `rfl`; all are
conditions on the reflected data, none is a reduction):

| declaration | `nDecl` (reader) | callee, `W` | predicted `f.oneout_kidIns` | conditions decided | known true before this round |
|---|---|---|---|---|---|
| `callerTwice` | 1 | `pick`, 8 | `[[2, 8]]` | `oneout_callsOk`, `_slotLen`, `_domB`, `_insts`, `_instFields`, `_outTy`, `_nomem`, `_slots`, `_outChars`, `_outScalar`, `_callArgs`, `_entries`; `pick.gate_width` and the Bool / bit-vector positions inside `pick.gate_full` / `_ports` / `_kidK` | `callsOk`, slot count, no late domain binder, `instFields = []` (= `gateCallsOk`, decided inside the BUILT `callerTwice.machine_closes_at`); `_nomem` (same theorem) |
| `callerD` | 2 | `pickD`, 8 | `[[2, 8]]` | the same list, with `pickD.gate_*` | as above (`callerD.machine_closes_at`) |
| `callerNested` | 2 | `pick`, 8 | `[[2, 8]]` | the same list | as above (`callerNested.machine_closes_at`) |
| `callerRep` | 1 | `pick`, 8 | `[[2, 8], [2, 8]]` | the same list; `_entries` over two entries | as above (`callerRep.machine_closes_at`) |

The `nDecl` and `oneout_kidIns` columns are predictions; the generator
computes both from the reflected data and prints them in its log line.

NOT known before the build for any of the four: `_outTy`, `_slots`,
`_insts`, `_outChars`, `_outScalar`, `_callArgs`, `_entries`, and that the
generated proofs elaborate (the generator is Meta code written without a
build). If a condition is false the line is `FAILED (data condition <name>
…)`, the endpoint does not exist for that declaration and nothing is left
in the environment; the test's assertion `"GENERATED"` then fails for that
section only.

Out of scope in this round: `callerMix`, `callerABA` (two called
declarations: `machine_closes_at` may contribute name-separation premises,
class `other`, to the closed form; the generator's several-callee branch is
unexercised); `callerInner` (no `machine_ships_hierHR`: the test asserts
`REFUSED`).

### 11.4 The scope sentence required with any "no check premise" claim of this section

For ONE declaration `f` at a time (a parent WITH a register, GATE children,
the one-output closing): `f.machine_design_svH_full_closed` has none of the
four check premises of `f.machine_design_svHR` — GIVEN (1) the
per-declaration data conditions `f.oneout_*`, `c.gate_width` and what
`#gate_child c` left, decided by the kernel on the reflected data
(conditions, not reductions); (2) the runtime boundary, which stays
premises: the run of the entry, `MachineDefines f`, `EntryDefines c`,
`ChildBnd`; (3) the compiler's guards with fallback; and the conclusion is
(4) about `DesignSV (childMap D.modules) 0 (checkedOptimize b)` — the module
list, not the SV string, not `#sim`. NOT covered: slotless parents (the
head needs the parent's register), machine-route children, several
outputs, any declaration not listed as GENERATED in a built log, "all
successful inputs".

### 11.5 UNVERIFIED (par/a-9), in risk order

1. `Tools/ShippingOneOutGenCommand.lean` — Meta / syntax code written
   blind: the tactic quotations `( … ; … )` with `obtain` / `rcases`
   patterns and the shared hygiene of `k hk y hy p hp j q hq hc hki hres`
   between the quotation that introduces them and the ones that use them
   (the built generators share `k hk' y hy` the same way); `rw [hc] at hy`
   on `RealChild mref cref (insts[k]).1 y`; `rw [hki]` on the goal under
   `∃`; the term `hres.trans (congrArg Option.some …)`; `decide` on
   `f.oneout_entries` (a bounded `∀ k (hk : k < insts.length)` with a
   `Name` equality, a `List Nat` equality and an `Option Nat` equality);
   `emitOrVerify`'s scratch generation and `setEnv`; the `TSyntax`
   constructions `⟨….raw⟩`; the empty binder splice of `f.machine_factsH`.
2. The statements of the named data lemmas must be the hypotheses of the
   general theorems up to `isDefEq` (they were copied from the signatures
   with full names: `MixedGateBinder.domain` written out, `nDecl` a
   numeral).
3. `endpoint`: `buildFull`'s `discharge` on generated lemmas (their binder
   order is the hand lemmas': `hcore hpost entry closes [hg] hB hR…`); for
   `caller` the `PRESENT` path with another record and `addTheorem` of
   `_gen`.
4. `callerD` / `callerNested`: `f.machine_ships_hierHR` having the 16
   arguments / 11 binders `build` expects (true for `caller`; not read for
   these); `callerNested`'s data under the nested reading.
5. The data conditions listed as "NOT known before the build" in §11.3.
6. `Tests/Compiler/OneOutFamilyTest.lean`: `gapOf` on the new closed
   forms; `premiseList` on `callerD`'s endpoint.

### 11.6 Build queue (par/a-9)

1. `Tools.ShippingOneOutGenCommand`
2. `Tests.Compiler.OneOutFamilyTest` (the concrete endpoints; imports
   `Tests.Compiler.OneOutCallerFullTest`)

`lakefile.lean` (integrator):

    lean_lib «Tools.ShippingOneOutGenCommand» where
      roots := #[`Tools.ShippingOneOutGenCommand]

`Tests/AllTests.lean` (integrator):

    import Tests.Compiler.OneOutFamilyTest

## 12. par/a-10: two called declarations (`callerMix`, `callerABA`) and a machine-route slotless child (`callerL` → `pickByteH`)

Branch `par/a-10` (base poc 04e5327b, where §11 is BUILT: `caller`,
`callerTwice`, `callerD`, `callerNested`, `callerRep` have
`f.machine_design_svH_full(_closed)` with no check premise).
WRITTEN, NOT BUILT: `Tools/ShippingLeafOneOut.lean`,
`Tests/Compiler/OneOutTwoCalleeTest.lean`,
`Tests/Compiler/OneOutCallerLTest.lean`. No existing file is edited but this
document. Until the integrator has built the tests and their premise lists
are read, NO premise of any endpoint below counts as removed.

### 12.1 `callerMix`, `callerABA`: what was read, what is expected

* `closesAtCore` (`Tools/ShippingMachineClosesAtGen.lean`): the name
  premises `hnames` / `hparent` are BINDERS of `f.machine_closes_at` only
  when `Tools.ShippingNameSep.sepB` fails on a pair of names; otherwise the
  proof discharges them (`hnames_of _ (by decide)`,
  `hparent_of _ _ (by decide)`); `hfresh` is discharged when no output name
  starts with `i`.
* `Tests/Compiler/ShippingCallsCloseTest.lean` (BUILT, in `Tests.AllTests`)
  asserts `auditClosed callerMix 2` and `auditClosed callerABA 2`: exactly
  two proposition binders each. With two distinct callees the generator
  pushes two reflection binders first, so there is NO name binder.
  §10 / §11 ("name-separation premises expected in the closed form") was a
  guess made without reading this; it is expected to be wrong.
* `#machine_oneout`'s several-callee branch (`perEntry` at `n ≥ 2`, the
  disjunction `alt`, the `binders` / `hRs` loops) was read against the
  single-callee branch that built: no defect found, NO corrected generator
  written. It has never been elaborated.

| declaration | endpoint | premise of `f.machine_design_svHR` | state |
|---|---|---|---|
| `callerMix` | `callerMix.machine_design_svH_full` (+ `_closed`), by `#machine_oneout` | A₁ `shipsHierHCheck D.modules b` | WRITTEN (the test; the generator is built) — predicted absent, pending build |
| | | A₂ `kidsComb D.modules (checkedOptimize b).body` | predicted absent, pending build |
| | | A₃ `designCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | | A₄ `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | | name separation in the closed form | predicted NOT a premise (discharged inside `callerMix.machine_closes_at` by `ShippingNameSep`: a per-declaration decided condition, not a reduction), pending build |
| `callerABA` | `callerABA.machine_design_svH_full` (+ `_closed`), by `#machine_oneout` | A₁–A₄ | predicted absent, pending build |
| | | name separation in the closed form | predicted NOT a premise, pending build |

Predicted log: `ONEOUT GEN callerMix: GENERATED [callerMix.machine_design_svH_full,
callerMix.machine_design_svH_full_closed] — … callArgsOk with
callerMix.oneout_kidIns = [[2, 8], [2, 8]], per entry the callee among
[pick, pickD] … [8, 8]`; the same for `callerABA` with three rows
`[[2, 8], [2, 8], [2, 8]]`; `ONEOUT FAMILY f: … other: NONE …`;
`ONEOUT TWO-CALLEE f: f.machine_closes_at has 2 proposition binders, all
EntryDefines …`. Closed-form proposition binders: `hr`, `entry`
(`MachineDefines f`), `hR0` (`EntryDefines pick`), `hR1`
(`EntryDefines pickD`); under `∃ raw D`: `ChildBnd`, the two `EntryDefines`.
The numerals are predictions; the generator prints the computed ones.

Data conditions decided per declaration: the `f.oneout_*` list of §11.3
(`_entries` a disjunction over `pick` / `pickD`), `pick.gate_width`,
`pickD.gate_width`, what `#gate_child` left, and — inside the BUILT
`f.machine_closes_at` — `gateCallsOk` and the name separation on the
candidate renderings.

### 12.2 `callerL` → `pickByteH`: the child-side hypotheses for a slotless leaf MACHINE child

`callerL`: one register (`sel`), `nDecl = 1` (`w`), one entry
`pickByteH w selS`, `instFields = []`. `pickByteH`: machine route, three
`let`s, no register, no call, the one output `out`.

Which child-side hypothesis comes from where (`Tools/ShippingLeafOneOut.lean`;
all read off ONE bundle `SlotlessLeaf mctx mref cctx cref c dk` =
`LeafKidAny` + `gateCallsOk dk.nIn`, `lets ≠ 0`, `slots = []`, the one
output `out`):

| hypothesis | consumer | for the machine leaf | existing (built) / NEW (written) |
|---|---|---|---|
| `hkidW` | `core_portsMatch_raw₁`, `core_hierTyped₁` | `hkidW_one` + `SlotlessLeaf.outTys` + the data condition `callWidthsStrict d nDecl (fun _ => dk.shape.layout.outs)` | existing: `hkidW_one`, `leaf_real_outTys_any` |
| `hkidT : PortsIn y.1` | `core_portsMatch_raw₁` | `SlotlessLeaf.portsIn` | existing: `leaf_real_portsIn` |
| `hkidIn` (emitter widths), `hkidInD` (IR widths) | both | `SlotlessLeaf.inWidths` — ONE statement, both tables, from the common `LeafPorts` facts (`args`, `argW`, `wal`, `pos`, `ins`) | NEW: `inPort_both` (the IR view is the intermediate fact of `inPort_weS`'s proof), `leafPorts_inWidths2`, `leafPorts_inPortsOf_eq` (slotless: every input is an argument port) |
| `hkidTy : childTyped (declWidth y.1) y.1` | `core_hierTyped₁` | `SlotlessLeaf.childTyped` | NEW: `typedIn_childTyped_out`, `childTyped_post_out`, `leaf_run_typedIn_out` / `leaf_real_typedIn_out` (see below) |
| `hkidK` | `core_designCheckH` | `SlotlessLeaf.kidK` | existing: `leaf_real_kidK_out` |
| `hkidA`, `hkidR` | `core_outsCheck_all_gate` | `SlotlessLeaf.kidA`, `.kidR` | NEW (pure): `comb_kidA`, `comb_kidR` from `ChildComb` + empty design; the `ChildComb` from the existing `machineChild_of_real`. The existing `leaf_real_kidA` asks `slots ≠ []` and does not apply |

FINDING (why `hkidTy` needed a run theorem and not only `leaf_real_typedIn`).
`leaf_real_typedIn` returns `y.1 = m0 ∨ y.1 = mergeChecked m0` with
`TypedIn m0`. For the merged case `typedIn_mergeDuplicates_out` needs `m0`
ASSIGNMENT-ONLY, and `childTyped` needs `out` written exactly once; the
conclusion of `leaf_real_typedIn` has neither (only the opposite fact for a
machine WITH slots), `mergeChecked_print_cases`' third alternative
(`printOk` of the merge) gives no typing, and nothing says a raw merge of a
body with a register keeps a register. `machineChild_of_real` has
`ChildComb y.1` but about another existential witness. So
`leaf_run_typedIn_out` is `leaf_run_typedIn`'s proof — lines 374–573 of
`Tools/ShippingLeafTyped.lean` copied unchanged by a script, in that file's
namespace and `open`s — with `hsl : slots = []`, `hone : outs' names =
["out"]` and the conclusion `… ∧ m0.body.all isAssign = true ∧
count "out" (writesOf m0.body) = 1`. The two new conjuncts:
`closeMachine_slotless_body` (no slot: the closed body is the transition's
statements before the packed assignment, then `outAssigns`),
`TypedStmts` of the closed transition (assignments), the transition's
targets are allocated names (`closedTransition_of_run`) and `out` is not
(`count_out_slotless`). Through the validated merge the writes are kept by
the existing `mergeDuplicates_closed`, fed with `readsClosedB_of_all` (any
body is read-closed over the list of every name it reads).

| declaration | endpoint | premise of `callerL.machine_design_svHR` | state |
|---|---|---|---|
| `callerL` | `callerL.machine_design_svH_full` (+ `_closed`), by the existing `#machine_design_svH_full callerL [callerL_factsH, callerL_hierTyped, callerL_designFull, callerL_outsH]` | A₁ `shipsHierHCheck D.modules b` (incl. `hierTyped`) | WRITTEN — pending build |
| | | A₂ `kidsComb D.modules (checkedOptimize b).body` | WRITTEN — pending build |
| | | A₃ `designCheck (childMap D.modules) 0 (checkedOptimize b)` (incl. `portsMatchB`) | WRITTEN — pending build |
| | | A₄ `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | WRITTEN — pending build |
| | | `hr`, `MachineDefines callerL`, `MachineDefines pickByteH`, `ChildBnd` | run boundary: they stay premises |

No residual was needed by reading: every child-side hypothesis has a
WRITTEN derivation. If `leaf_run_typedIn_out` or `SlotlessLeaf.childTyped`
does not build, the fallback is `#machine_design_svH_free callerL
(fun b D => hierTyped (childMap D.modules) b = true) [...]` with (R1) as the
one independent residual — NOT written in this round.

Predicted log: `SVHFULL GENERATED [callerL.machine_design_svH_full,
callerL.machine_design_svH_full_closed]: …`; the closed form's non-data
premise lines:

    run         binder hr : RunsTo (synthesizeCombinational `callerL) mctx mref cctx cref w (b, design) w'
    reflection  binder entry : MachineDefines mctx mref cctx cref `callerL callerL.machineData.shape
    reflection  binder hR0 : MachineDefines mctx mref cctx cref `pickByteH pickByteH.machineData.shape
    ChildBnd    antecedent under the existentials : ChildBnd mref cref w
    reflection  antecedent under the existentials : MachineDefines mctx mref cctx cref `pickByteH pickByteH.machineData.shape
    other       NONE

and `ONEOUT MACHINE-LEAF callerL: … other: NONE … goal gap …: none NOT ALLOWED`.

Data conditions (kernel `decide` / `rfl`; conditions, not reductions).
`callerL` at `nDecl = 1`: `callerL_callsOk`, `_slotLen`, `_domB`, `_insts`,
`_instFields`, `_outTy`, `_nomem`, `_slots` (the PARENT has a register),
`_outChars`, `_outScalar`, `_strict` (`callWidthsStrict callerL.machineData 1
(fun _ => pickByteH.machineData.shape.layout.outs)`: the result binder's
width), `_callArgs` (`callArgsOk callerL.machineData 1 kidIns`, `kidIns` =
`declWidths pickByteH.machineData`), and that entry 0's callee is
`pickByteH` (by reduction). `pickByteH` at `nIn` (the fields of
`pickByteH_leaf`): `ok`, the body equation, `callsOk nIn`, no domain binder
after `nIn`, `insts = []`, the slot count, output width / name / scalar
conditions, `gateCallsOk nIn`, `lets ≠ 0`, `slots = []`, the one output
`out`; its closing `pickByteH.machine_closes` is the generated theorem.

SCOPE sentence (binding). For ONE declaration, `callerL` — a parent WITH a
register, one call of a SLOTLESS LEAF MACHINE child with the one output
`out`, the one-output closing — `callerL.machine_design_svH_full_closed` is
WRITTEN to have none of the four check premises of
`callerL.machine_design_svHR`, GIVEN (1) the per-declaration data conditions
above; (2) the runtime boundary, which stays premises: the run,
`MachineDefines callerL`, `MachineDefines pickByteH`, `ChildBnd`; (3) the
compiler's guards with fallback (`checkedOptimize`, `deinline`,
`closeInsts`' checks, `mergeChecked`'s validation of the child's merge); and
the conclusion is (4) about `DesignSV (childMap D.modules) 0
(checkedOptimize b)` — the module list, not the SV string, not `#sim`. NOT
covered: slotless PARENTS, machine children with registers or calls,
several outputs, `callerLN`, `hftByte`, "all successful inputs". "The parent
has a register" (`callerL_slots`, the head) and "the child is a slotless
machine" (`SlotlessLeaf.slots`) are separate conditions.

### 12.3 `callerLN`, `hftByte`: what they need beyond `callerL` (READING only; nothing written, nothing measured)

Both have `machine_design_svHR` (`ShippingChildBoundaryTest`) and
`machine_closes_at` with ONE premise, the child's `MachineDefines`
(`auditClosed … 1`). Every `#machine_design_svHR` is built from the one head
`machine_ships_hierHC` (`ShippingMachineComposeRCommand` 341), so
`buildFull`'s 16-argument test is expected to pass.

* `callerLN` (child `pickByteH`; a flattened sub-machine `counterB`; the
  call is the `return` value; `nDecl = 2`): the SAME chain as `callerL` with
  `nDecl := 2` and the same `pickByteH_*` theorems. New `decide`s only:
  `callsOk 2`, `callWidthsStrict … 2 …`, `callArgsOk … 2 kidIns` (the first
  argument is a register, the second a sub-machine's result: by §11.2 both
  are `let`s of the callee's kinds). No new general theorem is expected.
* `hftByte` (child `Sparkle.IP.Net.HTTP.httpGetByte`, an implicit DOMAIN
  binder; the parent is `(hftStrategy inByte inValid).outByte`, the call
  sits in a sub-machine of the telescope): the general theorems quantify
  over any `MachineData`, and `SlotlessLeaf` is stated at `dk.nIn` with
  `declWidths` filtering the domain binder, so no new statement is expected.
  To check, none of it read off the data: (a) `httpGetByte`'s `SlotlessLeaf`
  fields — `callsOk nIn` and "no domain binder after `nIn`" with the
  implicit domain binder among the first `nIn`; `lets ≠ 0`, `slots = []`,
  `outs = [out]` are already decided inside the BUILT
  `hftByte.machine_closes_at`; (b) the PARENT's `slots ≠ []` (its registers
  are the flattened sub-machines'), `instFields = []`, `callArgsOk` and
  `callWidthsStrict` at its `nDecl`; (c) the cost of the kernel `decide`s on
  the larger data (12 `let`s in the child; the strategy's telescope) — may
  need `decide +kernel` or fail on depth, which is a failed data condition,
  not a false theorem; (d) the per-entry `cases k` arms need the entry's
  callee to reduce to `httpGetByte`.

A generator for the machine-leaf case (`#machine_oneout` accepting a
machine-route callee, emitting `c.machine_leaf` instead of `c.gate_*`) is
the natural next step once `callerL` is BUILT; not written.

### 12.4 UNVERIFIED (par/a-10), in risk order

1. `Tools/ShippingLeafOneOut.lean`, `leaf_run_typedIn_out`: the copied body
   is the built text, but it is elaborated in a NEW file (same namespace and
   `open`s re-declared by hand; `variable {m}` of the original not
   re-declared — the copied lines do not use it); the appended tail:
   `closeMachine_slotless_body hbodyc hsl` (unification of `B`, `w` with
   `Bc`, `coreW`), `typedc st hst'` then `subst he`, `simp only [outAssigns,
   List.mem_map] at h1`, `count_out_slotless hBa namedc hone`.
2. `closeMachine_slotless_body`: `simp [closeMachine, hpw, hdrop]` proving
   the body equation (the built `closeMachine_body` uses the same `simp`
   with one more rewrite), then the `rw` chain through `nextAssigns_nil` /
   `registers_nil`.
3. `typedIn_childTyped_out`: the `cases st` arms (`register` / `inst` by
   `rfl`, `memory` from `hall`), the `show`s through `childStmtTyped` and
   the `any` predicate (mirrored from `GateChildPorts.childTyped_ok`);
   `childTyped_post_out`: `rw [e, mergeChecked_assign hall]`,
   `mergeDuplicates_ports … .2.1.trans hout`.
4. `count_out_slotless` (`rfl` for `writesOf (outAssigns w [o]) = [o.name]`,
   the final `omega` over `List.count` atoms), `readsClosedB_of_all` (the
   `show` through the recursive definition), `mergeDuplicates_assign`.
5. `inPort_both` / `leafPorts_inWidths2` (copies of built proofs with one
   more conjunct), `leafPorts_inPortsOf_eq`, `SlotlessLeaf.comb` (the `have`
   through the definition `ChildIface`).
6. `Tests/Compiler/OneOutCallerLTest.lean`: the `decide`s on
   `pickByteH.machineData` at `nIn` and on `callerL.machineData` at `1`
   (`callerL_callArgs`, `callerL_strict` are true only if the reading of the
   source is right); `hy`'s type reducing to `RealChild … ``pickByteH y`;
   `discharge` finding `MachineDefines pickByteH` among the boundary's
   conjuncts (`isDefEq` with the statement `#machine_design_svHR` wrote);
   the `hidden` scan on a `MachineDefines` premise of a child; `gapOf`.
7. `Tests/Compiler/OneOutTwoCalleeTest.lean`: the generator's several-callee
   branch elaborated for the first time (`rcases hcase with ⟨hc, hki, hres⟩
   | hcase` and the shared names across quotations; `decide` on the
   disjunctive `oneout_entries`; `discharge` with two `EntryDefines`); the
   assertion that `machine_closes_at`'s proof uses `hnames_of` AND
   `hparent_of`.

### 12.5 Build queue (par/a-10)

1. `Tools.ShippingLeafOneOut`
2. `Tests.Compiler.OneOutTwoCalleeTest` (imports `Tests.Compiler.OneOutFamilyTest`)
3. `Tests.Compiler.OneOutCallerLTest` (imports `Tests.Compiler.OneOutCallerFullTest`, `Tools.ShippingLeafOneOut`)

2 and 3 are independent of each other. `lakefile.lean` (integrator):

    lean_lib «Tools.ShippingLeafOneOut» where
      roots := #[`Tools.ShippingLeafOneOut]

`Tests/AllTests.lean` (integrator):

    import Tests.Compiler.OneOutTwoCalleeTest
    import Tests.Compiler.OneOutCallerLTest

## 13. par/a-11: `callerLN`, `hftByte` by hand, the generator for slotless leaf machine children, and the slotless-PARENT axis on paper

Branch `par/a-11` (base poc 85ebb9fd, where §12 is BUILT: `callerMix`,
`callerABA`, `callerL` have `f.machine_design_svH_full(_closed)` with no
check premise). WRITTEN, NOT BUILT:

    Tools/ShippingLeafOneOutGen.lean           gateCallsOk_parts, leaf_outWidth
    Tools/ShippingOneOutAnyGenCommand.lean     #machine_oneout_any, #machine_oneout_any_try
    Tests/Compiler/OneOutLeafAudit.lean        the audit of OneOutCallerLTest's run_cmd, as a function
    Tests/Compiler/OneOutCallerLNTest.lean     hand instance, callerLN
    Tests/Compiler/OneOutHftByteTest.lean      hand instance, hftByte
    Tests/Compiler/OneOutAnyFamilyTest.lean    the generator on callerL, callerLN, hftByte, callerMix, callerInner

No existing file is edited but this document. Until the integrator has
built the tests and their premise lists are read, NO premise of any
endpoint below counts as removed.

### 13.1 Per declaration: endpoint — premise — state

A₁–A₄ are the four check premises of `f.machine_design_svHR` under
`∃ raw D`: A₁ `shipsHierHCheck D.modules b`, A₂ `kidsComb D.modules
(checkedOptimize b).body`, A₃ `designCheck (childMap D.modules) 0
(checkedOptimize b)`, A₄ `outsCheck (childMap D.modules) 0
(checkedOptimize b)`.

| declaration | endpoint (who builds it) | premise of `f.machine_design_svHR` | state |
|---|---|---|---|
| `callerLN` | `callerLN.machine_design_svH_full` (+ `_closed`) — by hand (`OneOutCallerLNTest`, `#machine_design_svH_full`) OR by `#machine_oneout_any` (`OneOutAnyFamilyTest`); the two files add the SAME name and exclude each other | A₁ | WRITTEN — pending build |
| | | A₂ | WRITTEN — pending build |
| | | A₃ | WRITTEN — pending build |
| | | A₄ | WRITTEN — pending build |
| | | `hr`, `MachineDefines callerLN`, `MachineDefines pickByteH`, `ChildBnd` | run boundary: they stay premises |
| `hftByte` | `hftByte.machine_design_svH_full` (+ `_closed`) — by hand (`OneOutHftByteTest`) OR by `#machine_oneout_any` (same exclusion) | A₁ | WRITTEN — pending build |
| | | A₂ | WRITTEN — pending build |
| | | A₃ | WRITTEN — pending build |
| | | A₄ | WRITTEN — pending build |
| | | `hr`, `MachineDefines hftByte`, `MachineDefines httpGetByte`, `ChildBnd` | run boundary: they stay premises |
| `callerL` | `callerL.machine_design_svH_full` (BUILT at 85ebb9fd by hand) | A₁–A₄ | already absent (BUILT, §12). This round only re-derives the statement from GENERATED lemmas (`callerL.machine_design_svH_full_gen`): WRITTEN — pending build; nothing more is removed |
| `callerMix` | `callerMix.machine_design_svH_full` (BUILT, `#machine_oneout`) | A₁–A₄ | already absent (BUILT). This round only compares the new generator's gate branch with the existing constants: WRITTEN — pending build |

Predicted log lines (classes asserted by the commands; numerals are
predictions, the commands print the computed ones):

    Tests/Compiler/OneOutCallerLNTest.lean
      SVHFULL GENERATED [callerLN.machine_design_svH_full, callerLN.machine_design_svH_full_closed]: …
      ONEOUT FULL PREMISE callerLN.machine_design_svH_full_closed: run | binder hr : RunsTo (synthesizeCombinational `callerLN) …
      ONEOUT FULL PREMISE …_closed: reflection | binder entry : MachineDefines … `callerLN callerLN.machineData.shape
      ONEOUT FULL PREMISE …_closed: reflection | binder hR0 : MachineDefines … `pickByteH pickByteH.machineData.shape
      ONEOUT FULL PREMISE …_closed: ChildBnd | antecedent under the existentials : ChildBnd mref cref w
      ONEOUT FULL PREMISE …_closed: reflection | antecedent under the existentials : MachineDefines … `pickByteH …
      GOALGAP callerLN.machine_design_svH_full_closed_gap from … (none NOT ALLOWED)
      ONEOUT MACHINE-LEAF callerLN: … other: NONE … Machine-route callees …: [pickByteH]; gate callees …: [] …
    Tests/Compiler/OneOutHftByteTest.lean
      ONEOUT DATA hftByte: nDecl=2 nIn=3 slots=… lets=… insts=[httpGetByte args(let indices)=[…]] instFields=[] outs=[out:8] binders(width or dom)=[8, 1, 8, …]
      ONEOUT DATA httpGetByte: nDecl=2 nIn=2 slots=0 lets=12 insts=[] instFields=[] outs=[out:8] binders(width or dom)=[dom, 6, 8, …]
      SVHFULL GENERATED [hftByte.machine_design_svH_full, hftByte.machine_design_svH_full_closed]: …
      (the same five non-data premise lines with hftByte / httpGetByte)
      ONEOUT MACHINE-LEAF hftByte: … other: NONE …
    Tests/Compiler/OneOutAnyFamilyTest.lean
      ONEOUT ANY callerL: PRESENT [callerL.machine_design_svH_full, …_closed] — already present, statement verified against the generated lemmas …; the existing constant is recorded as built from OTHER lemmas (…callerL_factsH…); the proof rebuilt now from the generated lemmas is kernel-checked as callerL.machine_design_svH_full_gen …; callees: machine leaves [pickByteH] …, gate children [] …; … callArgsOk with callerL.oneout_kidIns = [[16, 2]] … [8]
      ONEOUT ANY FAMILY callerL: … The endpoint existed (hand lemmas) …
      ONEOUT ANY callerLN: GENERATED [callerLN.machine_design_svH_full, …_closed] — … callerLN.oneout_kidIns = [[16, 2]] … [8]
      ONEOUT ANY FAMILY callerLN: … goal gap callerLN.machine_design_svH_full_closed_gap: … none NOT ALLOWED …
      ONEOUT ANY hftByte: GENERATED [hftByte.machine_design_svH_full, …_closed] — … hftByte.oneout_kidIns = [[6]] … [8]
      ONEOUT ANY FAMILY hftByte: …
      ONEOUT ANY callerMix: PRESENT [callerMix.machine_design_svH_full, …_closed] — already present, statement verified against the generated lemmas …, recorded lemmas equal …
      ONEOUT ANY FAMILY callerMix: … gate callees (premise: EntryDefines): [pick, pickD] …
      ONEOUT ANY callerInner: REFUSED (no …callerInner.machine_ships_hierHR: run #machine_design_svHR … first)
      ONEOUT ANY FAMILY: …callerInner REFUSED, nothing left under its names.

A FAILED outcome is `ONEOUT ANY f: FAILED (data condition … [the theorem's
name]: …)` followed by the command's error (expected GENERATED); in a hand
test it is the error of the named theorem (`hftByte_callArgs`,
`httpGetByte_outChars`, …).

### 13.2 `callerLN`: what is new against `callerL`

Source: `let s := counterB en` (a sub-machine with one register),
`let acc ← Signal.reg 0#16`, `acc <~ accS ^^^ w`, `return pickByteH accS s`.
By reading: `nDecl = 2` (`w`, `en`); registers `acc` and the flattened
`counterB`'s; one entry whose callee is `pickByteH`; `instFields = []`;
output `out : BitVec 8`.

No new general theorem and no new fact about the child: `pickByteH_leaf` and
the seven `pickByteH_*` theorems of `OneOutCallerLTest` (BUILT) are reused.
New: the parent's data conditions at `nDecl = 2`, each named —
`callerLN_callsOk`, `_slotLen`, `_domB`, `_insts`, `_instFields`, `_outTy`,
`_nomem`, `_slots`, `_outChars`, `_outScalar`, `_entries`, `_strict`,
`_callArgs`. So more than "three new `decide`s" (§12.3 counted only the
ones whose STATEMENT mentions `nDecl`'s new value and the child); all of
them are decided again on `callerLN.machineData`.

One difference of FORM from `callerL`'s hand instance: the per-entry facts
are not `cases k` against a literal count; `callerLN_entries` (`∀ k (hk :
k < insts.length), (insts[k]).1 = pickByteH`) is decided and rewritten with.

### 13.3 `hftByte`: what was read, and which conditions are open

The table of the reading is the header of
`Tests/Compiler/OneOutHftByteTest.lean`; in short:

* register: YES by reading (`hftStrategy`'s `cntR`; the parser's and the
  emitter's registers are slots of the flattened machine);
* `nDecl`: 2 by reading (`readMachine`: the binders peeled off the entry;
  no domain binder). The test does not write the literal: `hftNDecl := nIn -
  insts.length`, the only value `callsOk`'s first conjunct allows; the
  reader's number is logged (`ONEOUT DATA`);
* entries: one, callee `httpGetByte`, by reading; `instFields = []` follows
  from the BUILT `gateCallsOk` decide inside `hftByte.machine_closes_at`;
* `hftByte.machine_design_svHR`: exists (BUILT), from the head
  `machine_ships_hierHC` like every `…HR`; `hftByte.machine_closes_at` has
  the one premise `MachineDefines httpGetByte`;
* the child's `SlotlessLeaf` fields: `gate` (`gateCallsOk nIn`), `lets ≠ 0`,
  `slots = []`, the one output `out`, `outTy` are the SAME decides as in the
  BUILT `hftByte.machine_closes_at` (there at the reader's `nDecl`, which is
  `nIn` for a child without calls) — plausible. `calls`, `dom`, `ss` are
  conjuncts of `gate` (`gateCallsOk_parts`, WRITTEN) — plausible, and they
  cost no second evaluation. `insts = []` is checked by compiled code in
  `closesAtCore` and is `rfl` on a literal — plausible. OPEN (never decided
  for this declaration): `outChars` (`charOk` on the characters of `out`),
  `outScalar`. The implicit domain binder is the FIRST binder, inside the
  first `nIn`, so `dom` (no domain binder after `nIn`) is expected true and
  `declWidths` filters it: `kidIns = [6]`.
* OPEN on the parent: `hftByte_slots`, `_outTy`, `_outChars`, `_outScalar`,
  `_entries`, `_strict` (result binder 8 = `out`'s 8), `_callArgs` (the
  argument `let`'s width 6) — expected true by reading, never decided.
  `hftByte_callsOk`, `_slotLen`, `_domB`, `_instFields`, `_nomem` are
  conjuncts / arguments of decides of the BUILT `machine_closes_at`.

Kernel cost: `httpGetByte_gate` and `hftByte_callsOk` walk whole terms
(`fieldsOkB`, `reads` over every `let` field and the core) — both were
decided once in the BUILT `machine_closes_at` at the default recursion
depth; the others touch binder / entry lists but must reduce the
`machineData` constants. Every decide is `first | decide | decide +kernel`
under `maxRecDepth 100000`. A failure is a failed NAMED condition
(`httpGetByte_<cond>`, `hftByte_<cond>`), not a false theorem.

### 13.4 The generator `#machine_oneout_any`

`#machine_oneout` with one more callee kind. Reuses (imports, does not
copy) `emit`, `emitOrVerify`, `mkThm`, `perEntry`, `endpoint` of
`Tools/ShippingOneOutGenCommand.lean`; the scope test and the generation are
written again, the gate branch copied.

* Callee kind: `c.gate_peel` present ⇒ gate child (the test of
  `closesAtCore`); else `c.machineData` present ⇒ machine child, accepted
  only as a SLOTLESS LEAF with the one output `out`, at least one `let`, and
  `c.machine_closes` present.
* REFUSED with the reason, NOT COVERED: a machine callee WITH a register; a
  machine callee with calls of its own; no `let`; outputs other than
  `[out]`; no `c.machine_closes`; and everything `#machine_oneout` refuses
  (no `…HR`, no call, a slotless parent, `instFields ≠ []`, a memory
  callee). In the tests a parent of a register child is refused EARLIER
  (`instFields ≠ []` or no `…HR`), so the machine-callee refusals have no
  test.
* Per machine-leaf callee: `c.leaf_gate`, `_calls`, `_dom`, `_ss`, `_insts`,
  `_outTy`, `_outChars`, `_outScalar`, `_lets`, `_slots`, `_one`, `_outW`
  (each a named theorem by the kernel), and `c.leaf_slotless :
  MachineDefines … c c.machineData.shape → SlotlessLeaf … c c.machineData`.
* `hkidW` per entry: `leaf_outWidth` (WRITTEN: from `SlotlessLeaf.outTys`
  and `c.leaf_outW`) composed with the entry's result-binder width — NOT
  `hkidW_one` + `callWidthsStrict` as in the hand instances, because with
  several callees the one `kidOuts` function would have to be stated over
  all entries. Same conclusion; the data condition is `c.leaf_outW` and the
  third conjunct of `f.oneout_entries` instead of `callWidthsStrict`.
* `f.oneout_entries`: the alternative of a machine leaf compares
  `f.oneout_kidIns k` with `declWidths c.machineData`.
* MIXED parents (one gate callee and one machine-leaf callee) are in the
  design — the per-entry split is by callee, each case of its own kind —
  but NO test declaration has that shape: that combination has never been
  elaborated.

Name clash (not hidden): the generator and the two hand instances add the
same `f.machine_design_svH_full`. `OneOutAnyFamilyTest` imports only
`OneOutCallerLTest` (already in `Tests.AllTests`), so `callerL` goes
through the compare path (PRESENT) and `callerLN`, `hftByte` are GENERATED.
`OneOutCallerLNTest` and `OneOutHftByteTest` are then TARGET-BUILT only (a
module importing them and the family test does not load). The alternative
(hand instances in `AllTests`): import them in the family test and expect
PRESENT three times.

### 13.5 Scope sentence (binding)

For ONE declaration each — `callerLN`, `hftByte`: a parent WITH a register,
one call entry of a SLOTLESS LEAF MACHINE child with the one output `out`,
the one-output closing — `f.machine_design_svH_full_closed` is WRITTEN to
have none of the four check premises of `f.machine_design_svHR`, GIVEN (1)
the per-declaration data conditions of §13.2 / §13.3 (decided, not
removed); (2) the runtime boundary, which stays premises: the run,
`MachineDefines f`, `MachineDefines` of the child, `ChildBnd`; (3) the
compiler's guards with fallback (`checkedOptimize`, `deinline`,
`closeInsts`' checks, `mergeChecked`'s validation of the child's merge);
and the conclusion is (4) about `DesignSV (childMap D.modules) 0
(checkedOptimize b)` — the module list, not the SV string, not `#sim`. NOT
covered: slotless PARENTS, machine children with registers or calls,
several outputs, mixed gate / machine-leaf parents (no instance), "all
successful inputs". "The parent has a register" (`f…_slots`, the head) and
"the child's kind" (`SlotlessLeaf`) are separate conditions.

### 13.6 Paper only: the next axis — a parent WITHOUT a register (still one-output, combinational children)

Nothing below is written as Lean, built or measured; NO statement about
slotless parents is claimed.

**(a) What the head needs `"rst" ∈ b.inputs` for.** In
`machine_ships_hierHC` (`Tools/ShippingMachineShipsHierH.lean`) and its
check-free copy `machine_design_svH_free` (`Tools/ShippingOneOutHead.lean`,
`hF.rst`), `hrstIn` is used in exactly two places:

1. to turn the conclusion's premise `∀ t, ins t "rst" = 0` into
   `∀ t st, seedIn b ins t st "rst" = 0` — the reset premise of the composed
   theorem (`ComposedH`: `∀ t st, seed t st "rst" = 0`, for the seed
   `seedIn b ins`). `seedIn m ins t st n = if n ∈ m.inputs then ins t n else
   st n`: with `rst` an input the value comes from the stream;
2. as an argument of `hierRefineCheck_linkedH` (the optimizer's accepted
   candidate has the same outputs on the linked run), which passes it to the
   flat `seqOptCheck_run_sound` (`Tools/ShippingSeqOptSoundness.lean`:
   `hrstIn`, `hrstZ` — the registers of the flattened module do not reset
   during the run).

`core_rst_any` derives it from the parent's register (`hsl : slots ≠ []`):
the wiring's input clause is `ports ++ (if no slot then [] else [clk, rst])
++ extra`.

**(b) A slotless parent of combinational children has no `rst` input** (the
same clause, read in `Tools/ShippingChecksRaw.lean`'s header: `extra = [clk,
rst]` only when some child has a clock / reset input). Consequences, by
reading:

* `hierCheck`'s last conjunct is `(b.inputs.map (·.name)).contains "rst"`,
  and `shipsHierHCheck = hierCheck && kidsLocal && hierTyped`. So for such a
  parent `shipsHierHCheck D.modules b = false`: the EXISTING head
  `machine_ships_hierHC`, and any `f.machine_design_svHR` built from it,
  would be VACUOUS (its first check premise cannot hold). The header of
  `Tools/ShippingChecksRaw.lean` says such parents "ship by the
  combinational route `shipsHierHCheck`, which does not ask it" — that
  sentence does not match the definition as it is now (the conjunct is in
  `hierCheck`, which `shipsHierHCheck` contains). Not evaluated on any
  module; a reading of two definitions.
* The composed theorem's premise `∀ t st, seedIn b ins t st "rst" = 0` is
  FALSE when `rst` is not an input (`seedIn` then reads the state: take a
  state with `st "rst" = 1`). So the head cannot be instantiated with the
  seed `seedIn b ins` at all; this is not a missing derivation of a check,
  it is the statement.

**(c) Does a slotless parent of combinational children have an `…HR`
endpoint today?** In the tests, NO: every declaration given to
`#machine_design_svHR` / `#machine_ships_hierH` has a register (`caller`,
`callerTwice`, `callerNested`, `callerD`, `callerMix`, `callerRep`,
`callerABA`, `callerL`, `callerLN`, `hftByte`, `midH`). The three parents
the earlier sweep (`NoPortsSweepTest` over `HierBindsCensusTest.candidates`)
refused as "parent without a register" are
`Sparkle.Tests.Compiler.MultiInstance.engineOnce`, `twinCalls`, `mesh2x2`:
slotless parents of `pe`, a SEQUENTIAL child (two registers) with TWO
outputs (`aOut`, `pOut`). They are NOT instances of this axis: their
closing is `closeInstsG` (`instFields ≠ []`), their module gets `clk` /
`rst` from the child (`withClockFor`), and their endpoints are the
sequential head's (`f.machine_ships_hier`, `shipsHierCheck`, "a reset port"
evaluated true on the real modules). So there is NO real declaration in the
tests that is a slotless parent of one-output combinational children on the
machine route with a hierarchical endpoint; the commands that exist for a
slotless machine are `#machine_endpoint`, `#machine_child`, and the
combinational head `machine_ships_comb`, which asks `insts = []` (no call).
`machineClosesAt_of_gateKids` (the one-output closing's derivation) has no
condition on the slots, but `closesAtCore` was never run on such a parent
in the tests. (Which three the sweep refused is identified from the
candidate list and the sources — `pe` has two `Signal.reg`, the three
parents none; the sweep's own log line was not found in `docs/`.)

**(d) What the head's statement would be without `rst`.** The conclusion of
the present head, for the seed `seedIn b ins`, has the premises
`∀ t st r, r ∈ regs → seedIn b ins t st r = st r`, `∀ t, ins t "rst" = 0`,
the slots' initial values, the calls, the input fits, `BoundOff`, the
register fits. For a slotless parent `regs = []` (`regs.length =
d.ss.length = 0`) and there is no register: the pass-through, initial-value
and register-fit premises are vacuous, and `∀ t, ins t "rst" = 0`
constrains a stream at a name that is not an input — satisfiable by any
caller but MEANINGLESS (nothing reads `ins t "rst"`). What the proof needs
instead is one of:

  (i) a composed theorem for `d.ss = []` WITHOUT the reset premise (no
      register step reads `rst`; the trace is a sequence of independent
      combinational evaluations over the children's combinational
      evaluations), and an optimizer lemma for the linked run without
      `hrstIn` when the flattened module has no register
      (`seqRegs (openFlat b …) = []`); or
  (ii) the present theorems with the premise replaced by "`rst` is an input
      and the stream holds it low, OR no register and no child reads `rst`".

Neither exists. (i) is the honest statement: the conclusion would not
mention `rst` at all.

**(e) Precisely what is missing** (each is an absent theorem or an absent
instance; none was attempted):

1. a REAL declaration: a slotless parent with at least one one-output
   combinational `@[hardware_module]` call that the machine route compiles
   (`MachineData` with `slots = []`, `insts ≠ []`, `instFields = []`), with
   `#machine_endpoint`, a closing (`#machine_closes_at`) and a composed
   endpoint. Whether `#machine_linked` / `#machine_composed` /
   `#machine_design_svHR` accept such a parent was not read to the end;
2. a head: `machine_ships_hierHC`'s statement with the reset premise
   removed for `d.shape.layout.slots = []`, i.e. `ComposedH` without
   `∀ t st, seed t st "rst" = 0` for slotless data;
3. the optimizer step without `hrstIn`: `hierRefineCheck_linkedH` /
   `seqOptCheck_run_sound` for a flattened module without registers;
4. `hierCheck` / `HierFacts` without the `rst` conjunct for that head (or a
   separate checker), then `RunFactsH` without `rst`
   (`core_runFactsH` takes `hsl` only for `core_rst_any`; its other fields
   — `binds`, `wfO`, `ndB`, `ndO`, `nofb`, `outs` — are stated for any
   machine with calls, to be re-read for `slots = []`);
5. `core_designCheckH` asks `hsl` as well (through `RunFactsH`); the
   `DesignSV` conclusion (`ships_design_svH_all`) carries
   `∀ t, ins t "rst" = 0` as a premise of the emitted-text run — to be
   restated the same way.

"The parent has no register" is an axis of the HEAD (items 2–5); the
children's kind (gate / slotless machine leaf) is unchanged and the
child-side theorems of §4 / §12.2 do not mention the parent's slots.

### 13.7 UNVERIFIED (par/a-11), in risk order

1. `Tools/ShippingOneOutAnyGenCommand.lean` — never elaborated: the
   selective `open … (Outcome emit emitOrVerify mkThm perEntry endpoint)`;
   the structure-instance quotation of `c.leaf_slotless`; `⟨_, rfl, rfl⟩` as
   a standalone theorem body (`c.leaf_one`); the leaf tactics
   (`($(ls i) $(hR i)).kidA hy` etc., `leaf_outWidth … hy p hp`); the
   mixed-kind `perEntry` (no instance).
2. The kernel decides on `hftByte.machineData` /
   `httpGetByte.machineData`: `hftByte_callArgs`, `_strict`, `_entries`,
   `_slots`, `_out*`; `httpGetByte_outChars`, `_outScalar` (never decided
   before); `declWidths httpGetByte.machineData = [6]` against the parent's
   computed `oneout_kidIns` (generator) — true only if the reading is right.
3. `Tools/ShippingLeafOneOutGen.lean`: `gateCallsOk_parts` (`simp only
   [gateCallsOk, Bool.and_eq_true] at h`, the shape of the four conjuncts),
   `leaf_outWidth` (`rw [← e]` then `exact hW o ho` by projection of a
   structure literal).
4. `callerLN`: `callerLN_callArgs` (register `acc` and the sub-machine's
   result as arguments), `callerLN_strict`; `rw [callerLN_entries k hk] at
   hy` (the `getElem` proof term in `hy`).
5. The compare paths of the family test: `callerL` (statement rebuilt from
   generated lemmas `isDefEq` the hand-built one; `_gen` added), `callerMix`
   (every statement of the copied gate branch `isDefEq` `#machine_oneout`'s),
   `pickByteH.leaf_*` re-derived for `callerLN`.
6. `Tests/Compiler/OneOutLeafAudit.lean`: meta code only (a copy of the
   BUILT `run_cmd` with arguments).
7. `hftNDecl` as a `noncomputable def` inside statements (`binders[hftNDecl
   + k]?`, `(nDecl := hftNDecl)`): unification of the implicit `nDecl`.
8. The reading of §13.6 (two definitions and one header compared; nothing
   evaluated).

### 13.8 Build queue (par/a-11)

1. `Tools.ShippingLeafOneOutGen`
2. `Tools.ShippingOneOutAnyGenCommand`
3. `Tests.Compiler.OneOutLeafAudit`
4. `Tests.Compiler.OneOutCallerLNTest` (target only; see the name clash)
5. `Tests.Compiler.OneOutHftByteTest` (target only)
6. `Tests.Compiler.OneOutAnyFamilyTest`

4, 5, 6 are independent of each other (4 needs 3; 5 needs 1 and 3; 6 needs
1–3). `lakefile.lean` (integrator):

    lean_lib «Tools.ShippingLeafOneOutGen» where
      roots := #[`Tools.ShippingLeafOneOutGen]
    lean_lib «Tools.ShippingOneOutAnyGenCommand» where
      roots := #[`Tools.ShippingOneOutAnyGenCommand]

`Tests/AllTests.lean` (integrator) — ONE of the two, not both:

    import Tests.Compiler.OneOutAnyFamilyTest
    -- or (then edit the family test as its header says):
    -- import Tests.Compiler.OneOutCallerLNTest
    -- import Tests.Compiler.OneOutHftByteTest

## 14. par/a-12: `midH` — a one-output parent that §10 left out

Branch `par/a-12` (base poc fdd69046, where §13 is BUILT). WRITTEN, NOT
BUILT: `Tests/Compiler/OneOutMidHTest.lean`. The census of everything that
still carries a check premise, the ranked next units and the two other
files of this round (`NoPortsTwoTest`, `RemainingProbeTest`) are in
`docs/parallel/A-remaining.md`.

§10's table lists the one-output parents with a register and gate children
and omits `midH` (`ShippingMachineDepthHTest`): a register, ONE call entry
of the gate child `rcH`, a call result of one `Signal (BitVec 8)`
(`instFields = []`), `midH.machine_design_svHR` and
`midH.machine_closes_at` BUILT. It was read as "a child of `grandH`" and
never as an entry. By reading, no refusal line of `#machine_oneout`'s scope
test applies; what is new against §11 / §12 is that the PARENT has two
outputs of its own (`n`, `hit : Bool`) and is itself a domain-polymorphic
`@[hardware_module]`.

| declaration | endpoint | premise of `midH.machine_design_svHR` | state |
|---|---|---|---|
| `midH` | `midH.machine_design_svH_full` (+ `_closed`), by `#machine_oneout` | A₁ `shipsHierHCheck D.modules b` | WRITTEN (the test; the generator is built) — predicted absent, pending build |
| | | A₂ `kidsComb D.modules (checkedOptimize b).body` | predicted absent, pending build |
| | | A₃ `designCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | | A₄ `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | | `hr`, `MachineDefines midH`, `EntryDefines rcH`, `ChildBnd` | run boundary: they stay premises |

Scope sentence: that of §11.4 with `midH` / `rcH`. In addition, binding:
the endpoint is about `midH` AS AN ENTRY. It removes NO premise of
`grandH.machine_design_svNR1/2`, `mixD1.…NR1/2`, `topD2.…NR2/3`,
`mixDeep.…NR2`, whose check premises are about the parent's module and ask
the child's facts of the module the child cache serves
(`RealChild mref cref midH y`) — unit U2 of `A-remaining.md`, not written.

UNVERIFIED: `midH.oneout_callArgs`, `_entries`, `_outChars`, `_outScalar`
(never decided); the generated lemmas on a parent with two outputs (read:
no hypothesis of `core_runFactsH`, `core_portsMatch_raw₁`, `core_hierTyped₁`,
`core_designCheckH`, `core_outsCheck_all_gate` asks one output of the
parent; never elaborated with two).

# Shipping compiler: the retained trust base

The CompCert-style theorems in `Tools/Shipping*` prove compiled artifacts
against the source `Signal` semantics. This file states, in one place,
everything the claim RETAINS rather than proves: what is assumed, where
it enters formally, and what would discharge it. Nothing here is hidden
inside a proof — every item is a hypothesis of a theorem, a gate the test
suite evaluates, a definition that carries meaning, or an explicit
statement that something is outside every theorem.

Read it together with
[ShippingCompiler-Coverage.md](ShippingCompiler-Coverage.md), which says
WHICH compiles the theorems apply to. The short version: the theorems
are conditional on a syntactic gate, and on the measured corpus most
real designs do not pass it (§7).

## 1. The logical base

Every theorem is checked by the Lean 4 kernel and audited in the test
suite (`collectAxioms`) to depend only on `propext`, `Classical.choice`
and `Quot.sound`. `sorryAx`, `ofReduceBool` / `native_decide` and custom
axioms are rejected by the audits.

## 2. Run-environment boundaries

The theorems are stated over the ACTUAL `MetaM` run of the compiler
(`RunsTo`, `MReturns`). What a run reads from Lean's environment or from
mutable references cannot be derived inside the logic, so each such read
that a proof depends on is a named hypothesis. All of them have the same
form: *every* read of that kind in this run returns the stated value.

| Boundary | Says | Used by |
| --- | --- | --- |
| `EnvDefines … declName v` | every `getConstInfo declName` of the run returns a definition whose value is `v` | every entry endpoint |
| `EntryDefines … declName v` | the constant the entry hands on — `entryConst` of the declaration and the environment the run reads — is a definition with value `v`. For a gate-accepted declaration this IS `EnvDefines` (`EntryDefines.of_env`); for an unfolded one it is `EnvDefines` plus what the run's environment unfolds the value to (`EntryDefines.of_inline`) | `_of_entry` endpoints (helper-structured declarations) |
| `MachineDefines … declName shape` | the entry constant of the declaration — `entryConst` of the declaration and the environment the run reads — is refused by both shape gates and IS the machine `shape` (`machineShape?`, with the structure facts — field accessors, constructors and field kinds: `structEnv` — of the environment the run reads). The suite computes the same `machineShape?` on the real declaration and compares binders, layout and (reflected) body | machine endpoints (`synthesizeCombinationalCore_machine_sound`, `mThree_execution`, `lin_execution`) |
| `MachineCloses … declName shape` | every machine synthesis of `shape` in this run ties the `let` ports to their fields (`closeLets` accepts the transition module the run compiled: the operand wires are found, declared at the ports' widths, and the statements are in dependency order), so the run does not fall back to the legacy route. PROVED for a shape without `let`s (`machineCloses_of_noLets`); for a shape with `let`s the suite runs the real `synthesizeMachineCertified` and checks it returns a module | machine endpoints of shapes with `let`s (`lin_execution`) |
| the declaration's type is one scalar Signal (`mixedGateResultScalar`) | `EnvDefines` pins the value, not the type; the suite checks it on the real declaration | instance and cone endpoints |
| tag fact at the entry (`RunsTo getEnv … → isHardwareModule e mn`) | the environment the gate predicate is built from tags the child | instance, projection and cone endpoints |
| `HardwareTagged mn` | every environment the instance arm reads tags `mn` | instance contracts |
| `SubSynthDefines mn mc dc` | the nested child synthesis the arm performs returns `(mc, dc)` | root instance contracts |
| `SubSynthDefinesAll mn mc dc` | the same at every recursion fuel (inside a cone the arm runs below the entry fuel) | cone-leaf contract |
| `ProjEnvDefines pn structName cn` | the projection function is not itself tagged, is a projection of `structName`, and the record call's head is tagged | projection contract |
| `ProjFieldDefines pn structName field` | the arm's field-name resolution returns `field` | projection contract |
| `OutCacheEmpty` | every read of the multi-output port map comes back empty | projection contract |

Not boundaries any more: the single-out instance cache (a hit is honoured
only when the builder's own `translateRecord` names the same expression,
so no premise about the mutable cache is needed), and the expression
cache (validated the same way since S2). `OutCacheEmpty` is stronger
than what the projection arm needs — it only queries the keys of the
call at hand — and is false when the child itself instantiates
multi-output modules; narrowing it to those keys is open.

## 3. Premises about a linked child

The hierarchical statements speak about a parent whose instance
statements are executed against a table of children. Three premises are
about that table, not about the run:

- `children mc.name = some (mc, cwe)`: the table holds the pinned child
  under its module name. The suite checks `d.modules` on the real
  compiles; deriving the registration from the run is open, and needs a
  no-collision fact about module names (they come from declaration
  names).
- `ChildCorrect mn mc cwe out`: the pinned child's body computes the
  child's source function. A statement about one fixed module — proved
  outright for the test child; in general it is the child's own
  certified endpoint.
- `ChildOutsBounded children mems`: each child output fits its port
  width. Likewise a fact about fixed modules.

## 4. Decidable gates evaluated by the suite

Several theorems take decidable premises about the pipeline's artifacts.
The division of labour is deliberate: a theorem quantifies over any
artifacts satisfying the premise; a `throwError` gate in the suite
evaluates the premise on what the pipeline actually produced in this
build. A gate failure fails `Tests.AllTests`.

| Gate | Validates | Evaluated on |
| --- | --- | --- |
| `seqOptCheck m o` | the sequential merge and the optimizer on assign/register bodies | every certified register shape |
| `optCheck (openFlat m …) (openFlat o …)`, `instsKept`, `connAgreeOk` | the optimizer on instance-bearing bodies (interface extraction) | three hierarchical parents |
| `seqCheck` / `seqCheckM`, width agreement | the emitted-SV semantic layer applies | register, memory and hierarchical capstones |
| `semFragCheck`, `bodyImage`, `bodyReorderCheck`, fragment membership of the parsed body | the parsed-back text is the checked module up to reordering; the gates run the REAL parser on the REAL printed bytes | the same capstones |
| `linkedWF`, `instOutWidthsOk` | the linked/open bridge applies; instance outputs sit at their port widths | hierarchical capstones |
| post-processing identity (`mFull.body = mr.body`) | cleanup and merge leave the certified body unchanged | memory shapes, hierarchical parent |
| byte parity with the legacy front end | the certified front end emits exactly what the legacy one does | every family, including instances, projections, cones and pipelines |
| pinned child modules (`cm == childModule`) | the literal module a premise names IS the compiled child, name included | hierarchy tests |

`checkedOptimize` itself only checks assignment-only bodies whose
right-hand sides are all of a known shape (`simpleBody`): there the
optimised module ships only if the proved checker accepts it, and the
unoptimised input ships otherwise — which is always the case for a body
containing a part-select or a concatenation of two wires, since the
checker's normal form covers neither. On an assignment-only body with
an unknown right-hand side (a wider concatenation, a general slice
operand), and on
memories and instances the shipping pipeline keeps the optimizer's
output unchecked at run time. For those shapes the validation is exactly
the gates above: an optimizer change that broke one would fail the suite
rather than silently ship, but a compile the suite never ran is not
checked. On ASSIGN + REGISTER modules IN THE NORMAL FORMS
(`RefineCheck.seqGate` and `refineCheck m m`: every output and next
value normalises over the inputs and registers) both the duplicate merge
of the full entry (`mergeChecked`) and the optimizer (`checkedOptimize`)
are checked at run time by `refineCheck`, proved sound
(`refineCheck_transfer`): the merged / optimised module ships only if
accepted, the unmerged / unoptimised one otherwise. For these modules the
printed text is therefore a proved refinement of the core module in EVERY
compile, not only the suite's. A sequential module outside the normal
forms (legacy modules whose assigns reference wires defined later, forms
the normaliser does not know) keeps the unchecked passes, so the gate
changes no emitted text there.

## 5. Definitions that carry the meaning

The theorems relate these definitions. They are specifications, not
theorems, and reading them is part of trusting the claim.

- The source: `Signal`, its operators, and `Signal.val` at a cycle.
- The front-end unfolding: `inlineDefs` / `userInliner` (delta-beta of
  user definitions, projection of a constructor, zeta in front of it,
  `<$>`/`<*>` at the library's Signal instances as `Signal.map`/
  `Signal.ap`, literal `Nat` sums folded — `8 + 4` in a type argument
  becomes `12`) and the choice `entryConst`. The theorems do not reason about the unfolding — they
  speak about the value the entry constant HAS. That this value means
  what the declaration means is Lean's own delta/beta, and it is checked
  per declaration by the kernel: the test theorems identify the
  declaration, helpers and all, with the denotation of the quoted
  unfolded term by `rfl` (`useSel_library`, `oddParity_library`,
  `rcon_library`). Which definitions are
  unfolded (`userDefinition?`) only decides which declarations reach a
  certified front end; a wrong choice there cannot make a theorem false.
- The normal forms of the machine route: `machNorm` (other spellings of
  accepted hardware rewritten to the accepted one) and `kernelNat`, which
  reads the value of a constant computed in Lean with the kernel's own
  reduction (`Lean.Kernel.whnf` on a closed `Nat` term). Like the
  unfolding, they are not reasoned about: the theorems speak about the
  transition the run computed. That the normalised transition means what
  the declaration AS WRITTEN means is checked per declaration by the
  kernel — the generated endpoint compares the written body with the
  terms read off the normalised one (`f.machine_writes`,
  `f.machine_result`), and a constant with its literal by evaluating
  both. A wrong rewrite or a wrong value therefore cannot make a theorem
  false; without the endpoint of a declaration, its module rests on the
  rewrite rules being right, as with every dispatch arm.
- The IR semantics: `evalExpr`, `evalAssigns`, `stepModule`,
  `runModule` (`Sparkle/IR/Semantics.lean`). Instance statements are
  no-ops here: the open-module view.
- The linked meaning of an instance: `evalAssignsH` — the child's
  outputs are the standard evaluation of its body on the
  connection-fed environment, one level deep — and its order-free form
  `Consistent` (each instance's outputs equal its child's evaluation on
  what the instance reads). That this is what a SystemVerilog module
  instantiation means is retained. Its width side condition is no
  longer retained: every emitted instance is checked, and proved, to
  join equal widths (`instLinkCheck`, `Linked`, `InstsLinked`).
- The syntax view `view` (`Tools/ShippingUnifiedMeaning.lean`): which
  Lean expression counts as which operator node. It maps the
  applicative form `Signal.ap (Signal.map (fun x y => op x y) a) b` to
  the node of `op` on `a` and `b` — the pointwise reading of `<$>`/`<*>`
  on `Signal`; the kernel `rfl` bridge of each declaration checks that
  reading against the library's definitions. Likewise a `Signal.map`
  whose function is `BitVec.extractLsb' start len` is the slice node,
  with `BitVec.extractLsb'` itself as its meaning (`fc_library`), and
  `a ++ b` at the library's Signal instance is the concatenation node,
  with `BitVec` append as its meaning (`cSwap_library`).
- The emitted-SV semantics (`Tools/SVParser/EmitSem.lean`): continuous
  assignments, the always-block register shape, memories. An
  independent reading of the SystemVerilog subset the printer emits.
- The reader: the shipping parser and lowering
  (`Tools/SVParser/Parser.lean`, `Lower.lean`). The byte-level
  statements run in the PARSE direction — the module read back from
  the printed text is proved trace-equal to the checked module — so the
  parser is trusted as a reader of text. Combinational modules also
  have the render direction (`printedModule_render`); for sequential
  text it is blocked on the SV AST, whose sensitivity lists cannot
  carry an asynchronous reset.

## 6. What the hierarchical statements do and do not say

For a hierarchical parent the printed-text statements are in the
open-module view under the ORACLE SEEDING: instance-output wires start
at the values the linked semantics gives them, and `Consistent` says
those values are the children's. This is a statement about the PARENT
module's text. Not yet covered: the design-level text (children printed
alongside the parent), children that are themselves sequential (the
bridge is combinational; the per-cycle linked run `runH` is proved only
at the IR level), and children that themselves instantiate.

## 6b. What the machine statements do and do not say

A machine endpoint is about the module `synthesizeCombinationalCore`
returns (the raw module), run by the IR semantics with RESET LOW from a
state in which the registers hold the slots' values: every cycle's output
port (`out`, or one port per field of a structure result) is the source
declaration's value at that time. Reset behaviour itself
is not modelled (as for the single-register family): the registers'
reset VALUES and reset KIND (synchronous in `defaultDomain`,
asynchronous for a domain binder) are emitted by `closeMachine` and
checked on the emitted module by the suite, not proved against a source
semantics of reset. The unfolding and the reading of the transition
(`userInliner`, `machineShape?`) are not reasoned about either: the
theorems speak about the shape the run computed (`MachineDefines`), and
that this transition means what the SOURCE means is proved per
declaration by the kernel — the source's state recurrence
(`circuit_state`) against the evaluation of the quoted term; for a shape
with hardware `let`s the declaration also proves that the source's own
`let` values satisfy the transition's `let` equations (`LetsHold`).
For a GENERATED endpoint (`#machine_endpoint f`, `f.machine_sound`) the
same holds with nothing written by hand, and nothing added to the base:
the command's reader of the body (`unq`) and its construction of the
data are not trusted — the kernel checks that the body is the quotation
of the terms (`f.machine_body`), evaluates the one Boolean that decides
every side condition (`f.machine_ok`; by reduction, not `native_decide`),
and checks by `Eq.refl` that the declaration's own reset values, pending
writes and result are the terms' (`f.machine_inits`, `f.machine_writes`,
`f.machine_result`, `f.machine_source`). A declaration with sub-machines
goes through `machine_trace_of_nested` instead: the same checks, with the
enclosing body written over the tuple of the sub-machines' results and
each sub-machine's body over the enclosing handles (both read off the
declaration and checked by the kernel: the declaration IS that body on
the loops, `f.machine_source`); the generic fact that the loops together
are the flattened machine's state stream is proved (`fused_state`,
ShippingMachineFuse), not assumed. A declaration whose body CALLS a
combinational `@[hardware_module]` is a machine whose transition reads the
call's output as an input and whose emitted module ties that input to an
INSTANCE of the child (`closeInsts`); its `f.machine_sound` is stated with
the inputs at the calls' positions being the calls themselves over the
state loop (`MachineTraceWith`), and the kernel checks per call that the
call is pointwise in the state (`f.machine_inst_k`). What this theorem
takes as a hypothesis — the seed constraint at the call's position — is
that the instance's output wire carries the call's value at every cycle;
the flat semantics the theorem is stated in treats an instance as a no-op
(the open-module view of `Sparkle.IR.Semantics`). Discharging that
hypothesis for the real module is the child's own theorem (its module
computes its source function) composed through the linked semantics
(`evalAssignsH`, S6 `linked_open`). For machine modules the composition is
now PROVED generically (`Tools.ShippingMachineCompose.machine_linked`: the
linked run, each instance evaluated by the module its name resolves to in
the shipped design, seeded with the declaration's own inputs, shows the
source — given that each call's module computes a function `F k` of its
argument ports and the source's call is `F k` of its arguments), and the
child side is proved for combinational machine-route children
(`Tools.ShippingMachineChild.childFn_of_trace`, `childFn_full`). It is
generated per declaration (`#machine_linked f` → `f.machine_linked`,
`#machine_child c` → `c.machine_child`); two premises remain stated rather
than proved: the design's child module is
the child's own full-entry run (the child synthesizer is an opaque
`IO.Ref`, as S6's `SubSynthDefines`), and the run-module gate
`dropZeroWidthModule raw = raw` of the child.
This gap is not cosmetic: the open-module theorems cannot see WHICH wires an
instance connects, and a real miscompile lived there — `closeInstsM` found
the call's output and argument wires by BINDER position, so in a
domain-polymorphic declaration (the domain binder has no port) the instance
was wired one position off. It is fixed (the offset now counts ports;
regression `callerD` in ShippingMachineInstTest checks the instance drives
its own `_gen_inst` wire and reads only its argument wires); the entry
theorem now quantifies over the offset, and the linked composition is what
will rule out this class for good.
Declarations are added with
synchronous kernel checking and the theorem's axioms are audited, so a
failed check cannot leave a constant behind. The command also runs the
machine synthesis once and requires that it ties the `let`s — evidence
for the boundary `MachineCloses` in the environment of the check, not a
proof of it for another run. The
optimizer and the printer after the core entry ARE composed for machine
modules, up to the emitted-Verilog semantics: `f.machine_ships`
(`machine_ships_full`) states the same conclusion for the module the full
entry returns after `optimizeModule` and for its emitted Verilog
(`EmitSem.runModuleSV`), under gates that are decidable facts about the
modules of the run — `refineCheck raw b` (cleanup and duplicate merge),
`refineCheck b o` (optimizer), the reset port, the output ports,
`EmitSem.seqCheck` and its width agreement. `refineCheck` is proved sound
(`refineCheck_transfer`); the gates are evaluated by the suite on thirteen
declarations and by `scripts/shipping-coverage/pipeline.sh` on the corpus
(107 of 113 hold). Since the compiler checks the merge and the
optimizer itself (`mergeChecked`, `checkedOptimize`; `machine_ships_checked`),
`f.machine_ships` no longer needs `refineCheck` as a premise: what remains
are structural facts about the run's modules (no zero-width wire, the
assign + register shape, the normal forms of the core and merged modules
— `refineCheck m m`, the condition under which the compiler's gate binds
— the reset and output ports) and the emitted-Verilog check of the printed
module; they hold for 107 of 113
machine-route declarations. The module parsed back from the printed bytes
is not covered for machine modules.

**From the wiring (2026-10-08).** `f.machine_ships_wired`
(`Tools.ShippingMachineShipsW.machine_ships_wired`) discharges the
structural gates for a register machine from its WIRED endpoint
(`machine_traceL_of_data`): the zero-width cleanup is the identity
(`MachineWired`), a body with a register is merged only if `refineCheck`
accepts it (`mergeChecked_nonAssign`), an assign + register body is
optimized only if `refineCheck` accepts it (`checkedOptimize_seqOk`), the
reset and output ports are facts. Its premises are only the emitted-Verilog
check of the printed module (`EmitSem.seqCheck` and width agreement) and
that the body is not of the simple combinational shape. The generator emits
it for every register machine proved by `machine_trace_of_data`,
`_of_loop`, `_of_regs`, `_of_nested` or `_of_tele_ext` on the declaration
itself (their wired forms `machine_traceL_of_data`,
`Tools.ShippingMachineLoopL`, `machine_traceL_of_tele_ext` take the same
arguments); after a sign-normalisation / fusion transport too (the
theorem is built for the rewritten value and moved to the declaration's
source by the same `Eq.mpr` as `f.machine_sound`); not for instances. It is optional — a failure leaves
`f.machine_sound`/`f.machine_ships` as they were. Suite: 13 of 13
`circuit do` declarations, 8 of 8 hand-written loops, 5 of 5 sub-machine
nests, 3 of 4 telescopes. Corpus (partial: 38 of 184 files before the run
was stopped for memory): 27 of 84 endpoints.

**Combinational machines (2026-10-08).** `f.machine_ships_comb`
(`Tools.ShippingMachineShipsComb.machine_ships_comb`) is the same for a
machine without slots or calls: its module is assignments only (a
`MachineWired` clause), the full entry's merge is the self-validating
`mergeDuplicates` (the same environment), `checkedOptimize` keeps the
optimizer's output only when `optCheck` accepts it (the same outputs), and
the emitted Verilog runs as the module (`seq_run_to_sv`). Its statement
(`MachineShipsComb`) seeds every cycle with the inputs and the reset name
low (`seedR`: a combinational module has no reset port). Remaining premises:
the shipped body is of the simple shape and the emitted-Verilog check.
Suite: 4 of 4, and 6 of 6 sign-normalised (transported) endpoints.

**The optimizer on instance-bearing modules, checked at compile time
(2026-10-08).** `checkedOptimize` used to pass an instance-bearing module's
optimizer output to the printer UNCHECKED (the optimizer inlines connection
values into instance ports: `decoderPipeline` 530 → 175 statements). Now,
where the extracted interface is in the normal forms (`hierBinds`), the
output has its connections named again (`Sparkle.IR.HierCheck.deinline`)
and is kept only if `hierRefineCheck` accepts it: the same instance
statements both ways (`instsKept`), every connection validated or untouched
(`connAgreeOk`), and `refineCheck` on the extracted pair (`openFlat`:
instances dropped, instance-driven wires as inputs, instance-read wires as
outputs); else the module ships unoptimised. Measured (gold62): every
status identical; 21 output files differ, every difference an instance
connection that reads a named wire again (`assign w = …;` plus its `logic`
declaration). The check also requires that `o` drives no extracted input,
and the extraction classifies registers as driven (`drivesOf`).
PROVED (`Tools.ShippingHierOptRun.hierRefineCheck_linked`): when the check
accepts, every run of the STATEFUL linked semantics of the module
(`runModuleTG`, any child step `KS` that reads the parent only through its
input connections) has a run of the shipped module from the same state with
the same outputs — the linked run is an open run of the extracted module
(`linked_open_run`, from `linked_openKG`), `refineCheck_transfer` carries it
to the extracted optimized module, and that open run is a linked run of the
optimized module with the children stepping as before (`open_linked_run`,
from `linked_consistentKG` and `runModuleTG_of_open`). Premises: the
design's (linked-well-formed bodies, distinct instance names, no instance
reading its own output, the instance-driven wires among the extracted
inputs — evaluated on four real modules in
`Tests/Compiler/ShippingHierOptRunTest.lean`), inputs fitting their widths
with reset low, instance outputs and start register values fitting their
widths.

**Machines with instances, to the shipped module (2026-10-08).**
`Tools.ShippingMachineShipsHier.machine_ships_hier` carries a composed
theorem (the core module's stateful linked run shows the source) through the
full entry — the cleanup is the identity, and the checked merge is the
identity on an instance-bearing body (`mergeChecked_inst`: its validator
keeps assignments as assignments, `refineCheck` rejects instance
statements) — and the optimizer (`hierRefineCheck_linked`): the SHIPPED
module's stateful linked run shows the source. It is general in the child
step `KS`, the children's reset and the run boundary; `composedG_of_T`
instantiates it with the one-level composed theorem (`runModuleT` is
`runModuleTG flatKS` on memory-free bodies). Generated by
`#machine_ships_hier f` (`Tools/ShippingMachineShipsHierCommand.lean`) as
`f.machine_ships_hier`: 5 of 5 suite machines with sequential children
(`parent`, `chained`, `engineOnce`, `twinCalls`, `mesh2x2`), 3 of 3 suite
memory parents (`composedG_of_Tmem`, reset = memories and read latches
zero) and the corpus memory parent `quantModule` (H.264), their module
premises (the optimizer check binds, linked-well-formed bodies, distinct
instance names, no instance reading its own output, instance-driven wires
extracted, instance-output widths, a reset port) evaluated on the real
modules. Remaining premises: the run boundary per sequential child
(`BoundaryOf`, as for the composed theorem), inputs and start values within
their widths, and the children's outputs within their ports' widths — for
sequential children a decidable check (`kidsMasked`: no memory, every output
port assigned once by a self-masked expression no wider than the port;
`flatKS_boundedIn`), evaluated on the real modules; for memory children
the check `kidsMem` (every child the built memory module, no connection
naming its read latch) with the read-latch invariant `memInv` (zero at
reset, `resetM_inv`; a combinational read and a latched read are masked at
the data width; `memKS_boundedIn`). Found on the way: `deinline` named a
connection wire before EVERY instance reading it (two memory instances
sharing a write-enable wire got two assignments of it, which the linked
semantics' well-formedness rejects); it now names a wire once. The shipped module's EMITTED VERILOG: `Tools.ShippingHierSVRun.linked_sv_run`
— a stateful linked run of a module is the run of its emitted Verilog
(`runModuleSV`) from the oracle seeding, its instance outputs at each cycle
the values its children drove (`linked_open_runG`, then `seq_run_to_svI`),
under the emitted-SV check and width agreement of the shipped module
(evaluated on the five real shipped modules); `linked_sv_of_run` derives
the oracle seeding's bound from decidable facts of the shipped module (its
children's bound check, instance-output widths, instance-driven wires
extracted and no wider than emitted — evaluated on all eight shipped
machines with children) and the inputs and start state within the emitter's
widths. And the DESIGN:
`design_sv_run` — along that run (one-level children, `flatKS`), the
emitted Verilog of every instance's child, fed at each cycle with the run's
values on its input connections, runs to environments whose output ports
carry exactly the oracle values the parent's emitted Verilog was given
(`child_run_of_linked` + `seq_run_to_sv`): the emitted texts of parent and
children, connected, run as the linked run. The children's emitted-SV
premises are evaluated on the real children. OPEN: the boundedness
premises of the SV seedings (instance outputs, connection-fed child inputs)
discharged from widths, transported endpoints, depth > 1.

**Stateful composition with children (2026-10-08).** For a machine whose
calls are memory reads and/or sequential machine children (`closeInstsG`),
`f.machine_composedT` states the STATEFUL linked run (`runModuleT`,
`runModuleTG` at depth `n`: each instance steps its own child module with
its own registers and memories) of the emitted module. Its premises beyond
the machine endpoint's: (1) the run boundary per sequential child
(`BoundaryOf`: the module an instance of its calls resolves to is a run of
the full entry on the child — the child synthesizer is an `IO.Ref`, opaque
in the logic, as `SubSynthDefines`); memory children need none (the compiler
builds the memory module and checks that its name finds it); (2) the
children start from RESET (memories and sync-read latches zero, registers at
their reset values: `ResetN`); (3) the top seed holds reset and clock low.
Proved, not assumed: that the instance's connections feed the child exactly
its argument wires (`connsG`, `seq_inst_run`), the child's module at the
full entry (zero-width cleanup kept — now PROVED for every machine module,
with or without instances, so the run-module gate `dropZeroWidthModule raw =
raw` above is discharged; the merge is `refineCheck`-accepted or absent —
`mergeChecked` no longer ships an unchecked merge), and that the merged
design finds every child module and every module of a child's design as
itself (checked by the compiler with the IR's decidable equality). Children
that themselves have children are covered by the depth-`n` theorems up to
the links listed in the TODO (F6).

## 6c. The printer (the CompCert framing, F3)

CompCert's guarantee ends at its assembly AST; the printer that turns it
into text is trusted. Sparkle's guarantee is framed the same way, with the
FORWARD direction primary:

- **Proved (forward):** the shipped module's emitted SystemVerilog objects
  — the continuous assignments, register always-blocks and memory writes
  `EmitSem.emitAssigns` / `emitRegs` / `emitMemWrites` build from the
  shipped IR — run under the SV semantics (`runModuleSV`) as the source
  (`seq_run_to_sv`, `machine_ships*`, `linked_sv_run`, `design_sv_run`).
  This needs no parser.
- **Trusted (printer):** that the bytes `Sparkle.Backend.Verilog.toVerilog`
  / `toVerilogDesign` print are the SystemVerilog those objects denote —
  the module header, declarations, and the printing of each object. It is
  the analogue of CompCert's assembly printer.
- **Validated (parse-back), not trusted:** where the suite runs it, the
  printed bytes are read back by the shipping parser and the result is
  checked against the shipped module (`semFragCheck`, `bodyImage`,
  `bodyReorderCheck`, §4), and for those modules the parsed-back text is
  proved trace-equal to the checked module. This direction trusts the
  reader instead of the printer; it is a validation of the printer on the
  checked corpus, not the primary claim.

A verified printer with a proven inverse on the emitted sub-language would
remove the printer from this list; it is not planned.

## 6d. `partial def`s on the shipping path (F4 audit, 2026-10-08)

A `partial def` has no unfolding equations, so no theorem can look inside
one. Each that a compile of a certified or machine-route declaration
reaches is covered as follows — none is relied on unchecked:

| `partial def`s | Where | Covered by |
| --- | --- | --- |
| `machConv`, `machNested`, `machChain`, `machLoopBody`, `machLoopRoot`, `machInstance(S)`, `machLiftScalarN`, `machBoolMap`, `machNorm` (Elab); `rootFloat`, `zetaAll`, `projChain`, `prodMatcherArity?` (MachRawSurface); `packTupleInputs` (MachTupleIn) | reading a declaration into a machine shape | the boundary `MachineDefines` (§2) and, per declaration, the kernel `Eq.refl` checks of the generated endpoint against the declaration's own value (`machine_body`, `machine_writes`, `machine_result`, `machine_source`) — translation validation |
| `passM`, `iota`, `reduceHead`, `betaAll`, `listLit?`, `relevantClosure`, `headBetaM` (MachRecUnfold), `canonHardwareExpr`, `stripMemoizeWrappers`, `openRecordInputs`, `splitReturnLeaves` (Elab) | the front end's unfolding / normalisation | the same per-declaration kernel checks (`EntryDefines`/`MachineDefines` name the result; the endpoint's `rfl`s tie it to the declaration) |
| `optimizeExpr`, `substituteExpr`, `resolveSlice`, `inferWidth`, … (Optimize); `canonExpr` (RegDedup) | the optimizer and the duplicate merge | compile-time result checks: `optCheck`, `refineCheck`, `hierRefineCheck`, `validateMerge` (proved sound); an unchecked result only where no gate binds, and the shipping theorems then require the gate (§4) |
| the mutual `synthesizeCombinational` (child synthesis with `sparkleChildCache`) | a child compiled inside a parent's synthesis | the run boundary per child (`SubSynthDefines`, `BoundaryOf`, §2–3); the theorems are about the total top-level `synthesizeCombinational` |
| `translateExprToWireImpl` and the `handle*` arms | the legacy front end | outside every theorem (§7); the certified knot is the total fuel-bounded `translateExprToWire` |
| `emitDimExpr` and the printer (Backend/Verilog) | bytes | trusted printer (§6c) |
| the parser / lowering (`Tools/SVParser`) | reading bytes back | validation only (§6c) |
| `Type.evaluate`, `specializeType/Expr` | parameterized synthesis | outside every theorem (§7) |

## 6e. Universality (F1, stage 1 — decided 2026-10-08)

CompCert's theorem is universal over Clight ASTs; the text-to-AST step is
validated per program. Sparkle's claim is framed the same way:

- **Universal (proved once):** the compiler-correctness theorems quantify
  over EVERY reified source (`MachineData` with `d.ok`; the unified `Term`
  of the gate route) and over EVERY run of the real compiler
  (`RunsTo (synthesizeCombinationalCore …)`, `RunsTo (synthesizeCombinational …)`):
  `machine_trace_of_data` / `_of_loop` / `_of_regs` / `_of_nested` /
  `_of_tele_ext` / `_of_comb`, `machine_ships_wired`, `machine_ships_comb`,
  `machine_ships_hier`, `translateExprToWire_sound`,
  `execution_source_of_env`.
- **Per declaration (validated reflection):** that the declaration's Lean
  value IS the reified source — the kernel `Eq.refl` checks the endpoint
  generator emits (`machine_body`, `machine_writes`, `machine_result`,
  `machine_source`, …) and the boundary `MachineDefines` / `EntryDefines`
  (§2). This is the analogue of CompCert's validated parser; the generator
  that produces these checks is unverified meta-code, but every check it
  emits is checked by the kernel.
- **Monitored:** a successful compile without a kernel-checked endpoint
  would be outside the claim. The corpus measurement counts them
  (`scripts/shipping-coverage/endpoints.sh`): legacy-only 0 of 391 real
  declarations and every machine-route declaration with an endpoint
  (gold53); to be re-measured after every compiler change.

Stage 3 (planned) strengthens the reflection: the shape readers
(`machineShape?` and its `partial` helpers, §6d) rewritten total and
proved — `read succeeds ⇒ the declaration's expression is quote(shape)
∧ d.ok` — leaving only the reflection principle (a constant's value is its
expression) per declaration.

## 7. What is outside every theorem

- **Compiles that miss the certified gate.** The theorems apply when
  `certifiedShape?` or `mixedCertifiedShape?` accepts the declaration.
  Everything else compiles through the legacy front end and handlers,
  which have no theorem. On the measured corpus this is most real
  designs; the numbers and the reasons are in the coverage inventory.
- **Legacy handlers reached from a certified compile.** A certified
  family's theorem covers its own quoted shape. A nested child
  synthesis is covered only through the child-side premises of §3.
- **Symbolic-width synthesis** (`#synthesizeParameterizedVerilog`) and
  specialization of parameterized designs.
- **Other back ends**: the C simulation, JIT and CUDA emitters, and
  the SystemVerilog import path as a front end.
- **A width-generic `@[hardware_module]`** is compiled once at a
  fallback width. Instantiating it at another width is refused by the
  width-linkage check (it used to miscompile); it is not specialized.

## 8. What is NOT retained

For the certified shapes the following are proved, not assumed: the
translation of the quoted source, including both validated caches; the
elaboration semantics of the emitted module against the source streams;
zero-width cleanup; the width linkage of every emitted instance; and,
where the gates of §4 hold, the merge and the optimizer, the emitted SV
objects' cycle semantics, and the trace of the parsed-back text.

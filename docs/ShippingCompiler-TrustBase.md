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
registers, memories and instances the shipping pipeline keeps the
optimizer's output unchecked at run time. For those shapes the
validation is exactly the gates above: an optimizer change that broke
one would fail the suite rather than silently ship, but a compile the
suite never ran is not checked.

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
`f.machine_result`, `f.machine_source`). Declarations are added with
synchronous kernel checking and the theorem's axioms are audited, so a
failed check cannot leave a constant behind. The command also runs the
machine synthesis once and requires that it ties the `let`s — evidence
for the boundary `MachineCloses` in the environment of the check, not a
proof of it for another run. The
optimizer and the printer after the core entry are NOT yet composed for
machine modules; the family-agnostic sequential pipeline theorem
(`shipping_pipeline_transfer`) applies under its decidable premises but
that composition is not stated.

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

# Call-port and call-argument widths on the machine route (findings A, A', E)

Worker B, branch `par/b-3` on `a9fd07ca`. Everything below is READ from the
sources; nothing was built or run. Line numbers are those of
`Sparkle/Compiler/Elab.lean` at `a9fd07ca` unless a file is named.

Ruling this note works under: a runtime check that REJECTS inputs is not a
resolution; either width agreement is derived from the well-typedness of
the source, or an explicit cast matching the existing meaning, with its
proof; first find out whether mismatching-yet-successful examples exist.

## 1. The four widths of a call `c a₁ … aₙ`

`senv = structEnv env` (4379): `inst := instSignature? env`,
`instS := instSignatureS? env`, `fields := userStructure? env`. All the
functions named in this section except `machConv` / `machInstance` /
`machInstanceS` / `machChain` are ordinary `def`s (they have equations).

The one kind function everything goes through:

    mixedGateBinderKind? (2332)   DomainConfig            ↦ .domain
                                  Signal _ Bool           ↦ .bool
                                  Signal _ (BitVec wE)    ↦ .bits n   if canonicalNatLitValue? wE = some n, 0 < n
                                  anything else           ↦ none
    canonicalNatLitValue? (1384)  .lit n  |  OfNat.ofNat Nat (.lit n) (instOfNatNat (.lit n))   — nothing else

It is SYNTACTIC: no `whnf`, no `evalNat`, no transparency, no default. A
width that is not one of the two literal forms gives `none`.

### (i) the parent's binder for result field `f`

The binder is `(inst{k}, st.insts[k].2.2)` (5164–5165). `st.insts` is
written in two places only:

* one Signal result — `machInstCall?` (3713) reads `senv.inst c`, i.e.
  `instSignature? env c` (4358) = `(telescopeKinds ci.type, machResultKind? ci.type)`
  for `ci = env.find? c`, the child's RAW constant; `machInstance` (4041)
  pushes `(c, js, res)` with `res` that `machResultKind? ci.type` (4067).
  `machResultKind?` (4311) strips `∀`s and applies `mixedGateBinderKind?`.
* any other result — `machInstCallS?` (3724) reads `senv.instS c` =
  `instSignatureS? env c` (4370) = `(telescopeKinds ci.type, ci.type)`;
  `machInstanceS` (4075) instantiates the `∀`s of `ci.type` with the call's
  arguments (`inst`, 4081–4085: `instantiate1`, no reduction) and takes
  `machOuts? senv resTy` (4086); one entry `(c, js, f.2)` per field, in the
  list's order, `instFields` the fields' names (4110–4111).
  `machOuts?` (3851): `∀`s stripped; `Prod A B` ↦ `out_0`, `out_1` with
  `mixedGateBinderKind?` of `A`, `B`; a Signal ↦ `out`; otherwise the head
  constant `s` and `senv.fields s` = `userStructure? env s` (4333), whose
  kinds are `machResultKind?` of the TYPE OF EACH PROJECTION FUNCTION
  `s ++ f` — a function of the structure's declaration only; the
  structure's arguments at the call are not read.
* (a memory: `machInstance` with the kinds written in the reader, 3950–3951;
  the child is built from the same `aw`, `dw`, `MachMemory.memChild?`.)

So: (i) = `mixedGateBinderKind?` of the child's raw result type (one
Signal), of a component of it (pair), or of a projection's result type
(structure).

### (ii) the child's output field `f`

The closing takes the child's module from `sparkleChildSynth` =
`synthesizeChild c` (8784) = the full entry on `c` (5192, 5210). What the
port's type is depends on the route the CHILD takes:

* machine route: `outs` (5064–5066) is `machOuts? senv d.type` — or one
  packed `out` for a `Signal dom (A × B)` result (`machTupleKinds?`) — where
  `d` is the ENTRY constant: the raw one, or `inlinedConst inl ci` (3404)
  whose TYPE is rewritten by `userInliner` too (`type := inl d.type`). The
  layout field is `machOutFields … outs` (5174), its port type
  `machHWType kind` (4442).
* gate / mixed / legacy routes: the port is added by `emitLeaves`
  (2179–2186) with the type of the WIRE the translator returned for the
  leaf (`decl.ty`), an input's type when the leaf is an input, and
  **`.bitVector 8` when the leaf wire is neither** — a default. The
  declared result type is not read.

### (iii) the parent's argument wire `j`

`machInstance` / `machInstanceS` (4053–4063, 4088–4099): for the `j`-th
non-domain binder kind `kind` of `telescopeKinds ci.type` (the `∀` domains
of the child's RAW type) and the converted argument `v'`, the `let` index
is `machLetIndex (inst{k}_arg{j}) kind v' st.lets` (3735):

* `v'` is already a `let` placeholder ⇒ THAT `let`, with the kind it was
  bound with (`machBindLet`, 3611: `mixedGateBinderKind?` of the `let`'s
  type annotation; or an earlier call's kind);
* a `let` with the same value exists ⇒ that `let`, its kind;
* otherwise a new `let` of kind `kind`.

`kind` and the argument's own type are never compared. The wire's declared
width is the kind of binder `nDecl + (kI + (n + a))` (the harness declares
the transition's ports from `shape.binders`).

### (iv) the child's input port `j`

* machine route: `bs` (5061) = `mixedGatePeel (packTupleInputs d.value)` —
  the `λ` domains of the entry constant's VALUE (2340), by
  `mixedGateBinderKind?`; ports by `bindMixedCertifiedInputs` (2944).
* gate route: `gatePeel d.value`, `bindCertifiedInputs` (2915).
* legacy route: `bindInputsLegacy` (2110) — `inferHWTypeFromSignal` of the
  binder's type after `whnf`; a binder that is not hardware gets NO port.

### Same function on related types?

| pair | parent | child (machine route) | same function? |
|---|---|---|---|
| (i)/(ii) one Signal | `machResultKind? c.type` (raw) | `machOuts? senv (entry c).type` | yes up to the entry's `inl` on the type; both end in `mixedGateBinderKind?` of the same result type |
| (i)/(ii) structure | `senv.fields s`, `s` the head of the instantiated raw type | `senv.fields s'`, `s'` the head of the entry type | the same list when `s = s'` and the two `senv` are of the same environment (same run) |
| (i)/(ii) pair | `machOuts?` of the instantiated raw type | `machOuts?` of the entry type | yes; instantiation cannot change a literal |
| (iii)/(iv) | `telescopeKinds c.type`: **`∀` domains of the raw TYPE** — or the kind of a reused `let` | `mixedGatePeel`: **`λ` domains of the entry VALUE** | NO: two expressions, related only by the kernel's typing of the definition (`value : type`) and of the call |

For a child on another route (ii) and (iv) are the translator's.

## 2. Where the two sides could diverge although the source typechecks

Classes; "declines" means a reader returns `none` so the parent is not a
machine with this call (no mismatch can ship from it), "open" means read
but not decided by reading. Each has a candidate in
`Tests/Compiler/CallWidthHuntTest.lean`.

1. **Width not a literal in the child's type** (`BitVec (4+4)`, a reducible
   or ordinary `Nat` constant, a type alias for the payload) — `pSum`,
   `pAbbrev`, `pDef`, `pByte`. Parent: `instSignature?` is `none`
   (`machResultKind?` / `telescopeKinds` see no literal). If only the result
   is non-literal, `instSignatureS?` (4370) ACCEPTS it as "not one Signal";
   `machInstanceS` then asks `machOuts?`, which finds head `Signal` and
   `userStructure? env Signal` — `none` because `inlUserModule` (3303)
   excludes the `Sparkle` root. ⇒ declines. The CHILD's own entry may still
   be a machine through the `inl`-rewritten type (asymmetry, harmless as
   long as the parent declines). Nothing evaluates a width at two
   transparencies: there is no evaluation.
2. **`Bool` against `BitVec 1`** — `pBit1`, `pBool`. The machine reader is
   the same on both sides (`.bool ↦ .bit`, `.bits 1 ↦ .bitVector 1`,
   `machHWType` 4442 / `kindTy`). A child on the legacy route may declare
   `.bit` for `BitVec 1`: the TYPES differ, the widths (1) do not;
   `callWidthsOk`, `instOutWidthsOk`, `portsMatchB` compare widths.
3. **Structure results flattened in different orders** — `pTwo`, `pTri`.
   Both sides read the one list `senv.fields s`; the closing connects by
   port NAME (`instStmtG`, `Sparkle/IR/MachineInstG.lean` 30–53), not by
   position. A structure with a non-domain parameter or an inherited
   parent has a projection whose kind is `none` ⇒ declines.
4. **Structure behind an alias** — `pAlias`. Parent: head constant is the
   alias, `senv.fields` is `none` ⇒ declines (the child itself is read
   through the unfolded type).
5. **Pair of Signals** — `pPair`: same `machOuts?` on both sides; whether
   the parent's `Prod` projections are read at all is open.
6. **`{dom}`-polymorphic child** — `pPoly`, and `mid` / `grand` /
   `midH` of the census. Kinds do not mention the domain. NOT a width
   matter but noted: the child compiled alone takes the asynchronous reset
   kind (`machDom?` 4254, a domain binder) while a `defaultDomain` parent
   is synchronous.
7. **Port width computed from the child's BODY** (child on the gate, mixed
   or legacy route) — `pCat`, `pSlice`, `pZext`, `pTrunc`, `pPlain`. The
   parent's kind is the declared type's; the child's port is the
   translator's wire type or the `.bitVector 8` default (2185). Agreement
   is the translator's type correctness for that body, not a property of
   the call readers. This is the class where a mismatch is not excluded by
   reading; it is also where finding C (stale `sparkleWireWidthCache`)
   would surface.
8. **`λ` domains against `∀` domains** (iii)/(iv). For a definition
   written `def c (x : T) : R := …` they are the same expression. They can
   differ syntactically only up to definitional equality, and both readers
   demand a canonical literal: see §3 for why they then agree.
9. **A reused `let` as argument** — `pLetReuse`: the wire has the kind of
   the `let` (its own type annotation, or an earlier call's binder kind),
   not this child's. Equal by the same argument as 8.
10. **Arity** — `pUnused`, `pClkName`, `pCount`. `instStmtG` / `instStmt`
    filter the child's inputs by the NAMES `clk`, `rst` and compare counts
    only; connections are POSITIONAL (`inPorts.zip argWs`). A data binder
    named `clk` is dropped from the argument ports ⇒ count mismatch ⇒ the
    closing returns `none` ⇒ the machine arm declines after having run
    (finding E's path). Same for a sequential one-output child (`instStmt`
    refuses a child with a clock, `Sparkle/IR/Machine.lean` 278), and for a
    legacy child whose non-hardware binder got no port.
11. **The name `clk` in the parent** — `pClkIn`: a sequential child's `clk`
    port is connected to the NAME `clk` of the parent
    (`("clk", .ref "clk")`); if the parent has a data input of that name
    the connection's widths are 8 and 1. Open (does the port allocator keep
    the binder's name? not traced).
12. **Wrappers** — `pMapWrap`: `Signal.map` around the call or the
    argument changes nothing about the call's four widths; the wrapper is a
    separate `let` / operator.

Reading therefore predicts: no mismatching-yet-successful example from the
READERS (classes 1–6, 8, 9, 12 decline or agree); classes 7 and 11 are the
ones the run has to decide; class 10 produces fall-throughs, not
mismatches.

Also found while reading:

* `callWidthsOk` (`Tools/ShippingCallWidths.lean` 47) tests the child's
  field named `d.shape.instFields.getD k ""`. On the one-output closing
  `instFields = []`, the name is `""`, and the condition is VACUOUS. The
  test evaluates a strict per-pair comparison beside it.
* On the legacy fall-through the legacy arm translates the UNFOLDED entry
  constant (`entryConst` returned `inlinedConst` because `machineShape?`
  accepted it), not the original declaration.

## 3. Alternative (a): agreement from well-typedness

### What is true

**Claim K (defeq-invariance of the kind on its domain).** If
`mixedGateBinderKind? t₁ = some k₁`, `mixedGateBinderKind? t₂ = some k₂`
and `t₁ ≡ t₂` (the kernel's definitional equality, in a common context),
then `k₁ = k₂`.

Why: the domain of the function is exactly `DomainConfig`, `Signal d Bool`,
`Signal d (BitVec ⌜n⌝)` with `⌜n⌝` one of the two canonical literal forms.
`Signal` (`Sparkle/Core/Signal.lean` 92), `DomainConfig`, `BitVec`, `Bool`
are inductive types (type formers are injective and pairwise distinct
under `≡`); `⌜n⌝ ≡ ⌜m⌝` iff `n = m`. TRANSPARENCY plays no role: the
function never reduces, so it cannot read two defeq types at different
transparencies as different literals — where it cannot see a literal it
returns `none` and the reader declines.

With K: (iii)/(iv) agree because the kernel checked the child
(`value : type`, so `λ`-domain `j` ≡ `∀`-domain `j`) and the call (the
argument's type ≡ the instantiated `∀`-domain; a `let`'s annotation ≡ its
value's type); (i)/(ii) on the machine route agree because both are the
kind of the same result type up to `inl` (which preserves `≡`).

### What can be stated in Lean, and what cannot

K is a statement about `≡` on `Lean.Expr`. There is no such relation in
the logic (no formal typing judgment of Lean in this repository), so K is
a META-theorem about the kernel, not a theorem.

A propositional substitute does not exist: from
`Signal d (BitVec n) = Signal d (BitVec m)` one cannot prove `n = m`
(`Signal d α` is `Nat → α` up to structure; the two types have the same
cardinality for all `n, m ≥ 1`).

What the reflected shapes are tied to (read):

* `MachineDefines` (`Tools/ShippingMachineEntry.lean` 2261) is a PREMISE:
  `machineShape? (entryConst …) = some shape` in the run. It says the shape
  is the reader's output, nothing about types.
* the generated endpoints DO tie each shape to its declaration's Lean
  types, through the kernel: `#machine_endpoint parent` builds the input
  extension with the real call term at the reflected kind,
  `extendBits D bits pos (lit w) (call term)` with
  `extendBits … (w : Nat) (sig : Signal D (BitVec w))`
  (`Tools/ShippingMachineCommand.lean` 1722, `Tools/ShippingMachineAuto.lean`
  377), so the theorem typechecks only if the call's Lean type is
  `Signal D (BitVec w)` for the PARENT's reflected `w`;
  `#machine_linked` builds `BitVec.toNat (lit w) (arg.val j)` with `w` the
  CHILD's reflected binder kind and the call's actual argument
  (`Tools/ShippingMachineLinkedCommand.lean` 231–237), and checks the
  argument count against the child's binders (228).
  (UNVERIFIED: the child-side generator for its own outputs was not opened.)

So for every pair that HAS generated endpoints the kernel has already
compared each reflected width with a Lean type, and by K the data
conditions `callWidthsOk` / `callArgsOk` cannot fail there; but that
knowledge sits in the typing of generated statements, not in an equation a
proof can use. The object-level form of "derived from well-typedness" is
therefore still one closed equation per pair — which is what the `decide`
is. A lemma "for all pairs" needs the two data to be equal BY CONSTRUCTION:

### The reader-level statement that IS provable (proposal, not implemented)

Make the shape's call kinds a pure function of the child's entry type, so
that both shapes contain the same term:

    -- pure, total, in a new compiler file
    def callKind (senv : StructEnv) (entryTy : Lean.Expr) (field : String) : Option MixedGateBinder :=
      (machOutsOf senv entryTy).bind fun outs => (outs.find? (·.1 == field)).map (·.2)
        -- machOutsOf: the `tup?` / `machOuts?` choice of machineShape? 5063–5066
    def argKinds (entryValue : Lean.Expr) : Option (List MixedGateBinder) :=
      (mixedGatePeel (MachTupleIn.packTupleInputs entryValue)).map fun p => (p.1.map (·.2)).filter (· != .domain)

and in `machineShape?`, AFTER the partial reader returned, replace each
call binder's kind by `callKind senv (entry c).type field` when it is
`some`, keeping the reader's kind otherwise (`instBinders`, 5164), and the
kind of a `let` created for an argument likewise. This is not a check and
rejects nothing: it is the identity whenever the two computations agree
(by K: always, for well-typed sources), and when they would not agree the
transition is compiled against the child's kinds. Then, with no premise
about the run beyond the two `MachineDefines`:

    theorem callWidths_of_defines
        (hp : machineShape? false [] ecP senv = some sp)
        (hc : machineShape? false [] ecC senv = some sc)
        (hk : sp.insts[k]? = some (c, js, kd)) (hname : entry constant of c is ecC) :
        ∀ o ∈ sc.layout.outs, o.name = sp.instFields.getD k "out" →
          (sp.binders[nDecl + k]?).map (fun b => (kindTy b.2).bitWidth) = some o.ty.bitWidth

provable by unfolding `machineShape?` (a `def`) on both sides down to
`machOutFields` / `machHWType` (pure). The same for arguments against
`(sc.binders.take nDeclC)`. `callWidthsOk` / `callArgsOk` then follow for
EVERY pair of machine-route declarations, and the per-pair `decide`s go.

Cost: a compiler change (new file + two lines in `machineShape?`), the
`machineShape?`-unfolding lemmas (the existing proofs that already unfold
it for `layout.outs`: `leaf_real_outTys`' chain), and one more environment
read per call in the reader. What it does NOT cover: a child on the gate /
mixed / legacy route (class 7) — there the port is the translator's, and
the lemma needed is that route's own typed-ports fact
(`ChildOutTys`-style: "the `out` port has the declared result type's
width"), per route.

## 4. Alternative (b): an explicit adapter at the connection

### The existing meaning

Linked IR semantics (`Tools/ShippingHierarchySoundness.lean` 30, 170, 186):
an input connection hands the child `env w` as it is (`connEnvS`), an
output connection binds the parent wire to `cres p.name` as it is
(`bindOuts`). No masking in either direction: on a width mismatch the IR
run keeps the WIDE natural number on the narrow side.

Emitted Verilog: a port connection of different widths truncates or
zero-extends silently. So on a mismatch the IR run and the text differ;
`PortsMatch` (`Tools/ShippingDesignSV.lean` 57) is the premise that
excludes it, and `instOutWidthsOk` (`Tools/ShippingHierOpen.lean` 503) is
what bounds the seeded values (`ChildOutsBounded`) on the output side.

"Matching the existing meaning" can therefore only mean: identical to
today when the widths agree; equal to what the TEXT does today when they
do not.

### The adapter

`Tools/ShippingCallCast.lean` (new, not built, used by nothing):

    def castRef (x : String) (wFrom wTo : Nat) : Expr :=
      if wFrom = wTo then .ref x else .slice (.ref x) (wTo - 1) 0

    theorem castRef_same (x : String) (w : Nat) : castRef x w w = .ref x
    theorem eval_castRef (we : WEnv) (env : Env) (x : String) (wFrom wTo : Nat) (hpos : 0 < wTo) :
        evalExpr we env (castRef x wFrom wTo) =
          some (if wFrom = wTo then env x else mask wTo (env x))
    theorem eval_castRef_inRange … (hpos : 0 < wTo) (hv : env x < 2 ^ wTo) :
        evalExpr we env (castRef x wFrom wTo) = some (env x)
    theorem eval_castRef_lt … (hpos : 0 < wTo) (hx : wFrom = wTo → env x < 2 ^ wTo) :
        ∃ v, evalExpr we env (castRef x wFrom wTo) = some v ∧ v < 2 ^ wTo

Printer (`Sparkle/Backend/Verilog.lean` 172–196): a slice selecting the
full width of a known wire is ELIDED (prints the name); an over-wide slice
from bit 0 prints the size cast `w'(x)`; a narrower one `x[hi:0]`. So even
an unconditional slice would print the same text when widths agree — but
the IR would change (the connection must stay a `.ref`: `connEnvS`,
`bindOuts`, `instOutWires`, `noSelfFeed`, `portsMatchB` read `.ref` only).
Hence the conditional form, and the adapter as a separate ASSIGN:

    in instStmtG (Sparkle/IR/MachineInstG.lean 30), per output entry (field f, wire w):
      Wc := width of mc's output port f          Wp := declared width of w in m
      Wc = Wp : connection (f, .ref w)                       -- today's statement, verbatim
      else    : fresh wire t : Wc; connection (f, .ref t); assign w := castRef t Wc Wp
    per argument (port q, wire a):
      Wq = Wa : connection (q.name, .ref a)                  -- verbatim
      else    : fresh wire t : Wq; assign t := castRef a Wa Wq; connection (q.name, .ref t)

By construction every connected wire has its port's width, for every
input: no check, nothing rejected, and for every declaration measured so
far (all 29 parents: `wid` true) the output is today's, statement for
statement.

### What it would touch (not implemented)

* `Sparkle/IR/MachineInstG.lean`: `instStmtG` returns statements + wires;
  `stmtsG`, `closeInstsG` (the wires, the `woCheck` / `topoBody` inputs).
  `Sparkle/IR/Machine.lean`: `instStmt`, `closeInsts` likewise.
* `Tools/ShippingMachineInstG.lean`: `CallStmtG`, `instStmtG_some`,
  `closeInstsG_insts`; `Tools/ShippingInstStmtG.lean` (`callConnsG`);
  `Tools/ShippingPortsMatchRaw.lean` (`callStmtG_conn`, `core_callConns`);
  `Tools/ShippingChecksWidths.lean` (`callStmtG_outWireF`,
  `core_callPorts`, `core_instOutWidthsOk`); `Tools/ShippingChecksOuts.lean`
  (`callStmtG_outWire`, `outsExtracted`); the closing proofs
  (`Tools/ShippingCallsAssemblyG.lean`, `ShippingCallsKidsD.lean`,
  `ShippingTransitionClosed.lean`, `ShippingClosedTyped.lean`: the wire
  table); the linked run of the closed module
  (`Tools/ShippingMachineCompose.lean`: `machine_linked_calls` reads
  `CallStmt`); name freshness (`Tools/ShippingLinkedFresh.lean`, N1).
* New obligations it creates: in the agreeing branch none (verbatim). In
  the other branch the linked proof must show the child receives / the
  parent sees the masked value and that this is the SOURCE's value — which
  is only true if the mismatch does not occur for well-typed sources, i.e.
  claim K again. So (b) removes `callWidthsOk` / `callArgsOk` from
  `portsMatchB` / `instOutWidthsOk` (width-correct text by construction)
  but NOT from the source-level theorem: `machine_linked` would need
  "branch 2 is not taken" or a meaning for it.

### Choice

By reading, (a) is the fitting one for machine-route children: the two
sides are the same pure function on the same type, and the reader-level
proposal of §3 turns the per-pair `decide` into one lemma. (b) is the
fitting one only if the run finds a class-7 or class-11 mismatch (a child
whose port width is the translator's): there the text IS width-incorrect
today and an adapter fixes the text, while the source-level meaning needs
that route's typed-ports lemma anyway. The hunt decides which.

## 5. Finding E: the machine arm declines after running

`synthesizeFromConst` 5286–5300: `machine?` is the shape; the arm
`synthesizeMachineCertified` (5227) runs the harness
(`synthesizeMixedCertified`, a full `CompilerM` run that fills the refs),
then `closeLets`, then `closeInstsM` / `closeInstsGM`, which call
`synthesizeChild` for every child (nested entries: they clear
`sparkleFvarValueMap`, `sparkleWireWidthCache`, `sparkleLetWireCache`,
`sparkleLoopWireCache`, `sparkleWireCanon` on entry, 5478–5487, and on exit
restore ONLY the first two, 5506–5508). It returns `none` when `closeLets`
is `none` (5239) or the closing is (`sparkleChildSynth` unset, a child
missing, `instStmt` / `instStmtG` refusing — §2 class 10 —, `topoBody`, or
any conjunct of the closing's final test).

On `none` the entry continues at 5300 into the legacy arm:
`CircuitM.init` is fresh (5356), the expression cache is fresh (5352), but
none of `sparkleLetWireCache`, `sparkleLoopWireCache`, `sparkleWireCanon`,
`sparkleSingleOutInstanceCache`, `sparkleSubInstanceOutputs`,
`sparkleFvarValueMap`, `sparkleWireWidthCache` is reset between the two
arms (the only resets are at the entry's start, 5465–5487). The legacy arm
allocates wire names from a fresh counter, so the names coincide with the
harness run's; `getWireWidth` reads the global width table first (finding
C), and a `let`-wire / loop-wire cache hit returns a wire NAME of the
harness run's module. Also `sparkleChildCache` / `sparkleSubModuleCache`
keep the children the closing synthesised (benign: full-entry results).

Which declarations take the path is measured by
`Tests/Compiler/MachineFallThroughCensusTest.lean` (observable: the machine
arm re-run from reset refs returns `none`; comparison with the legacy arm
run on the same entry constant from reset refs, and with
`certifiedFrontEnd := false`; names read but not declared). Predicted
members from reading: `pUnused`?, `pClkName`, `pCount` of the hunt (class
10), any machine whose `let`s `closeLets` cannot tie.

A fix is not proposed here (compiler change; the user's rule on cache
fixes applies): the minimal one would reset the seven refs — exactly the
nested-entry list plus the two instance caches — right before the legacy
arm when `machine?` was `some`.

# Call kinds against the child's signature: status, corrected (rounds 2–3)

Worker B. Branches: `fix/call-kinds` (`ebe0a1ef`, the ISOLATED wrapper
candidate — stays isolated), `par/b-4` (this round: docs, Tools, Tests
only). **Everything in rounds 2 and 3 is UNVERIFIED: nothing was built or
run by the author.** Measured so far (integrator, poc `b0f7e915`): 59
candidates, 58 compiled, width mismatch with success 0; 85 machine-shaped
declarations, 1 fall-through.

## Corrected summary (user review of `ebe0a1ef`)

Ruling: `callKindsDecline` stays `false`. The census is taken under `false`.

1. **The candidate policy CAN lose an input.** Under `callKindsDecline =
   true` a shape that fails a test is not returned; the declaration then
   takes the route it takes without a shape. If that route (legacy) fails
   on it, a source that compiled before no longer compiles. The round-2
   report's sentence "it does not reject an input" was wrong as a general
   statement. A census with 0 firings is evidence about the measured
   population only; it is not a compatibility proof and does not by itself
   justify enabling the policy.
2. **"Keeping today's behaviour and a general lemma are incompatible" was
   NOT shown.** What was shown is weaker: the WRAPPER is defined on every
   value of type `MachineShape`, and for arbitrary shapes the lemma is
   false. That says nothing about the shapes the real `machineShapeRaw?`
   returns in a well-typed environment. Two different statements:
   * *hard to derive in the present logic*: the readers that produce the
     call entries are `partial` (no equations), and the agreement of the
     `∀`-domains of a type with the `λ`-domains of its value is a fact of
     the kernel's typing judgment, which is not formalized here;
   * *false*: there is a well-typed, reachable source whose two readings
     differ. NO such source is known: 0 of 58 successful runs, and by
     reading (`B-callwidths.md` §3, claim K) none should exist.
   The agreement proposition is therefore OPEN and believed true, not
   refuted. §7 decomposes it into reader invariants and says which are
   provable, which are kernel-checked per declaration already, and which
   need the typing judgment.
3. **`callsAgree` is conditional on KNOWN signatures.** It is
   `(sigs e.1).all …`: with an empty signature list it is `true`. The
   kernel theorems (`callsAgree_at`, `callWidths_of_defines`) take the
   membership `hsig` and the child's own `machineShapeWith true` as
   hypotheses, so they do not claim more — but neither `callsAgree = true`
   nor a clean census means "every child's types are guaranteed". Unknown
   stays unknown (it is NOT turned into `false`: that would narrow what
   compiles). The census of this round reports unknown, known
   disagreements by kind, declared-vs-inlined differences and
   over-declines in separate columns.
4. **Two kinds of lemma, kept apart.**
   * *general lemma derived from types*: "for every well-typed source, the
     real reader's call kinds are the child's". Not available; §7.
   * *conditional lemma under a new runtime check*: `callWidths_of_defines`
     on `fix/call-kinds`, valid only for shapes returned under
     `callKindsDecline = true`. With the policy `false` it says nothing
     about any run.
5. **The wrapper is not needed for the census.** `Tools/ShippingCallShadow.lean`
   (this round) computes the same comparisons from the EXISTING
   `machineShape?` result and the callee constants, with no compiler edit
   and no rebuild of `Sparkle`. `fix/call-kinds` is only the place where
   the conditional lemma lives.

Files of this round (`par/b-4`): `Tools/ShippingCallShadow.lean`,
`Tests/Compiler/CallShadowCensusTest.lean`,
`Tests/Compiler/CallWidthsContractTest.lean`,
`Tests/Compiler/MachineNoneStaleRefsTest.lean`, this note.
`Tools/ShippingCallWidthsStrict.lean` (from `ebe0a1ef`) is pure Tools and
is used by the contract test; `Tools/ShippingCallKinds.lean` and
`Tests/Compiler/CallKindsCensusTest.lean` need the wrapper and belong to
`fix/call-kinds` only.

---

# Round 2 text (the isolated wrapper candidate), with corrections

The sections below describe `fix/call-kinds`. Where they said the
candidate policy "rejects nothing", read point 1 above.

## 1. What was implemented, and where the child's kinds come from

New file `Sparkle/Compiler/CallKinds.lean` (generic, no compiler import):
`Sig κ` (output ports with kinds; kinds of the hardware binders),
`entryAgrees`, `callsAgree`.

`Sparkle/Compiler/Elab.lean`, four hunks (+80 lines, 2 changed):

1. `import Sparkle.Compiler.CallKinds`; `StructEnv` gets a field
   `callSig : Name → List (Sig MixedGateBinder) := fun _ => []`.
2. before `structEnv`: `selfSig fields ci` — the signature of a constant:
   outputs by the SAME choice `machineShapeRaw?` makes (one packed `out`
   for a tuple result, else `machOuts?`), inputs the non-domain kinds of
   `mixedGatePeel (packTupleInputs value)`; `callSigsOf env c` — the
   signatures of `env.find? c` and of its unfolding
   `inlinedConst (userInliner env) ci`; `structEnv env` sets
   `callSig := callSigsOf env`.
3. `machineShape?` renamed `machineShapeRaw?` (body untouched).
4. after it: `machDeclCount`, `shapeCallsAgree`, `shapeOwnAgrees`,
   `machineShapeWith decline …`, `callKindsDecline := false`, and
   `machineShape? := machineShapeWith callKindsDecline`.

`synthesizeFromConst`, `entryConst`, the partial readers and every other
definition are textually unchanged; no Tools file unfolds `machineShape?`
(checked by `grep`: it is used as an opaque premise only), and the
generator's `MachineShape.mk` application has the same seven fields.

**Inside or after?** After — a wrapper around the raw reader, not a change
in its body. Why: the raw reader's body calls `partial` functions; anything
placed inside it is as opaque to proofs as they are, while a wrapper has
equations (`machineShapeWith_true` is proved by unfolding the wrapper
only). And the test never has to run for the shipping policy
(`false && …`).

**Where the child's shape comes from.** The parent's reader is pure over
the environment, and so is the child's signature: the callee's constant is
enough, no synthesis and no `machineShape?` of the child is run. But WHICH
constant the child's entry reads is `entryConst` — the declaration or its
unfolding, depending on the gates and on `machineShape?` itself, which
would make `structEnv` recursive through the reader. The candidate avoids
the recursion by listing BOTH signatures and asking agreement with each
that exists (`entryConst_cases`: the entry constant is one of the two;
`mem_callSig_structEnv`: so its signature is in the list).

**For which children.** `selfSig` is route-independent: it reads the
constant's type and the binder types of its value, the same expressions
whatever route the child then takes. It is `none` when a binder or the
result is not readable (non-literal width, record input …), and there is
no signature for a memory child (`env.find?` is `none`; its kinds are
written by the reader and by `memChild?` from the same two numbers).
What differs per route is the LINK from the signature to the child's
module:

| child's route | signature | link to the child's ports |
|---|---|---|
| machine | `selfSig` | `shapeOwnAgrees` (by the wrapper, under the candidate policy) to the SHAPE; from the shape to the module: the existing `ChildOutTys` / `leaf_real_outTys`, `MachineWired` |
| gate / mixed | `selfSig` (same function: `mixedGatePeel` is the mixed gate's own binder reader; outputs `[("out", kind of the result type)]`) | NOT covered: the `out` port's type is the translator's leaf wire type (`emitLeaves`); needs that route's typed-port fact |
| legacy | `selfSig` when readable | NOT covered (as above; inputs by `inferHWTypeFromSignal`) |

## 2. Statements (Tools/ShippingCallKinds.lean, Tools/ShippingCallWidthsStrict.lean)

Corrected to what the implementation gives: the hypotheses are the two
readers' results under the candidate policy and the list membership of the
child's signature; the conclusion is about hardware TYPES of kinds
(`machHWType`), with existence of the named output.

    theorem machineShape?_eq_raw … :
        machineShape? symbolicMode parameters ci senv allowInsts =
          machineShapeRaw? symbolicMode parameters ci senv allowInsts

    theorem machineShapeWith_true
        (h : machineShapeWith true symbolicMode parameters ci senv allowInsts = some sp) :
        machineShapeRaw? symbolicMode parameters ci senv allowInsts = some sp ∧
        shapeCallsAgree senv sp = true ∧ shapeOwnAgrees senv ci sp = true

    theorem callWidths_of_defines
        (hp : machineShapeWith true false [] ecP senv aP = some sp)
        (hc : machineShapeWith true false [] ecC senvC aC = some sc)
        (hk : sp.insts[k]? = some (c, args, kd))
        (hsig : ∀ s, selfSig senvC.fields ecC = some s → s ∈ senv.callSig c) :
        (∃ o ∈ sc.layout.outs, o.name = sp.instFields.getD k "out") ∧
        ∀ o ∈ sc.layout.outs, o.name = sp.instFields.getD k "out" →
          ((sp.binders.map (·.2))[machDeclCount sp + k]?).map machHWType = some o.ty

    theorem callArgs_of_defines (same hypotheses) :
        ((((sc.binders.take (machDeclCount sc)).map (·.2)).filter
            (fun k => k != MixedGateBinder.domain)).map some) =
          args.map fun a => (sp.binders.map (·.2))[machDeclCount sp +
            (sp.insts.length + sp.layout.slots.length) + a]?

    theorem argKind_at (heq : ins.map some = args.map fun a => kinds[argBase + a]?)
        (ha : args[j]? = some a) : ∃ kd, kinds[argBase + a]? = some kd ∧ ins[j]? = some kd

    theorem entryConst_cases … : entryConst … ci isInst inl projs = ci ∨ … = inlinedConst inl ci
    theorem mem_callSig_structEnv (env) (hfind : env.find? c = some ci)
        (hec : ec = ci ∨ ec = inlinedConst (userInliner env) ci)
        (hs : selfSig (structEnv env).fields ec = some s) : s ∈ (structEnv env).callSig c

`hsig` is not a renamed conclusion: it says the parent's environment lists
the signature of the constant the child's shape was read from; the last
two lemmas give it when both runs read the same environment and the child's
entry constant is `entryConst … ci …` for `env.find? c = some ci`.

NOT written (the run-level assembly): from the two `MachineDefines` of an
endpoint (parent and child) to `callWidthsStrict` / `callArgsOk` of the
reflected data. Its steps: (1) `MachineDefines` gives
`machineShape? (entryConst … ci …) (structEnv envR') = some shape` — under
the candidate policy `machineShape?` unfolds to `machineShapeWith true`;
(2) the parent's and the child's runs read the same environment for `c`
(`getConstInfo c` in the child's run against `envR.find? c` in the
parent's: a fact about the run, of the kind `RealChild` already carries —
not traced); (3) `kindTy k = machHWType k` for `k ≠ .domain` (one `cases`),
with the existing data premise that call binders are not domains;
(4) `sp.binders[i]?.map (·.2)` against `(sp.binders.map (·.2))[i]?`
(`List.getElem?_map`). Then `callWidthsStrict d nDecl (fun k => child k's
layout outs)` and `callArgsOk` hold for every pair of machine-route
declarations with no `decide`.

### The strict condition (the vacuity found in round 1)

    def callWidthsStrict (d : MachineData) (nDecl : Nat) (kidOuts : Nat → List OutField) : Bool :=
      (List.range d.shape.insts.length).all fun k =>
        (kidOuts k).all fun o =>
          (d.shape.instFields[k]?).any (fun f => o.name != f) ||
            decide ((d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
              some o.ty.bitWidth)

    theorem hkidW_strict (hcw : callWidthsStrict d nDecl kidOuts = true) (hkidT : … ChildOutTys (kidOuts k) y.1) :
        ∀ k hk y, RealChild mref cref (d.shape.insts[k]).1 y →
          ∀ p ∈ y.1.outputs, (∀ f, d.shape.instFields[k]? = some f → p.name = f) →
            (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some p.ty.bitWidth
    theorem hkidW_of_strict … : (the conclusion of hkidW_of_data, verbatim)
    theorem callWidthsOk_of_strict (hcw : callWidthsStrict d nDecl kidOuts = true) :
        callWidthsOk d nDecl kidOuts = true

Existing instances that would switch (not edited): `parent_callWidths`,
`parent_kidW_data` (`Tests/Compiler/ChecksRawTest.lean`) and through them
`parent_portsMatch_raw`; the generated endpoints that take `hkidW`.
`callArgsOk` is positional and not vacuous; what it lacks is the ARITY
(`(kidIns k).length = args.length`), which `callArgs_of_defines` gives (a
list equality) and `instStmtG` checks at the closing.

## 3. Evidence that nothing changes

Kernel-checked (once built): `machineShape?_eq_raw` — the shipping reader
is the old definition for every constant, so no existing output can move.

Measured: `Tests/Compiler/CallKindsCensusTest.lean` (logs only, pure
readers, no synthesis) evaluates the candidate policy on every declaration
of the fall-through census's population whose entry constant has a raw
shape (the 85 machine-shaped ones and those a gate also accepts): the
reader's kinds per call entry against each signature of the child, the
shape's own interface against its constant's signature, and whether
`machineShapeWith true` would return `none`. Totals line
`KINDS CENSUS: n shapes; post-pass changes k […]; …`, expected `k = 0`.
A new file rather than a column of `CallWidthHuntTest`: it needs the sweep
of `MachineFallThroughCensusTest`, which imports the hunt. SUPERSEDED for
the shipping line by `Tests/Compiler/CallShadowCensusTest.lean` (no wrapper
needed, separate columns).

## 4. The one-output closing (`instFields = []`)

The same applies, with one difference in the STATEMENT. A parent whose
calls all have one Signal result and no clock is closed by `closeInsts`
(`Sparkle/IR/Machine.lean` 272): `let [outP] := mc.outputs`, the child's
ONLY output whatever its name. There `callWidthsOk` is vacuous (the name
it tests is `""`). What `hkidW` should be for such an entry:

    ∀ p ∈ y.1.outputs,
      (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some p.ty.bitWidth

— every output port, no name condition (`hkidW_strict` with
`instFields[k]? = none`). On the reader side the field of such an entry is
`out` (`shapeCallsAgree` uses `instFields.getD k "out"`): a machine child
with one Signal result has the single layout output `out`
(`machOuts?` / the tuple case), so `callWidths_of_defines` speaks about it;
that the layout has NO other output is `shapeOwnAgrees` + `selfSig`'s
one-element list for a Signal result (`machOuts?` unfolding — not proved).
A gate child's port is `out` as well (`synthesizeMixedCertified` emits the
leaf `("out", body)`); its type is the translator's.

## 5. Finding E follow-up (paper only)

Measured: of 85 machine-shaped declarations 84 take the machine route and
1 (the constructed `pCount`: a sequential child with one Signal result,
which the one-output closing refuses) falls through; its module equals the
clean legacy run's and reads no undeclared name.

Minimal fix candidate, two forms:

* RESET (smallest): in `synthesizeFromConst`, in the `| none =>` branch
  after `machineResult?`, when `machine?` was `some`, set to empty
  `sparkleLetWireCache`, `sparkleLoopWireCache`, `sparkleWireCanon`,
  `sparkleSingleOutInstanceCache`, `sparkleSubInstanceOutputs`,
  `sparkleFvarValueMap`, `sparkleWireWidthCache` (and
  `sparkleFvarZetaVisited`, which the cache fix also treats) before the
  legacy arm's `CircuitM.init`. At depth 0 this is the state the legacy arm
  has when there is no machine shape. At depth > 0 it is also what the
  entry itself does on a nested start for five of them (5478–5487); the two
  instance caches are deliberately NOT cleared on nested entry (they carry
  the cross-module instance dedup), so for a nested fall-through a reset
  could change which instance wires a later sibling reuses.
* SNAPSHOT / RESTORE (what the cache fix does): on `fix/cache-rollback`,
  `WireCaches` / `snapshotWireCaches` / `restoreWireCaches`
  (`Elab.lean` 5580–5622 there) read and write exactly these refs (plus the
  per-run expression cache and `sparkleFvarZetaVisited`) around a `catch`
  in `CompilerM`. The same pair around the machine arm — snapshot before
  `synthesizeMachineCertified`, restore when it returns `none` — puts the
  refs back to what the legacy arm would have seen had the machine arm not
  run, at any depth, including the instance caches. They are `CompilerM`
  functions; the machine arm is in `MetaM`, so a `MetaM` twin (the same
  `get`/`set` list without the expression cache, which each arm creates
  fresh) is needed.

SNAPSHOT / RESTORE is the one consistent with the ruling on the cache fix
(same refs, same mechanism, correct for nested entries); RESET is two
lines shorter and equal to it at depth 0.

Either edits the body of `synthesizeFromConst`, which these proofs unfold
(`unfold synthesizeFromConst`): `Tools/ShippingMachineEntry.lean` 2236 (the
machine arm's lemma — it takes the `some` result
and would not see the new branch, but its `RunsTo.bind` steps follow the
text), `Tools/ShippingChildRun.lean` 355, `Tools/ShippingEntrySoundness.lean`
1021, `Tools/ShippingMixedEntrySoundness.lean` 665,
`Tools/ShippingHierTermSoundness.lean` 700, `Tools/ShippingVectorMuxSoundness.lean`
90, `Tools/ShippingRegisterSoundness.lean` (6 places),
`Tools/ShippingUnifiedExecutionSoundness.lean` 774,
`Tools/ShippingInstanceEntrySoundness.lean` (5 places),
`Tools/ShippingMemoryEntrySoundness.lean` (2 places). The legacy arm
itself is spoken about by `Tools/ShippingChildBody.lean` and
`Tools/ShippingLegacySemContract.lean` (and the G2 line on
`fix/cache-rollback`). To keep those proofs' steps unchanged the reset can
be placed so that the gate arms' text does not move (inside the existing
`| none =>` of `machineResult?`, as one `if machine?.isSome then … ;`
statement); the proofs that walk INTO the legacy arm (the last two files,
and any that reach `MEMO HIT`) gain one `RunsTo.bind` step.

---

# Round 3

## 6. The contract of the width conditions, and the audit of the existing endpoints

### What `true` means

`callWidthsOk` and `callWidthsStrict` are both of the form
"for every entry `k`, for every layout output `o` of the child that the
entry's NAME TEST selects, `o` has the width of the type of the entry's
binder". Consequently (kernel-checked in
`Tests/Compiler/CallWidthsContractTest.lean`, once built):

| situation | `callWidthsOk` | `callWidthsStrict` |
|---|---|---|
| one-output closing (`instFields = []`), the child's only output has another width | true (the name tested is `""`) | false |
| the named field is MISSING from the child's layout | true | true |
| the child's output list is EMPTY | true | true |

So neither condition says that the field exists, that a one-output child
has exactly one output, or anything about arguments. The contract:

    width agreement of a connected port
      =  [the width condition]                       -- data, per parent / child
      ∧  [the connected port is a layout output]      -- EXISTENCE, from the real closing
      ∧  [one output, on the one-output closing]      -- from the real closing
      ∧  [as many argument ports as argument wires]   -- ARITY, from the real closing

and the last three are facts of the CLOSING THAT RAN, not of the data.

### Where each is discharged today (audit, by reading and `grep`)

* Existence, G path: `instStmtG` (`Sparkle/IR/MachineInstG.lean` 39) returns
  `none` unless `fields.all (fun f => mc.outputs.any (·.name == f))`, with
  `fields[k] = shape.instFields.getD k ""` (`stmtsG`, 68) — the SAME name
  expression `callWidthsOk` tests. Proof side: conjunct 5 of `CallStmtG`
  (`Tools/ShippingMachineInstG.lean` 19), obtained from the run by
  `instStmtG_some` / `closeInstsG_insts`, i.e. from `MachineClosesAt`
  (the closing returned `some`) — a premise every closed endpoint carries
  or has discharged (`f.machine_closes`).
* Arity, G path: `instStmtG` 36 (`inPorts.length != argWs.length → none`);
  `CallStmtG` conjunct 3.
* One output, one-output path: `instStmt` (`Sparkle/IR/Machine.lean` 281,
  `let [outP] := mc.outputs | none`), arity at 276; proof side `CallStmt`
  (`Tools/ShippingMachineInst.lean`).
* Width, G path: `hkidW`, from `callWidthsOk` by `hkidW_of_data`.

Existing endpoints:

* `parent`, `chained` (G path: `instFields` non-empty). Every theorem
  through which `hkidW` flows takes `hfne : d.shape.instFields ≠ []`
  (`core_instOutWidthsOk`, `Tools/ShippingChecksWidths.lean` 279; `hfne`
  occurs in 12 Tools files: `ShippingChecksWidths`, `ChecksOuts`,
  `ChecksRaw`, `ChecksRunFacts`, `PortsMatchRaw`, `PortsMatchRawLeaf`,
  `PortsMatchShipped`, `TextShipped`, `CallsKidsD`, `CallsSeqKids`,
  `KidsPassLeaf`, `ClosedTyped`). In `core_instOutWidthsOk` the conclusion
  `instOutWidthsOk` ranges over the child's output ports that are
  CONNECTED in an instance statement of the module; a connected output
  port is a field of an entry of the group (`core_callPorts`, from
  `CallStmtG`), so its name is `instFields.getD k ""` for a real `k` and
  `hkidW` applies. A missing field cannot reach this theorem: the closing
  would have returned `none` and `MachineClosesAt` would be false. So for
  `parent` / `chained` the weak condition is used only where existence
  comes from the closing; they did NOT hold "by vacuity".
  NOT traced: that `instFields.length = insts.length` is stated anywhere
  (it holds by the reader, 5179: both lists are pushed together; the
  closing's `getD k ""` makes a shorter list fail the existence test for
  the uncovered entries).
* The one-output parents `caller`, `callerTwice`, `callerNested`,
  `callerD` (`Tests/Compiler/ShippingMachineInstTest.lean` 152–165): their
  endpoints are `#machine_endpoint` and `#machine_linked`
  (`machine_linked_calls`, with `hsimple : instFields = []`): the LINKED IR
  run, whose calls' premise is `ChildFn mc (P k) (F k)` per `CallStmt`. No
  theorem with `hkidW` / `callWidthsOk` / `instOutWidthsOk` applies to them
  (all require `hfne`), so nothing about their port WIDTHS is claimed by an
  existing endpoint — neither truly nor vacuously. A width statement for
  them is what `hkidW_strict` (its `instFields[k]? = none` case) is for;
  the theorem that would consume it (a `core_instOutWidthsOk` for the
  one-output closing) does not exist.
* `callArgsOk` is positional: `(kidIns k)[j]?` against the `let` at
  `args[j]`, for `j < (kidIns k).length`. It says nothing for `j` beyond
  the child's ports; the arity comes from `CallStmtG` conjunct 3.

## 7. The agreement proposition as reader invariants (point 2)

Proposition A: *for every environment and every pair of declarations the
real entry compiles on the machine route, parent `f` calling child `c`:
the kind of `f`'s binder of a call entry is the kind of the field of
`c`'s layout it reads, and the kinds of the entry's argument `let`s are
the kinds of `c`'s hardware binders.*

Smallest invariants it decomposes into (`Sparkle/Compiler/Elab.lean` lines
at `a9fd07ca`):

| # | invariant | function | status |
|---|---|---|---|
| R1 | the entry pushed for a one-Signal call has kind `(senv.inst c).2`, field `out` | `machInstance` 4067 | property of a `partial` function's RESULT: no equation; true by reading |
| R2 | the entries pushed for a structure call are the fields of `machOuts? senv (inst ty args)`, in order, `instFields` their names | `machInstanceS` 4086–4111 | same |
| R3 | the `let` of argument `j` has the kind of the child's `j`-th non-domain binder of `telescopeKinds c.type`, or is an existing `let` | `machInstance` / `machInstanceS` / `machLetIndex` | same; the "existing `let`" case needs T2 |
| R4 | the shape's binders at `nDecl + k` and the `let` positions carry those kinds | `machineShape?` 5164–5167 | `machineShape?` is a `def`, but its inputs here are R1–R3's results |
| P1 | `instSignature? env c = (telescopeKinds ci.type, machResultKind? ci.type)` | pure | an equation (unfold) |
| P2 | `machResultKind? t = some k → machOuts? senv t = some (none, [("out", k)])` | pure | provable by induction on `t`; NOT proved |
| P3 | `machOuts?` of the type instantiated with the call's arguments = of the type | `inst` 4081 uses `Expr.instantiate1` | `instantiate1` is an `extern` without a body in the logic: NOT provable as it stands (a pure twin, like `instFVars` 2896, would make it provable) |
| P4 | the child's layout outputs are `machOutFields … (machOuts? senv d.type)` and its binders start with `mixedGatePeel (packTupleInputs d.value)` | `machineShape?` 5061–5066, 5166, 5174 | a `def`: provable by unfolding a 130-line `do` block; NOT proved |
| P5 | the kinds of the child's type are unchanged by `userInliner` (`inlinedConst` rewrites the TYPE) where they are defined | `userInliner` 3380 | total and budgeted, but through `Expr.replace` / `headBeta`; NOT attempted |
| T1 | the `∀`-domains of `c.type` and the `λ`-domains of `c`'s value have the same kinds | `telescopeKinds` vs `mixedGatePeel` | needs the kernel's typing of the definition + claim K; NOT expressible in the present logic |
| T2 | an existing `let` reused as an argument has the kind the child expects | `machLetIndex` | needs the typing of the call + claim K; same |

So A is not "false"; it splits into (i) four facts about `partial`
results that have no equations, (ii) five pure facts of which one is
blocked by an `extern`, and (iii) two facts that ARE the kernel's typing.

### What is already kernel-checked per declaration

For a parent WITH a generated endpoint (`#machine_endpoint f`), read in
`Tools/ShippingMachineCommand.lean` 1698–1727:

* the generator RE-READS the calls of the body (`callEntriesG senv`) and
  refuses unless their number is `shape.insts.length`;
* for entry `k` of reflected kind `.bits w` it builds
  `extendBits D bits pos (lit w) (call term)`, and
  `extendBits … (w : Nat) (sig : Signal D (BitVec w))`
  (`Tools/ShippingMachineAuto.lean` 377); for `.bool`, `extendBools`. The
  endpoint is added through the kernel. Hence, per declaration:
  **the Lean type of the `k`-th call term (e.g. `(cnt en).n`) is
  `Signal D (BitVec w)` for the parent's reflected `w`** — R1/R2/R4 for
  this declaration, up to "the generator's `k`-th entry is the reader's
  `k`-th" (same reading order; NOT checked beyond the count).

For `#machine_linked f` (one-output combinational children),
`Tools/ShippingMachineLinkedCommand.lean` 228–237: the number of the call's
actual arguments equals the number of the child's reflected binders
(a generator error otherwise), and each argument `a` is observed as
`BitVec.toNat (lit w) (a.val j)` with `w` the CHILD's reflected binder
kind — kernel-checked: **the Lean type of the call's `j`-th argument is
`Signal _ (BitVec w)` for the child's reflected `w`** (T1 + R3's child
half, for this pair).

NOT opened (UNVERIFIED): how the child's own endpoint types its outputs
(the child half of the result side), and how the parent's `let` terms are
typed against the reflected `let` kinds (`readMachine`'s typed reading).

### Is "endpoint generation succeeded ⇒ strict agreement" provable?

As a statement INSIDE the logic: no, in the present setting, and for a
reason unrelated to its truth. "Generation succeeded" is the existence of
kernel-accepted constants whose TYPES mention the call term at
`BitVec w_p` and the child at `BitVec w_c`. That both typings hold forces
`w_p = w_c` only through uniqueness of types up to definitional equality
and injectivity of `BitVec` on literals (claim K) — properties of the
kernel, not theorems one can apply to two constants. Inside the logic the
strongest available object is, per pair, the closed equation
`w_p = w_c`, whose proof is `rfl` / `decide`: exactly the per-declaration
check that exists.

What CAN be said precisely:

* META-level (by the kernel's own typing): for a pair with generated
  endpoints whose statements contain both typings, the per-pair `decide`
  cannot fail. For the argument side of one-output combinational children
  this is the case today (`#machine_linked`); for the result side the
  parent half is kernel-checked and the child half is UNVERIFIED (not
  opened).
* So for declarations with endpoints, agreement is a consequence of
  something kernel-checked per declaration that is NOT the weak `decide`
  — but it is still per declaration, and it is not available as a lemma.
* A GENERAL statement needs one of: (a) equations for the readers
  (R1–R4: a non-`partial` reader, or the strict reader of G3 proved to
  agree with it), plus P2–P5 and a pure `instantiate`; and for T1/T2
  either (b) a formal typing judgment, or (c) the two sides reading the
  SAME expression (then T1 disappears — that is a reader change, not a
  lemma about today's reader).

## 8. Finding E: one shared rollback API (design; nothing implemented)

Do not duplicate the cache fix. On `fix/cache-rollback`
(`Sparkle/Compiler/Elab.lean` 5580–5622 there) `WireCaches` /
`snapshotWireCaches` / `restoreWireCaches` are `CompilerM` functions: the
`MetaM`-level part is the eight `IO.Ref`s; the `CompilerM`-only part is
the per-run expression cache (`(← getCompilerState).exprCache`).

Proposed factoring (a new small compiler file, e.g.
`Sparkle/Compiler/WireRefs.lean`, or in place):

    structure WireRefs where            -- the MetaM-level part, common to both uses
      letWire loopWire wireCanon singleOut : Std.HashMap String String
      subInstOut : Std.HashMap (UInt64 × String) String
      wireWidth : Std.HashMap String Nat
      fvarValue : Std.HashMap Lean.Name Lean.Expr
      zetaVisited : Std.HashSet Lean.Name
    def snapshotWireRefs : MetaM WireRefs
    def restoreWireRefs (r : WireRefs) : MetaM Unit

    structure WireCaches where          -- as today, by composition
      expr : Option (Lean.ExprStructMap String)
      refs : WireRefs
    def snapshotWireCaches : CompilerM WireCaches   -- expr cache + liftMetaM snapshotWireRefs
    def restoreWireCaches (c : WireCaches) : CompilerM Unit

    -- the machine arm (synthesizeFromConst), the only new use:
    let saved ← snapshotWireRefs
    let machineResult? ← …synthesizeMachineCertified…
    match machineResult? with
    | some result => …
    | none => restoreWireRefs saved; …legacy arm…

What stays as it is: `sparkleChildCache` / `sparkleSubModuleCache` (the
children the closing synthesised are full-entry RESULTS, valid whatever
the parent's builder state — the same exclusion `WireCaches` documents)
and `sparkleTypeCache`. What is restored are wire NAMES and widths, which
are module-local: after the restore every entry refers to the parent
module's own builder state before the machine arm, i.e. nothing at depth
0, and the enclosing module's entries for a nested entry.

Module-local consistency to check for the restored refs (not checked by
one example): every value of `letWire` / `loopWire` / `wireCanon` /
`singleOut` / `subInstOut` is a declared wire of the module being built;
every key of `wireWidth` that is declared has its declared width. The
measurement of this round reports the violations of these two on the
legacy arm's starting state (`letOrphan`, `clash`, `orphan`).

Proofs that unfold the affected code: the two functions of the cache fix
are unfolded by the G2 line on `fix/cache-rollback` (no Tools or Tests
file on `b0f7e915` mentions `snapshotWireCaches` / `restoreWireCaches`) —
with the composition above `snapshotWireCaches` gains one `liftMetaM` step
in place of eight; `synthesizeFromConst` is unfolded by the files listed
in §5. The §5 text "snapshot / restore … a `MetaM` twin" is replaced by
this section: one API, not a twin.

### The measurement (`Tests/Compiler/MachineNoneStaleRefsTest.lean`)

For `pCount` and two more constructed fall-throughs it runs the machine
arm from reset refs, READS the seven refs as the legacy arm would find
them, runs the legacy arm on them (`dirty`) and from reset refs (`clean`),
and reports the ref sizes, `clash` (a stale width under a name the clean
module declares at ANOTHER width), `orphan` / `letOrphan` (stale entries
naming wires the clean module does not have) and `dirty == clean`.
`pCount` showed `real == clean` in the census; that is one declaration.

What a DISCRIMINATING declaration needs, by reading:

* width cache: `makeWire`, `addInput`, `addOutput` insert the new width
  (`Elab.lean` 175–250), so a stale width is overwritten when the legacy
  arm declares that name through them. It is READ stale only if
  `getWireWidth x` is asked (a) before `x` is declared in the legacy run,
  or (b) for a name declared by a path that does not insert — a symbolic
  width (`legacyCacheWidth? (.bitVectorDim _) = none`, 173) or a wire
  added without `makeWire`. So: a `clash` name that the legacy arm slices
  or concatenates (the handlers that call `getWireWidth`) before
  re-declaring it.
* `let`-wire / loop-wire cache: the key is the value's structure plus the
  wires its free variables denote. The harness translated the TRANSITION
  (slots and call results as input ports), the legacy arm translates the
  original body (registers, instances); a hit needs a hardware `let`
  whose value mentions only declaration INPUTS (same port names in both
  runs) and is structurally the same in both — e.g. `let t := x + y` over
  two inputs, used by the legacy arm AFTER the fall-through. Then the hit
  returns the harness module's wire name for `t`; if the legacy module's
  counter has not produced that name (or produced it for something else)
  the module reads an undeclared or a wrong wire. `eWide` has such a
  `let` only over a register read (`rs + x`), which the two runs name
  differently; `eIn` (a `let` over two INPUTS, a one-output sequential
  child) is the candidate written for this case — its outcome is not
  predicted (the key function was not opened).

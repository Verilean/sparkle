# G1: `portsMatchB` (conjunct 7 of `textCheckI`) — inventory (round optfb-6)

Status: read from the definitions; one pure lemma written
(`Tools.ShippingTextShipped.portsMatchB_of`, NOT built). Nothing below is
derived from a run. Items marked "not traced" were not read to the bottom.

## Definition (`Tools/ShippingDesignSV.lean` 57–70)

    PortsMatch C o : Prop :=
      ∀ mn iname conns child cwe, Stmt.inst mn iname conns ∈ o.body → C mn = some (child, cwe) →
        ∀ c ∈ conns, ∀ w, c.2 = .ref w → weS o w = weS child c.1

    portsMatchB C o : Bool :=
      o.body.all (inst mn _ conns ⇒ match C mn with
        | some (child, _) ⇒ conns.all (c ⇒ match c.2 with | .ref w ⇒ weS o w == weS child c.1 | _ ⇒ true)
        | none ⇒ false)

`weS m x = (moduleWof m x).getD 0`: the EMITTER's width of `x` in `m` —
wires ++ inputs ++ outputs by sanitized name, `0` when undeclared. Per
connection `(port, .ref w)` of an instance of `child`:

    weS o w = weS child port

for EVERY connection whose expression is a reference — output connections
(the child drives `w`) and input connections (the parent drives the child's
`port`, `clk`, `rst`) alike. A connection that is not a reference is not
tested. `portsMatchB_sound` (existing) is Bool ⇒ Prop;
`portsMatchB_of` (this round) is Prop ⇒ Bool given that every instance
resolves in `C` (`core_design_resolve`).

## The four quantities, and what covers each

| Quantity | Module | Existing fact | Gap |
|---|---|---|---|
| (a) `weS o w`, `w` an instance OUTPUT wire | parent | on `b`: `RunFacts.wid` — `instOutWidthsOk C (declWidth b) b.body`: `declWidth b w = p.ty.bitWidth` for the child's output port `p` connected to `w`; `w` is a wire (`RunFacts.outs`), so `weS b w = declWidth b w` by `pos_wire` / `declWidth_eq_weS` with `TypedIn.wn` | none on `b` (assembly not written). On an accepted candidate `o'`: `o'.wires` is a sublist of `b.wires` and the instance statements are `b`'s (`checkedOptimize_inst_iff_gate`), `hierRefineCheck` forbids `o'` to drive an extracted input; that `w` is still DECLARED in `o'` (the candidate's wire filter keeps it) — not traced |
| (b) `weS child p.name`, `p` an OUTPUT port of the child | child | `Tools.ShippingTextTyped.moduleWof_output`: `some p.ty.bitWidth` when no wire / input of the child has `p.name` as sanitized name, the output names are stable and distinct, `p` scalar — the fields `ow`, `oi`, `ostable`, `ond`, `oty` of `TypedIn child` | `TypedIn child` for a real child. For a child that is itself a machine with calls: `core_closed_typedIn` (round optfb-5). For a LEAF child (register machine without calls: `cnt`): the same chain with `M = closeMachine lay t'` — `closeMachine_typed` applies, the run-level assembly for `insts = []` is NOT written. `ChildOutTys` gives the ports and their types only |
| (c) `weS o w`, `w` an ARGUMENT wire (a `let` wire) | parent | `w` is a `let` port of the transition: a wire declared at its binder's type (`transitionPortTys_of_run`), kept by the closings; on `b`: `weS b w = (kindTy binder).bitWidth` by `pos_wire` | on `b`: assembly not written (which connection carries which `let`: `CallStmtG`'s argument connections — not traced). On `o'`: `connAgreeOk b o'` says a connected wire is an output / extracted output of `b` or is driven by neither body; it does not say the connection expression is still the same reference nor that it is declared at the same width in `o'` — not traced |
| (d) `weS child q.name`, `q` an INPUT port of the child (argument ports, `clk`, `rst`) | child | none found. `moduleWof child q.name` is the first of wires ++ inputs ++ outputs with that sanitized name: for a machine child the argument ports are ALSO wires (allocated names, `PrintBaseAt.inputWires`), so it is the wire's type; `clk` / `rst` are inputs only | (i) the child's argument port has the type of the child's binder (`transitionPortTys_of_run` on the CHILD, positions `< machNIn`: its statement covers the binders from `nDecl` on only); (ii) **nothing compares the parent's `let` width with the child's binder width** — this is gap (E) of round optfb-3, the argument-side analogue of finding (A) (`instOutWidthsOk` is checked by no compiler pass). `callWidthsOk` (`Tools/ShippingCallWidths.lean`) is the data condition for the RESULT side only |

So, per side:

* OUTPUT connections on `b`: (a) and (b) are within reach from existing
  facts — two assemblies, no new theory, given `TypedIn` of the child.
* INPUT connections on `b`: (c) is an assembly; (d)(ii) is a real missing
  fact about the declaration PAIR (parent argument width = child binder
  width). It is decidable per parent/child pair from the two
  `MachineData` (as `callWidthsOk` is for results); the statement would be

      argWidthsOk parent child : Bool    -- for every call entry k and argument position j:
        machWidth (parent's let binder of argument j) = machWidth (child's binder j)

  and nothing in the compiler checks it (to be confirmed by reading the
  call reader; not traced this round). `clk` / `rst`: one bit on both sides
  (`closeMachine` declares them `.bit`; the parent's `clk` / `rst` are
  inputs of type `.bit`).
* On an ACCEPTED candidate: all four need "the candidate declares the
  connected wires as `b` does". The print guard does not test connections
  (`seqText` skips instance statements). Two ways, as for conjuncts 2–3: a
  derivation from `hierRefineCheck`'s `instsKept` (the instance statements
  are `b`'s, literally — then only `weS o' w = weS b w` on connected wires
  is needed, i.e. the wires are kept with their types and no port of the
  same sanitized name shadows them), or one more guard conjunct:

      connected wires of the candidate have the widths they have in the input module
        o.body.all (inst _ _ conns ⇒ conns.all ((_, .ref w) ⇒ weOf o w == weOf m w))

  which is design-free (it compares `o` with `m`, not with the child), so
  it fits `keepGuarded`. Not implemented; a decision for the user.

## What is stated in Lean

    theorem portsMatchB_of (h : PortsMatch C o)
        (hres : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → (C mn).isSome = true) :
        portsMatchB C o = true                                  -- Tools/ShippingTextShipped.lean

`core_portsMatch_of` — the run-level statement asked for — is NOT written:
with (d)(ii) and the candidate-side fact as hypotheses its premise would be
`PortsMatch` restricted to input connections of the shipped module, which
only renames the conclusion. The honest form needs the two assemblies
above first:

    theorem core_portsMatch_raw (… core_runFacts' hypotheses …)
        (hkidT : ∀ k y, RealChild … y → TypedIn y.1)                 -- (b)
        (hargs : argWidthsOk-style data condition per call entry)    -- (d)(ii)
        (hkidIn : ∀ k y, RealChild … y → the child's argument ports are wires of their binders' types) -- (d)(i)
        : portsMatchB (childMap D.modules) b = true

for the RAW module `b`, and then either the derivation or the guard
conjunct above for the shipped one.

## Remaining hypotheses of `designCheck` after this round

`core_designCheck_rest2` / `core_designCheck_run`
(`Tools/ShippingTextShipped.lean`): `hports` (this note) and `hkids` (the
children: `kidsPass C (kidCheck C n) (checkedOptimize b).body`).

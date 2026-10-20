# Port matching and the children's check: state after round par/a-2 (worker A)

Nothing here was built. Sources read: `Tools/ShippingPortsMatchRaw.lean`
(header, 436–500), `docs/parallel/G1-portsMatch.md`,
`Tools/ShippingChecksDepthGate.lean`, `Tools/ShippingGuardsSound.lean` 291–297,
`Tools/ShippingKidsPassLeaf.lean`, `Tools/ShippingChecksDesign.lean` 119–129.

## 1. Port matching

### Done this round

* Guard G5 in `keepGuarded` (`Sparkle/IR/HierCheck.lean`, its own commit):

      connsKept m o := o.body.all (inst _ _ conns ⇒
        conns.all ((_, .ref w) ⇒ PrintGuard.weOf o w == PrintGuard.weOf m w))

  a kept candidate declares every connected wire at the emitted width the
  input module gives it; otherwise the input module is shipped.
* `Tools/ShippingPortsMatchShipped.lean`: `checkedOptimize_conns` (under
  `hierGate b`: `checkedOptimize b = b ∨ connsKept b (checkedOptimize b)`),
  `portsMatchB_shipped` (pure: `hierGate b → portsMatchB C b = true →
  portsMatchB C (checkedOptimize b) = true`), `core_portsMatch_shipped`
  (`core_portsMatch_raw`'s hypotheses, conclusion on the shipped module).

So the SHIPPED module's port matching is now exactly as far as the RAW
module's: what is open is open in `core_portsMatch_raw`.

### NOT done: the three underived hypotheses of `core_portsMatch_raw`

They are still hypotheses of `core_portsMatch_shipped`. I did not write
them: each needs the positional clauses of `MachineWired` (an anonymous
tuple of eleven or more conjuncts, read by position in every existing
proof) and `closeMachine`'s definition, none of which I read to the bottom
this round, and a wrong position is not something I can see without a
build. The exact statements to prove (for a parent `d` whose children are
leaf machines with a register, `kd` the child's data):

    -- (d)(i): the child's j-th argument port has its binder's emitted width
    leaf_real_inWidths (… leaf_real_typedIn's hypotheses for the child …)
        {y : Res} (h : RealChild mref cref c y) :
        ∀ (j : Nat) (q : Port), (inPortsOf y.1)[j]? = some q →
          ∃ wd, (kd.shape.binders.filter (·.2 ≠ .domain) |>.map (machWidth ·.2))[j]? = some wd ∧
            weS y.1 q.name = wd

    -- clock / reset of a leaf child with a register
    leaf_real_clk (…) (hsl : kd.shape.layout.slots ≠ []) {y} (h : RealChild mref cref c y) :
        weS y.1 "clk" = 1 ∧ weS y.1 "rst" = 1

    -- clock / reset of the parent's full-entry module
    core_clk (… core_closed_typedIn's hypotheses …) (hsl : d.shape.layout.slots ≠ []) :
        weS b "clk" = 1 ∧ weS b "rst" = 1

  Recipe (previous worker's, unchanged): `MachineWired`'s clause
  `m.inputs.filter … = machPorts …` and `inputPorts_typesD` for the
  argument ports; each is also a wire of that type (the leaf clause), and
  `pos_wire` turns the wire-table width into the emitted one; for `clk` /
  `rst`, `closeMachine` adds them as `.bit` inputs to a machine with slots,
  no wire has those names (`not_allocated_clk`, `nextName_ne_clk`) and no
  earlier input has that sanitized name. The cleanup and the checked merge
  keep ports and wires (`dropZW_inputs`, `mergeChecked_ports` — unchanged by
  the print guard), so the facts transfer from the closed machine to `y.1`
  / `b` as `PortsIn` does in `leaf_run_typedIn`.
  The `kidIns` of `callArgsOk` is then `fun k => the list above for entry k`
  (decidable by `decide`, as `callWidthsOk`).

  With the three, `core_portsMatch_raw_leaf` is `core_portsMatch_raw` with
  `hkidT := leaf_real_portsIn`, `hkidIn := leaf_real_inWidths`,
  `hkidClk := leaf_real_clk`, `hclkB := core_clk`, and
  `core_portsMatch_shipped` gives the shipped module.

### NOT done: `#machine_no_ports`

Not written: without the three facts its endpoint would keep them as
premises (not allowed ones), which is not the deliverable. Its shape, once
they exist: `Tools/ShippingNoKidsCommand.lean` copied, the head
`machine_design_noKids` copied once more without the `portsMatchB`
antecedent (`hDesign` then concludes `designCheck` with no check premise),
`f.machine_designP{n}` := `f.machine_designK{n}` applied to
`core_portsMatch_shipped` at `f`'s data (data conditions `callArgsOk`,
`callWidthsOk` by `decide`; per child the three leaf facts). The expected
remaining premise list of `parent` / `chained`: the run, the reflections
(`MachineDefines` of the parent and of each called declaration), `ChildBnd`.

## 2. `kidsPass` for a child WITH calls (grand → mid → cnt; topD2)

`kidsPass C f body` asks `f child` of each instance's child, with
`f = kidCheck C n`: `leafCheck` at `n = 0`, `designCheck C k` at `n = k + 1`.
`core_kidsPass_leaf` takes, per real child `y`,

    hkidK : (∀ C n, kidCheck C n y.1 = true) ∧ ∀ g ∈ y.2.modules, ∀ C n, kidCheck C n g = true

which a leaf satisfies for EVERY `C` and `n` (its check never consults `C`).
For a child with calls that is false twice: at `n = 0` (`leafCheck` refuses
an instance statement), and for a `C` that does not hold the child's own
children. What `hkidK` must become, for the parent's design `D` and a depth
`n` not below the child's:

    hkidD : ∀ k (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      kidCheck (childMap D.modules) n y.1 = true

(the second conjunct goes: `kidsPass` asks only of DIRECT children; the
grandchildren are asked inside `designCheck (childMap D.modules) (n - 1) y.1`).

For a child with calls, `kidCheck C (m + 1) y.1 = designCheck C m y.1 =
textCheckI C y.1 && kidsPass C (kidCheck C m) y.1.body`
(`Tools.ShippingChecksDesign.designCheck_eq`). Three things are missing:

1. **`designCheck` of the RAW module.** The child's module in the parent's
   design is its FULL-ENTRY module `y.1` — unoptimized — while
   `core_designCheck_run` concludes about `checkedOptimize b`. Needed:

       core_designCheck_raw (… core_designCheck_run's hypotheses …) (n : Nat)
           (hports : portsMatchB (childMap D.modules) b = true)
           (hkids : kidsPass (childMap D.modules) (kidCheck (childMap D.modules) n) b.body = true) :
           designCheck (childMap D.modules) n b = true

   Its pieces exist for `b`: `core_text_raw` (the text check and the width
   tables of `b`), `RunFacts` (`linkedWF`, distinct instance names,
   `noSelfRead`), `core_design_resolve`, `core_portsMatch_raw` (with the
   three facts of section 1), and `core_kids_facts` for the children; the
   assembly through `designCheck_eq` is not written.
2. **The child map.** The child's facts are about its OWN core design
   (`childMap y.2.modules`, from `RealChild` / `kidsChild_of_real`); the
   parent asks at `childMap D.modules`. Needed: a congruence

       designCheck_congr : (∀ mn, mn instantiated in m or below → C mn = C' mn) →
         designCheck C n m = designCheck C' n m

   and the agreement of the two maps on those names from the run (the
   depth run already carries `ExtendsAway raw.name (childMap D.modules)
   (childMap dsn.modules)`, `Tools/ShippingMachineDepthRun.lean` 75–82, for
   the semantic side; the same fact serves here).
3. **The depth.** The statement is an induction on the hierarchy depth:
   depth 0 is `core_kidsPass_leaf` (with `leaf_real_kidK_reg`), depth
   `k + 1` uses 1 and 2 at each child with its own `hkidD` at depth `k`.
   The generator has to emit it per declaration bottom-up, as
   `#machine_composedN` does for the semantic side (`grandH` 1, `topD2` 2).

Until then `core_kidsPass_leaf` and `#machine_no_kids` cover parents whose
children are leaves with a register (`parent`, `chained`); `grand`, `grandH`,
`topD2`, `mixD1` keep `kidsPass` as an antecedent.

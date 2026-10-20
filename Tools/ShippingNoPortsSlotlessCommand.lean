import Tools.ShippingNoPortsKidsCommand
import Tools.ShippingSlotlessKidFacts

/-! # `#machine_no_ports_seq f n`: the check-free depth endpoint of a parent of leaf register machines, WITH OR WITHOUT a register of its own (G1, unit U5a, round par/a-21)

`#machine_no_ports` (`Tools/ShippingNoPortsCommand.lean`) and
`#machine_no_ports_kids` (`Tools/ShippingNoPortsKidsCommand.lean`) — both
BUILT, not edited — REFUSE a parent without a register: the theorems they
apply ask `d.shape.layout.slots ≠ []` (the parent's `clk` / `rst` from its
own register). `Tools/ShippingSlotlessKidFacts.lean` (BUILT) states the two
run theorems concerned with

    hck : d.shape.layout.slots ≠ [] ∨ SeqKid mref cref d

This command is the leaf-children generator with that disjunction, and it
discharges it ALWAYS by the second disjunct: every callee in its scope is a
leaf REGISTER machine, hence sequential (`seqKid_of_leafAt` at call entry
0). Whether the parent has a register is not read by any generated proof.
It generates

    f.machine_design_noPortsNR{n}   (and its `_closed` form)

for a parent under the general closing whose every distinct callee is a
leaf register machine with `k.machine_closes`.

Generated, in this order:

    k.machine_leafKid         per distinct callee — the BUILT Tools.ShippingNoPortsCommand.leafKidTheorem
    f.machine_kidsK{n}        KidFacts of every call entry's callee — the BUILT Tools.ShippingNoPortsKidsCommand.kidsTheorem
    f.machine_seqKidS         SeqKid mref cref f.machineData — NEW (seqKid_of_leafAt at entry 0)
    f.machine_runFactsK{n}    kids_runFactsS   at Or.inr (f.machine_seqKidS …) — NEW
    f.machine_designPK{n}     kids_designCheckS at Or.inr (f.machine_seqKidS …) — NEW
    f.machine_outsGK{n}       kids_outsCheck — the BUILT runTheorems
    f.machine_maskedGK{n}     kids_maskedN   — the BUILT runTheorems
    f.machine_design_noPortsNR{n}          the BUILT endpointTerm (no gate binder)
    f.machine_design_noPortsNR{n}_closed   the BUILT closedTerm, if f.closes_deep or f.machine_closes_at exists

## How the BUILT generator is reused

`Tools.ShippingNoPortsKidsCommand.runTheorems` generates each of its four
theorems only if its name is absent. The two that ask the parent's register
(`…_runFactsK{n}`, `…_designPK{n}`) are generated HERE first, under the same
names and with the same statements (binders `hcore hpost entry closes hB`
and the callees' reflections), from the `…S` theorems; `runTheorems` then
adds the other two, which have no hypothesis on the slots. If one of the
two names EXISTS before this command (an earlier `#machine_no_ports_kids`
on a register parent), it is kept and the log line says `EXISTING` — never
silently. `Ctx`, `kidsTheorem`, `endpointTerm`, `closedTerm`,
`addOrCompare` are imported; the two quotations of this file are those of
`runTheorems` with `kids_runFacts` / `kids_designCheck` and their `hsl`
argument replaced.

## The compare path (never a silent return)

As `#machine_no_ports_kids` (`addOrCompare`, BUILT): if the endpoint (resp.
its `_closed`) EXISTS, it is rebuilt all the same, added as `…_regen`
(kernel-checked), and its statement must be `isDefEq` the existing one — an
ERROR otherwise. The log says `REBUILT … isDefEq` or `GENERATED`.

## Scope (anything else REFUSED with its reason, `scopeS`)

* not a machine with an endpoint; no call;
* a MEMORY child (no `KidFacts` for it: the memory heads are
  `Tools/ShippingMemOnlyCloses.lean`'s);
* a parent WITHOUT a register whose callees are ALL combinational (gate
  children, or machines without a register and without calls): NOT
  COVERED — nothing gives the parent's `clk` / `rst`, and the head's reset
  premise (`RunFacts.rst`) has to change (`docs/parallel/A-oneout.md` §13);
* a parent under the one-output closing (`instFields = []`);
* a callee without a machine endpoint; a callee with calls of its own
  (`LeafKid.leaf`; `#machine_no_ports_deep` is the command for a register
  parent of such callees); a callee without a register; a leaf callee
  without `k.machine_closes`;
* no depth endpoint `f.machine_ships_hierNR{n}`.

WRITTEN, NOT BUILT. -/
namespace Tools.ShippingNoPortsSlotlessCommand
open Lean Meta Elab Command
open Tools.ShippingShipsFreeCommand (checkMade)

private def nm (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)

private def noAsync {α : Type} (x : CommandElabM α) : CommandElabM α :=
  withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false }) x

/-- `k` has the three constants `#machine_endpoint` leaves. -/
def hasEndpoint (k : Name) : CommandElabM Bool := do
  let env ← getEnv
  return env.contains (k ++ `machineData) && env.contains (k ++ `machine_ok) &&
    env.contains (k ++ `machine_body)

/-- The scope, with its reasons: the reading of `f`, its call entries'
callees, the distinct callees (all leaf register machines). -/
def scopeS (f : Name) :
    CommandElabM (Tools.ShippingMachineCommand.Read × List Name × List Name) := do
  let isMachine ← hasEndpoint f
  unless isMachine do
    throwError "{f}: not a machine with an endpoint (no {f}.machineData / machine_ok / machine_body: #machine_endpoint was not run on it)"
  let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine f
  let calls := r.shape.insts.map (·.1)
  if calls.isEmpty then throwError "{f}: no call (nothing to match: no instance statement)"
  let kids := calls.eraseDups
  for k in kids do
    if (Sparkle.Compiler.MachMemory.memChild? k).isSome then
      throwError "{f}: {Tools.ShippingMachineCommand.memNameRefusal r.shape k "no KidFacts for a memory: the memory parents have their own heads, Tools/ShippingMemOnlyCloses.lean and the seqMem test; not generated here"}"
  -- the combinational callees: gate children, and machines without a
  -- register and without calls
  let mut comb : List Name := []
  for k in kids do
    let isMachine ← hasEndpoint k
    let isGate := (← getEnv).contains (k ++ `gate_peel)
    if isMachine then
      let cr ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine k
      if cr.shape.layout.slots.isEmpty && cr.shape.insts.isEmpty then comb := comb ++ [k]
    else if isGate then comb := comb ++ [k]
  if r.shape.layout.slots.isEmpty && comb.length == kids.length then
    throwError "{f}: NOT COVERED — a parent without a register whose callees {kids} are all combinational: neither a register of its own nor a sequential child gives the parent's clk / rst (hck : slots ≠ [] ∨ SeqKid has no true disjunct), and the head's reset premise (RunFacts.rst) would have to change — needs a head change (docs/parallel/A-oneout.md §13)"
  if r.shape.instFields.isEmpty then
    throwError "{f}: a parent under the one-output closing (instFields = []; kids_* ask the general closing — #machine_oneout_any is the command for it)"
  for k in kids do
    let isMachine ← hasEndpoint k
    unless isMachine do
      throwError "{f}: the callee {k} has no machine endpoint (a gate child of a general-closing parent, or #machine_endpoint was not run on it: no data for LeafKid)"
    let cr ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine k
    unless cr.shape.insts.isEmpty do
      throwError "{f}: the callee {k} has calls of its own (LeafKid.leaf asks shape.insts = []; this command generates for LEAF callees only — #machine_no_ports_deep is the command for a parent with a register, and a parent without a register over such a callee is not derived)"
    if cr.shape.layout.slots.isEmpty then
      throwError "{f}: the callee {k} has no register (LeafKid.slots asks one; a combinational child next to a sequential one is not generated here)"
    unless (← getEnv).contains (k ++ `machine_closes) do
      throwError "{f}: the leaf callee {k} has no {k}.machine_closes (its closing in every context is not derived)"
  return (r, calls, kids)

/-- **`f.machine_seqKidS`, generated**: call entry 0 of `f` is a sequential
child (`seqKid_of_leafAt`; its callee's `machine_leafKid`). Binders: the
reflections of the distinct callees (`Ctx.binders`). -/
def seqKidTheorem (c : Tools.ShippingNoPortsKidsCommand.Ctx) : CommandElabM Name := do
  let name := c.f ++ `machine_seqKidS
  if (← getEnv).contains name then return name
  let data := nm c.f "machineData"
  let k0 := c.calls[0]!
  let k0q : Term := quote k0
  let j := c.kids.idxOf k0
  -- the callee of entry 0, decided on the reflected data by a CLOSED
  -- statement over the entries (`h0` is a local hypothesis: a statement
  -- mentioning it could not be decided). One callee: every entry's callee
  -- (the built `kidsTheorem`'s `hall`); several: the entries with `k = 0`.
  let heT : Term ← if c.kids.length == 1 then
      `((by decide : ∀ (k : Nat) (hk : k < ($data).shape.insts.length),
          (($data).shape.insts[k]).1 = $k0q) 0 h0)
    else
      `((by decide : ∀ (k : Nat) (hk : k < ($data).shape.insts.length),
          k = 0 → (($data).shape.insts[k]).1 = $k0q) 0 h0 rfl)
  let bs ← c.binders
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    set_option maxHeartbeats 4000000 in
    theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State} $bs* :
        Tools.ShippingSlotlessClk.SeqKid mref cref $data := by
      have h0 : 0 < ($data).shape.insts.length := by decide
      have he : (($data).shape.insts[0]'h0).1 = $k0q := $heT
      refine Tools.ShippingSlotlessClk.seqKid_of_leafAt (mctx := mctx) (cctx := cctx) 0 h0
        (dk := $(nm k0 "machineData")) ?_
      rw [he]
      exact $(nm k0 "machine_leafKid") $(Tools.ShippingNoPortsKidsCommand.Ctx.hR j)))
  checkMade name before
  return name

/-- **`f.machine_runFactsK{n}` and `f.machine_designPK{n}`, generated from
the `…S` theorems** at the second disjunct (`Or.inr (f.machine_seqKidS …)`):
the names, binders and statements of
`Tools.ShippingNoPortsKidsCommand.runTheorems`, which then leaves them
alone. Returns, per name, whether it was generated HERE (`false`: it
existed). -/
def seqRunTheorems (c : Tools.ShippingNoPortsKidsCommand.Ctx) (kidsN seqN : Name) : CommandElabM ((Name × Bool) × (Name × Bool)) := do
  let f := c.f
  let data := nm f "machineData"
  let fq : Term := quote f
  let nLit := Syntax.mkNumLit (toString c.n)
  let nDecl := Syntax.mkNumLit (toString c.nDecl)
  let kidOuts ← c.kidOuts
  let kidIns ← c.kidIns
  let bs ← c.binders
  let hs := c.hyps
  let kidsI := mkIdent (`_root_ ++ kidsN)
  let seqI := mkIdent (`_root_ ++ seqN)
  let ok := nm f "machine_ok"
  let body := nm f "machine_body"
  let facts := f ++ Name.mkSimple s!"machine_runFactsK{c.n}"
  let design := f ++ Name.mkSimple s!"machine_designPK{c.n}"
  let mut factsNew : Bool := false
  let mut designNew : Bool := false
  unless (← getEnv).contains facts do
    let before := (← get).messages.toList.length
    elabCommand (← `(command|
      set_option maxHeartbeats 4000000 in
      theorem $(mkIdent (`_root_ ++ facts)) {mctx : Lean.Meta.Context}
          {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
          {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
          {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
          (hcore : Tools.ShippingEntrySoundness.RunsTo
            (Sparkle.Compiler.Elab.synthesizeCombinationalCore $fq [] false)
            mctx mref cctx cref w (raw, D) w1)
          (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
            b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
          (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $fq ($data).shape)
          (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $fq ($data).shape)
          (hB : Tools.ShippingChildInv.ChildBnd mref cref w) $bs* :
          Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
        Tools.ShippingSlotlessKidFacts.kids_runFactsS (nDecl := $nDecl) $data $ok $body
          (by decide) (by decide) (by decide)
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (Or.inr ($seqI $hs*))
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (by decide) (by decide)
          $kidOuts $kidIns $nLit ($kidsI $hs*)
          (show Tools.ShippingCallWidths.callWidthsOk $data $nDecl $kidOuts = true from by
            first | decide | decide +kernel)
          hB hcore hpost entry closes))
    checkMade facts before
    factsNew := true
  unless (← getEnv).contains design do
    let before := (← get).messages.toList.length
    elabCommand (← `(command|
      set_option maxHeartbeats 4000000 in
      theorem $(mkIdent (`_root_ ++ design)) {mctx : Lean.Meta.Context}
          {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
          {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
          {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
          (hcore : Tools.ShippingEntrySoundness.RunsTo
            (Sparkle.Compiler.Elab.synthesizeCombinationalCore $fq [] false)
            mctx mref cctx cref w (raw, D) w1)
          (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
            b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
          (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $fq ($data).shape)
          (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $fq ($data).shape)
          (hB : Tools.ShippingChildInv.ChildBnd mref cref w) $bs* :
          Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules)
            $nLit (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
        Tools.ShippingSlotlessKidFacts.kids_designCheckS (nDecl := $nDecl) $data $ok $body
          (by decide) (by decide) (by decide)
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (Or.inr ($seqI $hs*))
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (by decide) (by decide)
          $kidOuts $kidIns $nLit ($kidsI $hs*)
          (show Tools.ShippingCallWidths.callWidthsOk $data $nDecl $kidOuts = true from by
            first | decide | decide +kernel)
          (show Tools.ShippingPortsMatchRaw.callArgsOk $data $nDecl $kidIns = true from by
            first | decide | decide +kernel)
          hB hcore hpost entry closes
          (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
            ((show ∀ o ∈ ($data).shape.layout.outs, ∀ c ∈ o.name.toList,
                Sparkle.IR.NameHints.charOk c = true from by
              first | decide | decide +kernel) o ho))
          (by decide)))
    checkMade design before
    designNew := true
  return ((facts, factsNew), (design, designNew))

/-- The endpoint, its closed form, and the log line. -/
def noPortsSeq (f : Name) (n : Nat) : CommandElabM Unit := do
  let (r, calls, kids) ← scopeS f
  let ships := f ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  unless (← getEnv).contains ships do
    throwError "{f}: no depth endpoint at depth {n} ({ships} is not there: run #machine_design_svNR {f} {n} first)"
  for k in kids do
    discard <| noAsync (Tools.ShippingNoPortsCommand.leafKidTheorem k)
  let c : Tools.ShippingNoPortsKidsCommand.Ctx :=
    { f, n, nDecl := r.nDecl, calls,
      kinds := (kids.map fun k => (k, Tools.ShippingNoPortsKidsCommand.Kind.leaf)),
      gates := [] }
  let kidsN ← noAsync (Tools.ShippingNoPortsKidsCommand.kidsTheorem c)
  let seqN ← noAsync (seqKidTheorem c)
  let ((factsS, factsNew), (designS, designNew)) ← noAsync (seqRunTheorems c kidsN seqN)
  -- the BUILT generator: the two theorems above exist, it adds the output
  -- check and the children's bound (no hypothesis on the slots)
  let (facts, outs, masked, design) ←
    noAsync (Tools.ShippingNoPortsKidsCommand.runTheorems c kidsN)
  unless facts == factsS && design == designS do
    throwError "{f}: the built runTheorems names its theorems {facts} / {design}, not {factsS} / {designS} (the reuse of this file is wrong)"
  let name := f ++ Name.mkSimple s!"machine_design_noPortsNR{n}"
  let (openC, line1) ← liftTermElabM <|
    withOptions (fun o => Lean.Elab.async.set o false) do
      let (type, value) ←
        Tools.ShippingNoPortsKidsCommand.endpointTerm f [] n facts outs masked design
      Tools.ShippingNoPortsKidsCommand.addOrCompare name type value
  let mut lines := #[line1]
  let env ← getEnv
  let cl? : Option Name :=
    if env.contains (f ++ `closes_deep) then some (f ++ `closes_deep)
    else if env.contains (f ++ `machine_closes_at) then some (f ++ `machine_closes_at)
    else none
  match cl? with
  | none =>
    lines := lines.push s!"NO CLOSED FORM: neither {f}.closes_deep nor {f}.machine_closes_at exists"
  | some cl =>
    let closedN := Tools.ShippingMachineClosesGen.closedName name
    let (_, line2) ← liftTermElabM <|
      withOptions (fun o => Lean.Elab.async.set o false) do
        let (type, value) ← Tools.ShippingNoPortsKidsCommand.closedTerm f openC cl 0
        Tools.ShippingNoPortsKidsCommand.addOrCompare closedN type value
    lines := lines.push (line2 ++ s!" (closing: {cl})")
  let word (b : Bool) : String :=
    if b then "GENERATED here from the S theorem at Or.inr (SeqKid)"
    else "EXISTING before this command (NOT regenerated; its proof is whatever made it)"
  let c0 : Name := calls[0]!
  let slotWord : String :=
    if r.shape.layout.slots.isEmpty then "WITHOUT a register"
    else s!"with {r.shape.layout.slots.length} register slot(s)"
  logInfo m!"NOPORTS SEQ {f} at depth {n}: {String.intercalate "; " lines.toList}. Parent {slotWord}; callees (leaf register machines) {kids}; call entries {calls}. The depth endpoint without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents. hck : slots ≠ [] ∨ SeqKid discharged by the SECOND disjunct, {seqN} (seqKid_of_leafAt at entry 0, callee {c0}), whatever the parent's slots. Run facts by {facts} — {word factsNew}; designCheck by {design} — {word designNew}; output check under the gate by {outs} and children's bound by {masked} (the built runTheorems: kids_outsCheck, kids_maskedN); KidFacts of the entries by {kidsN} (the built kidsTheorem)"

/-- `#machine_no_ports_seq f n`: an error where it is refused. -/
elab "#machine_no_ports_seq " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  noPortsSeq f n.getNat

/-- The same, a refusal LOGGED (`NOPORTS SEQ REFUSED`) instead of thrown; a
refused declaration leaves nothing in the environment. -/
elab "#machine_no_ports_seq_try " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  try
    noPortsSeq f n.getNat
  catch ex =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    logInfo m!"NOPORTS SEQ REFUSED {f} at depth {n.getNat}: {ex.toMessageData}"

end Tools.ShippingNoPortsSlotlessCommand

import Tools.ShippingOneOutGenCommand
import Tools.ShippingLeafOneOut
import Tools.ShippingLeafOneOutGen
import Tools.ShippingCallWidthsStrict

/-! # `#machine_oneout_any f`: the one-output head's lemmas GENERATED, for callees that are gate children OR slotless leaf machine children (G1, round par/a-11)

`#machine_oneout f` (`Tools/ShippingOneOutGenCommand.lean`, BUILT, not
edited) refuses a machine-route callee. This command is that generator with
ONE more callee kind. It reuses that file's `emit`, `emitOrVerify`, `mkThm`,
`perEntry` and `endpoint` unchanged (imported, not copied); the scope test
and the generation are written again here, the gate branch copied.

## Scope (anything else is REFUSED, with its reason, before anything is generated)

The parent `f`, as in `#machine_oneout`:
* `f.machine_ships_hierHR`, `f.machineData`, `f.machine_ok`, `f.machine_body`;
* a machine shape with at least one call;
* the parent HAS a register: `shape.layout.slots ≠ []` (the head asks
  `"rst" ∈ b.inputs`). A slotless parent is REFUSED;
* `shape.instFields = []`: the ONE-OUTPUT closing `closeInsts`;
* no callee is a memory module.

Each distinct callee `c` is of ONE of two kinds (the test is
`#machine_closes_at`'s: `c.gate_peel` present means a gate child):
* a GATE child with what `#gate_child` left (`gate_peel`, `gate_old`,
  `gate_wf`, `gateBinders`, `gateSort`, `gateValue`) — as in `#machine_oneout`;
* a SLOTLESS LEAF MACHINE child: `c.machineData`, `c.machine_ok`,
  `c.machine_body`, `c.machine_closes` exist, and the reader's data of `c`
  have no call, no slot, at least one `let`, and the one output `out`.
  REFUSED, each with its reason — NOT COVERED:
  - a machine callee WITH a register (`slots ≠ []`): the one-output closing
    is for combinational children; a sequential child is another closing;
  - a machine callee with calls of its own (`insts ≠ []`);
  - a machine callee without a `let` (`lets = 0`);
  - a machine callee whose outputs are not exactly `[out]`;
  - a machine callee without `c.machine_closes` (its own closing is not
    derived).

"The parent has a register" and "the kind of each child" are separate
conditions. A parent with one gate callee AND one machine-leaf callee is in
the design (the per-entry case split is by callee, each case of its own
kind), but NO declaration of the tests has that shape: that branch
combination has never been elaborated.

## What is generated

Per distinct GATE callee `c`: `c.gate_full`, `c.gate_ports`, `c.gate_kidK`,
`c.gate_width` — the statements of `#machine_oneout` (an existing constant
of the name is re-derived and compared).

Per distinct MACHINE-LEAF callee `c`, the fields of
`Tools.ShippingLeafOneOut.SlotlessLeaf` as NAMED theorems on `c.machineData`
(kernel `decide` / `rfl`; a failed one makes the command FAIL naming it):

    c.leaf_gate       gateCallsOk c.machineData c.machineData.nIn = true
    c.leaf_calls      callsOk c.machineData c.machineData.nIn = true     (a conjunct of leaf_gate)
    c.leaf_dom        no domain binder after the first nIn                (a conjunct of leaf_gate)
    c.leaf_ss         ss.length = layout.slots.length                     (a conjunct of leaf_gate)
    c.leaf_insts      shape.insts = []                                    (a LEAF)
    c.leaf_outTy      every output's ty.bitWidth = width
    c.leaf_outChars   the output names are character-wise charOk
    c.leaf_outScalar  the output types are scalarTy
    c.leaf_lets       layout.lets ≠ 0
    c.leaf_slots      layout.slots = []                                   (SLOTLESS)
    c.leaf_one        ∃ o, layout.outs = [o] ∧ o.name = "out"
    c.leaf_outW       every layout output's ty.bitWidth = W               (W: the width of the type of
                                                                          f's result binder of its first call of c)
    c.leaf_slotless   MachineDefines … c c.machineData.shape → SlotlessLeaf … c c.machineData

`leaf_calls`, `leaf_dom`, `leaf_ss` are tried first as conjuncts of
`leaf_gate` (`gateCallsOk_parts`: no second evaluation), then by `decide`.

Per declaration `f`: the data conditions `f.oneout_*` of `#machine_oneout`
(same names, same statements for a parent of gate children). In
`f.oneout_entries` the alternative of a machine-leaf callee `c` is

    (insts[k]).1 = c ∧ f.oneout_kidIns k = declWidths c.machineData ∧
      (binders[nDecl + k]?).map (width of the kind's type) = some W

(`declWidths`: the widths of `c`'s declared non-domain binders). Then the
six lemmas `f.machine_factsH`, `_outsH`, `_portsRawH`, `_portsShippedH`,
`_hierTypedH`, `_designFullH` — binders: the contexts, the worlds,
`raw b D`, the core run, the post-processing fact, `MachineDefines f`,
`MachineClosesAt f`, `ChildBnd`, then per distinct callee its reflection
(`EntryDefines … c c.gateValue` for a gate child, `MachineDefines … c
c.machineData.shape` for a machine leaf) — and the endpoint
`f.machine_design_svH_full` (+ `_closed`).

## The generation contract (that of `#machine_oneout`, unchanged)

Every statement is re-derived from the data as read NOW. A name already
present is never trusted and never silently reused: it is generated again
under a scratch name and compared (`emitOrVerify`). The endpoint: ADDED when
the name is free (GENERATED); when it exists its statement must be `isDefEq`
the statement rebuilt now from the generated lemmas, on standard axioms —
recorded from the same lemmas: PRESENT, verified; recorded from OTHER lemmas
(a hand instance): the proof rebuilt now is kernel-checked as
`f.machine_design_svH_full_gen` and the outcome says so. On REFUSED or
FAILED the environment and the message log are put back.

The command must be run under `set_option maxHeartbeats 0 in`.

## What a generated endpoint does NOT say (binding for any report)

The data conditions are decided PER DECLARATION; they are conditions on the
reflected data, not reductions. `MachineDefines`, `EntryDefines`, `ChildBnd`
and the run stay premises (no runtime model). The conclusion is about
`DesignSV (childMap D.modules) 0 (checkedOptimize b)` — the module list, not
the SV string, not `#sim`. One declaration at a time: a register parent, the
one-output closing, gate children and slotless leaf machine children. NOT
slotless parents, NOT machine children with registers or calls, NOT several
outputs, NOT "all successful inputs".

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingOneOutAnyGenCommand
open Lean Meta Elab Command
open Tools.ShippingOneOutGenCommand (Outcome emit emitOrVerify mkThm perEntry endpoint)

/-- The kind of a callee. -/
inductive CalleeKind where
  | gate
  | leaf
  deriving BEq, Inhabited

/-- The log line. -/
def line (f : Name) : Outcome → String
  | .generated made note => s!"ONEOUT ANY {f}: GENERATED {made} — {note}"
  | .present made note => s!"ONEOUT ANY {f}: PRESENT {made} — {note}"
  | .refused reason => s!"ONEOUT ANY {f}: REFUSED ({reason})"
  | .failed cond => s!"ONEOUT ANY {f}: FAILED ({cond})"

/-- What the scope test read. -/
structure Info where
  r : Tools.ShippingMachineCommand.Read
  /-- The callee of every entry. -/
  calls : List Name
  /-- The distinct callees, and the kind of each. -/
  kids : List Name
  kinds : List CalleeKind
  /-- Per entry: the widths of the types of the parent's `let` binders of the
  call's arguments. -/
  kidIns : List (List Nat)
  /-- Per distinct callee: the width of the type of the parent's result
  binder of its first entry. -/
  resW : List Nat

/-- The scope test; every `throwError` here is a REFUSAL. -/
def scope (f : Name) : CommandElabM Info := do
  let env ← getEnv
  let ships := f ++ `machine_ships_hierHR
  unless env.contains ships do
    throwError "no {ships}: run #machine_design_svHR {f} first"
  for s in [`machineData, `machine_ok, `machine_body] do
    let need := f ++ s
    unless env.contains need do
      throwError "no {need}: run #machine_endpoint {f} first"
  let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine f
  let calls := r.shape.insts.map (·.1)
  if calls.isEmpty then throwError "no call"
  if r.shape.layout.slots.isEmpty then
    throwError "parent without a register: the head needs shape.layout.slots ≠ [] (slotless parents are not covered)"
  unless r.shape.instFields.isEmpty do
    throwError "instFields ≠ []: not the one-output closing (several outputs or a sequential child)"
  let kids := calls.eraseDups
  let mut kinds : Array CalleeKind := #[]
  for c in kids do
    if (Sparkle.Compiler.MachMemory.memChild? c).isSome then
      throwError "memory callee {c}"
    if env.contains (c ++ `gate_peel) then
      for s in [`gate_peel, `gate_old, `gate_wf, `gateBinders, `gateSort, `gateValue] do
        let need := c ++ s
        unless env.contains need do
          throwError "callee {c} is not a gate child with #gate_child data (no {need})"
      kinds := kinds.push CalleeKind.gate
    else if env.contains (c ++ `machineData) then
      for s in [`machine_ok, `machine_body] do
        let need := c ++ s
        unless env.contains need do
          throwError "machine callee {c}: no {need} (run #machine_endpoint {c} first)"
      let cr ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine c
      unless cr.shape.insts.isEmpty do
        throwError "machine callee {c} has calls of its own: NOT COVERED (only a LEAF machine child)"
      unless cr.shape.layout.slots.isEmpty do
        throwError "machine callee {c} has a register: NOT COVERED (only a SLOTLESS machine child; a sequential child is not a child of the one-output closing)"
      if cr.shape.layout.lets == 0 then
        throwError "machine callee {c} has no `let`: NOT COVERED"
      unless cr.shape.layout.outs.map (·.name) == ["out"] do
        throwError "machine callee {c} does not have the one output `out`: NOT COVERED"
      let needC := c ++ `machine_closes
      unless env.contains needC do
        throwError "machine callee {c}: no {needC} (its own closing is not derived; #machine_closes_at {f} generates it)"
      kinds := kinds.push CalleeKind.leaf
    else
      throwError "callee {c} is neither a gate child (#gate_child) nor a machine with an endpoint (#machine_endpoint)"
  -- the numerals, from the parent's reflected data
  let nD := r.nDecl
  let nI := r.shape.insts.length
  let nS := r.shape.layout.slots.length
  let wOf (p : Nat) : Option Nat :=
    (r.shape.binders[p]?).map fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth
  let mut kidIns : Array (List Nat) := #[]
  for c in r.shape.insts do
    let mut ws : Array Nat := #[]
    for a in c.2.1 do
      match wOf (nD + (nI + (nS + a))) with
      | some wd => ws := ws.push wd
      | none => throwError "the argument `let` {a} of a call of {c.1} has no binder in the reflected data"
    kidIns := kidIns.push ws.toList
  let mut resW : Array Nat := #[]
  for c in kids do
    match wOf (nD + calls.idxOf c) with
    | some wd => resW := resW.push wd
    | none => throwError "the result binder of the first call of {c} is not in the reflected data"
  return { r, calls, kids, kinds := kinds.toList, kidIns := kidIns.toList, resW := resW.toList }

/-- The named theorems of a slotless leaf machine callee `c` (see the
header); `W`: the width its outputs must have. -/
def leafFacts (f c : Name) (W : Nat) : CommandElabM Unit := do
  let nm (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)
  let kd := nm c "machineData"
  let cq : Term := quote c
  let wLit := Syntax.mkNumLit (toString W)
  let lf (s : String) : Ident := nm c ("leaf_" ++ s)
  let fact (s what : String) (ty pf : Term) : CommandElabM Unit := do
    discard <| emitOrVerify (c ++ Name.mkSimple ("leaf_" ++ s))
      s!"data condition of the machine callee {c}: {what}" fun id =>
        `(command| theorem $id : $ty := $pf)
  fact "gate" "gateCallsOk at nIn"
    (← `(Tools.ShippingMachineAuto.MachineData.gateCallsOk $kd ($kd).nIn = true))
    (← `(by first | decide | decide +kernel))
  fact "calls" "callsOk at nIn"
    (← `(Tools.ShippingMachineAuto.MachineData.callsOk $kd ($kd).nIn = true))
    (← `(by first | exact (Tools.ShippingLeafOneOutGen.gateCallsOk_parts $(lf "gate")).1 | decide | decide +kernel))
  fact "dom" "no domain binder after the first nIn"
    (← `(∀ b ∈ ($kd).shape.binders.drop ($kd).nIn,
      b.2 ≠ Sparkle.Compiler.Elab.MixedGateBinder.domain))
    (← `(by first | exact (Tools.ShippingLeafOneOutGen.gateCallsOk_parts $(lf "gate")).2.2.1 | decide | decide +kernel))
  fact "ss" "ss.length = layout.slots.length"
    (← `(($kd).ss.length = ($kd).shape.layout.slots.length))
    (← `(by first | exact (Tools.ShippingLeafOneOutGen.gateCallsOk_parts $(lf "gate")).2.1 | decide | decide +kernel))
  fact "insts" "shape.insts = [] (a leaf)"
    (← `(($kd).shape.insts = [])) (← `(by first | rfl | decide))
  fact "outTy" "every output's ty.bitWidth = width"
    (← `(∀ o ∈ ($kd).shape.layout.outs, o.ty.bitWidth = o.width))
    (← `(by first | decide | decide +kernel))
  fact "outChars" "the output names are character-wise charOk"
    (← `(∀ o ∈ ($kd).shape.layout.outs, ∀ c ∈ o.name.toList,
      Sparkle.IR.NameHints.charOk c = true))
    (← `(by first | decide | decide +kernel))
  fact "outScalar" "the output types are scalarTy"
    (← `(∀ o ∈ ($kd).shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true))
    (← `(by first | decide | decide +kernel))
  fact "lets" "layout.lets ≠ 0"
    (← `(($kd).shape.layout.lets ≠ 0)) (← `(by first | decide | decide +kernel))
  fact "slots" "layout.slots = [] (slotless)"
    (← `(($kd).shape.layout.slots = [])) (← `(by first | rfl | decide))
  fact "one" "the one output out"
    (← `(∃ o, ($kd).shape.layout.outs = [o] ∧ o.name = "out")) (← `(⟨_, rfl, rfl⟩))
  fact "outW"
    s!"every layout output's ty.bitWidth = {W} (the width of the type of {f}'s result binder of its first call of {c})"
    (← `(∀ o ∈ ($kd).shape.layout.outs, o.ty.bitWidth = $wLit))
    (← `(by first | decide | decide +kernel))
  discard <| emitOrVerify (c ++ `leaf_slotless) s!"child facts {c}.leaf_slotless" fun id =>
    `(command|
      theorem $id {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
          {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
          (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $cq ($kd).shape) :
          Tools.ShippingLeafOneOut.SlotlessLeaf mctx mref cctx cref $cq $kd :=
        { any :=
            { ok := $(nm c "machine_ok"),
              body := $(nm c "machine_body"),
              calls := $(lf "calls"),
              dom := $(lf "dom"),
              leaf := $(lf "insts"),
              ss := $(lf "ss"),
              outTy := $(lf "outTy"),
              outName := fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
                ($(lf "outChars") o ho),
              outScalar := $(lf "outScalar"),
              entry := hR0,
              closes := fun mc cc => $(nm c "machine_closes") mc _ cc _ },
          gate := $(lf "gate"),
          lets := $(lf "lets"),
          slots := $(lf "slots"),
          one := $(lf "one") })

/-- The named theorems of a gate callee `c` (those of `#machine_oneout`). -/
def gateFacts (f c : Name) (W : Nat) : CommandElabM Unit := do
  let nm (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)
  let cq : Term := quote c
  let wLit := Syntax.mkNumLit (toString W)
  discard <| emitOrVerify (c ++ `gate_full) s!"child facts {c}.gate_full" fun id =>
    `(command|
      theorem $id {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
          {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
          (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $cq
            $(nm c "gateValue"))
          {y : Tools.ShippingChildInv.Res}
          (hy : Tools.ShippingChildInv.RealChild mref cref $cq y) :
          Tools.ShippingGateChildComb.ChildFull $cq $(nm c "gateBinders") y.1 y.2 :=
        Tools.ShippingCallsGate.childFull_of_real hR0 $(nm c "gate_old") $(nm c "gate_peel")
          $(nm c "gate_wf") (Tools.ShippingGateChild.bool_positions (by decide))
          (Tools.ShippingGateChild.bits_positions (by decide)) hy)
  discard <| emitOrVerify (c ++ `gate_ports) s!"child facts {c}.gate_ports" fun id =>
    `(command|
      theorem $id {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
          {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
          (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $cq
            $(nm c "gateValue"))
          {y : Tools.ShippingChildInv.Res}
          (hy : Tools.ShippingChildInv.RealChild mref cref $cq y) :
          Tools.ShippingGatePorts.GateChildPorts $cq $(nm c "gateBinders")
            (Tools.ShippingUnifiedSource.SType.width $(nm c "gateSort")) y.1 :=
        Tools.ShippingGatePorts.gate_real_ports hR0 $(nm c "gate_old") $(nm c "gate_peel")
          $(nm c "gate_wf") (Tools.ShippingGateChild.bool_positions (by decide))
          (Tools.ShippingGateChild.bits_positions (by decide)) hy)
  discard <| emitOrVerify (c ++ `gate_kidK) s!"child facts {c}.gate_kidK" fun id =>
    `(command|
      theorem $id {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
          {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
          (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $cq
            $(nm c "gateValue"))
          {y : Tools.ShippingChildInv.Res}
          (hy : Tools.ShippingChildInv.RealChild mref cref $cq y) :
          (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
              Tools.ShippingChecksDesign.kidCheck C n y.1 = true) ∧
            ∀ g ∈ y.2.modules,
              ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
                (n : Nat), Tools.ShippingChecksDesign.kidCheck C n g = true :=
        Tools.ShippingCombKidText.gate_real_kidK hR0 $(nm c "gate_old") $(nm c "gate_peel")
          $(nm c "gate_wf") (Tools.ShippingGateChild.bool_positions (by decide))
          (Tools.ShippingGateChild.bits_positions (by decide)) hy)
  discard <| emitOrVerify (c ++ `gate_width)
      s!"data condition {c}.gateSort.width = {W} (the width of the type of {f}'s result binder of its first call of {c})" fun id =>
    `(command|
      theorem $id : Tools.ShippingUnifiedSource.SType.width $(nm c "gateSort") = $wLit := by
        first | rfl | decide)

/-- Everything after the scope test; every `throwError` here is a FAILURE. -/
def oneOutCore (f : Name) (info : Info) : CommandElabM (List Name × Bool × String) := do
  let r := info.r
  let kids := info.kids
  let isLeaf (i : Nat) : Bool := info.kinds.getD i CalleeKind.gate == CalleeKind.leaf
  let nm (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)
  let data := nm f "machineData"
  let okI := nm f "machine_ok"
  let bodyI := nm f "machine_body"
  let fq : Term := quote f
  let nDecl := Syntax.mkNumLit (toString r.nDecl)
  let dn (s : String) : Name := f ++ Name.mkSimple ("oneout_" ++ s)
  let dl (s : String) : Ident := nm f ("oneout_" ++ s)
  let hR (j : Nat) : Ident := mkIdent (Name.mkSimple s!"hR{j}")
  -- ## the callees' facts, once per callee, by kind
  for i in [0:kids.length] do
    let c := kids[i]!
    let W := info.resW.getD i 0
    if isLeaf i then leafFacts f c W else gateFacts f c W
  -- ## the parent's data conditions, each named
  let dataLemma (s cond : String) (ty pf : Term) : CommandElabM Unit := do
    discard <| emitOrVerify (dn s) s!"data condition {cond}" fun id =>
      `(command| theorem $id : $ty := $pf)
  dataLemma "callsOk" s!"callsOk {f}.machineData {r.nDecl}"
    (← `(Tools.ShippingMachineAuto.MachineData.callsOk $data $nDecl = true)) (← `(by first | decide | decide +kernel))
  dataLemma "slotLen" "ss.length = shape.layout.slots.length"
    (← `(($data).ss.length = ($data).shape.layout.slots.length)) (← `(by first | decide | decide +kernel))
  dataLemma "domB" s!"no domain binder after the first {r.nDecl}"
    (← `(∀ b ∈ ($data).shape.binders.drop $nDecl,
      b.2 ≠ Sparkle.Compiler.Elab.MixedGateBinder.domain)) (← `(by first | decide | decide +kernel))
  dataLemma "insts" "shape.insts ≠ []"
    (← `(($data).shape.insts ≠ []))
    (← `(fun h0 => absurd (congrArg List.length h0) (by decide)))
  dataLemma "instFields" "shape.instFields = []"
    (← `(($data).shape.instFields = []))
    (← `(by first | rfl | decide))
  dataLemma "outTy" "every output's ty.bitWidth = width"
    (← `(∀ o ∈ ($data).shape.layout.outs, o.ty.bitWidth = o.width)) (← `(by first | decide | decide +kernel))
  dataLemma "nomem" "no memory callee"
    (← `(∀ c ∈ ($data).shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none))
    (← `(by first | decide | decide +kernel))
  dataLemma "slots" "shape.layout.slots ≠ [] (the parent has a register)"
    (← `(($data).shape.layout.slots ≠ []))
    (← `(fun h0 => absurd (congrArg List.length h0) (by decide)))
  dataLemma "outChars" "the output names are character-wise charOk"
    (← `(∀ o ∈ ($data).shape.layout.outs, ∀ c ∈ o.name.toList,
      Sparkle.IR.NameHints.charOk c = true))
    (← `(by first | decide | decide +kernel))
  dataLemma "outScalar" "the output types are scalarTy"
    (← `(∀ o ∈ ($data).shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true))
    (← `(by first | decide | decide +kernel))
  -- the argument widths per entry: numerals computed from the parent's data
  let mut rows : Array Term := #[]
  for ws in info.kidIns do
    let mut lits : Array Term := #[]
    for wd in ws do
      let l : Term := ⟨(Syntax.mkNumLit (toString wd)).raw⟩
      lits := lits.push l
    let row : Term ← `([$lits,*])
    rows := rows.push row
  discard <| emitOrVerify (dn "kidIns") "the definition of the argument widths" fun id =>
    `(command| def $id : Nat → List Nat := fun k => List.getD [$rows,*] k [])
  let kidInsI := dl "kidIns"
  dataLemma "callArgs" s!"callArgsOk {f}.machineData {r.nDecl} {f}.oneout_kidIns with {f}.oneout_kidIns = {info.kidIns}"
    (← `(Tools.ShippingPortsMatchRaw.callArgsOk $data $nDecl $kidInsI = true)) (← `(by first | decide | decide +kernel))
  -- per entry: the callee, its argument widths, the result binder's width
  let alt (i : Nat) : CommandElabM Term := do
    let c := kids[i]!
    let cq : Term := quote c
    let wLit := Syntax.mkNumLit (toString (info.resW.getD i 0))
    if isLeaf i then
      `(((($data).shape.insts[k]).1 = $cq ∧
          $kidInsI k = Tools.ShippingPortWidthsPure.declWidths $(nm c "machineData") ∧
          (($data).shape.binders[$nDecl + k]?).map
            (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some $wLit))
    else
      `(((($data).shape.insts[k]).1 = $cq ∧
          $kidInsI k = ((($(nm c "gateBinders")).filter fun x =>
            x.2 != Sparkle.Compiler.Elab.MixedGateBinder.domain).map fun x =>
              (Tools.ShippingMachineEntry.kindTy x.2).bitWidth) ∧
          (($data).shape.binders[$nDecl + k]?).map
            (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some $wLit))
  let mut disj ← alt (kids.length - 1)
  for i' in [0:kids.length - 1] do
    let i := kids.length - 2 - i'
    disj ← `($(← alt i) ∨ $disj)
  dataLemma "entries"
    s!"per call entry: the callee among {kids}, {f}.oneout_kidIns k = the widths of the callee's declared non-domain binders ({info.kidIns}), and the result binder's width = the callee's output width ({info.resW} per callee)"
    (← `(∀ (k : Nat) (hk : k < ($data).shape.insts.length), $disj))
    (← `(by first | decide | decide +kernel))
  let ent := dl "entries"
  -- ## the lemmas of the head
  let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut hRs : Array Term := #[]
  for j in [0:kids.length] do
    let c := kids[j]!
    let cq : Term := quote c
    if isLeaf j then
      binders := binders.push (← `(bracketedBinder|
        ($(hR j) : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $cq
          ($(nm c "machineData")).shape)))
    else
      binders := binders.push (← `(bracketedBinder|
        ($(hR j) : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $cq
          $(nm c "gateValue"))))
    let t : Term := ⟨(hR j).raw⟩
    hRs := hRs.push t
  let n := kids.length
  let gf (i : Nat) : Ident := nm kids[i]! "gate_full"
  let gp (i : Nat) : Ident := nm kids[i]! "gate_ports"
  let gk (i : Nat) : Ident := nm kids[i]! "gate_kidK"
  let gw (i : Nat) : Ident := nm kids[i]! "gate_width"
  let ls (i : Nat) : Ident := nm kids[i]! "leaf_slotless"
  let lw (i : Nat) : Ident := nm kids[i]! "leaf_outW"
  let tacA ← perEntry ent n fun i =>
    if isLeaf i then
      `(tactic| (rw [hc] at hy; exact ($(ls i) $(hR i)).kidA hy))
    else
      `(tactic| (rw [hc] at hy; exact Tools.ShippingChecksGate.gate_kidA ($(gf i) $(hR i) hy)))
  let tacR ← perEntry ent n fun i =>
    if isLeaf i then
      `(tactic| (rw [hc] at hy; exact ($(ls i) $(hR i)).kidR hy))
    else
      `(tactic| (rw [hc] at hy; exact Tools.ShippingChecksGate.gate_kidR ($(gf i) $(hR i) hy)))
  let tacW ← perEntry ent n fun i =>
    if isLeaf i then
      `(tactic| (rw [hc] at hy;
                 exact hres.trans (congrArg Option.some
                   ((Tools.ShippingLeafOneOutGen.leaf_outWidth ($(ls i) $(hR i)) $(lw i)
                     hy p hp).symm))))
    else
      `(tactic| (rw [hc] at hy;
                 exact hres.trans (congrArg Option.some
                   ((((($(gp i) $(hR i) hy).outWidth p hp).2).trans $(gw i)).symm))))
  let tacT ← perEntry ent n fun i =>
    if isLeaf i then
      `(tactic| (rw [hc] at hy; exact ($(ls i) $(hR i)).portsIn hy))
    else
      `(tactic| (rw [hc] at hy; exact ($(gp i) $(hR i) hy).portsIn))
  let tacIn ← perEntry ent n fun i =>
    if isLeaf i then
      `(tactic| (rw [hc] at hy; rw [hki];
                 obtain ⟨wd, h1, h2, -⟩ := ($(ls i) $(hR i)).inWidths hy hq;
                 exact ⟨wd, h1, h2⟩))
    else
      `(tactic| (rw [hc] at hy; rw [hki];
                 obtain ⟨wd, h1, h2, -⟩ := ($(gp i) $(hR i) hy).inWidths hq;
                 exact ⟨wd, h1, h2⟩))
  let tacTy ← perEntry ent n fun i =>
    if isLeaf i then
      `(tactic| (rw [hc] at hy; exact ($(ls i) $(hR i)).childTyped hy))
    else
      `(tactic| (rw [hc] at hy; exact ($(gp i) $(hR i) hy).childTyped_ok))
  let tacInD ← perEntry ent n fun i =>
    if isLeaf i then
      `(tactic| (rw [hc] at hy; rw [hki];
                 obtain ⟨wd, h1, -, h3⟩ := ($(ls i) $(hR i)).inWidths hy hq;
                 exact ⟨wd, h1, h3⟩))
    else
      `(tactic| (rw [hc] at hy; rw [hki];
                 obtain ⟨wd, h1, -, h3⟩ := ($(gp i) $(hR i) hy).inWidths hq;
                 exact ⟨wd, h1, h3⟩))
  let tacK ← perEntry ent n fun i =>
    if isLeaf i then
      `(tactic| (rw [hc] at hy; exact ($(ls i) $(hR i)).kidK hy))
    else
      `(tactic| (rw [hc] at hy; exact $(gk i) $(hR i) hy))
  let hon : Term ← `(fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean ($(dl "outChars") o ho))
  let factsN := f ++ `machine_factsH
  let outsN := f ++ `machine_outsH
  let rawN := f ++ `machine_portsRawH
  let shippedN := f ++ `machine_portsShippedH
  let typedN := f ++ `machine_hierTypedH
  let designN := f ++ `machine_designFullH
  let rawI := nm f "machine_portsRawH"
  let shippedI := nm f "machine_portsShippedH"
  discard <| emitOrVerify factsN s!"{factsN} (core_runFactsH at {f}'s data)" fun id => do
    mkThm id fq data #[] false
      (← `(Tools.ShippingOneOutFacts.RunFactsH D.modules b))
      (← `(Tools.ShippingOneOutFacts.core_runFactsH (nDecl := $nDecl) $data $okI $bodyI
        $(dl "callsOk") $(dl "slotLen") $(dl "domB") $(dl "insts") $(dl "instFields")
        $(dl "outTy") $(dl "nomem") hB hcore hpost entry closes $(dl "slots")))
  discard <| emitOrVerify outsN s!"{outsN} (core_outsCheck_all_gate at {f}'s data)" fun id => do
    mkThm id fq data binders true
      (← `(Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
        (Sparkle.IR.OptCheck.checkedOptimize b) = true))
      (← `(Tools.ShippingChecksCoreGate.core_outsCheck_all_gate (nDecl := $nDecl) $data $okI $bodyI
        $(dl "callsOk") $(dl "slotLen") $(dl "domB") $(dl "insts") $(dl "outTy") $(dl "nomem")
        (by
          intro k hk y hy
          $tacA:tactic)
        (by
          intro k hk y hy
          $tacR:tactic)
        hB hcore hpost entry closes hg 0))
  discard <| emitOrVerify rawN s!"{rawN} (core_portsMatch_raw₁ at {f}'s data)" fun id => do
    mkThm id fq data binders false
      (← `(Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules) b =
        true))
      (← `(Tools.ShippingOneOutConns.core_portsMatch_raw₁ (nDecl := $nDecl) $data $okI $bodyI
        $(dl "callsOk") $(dl "slotLen") $(dl "domB") $(dl "insts") $(dl "instFields")
        $(dl "outTy") $(dl "nomem")
        (by
          intro k hk y hy p hp
          $tacW:tactic)
        (by
          intro k hk y hy
          $tacT:tactic)
        (kidIns := $kidInsI) $(dl "callArgs")
        (by
          intro k hk y hy j q hq
          $tacIn:tactic)
        hB hcore hpost entry closes $hon $(dl "outScalar")))
  discard <| emitOrVerify shippedN s!"{shippedN} (portsMatchB_shipped)" fun id => do
    mkThm id fq data binders false
      (← `(Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules)
        (Sparkle.IR.OptCheck.checkedOptimize b) = true))
      (← `(Tools.ShippingPortsMatchShipped.portsMatchB_shipped
        (Tools.ShippingHierGateAny.core_hierGate_any (nDecl := $nDecl) $data $okI $bodyI
          $(dl "callsOk") $(dl "slotLen") $(dl "domB") $(dl "insts") $(dl "outTy") $(dl "nomem")
          hB hcore hpost entry closes)
        ($rawI hcore hpost entry closes hB $hRs*)))
  discard <| emitOrVerify typedN s!"{typedN} (core_hierTyped₁ at {f}'s data)" fun id => do
    mkThm id fq data binders false
      (← `(Tools.ShippingHierTyped.hierTyped (Tools.ShippingMachineLinked.childMap D.modules) b =
        true))
      (← `(Tools.ShippingOneOutConns.core_hierTyped₁ (nDecl := $nDecl) $data $okI $bodyI
        $(dl "callsOk") $(dl "slotLen") $(dl "domB") $(dl "insts") $(dl "instFields")
        $(dl "outTy") $(dl "nomem")
        (by
          intro k hk y hy p hp
          $tacW:tactic)
        (by
          intro k hk y hy
          $tacTy:tactic)
        (kidIns := $kidInsI) $(dl "callArgs")
        (by
          intro k hk y hy j q hq
          $tacInD:tactic)
        hB hcore hpost entry closes $hon $(dl "outScalar")))
  discard <| emitOrVerify designN s!"{designN} (core_designCheckH at {f}'s data)" fun id => do
    mkThm id fq data binders false
      (← `(Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
        (Sparkle.IR.OptCheck.checkedOptimize b) = true))
      (← `(Tools.ShippingOneOutFacts.core_designCheckH (nDecl := $nDecl) $data $okI $bodyI
        $(dl "callsOk") $(dl "slotLen") $(dl "domB") $(dl "insts") $(dl "instFields")
        $(dl "outTy") $(dl "nomem") hB hcore hpost entry closes $(dl "slots")
        $hon $(dl "outScalar")
        (by
          intro k hk y hy
          $tacK:tactic)
        0 ($shippedI hcore hpost entry closes hB $hRs*)))
  -- ## the endpoint and its closed form
  let (name, fresh, note) ← liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) do
        endpoint f factsN typedN designN outsN
  let cl := f ++ `machine_closes_at
  let mut made := [name]
  let mut closedNote := s!"no {cl}: no closed form"
  if (← getEnv).contains cl then
    let nn := Tools.ShippingMachineClosesGen.closedName name
    let ok ← liftTermElabM <|
      withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
        withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) do
          let ok ← Tools.ShippingMachineClosesAtGen.closeEndpointAt f cl name nn
          if ok then
            Tools.ShippingOneOutCommand.refuse nn (← getConstInfo nn).type (mkConst ``True)
          pure ok
    if ok then
      made := made ++ [nn]
      closedNote := s!"closed form {nn} (added or verified by closeEndpointAt)"
    else
      closedNote := s!"{name} has no MachineClosesAt premise: no closed form"
  let leafKids := (List.range kids.length).filterMap fun i =>
    if isLeaf i then some kids[i]! else none
  let gateKids := (List.range kids.length).filterMap fun i =>
    if isLeaf i then none else some kids[i]!
  let dataNote := s!"callees: machine leaves {leafKids} (premise MachineDefines), gate children {gateKids} (premise EntryDefines); data conditions decided by the kernel for {f}: callsOk {r.nDecl}, slot lengths, no late domain binder, insts ≠ [], instFields = [], slots ≠ [], output width / name / scalar conditions, no memory callee, callArgsOk with {f}.oneout_kidIns = {info.kidIns}, per entry the callee among {kids} with its argument widths and the result binder's width {info.resW}; for a machine leaf c: c.leaf_gate, _calls, _dom, _ss, _insts, _outTy, _outChars, _outScalar, _lets, _slots, _one, _outW and its generated machine_ok / machine_body / machine_closes; for a gate child: gateSort.width, what #gate_child left. These are conditions, not reductions; the run, MachineDefines, EntryDefines and ChildBnd remain premises"
  return (made, fresh, s!"{note}; {closedNote}; {dataNote}")

/-- The generator on `f`: never throws; on REFUSED / FAILED the environment
and the message log are put back. -/
def oneOutAny (f : Name) : CommandElabM Outcome := do
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let restore : CommandElabM Unit := do
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
  let info? : Except String Info ← try
      pure (Except.ok (← scope f))
    catch ex =>
      let msg ← ex.toMessageData.toString
      restore
      pure (Except.error msg)
  match info? with
  | .error reason => return .refused reason
  | .ok info =>
    try
      let (made, fresh, note) ← oneOutCore f info
      if fresh then return .generated made note else return .present made note
    catch ex =>
      let msg ← ex.toMessageData.toString
      restore
      return .failed msg

/-- `#machine_oneout_any f`: an error where it is refused or fails. -/
elab "#machine_oneout_any " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← oneOutAny f
  match o with
  | .refused _ | .failed _ => throwError "{line f o}"
  | _ => logInfo m!"{line f o}"

/-- `#machine_oneout_any_try f "EXPECTED"`: the outcome is LOGGED (`ONEOUT
ANY f: GENERATED | PRESENT | REFUSED (reason) | FAILED (condition)`), and it
is an error when its class is not the expected one (`GENERATED`, `PRESENT`,
`REFUSED` or `FAILED`). -/
elab "#machine_oneout_any_try " d:ident ppSpace e:str : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let o ← oneOutAny f
  logInfo m!"{line f o}"
  unless o.tag == e.getString do
    throwError "ONEOUT ANY {f}: expected {e.getString}, found {o.tag}"

end Tools.ShippingOneOutAnyGenCommand

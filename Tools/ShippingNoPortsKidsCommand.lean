import Tools.ShippingNoPortsCommand
import Tools.ShippingOneOutKid
import Tools.ShippingLeafKidFacts
import Tools.ShippingNameSep
import Tools.ShippingCallsGate
import Tools.ShippingChecksGate
import Tools.ShippingKidsChildIface
import Tools.ShippingSVBridge
import Tools.ShippingMachineClosesGen

/-! # `#machine_no_ports_kids f n`: the check-free depth endpoint over callees of TWO kinds (G1, round par/a-14)

`#machine_no_ports` (`Tools/ShippingNoPortsCommand.lean`, not edited)
accepts leaf register machines only. This command generates

    f.machine_design_noPortsNR{n}   (and its `_closed` form)

for a parent WITH a register under the general closing whose every distinct
callee `k` is one of

* **leaf**: a machine without calls, with a register, with
  `k.machine_closes` — `KidFacts … n` by
  `Tools.ShippingLeafKidFacts.leafKid_facts (k.machine_leafKid …) n`;
* **one-output**: a machine with a register whose calls are all of ONE gate
  child `g` under the one-output closing (`instFields = []`), on which
  `#machine_oneout` / `#gate_child` / `#machine_closes_deep` left
  `k.oneout_*`, `k.machine_portsRawH`, `k.closes_deep`, `g.gate_full`,
  `g.gate_kidK` — `KidFacts … 1` by `(k.machine_oneOutKid …).facts`
  (`Tools.ShippingOneOutKid.OneOutKid`, generated here as the hand
  `midH_kid` of `Tests/Compiler/NoPortsGrandHTest.lean`); depth 1 only.

Everything else is REFUSED with a reason line (`scopeK`).

Generated, in this order (the proofs are those of the hand files
`NoPortsGrandHTest` / `NoPortsMixD1Test`, with the declaration's names):

    k.machine_leafKid / k.machine_oneOutKid          per distinct callee
    f.machine_kidsK{n}        KidFacts of every call entry's callee (per-entry tables in the reader's order)
    f.machine_runFactsK{n}    kids_runFacts
    f.machine_outsGK{n}       kids_outsCheck
    f.machine_maskedGK{n}     kids_maskedN
    f.machine_designPK{n}     kids_designCheck
    f.machine_design_noPortsNR{n}          the head applied to f.machine_ships_hierNR{n}'s arguments
    f.machine_design_noPortsNR{n}_closed   if f.closes_deep or f.machine_closes_at exists

The endpoint takes, after the binders of `f.machine_ships_hierNR{n}`, one
binder per distinct gate grandchild `g`: `EntryDefines mctx mref cctx cref
g g.gateValue` (the reflection at the run's contexts, as `grandH`'s hand
endpoint).

## The compare path (never a silent return)

If `f.machine_design_noPortsNR{n}` (resp. its `_closed`) EXISTS, the
statement is rebuilt all the same, the rebuilt theorem is added under
`…_regen` (so its proof is kernel-checked) and its statement must be
`isDefEq` the existing one — otherwise an ERROR. The log says `REBUILT …
isDefEq` or `GENERATED`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingNoPortsKidsCommand
open Lean Meta Elab Command
open Tools.ShippingShipsFreeCommand (checkMade)

/-- What a callee is, for this command. -/
inductive Kind where
  /-- a leaf register machine -/
  | leaf
  /-- a register machine with one-output calls of the gate child `gate`;
  `nDecl`: its declared binders -/
  | oneOut (gate : Name) (nDecl : Nat)
  deriving Inhabited

/-- The scope, with its reasons: the reading of `f`, its call entries'
callees, the distinct callees with their kinds. -/
def scopeK (f : Name) (n : Nat) :
    CommandElabM (Tools.ShippingMachineCommand.Read × List Name × List (Name × Kind)) := do
  unless (← getEnv).contains (f ++ `machineData) && (← getEnv).contains (f ++ `machine_ok) &&
      (← getEnv).contains (f ++ `machine_body) do
    throwError "{f}: not a machine with an endpoint (no {f}.machineData / machine_ok / machine_body: #machine_endpoint was not run on it)"
  let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine f
  let calls := r.shape.insts.map (·.1)
  if calls.isEmpty then throwError "{f}: no call (nothing to match: no instance statement)"
  if r.shape.layout.slots.isEmpty then
    throwError "{f}: parent without a register (kids_runFacts / kids_designCheck ask d.shape.layout.slots ≠ [])"
  if r.shape.instFields.isEmpty then
    throwError "{f}: a parent under the one-output closing (instFields = []; kids_* ask the general closing — #machine_oneout_any is the command for it)"
  let mut kinds : List (Name × Kind) := []
  for k in calls.eraseDups do
    if (Sparkle.Compiler.MachMemory.memChild? k).isSome then
      throwError "{f}: the callee {k} is a memory child (no KidFacts for it)"
    unless (← getEnv).contains (k ++ `machineData) && (← getEnv).contains (k ++ `machine_ok) &&
        (← getEnv).contains (k ++ `machine_body) do
      throwError "{f}: the callee {k} has no machine endpoint (a gate child of a general-closing parent, or #machine_endpoint was not run on it)"
    let cr ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine k
    if cr.shape.layout.slots.isEmpty then
      throwError "{f}: the callee {k} has no register (LeafKid.slots / OneOutKid.slots ask one)"
    if cr.shape.insts.isEmpty then
      unless (← getEnv).contains (k ++ `machine_closes) do
        throwError "{f}: the leaf callee {k} has no {k}.machine_closes (its closing in every context is not derived)"
      kinds := kinds ++ [(k, .leaf)]
    else
      unless cr.shape.instFields.isEmpty do
        throwError "{f}: the callee {k} has calls of its own under the GENERAL closing (instFields ≠ []): KidFacts of such a child is not derived (unit U3: topD2, mixDeep, grand)"
      let gs := (cr.shape.insts.map (·.1)).eraseDups
      let [g] := gs
        | throwError "{f}: the callee {k} calls several different declarations {gs} (generated for ONE gate grandchild only)"
      -- the kind of the grandchild, as `Tools.ShippingOneOutAnyGenCommand` (BUILT)
      -- decides it: `g.gate_peel` present means a GATE child (such a
      -- declaration may ALSO have `g.machineData` — `rcH` does); only
      -- otherwise is it a machine
      unless (← getEnv).contains (g ++ `gate_peel) do
        if (← getEnv).contains (g ++ `machineData) then
          throwError "{f}: the callee {k}'s callee {g} is a machine child (no {g}.gate_peel; generated for a GATE grandchild only)"
        else
          throwError "{f}: the callee {k}'s callee {g} has no #gate_child data (no {g}.gate_peel)"
      for sfx in [`gate_old, `gate_wf, `gateBinders, `gateSort] do
        unless (← getEnv).contains (g ++ sfx) do
          throwError "{f}: the callee {k}'s callee {g} is not a gate child with #gate_child data (no {g ++ sfx})"
      for c in [g ++ `gate_full, g ++ `gate_kidK, g ++ `gateValue, k ++ `oneout_callsOk,
          k ++ `oneout_slotLen, k ++ `oneout_domB, k ++ `oneout_insts, k ++ `oneout_instFields,
          k ++ `oneout_slots, k ++ `oneout_outTy, k ++ `oneout_outChars, k ++ `oneout_outScalar,
          k ++ `oneout_nomem, k ++ `machine_portsRawH, k ++ `closes_deep] do
        unless (← getEnv).contains c do
          throwError "{f}: the one-output callee {k} lacks {c} (run #gate_child {g}, #machine_design_svHR {k}, #machine_oneout {k} and a depth command that leaves {k}.closes_deep first)"
      unless n == 1 do
        throwError "{f}: depth {n} with the one-output callee {k}: OneOutKid.facts gives KidFacts at depth 1 only"
      kinds := kinds ++ [(k, .oneOut g cr.nDecl)]
  return (r, calls, kinds)

private def nm (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)

private def noAsync {α : Type} (x : CommandElabM α) : CommandElabM α :=
  withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false }) x

/-- **`k.machine_oneOutKid`, generated** (the hand `midH_kid`): the interface
`OneOutKid` of the callee `k` with the gate callee `g`, from the two
reflections in any contexts. -/
def oneOutKidTheorem (k g : Name) (nDeclK : Nat) : CommandElabM Name := do
  let name := k ++ `machine_oneOutKid
  if (← getEnv).contains name then return name
  let data := nm k "machineData"
  let kq : Term := quote k
  let gq : Term := quote g
  let nD := Syntax.mkNumLit (toString nDeclK)
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    set_option maxHeartbeats 4000000 in
    theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State}
        (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $kq ($data).shape)
        (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $gq
          $(nm g "gateValue")) :
        Tools.ShippingOneOutKid.OneOutKid mref cref $kq $data $nD
          (fun _ => ([] : List Lean.Name).map fun n => Sparkle.IR.ModuleName.ofDecl n) :=
      have hent : ∀ (k : Nat) (hk : k < ($data).shape.insts.length),
          (($data).shape.insts[k]).1 = $gq := (by decide)
      { ok := $(nm k "machine_ok")
        body := $(nm k "machine_body")
        calls := $(nm k "oneout_callsOk")
        ss := $(nm k "oneout_slotLen")
        dom := $(nm k "oneout_domB")
        insts := $(nm k "oneout_insts")
        oneOut := $(nm k "oneout_instFields")
        slots := $(nm k "oneout_slots")
        outTy := $(nm k "oneout_outTy")
        outName := fun o ho =>
          Tools.ShippingSVBridge.sanitizeName_of_clean ($(nm k "oneout_outChars") o ho)
        outScalar := $(nm k "oneout_outScalar")
        nomem := $(nm k "oneout_nomem")
        hkD := by decide
        hIlen := by decide
        hSL := by decide
        hSlen := by decide
        hLlen := by decide
        hNIn := by decide
        kid := by
          intro k hk y hy
          rw [hent k hk] at hy ⊢
          exact Tools.ShippingKidsChildIface.kid_of_iface
            (Tools.ShippingCallsGate.ChildFull.iface ($(nm g "gate_full") hRr hy))
        self := by
          have h : Tools.ShippingKidsChildIface.namesOf $data
                (fun _ => ([] : List Lean.Name).map fun n => Sparkle.IR.ModuleName.ofDecl n) =
              (Tools.ShippingKidsChildIface.declsOf $data
                (fun _ => ([] : List Lean.Name))).map fun n => Sparkle.IR.ModuleName.ofDecl n :=
            Tools.ShippingKidsChildIface.namesOf_map $data (fun _ => ([] : List Lean.Name))
          rw [h]
          exact Tools.ShippingNameSep.Enc.not_mem_map_of _ _ (by decide)
        kidA := by
          intro k hk y hy
          rw [hent k hk] at hy
          exact Tools.ShippingChecksGate.gate_kidA ($(nm g "gate_full") hRr hy)
        kidR := by
          intro k hk y hy
          rw [hent k hk] at hy
          exact Tools.ShippingChecksGate.gate_kidR ($(nm g "gate_full") hRr hy)
        kidK := by
          intro k hk y hy
          rw [hent k hk] at hy
          exact $(nm g "gate_kidK") hRr hy
        portsRaw := fun _ _ _ _ _ _ _ hB hcore hpost =>
          $(nm k "machine_portsRawH") hcore hpost (Tools.ShippingReflectCtx.MachineDefines.ctx hRm)
            ($(nm k "closes_deep") (Tools.ShippingReflectCtx.EntryDefines.ctx hRr)) hB
            (Tools.ShippingReflectCtx.EntryDefines.ctx hRr)
        entry := fun _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx hRm
        closes := fun _ _ =>
          $(nm k "closes_deep") (Tools.ShippingReflectCtx.EntryDefines.ctx hRr) }))
  checkMade name before
  return name

/-- The names, binders and tables shared by the generated theorems of `f`. -/
structure Ctx where
  f : Name
  n : Nat
  nDecl : Nat
  calls : List Name
  kinds : List (Name × Kind)
  /-- the distinct gate grandchildren -/
  gates : List Name

namespace Ctx

def kids (c : Ctx) : List Name := c.kinds.map (·.1)

def hR (j : Nat) : Ident := mkIdent (Name.mkSimple s!"hR{j}")
def hG (i : Nat) : Ident := mkIdent (Name.mkSimple s!"hG{i}")

/-- The reflection binders: `MachineDefines` of every distinct callee, then
`EntryDefines` of every distinct gate grandchild — at the run's contexts. -/
def binders (c : Ctx) : CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  let mut bs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for j in [0:c.kids.length] do
    let k := c.kids[j]!
    let kq : Term := quote k
    bs := bs.push (← `(bracketedBinder|
      ($(hR j) : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $kq
        ($(nm k "machineData")).shape)))
  for i in [0:c.gates.length] do
    let g := c.gates[i]!
    let gq : Term := quote g
    bs := bs.push (← `(bracketedBinder|
      ($(hG i) : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $gq
        $(nm g "gateValue"))))
  return bs

/-- The binders' names, in the binders' order. -/
def hyps (c : Ctx) : Array Term :=
  ((List.range c.kids.length).map fun j => (⟨(hR j).raw⟩ : Term)).toArray ++
    ((List.range c.gates.length).map fun i => (⟨(hG i).raw⟩ : Term)).toArray

def kindOf (c : Ctx) (k : Name) : Kind :=
  match c.kinds.find? (·.1 == k) with
  | some (_, kd) => kd
  | none => .leaf

/-- The layout outputs of the callee `k`. -/
def outsOf (k : Name) : CommandElabM Term := `(($(nm k "machineData")).shape.layout.outs)

/-- The argument widths of the callee `k`, by its kind. -/
def insOf (c : Ctx) (k : Name) : CommandElabM Term :=
  match c.kindOf k with
  | .leaf => `(Tools.ShippingPortWidthsPure.declWidths $(nm k "machineData"))
  | .oneOut _ nD =>
    `(Tools.ShippingCallsChildPorts.argWidths $(nm k "machineData")
      $(Syntax.mkNumLit (toString nD)))

/-- `KidFacts` of the callee `k` at depth `c.n`, from the binders. -/
def factOf (c : Ctx) (k : Name) : CommandElabM Term := do
  let j := c.kids.idxOf k
  let nLit := Syntax.mkNumLit (toString c.n)
  match c.kindOf k with
  | .leaf =>
    `(Tools.ShippingLeafKidFacts.leafKid_facts ($(nm k "machine_leafKid") $(hR j)) $nLit)
  | .oneOut g _ =>
    let i := c.gates.idxOf g
    `(Tools.ShippingOneOutKid.OneOutKid.facts ($(nm k "machine_oneOutKid") $(hR j) $(hG i)))

/-- The per-entry tables: one called declaration — the constant function;
several — the list of the ENTRIES' callees' data, in the reader's order. -/
def kidOuts (c : Ctx) : CommandElabM Term := do
  if c.kids.length == 1 then
    let o ← outsOf c.kids[0]!
    `(fun _ => $o)
  else
    let os ← c.calls.toArray.mapM outsOf
    `(fun k => List.getD [$os,*] k [])

def kidIns (c : Ctx) : CommandElabM Term := do
  if c.kids.length == 1 then
    let o ← c.insOf c.kids[0]!
    `(fun _ => $o)
  else
    let os ← c.calls.toArray.mapM c.insOf
    `(fun k => List.getD [$os,*] k [])

end Ctx

/-- **`f.machine_kidsK{n}`, generated**: `KidFacts` of every call entry's
callee, against the per-entry tables. -/
def kidsTheorem (c : Ctx) : CommandElabM Name := do
  let name := c.f ++ Name.mkSimple s!"machine_kidsK{c.n}"
  if (← getEnv).contains name then return name
  let data := nm c.f "machineData"
  let nLit := Syntax.mkNumLit (toString c.n)
  let nCalls := Syntax.mkNumLit (toString c.calls.length)
  let kidOuts ← c.kidOuts
  let kidIns ← c.kidIns
  let tacKid ← if c.kids.length == 1 then do
      let k0 := c.kids[0]!
      let k0q : Term := quote k0
      let fact ← c.factOf k0
      `(tactic| (
        have hall : ∀ (k : Nat) (hk : k < ($data).shape.insts.length),
            (($data).shape.insts[k]).1 = $k0q := by decide
        rw [hall k hk]
        exact $fact))
    else do
      let mut tac ← `(tactic| exact absurd hk' (by omega))
      for i' in [0:c.calls.length] do
        let i := c.calls.length - 1 - i'
        let fact ← c.factOf c.calls[i]!
        tac ← `(tactic| cases k with
          | zero => exact $fact
          | succ k => $tac:tactic)
      `(tactic| (
        have hk' : k < $nCalls := hk
        $tac:tactic))
  let bs ← c.binders
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    set_option maxHeartbeats 4000000 in
    theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State} $bs* :
        ∀ (k : Nat) (hk : k < ($data).shape.insts.length),
          Tools.ShippingKidFacts.KidFacts mref cref (($data).shape.insts[k]).1
            (($kidOuts) k) (($kidIns) k) $nLit := by
      intro k hk
      $tacKid:tactic))
  checkMade name before
  return name

/-- The four run theorems of `f` (`kids_runFacts`, `kids_outsCheck`,
`kids_maskedN`, `kids_designCheck` at `f`'s data): binders
`hcore hpost entry closes (hg) hB` and the reflections. -/
def runTheorems (c : Ctx) (kidsN : Name) : CommandElabM (Name × Name × Name × Name) := do
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
  let ok := nm f "machine_ok"
  let body := nm f "machine_body"
  let facts := f ++ Name.mkSimple s!"machine_runFactsK{c.n}"
  let outs := f ++ Name.mkSimple s!"machine_outsGK{c.n}"
  let masked := f ++ Name.mkSimple s!"machine_maskedGK{c.n}"
  let design := f ++ Name.mkSimple s!"machine_designPK{c.n}"
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
        Tools.ShippingKidFacts.kids_runFacts (nDecl := $nDecl) $data $ok $body
          (by decide) (by decide) (by decide)
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (by decide) (by decide)
          $kidOuts $kidIns $nLit ($kidsI $hs*)
          (show Tools.ShippingCallWidths.callWidthsOk $data $nDecl $kidOuts = true from by
            first | decide | decide +kernel)
          hB hcore hpost entry closes))
    checkMade facts before
  unless (← getEnv).contains outs do
    let before := (← get).messages.toList.length
    elabCommand (← `(command|
      set_option maxHeartbeats 4000000 in
      theorem $(mkIdent (`_root_ ++ outs)) {mctx : Lean.Meta.Context}
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
          (hg : Sparkle.IR.RefineCheck.hierGate b = true)
          (hB : Tools.ShippingChildInv.ChildBnd mref cref w) $bs* :
          Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules)
            $nLit (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
        Tools.ShippingKidFacts.kids_outsCheck (nDecl := $nDecl) $data $ok $body
          (by decide) (by decide) (by decide)
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (by decide) (by decide)
          $kidOuts $kidIns $nLit ($kidsI $hs*)
          hB hcore hpost entry closes hg))
    checkMade outs before
  unless (← getEnv).contains masked do
    let before := (← get).messages.toList.length
    elabCommand (← `(command|
      set_option maxHeartbeats 4000000 in
      theorem $(mkIdent (`_root_ ++ masked)) {mctx : Lean.Meta.Context}
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
          Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
        Tools.ShippingKidFacts.kids_maskedN (nDecl := $nDecl) $data $ok $body
          (by decide) (by decide) (by decide)
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (by decide) (by decide)
          $kidOuts $kidIns $nLit ($kidsI $hs*)
          hB hcore hpost entry closes))
    checkMade masked before
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
        Tools.ShippingKidFacts.kids_designCheck (nDecl := $nDecl) $data $ok $body
          (by decide) (by decide) (by decide)
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (fun h0 => absurd (congrArg List.length h0) (by decide))
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
  return (facts, outs, masked, design)

/-- `Tools.ShippingShipsFreeCommand.discharge` with extra hypotheses besides
the conjuncts of the boundary (the gate grandchildren's reflections at the
run's contexts). -/
def dischargeWith (thm : Name) (p0 hBnd goal : Lean.Expr) (extra : Array Lean.Expr) :
    MetaM Lean.Expr := do
  let parts := (← Tools.ShippingShipsNoOutsCommand.andParts hBnd) ++ extra
  let mut p := p0
  repeat
    let t ← whnfR (← instantiateMVars (← inferType p))
    let .forallE _ dom _ _ := t | break
    let mut found := false
    for q in parts do
      if ← isDefEq (← inferType q) dom then
        p := mkApp p q
        found := true
        break
    unless found do
      throwError "{thm}: asks{indentExpr dom}\nwhich is neither a conjunct of the endpoint's boundary{indentExpr (← inferType hBnd)}\nnor a grandchild's reflection"
  unless ← isDefEq (← inferType p) goal do
    throwError "{thm}: proves{indentExpr (← inferType p)}\nbut the head asks{indentExpr goal}"
  instantiateMVars p

/-- The statement and the proof of `f.machine_design_noPortsNR{n}`:
`Tools.ShippingNoPortsCommand.generate`, with one binder per gate grandchild
after the binders of `f.machine_ships_hierNR{n}`. Nothing is added to the
environment. -/
def endpointTerm (f : Name) (gates : List Name) (n : Nat) (facts outs masked design : Name) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let ships := f ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  let some (.thmInfo ti) := (← getEnv).find? ships
    | throwError "{ships}: not a theorem (run #machine_design_svNR first)"
  let v := ti.value
  unless v.isAppOf ``Tools.ShippingMachineShipsHier.machine_ships_hierC do
    throwError "{ships}: not built from machine_ships_hierC"
  let a := v.getAppArgs
  unless a.size == 25 do throwError "{ships}: {a.size} arguments of machine_ships_hierC, expected 25"
  let value ← forallTelescope (← inferType (mkConst ships)) fun xs _ => do
    unless xs.size == 11 do throwError "{ships}: {xs.size} binders, expected 11"
    let gDecls : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) :=
      gates.toArray.mapIdx fun i g =>
        (Name.mkSimple s!"hG{i}", fun (_ : Array Lean.Expr) =>
          mkAppM ``Tools.ShippingInlineSoundness.EntryDefines
            #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, toExpr g, mkConst (g ++ `gateValue)])
    withLocalDeclsD gDecls fun hGs => do
    let args : Array (Option Lean.Expr) :=
      #[some (mkNatLit n), some a[3]!, some a[4]!, some a[5]!, some a[6]!, some a[7]!,
        some a[8]!, some a[9]!, some a[10]!, some a[11]!,
        some a[12]!, some a[13]!, some a[14]!, some a[15]!, some a[16]!, some a[17]!,
        some a[18]!, some a[19]!, some a[20]!, some a[21]!,
        some a[22]!, some a[23]!, some a[24]!] ++ xs.map some
    let pre ← instantiateMVars
      (← mkAppOptM ``Tools.ShippingNoPorts.machine_design_noPorts args)
    if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
    -- the run's facts: zs = raw D w1 hcore hpost hBnd ; xs[9] = entry, xs[10] = closes
    let .forallE _ TF _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's run-facts hypothesis is not where it is expected"
    let hFacts ← forallTelescope TF fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the run-facts hypothesis has {zs.size} binders"
      let p ← mkAppM facts #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← dischargeWith facts p zs[5]! goal hGs)
    let pre := mkApp pre hFacts
    -- the output check under the gate: zs = raw D w1 hcore hpost hg hBnd
    let .forallE _ TO _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallTelescope TO fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      let p ← mkAppM outs #[zs[3]!, zs[4]!, xs[9]!, xs[10]!, zs[5]!]
      mkLambdaFVars zs (← dischargeWith outs p zs[6]! goal hGs)
    let pre := mkApp pre hOuts
    -- the children's bound: zs = raw D w1 hcore hpost hBnd (cut at 6 binders)
    let .forallE _ TM _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's children-bound hypothesis is not where it is expected"
    let hMasked ← forallBoundedTelescope TM (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the children-bound hypothesis has {zs.size} binders"
      let p ← mkAppM masked #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← dischargeWith masked p zs[5]! goal hGs)
    let pre := mkApp pre hMasked
    -- `designCheck` with no check premise: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TD _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's design-check hypothesis is not where it is expected"
    let hDesign ← forallBoundedTelescope TD (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the design-check hypothesis has {zs.size} binders"
      let p ← mkAppM design #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← dischargeWith design p zs[5]! goal hGs)
    mkLambdaFVars (xs ++ hGs) (mkApp pre hDesign)
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  for c in Tools.ShippingNoPortsCommand.forbidden do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{f}: REFUSED, the endpoint's statement still mentions {c}"
  return (type, value)

/-- The closed form of the open endpoint held by the constant `openC` (its
binders: …, `MachineClosesAt f`, then `nExtra` reflections): the closing
replaced by the premises of `cl`; a premise of `cl` that is one of the
trailing reflections is NOT repeated. Nothing is added to the environment. -/
def closedTerm (f openC cl : Name) (nExtra : Nat) : MetaM (Lean.Expr × Lean.Expr) := do
  let info ← getConstInfo openC
  let clT := (← getConstInfo cl).type
  let value ← forallTelescope info.type fun xs _ => do
    let m := xs.size
    unless m ≥ nExtra + 1 do throwError "{openC}: {m} binders"
    let closes := xs[m - 1 - nExtra]!
    let extras := xs.extract (m - nExtra) m
    let front := xs.extract 0 (m - 1 - nExtra)
    let ct ← instantiateMVars (← inferType closes)
    unless ct.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 && ct.getArg! 4 == toExpr f do
      throwError "{openC}: the binder before its {nExtra} trailing reflections is not MachineClosesAt of {f}:{indentExpr ct}"
    let ctx := ct.getAppArgs.extract 0 4
    forallTelescope (← instantiateForall clT ctx) fun hs goal => do
      unless ← isDefEq goal ct do
        throwError "{cl}: proves{indentExpr goal}\nnot{indentExpr ct}"
      let mut keep : Array Lean.Expr := #[]
      let mut args : Array Lean.Expr := #[]
      for h in hs do
        let hT ← instantiateMVars (← inferType h)
        let mut used : Option Lean.Expr := none
        for e in extras do
          if used.isNone then
            if ← isDefEq (← inferType e) hT then used := some e
        match used with
        | some e => args := args.push e
        | none =>
          keep := keep.push h
          args := args.push h
      let body := mkAppN (mkConst openC)
        (front ++ #[mkAppN (mkConst cl) (ctx ++ args)] ++ extras)
      mkLambdaFVars (front ++ keep ++ extras) body
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  if (type.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
    throwError "{openC}: the closed statement still asks MachineClosesAt"
  for c in Tools.ShippingNoPortsCommand.forbidden do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{openC}: REFUSED, the closed statement mentions {c}"
  return (type, value)

/-- `name` ↦ `name_regen`. -/
def regenName (e : Name) : Name :=
  match e with
  | .str p s => Name.str p (s ++ "_regen")
  | n => n ++ `regen

/-- Add `name : type := value`; if `name` EXISTS, add the rebuilt theorem as
`name_regen` (kernel-checked) and require its statement to be `isDefEq` the
existing one — an error otherwise. Returns the constant that holds the
rebuilt theorem and the log word. -/
def addOrCompare (name : Name) (type value : Lean.Expr) : MetaM (Name × String) := do
  if (← getEnv).contains name then
    let old := (← getConstInfo name).type
    unless ← isDefEq old type do
      throwError "{name}: EXISTS with a different statement. Existing:{indentExpr old}\nrebuilt:{indentExpr type}"
    let rn := regenName name
    if (← getEnv).contains rn then
      throwError "{rn}: exists already (the compare path was run twice)"
    Tools.ShippingMachineLinkedCommand.addTheorem rn type value
    return (rn, s!"REBUILT {name}: statement isDefEq the existing one (proof kept as {rn})")
  else
    Tools.ShippingMachineLinkedCommand.addTheorem name type value
    return (name, s!"GENERATED {name}")

/-- The endpoint, its closed form, and the log line. -/
def noPortsKids (f : Name) (n : Nat) : CommandElabM Unit := do
  let (r, calls, kinds) ← scopeK f n
  let ships := f ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  unless (← getEnv).contains ships do
    throwError "{f}: no depth endpoint at depth {n} ({ships} is not there: run #machine_design_svNR {f} {n} first)"
  let mut gates : List Name := []
  for (_, kd) in kinds do
    if let .oneOut g _ := kd then
      unless gates.contains g do gates := gates ++ [g]
  for (k, kd) in kinds do
    match kd with
    | .leaf => discard <| noAsync (Tools.ShippingNoPortsCommand.leafKidTheorem k)
    | .oneOut g nD => discard <| noAsync (oneOutKidTheorem k g nD)
  let c : Ctx := { f, n, nDecl := r.nDecl, calls, kinds, gates }
  let kidsN ← noAsync (kidsTheorem c)
  let (facts, outs, masked, design) ← noAsync (runTheorems c kidsN)
  let name := f ++ Name.mkSimple s!"machine_design_noPortsNR{n}"
  let (openC, line1) ← liftTermElabM <|
    withOptions (fun o => Lean.Elab.async.set o false) do
      let (type, value) ← endpointTerm f gates n facts outs masked design
      addOrCompare name type value
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
        let (type, value) ← closedTerm f openC cl gates.length
        addOrCompare closedN type value
    lines := lines.push (line2 ++ s!" (closing: {cl})")
  let kindLine := kinds.map fun (k, kd) =>
    match kd with
    | .leaf => s!"{k}: leaf register machine"
    | .oneOut g nD => s!"{k}: one-output calls of the gate child {g} (nDecl {nD})"
  logInfo m!"NOPORTS KIDS {f} at depth {n}: {String.intercalate "; " lines.toList}. Callees: {kindLine}; call entries {calls}. The depth endpoint without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents (run facts by {facts}, output check under the gate by {outs}, children's bound by {masked}, designCheck by {design}; KidFacts of the entries by {kidsN}); binders added after those of {ships}: the reflections of the gate grandchildren {gates} at the run's contexts"

/-- `#machine_no_ports_kids f n`: an error where it is refused. -/
elab "#machine_no_ports_kids " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  noPortsKids f n.getNat

/-- The same, a refusal LOGGED (`NOPORTS KIDS REFUSED`) instead of thrown; a
refused declaration leaves nothing in the environment. -/
elab "#machine_no_ports_kids_try " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  try
    noPortsKids f n.getNat
  catch ex =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    logInfo m!"NOPORTS KIDS REFUSED {f} at depth {n.getNat}: {ex.toMessageData}"

end Tools.ShippingNoPortsKidsCommand

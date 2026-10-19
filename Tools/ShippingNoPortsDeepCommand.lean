import Tools.ShippingNoPortsKidsCommand
import Tools.ShippingGenKid
import Tools.ShippingOneOutKidDepth
import Tools.ShippingSeqChildIface
import Tools.ShippingCallsKidsD

/-! # `#machine_no_ports_deep f n`: the check-free depth endpoint at depth `n ≥ 2`, over callees of THREE kinds (G1, unit U3, round par/a-16)

`#machine_no_ports_kids` (`Tools/ShippingNoPortsKidsCommand.lean`, BUILT, not
edited) accepts leaf register machines at every depth and one-output
callees at depth 1, and REFUSES a callee whose own calls are tied by the
general closing. This command generates

    f.machine_design_noPortsNR{n}   (and its `_closed` form)

at a depth `n ≥ 2` for a parent WITH a register under the general closing
whose every distinct callee `k` is one of

* **leaf**: a machine without calls, with a register, with
  `k.machine_closes` — `KidFacts … n` by
  `Tools.ShippingLeafKidFacts.leafKid_facts (k.machine_leafKid …) n`;
* **one-output**: a machine with a register whose calls are all of ONE gate
  child `g` under the one-output closing (`instFields = []`) with the
  constants `#machine_oneout` / `#gate_child` / `#machine_closes_deep` leave —
  `KidFacts … ((n - 1) + 1)` by
  `Tools.ShippingOneOutKidDepth.factsN (k.machine_oneOutKid …) (n - 1)`;
* **general**: a machine with a register whose calls are all of ONE
  declaration `s` under the GENERAL closing (`instFields ≠ []`), with
  `k.closes_deep`, where `s` is a leaf or a one-output machine as above —
  `KidFacts … ((n - 1) + 1)` by `Tools.ShippingGenKid.GenKid.facts` of the
  generated `k.machine_genKid{n - 1}` (the hand `mid_kid` of
  `Tests/Compiler/NoPortsGrandTest.lean` for a leaf `s`, the hand `mid2_kid`
  and `midH_names` of `Tests/Compiler/NoPortsTopD2Test.lean` for a one-output
  `s`; `kidsLo` at `n - 1`, `kidsHi` at `n`).

Everything else is REFUSED with a reason line (`scopeD`): depth below 2, a
parent without a call / without a register / under the one-output closing,
a memory callee, a callee without a machine endpoint or without a register,
a general callee without `closes_deep`, with several different callees, or
whose callee is itself under the general closing (the recursion is not
generated), a premise of `k.closes_deep` that is not the reflection of `k`'s
callee or of its gate.

Generated, in this order:

    s.machine_leafKid / s.machine_oneOutKid     per leaf / one-output declaration (BUILT generators)
    k.machine_genKid{n-1}                       per general callee
    f.machine_kidsD{n}        KidFacts of every call entry's callee (per-entry tables in the reader's order)
    f.machine_runFactsK{n}, _outsGK{n}, _maskedGK{n}, _designPK{n}
                              the BUILT `Tools.ShippingNoPortsKidsCommand.runTheorems`
    f.machine_design_noPortsNR{n}          the head applied to f.machine_ships_hierNR{n}'s arguments
    f.machine_design_noPortsNR{n}_closed   if f.closes_deep or f.machine_closes_at exists

The endpoint takes, after the binders of `f.machine_ships_hierNR{n}`:
`MachineDefines` of every callee `s` of a general callee that is NOT a
direct callee of `f` (in the order met), then `EntryDefines` of every
distinct gate (in the order met) — at the run's contexts. This is the
binder order of the hand endpoints `grand.machine_design_noPortsNR2` (`cnt`)
and `topD2.machine_design_noPortsNR2` (`midH`, `rcH`).

## How the BUILT run-theorem generator is reused

`Tools.ShippingNoPortsKidsCommand.runTheorems` reads from its `Ctx` only:
`f`, `n`, `nDecl`, the binders (`MachineDefines` of the names of `kinds`,
then `EntryDefines` of `gates`), and the per-entry tables (`outsOf` by the
callee's name; `insOf`: `declWidths` for `.leaf`, `argWidths … nD` for
`.oneOut _ nD`). `DeepScope.toK` builds that `Ctx`: `kinds` = the direct callees
followed by the extra machines (as `.leaf`: only their binder is read); a
GENERAL callee is entered as `.oneOut .anonymous nD` — only its declared
binder count is read (the table `argWidths k.machineData nD`, the `ins` of
`GenKid.facts`). `Ctx.factOf` (which would read the kind) is NOT used: the
entries' `KidFacts` are this file's `kidsTheoremD`.

## The compare path (never a silent return)

As `#machine_no_ports_kids` (`addOrCompare`, BUILT): if the endpoint (resp.
its `_closed`) EXISTS, it is rebuilt all the same, added as `…_regen`
(kernel-checked), and its statement must be `isDefEq` the existing one — an
ERROR otherwise. The log says `REBUILT … isDefEq` or `GENERATED`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingNoPortsDeepCommand
open Lean Meta Elab Command
open Tools.ShippingShipsFreeCommand (checkMade)
-- the whole namespace (not a name list): `Ctx.hR`, `Kind.leaf` are used qualified
-- by their type's name; used from it: Ctx, Kind, oneOutKidTheorem, runTheorems,
-- dischargeWith, closedTerm, addOrCompare
open Tools.ShippingNoPortsKidsCommand

/-- What the callee of a general callee is. -/
inductive SubKind where
  /-- a leaf register machine -/
  | leaf
  /-- a register machine with one-output calls of the gate child `gate`;
  `nDecl`: its declared binders -/
  | oneOut (gate : Name) (nDecl : Nat)
  deriving Inhabited

/-- What a direct callee is, for this command. -/
inductive KindD where
  | leaf
  | oneOut (gate : Name) (nDecl : Nat)
  /-- a register machine (declared binders `nDecl`) whose calls are all of
  `sub`, tied by the general closing -/
  | gen (nDecl : Nat) (sub : Name) (subKind : SubKind)
  deriving Inhabited

private def nm (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)

private def noAsync {α : Type} (x : CommandElabM α) : CommandElabM α :=
  withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false }) x

/-- `k` (read as `cr`, with calls, `instFields = []`) is a one-output callee
this command can use: its ONE callee is a gate child with `#gate_child`
data, and the `oneout` constants are there. Returns the gate. `who` starts
the refusal line. -/
def oneOutGate (who : String) (k : Name) (cr : Tools.ShippingMachineCommand.Read) :
    CommandElabM Name := do
  let env ← getEnv
  let gs := (cr.shape.insts.map (·.1)).eraseDups
  let [g] := gs
    | throwError "{who} {k} calls several different declarations {gs} (generated for ONE gate callee only)"
  -- `g.gate_peel` present means a GATE child (such a declaration may ALSO
  -- have `g.machineData`), as the BUILT generators decide it
  unless env.contains (g ++ `gate_peel) do
    if env.contains (g ++ `machineData) then
      throwError "{who} {k}'s callee {g} is a machine child under the ONE-OUTPUT closing (no {g}.gate_peel; generated for a GATE callee only)"
    else
      throwError "{who} {k}'s callee {g} has no #gate_child data (no {g}.gate_peel)"
  for sfx in [`gate_old, `gate_wf, `gateBinders, `gateSort] do
    unless env.contains (g ++ sfx) do
      throwError "{who} {k}'s callee {g} is not a gate child with #gate_child data (no {g ++ sfx})"
  for c in [g ++ `gate_full, g ++ `gate_kidK, g ++ `gateValue, k ++ `oneout_callsOk,
      k ++ `oneout_slotLen, k ++ `oneout_domB, k ++ `oneout_insts, k ++ `oneout_instFields,
      k ++ `oneout_slots, k ++ `oneout_outChars,
      k ++ `oneout_nomem, k ++ `machine_portsRawH, k ++ `closes_deep] do
    unless env.contains c do
      throwError "{who} {k} lacks {c} (run #gate_child {g}, #machine_design_svHR {k}, #machine_oneout {k} and a depth command that leaves {k}.closes_deep first)"
  return g

/-- The reading of a machine callee `k` with a register (refusals otherwise). -/
def readKid (who : String) (k : Name) : CommandElabM Tools.ShippingMachineCommand.Read := do
  let env ← getEnv
  -- `k.gate_peel` present means a GATE child for the generators, even when
  -- `k.machineData` exists too
  if env.contains (k ++ `gate_peel) then
    throwError "{who} {k} is a GATE child ({k}.gate_peel exists) under a general closing (no KidFacts for it)"
  if (Sparkle.Compiler.MachMemory.memChild? k).isSome then
    throwError "{who} {k} carries a memory placeholder NAME — a memory child, or a declaration declared under that name (a name collision); this command classifies by name (no KidFacts for it)"
  unless env.contains (k ++ `machineData) && env.contains (k ++ `machine_ok) &&
      env.contains (k ++ `machine_body) do
    throwError "{who} {k} has no machine endpoint (a gate child of a general-closing parent, or #machine_endpoint was not run on it)"
  let cr ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine k
  if cr.shape.layout.slots.isEmpty then
    throwError "{who} {k} has no register (LeafKid.slots / OneOutKid.slots / GenKid.slots ask one)"
  return cr

/-- The scope, with its reasons: the reading of `f`, its call entries'
callees, the distinct callees with their kinds. -/
def scopeD (f : Name) (n : Nat) :
    CommandElabM (Tools.ShippingMachineCommand.Read × List Name × List (Name × KindD)) := do
  let env ← getEnv
  unless n ≥ 2 do
    throwError "{f}: depth {n} (this command is for depth ≥ 2: GenKid.facts gives KidFacts at a depth m + 1 with m ≥ 1 here; #machine_no_ports_kids is the command for depth 1)"
  unless env.contains (f ++ `machineData) && env.contains (f ++ `machine_ok) &&
      env.contains (f ++ `machine_body) do
    throwError "{f}: not a machine with an endpoint (no {f}.machineData / machine_ok / machine_body: #machine_endpoint was not run on it)"
  let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine f
  let calls := r.shape.insts.map (·.1)
  if calls.isEmpty then throwError "{f}: no call (nothing to match: no instance statement)"
  if r.shape.layout.slots.isEmpty then
    throwError "{f}: parent without a register (kids_runFacts / kids_designCheck ask d.shape.layout.slots ≠ [])"
  if r.shape.instFields.isEmpty then
    throwError "{f}: a parent under the one-output closing (instFields = []; kids_* ask the general closing)"
  let mut kinds : List (Name × KindD) := []
  for k in calls.eraseDups do
    let cr ← readKid s!"{f}: the callee" k
    if cr.shape.insts.isEmpty then
      unless env.contains (k ++ `machine_closes) do
        throwError "{f}: the leaf callee {k} has no {k}.machine_closes (its closing in every context is not derived)"
      kinds := kinds ++ [(k, KindD.leaf)]
    else if cr.shape.instFields.isEmpty then
      let g ← oneOutGate s!"{f}: the one-output callee" k cr
      kinds := kinds ++ [(k, KindD.oneOut g cr.nDecl)]
    else
      -- a callee under the general closing: the GenKid shape
      unless env.contains (k ++ `closes_deep) do
        throwError "{f}: the general-closing callee {k} has no {k}.closes_deep (run #machine_closes_deep on a parent of it first)"
      let ss := (cr.shape.insts.map (·.1)).eraseDups
      let [s] := ss
        | throwError "{f}: the general-closing callee {k} calls several different declarations {ss} (GenKid is generated for ONE callee only: the per-entry tables and KidNames of several are not generated)"
      if env.contains (s ++ `gate_peel) then
        throwError "{f}: the general-closing callee {k} calls the GATE child {s} (a gate child directly under a general closing has no KidFacts)"
      let sr ← readKid s!"{f}: the general-closing callee {k}'s callee" s
      if sr.shape.insts.isEmpty then
        unless env.contains (s ++ `machine_closes) do
          throwError "{f}: the general-closing callee {k}'s leaf callee {s} has no {s}.machine_closes"
        kinds := kinds ++ [(k, KindD.gen cr.nDecl s SubKind.leaf)]
      else if sr.shape.instFields.isEmpty then
        let g ← oneOutGate s!"{f}: the general-closing callee {k}'s one-output callee" s sr
        kinds := kinds ++ [(k, KindD.gen cr.nDecl s (SubKind.oneOut g sr.nDecl))]
      else
        throwError "{f}: the general-closing callee {k}'s callee {s} is itself under the GENERAL closing (instFields ≠ []): GenKid of {k} needs GenKid of {s} one depth lower and KidNames of {s} by kidsChild_of_real over its fields — this recursion is not generated"
  return (r, calls, kinds)

/-- The premises of `k.closes_deep` after its four contexts, in order: each
must be the reflection of `s` (`true`) or of the gate `g?` (`false`). -/
def closesPremises (f k s : Name) (g? : Option Name) : MetaM (Array Bool) := do
  let cl := k ++ `closes_deep
  let info ← getConstInfo cl
  forallTelescope info.type fun xs _ => do
    let mut out : Array Bool := #[]
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if ← isProp t then
        if t.isAppOfArity ``Tools.ShippingMachineEntry.MachineDefines 6 then
          let a := t.getArg! 4
          if a == toExpr s || (← isDefEq a (toExpr s)) then
            out := out.push true
          else
            throwError "{f}: {cl} asks the reflection of a machine that is not {k}'s callee {s}:{indentExpr t}"
        else if t.isAppOfArity ``Tools.ShippingInlineSoundness.EntryDefines 6 then
          let a := t.getArg! 4
          match g? with
          | some g =>
            if a == toExpr g || (← isDefEq a (toExpr g)) then
              out := out.push false
            else
              throwError "{f}: {cl} asks the reflection of a gate that is not {s}'s gate callee {g}:{indentExpr t}"
          | none =>
            throwError "{f}: {cl} asks the reflection of a gate, but {k}'s callee {s} is a leaf:{indentExpr t}"
        else
          throwError "{f}: {cl} has a premise that is not a reflection (a name-separation premise is not discharged here):{indentExpr t}"
    return out

/-- **`k.machine_genKid{d}`, generated** (the hand `mid_kid` / `mid2_kid`):
the interface `GenKid … d` of the general-closing callee `k` whose every
call entry is of `s`, from the reflections of `k`, of `s` and (for a
one-output `s`) of its gate, in any contexts. `d ≥ 1`. -/
def genKidTheorem (f k s : Name) (sk : SubKind) (nDeclK d : Nat) : CommandElabM Name := do
  let name := k ++ Name.mkSimple s!"machine_genKid{d}"
  if (← getEnv).contains name then return name
  unless d ≥ 1 do throwError "{f}: GenKid of {k} at depth {d} (generated for depth ≥ 1)"
  let data := nm k "machineData"
  let sdata := nm s "machineData"
  let kq : Term := quote k
  let sq : Term := quote s
  let nD := Syntax.mkNumLit (toString nDeclK)
  let dLit := Syntax.mkNumLit (toString d)
  let dHi := Syntax.mkNumLit (toString (d + 1))
  let dLo := Syntax.mkNumLit (toString (d - 1))
  let g? : Option Name := match sk with
    | SubKind.leaf => none
    | SubKind.oneOut g _ => some g
  let prems ← liftTermElabM <| closesPremises f k s g?
  let closeArgs : Array Term ← prems.mapM fun isM =>
    if isM then `((Tools.ShippingReflectCtx.MachineDefines.ctx hRs))
    else `((Tools.ShippingReflectCtx.EntryDefines.ctx hG))
  -- `Syntax.mkApp`: no application node when `k.closes_deep` has no premise
  let closesT : Term := Syntax.mkApp (nm k "closes_deep") closeArgs
  let kidOuts ← `(fun _ => ($sdata).shape.layout.outs)
  let mut gBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut declsF : Term ← `(fun _ => ([] : List Lean.Name))
  let mut namesK : Term ← `(fun _ => ([] : List Lean.Name).map fun n => Sparkle.IR.ModuleName.ofDecl n)
  let mut kidIns : Term ← `(fun _ => Tools.ShippingPortWidthsPure.declWidths $sdata)
  let mut kidTac ← `(tactic|
    exact Tools.ShippingCallsKidsD.ChildIfaceD.kid (Tools.ShippingCallsKidsD.ChildIfaceG.toD
      (Tools.ShippingSeqChildIface.seqChild_of_real $sdata $(nm s "machine_ok")
        $(nm s "machine_body") rfl (by decide) hRs
        (fun mc cc => $(nm s "machine_closes") mc _ cc _) hy)))
  let mut lo : Term ←
    `(Tools.ShippingLeafKidFacts.leafKid_facts ($(nm s "machine_leafKid") hRs) $dLit)
  let mut hi : Term ←
    `(Tools.ShippingLeafKidFacts.leafKid_facts ($(nm s "machine_leafKid") hRs) $dHi)
  if let SubKind.oneOut g nDs := sk then
    let gq : Term := quote g
    let nDsLit := Syntax.mkNumLit (toString nDs)
    let sNames : Term ← `(fun _ => ([] : List Lean.Name).map fun n => Sparkle.IR.ModuleName.ofDecl n)
    gBinders := #[← `(bracketedBinder|
      (hG : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $gq
        $(nm g "gateValue")))]
    declsF ← `(fun _ => Tools.ShippingKidsChildIface.declsOf $sdata
      (fun _ => ([] : List Lean.Name)))
    namesK ← `(fun _ => (Tools.ShippingKidsChildIface.declsOf $sdata
      (fun _ => ([] : List Lean.Name))).map fun n => Sparkle.IR.ModuleName.ofDecl n)
    kidIns ← `(fun _ => Tools.ShippingCallsChildPorts.argWidths $sdata $nDsLit)
    kidTac ← `(tactic| (
      have K := $(nm s "machine_oneOutKid") hRs hG
      have h0 := Tools.ShippingCallsKidsD.ChildIfaceD.kid
        (Tools.ShippingKidsChildIface.kidsChild_of_real $sdata
          K.ok K.body K.calls K.ss K.dom K.insts K.slots K.outTy $nDsLit K.hkD K.hIlen K.hSL
          K.hSlen K.hLlen K.hNIn $sNames K.nomem K.kid K.self (K.entry mctx cctx)
          (fun mc cc _ => K.closes mc cc) hy)
      have hnm : Tools.ShippingKidsChildIface.namesOf $sdata $sNames =
          (Tools.ShippingKidsChildIface.declsOf $sdata
            (fun _ => ([] : List Lean.Name))).map fun n => Sparkle.IR.ModuleName.ofDecl n :=
        Tools.ShippingKidsChildIface.namesOf_map $sdata (fun _ => ([] : List Lean.Name))
      rw [hnm] at h0
      exact h0))
    lo ← `(Tools.ShippingOneOutKidDepth.factsN ($(nm s "machine_oneOutKid") hRs hG) $dLo)
    hi ← `(Tools.ShippingOneOutKidDepth.factsN ($(nm s "machine_oneOutKid") hRs hG) $dLit)
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    set_option maxHeartbeats 4000000 in
    theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State}
        (hRk : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $kq ($data).shape)
        (hRs : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $sq
          ($sdata).shape) $gBinders* :
        Tools.ShippingGenKid.GenKid mref cref $kq $data $nD $namesK $kidOuts $kidIns $dLit :=
      have hent : ∀ (k : Nat) (hk : k < ($data).shape.insts.length),
          (($data).shape.insts[k]).1 = $sq := (by decide)
      { ok := $(nm k "machine_ok")
        body := $(nm k "machine_body")
        calls := by decide
        ss := by decide
        dom := by decide
        insts := fun h0 => absurd (congrArg List.length h0) (by decide)
        general := fun h0 => absurd (congrArg List.length h0) (by decide)
        slots := fun h0 => absurd (congrArg List.length h0) (by decide)
        outTy := by decide
        outName := fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
          ((show ∀ o ∈ ($data).shape.layout.outs, ∀ c ∈ o.name.toList,
              Sparkle.IR.NameHints.charOk c = true from by
            first | decide | decide +kernel) o ho)
        outScalar := by decide
        nomem := by decide
        hkD := by decide
        hIlen := by decide
        hSL := by decide
        hSlen := by decide
        hLlen := by decide
        hNIn := by decide
        kid := by
          intro k hk y hy
          rw [hent k hk] at hy ⊢
          $kidTac:tactic
        self := by
          have hnm : Tools.ShippingKidsChildIface.namesOf $data $namesK =
              (Tools.ShippingKidsChildIface.declsOf $data $declsF).map fun n => Sparkle.IR.ModuleName.ofDecl n :=
            Tools.ShippingKidsChildIface.namesOf_map $data $declsF
          rw [hnm]
          exact Tools.ShippingNameSep.Enc.not_mem_map_of _ _ (by first | decide | decide +kernel)
        kidsLo := by
          intro k hk
          rw [hent k hk]
          exact $lo
        kidsHi := by
          intro k hk
          rw [hent k hk]
          exact $hi
        callW := by first | decide | decide +kernel
        callA := by first | decide | decide +kernel
        entry := fun _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx hRk
        closes := fun _ _ => $closesT }))
  checkMade name before
  return name

/-- What is generated for `f` at depth `n`. -/
structure DeepScope where
  f : Name
  n : Nat
  nDecl : Nat
  calls : List Name
  kinds : List (Name × KindD)
  /-- callees of general callees that are not direct callees -/
  extraM : List Name
  /-- the distinct gates -/
  gates : List Name

namespace DeepScope

def kids (c : DeepScope) : List Name := c.kinds.map (·.1)

/-- The `Ctx` of the BUILT generator carrying this scope's binders and
tables (see the header: a general callee is entered as `.oneOut .anonymous
nD`, an extra machine as `.leaf`; `Ctx.factOf` is not used). -/
def toK (c : DeepScope) : Ctx :=
  { f := c.f
    n := c.n
    nDecl := c.nDecl
    calls := c.calls
    kinds := (c.kinds.map fun (k, kd) =>
        match kd with
        | KindD.leaf => (k, Kind.leaf)
        | KindD.oneOut g nD => (k, Kind.oneOut g nD)
        | KindD.gen nD _ _ => (k, Kind.oneOut Lean.Name.anonymous nD)) ++
      c.extraM.map fun s => (s, Kind.leaf)
    gates := c.gates }

/-- The reflection binder of the machine `d` (a direct callee or an extra
machine), among the binders of `c.toK`. -/
def hM (c : DeepScope) (d : Name) : Ident := Ctx.hR ((c.kids ++ c.extraM).idxOf d)

def hGate (c : DeepScope) (g : Name) : Ident := Ctx.hG (c.gates.idxOf g)

/-- `KidFacts` of the direct callee `k` at depth `c.n`, from the binders. -/
def factOf (c : DeepScope) (k : Name) : CommandElabM Term := do
  let nLit := Syntax.mkNumLit (toString c.n)
  let nLo := Syntax.mkNumLit (toString (c.n - 1))
  -- the scrutinee's type is stated: the elaborator does not read it off the
  -- projection of a list of pairs (first build: "Invalid dotted identifier")
  let entry? : Option (Name × KindD) := c.kinds.find? fun p => p.1 == k
  let kd? : Option KindD := entry?.map fun p => p.2
  match kd? with
  | some (KindD.oneOut g _) =>
    `(Tools.ShippingOneOutKidDepth.factsN
      ($(nm k "machine_oneOutKid") $(c.hM k) $(c.hGate g)) $nLo)
  | some (KindD.gen _ s sk) =>
    let gk := mkIdent (`_root_ ++ k ++ Name.mkSimple s!"machine_genKid{c.n - 1}")
    match sk with
    | SubKind.leaf => `(Tools.ShippingGenKid.GenKid.facts ($gk $(c.hM k) $(c.hM s)))
    | SubKind.oneOut g _ =>
      `(Tools.ShippingGenKid.GenKid.facts ($gk $(c.hM k) $(c.hM s) $(c.hGate g)))
  | _ =>
    `(Tools.ShippingLeafKidFacts.leafKid_facts ($(nm k "machine_leafKid") $(c.hM k)) $nLit)

end DeepScope

/-- **`f.machine_kidsD{n}`, generated**: `KidFacts` of every call entry's
callee, against the per-entry tables of `c.toK` (those the BUILT
`runTheorems` states its theorems with). -/
def kidsTheoremD (c : DeepScope) : CommandElabM Name := do
  let name := c.f ++ Name.mkSimple s!"machine_kidsD{c.n}"
  if (← getEnv).contains name then return name
  let K := c.toK
  let data := nm c.f "machineData"
  let nLit := Syntax.mkNumLit (toString c.n)
  let nCalls := Syntax.mkNumLit (toString c.calls.length)
  let kidOuts ← K.kidOuts
  let kidIns ← K.kidIns
  -- `K.kidOuts` is the constant function exactly when `K.kids` has one name
  let tacKid ← if K.kids.length == 1 then do
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
  let bs ← K.binders
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

/-- The statement and the proof of `f.machine_design_noPortsNR{n}`:
`Tools.ShippingNoPortsKidsCommand.endpointTerm`, copied, with ONE change:
after the binders of `f.machine_ships_hierNR{n}` come `MachineDefines` of
the machines `extraM`, then `EntryDefines` of `gates`. Nothing is added to
the environment. -/
def endpointTermX (f : Name) (extraM gates : List Name) (n : Nat)
    (facts outs masked design : Name) : MetaM (Lean.Expr × Lean.Expr) := do
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
    let mDecls : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) :=
      extraM.toArray.mapIdx fun i s =>
        (Name.mkSimple s!"hX{i}", fun (_ : Array Lean.Expr) => do
          let shape ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape
            #[mkConst (s ++ `machineData)]
          mkAppM ``Tools.ShippingMachineEntry.MachineDefines
            #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, toExpr s, shape])
    let gDecls : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) :=
      gates.toArray.mapIdx fun i g =>
        (Name.mkSimple s!"hG{i}", fun (_ : Array Lean.Expr) =>
          mkAppM ``Tools.ShippingInlineSoundness.EntryDefines
            #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, toExpr g, mkConst (g ++ `gateValue)])
    withLocalDeclsD (mDecls ++ gDecls) fun hEx => do
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
      mkLambdaFVars zs (← dischargeWith facts p zs[5]! goal hEx)
    let pre := mkApp pre hFacts
    -- the output check under the gate: zs = raw D w1 hcore hpost hg hBnd
    let .forallE _ TO _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallTelescope TO fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      let p ← mkAppM outs #[zs[3]!, zs[4]!, xs[9]!, xs[10]!, zs[5]!]
      mkLambdaFVars zs (← dischargeWith outs p zs[6]! goal hEx)
    let pre := mkApp pre hOuts
    -- the children's bound: zs = raw D w1 hcore hpost hBnd (cut at 6 binders)
    let .forallE _ TM _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's children-bound hypothesis is not where it is expected"
    let hMasked ← forallBoundedTelescope TM (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the children-bound hypothesis has {zs.size} binders"
      let p ← mkAppM masked #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← dischargeWith masked p zs[5]! goal hEx)
    let pre := mkApp pre hMasked
    -- `designCheck` with no check premise: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TD _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's design-check hypothesis is not where it is expected"
    let hDesign ← forallBoundedTelescope TD (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the design-check hypothesis has {zs.size} binders"
      let p ← mkAppM design #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← dischargeWith design p zs[5]! goal hEx)
    mkLambdaFVars (xs ++ hEx) (mkApp pre hDesign)
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  for c in Tools.ShippingNoPortsCommand.forbidden do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{f}: REFUSED, the endpoint's statement still mentions {c}"
  return (type, value)

/-- The endpoint, its closed form, and the log line. -/
def noPortsDeep (f : Name) (n : Nat) : CommandElabM Unit := do
  let (r, calls, kinds) ← scopeD f n
  let env ← getEnv
  let ships := f ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  unless env.contains ships do
    throwError "{f}: no depth endpoint at depth {n} ({ships} is not there: run #machine_design_svNR {f} {n} first)"
  let direct := kinds.map (·.1)
  let mut gates : List Name := []
  let mut extraM : List Name := []
  for (_, kd) in kinds do
    match kd with
    | KindD.leaf => pure ()
    | KindD.oneOut g _ => unless gates.contains g do gates := gates ++ [g]
    | KindD.gen _ s sk =>
      unless direct.contains s || extraM.contains s do extraM := extraM ++ [s]
      if let SubKind.oneOut g _ := sk then
        unless gates.contains g do gates := gates ++ [g]
  -- the per-declaration interfaces (the BUILT generators), then GenKid
  for (k, kd) in kinds do
    match kd with
    | KindD.leaf => discard <| noAsync (Tools.ShippingNoPortsCommand.leafKidTheorem k)
    | KindD.oneOut g nD => discard <| noAsync (oneOutKidTheorem k g nD)
    | KindD.gen nD s sk =>
      match sk with
      | SubKind.leaf => discard <| noAsync (Tools.ShippingNoPortsCommand.leafKidTheorem s)
      | SubKind.oneOut g nDs => discard <| noAsync (oneOutKidTheorem s g nDs)
      discard <| noAsync (genKidTheorem f k s sk nD (n - 1))
  let c : DeepScope := { f, n, nDecl := r.nDecl, calls, kinds, extraM, gates }
  let kidsN ← noAsync (kidsTheoremD c)
  let (facts, outs, masked, design) ← noAsync (runTheorems c.toK kidsN)
  let name := f ++ Name.mkSimple s!"machine_design_noPortsNR{n}"
  let (openC, line1) ← liftTermElabM <|
    withOptions (fun o => Lean.Elab.async.set o false) do
      let (type, value) ← endpointTermX f extraM gates n facts outs masked design
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
        let (type, value) ← closedTerm f openC cl (extraM.length + gates.length)
        addOrCompare closedN type value
    lines := lines.push (line2 ++ s!" (closing: {cl})")
  let kindLine := kinds.map fun (k, kd) =>
    match kd with
    | KindD.leaf => s!"{k}: leaf register machine"
    | KindD.oneOut g nD => s!"{k}: one-output calls of the gate child {g} (nDecl {nD})"
    | KindD.gen nD s sk =>
      match sk with
      | SubKind.leaf => s!"{k}: general closing over the leaf register machine {s} (nDecl {nD}; GenKid at {n - 1})"
      | SubKind.oneOut g nDs => s!"{k}: general closing over {s}, which has one-output calls of the gate child {g} (nDecl {nD}, {nDs}; GenKid at {n - 1})"
  logInfo m!"NOPORTS DEEP {f} at depth {n}: {String.intercalate "; " lines.toList}. Callees: {kindLine}; call entries {calls}. The depth endpoint without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents (run facts by {facts}, output check under the gate by {outs}, children's bound by {masked}, designCheck by {design}; KidFacts of the entries by {kidsN}); binders added after those of {ships}: the reflections of the machines {extraM} and of the gates {gates} at the run's contexts"

/-- `#machine_no_ports_deep f n`: an error where it is refused. -/
elab "#machine_no_ports_deep " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  noPortsDeep f n.getNat

/-- The same, a refusal LOGGED (`NOPORTS DEEP REFUSED`) instead of thrown; a
refused declaration leaves nothing in the environment. -/
elab "#machine_no_ports_deep_try " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  try
    noPortsDeep f n.getNat
  catch ex =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    logInfo m!"NOPORTS DEEP REFUSED {f} at depth {n.getNat}: {ex.toMessageData}"

end Tools.ShippingNoPortsDeepCommand

import Lean.Elab.Command
import Tools.ShippingEntryOkCommand
import Tools.ShippingMachineClosesGen
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # `#entry_ok_all`: `EntryOk` swept over an environment, and two refusals removed

WRITTEN, NOT BUILT (par/a-42). A generator and a measurement; nothing here
is a proof about the compiler. The built `Tools/ShippingEntryOkCommand.lean`
is not edited: its helpers and its leaf generators are reused.

## What is wider than `#entry_ok`

(a) **A machine leaf without `f.machine_closes`** (the slotless leaves, and
    any register leaf no closing was generated for). The leaf interface
    `seqChild_of_real` has no hypothesis about slots (read:
    `Tools/ShippingSeqChildIface.lean`, `seqChild_iface`), so the built leaf
    generator applies as soon as the closing is there; it is produced by the
    built `Tools.ShippingMachineClosesGen.closesTheorem?` (from the
    declaration's own checks and `letsOk`, or from "no `let`, no call") —
    the function worker B's leaf sweeps use. If the leaf then fails, the
    environment is put back (no `machine_closes` is left).

(b) **A parent whose closing has another name or form.** Instead of three
    names, EVERY constant `f.<…closes…>` of the environment whose statement
    concludes `MachineClosesAt … f …` or `MachineCloses … f …` is a
    candidate (`closingsOf`): `closes_deep` (and its suffixed twins),
    `machine_closes_at`, `machine_closes`, `noPortsMem_closes`,
    `noPortsMemSeq_closes`, and whatever else a generator left. A candidate
    is used when its premises are discharged by the reflections at hand
    (`apply … <;> exact (….ctx hRᵢ)`); one with another premise (a name
    condition kept as a binder) is skipped. `closes_shared` concludes
    `MachineClosesAtS` and is NOT a candidate.

Because (b) admits the memory routes' closings, a parent with MEMORY call
entries is now ATTEMPTED (it was refused): `entryOk_machine` asks `K` only
of the non-memory callees (`hinsG`), and nothing of the callees when the
closing is the general one (`hinsM`: `instFields` not empty). Whether the
attempt goes through is NOT known — `hout_of_data` asks `callsOk`, which the
memory routes may not satisfy; a failure is a row with the reason
`memory call entry`.

The generated constant is the same `f.entry_ok`, with the same statement
form, checked by the built `checkEntryOk`.

## Commands

* `#entry_ok_wide f` — one declaration; never an error; one `ENTRYOKW` row.
* `#entry_ok_all n` — every declaration of the environment with generated
  data (`f.machineData` or `f.gateValue`), in dependency order (the height
  of the call tree, then the name), at most `n` and within `budgetMs`; the
  ones left out are counted. Never an error.
* `#entry_ok_all_summary` — the rows by kind and by reason.

Reasons of a row that is not `GENERATED` / `EXISTS`: `memory call entry`
(attempted, failed), `callee without entry_ok`, `missing data fact`,
`no closing theorem`, `no route` (neither the machine reader nor a gate
child), `failed` (with the message). No class and no count is expected by
this file. -/
namespace Tools.ShippingEntryOkWide
open Lean Meta Elab Command
open Tools.ShippingEntryOkCommand (Outcome sub reflection transported disj inject elimDisj
  firstOf runGenerated checkEntryOk ensureWf harnessTerm missing)

/-- What the compiler's reader says of a declaration (read off the SOURCE;
no reflected data is evaluated). -/
structure Info where
  /-- the machine reader reads it -/
  machine : Bool
  /-- `f.gateValue` exists -/
  gate : Bool
  /-- the non-memory call entries, distinct, in order -/
  callees : List Name
  hasMem : Bool
  hasCalls : Bool
  nDecl : Nat
  deriving Inhabited

initialize infoCache : IO.Ref (Std.HashMap Name Info) ← IO.mkRef {}

def infoOf (f : Name) : MetaM Info := do
  if let some i := (← infoCache.get).get? f then return i
  let env ← getEnv
  let shape? : Option Sparkle.Compiler.Elab.MachineShape ←
    try
      let r ← Tools.ShippingMachineCommand.readMachine f
      pure (some r.shape)
    catch _ => pure none
  let gate := env.contains (f ++ `gateValue)
  let i : Info := match shape? with
    | some shape =>
      let names := shape.insts.map (·.1)
      -- origin dispatch (patched compiler): an entry is a memory by its ORIGIN
      let tagged := shape.instTagged
      { machine := true, gate := gate
        callees := ((tagged.filter fun x => x.2.child?.isNone).map (·.1)).eraseDups
        hasMem := tagged.any fun x => x.2.child?.isSome
        hasCalls := !names.isEmpty
        nDecl := shape.binders.length - shape.insts.length - shape.layout.slots.length -
          shape.layout.lets }
    | none =>
      { machine := false, gate := gate, callees := [], hasMem := false, hasCalls := false,
        nDecl := 0 }
  infoCache.modify (·.insert f i)
  return i

/-- The non-memory descendants: the callees in order, each followed by its
own, first occurrences kept (the order of `#entry_ok`). -/
partial def descendantsW (f : Name) (fuel : Nat := 16) : MetaM (List Name) := do
  if fuel == 0 then return []
  let i ← infoOf f
  let mut out : List Name := []
  for c in i.callees do
    out := out ++ [c] ++ (← descendantsW c (fuel - 1))
  return out.eraseDups

/-- The height of the call tree (0: no non-memory callee). -/
partial def heightOf (f : Name) (fuel : Nat := 16) : MetaM Nat := do
  if fuel == 0 then return 0
  let i ← infoOf f
  let mut h : Nat := 0
  for c in i.callees do
    h := max h (1 + (← heightOf c (fuel - 1)))
  return h

private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The closing constants of `f`: `(constant, concludes MachineClosesAt)`.
Every `f.<…closes…>` whose statement concludes `MachineClosesAt` or
`MachineCloses`; the `…At` ones first, each group in name order. -/
def closingsOf (f : Name) : MetaM (List (Name × Bool)) := do
  let env ← getEnv
  let found : Array (Name × Bool) := env.constants.fold (fun acc nm ci =>
    match nm with
    | .str p s =>
      if p == f && has s "closes" then
        let hd := ci.type.getForallBody.getAppFn
        if hd.isConstOf ``Tools.ShippingChildInv.MachineClosesAt then acc.push (nm, true)
        else if hd.isConstOf ``Tools.ShippingMachineEntry.MachineCloses then acc.push (nm, false)
        else acc
      else acc
    | _ => acc) #[]
  let sorted := found.qsort fun a b =>
    (a.2 && !b.2) || (a.2 == b.2 && decide (a.1.toString < b.1.toString))
  return sorted.toList

/-- The closing at the goal's contexts, from the candidates. -/
def closingTacticW (cands : List (Name × Bool)) (hyps : List (Ident × Bool)) :
    CommandElabM (Option (TSyntax `tactic)) := do
  let mut exacts : List (TSyntax `tactic) := []
  for (h, machine) in hyps do
    let t ← transported h machine
    exacts := exacts ++ [← `(tactic| exact $t)]
  let discharge ← firstOf exacts
  let mut alts : List (TSyntax `tactic) := []
  for (c, isAt) in cands do
    let cid := mkIdent (`_root_ ++ c)
    if isAt then
      alts := alts ++ [← `(tactic| (apply $cid <;> $discharge:tactic))]
    else
      alts := alts ++ [← `(tactic|
        (refine Tools.ShippingChildInv.machineClosesAt_of_closes ?_
         apply $cid <;> $discharge:tactic))]
  if alts.isEmpty then return none
  return some (← firstOf alts)

/-- `f.entry_ok` of a parent: the built generator's text, with the closing
taken from `cands`, the descendants memory-aware, and the two callee
conditions split by whether there is a memory call entry. -/
def genParentW (f : Name) (info : Info) (cands : List (Name × Bool)) : CommandElabM Unit := do
  ensureWf f
  let fq : Term := quote f
  let L := mkIdent `L
  let ds ← liftTermElabM (descendantsW f)
  let n := ds.length
  let all := f :: ds
  let mut hyps : List (Name × Ident × Bool) := []
  let mut i : Nat := 0
  for d in all do
    let di ← liftTermElabM (infoOf d)
    hyps := hyps ++ [(d, mkIdent (Name.mkSimple s!"hR{i}"), di.machine)]
    i := i + 1
  let hypOf (d : Name) : CommandElabM (Ident × Bool) := do
    match hyps.find? (·.1 == d) with
    | some (_, h, m) => pure (h, m)
    | none => throwError "{f}: no reflection hypothesis for {d}"
  let (h0, _) ← hypOf f
  let k := mkIdent `k
  let kset ← disj k ds
  let x := mkIdent `x
  let xfst ← `(($x).1)
  let calleesProp ← disj xfst ds
  let md := sub f "machineData"
  -- the callee conditions
  let (hinsM, hinsG) : Term × Term ←
    if !info.hasMem then do
      unless (← getEnv).contains (f ++ `entry_callees) do
        runGenerated s!"{f}.entry_callees" (← `(command|
          theorem $(sub f "entry_callees") :
              ∀ $x, $x ∈ ($md).shape.insts → $calleesProp := by
            first | decide | decide +kernel))
      -- origin dispatch (patched compiler): the general closing maps the
      -- TAGGED entries (`shape.instTagged`), so its callee condition is over them
      unless (← getEnv).contains (f ++ `entry_calleesT) do
        runGenerated s!"{f}.entry_calleesT" (← `(command|
          theorem $(sub f "entry_calleesT") :
              ∀ $x, $x ∈ ($md).shape.instTagged → $calleesProp := by
            first | decide | decide +kernel))
      pure (← `(fun _ x hx => $(sub f "entry_callees") x hx),
            ← `(fun x hx _ => $(sub f "entry_calleesT") x hx))
    else do
      unless (← getEnv).contains (f ++ `entry_calleesWT) do
        runGenerated s!"{f}.entry_calleesWT" (← `(command|
          theorem $(sub f "entry_calleesWT") :
              ∀ $x, $x ∈ ($md).shape.instTagged →
                ($x).2.child?.isNone = true → $calleesProp := by
            first | decide | decide +kernel))
      pure (← `(fun hEmpty => absurd hEmpty (by first | decide | decide +kernel)),
            ← `(fun x hx hm => $(sub f "entry_calleesWT") x hx hm))
  -- the callees' `EntryOk` at the parent's key set, one branch per descendant
  let mut branches : List (Term → CommandElabM Term) := []
  for d in ds do
    let (hd, _) ← hypOf d
    let dds ← liftTermElabM (descendantsW d)
    let entry : Term ←
      if dds.isEmpty then do
        let di ← liftTermElabM (infoOf d)
        -- a leaf takes any key set; a memory-only parent has the empty one
        if di.hasCalls then
          `(Tools.ShippingCacheCoherentCert.EntryOk.mono ($(sub d "entry_ok") $L $hd)
              (fun _ hFalse => False.elim hFalse))
        else
          `($(sub d "entry_ok") $L _ $hd)
      else do
        let mut args : Array Term := #[]
        for dd in dds do
          let (hdd, _) ← hypOf dd
          args := args.push hdd
        let hk := mkIdent `hk
        let incl ← elimDisj hk (dds.map fun dd => fun (h : Term) => do
          match ds.findIdx? (· == dd) with
          | some j => inject h j n
          | none => throwError "{f}: {dd} is a descendant of {d} and not of {f}")
        `(Tools.ShippingCacheCoherentCert.EntryOk.mono ($(sub d "entry_ok") $L $hd $args*)
            (fun _ $hk => $incl))
    branches := branches ++ [fun (h : Term) => `(by subst $h; exact $entry)]
  let hc' := mkIdent `hc'
  let hRterm ← elimDisj hc' branches
  let hypList : List (Ident × Bool) := hyps.map fun p => (p.2.1, p.2.2)
  let some closing ← closingTacticW cands hypList
    | throwError "{f}: no closing theorem"
  let nLit := Syntax.mkNumLit (toString info.nDecl)
  let harness ← harnessTerm f
  let notSelf ← disj fq ds
  let body ← `(
    Tools.ShippingCacheCoherentCert.entryOk_machine $L
      (fun L' => Tools.ShippingChildInv.bodyRel L')
      (fun L' => Tools.ShippingChildInv.harnessRel_of L' (Tools.ShippingChildInv.translateRel L'))
      (Tools.ShippingCacheCoherentVia.coreVia_of $L
        (fun L' => Tools.ShippingChildInv.bodyRel L')
        (fun L' => Tools.ShippingChildInv.harnessRel_of L' (Tools.ShippingChildInv.translateRel L'))
        (fun _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx $h0)
        (fun _ _ => by $closing:tactic))
      $harness
      (fun b => Tools.ShippingCacheCoherentData.hout_of_data $md $(sub f "machine_ok")
        $(sub f "machine_body") (nDecl := $nLit)
        (by first | decide | decide +kernel) (by first | decide | decide +kernel)
        (by first | decide | decide +kernel) b)
      $hinsM
      $hinsG
      (fun _ $hc' => $hRterm)
      (by
        show ¬ ($notSelf)
        first | decide | exact not_false))
  let mut ty : Term ← `(Tools.ShippingCacheCoherentCert.EntryOk $L $fq (fun $k => $kset))
  let mut val : Term := body
  for (d, h, machine) in hyps.reverse do
    let refl ← reflection d machine
    ty ← `($refl → $ty)
    val ← `(fun $h => $val)
  runGenerated s!"{f}.entry_ok" (← `(command|
    theorem $(sub f "entry_ok") {$(mkIdent `mctx) : Lean.Meta.Context}
        {$(mkIdent `mref) : ST.Ref IO.RealWorld Lean.Meta.State}
        {$(mkIdent `cctx) : Lean.Core.Context}
        {$(mkIdent `cref) : ST.Ref IO.RealWorld Lean.Core.State}
        ($L : Tools.ShippingChildInv.RefLaws $(mkIdent `mref) $(mkIdent `cref)) : $ty :=
      $val))

/-- One row of a sweep. -/
structure Row where
  decl : Name
  /-- `gate leaf`, `machine leaf`, `parent`, `memory parent`, `-` -/
  kind : String
  /-- `GENERATED`, `EXISTS`, `REFUSED`, `FAILED` -/
  tag : String
  /-- `-` when made; else one of the reasons of the file header -/
  reason : String
  premises : Nat := 0
  note : String := ""
  ms : Nat := 0

/-- The reason class of a row of the BUILT generator, from its note. -/
def reasonOf (o : Outcome) : String :=
  if o.tag == "GENERATED" || o.tag == "EXISTS" then "-"
  else if has o.note "memory call entry" then "memory call entry"
  else if has o.note "callees without entry_ok" then "callee without entry_ok"
  else if has o.note "no closing theorem" then "no closing theorem"
  else if o.tag == "REFUSED" && has o.note "missing" then "missing data fact"
  else if o.tag == "REFUSED" then "no route"
  else "failed"

/-- The wide generator on one declaration. Never throws; on a failure the
environment and the message log are put back. -/
def entryOkWide (f : Name) : CommandElabM Row := do
  let name := f ++ `entry_ok
  let info : Info ←
    try
      liftTermElabM (infoOf f)
    catch _ => pure default
  let kind : String :=
    if !info.machine then (if info.gate then "gate leaf" else "-")
    else if !info.hasCalls then "machine leaf"
    else if info.hasMem then "memory parent"
    else "parent"
  if (← getEnv).contains name then
    return { decl := f, kind, tag := "EXISTS", reason := "-" }
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let restore : CommandElabM Unit := do
    setEnv savedEnv
    modify fun st => { st with messages := savedMsgs }
  let ofBuilt (o : Outcome) : CommandElabM Row := do
    unless o.tag == "GENERATED" || o.tag == "EXISTS" do restore
    pure { decl := f, kind, tag := o.tag, reason := reasonOf o, premises := o.premises,
           note := o.note }
  if !info.machine then
    if info.gate then
      ofBuilt (← Tools.ShippingEntryOkCommand.entryOk f)
    else
      return { decl := f, kind, tag := "REFUSED", reason := "no route",
               note := "the machine reader refuses it and there is no gateValue" }
  else if !info.hasCalls then
    -- (a) the closing of a leaf, generated when absent
    unless (← getEnv).contains (f ++ `machine_closes) do
      try
        discard <| liftTermElabM (Tools.ShippingMachineClosesGen.closesTheorem? f)
      catch _ => pure ()
    ofBuilt (← Tools.ShippingEntryOkCommand.entryOk f)
  else
    let failReason : String := if info.hasMem then "memory call entry" else "failed"
    try
      let miss ← missing f ["machineData", "machine_ok", "machine_body"]
      let env ← getEnv
      let noEntry := info.callees.filter fun c => !env.contains (c ++ `entry_ok)
      let cands ← liftTermElabM (closingsOf f)
      if !miss.isEmpty then
        return { decl := f, kind, tag := "REFUSED", reason := "missing data fact",
                 note := s!"missing {miss}" }
      else if !noEntry.isEmpty then
        return { decl := f, kind, tag := "REFUSED", reason := "callee without entry_ok",
                 note := s!"callees without entry_ok: {noEntry}" }
      else if cands.isEmpty then
        return { decl := f, kind, tag := "REFUSED", reason := "no closing theorem",
                 note := s!"no constant {f}.<…closes…> concludes MachineClosesAt or MachineCloses" }
      else
        genParentW f info cands
        let p ← checkEntryOk name
        return { decl := f, kind, tag := "GENERATED", reason := "-", premises := p,
                 note := s!"closing candidates {cands.map (·.1)}" }
    catch ex =>
      let msg ← ex.toMessageData.toString
      restore
      return { decl := f, kind, tag := "FAILED", reason := failReason, note := msg }

private def clip (s : String) (n : Nat) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ " …"

initialize rows : IO.Ref (Array Row) ← IO.mkRef #[]

/-- Wall-clock budget of one `#entry_ok_all`, in milliseconds. -/
def budgetMs : Nat := 1500000

/-- Run the generator on one declaration, log its row, record it. -/
def sweepOne (f : Name) : CommandElabM Unit := do
  IO.eprintln s!"ENTRYOKW START {f}"
  (← IO.getStderr).flush
  let t0 ← IO.monoMsNow
  let r ← entryOkWide f
  let ms := (← IO.monoMsNow) - t0
  if r.tag == "GENERATED" then
    logInfo m!"ENTRYOKW ROW {f}: GENERATED ({r.kind}); {r.premises} premises, all reflections; statement check and axiom audit passed; {ms} ms"
  else if r.tag == "EXISTS" then
    logInfo m!"ENTRYOKW ROW {f}: EXISTS ({r.kind})"
  else
    logInfo m!"ENTRYOKW ROW {f}: {r.tag} ({r.kind}) — reason: {r.reason} — {clip r.note 500}; {ms} ms"
  rows.modify fun a => a.push { r with ms := ms }

/-- `#entry_ok_wide f`: one declaration. Never an error. -/
elab "#entry_ok_wide " d:ident : command => do
  let f? : Option Name ← try
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
      pure (some n)
    catch _ => pure none
  match f? with
  | none => logInfo m!"ENTRYOKW ROW {d.getId}: UNRESOLVED — not a constant of the imports"
  | some f => sweepOne f

/-- `#entry_ok_all n`: see the file header. Never an error. -/
elab "#entry_ok_all " n:num : command => do
  let cap := n.getNat
  let env ← getEnv
  let found : Array Name := env.constants.fold (fun acc nm _ =>
    match nm with
    | .str p s =>
      if s == "machineData" then acc.push p
      else if s == "gateValue" && !env.contains (p ++ `machineData) then acc.push p
      else acc
    | _ => acc) #[]
  let done := (← rows.get).map (·.decl)
  -- dependency order: the height of the call tree, then the name
  let mut keyed : Array (Nat × Name) := #[]
  for f in found do
    let h ← try liftTermElabM (heightOf f) catch _ => pure 0
    keyed := keyed.push (h, f)
  let sorted := keyed.qsort fun a b =>
    a.1 < b.1 || (a.1 == b.1 && decide (a.2.toString < b.2.toString))
  let t0 ← IO.monoMsNow
  let mut ran : Nat := 0
  let mut left : Nat := 0
  for (_, f) in sorted do
    if done.contains f then continue
    let now ← IO.monoMsNow
    if ran ≥ cap || now - t0 > budgetMs then
      left := left + 1
    else
      sweepOne f
      ran := ran + 1
  logInfo m!"ENTRYOKW SCAN: {found.size} declarations with generated data in this environment; {done.size} had a row already; swept now {ran}; left out {left} (cap {cap}, budget {budgetMs} ms)"

/-- `#entry_ok_all_summary`: the rows by kind and by reason. -/
elab "#entry_ok_all_summary" : command => do
  let rs ← rows.get
  let made (r : Row) : Bool := r.tag == "GENERATED" || r.tag == "EXISTS"
  let mut lines : Array String := #[]
  for kind in ["gate leaf", "machine leaf", "parent", "memory parent", "-"] do
    let ks := rs.filter fun r => r.kind == kind
    unless ks.isEmpty do
      lines := lines.push s!"ENTRYOKW KIND {kind}: {ks.size} rows, made {(ks.filter made).size}, not made {(ks.filter fun r => !made r).size}"
  for reason in ["memory call entry", "callee without entry_ok", "missing data fact",
      "no closing theorem", "no route", "failed"] do
    let xs := rs.filter fun r => r.reason == reason
    unless xs.isEmpty do
      lines := lines.push s!"ENTRYOKW REASON {reason}: {xs.size} {xs.toList.map fun r => toString r.decl}"
  for r in rs do
    if r.tag == "FAILED" then
      lines := lines.push s!"ENTRYOKW FAILED {r.decl} ({r.kind}): {clip r.note 300}"
  logInfo m!"{String.intercalate "\n" lines.toList}"
  let total := (rs.foldl (fun acc r => acc + r.ms) 0)
  logInfo m!"ENTRYOKW SUMMARY of {rs.size} rows: made {(rs.filter made).size} (GENERATED {(rs.filter fun r => r.tag == "GENERATED").size}, EXISTS {(rs.filter fun r => r.tag == "EXISTS").size}); REFUSED {(rs.filter fun r => r.tag == "REFUSED").size}; FAILED {(rs.filter fun r => r.tag == "FAILED").size}; {total} ms. A made row: f.entry_ok is in the environment, kernel-checked — EntryOk of ONE declaration (a returning run of its entry from an invariant world of positive depth with a Prov cache and no entry for it), premises the reflections of the declaration and its non-memory descendants only. Not an endpoint; nothing about worlds without Prov. No class and no count was expected by this file."
  if rs.isEmpty then
    throwError "ENTRYOKW: nothing was swept in this file"

end Tools.ShippingEntryOkWide

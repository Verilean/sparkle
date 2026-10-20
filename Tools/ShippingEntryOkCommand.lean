import Lean.Elab.Command
import Tools.ShippingWalkStillMore
import Tools.ShippingCacheCoherentData
import Tools.ShippingSeqChildIface
import Tools.ShippingCallsGate
import Tools.ShippingGateChild
import Tools.ShippingReflectCtx
import Tools.ShippingMachineCommand
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # `#entry_ok f`: `EntryOk` of one declaration, as a generated theorem

WRITTEN, NOT BUILT (par/a-41). A generator: nothing here is a proof about the
compiler; each theorem it adds is elaborated and kernel-checked like a
hand-written one, from the built general theorems and the declaration's
generated data facts.

`EntryOk L c K` (`Tools/ShippingCacheCoherentCert.lean`): a returning run of
`c`'s full entry from an invariant world of positive depth whose cache
satisfies `Prov` and has no entry for `c` ends in a `Prov` world, its result
`Fresh` for `c`, the keys it added among `K`. It is the unit the provenance
chain of a parent consumes, one per callee.

## What is generated: `f.entry_ok`

| kind of `f` (read by the compiler's reader on the SOURCE; no reflected data is evaluated in compiled code) | statement | from |
|---|---|---|
| **gate leaf** — the machine reader refuses `f`, `f.gateValue` exists | `(L) (K) : EntryDefines … f f.gateValue → EntryOk L f K` | `entryOk_leaf`, `entryStill_gate_all`, `childFull_of_real` over `f.gate_old` / `gate_peel` / `gate_wf` |
| **machine leaf** — the reader reads `f`, no call entry | `(L) (K) : MachineDefines … f f.machineData.shape → EntryOk L f K` | `entryOk_leaf`, `entryStill_leaf`, `harnessStill_all`, `seqChild_of_real` over `f.machine_ok` / `machine_body` / `machine_closes` |
| **machine parent** — call entries, none a memory, every callee with `c.entry_ok` already | `(L) : (reflection of f) → (reflections of its descendants) → EntryOk L f (fun k => k = d₁ ∨ … ∨ k = dₙ)` | `entryOk_machine`, `coreVia_of` over the declaration's closing (`f.closes_deep` / `f.machine_closes_at` / `f.machine_closes`, whichever exists, its premises discharged by the reflections), `harnessStill_all`, `hout_of_data`, the callees' `entry_ok` |

The descendants `d₁ … dₙ`: the callees in the order of the call entries, each
followed by its own descendants, first occurrences kept. The premises come in
the same order, `f`'s first. (For `midH` and `mid2` this is the order of the
hand-written theorems.)

Helper theorems, kernel `decide`: `f.entry_wf` (the packed term is
well-formed) and, for a parent, `f.entry_callees` (every call entry is of a
descendant).

## Checked after generation

* the statement mentions none of `HarnessStill`, `EntryStill`, `CoreVia`,
  `MachineClosesAt`, `MachineCloses`;
* every proposition binder is a `MachineDefines` or an `EntryDefines`; the
  conclusion is an `EntryOk`;
* only the standard axioms.

A failure of any step leaves NO constant behind (the environment is put
back).

## Commands

* `#entry_ok f` — an error unless `f.entry_ok` is generated (or exists);
* `#entry_ok_sweep f` — the same generator, never an error: one `ENTRYOK`
  row; `#entry_ok_summary` prints the rows (an error only when nothing was
  swept);
* `#entry_ok_same a b` — `a`'s statement against `b`'s by `isDefEq` (`b` a
  theorem, or a `def … : Prop`, whose VALUE is then the statement); an error
  when they differ.

REFUSED (no attempt): a memory call entry; a callee without `entry_ok`; a
missing data fact (named in the row); no closing theorem for a parent. -/
namespace Tools.ShippingEntryOkCommand
open Lean Meta Elab Command

/-- The constants a generated statement must not mention. -/
def forbidden : List Name :=
  [``Tools.ShippingCacheCoherentCert.HarnessStill, ``Tools.ShippingCacheCoherentCert.EntryStill,
   ``Tools.ShippingCacheCoherentCert.CoreVia, ``Tools.ShippingChildInv.MachineClosesAt,
   ``Tools.ShippingMachineEntry.MachineCloses]

/-- How a declaration is compiled, as far as this generator distinguishes. -/
inductive Kind where
  | gateLeaf
  | machLeaf
  /-- call entries (distinct, in order) and the declaration's own binder count -/
  | parent (callees : List Name) (nDecl : Nat)
  | refused (why : String)

/-- The kind of `f`, by the compiler's reader on the source declaration. -/
def kindOf (f : Name) : MetaM Kind := do
  let env ← getEnv
  -- the shape as the compiler's reader reads it off the source declaration
  let shape? : Option Sparkle.Compiler.Elab.MachineShape ←
    try
      let r ← Tools.ShippingMachineCommand.readMachine f
      pure (some r.shape)
    catch _ => pure none
  match shape? with
  | some shape =>
    unless env.contains (f ++ `machineData) do
      return .refused s!"{f}: the machine route, but {f}.machineData is missing (#machine_endpoint)"
    let insts := shape.insts.map (·.1)
    -- origin dispatch (patched compiler): a memory entry is one of memory ORIGIN
    if shape.instTagged.any fun x => x.2.child?.isSome then
      return .refused s!"{f}: a memory call entry (not covered)"
    if insts.isEmpty then return .machLeaf
    let nDecl := shape.binders.length - shape.insts.length - shape.layout.slots.length -
      shape.layout.lets
    return .parent insts.eraseDups nDecl
  | none =>
    if env.contains (f ++ `gateValue) then return .gateLeaf
    return .refused s!"{f}: the machine reader refuses it and {f}.gateValue is missing"

/-- Whether `f` is on the machine route (for the form of its reflection). -/
def isMachine (f : Name) : MetaM Bool := do
  match ← kindOf f with
  | .machLeaf => pure true
  | .parent _ _ => pure true
  | _ => pure false

/-- The descendants of `f`: its callees in order, each followed by its own,
first occurrences kept. -/
partial def descendants (f : Name) (fuel : Nat := 16) : MetaM (List Name) := do
  if fuel == 0 then return []
  match ← kindOf f with
  | .parent callees _ =>
    let mut out : List Name := []
    for c in callees do
      out := out ++ [c] ++ (← descendants c (fuel - 1))
    return out.eraseDups
  | _ => return []

/-- A constant below `f`, as an identifier that resolves from any namespace. -/
def sub (f : Name) (s : String) : Ident := mkIdent (`_root_ ++ f ++ Name.mkSimple s)

/-- The reflection premise of `d`, in the theorem's contexts. -/
def reflection (d : Name) (machine : Bool) : CommandElabM Term := do
  let dq : Term := quote d
  let mctx := mkIdent `mctx
  let mref := mkIdent `mref
  let cctx := mkIdent `cctx
  let cref := mkIdent `cref
  if machine then
    `(Tools.ShippingMachineEntry.MachineDefines $mctx $mref $cctx $cref $dq
        ($(sub d "machineData")).shape)
  else
    `(Tools.ShippingInlineSoundness.EntryDefines $mctx $mref $cctx $cref $dq
        $(sub d "gateValue"))

/-- The reflection hypothesis `h`, at any contexts. -/
def transported (h : Ident) (machine : Bool) : CommandElabM Term :=
  if machine then `(Tools.ShippingReflectCtx.MachineDefines.ctx $h)
  else `(Tools.ShippingReflectCtx.EntryDefines.ctx $h)

/-- `x = ``d₁ ∨ … ∨ x = ``dₙ` (right-nested; `n ≥ 1`). -/
def disj (x : Term) : List Name → CommandElabM Term
  | [] => `(False)
  | [d] => do
    let dq : Term := quote d
    `($x = $dq)
  | d :: rest => do
    let dq : Term := quote d
    let r ← disj x rest
    `($x = $dq ∨ $r)

/-- The injection of the `i`-th disjunct of an `n`-fold right-nested
disjunction. -/
def inject (h : Term) : Nat → Nat → CommandElabM Term
  | 0, n => if n ≤ 1 then pure h else `(Or.inl $h)
  | i + 1, n => do
    let r ← inject h i (n - 1)
    `(Or.inr $r)

/-- Elimination of an `n`-fold right-nested disjunction `h`: one branch per
disjunct, each given the proof of its disjunct. -/
def elimDisj (h : Term) : List (Term → CommandElabM Term) → CommandElabM Term
  | [] => `(False.elim $h)
  | [k] => k h
  | k :: rest => do
    let a := mkIdent `hdisjL
    let b := mkIdent `hdisjR
    let l ← k a
    let r ← elimDisj b rest
    `(Or.elim $h (fun $a => $l) (fun $b => $r))

/-- A two-alternative `first`, folded over a list of tactics. -/
def firstOf : List (TSyntax `tactic) → CommandElabM (TSyntax `tactic)
  | [] => `(tactic| fail "no alternative")
  | [t] => pure t
  | t :: rest => do
    let r ← firstOf rest
    `(tactic| first | $t:tactic | $r:tactic)

/-- Elaborate one generated command; an error message means failure. -/
def runGenerated (what : String) (stx : Syntax) : CommandElabM Unit := do
  let before := (← get).messages.toList.length
  withScope (fun s => { s with opts := maxRecDepth.set (Lean.Elab.async.set s.opts false) 100000 })
    (elabCommand stx)
  let errs := (← get).messages.toList.drop before |>.filter (·.severity == .error)
  unless errs.isEmpty do
    let mut texts : List String := []
    for m in errs.take 3 do
      texts := texts ++ [← m.data.toString]
    throwError "{what}: the generated proof failed: {String.intercalate " | " texts}"

/-- The statement check and the axiom audit of a generated `entry_ok`. -/
def checkEntryOk (name : Name) : CommandElabM Nat := do
  let ci ← liftCoreM (getConstInfo name)
  for c in forbidden do
    if (ci.type.find? (·.isConstOf c)).isSome then
      throwError "{name}: its statement mentions {c}"
  let props ← liftTermElabM <| forallTelescope ci.type fun xs body => do
    let mut props : Nat := 0
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if ← isProp t then
        props := props + 1
        let hd := t.getAppFn
        unless hd.isConstOf ``Tools.ShippingMachineEntry.MachineDefines ||
            hd.isConstOf ``Tools.ShippingInlineSoundness.EntryDefines do
          throwError "{name}: a premise that is not a reflection: {t}"
    unless body.getAppFn.isConstOf ``Tools.ShippingCacheCoherentCert.EntryOk do
      throwError "{name}: the conclusion is not an EntryOk: {body}"
    pure props
  for ax in ← liftCoreM (Lean.collectAxioms name) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{name} uses a non-standard axiom: {ax}"
  return props

/-- The well-formedness of the packed term, decided once. -/
def ensureWf (f : Name) : CommandElabM Unit := do
  unless (← getEnv).contains (f ++ `entry_wf) do
    let md := sub f "machineData"
    runGenerated s!"{f}.entry_wf" (← `(command|
      theorem $(sub f "entry_wf") :
          (($md).packed).WF ($md).kb ($md).kv ($md).vw := by
        first | decide | decide +kernel))

/-- The harness of `f`'s transition leaves the child cache. -/
def harnessTerm (f : Name) : CommandElabM Term := do
  let L := mkIdent `L
  `(Tools.ShippingWalkStillMore.harnessStill_all $L $(sub f "entry_wf")
      (Tools.ShippingHarnessStill.bool_pos_of_map (by first | decide | decide +kernel))
      (Tools.ShippingHarnessStill.bits_pos_of_map (by first | decide | decide +kernel))
      $(sub f "machine_body"))

/-- The constants a kind needs; the missing ones. -/
def missing (f : Name) (needs : List String) : CommandElabM (List String) := do
  let env ← getEnv
  return needs.filter fun s => !env.contains (f ++ Name.mkSimple s)

def genGateLeaf (f : Name) : CommandElabM Unit := do
  let fq : Term := quote f
  let L := mkIdent `L
  let hR := mkIdent `hR0
  let refl ← reflection f false
  runGenerated s!"{f}.entry_ok" (← `(command|
    theorem $(sub f "entry_ok") {$(mkIdent `mctx) : Lean.Meta.Context}
        {$(mkIdent `mref) : ST.Ref IO.RealWorld Lean.Meta.State}
        {$(mkIdent `cctx) : Lean.Core.Context}
        {$(mkIdent `cref) : ST.Ref IO.RealWorld Lean.Core.State}
        ($L : Tools.ShippingChildInv.RefLaws $(mkIdent `mref) $(mkIdent `cref))
        (K : Lean.Name → Prop) ($hR : $refl) :
        Tools.ShippingCacheCoherentCert.EntryOk $L $fq K :=
      Tools.ShippingCacheCoherentCert.entryOk_leaf $L
        (Tools.ShippingWalkStillMore.entryStill_gate_all $L
          (fun L' => Tools.ShippingChildInv.bodyRel L')
          (fun _ _ => Tools.ShippingReflectCtx.EntryDefines.ctx $hR)
          $(sub f "gate_old") $(sub f "gate_peel") $(sub f "gate_wf")
          (Tools.ShippingGateChild.bool_positions (by decide))
          (Tools.ShippingGateChild.bits_positions (by decide)))
        (fun y hy =>
          let h := Tools.ShippingCallsGate.childFull_of_real $hR $(sub f "gate_old")
            $(sub f "gate_peel") $(sub f "gate_wf")
            (Tools.ShippingGateChild.bool_positions (by decide))
            (Tools.ShippingGateChild.bits_positions (by decide)) hy
          ⟨h.name, h.design⟩)))

def genMachLeaf (f : Name) : CommandElabM Unit := do
  ensureWf f
  let fq : Term := quote f
  let L := mkIdent `L
  let hR := mkIdent `hR0
  let refl ← reflection f true
  let harness ← harnessTerm f
  let md := sub f "machineData"
  runGenerated s!"{f}.entry_ok" (← `(command|
    theorem $(sub f "entry_ok") {$(mkIdent `mctx) : Lean.Meta.Context}
        {$(mkIdent `mref) : ST.Ref IO.RealWorld Lean.Meta.State}
        {$(mkIdent `cctx) : Lean.Core.Context}
        {$(mkIdent `cref) : ST.Ref IO.RealWorld Lean.Core.State}
        ($L : Tools.ShippingChildInv.RefLaws $(mkIdent `mref) $(mkIdent `cref))
        (K : Lean.Name → Prop) ($hR : $refl) :
        Tools.ShippingCacheCoherentCert.EntryOk $L $fq K :=
      Tools.ShippingCacheCoherentCert.entryOk_leaf $L
        (Tools.ShippingHarnessStill.entryStill_leaf $L
          (fun L' => Tools.ShippingChildInv.bodyRel L')
          (fun L' => Tools.ShippingChildInv.harnessRel_of L' (Tools.ShippingChildInv.translateRel L'))
          (fun _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx $hR)
          (fun mc cc => Tools.ShippingChildInv.machineClosesAt_of_closes
            ($(sub f "machine_closes") mc _ cc _))
          (by first | rfl | decide | decide +kernel)
          $harness)
        (fun y hy =>
          let h := Tools.ShippingSeqChildIface.seqChild_of_real $md $(sub f "machine_ok")
            $(sub f "machine_body") (by first | rfl | decide | decide +kernel)
            (by first | decide | decide +kernel) $hR
            (fun mc cc => $(sub f "machine_closes") mc _ cc _) hy
          ⟨h.name, h.design⟩)))

/-- The closing of a parent, at the contexts of the goal: whichever closing
theorem exists, its premises discharged by the reflections at hand. -/
def closingTactic (f : Name) (hyps : List (Ident × Bool)) :
    CommandElabM (Option (TSyntax `tactic)) := do
  let env ← getEnv
  let mut exacts : List (TSyntax `tactic) := []
  for (h, machine) in hyps do
    let t ← transported h machine
    exacts := exacts ++ [← `(tactic| exact $t)]
  let discharge ← firstOf exacts
  let mut alts : List (TSyntax `tactic) := []
  if env.contains (f ++ `closes_deep) then
    alts := alts ++ [← `(tactic| (apply $(sub f "closes_deep") <;> $discharge:tactic))]
  if env.contains (f ++ `machine_closes_at) then
    alts := alts ++ [← `(tactic| (apply $(sub f "machine_closes_at") <;> $discharge:tactic))]
  if env.contains (f ++ `machine_closes) then
    alts := alts ++ [← `(tactic|
      exact Tools.ShippingChildInv.machineClosesAt_of_closes ($(sub f "machine_closes") _ _ _ _))]
  if alts.isEmpty then return none
  return some (← firstOf alts)

def genParent (f : Name) (callees : List Name) (nDecl : Nat) : CommandElabM Unit := do
  ensureWf f
  let fq : Term := quote f
  let L := mkIdent `L
  let ds ← liftTermElabM (descendants f)
  let n := ds.length
  -- the reflections: `f` first, then the descendants in order
  let all := f :: ds
  let mut hyps : List (Name × Ident × Bool) := []
  let mut i : Nat := 0
  for d in all do
    let machine ← liftTermElabM (isMachine d)
    hyps := hyps ++ [(d, mkIdent (Name.mkSimple s!"hR{i}"), machine)]
    i := i + 1
  let hypOf (d : Name) : CommandElabM (Ident × Bool) := do
    match hyps.find? (·.1 == d) with
    | some (_, h, m) => pure (h, m)
    | none => throwError "{f}: no reflection hypothesis for {d}"
  let (h0, _) ← hypOf f
  -- the key set
  let k := mkIdent `k
  let kset ← disj k ds
  let x := mkIdent `x
  let xfst ← `(($x).1)
  let calleesProp ← disj xfst ds
  let md := sub f "machineData"
  unless (← getEnv).contains (f ++ `entry_callees) do
    runGenerated s!"{f}.entry_callees" (← `(command|
      theorem $(sub f "entry_callees") :
          ∀ $x, $x ∈ ($md).shape.insts → $calleesProp := by
        first | decide | decide +kernel))
  -- origin dispatch (patched compiler): the general closing maps the TAGGED
  -- entries (`shape.instTagged`), so `hinsG` is over them
  unless (← getEnv).contains (f ++ `entry_calleesT) do
    runGenerated s!"{f}.entry_calleesT" (← `(command|
      theorem $(sub f "entry_calleesT") :
          ∀ $x, $x ∈ ($md).shape.instTagged → $calleesProp := by
        first | decide | decide +kernel))
  -- the callees' `EntryOk` at the parent's key set, one branch per descendant
  let mut branches : List (Term → CommandElabM Term) := []
  for d in ds do
    let (hd, _) ← hypOf d
    let dds ← liftTermElabM (descendants d)
    let entry : Term ←
      if dds.isEmpty then
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
  -- the closing
  let hypList : List (Ident × Bool) := hyps.map fun p => (p.2.1, p.2.2)
  let some closing ← closingTactic f hypList
    | throwError "{f}: no closing theorem ({f}.closes_deep / machine_closes_at / machine_closes)"
  let nLit := Syntax.mkNumLit (toString nDecl)
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
      (fun _ x hx => $(sub f "entry_callees") x hx)
      (fun x hx _ => $(sub f "entry_calleesT") x hx)
      (fun _ $hc' => $hRterm)
      (by
        show ¬ ($notSelf)
        decide))
  -- the statement: the reflections as premises, in order
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

/-- What one run of the generator did. -/
structure Outcome where
  /-- `GENERATED`, `EXISTS`, `REFUSED` or `FAILED` -/
  tag : String
  kind : String
  premises : Nat := 0
  note : String := ""

/-- The generator on one declaration. Never throws; on any failure the
environment and the message log are put back. -/
def entryOk (f : Name) : CommandElabM Outcome := do
  let name := f ++ `entry_ok
  if (← getEnv).contains name then
    return { tag := "EXISTS", kind := "-", note := s!"{name} is in the environment already" }
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let kind : Kind ←
    try
      liftTermElabM (kindOf f)
    catch ex => do
      let msg ← ex.toMessageData.toString
      pure (Kind.refused s!"{f}: the reader threw: {msg}")
  let kindS : String := match kind with
    | .gateLeaf => "gate leaf"
    | .machLeaf => "machine leaf"
    | .parent cs _ => s!"machine parent of {cs}"
    | .refused _ => "-"
  let refuse (why : String) : CommandElabM Outcome :=
    pure { tag := "REFUSED", kind := kindS, note := why }
  let generated : CommandElabM Outcome := do
    let p ← checkEntryOk name
    pure { tag := "GENERATED", kind := kindS, premises := p }
  try
    match kind with
    | .refused why => refuse why
    | .gateLeaf => do
      let miss ← missing f ["gateValue", "gate_old", "gate_peel", "gate_wf"]
      if !miss.isEmpty then
        refuse s!"{f}: missing {miss} (#gate_child)"
      else do
        genGateLeaf f
        generated
    | .machLeaf => do
      let miss ← missing f ["machineData", "machine_ok", "machine_body", "machine_closes"]
      if !miss.isEmpty then
        refuse s!"{f}: missing {miss}"
      else do
        genMachLeaf f
        generated
    | .parent callees nDecl => do
      let miss ← missing f ["machineData", "machine_ok", "machine_body"]
      let env ← getEnv
      let noEntry := callees.filter fun c => !env.contains (c ++ `entry_ok)
      if !miss.isEmpty then
        refuse s!"{f}: missing {miss}"
      else if !noEntry.isEmpty then
        refuse s!"{f}: callees without entry_ok: {noEntry} (run #entry_ok on them first)"
      else do
        genParent f callees nDecl
        generated
  catch ex =>
    let msg ← ex.toMessageData.toString
    setEnv savedEnv
    modify fun st => { st with messages := savedMsgs }
    pure { tag := "FAILED", kind := kindS, note := msg }

private def clip (s : String) (n : Nat) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ " …"

/-- `#entry_ok f`: `f.entry_ok`, or an error. -/
elab "#entry_ok " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  IO.eprintln s!"ENTRYOK START {f}"
  (← IO.getStderr).flush
  let o ← entryOk f
  match o.tag with
  | "GENERATED" =>
    logInfo m!"ENTRYOK GENERATED {f} ({o.kind}): {f}.entry_ok, {o.premises} premises, all reflections; no HarnessStill / EntryStill / CoreVia / MachineClosesAt; standard axioms"
  | "EXISTS" => logInfo m!"ENTRYOK EXISTS {f}: {o.note}"
  | _ => throwError "ENTRYOK {o.tag} {f} ({o.kind}): {o.note}"

/-- The rows of the file being elaborated. -/
initialize rows : IO.Ref (Array (String × Outcome × Nat)) ← IO.mkRef #[]

/-- `#entry_ok_sweep f`: the same generator, never an error. -/
elab "#entry_ok_sweep " d:ident : command => do
  let shown : String := toString d.getId
  IO.eprintln s!"ENTRYOK START {shown}"
  (← IO.getStderr).flush
  let t0 ← IO.monoMsNow
  let f? : Option Name ← try
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
      pure (some n)
    catch _ => pure none
  match f? with
  | none =>
    logInfo m!"ENTRYOK ROW {shown}: UNRESOLVED — the identifier is not a constant of the imports"
    rows.modify fun a => a.push
      (shown, { tag := "UNRESOLVED", kind := "-", note := "the identifier does not resolve" }, 0)
  | some f =>
    let o ← entryOk f
    let ms := (← IO.monoMsNow) - t0
    if o.tag == "GENERATED" then
      logInfo m!"ENTRYOK ROW {f}: GENERATED ({o.kind}); {o.premises} premises, all reflections; statement check and axiom audit passed; {ms} ms"
    else
      logInfo m!"ENTRYOK ROW {f}: {o.tag} ({o.kind}) — {clip o.note 700}; {ms} ms"
    rows.modify fun a => a.push (toString f, o, ms)

/-- `#entry_ok_summary`: the rows of this file. An error only when nothing
was swept. -/
elab "#entry_ok_summary" : command => do
  let rs ← rows.get
  let count (t : String) : Nat := (rs.filter fun r => r.2.1.tag == t).size
  let namesOf (t : String) : List String := (rs.filter fun r => r.2.1.tag == t).toList.map (·.1)
  logInfo m!"ENTRYOK SUMMARY of {rs.size}: GENERATED {count "GENERATED"} {namesOf "GENERATED"}; EXISTS {count "EXISTS"} {namesOf "EXISTS"}; REFUSED {count "REFUSED"} {namesOf "REFUSED"}; FAILED {count "FAILED"} {namesOf "FAILED"}; UNRESOLVED {count "UNRESOLVED"} {namesOf "UNRESOLVED"}. A GENERATED row: f.entry_ok was added and kernel-checked — EntryOk of ONE declaration (a returning run of its entry from an invariant world of positive depth with a Prov cache and no entry for it), premises the reflections of the declaration and its descendants only. It is not an endpoint, and says nothing about worlds without Prov. No class and no count was expected by this file."
  if rs.isEmpty then
    throwError "ENTRYOK: nothing was swept in this file"

/-- `#entry_ok_same a b`: the statement of `a` against the statement of `b`
(`b` a theorem; or a `def … : Prop`, whose value is then the statement). -/
elab "#entry_ok_same " a:ident b:ident : command => do
  let an ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo a
  let bn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
  IO.eprintln s!"ENTRYOK SAME START {an} / {bn}"
  (← IO.getStderr).flush
  let same ← liftTermElabM do
    let ai ← getConstInfo an
    let bi ← getConstInfo bn
    let expected : Lean.Expr :=
      if bi.type.isProp then
        match bi.value? with
        | some v => v
        | none => bi.type
      else bi.type
    isDefEq ai.type expected
  logInfo m!"ENTRYOK SAME {an} / {bn}: {if same then "T" else "F"}"
  unless same do
    throwError "ENTRYOK SAME: the statement of {an} is not the statement of {bn}"

end Tools.ShippingEntryOkCommand

import IP.Crypto.Keccak256Sponge
import Tools.ShippingMachineCommand
import Tools.ShippingMachineLinkedCommand
import Tools.ShippingGateChildCommand
import Tools.ShippingMachineComposeRCommand
import Tools.ShippingMachineClosesAtGen
import Tools.ShippingMachineDepthCommandR
import Tests.Compiler.KeccakSpongeLogLib

/-! # The sponge's `generateCoreNR`, in budgeted pieces: a LOG-ONLY probe (round par/a-26)

WRITTEN, NOT BUILT, NOT RUN. CLAIMS NOTHING. It replaces
`Tests/Compiler/KeccakSpongeStepProbe.lean` (round par/a-25), whose steps 12
and 13 never ran: that file's `elab "#sponge_calls"` did not compile — its
body used a local named `needs` (line 630, renamed by the integrator, and
again on line 632, `runStep … needs do`, still there) after the file had
declared the token `" needs "` — so both uses of the command were errors
("elaboration function … has not been implemented") that only the build's
message log would have shown, and the build was killed. Nothing was wrong
with the logging path.

What this file changes:

* its commands are `#sp2_*`, their keyword is `given`; NO local, parameter
  or field of this file is named `given`, `budget`, `wall` or `at`;
* step `0d` runs the pieces command on a declaration it must refuse: the
  line `SP2 STEP 0d …: FAILED` in the progress FILE shows, 2 s into the
  file, that the command exists and writes;
* every piece writes `START` to the file before it runs and `OK (ms)` /
  `FAILED (ms) — message` / `SKIPPED — soft wall budget` after it; a piece
  that fails or runs out of its budget does NOT stop the other pieces;
* each piece runs under its own HEARTBEAT budget (`maxHeartbeats` of
  `Core.Context` with the heartbeat counter restarted; caught by
  `tryCatchRuntimeEx`), and before each piece the step's soft WALL budget is
  checked. Granularity that is achievable: one `Tactic.run` call — the
  entry's tactic is cut into 10 such calls and one per leaf; INSIDE one call
  only the heartbeat budget acts (the elaborator checks it in `whnf`, `simp`,
  `isDefEq`; it counts allocations, not seconds, and the kernel's own budget
  is set separately for the kernel-checked pieces). A wall-clock limit inside
  one tactic call is not available;
* the pieces now cover the WHOLE interval between the generator's two
  progress lines (`f: composedNR 1` at `ShippingMachineDepthCommandR` 185 and
  `…machine_composedNR1: checking` at 560): set-up, `closesAtNames`, the 8
  parent decides (kernel, alone), `hrunN` of an entry (cheap by reading, so
  FIRST), then the entry's tactic in pieces, then `Meta.check`;
* the full `generateCoreNR` and what follows it (steps 15–17) run ONLY when
  `SPARKLE_SPONGE_FULL` is set: the default run is the diagnostic alone and
  is bounded by the budgets.

## For the integrator

TARGET-ONLY, NEVER IMPORTED, NOT for `Tests/AllTests.lean`; never together
with `KeccakProbeTest`, `OneOutWKeccakFTest`, `KeccakSpongeStepProbe` (the
same constants).

    SPARKLE_MACHINE_PROGRESS=$HOME/sparkle-work/keccak-sponge-step2.log \
      ~/sparkle-work/bin/cgrun.sh -n sponge-step3 -m 3G -s 0 -t 2400 -- \
      lake build Tests.Compiler.KeccakSpongeStepProbe2

(a fresh file each run). Expected [P]: steps 0–11 ≈ 3.5 min (measured in the
previous run: 2–7 ≈ 2 min, 8–11 = 24 + 13 + 3 + 13 s); step 12 ≤ its soft
limit of 420 s plus one piece; step 13 the same. With `SPARKLE_SPONGE_FULL=1`
also exported, step 15 is the step that did not end in 38 min before.

## The steps

| step | what |
|---|---|
| 0a, 0b, 0c, 0d | self-tests (FAILED, OK, the variable, FAILED expected) |
| 1 | reader data |
| 2–7 | base (as before) |
| 8–11 | `closingCandidates`; `generateComposedR (atW)`, `generateCombNR`, `generateRunOfR` on `wKeccakF` (as before: 24.3, 12.6, 2.6, 12.7 s measured) |
| 12 | entry k = 0: the pieces, 20 000 k heartbeats each, soft limit 420 s |
| 13 | entries k = 1, 26: the same |
| 15–17 | only with `SPARKLE_SPONGE_FULL`: `generateCoreNR`, `generateShipsNR`, `generateDesignNR` |

The pieces of step 12 / 13, in this order (cheap by reading first):

    setup.read, setup.children, setup.names (closesAtNames), setup.head
    parent decide 0 … 7           kernel, alone, the kernel's heartbeat budget
    call k: hrunN.closing         closesAtProof (a child whose closing is derived)
    call k: hrunN.tactic          machineRunNC_of_real …
    call k: refine                the skeleton
    call k: r, l, b
    call k: f.refine, f.fin, f.hb, f.hv.simp, f.hv.split, f.hv.leaf j (each),
    call k: instantiate, Meta.check   only when every piece before closed its goal

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The pieces (MetaM; the opens of `Tools/ShippingMachineDepthCommandR.lean`) -/

namespace Tests.Compiler.KeccakSpongeStepProbe2
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine progress listE)
open Tools.ShippingMachineSeqCommand
open Tools.ShippingMachineShipsHierCommand (conj projs)
open Tools.ShippingMachineDepthCommand

/-- The file the lines go to without the progress variable. -/
def fallback : String := ".lake/keccak-sponge-step2.log"

/-- A line of a piece: to the progress file, at once. -/
def fileLine (msg : String) : IO Unit :=
  Tests.Compiler.KeccakSpongeLogLib.toFile fallback s!"SP2   {msg}"

/-- The budgets of a step and where its pieces' lines are collected. -/
structure Cfg where
  acc : IO.Ref (Array String)
  /-- heartbeats per piece, in thousands (the unit of the option); 0: no limit -/
  hbK : Nat
  /-- when the step started (ms) -/
  start : Nat
  /-- the step's soft limit in ms, checked BEFORE each piece; 0: none -/
  softMs : Nat

/-- Is the step's soft limit used up? -/
def Cfg.spent (cfg : Cfg) : IO Bool := do
  let now ← IO.monoMsNow
  return cfg.softMs != 0 && now - cfg.start > cfg.softMs

/-- A timed, budgeted piece (MetaM): `none` when it failed, ran out of its
heartbeats, or was skipped. Never throws. -/
def pieceM {α : Type} (cfg : Cfg) (label : String) (x : MetaM α) : MetaM (Option α) := do
  if ← cfg.spent then
    fileLine s!"SKIPPED {label} — the step's soft limit ({cfg.softMs} ms) is used up"
    cfg.acc.modify fun l => l.push s!"{label}: SKIPPED (soft limit)"
    return none
  fileLine s!"START {label}"
  let t0 ← IO.monoMsNow
  let r : Except String α ← tryCatchRuntimeEx
    (do
      let a ← withTheReader Core.Context (fun c => { c with maxHeartbeats := cfg.hbK * 1000000 })
        (withCurrHeartbeats x)
      pure (Except.ok a))
    (fun ex => do
      let msg ← ex.toMessageData.toString
      pure (Except.error msg))
  let t1 ← IO.monoMsNow
  match r with
  | Except.ok a =>
    fileLine s!"OK {label} ({t1 - t0} ms)"
    cfg.acc.modify fun l => l.push s!"{label}: {t1 - t0} ms"
    return some a
  | Except.error msg =>
    fileLine s!"FAILED {label} ({t1 - t0} ms) — {Tests.Compiler.KeccakSpongeLogLib.clipStr msg 800}"
    cfg.acc.modify fun l => l.push s!"{label}: FAILED after {t1 - t0} ms"
    return none

/-- A timed, budgeted piece (TermElabM). Never throws. -/
def pieceT {α : Type} (cfg : Cfg) (label : String) (x : Term.TermElabM α) :
    Term.TermElabM (Option α) := do
  if ← cfg.spent then
    fileLine s!"SKIPPED {label} — the step's soft limit ({cfg.softMs} ms) is used up"
    cfg.acc.modify fun l => l.push s!"{label}: SKIPPED (soft limit)"
    return none
  fileLine s!"START {label}"
  let t0 ← IO.monoMsNow
  let r : Except String α ← tryCatchRuntimeEx
    (do
      let a ← withTheReader Core.Context (fun c => { c with maxHeartbeats := cfg.hbK * 1000000 })
        (withCurrHeartbeats x)
      pure (Except.ok a))
    (fun ex => do
      let msg ← ex.toMessageData.toString
      pure (Except.error msg))
  let t1 ← IO.monoMsNow
  match r with
  | Except.ok a =>
    fileLine s!"OK {label} ({t1 - t0} ms)"
    cfg.acc.modify fun l => l.push s!"{label}: {t1 - t0} ms"
    return some a
  | Except.error msg =>
    fileLine s!"FAILED {label} ({t1 - t0} ms) — {Tests.Compiler.KeccakSpongeLogLib.clipStr msg 800}"
    cfg.acc.modify fun l => l.push s!"{label}: FAILED after {t1 - t0} ms"
    return none

/-- The size of a term as a TREE, counted up to `cap` (sharing is not seen). -/
partial def sizeCap (cap : Nat) (e : Lean.Expr) (acc : Nat) : Nat :=
  if acc ≥ cap then acc
  else match e with
    | Lean.Expr.app f a => sizeCap cap a (sizeCap cap f (acc + 1))
    | Lean.Expr.lam _ t b _ => sizeCap cap b (sizeCap cap t (acc + 1))
    | Lean.Expr.forallE _ t b _ => sizeCap cap b (sizeCap cap t (acc + 1))
    | Lean.Expr.letE _ t v b _ => sizeCap cap b (sizeCap cap v (sizeCap cap t (acc + 1)))
    | Lean.Expr.mdata _ b => sizeCap cap b (acc + 1)
    | Lean.Expr.proj _ _ b => sizeCap cap b (acc + 1)
    | _ => acc + 1

/-- Tree size, capped at 5 000 000 nodes. -/
def sz (e : Lean.Expr) : Nat := sizeCap 5000000 e 0

/-- The last component of a goal's tag. -/
def tagEnd (n : Name) : String :=
  match n.eraseMacroScopes with
  | Name.str _ s => s
  | _ => ""

/-- The goal whose tag ends in `s`, if there is one. -/
def goalTagged? (gs : List MVarId) (s : String) : MetaM (Option MVarId) := do
  for g in gs do
    let t ← g.getTag
    if tagEnd t == s then return some g
  return none

/-- The tags of goals, for the log. -/
def tagsOf (gs : List MVarId) : MetaM (List Name) := do
  let mut tags : List Name := []
  for g in gs do
    let t ← g.getTag
    tags := tags ++ [t]
  return tags

/-- A closed proof checked by the KERNEL alone (as a theorem that is removed
again), under the kernel's heartbeat budget. Logged, never thrown. -/
def kernelProbe (cfg : Cfg) (label : String) (thmName : Name) (ty prf : Lean.Expr) :
    MetaM Unit := do
  if ty.hasFVar || prf.hasFVar || ty.hasExprMVar || prf.hasExprMVar then
    fileLine s!"{label}: not closed — not kernel-checked alone"
    return
  let saved ← getEnv
  let r ← pieceM cfg label
    (withOptions (fun o => maxHeartbeats.set o (cfg.hbK * 1000))
      (addDecl (.thmDecl { name := thmName, levelParams := [], type := ty, value := prf })))
  setEnv saved
  if r.isNone then
    fileLine s!"{label}: the kernel did not accept it within the budget (see the line above)"

/-- One budgeted tactic on the goal tagged `tag`: the goals it leaves. -/
def runOnTag (cfg : Cfg) (label : String) (gs : List MVarId) (tag : String) (tac : Syntax) :
    Term.TermElabM (Option (List MVarId)) := do
  let g? ← goalTagged? gs tag
  match g? with
  | Option.none =>
    fileLine s!"SKIPPED {label} — no goal tagged {tag}"
    return none
  | Option.some g => pieceT cfg label (Tactic.run g (Tactic.evalTactic tac))

/-- One budgeted tactic that must close the goal tagged `tag`. -/
def closeOnTag (cfg : Cfg) (label : String) (gs : List MVarId) (tag : String) (tac : Syntax) :
    Term.TermElabM Bool := do
  let r ← runOnTag cfg label gs tag tac
  match r with
  | Option.none => return false
  | Option.some remaining =>
    if remaining.isEmpty then return true
    fileLine s!"FAILED {label} — {remaining.length} goals remain"
    return false

/-- **Everything `generateCoreNR declName dep` does between its two progress
lines, for the call entries `ks` only, in budgeted pieces.** A copy of
`Tools.ShippingMachineDepthCommand.generateCoreNR` 186–353 (set-up, the
children's premises, the head and its decides), 354–417 and 439–470 (one
entry of `hcalls`, the tactic cut into pieces), 499–537 (one entry of
`hrunN`). The chains (477–494, 538–552) and the final term (554–559) are not
copied: they are 27 applications each. Adds no constant. Throws only where
the set-up itself fails (the wrapper logs it). -/
def callPieces (declName : Name) (dep : Nat) (ks : List Nat) (cfg : Cfg) : MetaM Unit := do
  let r? ← pieceM cfg "setup.read (readMachine, endpointParts)" (do
    let r ← readMachine declName
    let parts ← endpointParts declName
    pure (r, parts))
  let some (r, (headL, args, back?)) := r? | throwError "{declName}: the set-up did not end"
  if r.shape.insts.isEmpty then throwError "{declName}: no call"
  if r.shape.instFields.isEmpty then
    throwError "{declName}: one-output combinational calls (the derived boundary asks the general closing)"
  if back?.isSome then throwError "{declName}: a transported endpoint (not yet at depth)"
  -- the head carrying `ServedReal` (under `ChildBnd`)
  let headRA : Name := headL.appendAfter "RA"
  let pL := mkAppN (mkConst headRA) args
  let calls := r.shape.insts
  let seqKids := ((calls.map (·.1)).eraseDups.filter fun c =>
    (Tools.ShippingMachineMemCommand.memWidths? c).isNone)
  let kids? ← pieceM cfg "setup.children (the children's run theorems: found, or generated)" (do
    let mut seqRuns : Std.HashMap Name Name := {}
    let mut leaf : Std.HashMap Name Bool := {}
    let mut bndOf : Std.HashMap Name Lean.Expr := {}
    for c in seqKids do
      let cr ← readMachine c
      let isLeaf := cr.shape.insts.isEmpty
      leaf := leaf.insert c isLeaf
      if isLeaf then
        seqRuns := seqRuns.insert c (← generateSeqChildN c)
      else
        if dep == 0 then throwError "{declName}: the child {c} has children; depth 0 is too shallow"
        let (rn, bnd) ← generateRunOfR c (dep - 1)
        seqRuns := seqRuns.insert c rn
        bndOf := bndOf.insert c bnd
    pure (seqRuns, leaf, bndOf))
  let some (seqRuns, leaf, bndOf) := kids? | throwError "{declName}: the children's theorems"
  fileLine s!"pieces of {declName}: head {headRA}; {calls.length} call entries; sequential children {seqKids}"
  forallTelescope (← inferType pL) fun xs traceT => do
  let h := mkAppN pL xs
  let tyArgs := (← whnfR traceT).getAppArgs
  unless tyArgs.size == 11 do throwError "{declName}: the trace's arguments"
  let (dE, _mE, dsnE) := (tyArgs[2]!, tyArgs[3]!, tyArgs[4]!)
  -- the run's contexts (the endpoint's binders) and its `ChildBnd` premise
  let ctxOf (n : Name) : MetaM Lean.Expr := do
    for x in xs do
      if (← whnfR (← inferType x)).isAppOf n then return x
    throwError "{declName}: no binder of type {n}"
  let refOf (st : Name) : MetaM Lean.Expr := do
    for x in xs do
      let t ← whnfR (← inferType x)
      if t.isAppOf ``ST.Ref && (t.getAppArgs.back?.map (·.isConstOf st)).getD false then return x
    throwError "{declName}: no reference to {st}"
  let ctx := #[← ctxOf ``Lean.Meta.Context, ← refOf ``Lean.Meta.State, ← ctxOf ``Lean.Core.Context,
    ← refOf ``Lean.Core.State]
  -- the families over the sequential children
  let bsTy ← inferType (← mkAppM ``Tools.ShippingMachineAuto.MachineData.bsIn #[dE])
  let outsTy ← inferType (← mkAppM ``Sparkle.IR.Machine.Layout.outs
    #[← mkAppM ``Sparkle.Compiler.Elab.MachineShape.layout #[← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[dE]]])
  let nat := mkConst ``Nat
  let valsTy ← mkArrow nat (mkApp (mkConst ``List [.zero]) nat)
  let obsTy := mkApp (mkConst ``List [.zero]) (← mkArrow nat nat)
  let mut bsCases : List (Name × Lean.Expr) := []
  let mut outsCases : List (Name × Lean.Expr) := []
  -- the parent's family index type and domain map
  let ιP := tyArgs[5]!
  let domP := tyArgs[6]!
  -- a child's source at the child index matching parent index `iv`, and its domain
  let srcAt (c : Name) (iv : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Lean.Expr) := do
    let csrc := mkConst (c ++ `machineSource)
    let ιc := (← inferType csrc).bindingDomain!
    let idx ← if ιc.isConstOf ``Unit then pure (mkConst ``Unit.unit)
      else whnf (mkApp domP iv)
    let src0 := mkApp csrc idx
    let Dc := ((← whnf (← inferType src0)).bindingDomain!).bindingBody!.getAppArgs[0]!
    pure (src0, Dc, idx)
  for c in seqKids do
    let cd := mkConst (c ++ `machineData)
    let bsIn0 ← mkAppM ``Tools.ShippingMachineAuto.MachineData.bsIn #[cd]
    let bsIn ← if leaf.getD c true then pure bsIn0
      else mkAppM ``List.take #[mkNatLit (← readMachine c).nDecl, bsIn0]
    bsCases := bsCases ++ [(c, bsIn)]
    outsCases := outsCases ++ [(c, ← mkAppM ``Sparkle.IR.Machine.Layout.outs
      #[← mkAppM ``Sparkle.Compiler.Elab.MachineShape.layout #[← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[cd]]])]
  let bsC ← nameCases bsTy bsCases (mkApp (mkConst ``List.nil [.zero]) bsTy.appArg!)
  let outsC ← nameCases outsTy outsCases (mkApp (mkConst ``List.nil [.zero]) outsTy.appArg!)
  let natNat ← mkArrow nat nat
  let sDflt ← withLocalDeclD `vals valsTy fun vals =>
    mkLambdaFVars #[vals] (mkApp (mkConst ``List.nil [.zero]) natNat)
  let S ← withLocalDeclD `i ιP fun iv => do
    let mut sCases : List (Name × Lean.Expr) := []
    for (c, bsIn) in bsCases do
      let (src0, Dc, _) ← srcAt c iv
      let sF ← withLocalDeclD `vals valsTy fun vals => do
        mkLambdaFVars #[vals] (mkApp2 src0
          (← mkAppOptM ``Tools.ShippingMachineChild.boolsOf #[Dc, bsIn, vals])
          (← mkAppOptM ``Tools.ShippingMachineChild.bitsOf #[Dc, bsIn, vals]))
      sCases := sCases ++ [(c, sF)]
    mkLambdaFVars #[iv] (← nameCases (← mkArrow valsTy obsTy) sCases sDflt)
  -- per sequential child: its predicate `PC c` and its premise (283–336)
  let modT := mkConst ``Sparkle.IR.AST.Module
  let desT := mkConst ``Sparkle.IR.AST.Design
  let mut pcCases : List (Name × Lean.Expr) := []
  let mut pTypes : List Lean.Expr := []
  let mut freeOf : Std.HashMap Name Bool := {}
  -- children with calls whose closing is derived: the name premises it asks
  let mut namesOf : Std.HashMap Name (List Lean.Expr) := {}
  for c in seqKids do
    unless leaf.getD c true do
      let nm? ← pieceM cfg s!"setup.names (closesAtNames {c})" (closesAtNames c ctx)
      match nm? with
      | Option.some (Option.some names) => namesOf := namesOf.insert c names
      | _ => fileLine s!"setup.names: the closing of {c} would stay a premise (no derived closing read)"
  for c in seqKids do
    let cshape ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[mkConst (c ++ `machineData)]
    let pcF ← withLocalDeclD `mc modT fun mc => do
      if leaf.getD c true then
        mkLambdaFVars #[mc] (← mkAppM ``Tools.ShippingGateChild.MachineRun #[toExpr c, cshape, mc])
      else
        let some bnd := bndOf.get? c | throwError "{declName}: boundary of {c}"
        mkLambdaFVars #[mc] (← mkAppM ``Tools.ShippingMachineDepthRun.MachineRunNC
          #[toExpr c, cshape, bnd, mc, dsnE])
    pcCases := pcCases ++ [(c, pcF)]
    let defs0 := mkAppN (mkConst ``Tools.ShippingMachineEntry.MachineDefines) (ctx ++ #[toExpr c, cshape])
    let pT ← withLocalDeclD `mctx' (mkConst ``Lean.Meta.Context) fun mc' =>
      withLocalDeclD `cctx' (mkConst ``Lean.Core.Context) fun cc' => do
      let ctx' := #[mc', ctx[1]!, cc', ctx[3]!]
      let closes := mkAppN (mkConst ``Tools.ShippingMachineEntry.MachineCloses) (ctx' ++ #[toExpr c, cshape])
      let closesAt := mkAppN (mkConst ``Tools.ShippingChildInv.MachineClosesAt) (ctx' ++ #[toExpr c, cshape])
      let body ← if leaf.getD c true then pure closes
        else do
          let some bnd := bndOf.get? c | throwError "{declName}: boundary of {c}"
          let bndHere ← withLocalDeclD `wc (mkConst ``Void [] |>.app (mkConst ``IO.RealWorld)) fun wc =>
            withLocalDeclD `raw modT fun raw => withLocalDeclD `D desT fun dD => do
            let cb := mkAppN (mkConst ``Tools.ShippingChildInv.ChildBnd) #[ctx[1]!, ctx[3]!, wc]
            mkForallFVars #[wc, raw, dD] (← mkArrow cb (bnd.beta (ctx' ++ #[wc, raw, dD])).headBeta)
          if (namesOf.get? c).isSome then pure bndHere else mkAppM ``And #[closesAt, bndHere]
      let ran := mkAppN (mkConst ``Tools.ShippingChildInv.ChildRanIn) #[ctx[1]!, ctx[3]!, toExpr c, mc', cc']
      mkForallFVars #[mc', cc'] (← mkArrow ran body)
    let free ← if leaf.getD c true then (do pure (← Tools.ShippingMachineClosesGen.closesTheorem? c).isSome) else pure false
    freeOf := freeOf.insert c free
    pTypes := pTypes ++ [← if free then pure defs0
      else match namesOf.get? c with
        | some names => do mkAppM ``And #[defs0, ← mkAppM ``And #[← conj names, pT]]
        | none => mkAppM ``And #[defs0, pT]]
  let some (_, pc0) := pcCases.head? | throwError "{declName}: no sequential child"
  let PC ← nameCases (← mkArrow modT (mkSort .zero)) pcCases pc0
  let pDecls := (seqKids.zip pTypes).toArray.mapIdx fun j (_, ty) =>
    (Name.mkSimple s!"hP{j}", fun (_ : Array Lean.Expr) => pure ty)
  withLocalDeclsD pDecls fun hPs => do
  let hPOf : Std.HashMap Name Lean.Expr := Id.run do
    let mut m : Std.HashMap Name Lean.Expr := {}
    for (c, hb) in seqKids.zip hPs.toList do m := m.insert c hb
    m
  -- the head and its 1 + 7 decided conditions on the PARENT's data: built as
  -- the generator builds them (unchecked), each also kernel-checked alone
  let mut p ← mkAppM ``Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN #[mkNatLit dep, h]
  let ty0 := (← whnf (← inferType p)).bindingDomain!
  let d0 ← mkDecideProof ty0
  kernelProbe cfg "parent decide 0 (hfe), kernel alone" (declName ++ `sp2_decide0) ty0 d0
  p := mkApp p d0
  p := mkApp p (mkNatLit r.nDecl)
  for j in [0:7] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    let dj ← mkDecideProof ty
    kernelProbe cfg s!"parent decide {j + 1} (hkD, hI, hIlen, hSL, hSlen, hLlen, hNIn in this order), kernel alone"
      (declName ++ Name.mkSimple s!"sp2_decide{j + 1}") ty dj
    p := mkApp p dj
  p := mkApp4 p bsC outsC S PC
  let afterT ← whnf (← inferType p)
  let hcallsT := afterT.bindingDomain!
  -- `hrunN`'s statement: the premise after `hcalls` (an arrow: it does not read the proof)
  let afterB := afterT.bindingBody!
  if afterB.hasLooseBVars then throwError "{declName}: the premise after hcalls reads its proof"
  let hrunNT := (← whnf afterB).bindingDomain!
  fileLine s!"setup.head done: tree sizes (capped at 5000000) — the calls' premise {sz hcallsT}, the runs' premise {sz hrunNT}"
  -- ONE entry of `hrunN` per chosen k (499–537): cheap by reading, so first
  for k in ks do
    let some (c, _, _) := calls[k]? | throwError "{declName}: call {k}"
    if (Tools.ShippingMachineMemCommand.memWidths? c).isSome then
      throwError "{declName}: call {k} is a memory read (not what this probe is for)"
    let goalK := ((hrunNT.bindingBody!.instantiate1 (mkNatLit k)).bindingBody!.instantiate1
      (toExpr c)).bindingBody!
    let some hP := hPOf.get? c | throwError "{declName}: premise {c}"
    let j := seqKids.idxOf c
    let hPS : Term := ⟨mkIdent (Name.mkSimple s!"hP{j}")⟩
    if freeOf.getD c false then
      discard <| pieceM cfg s!"call {k}: hrunN.tactic (a leaf child that closes in every context)"
        (proveByTacticT goalK `(tactic| (intro _ mctx' cctx' mc Dc w w' hw hrun _ _; exact ⟨_, _, _, _, w, w', Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx $hPS, $(mkIdent (`_root_ ++ c ++ `machine_closes)) _ _ _ _⟩)))
    else if leaf.getD c true then
      discard <| pieceM cfg s!"call {k}: hrunN.tactic (a leaf child)"
        (proveByTacticT goalK `(tactic| (intro _ mctx' cctx' mc Dc w w' hw hrun _ _; exact ⟨_, _, _, _, w, w', Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx ($hPS).1, ($hPS).2 mctx' cctx' (Tools.ShippingChildInv.ChildRanIn.of_run hw hrun)⟩)))
    else match namesOf.get? c with
      | none =>
        discard <| pieceM cfg s!"call {k}: hrunN.tactic (a child with calls, its closing a premise)"
          (proveByTacticT goalK `(tactic| (intro _ mctx' cctx' mc Dc w w' hw hrun hcons _; exact Tools.ShippingMachineDepthRun.machineRunNC_of_real (Tools.ShippingChildInv.RealChild.of_inv hw hrun) hcons ($hPS).1 (fun mc cc ran => (($hPS).2 mc cc ran).2) (fun mc cc _ _ _ ran _ => (($hPS).2 mc cc ran).1) (by decide))))
      | some names => do
        -- the closing, from the child's boundary: `c.machine_closes_at`
        let some bnd := bndOf.get? c | throwError "{declName}: boundary of {c}"
        let worldT := mkApp (mkConst ``Void []) (mkConst ``IO.RealWorld)
        let hclE? ← pieceM cfg s!"call {k}: hrunN.closing (closesAtProof {c})" (
          withLocalDeclD `mc (mkConst ``Lean.Meta.Context) fun mc' =>
          withLocalDeclD `cc (mkConst ``Lean.Core.Context) fun cc' =>
          withLocalDeclD `wc worldT fun wc =>
          withLocalDeclD `raw modT fun raw => withLocalDeclD `D desT fun dD => do
          let ctx' := #[mc', ctx[1]!, cc', ctx[3]!]
          let ran := mkAppN (mkConst ``Tools.ShippingChildInv.ChildRanIn) #[ctx[1]!, ctx[3]!, toExpr c, mc', cc']
          withLocalDeclD `ran ran fun hran =>
          withLocalDeclD `hb (bnd.beta (ctx' ++ #[wc, raw, dD])).headBeta fun hb => do
            let nameHs ← projs (← mkAppM ``And.left #[← mkAppM ``And.right #[hP]]) names
            mkLambdaFVars #[mc', cc', wc, raw, dD, hran, hb] (← closesAtProof c ctx' hb nameHs))
        match hclE? with
        | Option.none => fileLine s!"call {k}: hrunN.tactic not run (no closing proof)"
        | Option.some hclE =>
          discard <| pieceM cfg s!"call {k}: hrunN.tactic (machineRunNC_of_real, the closing derived)" (
            withLocalDeclD `hclC (← inferType hclE) fun hclV => do
              let pr ← proveByTacticT goalK `(tactic| (intro _ mctx' cctx' mc Dc w w' hw hrun hcons _; exact Tools.ShippingMachineDepthRun.machineRunNC_of_real (Tools.ShippingChildInv.RealChild.of_inv hw hrun) hcons ($hPS).1 (fun mc cc ran => ($hPS).2.2 mc cc ran) $(mkIdent `hclC) (by decide)))
              pure ((← mkLambdaFVars #[hclV] pr).beta #[hclE]))
  -- ONE entry of `hcalls` per chosen k (354–476), the tactic in pieces
  forallBoundedTelescope hcallsT (some 3) fun ibb rest => do
    -- the parent's let observations and call extension at this family point
    let lsrcE := (tyArgs[10]!).beta ibb
    let extE := (tyArgs[8]!).beta ibb
    let extBE := (tyArgs[9]!).beta ibb
    -- the call extension's definition, for the calls' argument Signals
    let unfoldExt (e : Lean.Expr) : MetaM Lean.Expr := do
      let e ← whnfCore e.headBeta
      let f := e.getAppFn
      if let .const n _ := f then
        if let some v := (← getEnv).find? n >>= (·.value?) then
          return (v.beta e.getAppArgs).headBeta
      pure e
    let extBody ← unfoldExt extE
    let extBBody ← unfoldExt extBE
    fileLine s!"pieces of {declName}: tree sizes (capped at 5000000) — the extension's body {sz extBody}, the Bool extension's body {sz extBBody}, the let observations {sz lsrcE}"
    for k in ks do
      let some (c, argsK, _) := calls[k]? | throwError "{declName}: call {k}"
      let goalK := ((rest.bindingBody!.instantiate1 (mkNatLit k)).bindingBody!.instantiate1
        (toExpr c)).bindingBody!
      let some seqRun := seqRuns.get? c | throwError "{declName}: child {c}"
      let (src0, Dc, idxE) ← srcAt c ibb[0]!
      -- the call: its signal at the call's port, and its arguments
      let pos := r.nDecl + k
      let some sig := (sigAtPos pos extBody).orElse fun _ => sigAtPos pos extBBody
        | throwError "{declName}: call {k}: no signal at port {pos}"
      let some call := findCall c sig | throwError "{declName}: call {k}: no call of {c}"
      let callArgs := call.getAppArgs
      let cr ← readMachine c
      let bsIn : List (Name × MixedGateBinder) := cr.shape.binders.take cr.nDecl
      unless callArgs.size == bsIn.length do
        throwError "{declName}: call {k}: {callArgs.size} arguments, {bsIn.length} binders"
      -- the child's output read by this call
      let field := r.shape.instFields.getD k ""
      let some k' := cr.shape.layout.outs.findIdx? (fun (o : Sparkle.IR.Machine.OutField) => o.name == field)
        | throwError "{declName}: call {k}: field {field}"
      let bsInE0 ← mkAppM ``Tools.ShippingMachineAuto.MachineData.bsIn #[mkConst (c ++ `machineData)]
      let bsInE ← if leaf.getD c true then pure bsInE0
        else mkAppM ``List.take #[mkNatLit cr.nDecl, bsInE0]
      let vs ← mkAppM ``Tools.ShippingMachineCallsLinkedT.valsOf
        #[lsrcE, listE nat (argsK.map mkNatLit)]
      -- the families the decoded inputs are: the call's arguments at their positions
      let mut A ← mkAppOptM ``Tools.ShippingMachineChild.boolsOf #[Dc, bsInE, vs]
      let mut B ← mkAppOptM ``Tools.ShippingMachineChild.bitsOf #[Dc, bsInE, vs]
      for (pIdx, bnd) in (List.range bsIn.length).zip bsIn do
        let kind : MixedGateBinder := bnd.2
        if kind == MixedGateBinder.bool then
          A ← mkAppM ``Tools.ShippingMachineCausal.extendBools #[A, mkNatLit pIdx, callArgs[pIdx]!]
        if let .bits w := kind then
          B ← mkAppM ``Tools.ShippingMachineAuto.extendBits
            #[B, mkNatLit pIdx, mkNatLit w, callArgs[pIdx]!]
      let kinds : List MixedGateBinder := bsIn.map (fun b => b.2)
      let argSizes : List Nat := callArgs.toList.map sz
      fileLine s!"call {k} of {c}: field {field} = the child's output {k'}; argument lets {argsK}; {callArgs.size} call arguments of tree sizes {argSizes}; the call's signal {sz sig}; the Bool family {sz A}; the bit-vector family {sz B}; the entry's goal {sz goalK}"
      let tyA ← inferType A
      let tyB ← inferType B
      let tyI ← inferType idxE
      let srcE := src0
      let tyS ← inferType srcE
      let proofK? ← withLetDecl `famA tyA A fun aF => withLetDecl `famB tyB B fun bF =>
        withLetDecl `famI tyI idxE fun iF => withLetDecl `famS tyS srcE fun sF => do
        let mvar ← mkFreshExprMVar goalK
        let (allOk, _) ← (Term.TermElabM.run (do
          let lit (n : Nat) := Syntax.mkNumLit (toString n)
          let argsArr : Array Term := (argsK.map fun n => (⟨lit n⟩ : Term)).toArray
          let argsS ← `([$argsArr,*])
          let srcS : Term := ⟨mkIdent `famS⟩
          let idxS : Term := ⟨mkIdent `famI⟩
          let AS : Term := ⟨mkIdent `famA⟩
          let BS : Term := ⟨mkIdent `famB⟩
          let rangeS ← rangeSyntax kinds
          let seqRunS := mkIdent (`_root_ ++ seqRun)
          let caseB ← if leaf.getD c true then
              `(tactic| (
                obtain ⟨_, _, _, _, _, _, _, hr', entry', closes'⟩ := hmr
                refine ⟨$seqRunS $idxS hr' entry' closes' _ _ _, ?_⟩
                rw [($seqRunS $idxS hr' entry' closes' (fun _ => none)
                  { topModule := "", modules := [] } 0).2.2.2.2.2.1]
                decide))
            else
              `(tactic| (
                have hrn := hmr
                exact ⟨$seqRunS $idxS hrn, by rw [($seqRunS $idxS hrn).2.2.2.2.2.1]; decide⟩))
          -- the skeleton
          let stage1 ← `(tactic| (
            right
            unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
            refine ⟨rfl, $argsS, rfl, ?b, ?l, ?r, $(lit k'), _, _, rfl, rfl, ?f, fun τ => rfl⟩))
          let gs? ← pieceT cfg s!"call {k}: refine (the skeleton)"
            (Tactic.run mvar.mvarId! (Tactic.evalTactic stage1))
          match gs? with
          | Option.none => return false
          | Option.some gs =>
            let tags ← tagsOf gs
            fileLine s!"call {k}: after the skeleton {gs.length} goals, tags {tags}"
            let mut ok : Bool := true
            -- case r
            let tacR ← `(tactic| (
              intro τ
              unfold Tools.ShippingMachineChild.InRange
              exact $rangeS))
            let okR ← closeOnTag cfg s!"call {k}: r (InRange of {kinds.length} inputs)" gs "r" tacR
            ok := ok && okR
            -- case l
            let tacL ← `(tactic| (
              exact Tools.ShippingMachineCallsLinkedT.args_facts (by decide)
                (by simp [Tools.ShippingMachineCausal.letObsB, Tools.ShippingMachineCausal.letObsLoop,
                  Tools.ShippingMachineCausal.letObsComb])))
            let okL ← closeOnTag cfg s!"call {k}: l (args_facts: decide, simp of the let observations' length)"
              gs "l" tacL
            ok := ok && okL
            -- case b
            let tacB ← `(tactic| (
              intro mc hmr
              $caseB:tactic))
            let okB ← closeOnTag cfg s!"call {k}: b (the child's run theorem at the instance; decide of argPorts' length)"
              gs "b" tacB
            ok := ok && okB
            -- case f, cut at decoded_eq's two arguments and the final rfl
            let stageF ← `(tactic| (
              refine (congrArg (fun l => l[$(lit k')]?)
                (Tools.ShippingMachineCallsLinkedT.decoded_eq (bools' := $AS) (bits' := $BS) $srcS
                  ?hb ?hv)).trans ?fin))
            let fs? ← runOnTag cfg s!"call {k}: f.refine (congrArg … (decoded_eq … ?hb ?hv) |>.trans ?fin)"
              gs "f" stageF
            match fs? with
            | Option.none => return false
            | Option.some fs =>
              let ftags ← tagsOf fs
              fileLine s!"call {k}: after f.refine {fs.length} goals, tags {ftags}"
              let tacFin ← `(tactic| exact rfl)
              let okFin ← closeOnTag cfg s!"call {k}: f.fin (rfl: the child's source at field {k'} on the families = the parent's extension at position {pos})"
                fs "fin" tacFin
              ok := ok && okFin
              let tacHb ← `(tactic| (
                funext p
                try simp (config := { zetaDelta := true }) only [Tools.ShippingMachineCausal.extendBools]
                (repeat' split) <;> (first
                  | (rename_i hp; subst hp; exact Tools.ShippingMachineCallsLinkedT.boolsOf_at
                      (fun τ => Tools.ShippingMachineCallsLinkedT.decB_valsOf rfl (by decide) rfl τ))
                  | rfl)))
              let okHb ← closeOnTag cfg s!"call {k}: f.hb (the Bool family: funext, simp only [extendBools], split, close)"
                fs "hb" tacHb
              ok := ok && okHb
              let tacHvSimp ← `(tactic| (
                funext p n
                try simp (config := { zetaDelta := true }) only [Tools.ShippingMachineAuto.extendBits]))
              let hv1? ← runOnTag cfg s!"call {k}: f.hv.simp (funext, simp only [extendBits] with zetaDelta)"
                fs "hv" tacHvSimp
              match hv1? with
              | Option.none => return false
              | Option.some hv1 =>
                let mut leaves : List MVarId := []
                let mut splitOk : Bool := true
                for g in hv1 do
                  let tacSplit ← `(tactic| repeat' split)
                  let ls? ← pieceT cfg s!"call {k}: f.hv.split (repeat' split)"
                    (Tactic.run g (Tactic.evalTactic tacSplit))
                  match ls? with
                  | Option.none => splitOk := false
                  | Option.some ls => leaves := leaves ++ ls
                ok := ok && splitOk
                fileLine s!"call {k}: f.hv.split left {leaves.length} leaves"
                let tacLeaf ← `(tactic| first
                  | (rename_i hp; obtain ⟨hp1, hp2⟩ := hp; subst hp1; subst hp2; (try simp only [cast_eq]); exact Tools.ShippingMachineCallsLinkedT.bitsOf_at
                      (fun τ => Tools.ShippingMachineCallsLinkedT.decV_valsOf rfl (by decide) rfl τ))
                  | rfl)
                let mut idx : Nat := 0
                for g in leaves do
                  let lf? ← pieceT cfg s!"call {k}: f.hv.leaf {idx} (bitsOf_at (decV_valsOf rfl (by decide) rfl), or rfl)"
                    (Tactic.run g (Tactic.evalTactic tacLeaf))
                  match lf? with
                  | Option.none => ok := false
                  | Option.some remaining =>
                    unless remaining.isEmpty do
                      fileLine s!"FAILED call {k}: f.hv.leaf {idx} — {remaining.length} goals remain"
                      ok := false
                  idx := idx + 1
                return ok)) {}
        if allOk then
          let pr? ← pieceM cfg s!"call {k}: instantiateMVars and the families put back" (do
            pure ((← instantiateMVars mvar).replaceFVar aF A |>.replaceFVar bF B |>.replaceFVar iF idxE
              |>.replaceFVar sF srcE))
          pure pr?
        else
          fileLine s!"call {k}: a piece did not close its goal — no proof of the entry, no Meta.check"
          pure none
      match proofK? with
      | Option.none => pure ()
      | Option.some proofK =>
        if proofK.hasExprMVar then
          fileLine s!"call {k}: the entry's proof has unassigned metavariables — no Meta.check"
        else
          fileLine s!"call {k}: the entry's proof, tree size {sz proofK} (capped at 5000000)"
          discard <| pieceM cfg s!"call {k}: Meta.check of the entry's proof (the generator's line 475)"
            (check proofK)

end Tests.Compiler.KeccakSpongeStepProbe2

/-! ## The step wrappers (commands) -/

namespace Tests.Compiler.KeccakSpongeStepProbe2
open Lean Meta Elab Command

/-- A line of the probe: to the progress file now, to the message log when
the command ends. -/
def note (msg : String) : CommandElabM Unit := do
  Tests.Compiler.KeccakSpongeLogLib.toFile fallback msg
  logInfo m!"{msg}"

/-- A generator function under the options `#machine_design_svNR` sets. -/
def deep {α : Type} (x : MetaM α) : CommandElabM α :=
  liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) x

/-- One step. The FIRST thing it does is write a line to the file: `START`,
or `SKIPPED` with the missing constants. Then the action; `OK (ms) — its
line` or `FAILED (ms) — message` with the environment and the message log
put back. Never throws. -/
def runStep (label : String) (deps : List Name) (act : CommandElabM String) :
    CommandElabM Unit := do
  let env0 ← getEnv
  let missing : List Name := deps.filter fun n => !env0.contains n
  unless missing.isEmpty do
    note s!"SP2 STEP {label}: SKIPPED — not in the environment: {missing}"
    return
  note s!"SP2 STEP START {label}"
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let before := savedMsgs.toList.length
  let t0 ← IO.monoMsNow
  let res : Except String String ← try
      let s ← act
      pure (Except.ok s)
    catch ex =>
      let msg ← ex.toMessageData.toString
      pure (Except.error msg)
  let t1 ← IO.monoMsNow
  let msgs := (← get).messages.toList.drop before
  let errs ← (msgs.filter (·.severity == .error)).mapM fun m => m.data.toString
  let failure : Option String := match res with
    | Except.error msg => some msg
    | Except.ok _ => if errs.isEmpty then none else some (String.intercalate " | " (errs.take 2))
  match failure with
  | some msg =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    note s!"SP2 STEP {label}: FAILED ({t1 - t0} ms) — {Tests.Compiler.KeccakSpongeLogLib.clipStr msg}"
  | none =>
    let infos ← (msgs.filter (·.severity == .information)).mapM fun m => m.data.toString
    for i in infos do
      Tests.Compiler.KeccakSpongeLogLib.toFile fallback s!"  | {Tests.Compiler.KeccakSpongeLogLib.clipStr i 3000}"
    let line : String := match res with
      | Except.ok s => s
      | Except.error _ => ""
    let tail : String := if line.isEmpty then "" else " — " ++ line
    note s!"SP2 STEP {label}: OK ({t1 - t0} ms){tail}"

/-- `#sp2_cmd "n" "what" given [c, …] in cmd`: a command as a step. -/
elab "#sp2_cmd " step:str ppSpace tag:str " given " "[" ids:ident,* "]" " in " c:command :
    command => do
  let deps : List Name := ids.getElems.toList.map fun i => i.getId
  runStep s!"{step.getString} {tag.getString}" deps do
    elabCommand c
    pure ""

/-- `#sp2_env "n"`: is the generators' progress variable set; is the full run asked. -/
elab "#sp2_env " step:str : command => do
  let isSet ← Tests.Compiler.KeccakSpongeLogLib.progressSet
  let full := (← IO.getEnv "SPARKLE_SPONGE_FULL").isSome
  note s!"SP2 STEP {step.getString} SPARKLE_MACHINE_PROGRESS set: {isSet} (when false the generators write NO progress line and this file's lines are in {fallback}); SPARKLE_SPONGE_FULL set: {full} (when false steps 15–17, the full generateCoreNR and what follows, are SKIPPED)"

/-- `#sp2_read "n" [decl, …]`: the reader's data (logged, nothing asserted). -/
elab "#sp2_read " step:str " [" ids:ident,* "]" : command => do
  for i in ids.getElems do
    let n := i.getId
    runStep s!"{step.getString} read {n}" [n] do
      let r ← liftTermElabM (Tools.ShippingMachineCommand.readMachine n)
      pure (Tests.Compiler.KeccakSpongeLogLib.describeRead r)

/-- `#sp2_fn "n" kind decl depth given [c, …]`: one function of the depth
generator as a step. `kind`: `candidates`, `composedRA`, `combNR`, `runOfR`,
and — only when `SPARKLE_SPONGE_FULL` is set — `coreNR`, `shipsNR`,
`designNR`. -/
elab "#sp2_fn " step:str ppSpace kind:ident ppSpace d:ident ppSpace n:num " given "
    "[" ids:ident,* "]" : command => do
  let decl := d.getId
  let dep : Nat := n.getNat
  let deps : List Name := decl :: (ids.getElems.toList.map fun i => i.getId)
  let k : String := kind.getId.toString
  let label := s!"{step.getString} {k} {decl} {dep}"
  let full := (← IO.getEnv "SPARKLE_SPONGE_FULL").isSome
  if (k == "coreNR" || k == "shipsNR" || k == "designNR") && !full then
    note s!"SP2 STEP {label}: SKIPPED — SPARKLE_SPONGE_FULL is not set (the step that did not end in 38 min; the pieces of steps 12–13 are the diagnostic)"
  else if k == "candidates" then
    runStep label deps <| deep do
      let cands ← Tools.ShippingMachineDepthCommand.closingCandidates decl (← IO.mkRef [])
      let mut out : List String := []
      for c in cands do
        let th ← Tools.ShippingMachineDepthCommand.closingThm? c
        out := out ++ [s!"{c}: closing theorem {th}"]
      pure s!"the descendants with calls, children first: {out}"
  else if k == "composedRA" then
    runStep label deps <| deep do
      let nm ← Tools.ShippingMachineComposeRCommand.generateComposedR decl (atW := true)
      pure s!"{nm}"
  else if k == "combNR" then
    runStep label deps <| deep do
      let nm ← Tools.ShippingMachineDepthCommand.generateCombNR decl dep
      pure s!"{nm}"
  else if k == "runOfR" then
    runStep label deps <| deep do
      let (nm, _) ← Tools.ShippingMachineDepthCommand.generateRunOfR decl dep
      pure s!"{nm}"
  else if k == "coreNR" then
    runStep label deps <| deep do
      let nm ← Tools.ShippingMachineDepthCommand.generateCoreNR decl dep
      pure s!"{nm}"
  else if k == "shipsNR" then
    runStep label deps <| deep do
      let nm ← Tools.ShippingMachineDepthCommand.generateShipsNR decl dep
      pure s!"{nm}"
  else if k == "designNR" then
    runStep label deps <| deep do
      let nm ← Tools.ShippingMachineDepthCommand.generateDesignNR decl dep
      pure s!"{nm}"
  else
    note s!"SP2 STEP {label}: SKIPPED — unknown kind {k} (a defect of the probe file)"

/-- `#sp2_calls "n" decl depth at [k, …] budget hbK wall sec given [c, …]`:
the call entries `k` in budgeted pieces — `hbK` thousand heartbeats per
piece (0: no limit), `sec` seconds of soft limit for the step (0: none).
Adds no constant. Its first action is the `START` (or `SKIPPED`) line of
`runStep`, in the progress file. -/
elab "#sp2_calls " step:str ppSpace d:ident ppSpace n:num " at " "[" ks:num,* "]"
    " budget " hb:num " wall " sec:num " given " "[" ids:ident,* "]" : command => do
  let decl := d.getId
  let dep : Nat := n.getNat
  let kl : List Nat := ks.getElems.toList.map fun x => x.getNat
  let hbK : Nat := hb.getNat
  let softMs : Nat := sec.getNat * 1000
  let deps : List Name := decl :: (ids.getElems.toList.map fun i => i.getId)
  let savedEnv ← getEnv
  let label := s!"{step.getString} call entries {kl} of {decl} at depth {dep}, in pieces ({hbK}k heartbeats per piece, soft limit {softMs} ms)"
  runStep label deps do
    let acc ← IO.mkRef (#[] : Array String)
    let start ← IO.monoMsNow
    let cfg : Cfg := { acc := acc, hbK := hbK, start := start, softMs := softMs }
    let res : Option String ← try
        deep (callPieces decl dep kl cfg)
        pure none
      catch ex =>
        let msg ← ex.toMessageData.toString
        pure (some msg)
    -- nothing of the pieces is kept
    setEnv savedEnv
    let lines ← acc.get
    match res with
    | some msg =>
      Tests.Compiler.KeccakSpongeLogLib.toFile fallback s!"SP2   the pieces stopped: {Tests.Compiler.KeccakSpongeLogLib.clipStr msg}; pieces so far (ms): {lines.toList}"
      throwError "the pieces stopped: {msg}; pieces so far (ms): {lines.toList}"
    | none => pure s!"pieces (ms): {lines.toList}"

/-- `#sp2_summary [c, …]`: which of the named constants exist at the end. -/
elab "#sp2_summary " "[" ids:ident,* "]" : command => do
  let env ← getEnv
  let names : List Name := ids.getElems.toList.map fun i => i.getId
  let present : List Name := names.filter fun n => env.contains n
  let absent : List Name := names.filter fun n => !env.contains n
  note s!"SP2 STEP END: in the environment {present}; NOT in the environment {absent}. LOG ONLY — nothing here is asserted"

end Tests.Compiler.KeccakSpongeStepProbe2

/-! ## Step 0: the wrappers themselves -/

#sp2_cmd "0a" "self-test of the wrapper (FAILED is the expected line: an unknown constant)"
    given [Nat] in
  #check keccakSpongeStep2NoSuchConstant

#sp2_cmd "0b" "self-test of the wrapper (OK is the expected line)" given [Nat] in
  #check Nat

#sp2_env "0c"

-- the pieces command on a declaration it must refuse: FAILED is the expected line
#sp2_calls "0d" Nat 0 at [0] budget 1000 wall 10 given [Nat]

/-! ## Step 1: the reader's data -/

set_option maxHeartbeats 0 in
#sp2_read "1" [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF]

/-! ## Steps 2–7: the base -/

set_option maxHeartbeats 0 in
#sp2_cmd "2" "keccakRcHW #gate_child" given [Sparkle.IP.Crypto.Keccak256HW.keccakRcHW] in
  #gate_child Sparkle.IP.Crypto.Keccak256HW.keccakRcHW

set_option maxHeartbeats 0 in
#sp2_cmd "3" "wKeccakF #machine_endpoint" given [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF] in
  #machine_endpoint Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
#sp2_cmd "4" "wKeccakF #machine_linked"
    given [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound] in
  #machine_linked Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
#sp2_cmd "5" "wKeccakF #machine_composed"
    given [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_linked,
      Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_child] in
  #machine_composed Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
#sp2_cmd "6" "keccak256SpongeHW #machine_endpoint"
    given [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound] in
  #machine_endpoint Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW

set_option maxHeartbeats 0 in
#sp2_cmd "7" "wKeccakF #machine_closes_at"
    given [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound,
      Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_child] in
  #machine_closes_at Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

/-! ## Steps 8–11: what the depth generator does before `generateCoreNR`'s own work -/

set_option maxHeartbeats 0 in
#sp2_fn "8" candidates Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1
  given [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound]

set_option maxHeartbeats 0 in
#sp2_fn "9" composedRA Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF 0
  given [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound,
    Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_linked]

set_option maxHeartbeats 0 in
#sp2_fn "10" combNR Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF 0
  given [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_composedRA]

set_option maxHeartbeats 0 in
#sp2_fn "11" runOfR Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF 0
  given [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_composedNRH0]

/-! ## Steps 12–13: the interval between the generator's two progress lines, in budgeted pieces -/

set_option maxHeartbeats 0 in
#sp2_calls "12" Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1 at [0]
  budget 20000 wall 420
  given [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound,
    Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.seq_child_runN_ofR0,
    Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at]

set_option maxHeartbeats 0 in
#sp2_calls "13" Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1 at [1, 26]
  budget 20000 wall 420
  given [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound,
    Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.seq_child_runN_ofR0,
    Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at]

/-! ## Steps 15–17: the generator's own functions — ONLY with `SPARKLE_SPONGE_FULL` set -/

set_option maxHeartbeats 0 in
#sp2_fn "15" coreNR Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1
  given [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound,
    Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.seq_child_runN_ofR0,
    Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at]

set_option maxHeartbeats 0 in
#sp2_fn "16" shipsNR Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1
  given [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_composedNR1]

set_option maxHeartbeats 0 in
#sp2_fn "17" designNR Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1
  given [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_ships_hierNR1]

/-! ## What exists at the end -/

#sp2_summary [Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_child,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_composedRA,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_composedNRH0,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.seq_child_runN_ofR0,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_composedNR1,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_ships_hierNR1,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_svNR1]

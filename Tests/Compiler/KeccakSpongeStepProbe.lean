import IP.Crypto.Keccak256Sponge
import Tools.ShippingMachineCommand
import Tools.ShippingMachineLinkedCommand
import Tools.ShippingGateChildCommand
import Tools.ShippingMachineComposeRCommand
import Tools.ShippingMachineClosesAtGen
import Tools.ShippingMachineDepthCommandR
import Tests.Compiler.KeccakSpongeLogLib

/-! # The sponge's depth endpoint, sub-step by sub-step: a LOG-ONLY, TIME-LIMITED probe (round par/a-25)

WRITTEN, NOT BUILT, NOT RUN. This file CLAIMS NOTHING: no step asserts, a
failing step is logged and the file goes on. It answers ONE question: in
`#machine_design_svNR keccak256SpongeHW 1` — which did not return within the
limit of the Keccak probe (`docs/parallel/B-keccak.md`, run record, step 13)
— WHICH sub-step of the depth generator is the expensive one. Reading and
predictions: `docs/parallel/A-keccak.md`.

## For the integrator

* TARGET-ONLY, NEVER IMPORTED, NOT for `Tests/AllTests.lean`. It generates
  `keccakRcHW.gate_*`, `wKeccakF.machine_*`, `keccak256SpongeHW.machine_*`
  under their usual names in THIS module: never import it together with
  `Tests/Compiler/KeccakProbeTest.lean` or `Tests/Compiler/OneOutWKeccakFTest.lean`.
* Run it with a wall-clock limit, the memory cap, and — THIS TIME — the
  progress variable SET, as an ABSOLUTE path to a FRESH file:

      SPARKLE_MACHINE_PROGRESS=$HOME/sparkle-work/keccak-sponge-step.log \
        ~/sparkle-work/bin/cgrun.sh -n sponge-step -m 3G -s 0 -t 2400 -- \
        lake build Tests.Compiler.KeccakSpongeStepProbe

  The Keccak probe's run had the variable UNSET (its `env.sh` has no
  `SPARKLE_*` line; the probe's lines went to the fallback
  `.lake/keccak-probe.log`): the generators' own `progress` lines are then
  not written at all (`Tools.ShippingMachineCommand.progress` 548–555 is a
  no-op without the variable). That is why none appeared after `START 13`;
  it says NOTHING about where the generator was. Step `0c` of this file
  logs whether the variable is set.
* Every line is written to the progress file AT ONCE with a millisecond
  clock, VmRSS and VmHWM (fallback without the variable:
  `.lake/keccak-sponge-step.log`, and then WITHOUT the generators' lines).
  `SPONGE STEP START <n> <what>` before a step, `SPONGE STEP <n> <what>: OK
  (ms) | FAILED (ms) — message | SKIPPED — missing` after it; inside steps
  12–13 a `START` / `OK (ms)` pair per PIECE of one call entry's proof. After
  a timeout or a memory kill the LAST line of the file names the sub-step
  (and the piece) that was running. The build's message log shows nothing of
  a killed command.
* VmRSS counts the mapped `.olean` files (≈ 1.8 GB before any step); the cap
  is about the cgroup's `memory.current` (`samples.txt` of the run record).
  The earlier run reached `memory.high` (2.74 GB) 989 s after its start and
  was throttled from then on: the time after that point measures the
  throttle, not the generator.

## The steps (ordered so that a timeout shows which sub-step was running)

| step | what | the generator's sub-step it is |
|---|---|---|
| 0a, 0b, 0c | self-test of the wrapper (FAILED, OK expected); is the progress variable set | — |
| 1 | reader data of the sponge and of `wKeccakF` | — |
| 2–7 | base: `#gate_child keccakRcHW`; `#machine_endpoint`, `#machine_linked`, `#machine_composed` on `wKeccakF`; `#machine_endpoint` on the sponge; `#machine_closes_at wKeccakF` | the Keccak probe's steps 5–10 (all OK there, 5–50 s each) |
| 8 | `closingCandidates` of the sponge | `preClose` (`ShippingMachineDepthCommandR` 658–676): reader runs only when the closing theorems exist |
| 9 | `generateComposedR wKeccakF (atW := true)` → `wKeccakF.machine_composedRA` | first thing `generateCombNR` does (line 43); in the Keccak probe's run the constant existed already (`#machine_design_svHR wKeccakF` generates it, `generateShipsHR` 311 — not run in this file) |
| 10 | `generateCombNR wKeccakF 0` → `wKeccakF.machine_composedNRH0` | 2 decided conditions on the child's data |
| 11 | `generateRunOfR wKeccakF 0` → `wKeccakF.seq_child_runN_ofR0` | 10 decided conditions on the child's data (27 output names) + the two extension tactics |
| 12 | ONE call entry (k = 0) of the per-call loop, in PIECES, each timed; before it the 8 decided conditions on the PARENT's data, each kernel-checked alone | `generateCoreNR` 346–476: the loop body, once instead of 27 times |
| 13 | the same for k = 1 and k = 26 (the `Bool` output `done`) | does a second entry cost the same (no reuse)? |
| 14 | `generateCoreNR keccak256SpongeHW 1` → `…machine_composedNR1` | the whole loop (27 entries), `hrunN` (27), the kernel check (after the generator's own line `…machine_composedNR1: checking`) |
| 15 | `generateShipsNR … 1` → `…machine_ships_hierNR1` | `machine_ships_hierC`, one decided output-width condition |
| 16 | `generateDesignNR … 1` → `…machine_design_svNR1` | `ShippingShipsDesignSVCommand.compose` |

Steps 12–13 add NO constant: the pieces' proofs are thrown away. They are a
COPY of the generator's loop body (the set-up of `generateCoreNR` 186–273,
346–353, 354–417 verbatim; the entry's tactic of 439–470 cut at its `case`s
and, inside `case f`, at `decoded_eq`'s two arguments and the final `rfl`),
so their times are the times of the generator's own proof of that entry up
to the cuts. The pieces of one entry:

    refine      the skeleton ⟨rfl, args, rfl, ?b, ?l, ?r, k', _, _, rfl, rfl, ?f, fun τ => rfl⟩
    b           the child's run theorem at the instance, argPorts' length (decide)
    l           args_facts (decide; simp of the let observations' length)
    r           InRange (26 inputs)
    f.refine    congrArg … (decoded_eq … ?hb ?hv) |>.trans ?fin
    f.hb        the Bool family: funext, simp only [extendBools], repeat' split, close
    f.hv.simp   the bit-vector family: funext, simp only [extendBits] (25 nested dites appear)
    f.hv.split  repeat' split  (25 splits, 26 leaves)
    f.hv.close  per leaf: bitsOf_at (decV_valsOf rfl (by decide) rfl) — the rfl compares the
                parent's REFLECTED let, evaluated through typedVal (35 lets, 30 slots), with the
                call's source argument
    f.fin       rfl: the child's machineSource at field k' on the families = the parent's
                extension at the call's position
    instantiate, Meta.check   as the generator does after the tactic (line 475)

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The pieces of one call entry (MetaM; the opens of `Tools/ShippingMachineDepthCommandR.lean`) -/

namespace Tests.Compiler.KeccakSpongeStepProbe
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine progress listE)
open Tools.ShippingMachineSeqCommand
open Tools.ShippingMachineDepthCommand

/-- The file the lines go to without the progress variable. -/
def fallback : String := ".lake/keccak-sponge-step.log"

/-- A line of a piece: to the progress file, at once. -/
def fileLine (msg : String) : IO Unit :=
  Tests.Compiler.KeccakSpongeLogLib.toFile fallback s!"SPONGE STEP   {msg}"

/-- A timed piece (MetaM). The `OK` line exists only when the piece ended. -/
def pieceM {α : Type} (acc : IO.Ref (Array String)) (label : String) (x : MetaM α) : MetaM α := do
  fileLine s!"START {label}"
  let t0 ← IO.monoMsNow
  let a ← x
  let t1 ← IO.monoMsNow
  fileLine s!"OK {label} ({t1 - t0} ms)"
  acc.modify fun l => l.push s!"{label}: {t1 - t0} ms"
  return a

/-- A timed piece (TermElabM). -/
def pieceT {α : Type} (acc : IO.Ref (Array String)) (label : String) (x : Term.TermElabM α) :
    Term.TermElabM α := do
  fileLine s!"START {label}"
  let t0 ← IO.monoMsNow
  let a ← x
  let t1 ← IO.monoMsNow
  fileLine s!"OK {label} ({t1 - t0} ms)"
  acc.modify fun l => l.push s!"{label}: {t1 - t0} ms"
  return a

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

/-- The goal whose tag ends in `s`. -/
def goalTagged (gs : List MVarId) (s : String) : MetaM MVarId := do
  let mut tags : List Name := []
  for g in gs do
    let t ← g.getTag
    if tagEnd t == s then return g
    tags := tags ++ [t]
  throwError "no goal tagged {s}; the goals' tags: {tags}"

/-- A closed proof checked by the KERNEL alone (as a theorem that is removed
again): what the final kernel check pays for it. Logged, never thrown. -/
def kernelProbe (acc : IO.Ref (Array String)) (label : String) (tag : Name)
    (ty prf : Lean.Expr) : MetaM Unit := do
  if ty.hasFVar || prf.hasFVar || ty.hasExprMVar || prf.hasExprMVar then
    fileLine s!"{label}: not closed — not kernel-checked alone"
    return
  let saved ← getEnv
  fileLine s!"START {label}"
  let t0 ← IO.monoMsNow
  let res : Option String ← try
      addDecl (.thmDecl { name := tag, levelParams := [], type := ty, value := prf })
      pure none
    catch ex =>
      let msg ← ex.toMessageData.toString
      pure (some msg)
  let t1 ← IO.monoMsNow
  setEnv saved
  match res with
  | none =>
    fileLine s!"OK {label} ({t1 - t0} ms)"
    acc.modify fun l => l.push s!"{label}: {t1 - t0} ms"
  | some msg =>
    fileLine s!"REJECTED {label} ({t1 - t0} ms) — {Tests.Compiler.KeccakSpongeLogLib.clipStr msg 600}"
    acc.modify fun l => l.push s!"{label}: REJECTED by the kernel ({t1 - t0} ms)"

/-- One timed tactic on one goal; the goals it leaves. -/
def runOn (acc : IO.Ref (Array String)) (label : String) (g : MVarId) (tac : Syntax) :
    Term.TermElabM (List MVarId) :=
  pieceT acc label (Tactic.run g (Tactic.evalTactic tac))

/-- One timed tactic that must close its goal. -/
def closeOn (acc : IO.Ref (Array String)) (label : String) (g : MVarId) (tac : Syntax) :
    Term.TermElabM Unit := do
  let rest ← runOn acc label g tac
  unless rest.isEmpty do throwError "{label}: goals remain: {rest}"

/-- **The per-call loop body of `generateCoreNR declName dep`, for the call
entries `ks` only, in timed pieces.** A copy of
`Tools.ShippingMachineDepthCommand.generateCoreNR` (lines 186–273, 346–353,
354–417 as they are; the entry's tactic of 439–470 cut into pieces). Adds no
constant; returns the pieces' lines. Needs what the generator's first part
leaves (`c.seq_child_runN_ofR{dep-1}` of a child with calls: found, not
generated again). -/
def callPieces (declName : Name) (dep : Nat) (ks : List Nat) : MetaM (Array String) := do
  let acc ← IO.mkRef (#[] : Array String)
  let r ← readMachine declName
  if r.shape.insts.isEmpty then throwError "{declName}: no call"
  if r.shape.instFields.isEmpty then
    throwError "{declName}: one-output combinational calls (the derived boundary needs the general closing)"
  let (headL, args, back?) ← endpointParts declName
  if back?.isSome then throwError "{declName}: a transported endpoint (not yet at depth)"
  -- the head carrying `ServedReal` (under `ChildBnd`)
  let pL := mkAppN (mkConst (headL.appendAfter "RA")) args
  let calls := r.shape.insts
  let seqKids := ((calls.map (·.1)).eraseDups.filter fun c =>
    (Tools.ShippingMachineMemCommand.memWidths? c).isNone)
  let mut seqRuns : Std.HashMap Name Name := {}
  let mut leaf : Std.HashMap Name Bool := {}
  let mut bndOf : Std.HashMap Name Lean.Expr := {}
  for c in seqKids do
    let cr ← readMachine c
    let isLeaf := cr.shape.insts.isEmpty
    leaf := leaf.insert c isLeaf
    if isLeaf then
      seqRuns := seqRuns.insert c (← (try generateSeqChildN c catch e => throwError "seq child {c}: {e.toMessageData}"))
    else
      if dep == 0 then throwError "{declName}: the child {c} has children; depth 0 is too shallow"
      let (rn, bnd) ← (try generateRunOfR c (dep - 1) catch e => throwError "child {c}: {e.toMessageData}")
      seqRuns := seqRuns.insert c rn
      bndOf := bndOf.insert c bnd
  let headRA : Name := headL.appendAfter "RA"
  fileLine s!"pieces of {declName}: head {headRA}; {calls.length} call entries; sequential children {seqKids}"
  forallTelescope (← inferType pL) fun xs traceT => do
  let h := mkAppN pL xs
  let tyArgs := (← whnfR traceT).getAppArgs
  unless tyArgs.size == 11 do throwError "{declName}: the trace's arguments"
  let (dE, _mE, dsnE) := (tyArgs[2]!, tyArgs[3]!, tyArgs[4]!)
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
  -- per sequential child: its predicate `PC c`
  let modT := mkConst ``Sparkle.IR.AST.Module
  let mut pcCases : List (Name × Lean.Expr) := []
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
  let some (_, pc0) := pcCases.head? | throwError "{declName}: no sequential child"
  let PC ← nameCases (← mkArrow modT (mkSort .zero)) pcCases pc0
  -- the head and its 1 + 7 decided conditions on the PARENT's data: built as
  -- the generator builds them (unchecked), each also kernel-checked alone
  let mut p ← mkAppM ``Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN #[mkNatLit dep, h]
  let ty0 := (← whnf (← inferType p)).bindingDomain!
  let d0 ← mkDecideProof ty0
  kernelProbe acc "parent decide 0 (hfe), kernel alone" (declName ++ `spongeStepProbe_decide0) ty0 d0
  p := mkApp p d0
  p := mkApp p (mkNatLit r.nDecl)
  for j in [0:7] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    let dj ← mkDecideProof ty
    kernelProbe acc s!"parent decide {j + 1} (hkD, hI, hIlen, hSL, hSlen, hLlen, hNIn in this order), kernel alone"
      (declName ++ Name.mkSimple s!"spongeStepProbe_decide{j + 1}") ty dj
    p := mkApp p dj
  p := mkApp4 p bsC outsC S PC
  let hcallsT := (← whnf (← inferType p)).bindingDomain!
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
    fileLine s!"pieces of {declName}: tree sizes (capped at 5000000) — the extension's body {sz extBody}, the Bool extension's body {sz extBBody}, the let observations {sz lsrcE}, the calls' premise {sz hcallsT}"
    for k in ks do
      let some (c, argsK, _) := calls[k]? | throwError "{declName}: call {k}"
      if (Tools.ShippingMachineMemCommand.memWidths? c).isSome then
        throwError "{declName}: call {k} is a memory read (not what this probe is for)"
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
      let proofK ← withLetDecl `famA tyA A fun aF => withLetDecl `famB tyB B fun bF =>
        withLetDecl `famI tyI idxE fun iF => withLetDecl `famS tyS srcE fun sF => do
        let mvar ← mkFreshExprMVar goalK
        let ((), _) ← (Term.TermElabM.run (do
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
          let gs ← runOn acc s!"call {k}: refine (the skeleton)" mvar.mvarId! stage1
          let mut tags : List Name := []
          for g in gs do
            let t ← g.getTag
            tags := tags ++ [t]
          fileLine s!"call {k}: after the skeleton {gs.length} goals, tags {tags}"
          -- case b
          let tacB ← `(tactic| (
            intro mc hmr
            $caseB:tactic))
          closeOn acc s!"call {k}: b (the child's run theorem at the instance; decide of argPorts' length)"
            (← goalTagged gs "b") tacB
          -- case l
          let tacL ← `(tactic| (
            exact Tools.ShippingMachineCallsLinkedT.args_facts (by decide)
              (by simp [Tools.ShippingMachineCausal.letObsB, Tools.ShippingMachineCausal.letObsLoop,
                Tools.ShippingMachineCausal.letObsComb])))
          closeOn acc s!"call {k}: l (args_facts: decide, simp of the let observations' length)"
            (← goalTagged gs "l") tacL
          -- case r
          let tacR ← `(tactic| (
            intro τ
            unfold Tools.ShippingMachineChild.InRange
            exact $rangeS))
          closeOn acc s!"call {k}: r (InRange of {kinds.length} inputs)" (← goalTagged gs "r") tacR
          -- case f, cut at decoded_eq's two arguments and the final rfl
          let stageF ← `(tactic| (
            refine (congrArg (fun l => l[$(lit k')]?)
              (Tools.ShippingMachineCallsLinkedT.decoded_eq (bools' := $AS) (bits' := $BS) $srcS
                ?hb ?hv)).trans ?fin))
          let fs ← runOn acc s!"call {k}: f.refine (congrArg … (decoded_eq … ?hb ?hv) |>.trans ?fin)"
            (← goalTagged gs "f") stageF
          let mut ftags : List Name := []
          for g in fs do
            let t ← g.getTag
            ftags := ftags ++ [t]
          fileLine s!"call {k}: after f.refine {fs.length} goals, tags {ftags}"
          let tacHb ← `(tactic| (
            funext p
            try simp (config := { zetaDelta := true }) only [Tools.ShippingMachineCausal.extendBools]
            (repeat' split) <;> (first
              | (rename_i hp; subst hp; exact Tools.ShippingMachineCallsLinkedT.boolsOf_at
                  (fun τ => Tools.ShippingMachineCallsLinkedT.decB_valsOf rfl (by decide) rfl τ))
              | rfl)))
          closeOn acc s!"call {k}: f.hb (the Bool family: funext, simp only [extendBools], split, close)"
            (← goalTagged fs "hb") tacHb
          let tacHvSimp ← `(tactic| (
            funext p n
            try simp (config := { zetaDelta := true }) only [Tools.ShippingMachineAuto.extendBits]))
          let hv1 ← runOn acc s!"call {k}: f.hv.simp (funext, simp only [extendBits] with zetaDelta)"
            (← goalTagged fs "hv") tacHvSimp
          let mut leaves : List MVarId := []
          for g in hv1 do
            let tacSplit ← `(tactic| repeat' split)
            let ls ← runOn acc s!"call {k}: f.hv.split (repeat' split)" g tacSplit
            leaves := leaves ++ ls
          fileLine s!"call {k}: f.hv.split left {leaves.length} leaves"
          let tacLeaf ← `(tactic| first
            | (rename_i hp; obtain ⟨hp1, hp2⟩ := hp; subst hp1; subst hp2; (try simp only [cast_eq]); exact Tools.ShippingMachineCallsLinkedT.bitsOf_at
                (fun τ => Tools.ShippingMachineCallsLinkedT.decV_valsOf rfl (by decide) rfl τ))
            | rfl)
          let mut closeMs : Nat := 0
          let mut closeMax : Nat := 0
          let mut idx : Nat := 0
          fileLine s!"START call {k}: f.hv.close ({leaves.length} leaves; per leaf bitsOf_at (decV_valsOf rfl (by decide) rfl))"
          for g in leaves do
            let t0 ← IO.monoMsNow
            let remaining ← Tactic.run g (Tactic.evalTactic tacLeaf)
            let t1 ← IO.monoMsNow
            unless remaining.isEmpty do
              throwError "call {k}: f.hv.close: leaf {idx}: goals remain: {remaining}"
            fileLine s!"call {k}: f.hv.close leaf {idx} ({t1 - t0} ms)"
            closeMs := closeMs + (t1 - t0)
            if t1 - t0 > closeMax then closeMax := t1 - t0
            idx := idx + 1
          fileLine s!"OK call {k}: f.hv.close ({closeMs} ms; {idx} leaves; slowest {closeMax} ms)"
          acc.modify fun l => l.push s!"call {k}: f.hv.close: {closeMs} ms over {idx} leaves (slowest {closeMax} ms)"
          let tacFin ← `(tactic| exact rfl)
          closeOn acc s!"call {k}: f.fin (rfl: the child's source at field {k'} on the families = the parent's extension at position {pos})"
            (← goalTagged fs "fin") tacFin)) {}
        let pr ← pieceM acc s!"call {k}: instantiateMVars and the families put back" (do
          pure ((← instantiateMVars mvar).replaceFVar aF A |>.replaceFVar bF B |>.replaceFVar iF idxE
            |>.replaceFVar sF srcE))
        pure pr
      if proofK.hasExprMVar then throwError "{declName}: call {k}: the entry's proof has unassigned metavariables"
      fileLine s!"call {k}: the entry's proof, tree size {sz proofK} (capped at 5000000)"
      pieceM acc s!"call {k}: Meta.check of the entry's proof (the generator's line 475)" (check proofK)
    acc.get

end Tests.Compiler.KeccakSpongeStepProbe

/-! ## The step wrappers (commands) -/

namespace Tests.Compiler.KeccakSpongeStepProbe
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

/-- One step: SKIPPED when a needed constant is missing; else `START`, the
action, `OK (ms) — its line` or `FAILED (ms) — message` with the environment
and the message log put back. Never throws. -/
def runStep (label : String) (needs : List Name) (act : CommandElabM String) :
    CommandElabM Unit := do
  let env0 ← getEnv
  let missing : List Name := needs.filter fun n => !env0.contains n
  unless missing.isEmpty do
    note s!"SPONGE STEP {label}: SKIPPED — not in the environment: {missing}"
    return
  note s!"SPONGE STEP START {label}"
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
    note s!"SPONGE STEP {label}: FAILED ({t1 - t0} ms) — {Tests.Compiler.KeccakSpongeLogLib.clipStr msg}"
  | none =>
    let infos ← (msgs.filter (·.severity == .information)).mapM fun m => m.data.toString
    for i in infos do
      Tests.Compiler.KeccakSpongeLogLib.toFile fallback s!"  | {Tests.Compiler.KeccakSpongeLogLib.clipStr i 3000}"
    let line : String := match res with
      | Except.ok s => s
      | Except.error _ => ""
    let tail : String := if line.isEmpty then "" else " — " ++ line
    note s!"SPONGE STEP {label}: OK ({t1 - t0} ms){tail}"

/-- `#sponge_cmd "n" "what" needs [c, …] in cmd`: a command as a step. -/
elab "#sponge_cmd " step:str ppSpace tag:str " needs " "[" ids:ident,* "]" " in " c:command :
    command => do
  runStep s!"{step.getString} {tag.getString}" (ids.getElems.toList.map fun i => i.getId) do
    elabCommand c
    pure ""

/-- `#sponge_env "n"`: is the generators' progress variable set? -/
elab "#sponge_env " step:str : command => do
  let isSet ← Tests.Compiler.KeccakSpongeLogLib.progressSet
  if isSet then
    note s!"SPONGE STEP {step.getString} SPARKLE_MACHINE_PROGRESS is SET: the generators' own progress lines are in this file, between the probe's lines"
  else
    note s!"SPONGE STEP {step.getString} SPARKLE_MACHINE_PROGRESS is NOT SET: the generators write NO progress line; only the probe's lines exist, in {fallback}. Steps 14–16 then show their START / OK lines only"

/-- `#sponge_read "n" [decl, …]`: the reader's data (logged, nothing asserted). -/
elab "#sponge_read " step:str " [" ids:ident,* "]" : command => do
  for i in ids.getElems do
    let n := i.getId
    runStep s!"{step.getString} read {n}" [n] do
      let r ← liftTermElabM (Tools.ShippingMachineCommand.readMachine n)
      pure (Tests.Compiler.KeccakSpongeLogLib.describeRead r)

/-- `#sponge_fn "n" kind decl depth needs [c, …]`: one function of the depth
generator as a step. `kind`: `candidates` (what `preClose` reads),
`composedRA`, `combNR`, `runOfR`, `coreNR`, `shipsNR`, `designNR`. -/
elab "#sponge_fn " step:str ppSpace kind:ident ppSpace d:ident ppSpace n:num " needs "
    "[" ids:ident,* "]" : command => do
  let decl := d.getId
  let dep : Nat := n.getNat
  let deps : List Name := decl :: (ids.getElems.toList.map fun i => i.getId)
  let k : String := kind.getId.toString
  let label := s!"{step.getString} {k} {decl} {dep}"
  if k == "candidates" then
    runStep label deps <| deep do
      let cands ← Tools.ShippingMachineDepthCommand.closingCandidates decl (← IO.mkRef [])
      let mut out : List String := []
      for c in cands do
        let th ← Tools.ShippingMachineDepthCommand.closingThm? c
        out := out ++ [s!"{c}: closing theorem {th}"]
      pure s!"the descendants with calls, children first (preClose generates a closing for those without one): {out}"
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
    note s!"SPONGE STEP {label}: SKIPPED — unknown kind {k} (a defect of the probe file)"

/-- `#sponge_calls "n" decl depth at [k, …] needs [c, …]`: the call entries
`k` of the per-call loop, in timed pieces. Adds no constant. -/
elab "#sponge_calls " step:str ppSpace d:ident ppSpace n:num " at " "[" ks:num,* "]" " needs "
    "[" ids:ident,* "]" : command => do
  let decl := d.getId
  let dep : Nat := n.getNat
  let kl : List Nat := ks.getElems.toList.map fun x => x.getNat
  let deps : List Name := decl :: (ids.getElems.toList.map fun i => i.getId)
  let savedEnv ← getEnv
  runStep s!"{step.getString} call entries {kl} of {decl} at depth {dep}, in pieces" needs do
    let lines ← deep (callPieces decl dep kl)
    -- nothing of the pieces is kept
    setEnv savedEnv
    pure s!"pieces (ms): {lines.toList}"

/-- `#sponge_summary [c, …]`: which of the named constants exist at the end. -/
elab "#sponge_summary " "[" ids:ident,* "]" : command => do
  let env ← getEnv
  let names : List Name := ids.getElems.toList.map fun i => i.getId
  let present : List Name := names.filter fun n => env.contains n
  let absent : List Name := names.filter fun n => !env.contains n
  note s!"SPONGE STEP END: in the environment {present}; NOT in the environment {absent}. LOG ONLY — nothing here is asserted; a constant present here exists in THIS target-only module and nowhere else"

end Tests.Compiler.KeccakSpongeStepProbe

/-! ## Step 0: the wrapper itself (0a must be FAILED, 0b must be OK), and the variable -/

#sponge_cmd "0a" "self-test of the wrapper (FAILED is the expected line: an unknown constant)"
    needs [Nat] in
  #check keccakSpongeStepNoSuchConstant

#sponge_cmd "0b" "self-test of the wrapper (OK is the expected line)" needs [Nat] in
  #check Nat

#sponge_env "0c"

/-! ## Step 1: the reader's data -/

set_option maxHeartbeats 0 in
#sponge_read "1" [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF]

/-! ## Steps 2–7: the base (the Keccak probe's steps 5–10, all OK there) -/

set_option maxHeartbeats 0 in
#sponge_cmd "2" "keccakRcHW #gate_child" needs [Sparkle.IP.Crypto.Keccak256HW.keccakRcHW] in
  #gate_child Sparkle.IP.Crypto.Keccak256HW.keccakRcHW

set_option maxHeartbeats 0 in
#sponge_cmd "3" "wKeccakF #machine_endpoint" needs [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF] in
  #machine_endpoint Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
#sponge_cmd "4" "wKeccakF #machine_linked"
    needs [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound] in
  #machine_linked Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
#sponge_cmd "5" "wKeccakF #machine_composed"
    needs [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_linked,
      Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_child] in
  #machine_composed Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

set_option maxHeartbeats 0 in
#sponge_cmd "6" "keccak256SpongeHW #machine_endpoint"
    needs [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound] in
  #machine_endpoint Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW

set_option maxHeartbeats 0 in
#sponge_cmd "7" "wKeccakF #machine_closes_at"
    needs [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound,
      Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_child] in
  #machine_closes_at Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF

/-! ## Steps 8–11: what the depth generator does BEFORE the per-call loop -/

set_option maxHeartbeats 0 in
#sponge_fn "8" candidates Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1
  needs [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound]

set_option maxHeartbeats 0 in
#sponge_fn "9" composedRA Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF 0
  needs [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound,
    Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_linked]

set_option maxHeartbeats 0 in
#sponge_fn "10" combNR Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF 0
  needs [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_composedRA]

set_option maxHeartbeats 0 in
#sponge_fn "11" runOfR Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF 0
  needs [Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_composedNRH0]

/-! ## Steps 12–13: the per-call loop's body, ONE entry at a time, in pieces -/

set_option maxHeartbeats 0 in
#sponge_calls "12" Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1 at [0]
  needs [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound,
    Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.seq_child_runN_ofR0,
    Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at]

set_option maxHeartbeats 0 in
#sponge_calls "13" Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1 at [1, 26]
  needs [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound,
    Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.seq_child_runN_ofR0,
    Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at]

/-! ## Steps 14–16: the generator's own functions, in its order

Step 14 is the whole per-call loop (27 entries), `hrunN` and the kernel
check. With the progress variable set the generator writes
`…keccak256SpongeHW: composedNR 1` when it starts and
`…machine_composedNR1: checking` when the term is built and handed to the
kernel: a file ending between the two means the loop / `hrunN`; ending after
`checking`, the kernel. -/

set_option maxHeartbeats 0 in
#sponge_fn "14" coreNR Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1
  needs [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound,
    Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.seq_child_runN_ofR0,
    Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at]

set_option maxHeartbeats 0 in
#sponge_fn "15" shipsNR Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1
  needs [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_composedNR1]

set_option maxHeartbeats 0 in
#sponge_fn "16" designNR Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW 1
  needs [Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_ships_hierNR1]

/-! ## What exists at the end -/

#sponge_summary [Sparkle.IP.Crypto.Keccak256HW.keccakRcHW.gate_child,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_sound,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_closes_at,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_composedRA,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.machine_composedNRH0,
  Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF.seq_child_runN_ofR0,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_sound,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_composedNR1,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_ships_hierNR1,
  Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW.machine_design_svNR1]

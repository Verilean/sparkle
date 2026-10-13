import Tools.ShippingMachineDepthCommandR

/-! # The depth generator with the per-call facts proved once per GROUP (round par/a-27)

WRITTEN, NOT BUILT. `#machine_design_svNRG f n` generates the theorems of
`#machine_design_svNR f n` (`Tools/ShippingMachineDepthCommandR.lean`, which
this file does not change) under the names

    f.machine_composedNRG{n}   f.machine_ships_hierNRG{n}   f.machine_design_svNRG{n}

with the SAME statements: the type of `machine_composedNRG{n}` is computed by
the same code from the same head and the same arguments (the proof of
`hcalls` is the only thing that differs), and the two others are built from
it by the code of `generateShipsNR` and by `compose`.

## What is grouped

An entry of the old loop (`generateCoreNR` 371–476) proves, for call entry
`k` of callee `c` with argument lets `args` and result field `k'`,

    SeqFactsRN … k c  =  memChild? c = none ∧ ∃ args, … = some args ∧
      (b)  (∀ mc, PC c mc → SeqChildRunN … mc (bsC c) (outsC c) (S i c) ∧ (argPorts mc).length = args.length) ∧
      (l)  (∀ q hq, args[q] < nL ∧ ∃ g, lsrc[args[q]]? = some g) ∧
      (r)  (∀ τ, InRange (valsOf lsrc args τ) ((bsC c).filter …)) ∧
      ∃ k' o f, (outsC c)[k']? = some o ∧ o.name = shape.instFields.getD k "" ∧
        (S i c (valsOf lsrc args))[k']? = some f ∧ ∀ τ, posEnc … (kD + k) … = f τ

(`Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN`). The conjuncts `b`, `l`,
`r` mention the callee and the argument list only: NOT `k`, NOT `k'`, NOT the
field. The entry's last equation is proved from two facts about the decoded
input families (`decoded_eq`'s `hb`, `hv`: the decoded Bool / bit-vector
inputs ARE the call's argument Signals) which mention the callee, the
argument lets and the call's argument Signals only. So the five facts are
literally the same propositions for all entries of one GROUP

    key = (callee, argument lets, the two families built from the call's argument Signals)

(the families are compared as terms: two calls of one callee with the same
argument lets but different argument terms are two groups, never one).

Here each group's five facts are proved ONCE, by the old tactics, as terms;
an entry's proof takes them as LOCAL HYPOTHESES (`gfB{g}`, `gfL{g}`,
`gfR{g}`, `gfHb{g}`, `gfHv{g}`) and does only its own part (the skeleton,
`k'`, the three `rfl`s, the final `.trans rfl`). The hypotheses are bound
once around the chain over the entries,

    hcalls = fun i bools bits k c hk => (fun gfB0 … gfHv{G-1} => chain k c hk) pB0 … pHv{G-1}

so the elaborator, `Meta.check` and the kernel each see a group's proof once.

## Differences from the old loop that are NOT only sharing

* **No `case … =>`.** The old tactic closes `b`, `l`, `r`, `f` under `case`,
  which in Lean is `closeUsingOrAdmit`: with error recovery on (the default
  of `Tactic.run`) a failing case is LOGGED and its goal ADMITTED, and the
  generator goes on to the next entry (the theorem is refused only at the
  end, by `addTheorem`'s axiom check, or by the build's error). Here every
  fact is proved by `proveByTacticT` on its own goal and a proof containing
  `sorryAx` is an error at once (`groupFact`, `entryProof`).
* **A second way to prove a family fact** (`extendBools_absorb`,
  `extendBits_absorb`, below): used when the old `repeat' split` tactic does
  not prove it, or alone when `absorb` is set. See the note
  `docs/parallel/A-depth-grouped.md` for why (`split` on the sponge's
  bit-vector family left its goal unsplit in the measured probe).
* `readMachine c` is read once per callee, not once per entry.
* `check hcalls` (old line 495) is replaced by: `Meta.check` of each group
  fact (once), of each entry's proof (the facts are hypotheses there), and of
  the chain (under the hypotheses).

## Restated from `ShippingMachineDepthCommandR.lean` (inline there, not callable)

`generateCoreNRGS` repeats `generateCoreNR` 186–353 (set-up, families,
children's premises, the head and its decides: 168 lines), 355–369, 477–490
(the chain) and 496–559 (`hrunN`, the second chain, the final term: 64
lines) UNCHANGED; the entry's data (379–410) is repeated with the callee's
`readMachine` cached. `generateShipsNRG` repeats `generateShipsNR` 570–627
with the two names as parameters. Everything else is called by import. -/
namespace Tools.ShippingMachineDepthCommand
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine progress listE)
open Tools.ShippingMachineLinkedCommand (addTheorem soundArgs)
open Tools.ShippingMachineSeqCommand
open Tools.ShippingMachineShipsHierCommand (conj projs)

/-! ## The family facts without `split` -/

section Absorb
open Sparkle.Core.Domain Sparkle.Core.Signal

/-- A family that IS `bools`, and is `sig` at `pos`, is `bools` with `sig`
put at `pos`. -/
theorem extendBools_absorb {D : DomainConfig} {X bools : Nat → Signal D Bool} {pos : Nat}
    {sig : Signal D Bool} (hprev : X = bools) (hat : X pos = sig) :
    X = Tools.ShippingMachineCausal.extendBools bools pos sig := by
  subst hprev
  funext j
  unfold Tools.ShippingMachineCausal.extendBools
  by_cases h : j = pos
  · rw [if_pos h]
    subst h
    exact hat
  · rw [if_neg h]

/-- A family that IS `bits`, and is `sig` at `(pos, w)`, is `bits` with `sig`
put at `(pos, w)`. -/
theorem extendBits_absorb {D : DomainConfig}
    {X bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)} {pos w : Nat}
    {sig : Signal D (BitVec w)} (hprev : X = bits) (hat : X pos w = sig) :
    X = Tools.ShippingMachineAuto.extendBits bits pos w sig := by
  subst hprev
  funext j n
  unfold Tools.ShippingMachineAuto.extendBits
  by_cases h : j = pos ∧ n = w
  · rw [dif_pos h]
    obtain ⟨hj, hn⟩ := h
    subst hj
    subst hn
    exact hat.trans (cast_eq _ _).symm
  · rw [dif_neg h]

end Absorb

/-! ## Helpers -/

/-- What the grouped loop did (for the tests' log). -/
structure GroupedStats where
  /-- call entries -/
  entries : Nat := 0
  /-- of them, entries of sequential children (the others are memory reads) -/
  seqEntries : Nat := 0
  /-- groups of sequential entries -/
  groups : Nat := 0
  /-- groups whose Bool family fact was proved by the absorb chain -/
  absorbBools : Nat := 0
  /-- groups whose bit-vector family fact was proved by the absorb chain -/
  absorbBits : Nat := 0
  deriving Inhabited

/-- A group of call entries: the callee, the argument lets, the two families
of the call's argument Signals, and its five facts (statements and proofs,
in the order `b`, `l`, `r`, `hb`, `hv`). -/
structure GroupG where
  c : Name
  argsK : List Nat
  famA : Lean.Expr
  famB : Lean.Expr
  tys : Array Lean.Expr
  prfs : Array Lean.Expr
  absorbBools : Bool
  absorbBits : Bool

/-- A sequential call entry: its group, the child's output it reads, the
child's source at the family index. -/
structure EntryG where
  grp : Nat
  kOut : Nat
  srcE : Lean.Expr

/-- The local hypothesis of fact `j` (`b`, `l`, `r`, `hb`, `hv`) of group `gi`. -/
def gfName (gi j : Nat) : Name :=
  let base : String := match j with
    | 0 => "gfB"
    | 1 => "gfL"
    | 2 => "gfR"
    | 3 => "gfHb"
    | _ => "gfHv"
  Name.mkSimple s!"{base}{gi}"

/-- The last component of a goal's tag. -/
def tagEndG (n : Name) : String :=
  match n.eraseMacroScopes with
  | Name.str _ s => s
  | _ => ""

/-- The goal whose tag ends in `s`. -/
def goalTaggedG (what : String) (gs : List MVarId) (s : String) : MetaM MVarId := do
  let mut tags : List Name := []
  for g in gs do
    let t ← g.getTag
    if tagEndG t == s then return g
    tags := tags ++ [t]
  throwError "{what}: no goal tagged {s} among {tags}"

/-- One tactic on a goal: the goals it leaves. -/
def runTacG (g : MVarId) (tac : Syntax) : MetaM (List MVarId) := do
  let (gs, _) ← (Term.TermElabM.run (Tactic.run g (Tactic.evalTactic tac))) {}
  return gs

/-- A message, cut for a progress line. -/
def clipG (s : String) (n : Nat := 600) : String :=
  if s.length ≤ n then s
  else (s.toList.take n).foldl (fun acc ch => acc.push ch) "" ++ " …[clipped]"

/-- A fact of a group: proved by `tac` on its own goal (no `case`: a failure
is an error here, never an admitted goal), refused if the proof contains
`sorryAx` or a metavariable, then `Meta.check`ed — once. Progress lines
before, after the proof, after the check. -/
def groupFact (label : String) (ty : Lean.Expr) (tac : Syntax) : MetaM Lean.Expr := do
  progress s!"{label}: START"
  let t0 ← IO.monoMsNow
  let pr ← proveByTacticT ty (pure tac)
  if pr.hasSorry then
    throwError "{label}: the proof contains sorry (an error inside the tactic was recovered from)"
  if pr.hasExprMVar then throwError "{label}: the proof has unassigned metavariables"
  let t1 ← IO.monoMsNow
  progress s!"{label}: proved ({t1 - t0} ms)"
  try check pr catch e => throwError "{label}: proof ill-formed: {e.toMessageData}"
  let t2 ← IO.monoMsNow
  progress s!"{label}: Meta.check ({t2 - t1} ms)"
  return pr

/-- A family fact: by the old tactic (`splitTac`), and where that does not
prove it — or at once when `absorb` is set — by the absorb chain
(`chainTac`). Returns the proof and whether the chain was used. -/
def familyFact (absorb : Bool) (label : String) (ty : Lean.Expr) (splitTac chainTac : Syntax) :
    MetaM (Lean.Expr × Bool) := do
  if absorb then
    let pr ← groupFact s!"{label} [absorb chain]" ty chainTac
    return (pr, true)
  let saved ← Meta.saveState
  let first? : Option Lean.Expr ← try
      let pr ← groupFact s!"{label} [split]" ty splitTac
      pure (some pr)
    catch ex =>
      let msg ← ex.toMessageData.toString
      saved.restore
      progress s!"{label} [split]: NOT proved — {clipG msg}; the absorb chain next"
      pure none
  match first? with
  | some pr => return (pr, false)
  | none =>
    let pr ← groupFact s!"{label} [absorb chain]" ty chainTac
    return (pr, true)

/-- Only with `SPARKLE_DEPTH_GROUP_KERNEL` set: a group fact, closed over
`closeOver`, checked by the KERNEL alone (as a theorem that is removed
again), with a progress line for its time. Never throws; adds nothing. -/
def kernelAlone (label : String) (thmName : Name) (closeOver : Array Lean.Expr)
    (ty pr : Lean.Expr) : MetaM Unit := do
  let asked := (← IO.getEnv "SPARKLE_DEPTH_GROUP_KERNEL").isSome
  if asked then
    let saved ← getEnv
    let t0 ← IO.monoMsNow
    try
      let tyC ← instantiateMVars (← mkForallFVars closeOver ty)
      let prC ← instantiateMVars (← mkLambdaFVars closeOver pr)
      if tyC.hasFVar || prC.hasFVar || tyC.hasExprMVar || prC.hasExprMVar then
        progress s!"{label}: kernel alone — not closed over the given binders, not checked"
      else
        progress s!"{label}: kernel alone START"
        addDecl (.thmDecl { name := thmName, levelParams := [], type := tyC, value := prC })
        let t1 ← IO.monoMsNow
        progress s!"{label}: kernel alone OK ({t1 - t0} ms)"
    catch ex =>
      let msg ← ex.toMessageData.toString
      let t1 ← IO.monoMsNow
      progress s!"{label}: kernel alone FAILED ({t1 - t0} ms) — {clipG msg}"
    setEnv saved

/-- **A group's five facts, each proved once.** `goalK` is the goal of the
group's first entry (the statements of `b`, `l`, `r` are read off it after
the old skeleton; `hb`, `hv` are stated as `baseA = A`, `baseB = B`); the tactics are the
old ones (`generateCoreNR` 428–470), without `case`. `baseA`, `baseB` are
the decoded families before the call's arguments are put in. -/
def proveGroup (declName : Name) (absorb : Bool) (gi : Nat) (goalK : Lean.Expr) (c : Name)
    (argsK : List Nat) (isLeaf : Bool) (seqRun : Name) (kOut : Nat)
    (kinds : List MixedGateBinder) (baseA baseB A B idxE srcE : Lean.Expr)
    (closeOver : Array Lean.Expr) : MetaM GroupG := do
  let tag := s!"{declName}: group {gi} ({c}, argument lets {argsK})"
  let tyA ← inferType A
  let tyB ← inferType B
  let tyI ← inferType idxE
  let tyS ← inferType srcE
  let (tys, prfs, usedB, usedV) ← withLetDecl `famA tyA A fun aF => withLetDecl `famB tyB B fun bF =>
    withLetDecl `famI tyI idxE fun iF => withLetDecl `famS tyS srcE fun sF => do
    let back (e : Lean.Expr) : Lean.Expr :=
      e.replaceFVar aF A |>.replaceFVar bF B |>.replaceFVar iF idxE |>.replaceFVar sF srcE
    let lit (n : Nat) := Syntax.mkNumLit (toString n)
    let argsArr : Array Term := (argsK.map fun n => (⟨lit n⟩ : Term)).toArray
    let argsS ← `([$argsArr,*])
    let srcS : Term := ⟨mkIdent `famS⟩
    let idxS : Term := ⟨mkIdent `famI⟩
    let AS : Term := ⟨mkIdent `famA⟩
    let BS : Term := ⟨mkIdent `famB⟩
    let rangeS ← rangeSyntax kinds
    let seqRunS := mkIdent (`_root_ ++ seqRun)
    -- the statements: the old skeleton on the first entry's goal
    -- Only the three STATEMENTS leave this block; the metavariable context is
    -- put back after it. The named holes `?b ?l ?r ?f` stay unassigned here
    -- (their goals are only read), and a named hole is looked up by name in
    -- the whole metavariable context: left there, the NEXT group's skeleton
    -- would find this group's holes, declared under this group's local
    -- definitions ("synthetic hole has already been defined with an
    -- incompatible local context").
    let skel ← `(tactic| (
      right
      unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
      refine ⟨rfl, $argsS, rfl, ?b, ?l, ?r, $(lit kOut), _, _, rfl, rfl, ?f, fun τ => rfl⟩))
    let (tB, tL, tR) ← withoutModifyingState do
      let mv ← mkFreshExprMVar goalK
      let gs ← runTacG mv.mvarId! skel
      let gB ← goalTaggedG tag gs "b"
      let gL ← goalTaggedG tag gs "l"
      let gR ← goalTaggedG tag gs "r"
      let closedTy (g : MVarId) (what : String) : MetaM Lean.Expr := do
        let t ← instantiateMVars (← g.getType)
        if t.hasMVar then throwError "{tag}: the statement of {what} has unassigned metavariables"
        pure t
      let tB ← closedTy gB "b"
      let tL ← closedTy gL "l"
      let tR ← closedTy gR "r"
      pure (tB, tL, tR)
    -- the family facts' statements, on the generator's own decoded families
    -- (`baseA`, `baseB`). They are NOT read off `decoded_eq … ?hb ?hv`: a
    -- child whose source does not read its bit-vector (or Bool) inputs
    -- leaves that family undetermined by the goal (the old tactic's `rfl`
    -- inside the `by` block fixed it; here the hypotheses' types do, in the
    -- entry: `decoded_eq`'s `bools`, `bits` are read off `gfHb`, `gfHv`).
    let _ := (srcS, AS, BS)
    let tHb ← mkEq baseA aF
    let tHv ← mkEq baseB bF
    -- the old tactics
    let caseB ← if isLeaf then
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
    let tacB ← `(tactic| (
      intro mc hmr
      $caseB:tactic))
    let tacL ← `(tactic| (
      exact Tools.ShippingMachineCallsLinkedT.args_facts (by decide)
        (by simp [Tools.ShippingMachineCausal.letObsB, Tools.ShippingMachineCausal.letObsLoop,
          Tools.ShippingMachineCausal.letObsComb])))
    let tacR ← `(tactic| (
      intro τ
      unfold Tools.ShippingMachineChild.InRange
      exact $rangeS))
    let tacHb ← `(tactic| (
      funext p
      try simp (config := { zetaDelta := true }) only [Tools.ShippingMachineCausal.extendBools]
      (repeat' split) <;> (first
        | (rename_i hp; subst hp; exact Tools.ShippingMachineCallsLinkedT.boolsOf_at
            (fun τ => Tools.ShippingMachineCallsLinkedT.decB_valsOf rfl (by decide) rfl τ))
        | rfl)))
    let tacHv ← `(tactic| (
      funext p n
      try simp (config := { zetaDelta := true }) only [Tools.ShippingMachineAuto.extendBits]
      (repeat' split) <;> (first
        | (rename_i hp; obtain ⟨hp1, hp2⟩ := hp; subst hp1; subst hp2; (try simp only [cast_eq]); exact Tools.ShippingMachineCallsLinkedT.bitsOf_at
            (fun τ => Tools.ShippingMachineCallsLinkedT.decV_valsOf rfl (by decide) rfl τ))
        | rfl)))
    -- the absorb chains: one step per Bool / bit-vector input, in the order
    -- the families are built in (innermost first)
    let mut chainA : Term ← `(rfl)
    let mut chainV : Term ← `(rfl)
    for kd in kinds do
      match kd with
      | MixedGateBinder.bool =>
        chainA ← `(Tools.ShippingMachineDepthCommand.extendBools_absorb $chainA
          (Tools.ShippingMachineCallsLinkedT.boolsOf_at
            (fun τ => Tools.ShippingMachineCallsLinkedT.decB_valsOf rfl (by decide) rfl τ)))
      | MixedGateBinder.bits _ =>
        chainV ← `(Tools.ShippingMachineDepthCommand.extendBits_absorb $chainV
          (Tools.ShippingMachineCallsLinkedT.bitsOf_at
            (fun τ => Tools.ShippingMachineCallsLinkedT.decV_valsOf rfl (by decide) rfl τ)))
      | MixedGateBinder.domain => pure ()
    let tacChainA ← `(tactic| exact $chainA)
    let tacChainV ← `(tactic| exact $chainV)
    let pB ← groupFact s!"{tag}: b (the child's run theorem at the instance; argPorts' length)" tB tacB
    let pL ← groupFact s!"{tag}: l (args_facts)" tL tacL
    let pR ← groupFact s!"{tag}: r (InRange)" tR tacR
    -- the family facts, stated on the families themselves (no local
    -- definition in the statement: the chain's unification is structural)
    let (pHb, usedB) ← familyFact absorb s!"{tag}: hb (the Bool family)" (back tHb) tacHb tacChainA
    let (pHv, usedV) ← familyFact absorb s!"{tag}: hv (the bit-vector family)" (back tHv) tacHv tacChainV
    pure (#[back tB, back tL, back tR, back tHb, back tHv],
      #[back pB, back pL, back pR, back pHb, back pHv], usedB, usedV)
  let labels : List String := ["b", "l", "r", "hb", "hv"]
  for j in [0:5] do
    let some ty := tys[j]? | throwError "{tag}: fact {j}"
    let some pr := prfs[j]? | throwError "{tag}: fact {j}"
    kernelAlone s!"{tag}: {labels.getD j ""}"
      (declName ++ Name.mkSimple s!"depthGroupedKernelProbe{gi}x{j}") closeOver ty pr
  return { c := c, argsK := argsK, famA := A, famB := B, tys := tys, prfs := prfs,
           absorbBools := usedB, absorbBits := usedV }

/-- **An entry's proof from its group's facts** (the local hypotheses
`gfB{gi}` … `gfHv{gi}`): the old skeleton with the three facts in place, and
the last equation by `decoded_eq` on the two family facts. -/
def entryProof (label : String) (goalK : Lean.Expr) (gi : Nat) (argsK : List Nat) (kOut : Nat)
    (A B srcE : Lean.Expr) : MetaM Lean.Expr := do
  let tyA ← inferType A
  let tyB ← inferType B
  let tyS ← inferType srcE
  withLetDecl `famA tyA A fun aF => withLetDecl `famB tyB B fun bF =>
    withLetDecl `famS tyS srcE fun sF => do
    let lit (n : Nat) := Syntax.mkNumLit (toString n)
    let argsArr : Array Term := (argsK.map fun n => (⟨lit n⟩ : Term)).toArray
    let argsS ← `([$argsArr,*])
    let srcS : Term := ⟨mkIdent `famS⟩
    let AS : Term := ⟨mkIdent `famA⟩
    let BS : Term := ⟨mkIdent `famB⟩
    let hB : Term := ⟨mkIdent (gfName gi 0)⟩
    let hL : Term := ⟨mkIdent (gfName gi 1)⟩
    let hR : Term := ⟨mkIdent (gfName gi 2)⟩
    let hHb : Term := ⟨mkIdent (gfName gi 3)⟩
    let hHv : Term := ⟨mkIdent (gfName gi 4)⟩
    let tac ← `(tactic| (
      right
      unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
      refine ⟨rfl, $argsS, rfl, $hB, $hL, $hR, $(lit kOut), _, _, rfl, rfl, ?_, fun τ => rfl⟩
      exact (congrArg (fun l => l[$(lit kOut)]?)
        (Tools.ShippingMachineCallsLinkedT.decoded_eq (bools' := $AS) (bits' := $BS) $srcS
          $hHb $hHv)).trans rfl))
    let pr ← proveByTacticT goalK (pure tac)
    if pr.hasSorry then
      throwError "{label}: the proof contains sorry (an error inside the tactic was recovered from)"
    pure (pr.replaceFVar aF A |>.replaceFVar bF B |>.replaceFVar sF srcE)

/-- `newName` as another name of the theorem `thm` (the same statement, the
proof `thm` itself), unless `newName` exists. -/
def aliasOf (newName thm : Name) : MetaM Unit := do
  let env ← getEnv
  unless env.contains newName do
    let ci ← getConstInfo thm
    addTheorem newName ci.type (mkConst thm)
    progress s!"{newName}: added as another name of {thm}"

/-- `declName.machine_composedNRG{dep}`: the statement of
`declName.machine_composedNR{dep}`, the per-call facts proved once per
group. `asOld`: the old name is added too when absent (the same statement,
proved by the new theorem), and children with multi-output calls are
generated by this function first, under both names — so `generateRunOfR`
finds them. `absorb`: the family facts by the absorb chain alone. -/
partial def generateCoreNRGS (declName : Name) (dep : Nat) (asOld absorb : Bool) :
    MetaM (Name × Option GroupedStats) := do
  let name := declName ++ Name.mkSimple s!"machine_composedNRG{dep}"
  let oldName := declName ++ Name.mkSimple s!"machine_composedNR{dep}"
  if (← getEnv).contains name then
    if asOld then aliasOf oldName name
    return (name, none)
  progress s!"{declName}: composedNRG {dep}"
  let r ← readMachine declName
  if r.shape.insts.isEmpty then throwError "{declName}: no call"
  if r.shape.instFields.isEmpty then
    throwError "{declName}: one-output combinational calls (the derived boundary needs the general closing)"
  let (headL, args, back?) ← endpointParts declName
  -- the head carrying `ServedReal` (under `ChildBnd`)
  let pL := mkAppN (mkConst (headL.appendAfter "RA")) args
  let calls := r.shape.insts
  let seqKids := ((calls.map (·.1)).eraseDups.filter fun c =>
    (Tools.ShippingMachineMemCommand.memWidths? c).isNone)
  -- each sequential child's own theorem: without calls at any depth; with
  -- calls, from its composed theorem one level down
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
      -- (grouped) a child with multi-output calls: by this generator first,
      -- under both names, so that `generateRunOfR` finds its composed theorem
      if asOld && !cr.shape.instFields.isEmpty then
        discard <| (try generateCoreNRGS c (dep - 1) asOld absorb catch e => throwError "child {c} (grouped): {e.toMessageData}")
      let (rn, bnd) ← (try generateRunOfR c (dep - 1) catch e => throwError "child {c}: {e.toMessageData}")
      seqRuns := seqRuns.insert c rn
      bndOf := bndOf.insert c bnd
  forallTelescope (← inferType pL) fun xs traceT => do
  let h := mkAppN pL xs
  let tyArgs := (← whnfR traceT).getAppArgs
  unless tyArgs.size == 11 do throwError "{declName}: the trace's arguments"
  let (dE, _mE, dsnE) := (tyArgs[2]!, tyArgs[3]!, tyArgs[4]!)
  -- the run's contexts (the endpoint's binders) and its `ChildBnd` premise
  let hsyn := xs.back!
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
  -- per sequential child: its predicate `PC c` (`MachineRun` without calls,
  -- `MachineRunN` with them), and its premise in the run's contexts — the
  -- reflection facts (no calls), or that every run of its entry satisfies
  -- its depth conditions (with calls)
  let modT := mkConst ``Sparkle.IR.AST.Module
  let desT := mkConst ``Sparkle.IR.AST.Design
  let mut pcCases : List (Name × Lean.Expr) := []
  let mut pTypes : List Lean.Expr := []
  let mut freeOf : Std.HashMap Name Bool := {}
  -- children with calls whose closing is derived: the name premises it asks
  let mut namesOf : Std.HashMap Name (List Lean.Expr) := {}
  for c in seqKids do
    unless leaf.getD c true do
      match ← closesAtNames c ctx with
      | some names => namesOf := namesOf.insert c names
      | none =>
        -- not silently: the endpoint will ASK this child's closing
        logWarning m!"{declName}: the closing of the child {c} stays a premise of this endpoint (MachineClosesAt in the contexts {c} is synthesised in): there is no {c}.machine_closes_at"
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
    -- what the child's declaration is (`MachineDefines`): asked ONCE, in the
    -- run's own contexts — it does not depend on them (`MachineDefines.ctx`).
    -- That its machine synthesis closes, and its own boundary: in the Meta
    -- and Core contexts the child is synthesised in (`ChildRanIn`: its entry
    -- has a run there, over the run's state references)
    let defs0 := mkAppN (mkConst ``Tools.ShippingMachineEntry.MachineDefines) (ctx ++ #[toExpr c, cshape])
    let pT ← withLocalDeclD `mctx' (mkConst ``Lean.Meta.Context) fun mc' =>
      withLocalDeclD `cctx' (mkConst ``Lean.Core.Context) fun cc' => do
      let ctx' := #[mc', ctx[1]!, cc', ctx[3]!]
      let closes := mkAppN (mkConst ``Tools.ShippingMachineEntry.MachineCloses) (ctx' ++ #[toExpr c, cshape])
      -- a child with calls: where the real compile runs its machine synthesis
      -- (`MachineClosesAt`) — not asked when `c.machine_closes_at` derives it
      -- from the child's own boundary (its children's reflection)
      let closesAt := mkAppN (mkConst ``Tools.ShippingChildInv.MachineClosesAt) (ctx' ++ #[toExpr c, cshape])
      let body ← if leaf.getD c true then pure closes
        else do
          -- with calls: its reflection facts and its own derived boundary, in
          -- every start world where the child boundary holds
          -- (`machineRunNC_of_real` derives the rest from the run the compile used)
          let some bnd := bndOf.get? c | throwError "{declName}: boundary of {c}"
          let bndHere ← withLocalDeclD `wc (mkConst ``Void [] |>.app (mkConst ``IO.RealWorld)) fun wc =>
            withLocalDeclD `raw modT fun raw => withLocalDeclD `D desT fun dD => do
            let cb := mkAppN (mkConst ``Tools.ShippingChildInv.ChildBnd) #[ctx[1]!, ctx[3]!, wc]
            mkForallFVars #[wc, raw, dD] (← mkArrow cb (bnd.beta (ctx' ++ #[wc, raw, dD])).headBeta)
          if (namesOf.get? c).isSome then pure bndHere else mkAppM ``And #[closesAt, bndHere]
      let ran := mkAppN (mkConst ``Tools.ShippingChildInv.ChildRanIn) #[ctx[1]!, ctx[3]!, toExpr c, mc', cc']
      mkForallFVars #[mc', cc'] (← mkArrow ran body)
    -- (a leaf child without `let`s closes in every context: proved,
    -- `c.machine_closes`: no call, `let`s that pass `MachineData.letsOk` — only its `MachineDefines` is asked)
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
  let mut p ← mkAppM ``Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN #[mkNatLit dep, h]
  p := mkApp p (← mkDecideProof (← whnf (← inferType p)).bindingDomain!)
  p := mkApp p (mkNatLit r.nDecl)
  for _ in [0:7] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    p := mkApp p (← mkDecideProof ty)
  p := mkApp4 p bsC outsC S PC
  let hcallsT := (← whnf (← inferType p)).bindingDomain!
  -- ===== the grouped per-call loop (the old loop is 354–495) =====
  let statsRef ← IO.mkRef ({} : GroupedStats)
  let hcalls ← forallBoundedTelescope hcallsT (some 3) fun ibb rest => do
    let names := calls.map (·.1)
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
    let goalOf (k : Nat) (c : Name) : Lean.Expr :=
      ((rest.bindingBody!.instantiate1 (mkNatLit k)).bindingBody!.instantiate1 (toExpr c)).bindingBody!
    -- what a group's facts are closed over, for the kernel-alone probe
    let closeOver : Array Lean.Expr := xs ++ hPs ++ ibb
    progress s!"{declName}: grouped loop, {calls.length} call entries"
    -- PHASE 1: the entries' data (old 379–410), their groups, each group's
    -- five facts proved once
    let mut crOf : Std.HashMap Name Tools.ShippingMachineCommand.Read := {}
    let mut ents : Array (Option EntryG) := #[]
    let mut grps : Array GroupG := #[]
    let mut nSeq : Nat := 0
    for k in [0:calls.length] do
      let some (c, argsK, _) := calls[k]? | throwError "{declName}: call {k}"
      if (Tools.ShippingMachineMemCommand.memWidths? c).isSome then
        ents := ents.push none
      else
        nSeq := nSeq + 1
        let cr ← match crOf.get? c with
          | some cr0 => pure cr0
          | none => readMachine c
        crOf := crOf.insert c cr
        let isLeaf : Bool := leaf.getD c true
        let (baseA, baseB, A, B, idxE, srcE, kOut, kinds, seqRun) ← (try do
            let some seqRun := seqRuns.get? c | throwError "{declName}: child {c}"
            let (src0, Dc, idxE) ← srcAt c ibb[0]!
            -- the call: its signal at the call's port, and its arguments
            let pos := r.nDecl + k
            let some sig := (sigAtPos pos extBody).orElse fun _ => sigAtPos pos extBBody
              | throwError "{declName}: call {k}: no signal at port {pos}"
            let some call := findCall c sig | throwError "{declName}: call {k}: no call of {c}"
            let callArgs := call.getAppArgs
            let bsIn : List (Name × MixedGateBinder) := cr.shape.binders.take cr.nDecl
            unless callArgs.size == bsIn.length do
              throwError "{declName}: call {k}: {callArgs.size} arguments, {bsIn.length} binders"
            -- the child's output read by this call
            let field := r.shape.instFields.getD k ""
            let some k' := cr.shape.layout.outs.findIdx? (fun (o : Sparkle.IR.Machine.OutField) => o.name == field)
              | throwError "{declName}: call {k}: field {field}"
            let bsInE0 ← mkAppM ``Tools.ShippingMachineAuto.MachineData.bsIn #[mkConst (c ++ `machineData)]
            let bsInE ← if isLeaf then pure bsInE0
              else mkAppM ``List.take #[mkNatLit cr.nDecl, bsInE0]
            let vs ← mkAppM ``Tools.ShippingMachineCallsLinkedT.valsOf
              #[lsrcE, listE nat (argsK.map mkNatLit)]
            -- the families the decoded inputs are: the call's arguments at their positions
            let baseA ← mkAppOptM ``Tools.ShippingMachineChild.boolsOf #[Dc, bsInE, vs]
            let baseB ← mkAppOptM ``Tools.ShippingMachineChild.bitsOf #[Dc, bsInE, vs]
            let mut A := baseA
            let mut B := baseB
            for (pIdx, bnd) in (List.range bsIn.length).zip bsIn do
              let kind : MixedGateBinder := bnd.2
              if kind == MixedGateBinder.bool then
                A ← mkAppM ``Tools.ShippingMachineCausal.extendBools #[A, mkNatLit pIdx, callArgs[pIdx]!]
              if let .bits w := kind then
                B ← mkAppM ``Tools.ShippingMachineAuto.extendBits
                  #[B, mkNatLit pIdx, mkNatLit w, callArgs[pIdx]!]
            let kinds : List MixedGateBinder := bsIn.map (fun b => b.2)
            pure (baseA, baseB, A, B, idxE, src0, k', kinds, seqRun)
          catch ex => throwError "call {k}: {ex.toMessageData}")
        -- the entry's group: the same callee, argument lets and families
        let mut gi : Nat := grps.size
        match grps.findIdx? (fun g => g.c == c && g.argsK == argsK && g.famA == A && g.famB == B) with
        | some j => gi := j
        | none =>
          progress s!"{declName}: call {k} opens group {gi} ({c}, argument lets {argsK})"
          let g ← (try
              proveGroup declName absorb gi (goalOf k c) c argsK isLeaf seqRun kOut kinds
                baseA baseB A B idxE srcE closeOver
            catch ex => throwError "call {k} (group {gi}): {ex.toMessageData}")
          grps := grps.push g
        ents := ents.push (some { grp := gi, kOut := kOut, srcE := srcE })
    let nAbsA : Nat := (grps.filter fun g => g.absorbBools).size
    let nAbsV : Nat := (grps.filter fun g => g.absorbBits).size
    statsRef.set { entries := calls.length, seqEntries := nSeq, groups := grps.size,
                   absorbBools := nAbsA, absorbBits := nAbsV }
    progress s!"{declName}: {calls.length} call entries ({nSeq} of sequential children) in {grps.size} groups; absorb chain used for the Bool family of {nAbsA}, the bit-vector family of {nAbsV}"
    -- PHASE 2: every entry from its group's facts, as local hypotheses
    let mut gDecls : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) := #[]
    let mut gProofs : Array Lean.Expr := #[]
    for gi in [0:grps.size] do
      let some g := grps[gi]? | throwError "{declName}: group {gi}"
      for j in [0:5] do
        let some ty := g.tys[j]? | throwError "{declName}: group {gi}: fact {j}"
        let some pr := g.prfs[j]? | throwError "{declName}: group {gi}: fact {j}"
        gDecls := gDecls.push ((gfName gi j), (fun (_ : Array Lean.Expr) => pure ty))
        gProofs := gProofs.push pr
    withLocalDeclsD gDecls fun gHyps => do
      let mut perK : Array Lean.Expr := #[]
      for k in [0:calls.length] do
        let some (c, argsK, _) := calls[k]? | throwError "{declName}: call {k}"
        let goalK := goalOf k c
        let t0 ← IO.monoMsNow
        let proofK ← match ents[k]? with
          | some (some e) => (try do
              let some g := grps[e.grp]? | throwError "{declName}: call {k}: group {e.grp}"
              entryProof s!"{declName}: call {k}" goalK e.grp argsK e.kOut g.famA g.famB e.srcE
            catch ex => throwError "call {k}: {ex.toMessageData}")
          | _ => match Tools.ShippingMachineMemCommand.memWidths? c with
            | some (cb, aw, dw) => proveByTacticT goalK (do pure (← memTactic cb aw dw argsK))
            | none => throwError "{declName}: call {k}: neither a memory read nor a grouped entry"
        try check proofK catch e => throwError "call {k} proof ill-formed: {e.toMessageData}"
        let t1 ← IO.monoMsNow
        progress s!"{declName}: call {k} of {c}: proved and checked from its group's facts ({t1 - t0} ms)"
        perK := perK.push proofK
      -- the chain over the call list
      let nameT := mkConst ``Name
      let Qm (m : Nat) : MetaM Lean.Expr :=
        withLocalDeclD `k nat fun kv => withLocalDeclD `c nameT fun cv => do
          let rk := ((rest.bindingBody!.instantiate1 (← mkAdd kv (mkNatLit m))).bindingBody!.instantiate1
            cv).bindingBody!
          mkLambdaFVars #[kv, cv] rk
      let n := names.length
      let mut chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_nil #[nameT, ← Qm n]
      for m' in [0:n] do
        let m := n - 1 - m'
        let rest' := listE nameT ((names.drop (m + 1)).map toExpr)
        chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_cons
          #[nameT, ← Qm m, toExpr names[m]!, rest', perK[m]!, chain]
      try check chain catch e => throwError "the chain over the entries is ill-formed: {e.toMessageData}"
      -- the groups' facts, bound ONCE around the chain
      withLocalDeclD `k nat fun kv => withLocalDeclD `c nameT fun cv => do
        let hkT := ((rest.bindingBody!.instantiate1 kv).bindingBody!.instantiate1 cv).bindingDomain!
        withLocalDeclD `hk hkT fun hk => do
          let body := mkAppN chain #[kv, cv, hk]
          let shared := mkAppN (← mkLambdaFVars gHyps body) gProofs
          mkLambdaFVars (ibb ++ #[kv, cv, hk]) shared
  -- (no `check hcalls` here: each group fact, each entry and the chain were
  -- checked; the kernel checks the theorem)
  progress s!"{declName}: grouped loop done"
  p := mkApp p hcalls
  if back?.isSome then throwError "{declName}: a transported endpoint (not yet at depth)"
  -- `hrunN`, call by call, from the children's premises
  let hrunNT := (← whnf (← inferType p)).bindingDomain!
  let names := calls.map (·.1)
  let mut perR : Array Lean.Expr := #[]
  for k in [0:calls.length] do
    let some (c, _, _) := calls[k]? | throwError "{declName}: call {k}"
    let goalK := ((hrunNT.bindingBody!.instantiate1 (mkNatLit k)).bindingBody!.instantiate1
      (toExpr c)).bindingBody!
    let prK ← match Tools.ShippingMachineMemCommand.memWidths? c with
      | some _ => proveByTacticT goalK `(tactic| (intro h; first | cases h | simp [Sparkle.Compiler.MachMemory.memChild?] at h))
      | none => do
        let some hP := hPOf.get? c | throwError "{declName}: premise {c}"
        let j := seqKids.idxOf c
        let hPS : Term := ⟨mkIdent (Name.mkSimple s!"hP{j}")⟩
        let _ := hP
        if freeOf.getD c false then
          proveByTacticT goalK `(tactic| (intro _ mctx' cctx' mc Dc w w' hw hrun _ _; exact ⟨_, _, _, _, w, w', Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx $hPS, $(mkIdent (`_root_ ++ c ++ `machine_closes)) _ _ _ _⟩))
        else if leaf.getD c true then
          proveByTacticT goalK `(tactic| (intro _ mctx' cctx' mc Dc w w' hw hrun _ _; exact ⟨_, _, _, _, w, w', Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx ($hPS).1, ($hPS).2 mctx' cctx' (Tools.ShippingChildInv.ChildRanIn.of_run hw hrun)⟩))
        else match namesOf.get? c with
          | none =>
            proveByTacticT goalK `(tactic| (intro _ mctx' cctx' mc Dc w w' hw hrun hcons _; exact Tools.ShippingMachineDepthRun.machineRunNC_of_real (Tools.ShippingChildInv.RealChild.of_inv hw hrun) hcons ($hPS).1 (fun mc cc ran => (($hPS).2 mc cc ran).2) (fun mc cc _ _ _ ran _ => (($hPS).2 mc cc ran).1) (by decide)))
          | some names => do
            -- the closing, from the child's boundary: `c.machine_closes_at`
            let some bnd := bndOf.get? c | throwError "{declName}: boundary of {c}"
            let worldT := mkApp (mkConst ``Void []) (mkConst ``IO.RealWorld)
            let hclE ← withLocalDeclD `mc (mkConst ``Lean.Meta.Context) fun mc' =>
              withLocalDeclD `cc (mkConst ``Lean.Core.Context) fun cc' =>
              withLocalDeclD `wc worldT fun wc =>
              withLocalDeclD `raw modT fun raw => withLocalDeclD `D desT fun dD => do
              let ctx' := #[mc', ctx[1]!, cc', ctx[3]!]
              let ran := mkAppN (mkConst ``Tools.ShippingChildInv.ChildRanIn) #[ctx[1]!, ctx[3]!, toExpr c, mc', cc']
              withLocalDeclD `ran ran fun hran =>
              withLocalDeclD `hb (bnd.beta (ctx' ++ #[wc, raw, dD])).headBeta fun hb => do
                let nameHs ← projs (← mkAppM ``And.left #[← mkAppM ``And.right #[hP]]) names
                mkLambdaFVars #[mc', cc', wc, raw, dD, hran, hb] (← closesAtProof c ctx' hb nameHs)
            withLocalDeclD `hclC (← inferType hclE) fun hclV => do
              let pr ← proveByTacticT goalK `(tactic| (intro _ mctx' cctx' mc Dc w w' hw hrun hcons _; exact Tools.ShippingMachineDepthRun.machineRunNC_of_real (Tools.ShippingChildInv.RealChild.of_inv hw hrun) hcons ($hPS).1 (fun mc cc ran => ($hPS).2.2 mc cc ran) $(mkIdent `hclC) (by decide)))
              pure ((← mkLambdaFVars #[hclV] pr).beta #[hclE])
    perR := perR.push prK
  let nameT := mkConst ``Name
  let nat := mkConst ``Nat
  let QmR (m : Nat) : MetaM Lean.Expr :=
    withLocalDeclD `k nat fun kv => withLocalDeclD `c nameT fun cv => do
      let rk := ((hrunNT.bindingBody!.instantiate1 (← mkAdd kv (mkNatLit m))).bindingBody!.instantiate1
        cv).bindingBody!
      mkLambdaFVars #[kv, cv] rk
  let n := names.length
  let mut chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_nil #[nameT, ← QmR n]
  for m' in [0:n] do
    let m := n - 1 - m'
    let rest' := listE nameT ((names.drop (m + 1)).map toExpr)
    chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_cons
      #[nameT, ← QmR m, toExpr names[m]!, rest', perR[m]!, chain]
  p := mkApp p chain
  -- the boundary in the run's contexts: `ChildBnd` and the children's premises, bundled
  let bTypes := (← inferType hsyn) :: pTypes
  let bnd ← conj bTypes
  let value ← withLocalDeclD `hBnd bnd fun hBnd => do
    let ps ← projs hBnd bTypes
    let p' := p.replaceFVars (#[hsyn] ++ hPs) ps.toArray
    mkLambdaFVars (xs.pop ++ #[hBnd]) p'
  progress s!"{name}: checking"
  addTheorem name (← inferType value) value
  progress s!"{name}: checked"
  if asOld then aliasOf oldName name
  return (name, some (← statsRef.get))

/-- `generateCoreNRGS`, the name only. -/
def generateCoreNRG (declName : Name) (dep : Nat) (asOld : Bool := false) (absorb : Bool := false) :
    MetaM Name := do
  return (← generateCoreNRGS declName dep asOld absorb).1

/-- `generateShipsNR` (`ShippingMachineDepthCommandR` 566–630) with the
composed theorem `cN` and the result's `name` as parameters: lines 570–627
unchanged. -/
def generateShipsNRG (declName : Name) (n : Nat) (cN name : Name) : MetaM Name := do
  if (← getEnv).contains name then return name
  let (headL, args, back?) ← endpointParts declName
  if back?.isSome then throwError "{declName}: a transported endpoint (not yet at depth)"
  let soundL := mkAppN (mkConst headL) args
  let cT := mkConst cN
  let data := mkConst (declName ++ `machineData)
  let modT := mkConst ``Sparkle.IR.AST.Module
  let desT := mkConst ``Sparkle.IR.AST.Design
  let nE := mkNatLit n
  forallTelescope (← inferType cT) fun ys _ => do
    unless ys.size == 12 do throwError "{declName}: the composed theorem's binders ({ys.size})"
    let m := ys[6]!
    -- the run boundary in the run's contexts: the composed theorem's last premise
    let Bnd ← mkLambdaFVars #[ys[0]!, ys[1]!, ys[2]!, ys[3]!, ys[4]!, m, ys[7]!] (← inferType ys[11]!)
    let memF ← mkAppM ``Tools.ConeFold.memFree #[← mkAppM ``Sparkle.IR.AST.Module.body #[m]]
    let composed ← withLocalDeclD `hm memF fun hm => do
      let inner ← mkAppM ``Tools.ShippingMachineShipsDepth.composedG_of_NW #[mkAppN cT ys]
      mkLambdaFVars (ys ++ #[hm]) inner
    let KS ← withLocalDeclD `D desT fun D => do
      mkLambdaFVars #[D] (← mkAppM ``Tools.ShippingHierStateG.KSn
        #[← mkAppM ``Tools.ShippingMachineLinked.childMap #[← mkAppM ``Sparkle.IR.AST.Design.modules #[D]], nE])
    let hloc ← withLocalDeclD `D desT fun D => do
      mkLambdaFVars #[D] (← mkAppM ``Tools.ShippingHierStateG.KSn_local
        #[← mkAppM ``Tools.ShippingMachineLinked.childMap #[← mkAppM ``Sparkle.IR.AST.Design.modules #[D]], nE])
    let reset := mkApp (mkConst ``Tools.ShippingMachineShipsDepth.ResetNk) nE
    let (Bd, hBd) ← withLocalDeclD `b modT fun b => withLocalDeclD `D desT fun D => do
      let ms ← mkAppM ``Sparkle.IR.AST.Design.modules #[D]
      let body ← mkAppM ``Sparkle.IR.AST.Module.body #[b]
      let bd ← mkEq (← mkAppM ``Tools.ShippingMachineShipsDepth.kidsMaskedN #[ms, body]) (mkConst ``Bool.true)
      let Bd ← mkLambdaFVars #[b, D] bd
      let hBd ← withLocalDeclD `h bd fun h => do
        mkLambdaFVars #[b, D, h] (mkApp (← mkAppM ``Tools.ShippingMachineShipsDepth.KSn_boundedIn
          #[ms, body, h]) nE)
      pure (Bd, hBd)
    let ktT := mkApp (mkConst ``Tools.ShippingHierStateG.KT) nE
    let inv ← withLocalDeclD `c modT fun c => withLocalDeclD `s ktT fun sv =>
      mkLambdaFVars #[c, sv] (mkConst ``True)
    let hRI ← mkAppM ``Tools.ShippingMachineShipsHier.true_inv #[reset]
    -- the closing premise of the composed theorem (`MachineClosesAt`), and the
    -- wired endpoint from the head asking the same, under the run boundary
    let _ := soundL
    let C ← mkLambdaFVars #[ys[0]!, ys[1]!, ys[2]!, ys[3]!] (← inferType ys[10]!)
    let pLA := mkAppN (mkConst (headL.appendAfter "RA")) args
    let soundA ← forallTelescope (← inferType pLA) fun zs _ => do
      unless zs.size == 12 do throwError "{declName}: the head's binders ({zs.size})"
      let bndT := (Bnd.beta #[zs[0]!, zs[1]!, zs[2]!, zs[3]!, zs[4]!, zs[6]!, zs[7]!]).headBeta
      withLocalDeclD `hB bndT fun hB => do
        let hsynT ← inferType zs[11]!
        let hsyn ← if ← isDefEq bndT hsynT then pure hB else mkAppM ``And.left #[hB]
        let tr ← mkAppM ``Tools.ShippingMachineTraceX.MachineTraceLBX.toLB
          #[(mkAppN pLA zs).replaceFVar zs[11]! hsyn]
        mkLambdaFVars (zs.pop ++ #[hB]) tr
    let thm ← mkAppOptM ``Tools.ShippingMachineShipsHier.machine_ships_hierC
      #[none, KS, hloc, reset, Bnd, C, Bd, inv, hBd, hRI, none, data, none, none, none, none,
        none, none, none, none, none, none, soundA, composed]
    let thm ← instantiateMVars thm
    let ty ← inferType thm
    let .forallE _ hT _ _ ← whnfR ty | throwError "{declName}: the output-width premise"
    let thm := mkApp thm (← mkExpectedTypeHint (← mkDecideProof hT) hT)
    addTheorem name (← inferType thm) thm
    return name

/-- `f.machine_design_svNRG{n}` (and `f.machine_ships_hierNRG{n}`,
`f.machine_composedNRG{n}`): the statements of the `NR` theorems.

* `asOld = false`: only the `G` names are added; the ships theorem by
  `generateShipsNRG`, the design theorem by `compose`.
* `asOld = true`: ALSO the old names, where absent — the downstream commands
  (`#machine_no_ports_kids`, `#machine_closes_at`, the `noShips` / `noKids` /
  `noOuts` generators, `#machine_final_goal`) look `f.machine_ships_hierNR{n}`
  / `f.machine_design_svNR{n}` up BY NAME and read the ships theorem's VALUE
  (`machine_ships_hierC` applied to 25 arguments). So: `machine_composedNR{n}`
  is added as another name of the grouped theorem (nothing reads its value),
  then the OLD `generateDesignNR` builds `machine_ships_hierNR{n}` and
  `machine_design_svNR{n}` from it (their values have the old form), and the
  two `G` names are added as other names of those. Safe: an added name has
  the statement of the theorem it names, by construction. -/
def generateDesignNRG (declName : Name) (n : Nat) (asOld : Bool := false) (absorb : Bool := false) :
    MetaM (Name × Option GroupedStats) := do
  let (cG, st?) ← generateCoreNRGS declName n asOld absorb
  let shipsG := declName ++ Name.mkSimple s!"machine_ships_hierNRG{n}"
  let designG := declName ++ Name.mkSimple s!"machine_design_svNRG{n}"
  if asOld then
    progress s!"{declName}: the old names (generateDesignNR on the grouped composed theorem)"
    let designOld ← generateDesignNR declName n
    let shipsOld := declName ++ Name.mkSimple s!"machine_ships_hierNR{n}"
    aliasOf shipsG shipsOld
    aliasOf designG designOld
  else
    progress s!"{declName}: ships_hierNRG {n}"
    let sG ← generateShipsNRG declName n cG shipsG
    progress s!"{declName}: design_svNRG {n}"
    discard <| Tools.ShippingShipsDesignSVCommand.compose declName sG designG n
  progress s!"{designG}: done"
  return (designG, st?)

/-- The command's body. -/
def designNRGCommand (d : Ident) (n : Nat) (asOld : Bool) : Command.CommandElabM Unit := do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  preClose declName
  let (name, st?) ← Command.liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 })
        (generateDesignNRG declName n asOld false)
  let groupLine : String := match st? with
    | some st => s!"{st.entries} call entries ({st.seqEntries} of sequential children) in {st.groups} groups; the absorb chain proved the Bool family of {st.absorbBools} groups and the bit-vector family of {st.absorbBits}"
    | none => "the composed theorem existed already (no loop run)"
  let oldLine : String :=
    if asOld then "; the old names machine_composedNR / machine_ships_hierNR / machine_design_svNR were added where absent (the same statements)"
    else ""
  logInfo m!"{name}: source → shipped design's closed emitted texts at depth {n}, the instance binding derived (ChildBnd at the run's start world + the children's premises), the per-call facts proved once per group — {groupLine}{oldLine}; checked by the kernel"

/-- `#machine_design_svNRG f n`: the theorems of `#machine_design_svNR f n`
under the names `…NRG{n}`. -/
elab "#machine_design_svNRG " d:ident n:num : command =>
  designNRGCommand d n.getNat false

/-- `#machine_design_svNRG f n as_old`: the same, and the old names
`…NR{n}` where they are absent (for the commands that look them up). -/
elab "#machine_design_svNRG " d:ident n:num " as_old" : command =>
  designNRGCommand d n.getNat true

end Tools.ShippingMachineDepthCommand

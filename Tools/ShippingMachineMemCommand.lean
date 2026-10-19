import Tools.ShippingMachineLinkedCommand
import Tools.ShippingMachineSeqLinked
import Tools.ShippingMachineMemLinked

/-! # Generated composition with memory children

`#machine_composedT f` (after `#machine_endpoint f`, for a hand-written
`Signal.loop` whose calls are all memory reads (combinational or synchronous)) adds
`f.machine_composedT`: the STATEFUL linked run of the emitted module — each
memory instance stepping its own memory module, from zeroed memories and read latches —
seeded with `f`'s own inputs only, shows `f`
(`Tools.ShippingMachineMemLinked.machine_linkedT_mem`). Per call the operand
Signals are read off the call's value (the extension at its port is the
source read, a kernel `rfl`) and the `let`s observe them (kernel `rfl`s). -/
namespace Tools.ShippingMachineMemCommand
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine progress)
open Tools.ShippingMachineLinkedCommand (proveByTactic addTheorem soundArgs)

/-- A memory placeholder's read kind and widths (`SparkleMem.combo.aw.dw`,
`SparkleMem.sync.aw.dw`). -/
def memWidths? (c : Name) : Option (Bool × Nat × Nat) :=
  match c with
  | .num (.num (.str (.str .anonymous "SparkleMem") "combo") aw) dw => some (true, aw, dw)
  | .num (.num (.str (.str .anonymous "SparkleMem") "sync") aw) dw => some (false, aw, dw)
  | _ => none

/-- **The memory parameters of call entry `k` by its stored ORIGIN** (origin-tag
compiler): `some (cb, aw, dw)` exactly for an entry of origin `.mem cb aw dw`,
whatever the callee's NAME (a declaration named as a memory placeholder has
origin `.ord`). A missing tag is an error, never a default. -/
def originMem? (shape : MachineShape) (k : Nat) : MetaM (Option (Bool × Nat × Nat)) := do
  unless shape.instOrigins.length == shape.insts.length do
    throwError "the shape has {shape.instOrigins.length} origins for {shape.insts.length} call entries"
  match shape.instOrigins[k]? with
  | some (.mem cb aw dw) => pure (some (cb, aw, dw))
  | some _ => pure none
  | none => throwError "call entry {k}: no origin tag"

/-- Every call entry has a memory origin (the memory-only route). -/
def allMemOrigins (shape : MachineShape) : MetaM Bool := do
  let mut all := true
  for k in [0:shape.insts.length] do
    if (← originMem? shape k).isNone then all := false
  pure all

/-- The callees of the entries WITHOUT a memory origin (the sequential
children), without repetition, in entry order. -/
def seqCallees (shape : MachineShape) : MetaM (List Name) := do
  let mut out : List Name := []
  for k in [0:shape.insts.length] do
    if (← originMem? shape k).isNone then
      if let some (c, _, _) := shape.insts[k]? then
        unless out.contains c do out := out ++ [c]
  pure out

/-- The tactic for the calls' premise: one case per call. -/
def callsTactic (declName : Name) (insts : List (Name × List Nat × MixedGateBinder)) :
    MetaM Syntax := do
  let mut tac ← `(tactic| exact absurd (hc.symm.trans rfl : some c = none) (by simp))
  for (k, (c, args, _)) in (List.range insts.length).zip insts |>.reverse do
    let hole (s : String) : TSyntax `term := ⟨mkNode ``Lean.Parser.Term.syntheticHole
      #[mkAtom "?", mkIdent (Name.mkSimple s!"{s}{k}")]⟩
    let some (cb, aw, dw) := memWidths? c
      | throwError "{declName}: the call of {c} is not a memory"
    let cbE ← if cb then `(true) else `(false)
    let [l0, l1, l2, l3] := args | throwError "{declName}: a memory call with {args.length} arguments"
    let lit (n : Nat) := Syntax.mkNumLit (toString n)
    let cE := quote c
    let t0 ← `(tactic| (
        have hc' : c = $cE := Option.some.inj (hc.symm.trans rfl);
        subst hc';
        refine ⟨$cbE, $(lit aw), $(lit dw), $(hole "A"), $(hole "D"), $(hole "E"), $(hole "R"),
          $(lit l0), $(lit l1), $(lit l2), $(lit l3),
          rfl, rfl, $(hole "h0_"), by decide, $(hole "h1_"), by decide, $(hole "h2_"), by decide,
          $(hole "h3_"), by decide, rfl, $(hole "hx")⟩;
        case $(mkIdent (Name.mkSimple s!"hx{k}")):ident => (intro j; rfl);
        all_goals rfl))
    tac ← `(tactic| (cases k with | zero => $t0:tactic | succ k => $tac:tactic))
  `(tactic| (intro i bools bits k c hc; $tac:tactic))

def generateCore (declName : Name) : MetaM Name := do
  progress s!"{declName}: composedT"
  let r ← readMachine declName
  if r.shape.insts.isEmpty then throwError "{declName}: no call"
  -- the endpoint's head; a rewritten value (fused loops, sign operations) is
  -- transported back to the declaration (`Eq.mpr` of `congrArg _ heq`)
  let some (.thmInfo ti) := (← getEnv).find? (declName ++ `machine_sound)
    | throwError "{declName}: no machine_sound"
  let mut v := ti.value
  let mut back? : Option (Lean.Expr × Lean.Expr) := none   -- (heq, the rewritten source)
  if v.isAppOfArity ``Eq.mpr 4 then
    let hT := v.getAppArgs[2]!
    unless hT.isAppOfArity ``congrArg 6 do throwError "{declName}: the endpoint's transport"
    let heq := hT.getAppArgs[5]!
    let some (_, _, srcN) := (← inferType heq).eq? | throwError "{declName}: the transport's equation"
    back? := some (heq, srcN)
    v := v.getAppArgs[3]!
  let headL ← if v.isAppOf ``Tools.ShippingMachineCausal.machine_trace_of_loop_causal then
      pure ``Tools.ShippingMachineCausal.machine_traceL_of_loop_causal
    else if v.isAppOf ``Tools.ShippingMachineCausal.machine_trace_of_comb_calls then
      pure ``Tools.ShippingMachineCausal.machine_traceL_of_comb_calls
    else throwError "{declName}.machine_sound is not built from machine_trace_of_loop_causal or machine_trace_of_comb_calls"
  let args := v.getAppArgs
  let pL := mkAppN (mkConst headL) args
  forallTelescope (← inferType pL) fun xs _ => do
  let h := mkAppN pL xs
  let mut p ← mkAppM ``Tools.ShippingMachineMemLinked.machine_linkedT_mem #[h]
  -- `instFields ≠ []`
  p := mkApp p (← mkDecideProof (← whnf (← inferType p)).bindingDomain!)
  p := mkApp p (mkNatLit r.nDecl)
  -- the decidable facts about the data
  for _ in [0:7] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    p := mkApp p (← mkDecideProof ty)
  -- the calls
  let hcallsT := (← whnf (← inferType p)).bindingDomain!
  let hcalls ← proveByTactic hcallsT (← callsTactic declName r.shape.insts)
  p := mkApp p hcalls
  let mut value ← mkLambdaFVars xs p
  if let some (heq, srcN) := back? then
    let T ← inferType value
    let motT ← kabstract T srcN
    unless motT.hasLooseBVars do throwError "{declName}: the theorem does not read the source"
    let hT ← mkCongrArg (.lam `s (← inferType srcN) motT .default) heq
    value ← mkEqMPR hT value
  let name := declName ++ `machine_composedT
  progress s!"{name}: checking"
  addTheorem name (← inferType value) value
  return name

def generate (declName : Name) : MetaM Name := do
  let saved ← getEnv
  try
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) (generateCore declName)
  catch ex =>
    setEnv saved
    throw ex

open Lean.Elab.Command in
elab "#machine_composedT " d:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← liftTermElabM (generate declName)
  logInfo m!"{name}: the stateful linked run of the emitted module, its memories stepping their own memory modules from zero, shows the source, checked by the kernel"

end Tools.ShippingMachineMemCommand

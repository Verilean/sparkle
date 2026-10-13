import Tools.ShippingMachineDepthMemKidCommand

/-! # `#machine_seq_child_memNR f n`: the run theorem of a memory-only kid, and the depth generator's sub-steps one by one (round par/c-3)

WRITTEN, NOT BUILT.

## What failed (measured, round par/c-2)

`#machine_design_svNR memParent 1` after `#machine_composed_memNR memCounterH
0`: "child …memCounterH: No goals to be solved". By reading, the only tactics
the built `generateRunOfR` runs for the kid once its composed theorem exists
are the two extension tactics (`Tools/ShippingMachineDepthCommandR.lean`
527–534). `extBTactic` (`Tools/ShippingMachineDepthCommand.lean` 100–106) is

    intro _ _ _ j hj
    delta f.machineExtB
    simp only [extendBits, extendBools]
    (repeat' split) <;> first | rfl | (exfalso; omega)

A kid whose call entries are all bit-vectors (every memory read is) has
`f.machineExtB := fun i bools bits S => bools`: after `delta` the goal is
`bools j = bools j`, `simp only` CLOSES it, and `t <;> s` is `focus (t;
all_goals s)` — `focus` with no goal left is "No goals to be solved". The
built kids with calls on this path either have a Bool entry (`mid`: the
field `hit` of `cnt`) or no `machineExtB` at all (one-output calls: the
generator's other branch, `intro _ _ _ _ _; rfl`), so the case did not occur.

## The fix, without a built-file edit

`generateRunOfR c n` returns the existing theorem when
`c.seq_child_runN_ofR{n}` is in the environment (523). This command makes it
first: the same term (`seqChildRunN_of_composedC n bnd c.machine_composedNR{n}`,
the ten data premises by `decide`), with the extension premises by

* `intro _ _ _ _ _; rfl` when the Bool extension IS the Bool inputs (read off
  the value of `f.machineExtB`: its body is its second binder) — the built
  generator's own tactic for a kid without `machineExtB`; the built
  `extBTactic` otherwise;
* the built `extTactic` for the bit-vector extension (`intro _ _ _ _ _ _;
  rfl` if it is the inputs themselves).

The branch is taken on a syntactic test of the extension's definition, not
by trying one tactic and falling back to another. Scope: that of
`#machine_composed_memNR` (every callee a memory placeholder).

## The sub-steps of `#machine_design_svNR f n`, one command each

For a probe: each runs ONE of the built generator's steps (after the built
`preClose`, as `#machine_design_svNR` does) and adds what that step adds, so
a later `#machine_design_svNR` finds it.

* `#machine_depth_run_of c n` — the built `generateRunOfR c n`
  (`c.seq_child_runN_ofR{n}`: a kid with calls, from its composed theorem);
* `#machine_depth_core f n` — the built `generateCoreNR f n`
  (`f.machine_composedNR{n}`: the children's run theorems, the grouped
  per-call loop, the child premises);
* `#machine_depth_ships f n` — the built `generateShipsNR f n`
  (`f.machine_ships_hierNR{n}`: `machine_ships_hierC`).

`#machine_design_svNR f n` itself is then only `compose`
(`ships_design_svN_all`). On a failure nothing is added. -/
namespace Tools.ShippingMachineDepthMemKid
open Lean Meta Elab
open Tools.ShippingMachineCommand (readMachine progress)
open Tools.ShippingMachineLinkedCommand (addTheorem)
open Tools.ShippingMachineSeqCommand
open Tools.ShippingMachineDepthCommand (bndOfComposed extTactic extBTactic)

/-- Whether the extension constant `extName` (`fun i bools bits S => …`) is
its binder `idx` itself (1: the Bool inputs, 2: the bit-vector inputs). -/
def extIsBase (extName : Name) (idx : Nat) : MetaM Bool := do
  let some v := (← getEnv).find? extName >>= (·.value?) | return false
  lambdaBoundedTelescope v 4 fun xs body => do
    return xs.size == 4 && body == xs[idx]!

/-- `c.seq_child_runN_ofR{n}` for a kid whose calls are all memory
placeholders (no restore on failure: `generateRun`). -/
def generateRunCore (c : Name) (n : Nat) : MetaM Name := do
  let name := c ++ Name.mkSimple s!"seq_child_runN_ofR{n}"
  if (← getEnv).contains name then return name
  let cT ← generateCore c n
  let bnd ← bndOfComposed cT
  progress s!"{name}: the head"
  let mut p ← mkAppM ``Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC
    #[mkNatLit n, bnd, mkConst cT]
  let mut dataTys : Array Lean.Expr := #[]
  for _ in [0:10] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    dataTys := dataTys.push ty
    p := mkApp p (← mkDecideProof ty)
  -- the Bool extension below the calls
  let tyB := (← whnf (← inferType p)).bindingDomain!
  let hasB := (← getEnv).contains (c ++ `machineExtB)
  let trivB ← extIsBase (c ++ `machineExtB) 1
  progress s!"{name}: hextB (machineExtB present {hasB}, the inputs themselves {trivB})"
  let pfB ← (try
      if !hasB || trivB then
        proveByTacticT tyB `(tactic| (intro _ _ _ _ _; rfl))
      else proveByTacticT tyB (extBTactic (c ++ `machineExtB))
    catch ex => throwError "{c}: hextB (machineExtB present {toString hasB}, the inputs themselves {toString trivB}) is not proved:{indentExpr tyB}\n{ex.toMessageData}")
  if pfB.hasSorry then throwError "{c}: hextB: the proof contains sorry"
  p := mkApp p pfB
  -- the bit-vector extension below the calls
  let tyE := (← whnf (← inferType p)).bindingDomain!
  let hasE := (← getEnv).contains (c ++ `machineExt)
  let trivE ← extIsBase (c ++ `machineExt) 2
  progress s!"{name}: hext (machineExt present {hasE}, the inputs themselves {trivE})"
  let pfE ← (try
      if !hasE || trivE then
        proveByTacticT tyE `(tactic| (intro _ _ _ _ _ _; rfl))
      else proveByTacticT tyE (extTactic (c ++ `machineExt))
    catch ex => throwError "{c}: hext (machineExt present {toString hasE}, the inputs themselves {toString trivE}) is not proved:{indentExpr tyE}\n{ex.toMessageData}")
  if pfE.hasSorry then throwError "{c}: hext: the proof contains sorry"
  p := mkApp p pfE
  progress s!"{name}: checking"
  try
    addTheorem name (← inferType p) p
  catch ex =>
    -- which data premise the kernel may have refused: each one's `decide`,
    -- reduced here (reported only on this failure)
    let mut lines : Array String := #[]
    for j in [0:dataTys.size] do
      let r ← (try
          let dv ← whnf (← mkDecide dataTys[j]!)
          let dvFmt ← ppExpr dv
          pure (if dv.isConstOf ``Bool.true then "true" else s!"NOT true ({dvFmt})")
        catch _ => pure "not reduced")
      lines := lines.push s!"data premise {j}: {r}"
    throwError "{c}: {name} is not checked by the kernel: {ex.toMessageData}\n{String.intercalate "; " lines.toList}"
  progress s!"{name}: checked"
  return name

/-- The options the depth generator runs under; on failure nothing is added. -/
def guarded {α : Type} (x : MetaM α) : MetaM α := do
  let saved ← getEnv
  try
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) x
  catch ex =>
    setEnv saved
    throw ex

/-- `#machine_seq_child_memNR f n`: `f.machine_composedNR{n}` (if absent) and
`f.seq_child_runN_ofR{n}` for a kid whose calls are all memory placeholders —
run it before `#machine_design_svNR` on a parent of `f` at depth `n + 1`. -/
elab "#machine_seq_child_memNR " d:ident n:num : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← Command.liftTermElabM (guarded (generateRunCore declName n.getNat))
  logInfo m!"{name}: a kid whose calls are all memory reads, at depth {n.getNat + 1}, from its composed theorem at depth {n.getNat} (seqChildRunN_of_composedC), checked by the kernel"

/-- `#machine_depth_run_of c n`: the built `generateRunOfR c n` alone. -/
elab "#machine_depth_run_of " d:ident n:num : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let (name, _) ← Command.liftTermElabM
    (guarded (Tools.ShippingMachineDepthCommand.generateRunOfR declName n.getNat))
  logInfo m!"{name}: the built generateRunOfR at depth {n.getNat}"

/-- `#machine_depth_core f n`: the built `preClose` and `generateCoreNR f n`
alone (`f.machine_composedNR{n}`). -/
elab "#machine_depth_core " d:ident n:num : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  Tools.ShippingMachineDepthCommand.preClose declName
  let name ← Command.liftTermElabM
    (guarded (Tools.ShippingMachineDepthCommand.generateCoreNR declName n.getNat))
  logInfo m!"{name}: the built generateCoreNR at depth {n.getNat}"

/-- `#machine_depth_ships f n`: the built `preClose` and `generateShipsNR f n`
alone (`f.machine_ships_hierNR{n}`). -/
elab "#machine_depth_ships " d:ident n:num : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  Tools.ShippingMachineDepthCommand.preClose declName
  let name ← Command.liftTermElabM
    (guarded (Tools.ShippingMachineDepthCommand.generateShipsNR declName n.getNat))
  logInfo m!"{name}: the built generateShipsNR at depth {n.getNat}"

end Tools.ShippingMachineDepthMemKid

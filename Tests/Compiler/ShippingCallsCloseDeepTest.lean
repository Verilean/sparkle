import Tests.Compiler.ShippingCallsCloseTest
import Tools.ShippingChildIfaceGen

/-! Closings over children that have calls of their own (B3), split from
`ShippingCallsCloseTest` so that neither test process holds all the
kernel-decided name-separation proofs at once (the single file peaked at
2.18 GiB of the 3 GiB cap). -/
open Lean Meta

/-! ## Children with calls of their own (B3)

`grand → mid → cnt`, `grandH → midH → rcH`, `mixD1 → {midH → rcH, cnt}`,
`topD2 → mid2 → midH → rcH`: the parent is closed by the general closing over
a child that has calls. `#machine_closes_deep` derives the parent's
`MachineClosesAt` (`machineClosesAt_of_kidsD`), each child with calls read by
its interface from its own run (`kidsChild_of_real`: ports, the design as the
join of its children, the post-passes), and closes the depth endpoints.
Premises: every descendant's reflection, and name separation per node (N1,
obligations). What is left, recorded exactly: `topD2`'s depth endpoint still
asks the closing of `mid2` in the contexts `mid2` is synthesised in — that
closing needs the reflection of `rcH` (a grandchild of `mid2`) there, which
the child's boundary does not carry. -/

set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand 2
set_option maxHeartbeats 0 in
#machine_closes_deep Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand
set_option maxHeartbeats 0 in
#machine_closes_deep Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH
set_option maxHeartbeats 0 in
#machine_closes_deep Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1
set_option maxHeartbeats 0 in
#machine_closes_deep Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2

/-- The declarations whose `MachineClosesAt` the statement of `thm` mentions
(anywhere), among `cands`. -/
def closingsLeft (thm : Name) (cands : List Name) : MetaM (List Name) := do
  let info ← getConstInfo thm
  let mut out : List Name := []
  -- every application of `MachineClosesAt` in the statement
  let rec go (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
    let acc := if e.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 then acc.push (e.getArg! 4)
      else acc
    match e with
    | .app f a => go a (go f acc)
    | .lam _ t b _ => go b (go t acc)
    | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ b => go b acc
    | _ => acc
  for a in go info.type #[] do
    let mut hit := false
    for c in cands do
      if !hit && (← isDefEq a (toExpr c)) then
        hit := true
        unless out.contains c do out := out ++ [c]
    unless hit do throwError "{thm}: a closing of an unlisted declaration: {a}"
  return out

run_cmd Lean.Elab.Command.liftTermElabM do
  let cands := [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand,
    ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid,
    ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH,
    ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH,
    ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1,
    ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2,
    ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2]
  let std (e : Name) : MetaM Unit := do
    let axs ← Lean.collectAxioms e
    if axs.any fun a => !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound) then
      throwError "{e} depends on a non-standard axiom: {axs}"
  let mut report : Array MessageData := #[]
  for (f, ns, want) in
      [(``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand, [2], ([] : List Name)),
       (``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH, [1, 2], []),
       (``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1, [1, 2], []),
       (``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2, [2, 3],
         [``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2])] do
    std (f ++ `closes_deep)
    unless (← closingsLeft (f ++ `closes_deep) cands) == [f] do
      throwError "{f}.closes_deep: its statement asks a closing"
    for n in ns do
      let o := f ++ Name.mkSimple s!"machine_design_svNR{n}"
      let e := Tools.ShippingMachineClosesGen.closedName o
      std e
      -- the open endpoint asks the parent's closing; the closed one does not
      unless (← closingsLeft o cands).contains f do
        throwError "{o}: the open endpoint does not ask {f}'s closing"
      let left ← closingsLeft e cands
      unless left == want do
        throwError "{e}: closings left {left}, expected {want}"
      lawAudit e
      report := report.push m!"{e}: closings left {left}"
    unless ← namesHold f do throwError "{f}: a name condition is false"
  Lean.logInfo m!"CHILDREN WITH CALLS (B3): {report} — MachineClosesAt derived through a child with calls; premises: the descendants' reflection and name separation per node; standard axioms"

-- Every premise of the deep closings is a descendant's reflection: the name
-- separation over the descendants is PROVED (`Tools.ShippingNameSep`).
run_cmd Lean.Elab.Command.liftTermElabM do
  for (f, nRefl) in [(``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand, 2),
      (``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH, 2),
      (``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1, 3),
      (``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2, 3)] do
    let hyps ← premises (f ++ `closes_deep)
    for h in hyps do
      unless h.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines ||
          h.isAppOf ``Tools.ShippingMachineEntry.MachineDefines do
        throwError "{f}.closes_deep: a premise that is not a reflection: {h}"
    unless hyps.size == nRefl do throwError "{f}.closes_deep: {hyps.size} premises"
  Lean.logInfo m!"DEEP CLOSINGS: grand, grandH, mixD1, topD2 — the only premises are the descendants' reflections (2, 2, 3, 3); name separation over the descendants proved from the candidate renderings"

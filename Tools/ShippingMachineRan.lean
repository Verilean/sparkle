import Tools.ShippingCacheCoherentOuter
import Tools.ShippingKidsSelf
import Tools.ShippingMachineRanBase

variable {tenv : Lean.Environment}

/-! # `MachineRan`: what every design-level consumer takes of the closing, stated for ONE run

BUILT as of par/a-43 (docs/parallel/A-outermost-form.md, the integrator's
record). EDITED in round par/g-1 (WRITTEN, NOT BUILT), statements unchanged:
`MachineRan` and `machineRan_of_closes` MOVED to
`Tools/ShippingMachineRanBase.lean` (same full names), and
`core_kids_self_ran` is now the split lemma of `Tools/ShippingKidsSelf.lean`
instead of a copy of its tail. The section "Do the built proofs factor through
it?" below describes the state BEFORE that round: the thirteen tails are no
longer inline (docs/parallel/G-mixdeep-outermost.md).

## What the consumers do with `closes` (read line by line)

The design-level chain of a parent with calls
(`Tools/ShippingKidFacts.lean`: `kids_runFacts`, `kids_outsCheck`,
`kids_maskedN`, `kids_designCheck`, and the general theorems below them)
carries `closes : MachineClosesAt mctx mref cctx cref c d.shape` and only
threads it down. It is USED in thirteen base lemmas, each time by the same
three lines at the start of the proof:

    obtain ⟨_, bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ := machine_run_of_core hcore entry hB
    have hne := closes bb _ _ _ hw9 hd9 hrun9
    cases r with | none => exact absurd rfl hne | some res => …

after which the proof (its TAIL) works from the machine synthesis's run with
result `some (M, D)` and the invariant of its start world — and never
mentions `closes`, `hcore`, `entry` or `hB` again in the lemmas read
(`core_kids_self`, `seqChild_iface`).

So what a consumer takes of the closing is exactly **`MachineRan`**: the
machine synthesis this core run performs returned the run's result, from an
invariant world of positive depth.

* `machineRan_of_closes`: `MachineRan` from the all-worlds premise — the
  three lines, once. The BUILT forms are this instance.
* `machineRan_outermost`: `MachineRan` for a core run that starts at depth 0
  (`Start0`), from a closing at `Prov` worlds only — `coreVia0_of`, BUILT.
  This is the "consumed" end of the provenance chain.
* `Start0`: the depth-0 start condition, and `Start0.childBnd`: it is
  `ChildBnd` with its depth-0 disjunct chosen.

## Do the built proofs factor through it? NO.

The tails are INLINE in the thirteen base lemmas; none is a lemma about
`MachineRan`. A common generalisation therefore cannot be obtained without
either splitting those proofs in the built files (each into a tail over
`MachineRan` and a two-line corollary with the present statement) or copying
the tails. Neither is done here beyond ONE worked example:

* `core_kids_self_ran`: the tail of `Tools.ShippingKidsSelf.core_kids_self`,
  verbatim, over `MachineRan`;
* `core_kids_self_of_closes`: the BUILT statement of `core_kids_self`,
  re-derived as its instance.

The list of the thirteen, their sizes, and what an endpoint at outermost
starts needs: `docs/parallel/A-outermost-form.md`. -/
namespace Tools.ShippingMachineRan
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingCacheCoherentRun (Prov)

/-- **The depth-0 start condition**: for ONE law witness, the synthesis ref
is set, the synthesis depth reads 0, and the world is quiet. -/
def Start0 (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) : Prop :=
  ∃ L : RefLaws mref cref, L.sval w = some synthesizeChild ∧ L.dval w = 0 ∧ L.quiet w

-- `MachineRan` (the machine synthesis a core run performs returned the run's
-- result, from an invariant world of positive depth) and `machineRan_of_closes`
-- (from the all-worlds closing) are in `Tools/ShippingMachineRanBase.lean` since
-- round par/g-1: same names, same namespace, same statements. They were MOVED
-- so that the base lemmas below `Tools.ShippingKidsSelf` can use them.

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The depth-0 start is `ChildBnd` with its depth-0 disjunct chosen. -/
theorem Start0.childBnd {w : Void IO.RealWorld} (h : Start0 mref cref w) :
    ChildBnd mref cref w := by
  obtain ⟨L, hs, hd, hq⟩ := h
  exact ⟨L, ⟨hs, Or.inl hd⟩, hq⟩

/-- **`MachineRan` at an OUTERMOST start**, from a closing at `Prov` worlds
only (`hclose`: what the provenance chain proves of a parent,
`Tools.ShippingCacheCoherentCert.machine_closes_of_entryOk`). No
`MachineClosesAt`. -/
theorem machineRan_outermost {c : Name} {shape : MachineShape}
    {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c shape)
    (h0 : Start0 mref cref w)
    (hclose : ∀ {tenv : Lean.Environment} (L : RefLaws mref cref) (b : Bool)
      (w9 : Void IO.RealWorld) (r : Option Res)
      (w10 : Void IO.RealWorld), InvV L w9 → L.dval w9 ≠ 0 → Prov (L.val w9) →
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape)
        mctx mref cctx cref w9 r w10 → r ≠ none) :
    MachineRan mctx mref cctx cref c shape M D := by
  obtain ⟨L, hs, hd0, hq⟩ := h0
  obtain ⟨_, b, w9, w10, hrun, hw9, hd9, -⟩ :=
    Tools.ShippingCacheCoherentOuter.coreVia0_of L (fun L' => bodyRel L')
      (fun L' => harnessRel_of L' (translateRel L')) entry (hclose L) hs hq hd0 hcore
  exact ⟨_, b, w9, w10, hrun, invW_of_invV L hw9, depthPos_of L hd9⟩

/-! ## One worked example: `core_kids_self` -/

/-- **`core_kids_self` over `MachineRan`**: the design of a core run on a
machine with calls resolves its real children's modules, and the modules of
their designs, to themselves. Since round par/g-1 the tail itself is
`Tools.ShippingKidsSelf.core_kids_self_ran` (the split of the built lemma, in
its own file); this theorem keeps its name and statement and is that one. -/
theorem core_kids_self_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {M : Sparkle.IR.AST.Module} {D : Design}
    (ran : MachineRan mctx mref cctx cref c d.shape M D) :
    ∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
      moduleByName D.modules y.1.name = some y.1 ∧
      ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2 :=
  Tools.ShippingKidsSelf.core_kids_self_ran d ok hbody hC hslots hdomB hins hnomem ran

/-- The BUILT statement of `Tools.ShippingKidsSelf.core_kids_self`, as the
instance of `core_kids_self_ran` at the all-worlds closing. -/
theorem core_kids_self_of_closes {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
      moduleByName D.modules y.1.name = some y.1 ∧
      ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2 :=
  core_kids_self_ran d ok hbody hC hslots hdomB hins hnomem
    (machineRan_of_closes hcore entry hB closes)

end Tools.ShippingMachineRan

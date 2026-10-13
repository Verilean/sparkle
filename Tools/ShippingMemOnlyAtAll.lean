import Tools.ShippingClosesSplit

variable {tenv : Lean.Environment}

/-! # The all-worlds closing `MachineCloses` of a shape with calls: its counter-world (G1, unit U4, round par/b-15)

DECISION RECORDED HERE (by reading; this file states the reason as a theorem).

`MachineCloses mctx mref cctx cref f shape`
(`Tools/ShippingMachineEntry.lean` 2279–2284) quantifies over EVERY world and
every logger. For a shape with calls the machine synthesis ends in
`closeInstsM` / `closeInstsGM` (`Sparkle/Compiler/Elab.lean` 5189–5221,
5228–5242), and BOTH begin with

    let some synth ← sparkleChildSynth.get | return none

(5192, 5209) — BEFORE the children are looked at. A memory entry's child is
built with `pure md` (5211–5213) and reads neither the child cache nor
`synth`, but the read of the synthesis reference above it is unconditional:
a memory-ONLY shape returns `none` exactly like any other shape with calls
when that reference holds `none`. So for a memory-only parent the only
world-dependent state the closing reads is this one reference, and it is
enough: the all-worlds closing is contradicted by ONE successful run of the
harness that ends in a world where the reference reads `none`
(`not_machineCloses_of_synthNone` below).

What is NOT proved here, and cannot be from what exists: that such a run
EXISTS (`¬ MachineCloses` outright). The model has no existence statement for
runs of `synthesizeMixedCertified` (only `refGet_runs` / `refSet_runs` /
`refModify_runs` for single reference operations,
`Tools/ShippingChildInv.lean` 616–640), and the worlds are opaque. In the
running compiler such worlds exist: the reference is created holding `none`
(`initialize sparkleChildSynth … ← IO.mkRef none`, Elab 1037–1039) and is set
only by a later initializer (8850), and any `sparkleChildSynth.set none`
gives one. Conversely `MachineCloses` of a shape with calls is not PROVABLE
from the runtime laws: it would need `L.sval w1 = some _` of every world,
which no law gives (`RefLaws.synthGet`, `ShippingChildInv` 398–399, only
says a read returns `sval`).

So: a premise `MachineCloses f` of a memory-only parent (`f.machine_design_sv0`,
`f.machine_design_noPorts0`) can only be ASSUMED, never discharged, and it is
false of the real runtime; the statement a real compile supports is
`MachineClosesAt` (`Tools/ShippingChildRun.lean` 444–449: invariant worlds,
where `SynthAt` makes the read return `synthesizeChild`).

Nothing here is a closing theorem. No copy of a built proof.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingMemOnlyAtAll
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingClosesSplit

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The general closing returns nothing from a world where the child
synthesis reference reads `none` — whatever the calls are (memory entries
included: the read comes first). -/
theorem closeInstsGM_none_of_synthNone {shape : MachineShape} {t m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w1 : Void IO.RealWorld}
    (hget : RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w none w1) :
    RunsTo (closeInstsGM shape t m d) mctx mref cctx cref w none w1 := by
  unfold closeInstsGM
  refine Tools.ShippingReflectCtx.RunsTo.bind_intro hget ?_
  first
    | rfl
    | (dsimp only; rfl)

/-- The one-output closing likewise. -/
theorem closeInstsM_none_of_synthNone {shape : MachineShape} {t m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w1 : Void IO.RealWorld}
    (hget : RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w none w1) :
    RunsTo (closeInstsM shape t m d) mctx mref cctx cref w none w1 := by
  unfold closeInstsM
  refine Tools.ShippingReflectCtx.RunsTo.bind_intro hget ?_
  first
    | rfl
    | (dsimp only; rfl)

/-- The calls' closing, as the machine synthesis runs it, returns nothing
from such a world. -/
theorem closeCalls_none_of_synthNone {shape : MachineShape} {t t' : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w1 : Void IO.RealWorld}
    (hget : RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w none w1) :
    RunsTo (closeCalls shape t t' d) mctx mref cctx cref w none w1 := by
  unfold closeCalls
  split
  · exact closeInstsM_none_of_synthNone hget
  · exact closeInstsGM_none_of_synthNone hget

/-- **The counter-world of the all-worlds closing.** For a shape with calls
— memory-only shapes included — ONE successful run of the harness whose
transition `closeLets` accepts and whose end world reads no child synthesis
contradicts `MachineCloses`. -/
theorem not_machineCloses_of_synthNone {declName : Name} {shape : MachineShape}
    (hi : shape.insts ≠ [])
    {logProf : String → IO Unit} {w w1 w2 : Void IO.RealWorld}
    {t t' : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named)
      logProf declName shape.binders shape.body) mctx mref cctx cref w (t, d) w1)
    (hcl : closeLets shape.layout.lets t = some t')
    (hget : RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w1 none w2) :
    ¬ MachineCloses mctx mref cctx cref declName shape := by
  intro hc
  exact (machineCloses_iff.mp hc).2 hi logProf w t d w1 t' hr hcl none w2
    (closeCalls_none_of_synthNone hget) rfl

end Tools.ShippingMemOnlyAtAll

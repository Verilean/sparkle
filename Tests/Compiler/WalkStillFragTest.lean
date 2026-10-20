import Tests.Compiler.ChecksRawTest
import Tests.Compiler.NoPortsGrandHTest
import Tools.ShippingWalkStill

variable {tenv : Lean.Environment}

/-! # The walk's fragment on two built machine transitions: `cnt` (a leaf) and `midH`

WRITTEN, NOT BUILT (par/a-36). Target-only; not in `Tests.AllTests`.

`Tools.ShippingWalkStill.walk_still` covers the constructors of `wfrag`. A
machine's transition body is `quote … d.packed` (`machine_body`); whether
`d.packed` is in the fragment is a `Bool` on reflected data. This file

1. LOGS the two Booleans first (standard error, flushed, and the message
   log) — evaluated by the compiler, so the line appears whatever the value:

       WALKFRAG START <decl>
       WALKFRAG <decl>: wfrag packed = <true/false>

2. then PROVES them (`decide`) and instantiates the walk: `cnt_walk`,
   `midH_walk` — a returning run of the shipping translator on the quoted
   packed term, in a context that binds the input binders, leaves the child
   cache. If a Boolean is `false` the corresponding theorem does not
   compile, and line 1 says which: the packed term then uses a constructor
   outside the fragment (candidates by reading: a Bool output packed through
   a constructor not listed in `wfrag`), and the fragment has to grow.

PREDICTED: both `true` (the bodies use inputs, `bitsLit`, `binary`,
`compare`, `mux`; the packing uses `concat` — and, NOT certain, nothing
else). `cnt_walk` is NOT `EntryStill cnt`: the harness shell is missing. -/
namespace Tests.Compiler.WalkStillFragTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.Tests.Compiler.ShippingMachineDepthHTest
open Tools.ShippingWalkStill
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning

-- The two Booleans are decided by the KERNEL (the compiled evaluation of
-- `wfrag … .packed` in a `run_cmd` crashed Lean's code generator: "unknown
-- join point", ExplicitBoxing panic — integrator, 2026-10-13).
example : wfrag cnt.machineData.packed = true := by decide
example : wfrag midH.machineData.packed = true := by decide
run_cmd Lean.logInfo m!"WALKFRAG cnt, midH: wfrag packed = true (kernel decide, the two examples above)"

theorem cnt_frag : wfrag cnt.machineData.packed = true := by
  first | decide | decide +kernel

theorem cnt_wf : cnt.machineData.packed.WF cnt.machineData.kb cnt.machineData.kv
    cnt.machineData.vw := by
  first | decide | decide +kernel

theorem midH_frag : wfrag midH.machineData.packed = true := by
  first | decide | decide +kernel

theorem midH_wf : midH.machineData.packed.WF midH.machineData.kb midH.machineData.kv
    midH.machineData.vw := by
  first | decide | decide +kernel

/-- The walk on `cnt`'s transition leaves the child cache. -/
theorem cnt_walk {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Tools.ShippingChildInv.RefLaws mref cref)
    {mb : Std.HashMap Lean.Name Tools.ShippingChildInv.Res}
    {ctx : Sparkle.Compiler.Elab.CompilerState} {dom : Lean.Expr} {bi vi : Nat → Lean.FVarId}
    (hb : ∀ j, j < cnt.machineData.kb → WBound ctx (bi j))
    (hv : ∀ j, j < cnt.machineData.kv → WBound ctx (vi j)) :
    WCh mctx cctx L mb ctx
      (fun e hint top named => Sparkle.Compiler.Elab.translateExprToWire tenv e hint top named)
      (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) cnt.machineData.packed) :=
  walk_still L hb hv _ cnt_wf cnt_frag

/-- The walk on `midH`'s transition leaves the child cache. -/
theorem midH_walk {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Tools.ShippingChildInv.RefLaws mref cref)
    {mb : Std.HashMap Lean.Name Tools.ShippingChildInv.Res}
    {ctx : Sparkle.Compiler.Elab.CompilerState} {dom : Lean.Expr} {bi vi : Nat → Lean.FVarId}
    (hb : ∀ j, j < midH.machineData.kb → WBound ctx (bi j))
    (hv : ∀ j, j < midH.machineData.kv → WBound ctx (vi j)) :
    WCh mctx cctx L mb ctx
      (fun e hint top named => Sparkle.Compiler.Elab.translateExprToWire tenv e hint top named)
      (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) midH.machineData.packed) :=
  walk_still L hb hv _ midH_wf midH_frag

#print axioms cnt_walk
#print axioms midH_walk

end Tests.Compiler.WalkStillFragTest

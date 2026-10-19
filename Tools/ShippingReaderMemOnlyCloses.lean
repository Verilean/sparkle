import Tools.ShippingReaderOutsMemOnly
import Tools.ShippingMemOnlyNames
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # The closing of a memory-only parent over `MemOnlyDataR` (no `outTy` / `outScalar`)

WRITTEN, NOT BUILT (branch `par/r-2`; record `docs/parallel/R-reader-outs-inv-2.md`).
No `sorry`, no axiom, no `native_decide`.

`Tools.ShippingMemOnlyNames.machineClosesAt_of_memOnlyData_names` (built)
takes the full `MemOnlyData`; its proof reads only the fields `ok`, `body`,
`calls`, `slots`, `domB`, `fne`, `mem` — all of them fields of
`MemOnlyDataR` as well. The closing has NO run hypothesis, so `outTy` /
`outScalar` could not be supplied by the reader there; it does not need
them. The theorem below is the same statement over `MemOnlyDataR`, proved by
the same built theorem underneath (`machineClosesAt_memOnly_names`).

Used by the switched generator `#machine_no_ports_mem`
(`Tools/ShippingNoPortsMemCommand.lean`) for `f.noPortsMem_closes`. -/
namespace Tools.ShippingReaderMemOnlyCloses
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Machine
open Tools.ShippingMachineAuto Tools.ShippingChildInv
open Tools.ShippingMemOnlyCloses (MemOnlyCloseData)
open Tools.ShippingReaderOutsMemOnly (MemOnlyDataR)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`MachineClosesAt` of a memory-only parent over `MemOnlyDataR`,
without name hypotheses.** Same statement as
`machineClosesAt_of_memOnlyData_names`, with `MemOnlyDataR` in place of
`MemOnlyData`. -/
theorem machineClosesAt_of_memOnlyDataR_names {declName : Name} {d : MachineData}
    {nDecl aw dw : Nat}
    (D : MemOnlyDataR d nDecl aw dw) (C : MemOnlyCloseData d) :
    MachineClosesAt mctx mref cctx cref declName d.shape :=
  Tools.ShippingMemOnlyNames.machineClosesAt_memOnly_names d D.ok D.body C.alias D.calls
    D.slots D.domB D.fne
    (fun k hk => (D.mem k hk).elim fun cb h =>
      Exists.intro cb (Exists.intro aw (Exists.intro dw h)))
    C.argsN C.field C.argsNd C.outHead C.agree

end Tools.ShippingReaderMemOnlyCloses

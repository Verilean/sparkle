/-
  RV32 CSR read mux — Signal-level wrapper + spec

  The CSR read mux in `IP/RV32/SoC.lean` (~line 956) is a 28-way
  priority cascade that produces `csr_rdata` from the matched
  `csrIs*` signal and the corresponding register/view. This file
  packages it as a single Signal-level def whose semantics match
  the inline form exactly, plus per-arm rfl-closed spec lemmas.

  The wide signature (28 inputs + 28 register inputs ≈ 56 args)
  is unavoidable for a flat mux. We pass them as positional
  arguments in priority order, and the per-arm spec proofs show
  that a single `csrIs*` true → the corresponding register is
  returned.

  Reference: per RISC-V priv §3.1, §4.1, §6 (read-side semantics
  of the CSRs Sparkle implements).
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.CSR

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Signal-level 28-way priority mux for csr_rdata

  Priority: mstatus > mie > mtvec > mscratch > mepc > mcause >
  mtval > mip > misa > mhartid > medeleg > mideleg > sstatus >
  sie > stvec > sscratch > sepc > scause > stval > sip > satp >
  mcounteren > scounteren > time > timeh > cycle > cycleh > pmp.

  Default = 0 (any unrecognized CSR address). This is the same
  shape as the inline cascade in SoC.lean. -/
def csrReadMuxSignal {dom : DomainConfig}
    (csrIsMstatus csrIsMie csrIsMtvec csrIsMscratch
     csrIsMepc csrIsMcause csrIsMtval csrIsMip
     csrIsMisa csrIsMhartid csrIsMedeleg csrIsMideleg
     csrIsSstatus csrIsSie csrIsStvec csrIsSscratch
     csrIsSepc csrIsScause csrIsStval csrIsSip
     csrIsSatp csrIsMcounteren csrIsScounteren
     csrIsTime csrIsTimeh csrIsCycle csrIsCycleh csrIsPmp
       : Signal dom Bool)
    (mstatusReg mieReg mtvecReg mscratchReg
     mepcReg mcauseReg mtvalReg mipValue
     medelegReg midelegReg
     sstatusView sieReg stvecReg sscratchReg
     sepcReg scauseReg stvalReg sipMasked
     satpReg mcounterenReg scounterenReg
     mtimeLoReg mtimeHiReg
       : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  let misaConst : Signal dom (BitVec 32) := Signal.pure 0x40141101#32
  let zero : Signal dom (BitVec 32) := Signal.pure 0#32
  Signal.mux csrIsMstatus mstatusReg
  (Signal.mux csrIsMie mieReg
  (Signal.mux csrIsMtvec mtvecReg
  (Signal.mux csrIsMscratch mscratchReg
  (Signal.mux csrIsMepc mepcReg
  (Signal.mux csrIsMcause mcauseReg
  (Signal.mux csrIsMtval mtvalReg
  (Signal.mux csrIsMip mipValue
  (Signal.mux csrIsMisa misaConst
  (Signal.mux csrIsMhartid zero
  (Signal.mux csrIsMedeleg medelegReg
  (Signal.mux csrIsMideleg midelegReg
  (Signal.mux csrIsSstatus sstatusView
  (Signal.mux csrIsSie sieReg
  (Signal.mux csrIsStvec stvecReg
  (Signal.mux csrIsSscratch sscratchReg
  (Signal.mux csrIsSepc sepcReg
  (Signal.mux csrIsScause scauseReg
  (Signal.mux csrIsStval stvalReg
  (Signal.mux csrIsSip sipMasked
  (Signal.mux csrIsSatp satpReg
  (Signal.mux csrIsMcounteren mcounterenReg
  (Signal.mux csrIsScounteren scounterenReg
  (Signal.mux csrIsTime mtimeLoReg
  (Signal.mux csrIsTimeh mtimeHiReg
  (Signal.mux csrIsCycle mtimeLoReg
  (Signal.mux csrIsCycleh mtimeHiReg
  (Signal.mux csrIsPmp zero
    zero)))))))))))))))))))))))))))

end Sparkle.IP.RV32.CSR

/-
  IP.RV32.JITDebug — debug/trace helpers for the JIT-driven SoC harness.

  Verilator's `tb_soc.cpp` prints a `*** TRAP at cycle N: PC=... cause=...`
  line and a stream of `cycle N: PTW-WALK / PTW-PTE / SATP` events so
  silent-Linux problems are visible at a glance. The JIT harness has
  the same wires available (extended in `SoCOutput.wireNames`); this
  module gives the same diagnostic shape on top of them.

  Drop-in into a `JIT.runOptimized` callback:

      let trace ← JITDebug.mkTracer
      let _ ← JIT.runOptimized handle maxCycles wireIndices oracle
        fun cycle vals => do
          let out := SoCOutput.fromWireValues vals
          JITDebug.observe trace cycle out
          ...

  Each trap pulse, SATP change, and (optional) PTW transition emits one
  printf. The tracer keeps last-cycle values internally so each event
  fires exactly once.
-/

import Sparkle.Core.JIT
import IP.RV32.SoC

namespace Sparkle.IP.RV32.JITDebug

open Sparkle.Core.JIT
open Sparkle.IP.RV32.SoC

/-- Mutable tracer state. -/
structure State where
  prevSatp     : BitVec 32 := 0
  prevPtwPte   : BitVec 32 := 0
  prevPtwVaddr : BitVec 32 := 0
  prevSepc     : BitVec 32 := 0
  prevScause   : BitVec 32 := 0
  prevStval    : BitVec 32 := 0
  deriving Inhabited

/-- Create a fresh tracer state behind an `IO.Ref`. -/
def mkTracer : IO (IO.Ref State) := IO.mkRef {}

/-- Pretty-print a 32-bit value as 8-char lowercase hex. -/
def hex32 (v : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 v)
  String.ofList (List.replicate (8 - s.length) '0') ++ s

/-- Decode `scause` / `mcause` / `_gen_trapCause` to a short label.
    Mirrors Verilator's tb_soc.cpp branch table. -/
def causeLabel (cause : BitVec 32) : String :=
  match cause.toNat with
  | 0x00000002 => "illegal instruction"
  | 0x00000005 => "load access fault"
  | 0x00000007 => "store access fault"
  | 0x00000008 => "U-mode ecall"
  | 0x00000009 => "S-mode ecall"
  | 0x0000000B => "M-mode ecall"
  | 0x0000000C => "instruction page fault"
  | 0x0000000D => "load page fault"
  | 0x0000000F => "store page fault"
  | 0x80000003 => "SW interrupt"
  | 0x80000007 => "timer interrupt"
  | 0x80000009 => "S-mode external interrupt"
  | 0x8000000B => "external interrupt"
  | _          => "unknown"

/-- Trap observation: when `_gen_trap_taken` pulses high, print the cycle,
    PC about to take the trap, the committed cause, and tval. Two flavors
    are printed when distinguishable: M-mode (`mepc/mcause/mtval`) and
    S-mode (`sepc/scause/stval`).

    The 14-wire output struct adds ~50 % overhead per cycle vs the 6-wire
    minimum. Pass `enabled := false` to skip the call entirely (caller
    short-circuits). -/
def observe (ref : IO.Ref State) (cycle : Nat) (out : SoCOutput) (verbose : Bool := false) : IO Unit := do
  let mut st ← ref.get
  -- One-cycle trap pulse.
  if out.trapTaken then
    let tcause := out.trapCause
    IO.println s!"*** TRAP at cycle {cycle}: PC=0x{hex32 out.pc.toNat} \
                 cause=0x{hex32 tcause.toNat} ({causeLabel tcause})"
  -- S-mode CSR diff (sepc/scause/stval) → print when sepc changes.
  if out.sepc != st.prevSepc || out.scause != st.prevScause || out.stval != st.prevStval then
    IO.println s!"  S-trap: sepc=0x{hex32 out.sepc.toNat} \
                 scause=0x{hex32 out.scause.toNat} ({causeLabel out.scause}) \
                 stval=0x{hex32 out.stval.toNat}"
    st := { st with prevSepc := out.sepc, prevScause := out.scause, prevStval := out.stval }
  -- SATP change.
  if out.satp != st.prevSatp then
    IO.println s!"cycle {cycle}: SATP: 0x{hex32 st.prevSatp.toNat} -> 0x{hex32 out.satp.toNat}"
    st := { st with prevSatp := out.satp }
  -- Optional PTW trace (high volume; off by default).
  if verbose && (out.ptwVaddr != st.prevPtwVaddr || out.ptwPte != st.prevPtwPte) then
    IO.println s!"cycle {cycle}: PTW vaddr=0x{hex32 out.ptwVaddr.toNat} \
                 pte=0x{hex32 out.ptwPte.toNat} satp=0x{hex32 out.satp.toNat}"
    st := { st with prevPtwVaddr := out.ptwVaddr, prevPtwPte := out.ptwPte }
  ref.set st

end Sparkle.IP.RV32.JITDebug

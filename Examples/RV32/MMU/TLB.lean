/-
  Sv32 Translation Lookaside Buffer (TLB)

  Fully-associative TLB with 16 entries for Sv32 page translation.
  Each entry stores: valid, VPN (20 bits), PPN (22 bits), flags (8 bits),
  and megapage indicator.

  Supports lookup, fill (from PTW), and flush (SFENCE.VMA).
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.RV32.CSR.Types

set_option maxRecDepth 8192

namespace Sparkle.Examples.RV32.MMU.TLB

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Examples.RV32.CSR
open CircuitM

/-- Number of TLB entries -/
def tlbEntries : Nat := 16

/-- TLB entry field widths -/
def vpnWidth : Nat := 20    -- Virtual Page Number
def ppnWidth : Nat := 22    -- Physical Page Number (Sv32: 34-bit PA)
def flagWidth : Nat := 8    -- PTE flags: D,A,G,U,X,W,R,V

/-- Total TLB entry width: valid(1) + vpn(20) + ppn(22) + flags(8) + megapage(1) = 52 -/
def entryWidth : Nat := 1 + vpnWidth + ppnWidth + flagWidth + 1

/-- Generate a single TLB entry with lookup and update logic.

    Each entry is a set of registers storing the TLB fields.
    Returns: (hit_signal_name, ppn_output_name, flags_output_name, megapage_name)
-/
def generateTLBEntry (idx : Nat) (lookupVPN : String) (fillValid : String)
    (fillVPN fillPPN fillFlags fillMega : String)
    (flushAll : String) (replaceIdx : String) : CircuitM (String × String × String × String) := do
  let pfx := s!"tlb_e{idx}"

  -- Entry registers
  let validNext ← makeWire s!"{pfx}_valid_next" .bit
  let validReg ← emitRegister s!"{pfx}_valid" "clk" "rst" (.ref validNext) 0 .bit

  let vpnNext ← makeWire s!"{pfx}_vpn_next" (.bitVector vpnWidth)
  let vpnReg ← emitRegister s!"{pfx}_vpn" "clk" "rst" (.ref vpnNext) 0 (.bitVector vpnWidth)

  let ppnNext ← makeWire s!"{pfx}_ppn_next" (.bitVector ppnWidth)
  let ppnReg ← emitRegister s!"{pfx}_ppn" "clk" "rst" (.ref ppnNext) 0 (.bitVector ppnWidth)

  let flagsNext ← makeWire s!"{pfx}_flags_next" (.bitVector flagWidth)
  let flagsReg ← emitRegister s!"{pfx}_flags" "clk" "rst" (.ref flagsNext) 0 (.bitVector flagWidth)

  let megaNext ← makeWire s!"{pfx}_mega_next" .bit
  let megaReg ← emitRegister s!"{pfx}_mega" "clk" "rst" (.ref megaNext) 0 .bit

  -- VPN match: compare stored VPN with lookup VPN
  -- For megapages (4MB), only compare VPN[1] (top 10 bits of VPN)
  let fullMatch ← makeWire s!"{pfx}_full_match" .bit
  emitAssign fullMatch (.op .eq [.ref vpnReg, .ref lookupVPN])

  let megaMatch ← makeWire s!"{pfx}_mega_match" .bit
  emitAssign megaMatch (.op .eq [
    .slice (.ref vpnReg) 19 10,
    .slice (.ref lookupVPN) 19 10])

  let vpnMatch ← makeWire s!"{pfx}_vpn_match" .bit
  emitAssign vpnMatch (Expr.mux (.ref megaReg) (.ref megaMatch) (.ref fullMatch))

  -- Hit: valid AND vpn match
  let hit ← makeWire s!"{pfx}_hit" .bit
  emitAssign hit (.op .and [.ref validReg, .ref vpnMatch])

  -- Fill: this entry is selected for replacement
  let thisReplace ← makeWire s!"{pfx}_replace" .bit
  emitAssign thisReplace (.op .eq [.ref replaceIdx, .const idx 4])
  let doFill ← makeWire s!"{pfx}_do_fill" .bit
  emitAssign doFill (.op .and [.ref fillValid, .ref thisReplace])

  -- Update logic
  -- Valid: clear on flush, set on fill, keep otherwise
  emitAssign validNext
    (Expr.mux (.ref flushAll) (.const 0 1)
    (Expr.mux (.ref doFill) (.const 1 1)
      (.ref validReg)))

  -- VPN/PPN/flags/mega: update on fill, keep otherwise
  emitAssign vpnNext (Expr.mux (.ref doFill) (.ref fillVPN) (.ref vpnReg))
  emitAssign ppnNext (Expr.mux (.ref doFill) (.ref fillPPN) (.ref ppnReg))
  emitAssign flagsNext (Expr.mux (.ref doFill) (.ref fillFlags) (.ref flagsReg))
  emitAssign megaNext (Expr.mux (.ref doFill) (.ref fillMega) (.ref megaReg))

  return (hit, ppnReg, flagsReg, megaReg)

/-- Generate the TLB module.

    Inputs:
      clk, rst
      lookup_vpn[19:0]    - Virtual page number to look up
      lookup_valid        - Lookup request valid
      fill_valid          - Fill request from PTW
      fill_vpn[19:0]      - VPN for fill
      fill_ppn[21:0]      - PPN for fill
      fill_flags[7:0]     - PTE flags for fill
      fill_mega           - Megapage indicator for fill
      flush_all           - SFENCE.VMA: invalidate all entries

    Outputs:
      hit                 - TLB hit
      ppn[21:0]           - Physical page number (on hit)
      flags[7:0]          - PTE flags (on hit)
      megapage            - Megapage indicator (on hit)
-/
def generateTLB : CircuitM Unit := do
  addInput "clk" .bit
  addInput "rst" .bit
  addInput "lookup_vpn" (.bitVector vpnWidth)
  addInput "lookup_valid" .bit
  addInput "fill_valid" .bit
  addInput "fill_vpn" (.bitVector vpnWidth)
  addInput "fill_ppn" (.bitVector ppnWidth)
  addInput "fill_flags" (.bitVector flagWidth)
  addInput "fill_mega" .bit
  addInput "flush_all" .bit
  addOutput "hit" .bit
  addOutput "ppn" (.bitVector ppnWidth)
  addOutput "flags" (.bitVector flagWidth)
  addOutput "megapage" .bit

  -- FIFO replacement pointer (4 bits for 16 entries)
  let replNext ← makeWire "repl_next" (.bitVector 4)
  let replReg ← emitRegister "repl_ptr" "clk" "rst" (.ref replNext) 0 (.bitVector 4)

  -- Increment replacement pointer on fill
  let replInc ← makeWire "repl_inc" (.bitVector 4)
  emitAssign replInc (Expr.add (.ref replReg) (.const 1 4))
  emitAssign replNext (Expr.mux (.ref "fill_valid") (.ref replInc) (.ref replReg))

  -- Generate all 16 TLB entries
  let mut hits : List String := []
  let mut ppns : List String := []
  let mut flagsList : List String := []
  let mut megas : List String := []

  for i in List.range tlbEntries do
    let (hit, ppn, flags, mega) ← generateTLBEntry i
      "lookup_vpn" "fill_valid" "fill_vpn" "fill_ppn" "fill_flags" "fill_mega"
      "flush_all" replReg
    hits := hits ++ [hit]
    ppns := ppns ++ [ppn]
    flagsList := flagsList ++ [flags]
    megas := megas ++ [mega]

  -- OR all hit signals for overall hit
  let buildOr (signals : List String) : CircuitM String := do
    match signals with
    | [] => do
      let z ← makeWire "zero_hit" .bit
      emitAssign z (.const 0 1)
      return z
    | [s] => return s
    | s :: rest => do
      let mut acc := s
      for r in rest do
        let w ← makeWire "hit_or" .bit
        emitAssign w (.op .or [.ref acc, .ref r])
        acc := w
      return acc

  let anyHit ← buildOr hits
  emitAssign "hit" (.ref anyHit)

  -- Priority mux for PPN output (first hit wins)
  let buildPriorityMux (hits : List String) (vals : List String)
      (defaultVal : Expr) (width : Nat) (pfx : String) : CircuitM String := do
    let mut result ← makeWire s!"{pfx}_default" (.bitVector width)
    emitAssign result defaultVal
    -- Build from last to first (last has lowest priority)
    let pairs := hits.zip vals
    for (h, v) in pairs.reverse do
      let w ← makeWire s!"{pfx}_sel" (.bitVector width)
      emitAssign w (Expr.mux (.ref h) (.ref v) (.ref result))
      result := w
    return result

  let ppnOut ← buildPriorityMux hits ppns (.const 0 ppnWidth) ppnWidth "ppn_mux"
  emitAssign "ppn" (.ref ppnOut)

  let flagsOut ← buildPriorityMux hits flagsList (.const 0 flagWidth) flagWidth "flags_mux"
  emitAssign "flags" (.ref flagsOut)

  -- Megapage output via priority mux on 1-bit values, need special handling
  -- Use hit signals to select mega bit
  let mut megaResult ← makeWire "mega_default" .bit
  emitAssign megaResult (.const 0 1)
  let megaPairs := hits.zip megas
  for (h, m) in megaPairs.reverse do
    let w ← makeWire "mega_sel" .bit
    emitAssign w (Expr.mux (.ref h) (.ref m) (.ref megaResult))
    megaResult := w
  emitAssign "megapage" (.ref megaResult)

/-- Build the TLB module -/
def buildTLB : Module :=
  CircuitM.runModule "RV32I_TLB" do
    generateTLB

end Sparkle.Examples.RV32.MMU.TLB

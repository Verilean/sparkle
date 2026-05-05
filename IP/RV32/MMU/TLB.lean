/-
  RV32 TLB hit-lookup — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 491..517). The Sparkle
  SoC has a 4-entry fully-associative TLB. Each entry stores:

    valid : Bool        — entry is in use
    VPN   : BitVec 20   — virtual page number (looked up against dVPN)
    PPN   : BitVec 22   — physical page number (returned on hit)
    flags : BitVec 8    — PTE flags {V,R,W,X,U,G,A,D}
    mega  : Bool        — this entry is a 4MB mega-page

  Lookup spec:
    For a 4KB regular entry:  match iff entry.VPN == dVPN
    For a 4MB mega-page entry: match iff entry.VPN[19:10] == dVPN[19:10]
                              (only the high 10 bits matter; low 10
                               are page-internal offset for megapages)

  Hit iff valid AND VPN match. anyTLBHit = OR over the 4 entries.
  On hit, the PPN/Mega selector returns the data from the
  highest-numbered hitting entry (priority cascade tlb0 > tlb1 >
  tlb2 > tlb3).

  Commit bf6d873 fixed a bug in the megapage VPN-match logic;
  this module makes the spec machine-checkable.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.MMU

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure per-entry hit -/

/-- Per-entry VPN match: regular = full equality, mega = high-10 only. -/
@[inline] def tlbVPNMatchPure
    (mega : Bool) (entryVPN dVPN : BitVec 20) : Bool :=
  if mega then
    entryVPN.extractLsb' 10 10 == dVPN.extractLsb' 10 10
  else
    entryVPN == dVPN

/-- Per-entry hit: valid AND VPN match. -/
@[inline] def tlbHitPure
    (valid mega : Bool) (entryVPN dVPN : BitVec 20) : Bool :=
  valid && tlbVPNMatchPure mega entryVPN dVPN

/-- 4-way any-hit. -/
@[inline] def anyTLBHitPure (h0 h1 h2 h3 : Bool) : Bool :=
  (h0 || h1) || (h2 || h3)

/-! ## Per-entry data selectors -/

/-- 4-way PPN selector with priority tlb0 > tlb1 > tlb2 > tlb3. -/
@[inline] def tlbPPNPure
    (h0 h1 h2 h3 : Bool) (p0 p1 p2 p3 : BitVec 22) : BitVec 22 :=
  if h0 then p0
  else if h1 then p1
  else if h2 then p2
  else if h3 then p3
  else 0#22

/-- 4-way Mega-flag selector. -/
@[inline] def tlbMegaPure
    (h0 h1 h2 h3 : Bool) (m0 m1 m2 m3 : Bool) : Bool :=
  if h0 then m0
  else if h1 then m1
  else if h2 then m2
  else if h3 then m3
  else false

/-! ## Spec invariants -/

/-- Mega-entry match ignores low 10 bits of VPN. -/
theorem tlbVPNMatch_mega_ignores_low10
    (entryVPN dVPN : BitVec 20)
    (h : entryVPN.extractLsb' 10 10 = dVPN.extractLsb' 10 10) :
    tlbVPNMatchPure true entryVPN dVPN = true := by
  unfold tlbVPNMatchPure
  simp [h]

/-- Regular-entry match requires full VPN equality. -/
theorem tlbVPNMatch_regular
    (entryVPN dVPN : BitVec 20) (h : entryVPN = dVPN) :
    tlbVPNMatchPure false entryVPN dVPN = true := by
  unfold tlbVPNMatchPure
  simp [h]

/-- Invalid entry never hits. -/
@[simp] theorem tlbHit_invalid
    (mega : Bool) (entryVPN dVPN : BitVec 20) :
    tlbHitPure false mega entryVPN dVPN = false := by
  unfold tlbHitPure
  rfl

/-- Valid + VPN match → hit. -/
theorem tlbHit_valid_match
    (mega : Bool) (entryVPN dVPN : BitVec 20)
    (h : tlbVPNMatchPure mega entryVPN dVPN = true) :
    tlbHitPure true mega entryVPN dVPN = true := by
  unfold tlbHitPure
  simp [h]

/-! ### anyTLBHit spec -/

/-- All-clear → no hit. -/
@[simp] theorem anyTLBHit_none :
    anyTLBHitPure false false false false = false := by rfl

/-- Any single entry hitting → anyTLBHit fires. -/
theorem anyTLBHit_h0 (h1 h2 h3 : Bool) :
    anyTLBHitPure true h1 h2 h3 = true := by
  unfold anyTLBHitPure
  cases h1 <;> cases h2 <;> cases h3 <;> rfl

theorem anyTLBHit_h1 (h0 h2 h3 : Bool) :
    anyTLBHitPure h0 true h2 h3 = true := by
  unfold anyTLBHitPure
  cases h0 <;> cases h2 <;> cases h3 <;> rfl

theorem anyTLBHit_h2 (h0 h1 h3 : Bool) :
    anyTLBHitPure h0 h1 true h3 = true := by
  unfold anyTLBHitPure
  cases h0 <;> cases h1 <;> cases h3 <;> rfl

theorem anyTLBHit_h3 (h0 h1 h2 : Bool) :
    anyTLBHitPure h0 h1 h2 true = true := by
  unfold anyTLBHitPure
  cases h0 <;> cases h1 <;> cases h2 <;> rfl

/-! ### Priority spec -/

/-- tlb0 hit takes precedence over the other entries. -/
@[simp] theorem tlbPPN_h0_priority
    (h1 h2 h3 : Bool) (p0 p1 p2 p3 : BitVec 22) :
    tlbPPNPure true h1 h2 h3 p0 p1 p2 p3 = p0 := by rfl

/-- tlb1 takes precedence over h2, h3 when h0 is clear. -/
@[simp] theorem tlbPPN_h1_priority
    (h2 h3 : Bool) (p0 p1 p2 p3 : BitVec 22) :
    tlbPPNPure false true h2 h3 p0 p1 p2 p3 = p1 := by rfl

/-- No hit → 0 (default). -/
@[simp] theorem tlbPPN_none (p0 p1 p2 p3 : BitVec 22) :
    tlbPPNPure false false false false p0 p1 p2 p3 = 0#22 := by rfl

/-- The Mega selector follows the same priority. -/
@[simp] theorem tlbMega_h0_priority
    (h1 h2 h3 : Bool) (m0 m1 m2 m3 : Bool) :
    tlbMegaPure true h1 h2 h3 m0 m1 m2 m3 = m0 := by rfl

/-! ## Composite specs -/

theorem tlbHitPure_spec
    (valid mega : Bool) (entryVPN dVPN : BitVec 20) :
    tlbHitPure valid mega entryVPN dVPN =
      (valid && (if mega then
                   entryVPN.extractLsb' 10 10 == dVPN.extractLsb' 10 10
                 else
                   entryVPN == dVPN)) := by rfl

theorem anyTLBHitPure_spec :
    ∀ (h0 h1 h2 h3 : Bool),
      anyTLBHitPure h0 h1 h2 h3 = (h0 || h1 || h2 || h3) := by
  decide

/-! ## Signal-level wrappers -/

def tlbVPNMatchSignal {dom : DomainConfig}
    (mega : Signal dom Bool)
    (entryVPN dVPN : Signal dom (BitVec 20)) : Signal dom Bool :=
  let fullMatch := entryVPN === dVPN
  let megaMatch := (entryVPN.map (BitVec.extractLsb' 10 10 ·))
                     === (dVPN.map (BitVec.extractLsb' 10 10 ·))
  Signal.mux mega megaMatch fullMatch

def tlbHitSignal {dom : DomainConfig}
    (valid mega : Signal dom Bool)
    (entryVPN dVPN : Signal dom (BitVec 20)) : Signal dom Bool :=
  valid &&& tlbVPNMatchSignal mega entryVPN dVPN

def anyTLBHitSignal {dom : DomainConfig}
    (h0 h1 h2 h3 : Signal dom Bool) : Signal dom Bool :=
  (h0 ||| h1) ||| (h2 ||| h3)

def tlbPPNSignal {dom : DomainConfig}
    (h0 h1 h2 h3 : Signal dom Bool)
    (p0 p1 p2 p3 : Signal dom (BitVec 22)) : Signal dom (BitVec 22) :=
  Signal.mux h0 p0
    (Signal.mux h1 p1
    (Signal.mux h2 p2
    (Signal.mux h3 p3 (Signal.pure 0#22))))

def tlbMegaSignal {dom : DomainConfig}
    (h0 h1 h2 h3 m0 m1 m2 m3 : Signal dom Bool) : Signal dom Bool :=
  Signal.mux h0 m0
    (Signal.mux h1 m1
    (Signal.mux h2 m2
    (Signal.mux h3 m3 (Signal.pure false))))

end Sparkle.IP.RV32.MMU

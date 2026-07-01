/-
  IP.Crypto.MerkleHW — streaming Merkle-tree root accumulator.

  Storage: `depth` register slots, each 256 bits (SHA-256 digest
  size), plus a `depth`-bit occupancy mask.  When a new leaf
  digest is pushed:

    * Walk up the occupancy mask starting at level 0.
    * If level k is unoccupied: place the carry into slot k,
      mark k occupied, and stop.
    * If level k is occupied: combine (slot_k, carry) via the
      caller-supplied SHA-256 combiner, clear level k, and
      propagate the combined digest as the new carry to level
      k+1.

  Combining is delegated to a caller signal (`combineOut : Signal
  dom (BitVec 256)`), driven by an external SHA-256 engine — see
  Tests/IP/Crypto/MerkleHWTest.lean for how the test wires it.
  This keeps the module small; the SHA-256 HW piece is validated
  independently in Tests/IP/Crypto/SHA256Test.lean.

  Interface:
    inputs  start (Bool pulse)  — reset all slots to zero.
            push (Bool pulse)   — enqueue a new leaf.
            leafIn (BitVec 256) — leaf digest to enqueue.
            combineOut (BitVec 256) — SHA-256(left ++ right)
                                     computed externally with
                                     `combineLeft` / `combineRight`
                                     as its inputs.
            combineDone (Bool)  — high when combineOut is valid.
    outputs combineLeft, combineRight : BitVec 256
                        — operands the accumulator wants hashed.
            combineReq  : Bool
                        — high when the accumulator is waiting
                          on the external hasher.
            root        : BitVec 256
                        — current running root (folded slots).
            ready       : Bool
                        — high when a new `push` can be accepted.

  Fixed depth = 4 (i.e. up to 2^4 = 16 leaves) in this
  reference module.  Larger trees just widen the slot array;
  the FSM shape is unchanged.  The tutorial workflow — commit
  → open → verify — uses trees of at most a few dozen leaves
  in tests, so 16 is enough headroom for the coverage checks.
-/
import Sparkle

namespace Sparkle.IP.Crypto.MerkleHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Fixed max depth = 4 slots (2^4 = 16 leaves) in this
    reference module.  Wider trees just widen the slot array
    (see the file docstring). -/
def depth : Nat := 4

/-- Output bundle. -/
structure MerkleOut (dom : DomainConfig) where
  /-- Slot 0..3 (each 256 bits).  For a fully-loaded 2^k-leaf
      tree the root lives in slot k-1; e.g. 4 leaves → slot 1,
      wait no — the *carry-propagation* semantics puts the
      root at slot log₂(N) since combining at level k stores
      the result at level k+1.  So 4 leaves ⇒ slot 2,
      8 leaves ⇒ slot 3.  The test extracts the right slot. -/
  slot0        : Signal dom (BitVec 256)
  slot1        : Signal dom (BitVec 256)
  slot2        : Signal dom (BitVec 256)
  slot3        : Signal dom (BitVec 256)
  /-- 4-bit occupancy mask (bit k = slot k holds a partial digest). -/
  occ          : Signal dom (BitVec 4)
  /-- Left/right operands the accumulator is asking the external
      hasher to combine on this cycle.  `combineReq` is high
      exactly when the accumulator is stalled waiting on the
      hasher. -/
  combineLeft  : Signal dom (BitVec 256)
  combineRight : Signal dom (BitVec 256)
  combineReq   : Signal dom Bool
  /-- High when a new `push` can be accepted. -/
  ready        : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (MerkleOut dom) dom := ⟨⟩

/-- Streaming Merkle-tree accumulator.

    See the docstring at the top of the file for the interface.
    Uses 4 slots (2^4 = 16-leaf trees) as the internal register
    count — deeper trees just add more slot registers on the same
    FSM shape.  We keep this compact so `#synthesizeVerilog`
    stays under the elaborator's per-module recursion budget. -/
def merkleRootHW {dom : DomainConfig}
    (start push : Signal dom Bool)
    (leafIn combineOut : Signal dom (BitVec 256))
    (combineDone : Signal dom Bool) :
    MerkleOut dom :=
  circuit do
    -- Four slots × 256 bits.  Deeper trees just add more of these.
    let s0R ← Signal.reg (0#256)
    let s1R ← Signal.reg (0#256)
    let s2R ← Signal.reg (0#256)
    let s3R ← Signal.reg (0#256)
    -- Occupancy mask (bit k = 1 if slot k holds a partial digest).
    let occR ← Signal.reg (0#4)
    -- Carry-digest register (the current propagating "carry"
    -- we're trying to place).
    let carryR ← Signal.reg (0#256)
    -- Current level pointer (0..3).  When busy, tells the FSM
    -- which slot is under consideration.
    let lvlR ← Signal.reg (0#3)
    -- Busy flag: true while walking the occupancy carry chain.
    let busyR ← Signal.reg false

    let s0Sig := (s0R : Signal dom (BitVec 256))
    let s1Sig := (s1R : Signal dom (BitVec 256))
    let s2Sig := (s2R : Signal dom (BitVec 256))
    let s3Sig := (s3R : Signal dom (BitVec 256))
    let occSig := (occR : Signal dom (BitVec 4))
    let carrySig := (carryR : Signal dom (BitVec 256))
    let lvlSig := (lvlR : Signal dom (BitVec 3))
    let busySig := (busyR : Signal dom Bool)

    -- Constants.
    let p0_3 := (Signal.pure 0#3 : Signal dom (BitVec 3))
    let p1_3 := (Signal.pure 1#3 : Signal dom (BitVec 3))
    let p2_3 := (Signal.pure 2#3 : Signal dom (BitVec 3))
    let p3_3 := (Signal.pure 3#3 : Signal dom (BitVec 3))
    let p0_4 := (Signal.pure 0#4 : Signal dom (BitVec 4))
    let pOccBit0 := (Signal.pure 1#4  : Signal dom (BitVec 4))
    let pOccBit1 := (Signal.pure 2#4  : Signal dom (BitVec 4))
    let pOccBit2 := (Signal.pure 4#4  : Signal dom (BitVec 4))
    let pOccBit3 := (Signal.pure 8#4  : Signal dom (BitVec 4))
    let p0_256 := (Signal.pure 0#256 : Signal dom (BitVec 256))

    -- Level predicates.
    let isL0 := ((· == ·) <$> lvlSig <*> p0_3 : Signal dom Bool)
    let isL1 := ((· == ·) <$> lvlSig <*> p1_3 : Signal dom Bool)
    let isL2 := ((· == ·) <$> lvlSig <*> p2_3 : Signal dom Bool)
    let isL3 := ((· == ·) <$> lvlSig <*> p3_3 : Signal dom Bool)

    -- Current slot content for this level.
    let curSlot :=
      Signal.mux isL0 s0Sig
        (Signal.mux isL1 s1Sig
          (Signal.mux isL2 s2Sig s3Sig))

    -- Occupancy bit at this level (occ bitand slot-mask ≠ 0).
    let occMask :=
      Signal.mux isL0 pOccBit0
        (Signal.mux isL1 pOccBit1
          (Signal.mux isL2 pOccBit2 pOccBit3))
    let occAnd := ((· &&& ·) <$> occSig <*> occMask : Signal dom (BitVec 4))
    let occIsZero := ((· == ·) <$> occAnd <*> p0_4 : Signal dom Bool)
    let occHere := ((fun b => !b) <$> occIsZero : Signal dom Bool)

    -- combineReq is high while busy AND the current level is occupied
    -- (i.e. we're waiting on external hasher).
    let combineReq := ((· && ·) <$> busySig <*> occHere : Signal dom Bool)

    -- On a push (accepted only when !busy): load carryR = leafIn, lvl = 0, busy = true.
    let pushAccepted := ((fun b p => !b && p) <$> busySig <*> push : Signal dom Bool)

    -- Progress condition: busy & level-is-empty ⇒ place carry, mark occupied, finish.
    -- Or: busy & level-is-occupied & combineDone ⇒ move to next level, carry = combineOut.
    let placeNow := ((· && ·) <$> busySig <*> occIsZero : Signal dom Bool)
    let combStep := ((· && ·) <$> combineReq <*> combineDone : Signal dom Bool)

    -- Level increment.
    let lvlInc := ((· + ·) <$> lvlSig <*> p1_3 : Signal dom (BitVec 3))
    -- New occupancy mask on placement: occ | occMask (using OR).
    let occSet := ((· ||| ·) <$> occSig <*> occMask : Signal dom (BitVec 4))
    -- New occupancy mask on combine step: occ &~ occMask (clear the current level).
    let notMask := ((~~~ ·) <$> occMask : Signal dom (BitVec 4))
    let occClr := ((· &&& ·) <$> occSig <*> notMask : Signal dom (BitVec 4))

    -- Register updates.
    -- Reset (start): everything back to zero, busy off.
    -- Push:  carry ← leafIn, lvl ← 0, busy ← true.
    -- placeNow: slot[lvl] ← carry, occ ← occSet, busy ← false, lvl ← 0.
    -- combStep: carry ← combineOut, occ ← occClr, lvl ← lvl+1, busy stays true.
    -- Slot update: on placeNow AND isLk, slot k takes carry; else hold.
    let placeS0 := ((· && ·) <$> placeNow <*> isL0 : Signal dom Bool)
    let placeS1 := ((· && ·) <$> placeNow <*> isL1 : Signal dom Bool)
    let placeS2 := ((· && ·) <$> placeNow <*> isL2 : Signal dom Bool)
    let placeS3 := ((· && ·) <$> placeNow <*> isL3 : Signal dom Bool)
    s0R <~ Signal.mux start p0_256 (Signal.mux placeS0 carrySig s0Sig)
    s1R <~ Signal.mux start p0_256 (Signal.mux placeS1 carrySig s1Sig)
    s2R <~ Signal.mux start p0_256 (Signal.mux placeS2 carrySig s2Sig)
    s3R <~ Signal.mux start p0_256 (Signal.mux placeS3 carrySig s3Sig)

    -- Occupancy update.
    occR <~ Signal.mux start p0_4
              (Signal.mux placeNow occSet
                (Signal.mux combStep occClr occSig))

    -- Carry register.
    carryR <~ Signal.mux start p0_256
                (Signal.mux pushAccepted leafIn
                  (Signal.mux combStep combineOut carrySig))

    -- Level.
    lvlR <~ Signal.mux start p0_3
              (Signal.mux pushAccepted p0_3
                (Signal.mux combStep lvlInc
                  (Signal.mux placeNow p0_3 lvlSig)))

    -- Busy.
    busyR <~ Signal.mux start (Signal.pure false : Signal dom Bool)
              (Signal.mux pushAccepted (Signal.pure true : Signal dom Bool)
                (Signal.mux placeNow (Signal.pure false : Signal dom Bool) busySig))

    -- Combine operands: currently-occupied slot & the carry.
    let combineLeft := curSlot
    let combineRight := carrySig

    -- Ready = !busy.
    let ready := ((fun b => !b) <$> busySig : Signal dom Bool)

    -- Expose all four slots (root lives in slot log₂(N)).
    return ({ slot0        := s0Sig
            , slot1        := s1Sig
            , slot2        := s2Sig
            , slot3        := s3Sig
            , occ          := occSig
            , combineLeft  := combineLeft
            , combineRight := combineRight
            , combineReq   := combineReq
            , ready        := ready
            } : MerkleOut dom)

end Sparkle.IP.Crypto.MerkleHW

/-
  Sim test for IP.Crypto.Merkle.

  Validates:
    1. Commit + open + verify round-trip for an 8-leaf tree.
    2. Verify rejects when the leaf value is tampered.
    3. Verify rejects when the index is wrong.
    4. Verify rejects when one auth-path digest is corrupted.
-/

import IP.Crypto.Merkle

open Sparkle.IP.Crypto.Merkle

namespace Sparkle.Tests.IP.Crypto.MerkleTest

def main : IO Unit := do
  IO.println "=== Merkle commitment sim ==="
  let mut ok := true

  -- 8-leaf tree with simple values.
  let leaves : Array Nat := #[10, 20, 30, 40, 50, 60, 70, 80]
  let root := commit leaves
  IO.println s!"  root size = {root.size} bytes (expected 32)"
  if root.size ≠ 32 then ok := false

  -- 1. Open + verify each leaf round-trips.
  let mut roundOk := true
  for h : i in [:8] do
    let path := openAt leaves i
    let v := verifyOpen root (leaves.getD i 0) i path
    if !v then
      IO.println s!"  ✗ leaf {i}: verify failed"
      roundOk := false
  if roundOk then
    IO.println "  ✓ all 8 leaf openings verify against the root"
  else ok := false

  -- 2. Tampered leaf value: should fail.
  let path3 := openAt leaves 3
  let tamper := verifyOpen root 999 3 path3
  IO.println s!"  tampered leaf value (3 → 999): verify = {tamper} (expected false)"
  if tamper then ok := false

  -- 3. Wrong index with right value: should fail.
  let wrongIdx := verifyOpen root 30 7 path3  -- value=30 is at idx 2, but we claim idx 7
  IO.println s!"  wrong index (claim leaf 30 at idx 7): verify = {wrongIdx} (expected false)"
  if wrongIdx then ok := false

  -- 4. Corrupted auth path: should fail.
  let path0 := openAt leaves 0
  let mut corruptPath := path0
  -- Flip a byte in the first sibling.
  let firstSib := corruptPath.getD 0 #[]
  let firstSibCorrupt := firstSib.set! 0 ((firstSib.getD 0 0) ^^^ 1)
  corruptPath := corruptPath.set! 0 firstSibCorrupt
  let corrupt := verifyOpen root 10 0 corruptPath
  IO.println s!"  corrupted auth-path: verify = {corrupt} (expected false)"
  if corrupt then ok := false

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.MerkleTest

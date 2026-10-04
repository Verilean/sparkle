/-
  Sim test for the pure-data memcached parser + KV oracle.
  No HW signals — this is the spec the Signal-DSL implementation
  in IP/Net/MemcachedHW.lean must reproduce cycle-for-cycle.
-/

import IP.Net.Memcached

open Sparkle.IP.Net.Memcached

namespace Sparkle.Tests.IP.Net.MemcachedOracleTest

private def strBytes (s : String) : List UInt8 :=
  s.toUTF8.toList.toArray.toList.map (fun c => c.toNat.toUInt8)

def testParseGet : IO Bool := do
  IO.println "=== parse: get foo ==="
  let mut ok := true
  let input := strBytes "get foo\r\n"
  match parseOne input with
  | some (.get key, rest) =>
    let keyStr := String.ofList (key.toList.map (fun b => Char.ofNat b.toNat))
    if keyStr = "foo" ∧ rest = [] then
      IO.println s!"  ✓ parsed get with key={keyStr}"
    else
      IO.println s!"  ✗ unexpected: key={keyStr} rest_len={rest.length}"
      ok := false
  | some (c, _) => IO.println s!"  ✗ wrong command type: {repr c}"; ok := false
  | none => IO.println "  ✗ parse returned none"; ok := false
  return ok

def testParseSet : IO Bool := do
  IO.println "\n=== parse: set foo 0 0 5\\r\\nhello\\r\\n ==="
  let mut ok := true
  let input := strBytes "set foo 0 0 5\r\nhello\r\n"
  match parseOne input with
  | some (.set key flags exp value, _) =>
    let keyStr := String.ofList (key.toList.map (fun b => Char.ofNat b.toNat))
    let valStr := String.ofList (value.toList.map (fun b => Char.ofNat b.toNat))
    if keyStr = "foo" ∧ valStr = "hello" ∧ flags = 0 ∧ exp = 0 then
      IO.println s!"  ✓ parsed set: key={keyStr} flags={flags} exp={exp} value={valStr}"
    else
      IO.println s!"  ✗ mismatched: key={keyStr} value={valStr}"
      ok := false
  | some (c, _) => IO.println s!"  ✗ wrong command type: {repr c}"; ok := false
  | none => IO.println "  ✗ parse returned none"; ok := false
  return ok

def testParseDelete : IO Bool := do
  IO.println "\n=== parse: delete foo\\r\\n ==="
  let mut ok := true
  let input := strBytes "delete foo\r\n"
  match parseOne input with
  | some (.del key, _) =>
    let keyStr := String.ofList (key.toList.map (fun b => Char.ofNat b.toNat))
    if keyStr = "foo" then
      IO.println s!"  ✓ parsed delete with key={keyStr}"
    else
      IO.println s!"  ✗ wrong key: {keyStr}"
      ok := false
  | some (c, _) => IO.println s!"  ✗ wrong command type: {repr c}"; ok := false
  | none => IO.println "  ✗ parse returned none"; ok := false
  return ok

def testKvBasicSet : IO Bool := do
  IO.println "\n=== KV: set + get round-trip ==="
  let mut ok := true
  let store0 : KvStore := {}
  let setCmd : Command := .set (strToBytes "foo") 0 0 (strToBytes "hello")
  let (store1, r1) := applyCommand store0 setCmd
  match r1 with
  | [.stored] => IO.println "  ✓ set replied STORED"
  | rs => IO.println s!"  ✗ unexpected reply: {repr rs}"; ok := false

  let getCmd : Command := .get (strToBytes "foo")
  let (_, r2) := applyCommand store1 getCmd
  match r2 with
  | [.value key flags value, .end_] =>
    let keyStr := String.ofList (key.toList.map (fun b => Char.ofNat b.toNat))
    let valStr := String.ofList (value.toList.map (fun b => Char.ofNat b.toNat))
    if keyStr = "foo" ∧ valStr = "hello" ∧ flags = 0 then
      IO.println s!"  ✓ get returned VALUE foo {flags} 5 / hello / END"
    else
      IO.println s!"  ✗ get returned VALUE {keyStr} {flags} ?/{valStr}/END"
      ok := false
  | rs => IO.println s!"  ✗ unexpected reply: {repr rs}"; ok := false
  return ok

def testKvDeleteThenGet : IO Bool := do
  IO.println "\n=== KV: set, delete, get → END only ==="
  let mut ok := true
  let store0 : KvStore := {}
  let key : Array UInt8 := (strToBytes "foo")
  let val : Array UInt8 := ("bar".toUTF8.toList.toArray.map (fun c => c.toNat.toUInt8))
  let (store1, _) := applyCommand store0 (.set key 0 0 val)
  let (store2, r2) := applyCommand store1 (.del key)
  match r2 with
  | [.deleted] => IO.println "  ✓ delete replied DELETED"
  | rs => IO.println s!"  ✗ unexpected delete reply: {repr rs}"; ok := false

  let (_, r3) := applyCommand store2 (.get key)
  match r3 with
  | [.end_] => IO.println "  ✓ get after delete → END only"
  | rs => IO.println s!"  ✗ expected [END], got {repr rs}"; ok := false
  return ok

def testKvAddSemantics : IO Bool := do
  IO.println "\n=== KV: add → STORED only when absent ==="
  let mut ok := true
  let store0 : KvStore := {}
  let key : Array UInt8 := (strToBytes "foo")
  let val : Array UInt8 := ("v1".toUTF8.toList.toArray.map (fun c => c.toNat.toUInt8))
  let val2 : Array UInt8 := ("v2".toUTF8.toList.toArray.map (fun c => c.toNat.toUInt8))

  -- first add — should STORE
  let (store1, r1) := applyCommand store0 (.add key 0 0 val)
  match r1 with
  | [.stored] => IO.println "  ✓ first add → STORED"
  | rs => IO.println s!"  ✗ first add: {repr rs}"; ok := false

  -- second add — should NOT_STORE
  let (store2, r2) := applyCommand store1 (.add key 0 0 val2)
  match r2 with
  | [.notStored] => IO.println "  ✓ second add → NOT_STORED"
  | rs => IO.println s!"  ✗ second add: {repr rs}"; ok := false

  -- value should still be v1
  let (_, r3) := applyCommand store2 (.get key)
  match r3 with
  | [.value _ _ v, .end_] =>
    let s := String.ofList (v.toList.map (fun b => Char.ofNat b.toNat))
    if s = "v1" then IO.println "  ✓ get still returns v1 (add didn't overwrite)"
    else IO.println s!"  ✗ get returned {s}"; ok := false
  | rs => IO.println s!"  ✗ get reply: {repr rs}"; ok := false
  return ok

def testEndToEndScript : IO Bool := do
  IO.println "\n=== end-to-end script: parse → apply → serialize ==="
  let mut ok := true
  let inputStr := "set foo 0 0 5\r\nhello\r\nget foo\r\ndelete foo\r\nget foo\r\n"
  let input := strBytes inputStr
  let commands := parseAll input
  IO.println s!"  parsed {commands.length} commands"
  if commands.length ≠ 4 then
    IO.println s!"  ✗ expected 4 commands"
    ok := false

  let (_, replyBytes) := runScript {} commands
  let replyStr := String.ofList (replyBytes.map (fun b => Char.ofNat b.toNat))
  IO.println s!"  reply stream ({replyBytes.length} bytes):"
  IO.println s!"    {repr replyStr}"

  -- Expected sequence:
  --   STORED\r\n
  --   VALUE foo 0 5\r\nhello\r\nEND\r\n
  --   DELETED\r\n
  --   END\r\n
  let expected := "STORED\r\nVALUE foo 0 5\r\nhello\r\nEND\r\nDELETED\r\nEND\r\n"
  if replyStr = expected then
    IO.println "  ✓ reply byte stream matches expected memcached protocol"
  else
    IO.println s!"  ✗ reply mismatch"
    IO.println s!"    expected: {repr expected}"
    ok := false

  return ok

def main : IO Unit := do
  IO.println "╔════════════════════════════════════════════╗"
  IO.println "║  memcached oracle (parser + KV reference) ║"
  IO.println "╚════════════════════════════════════════════╝"
  let results ← [
    testParseGet, testParseSet, testParseDelete,
    testKvBasicSet, testKvDeleteThenGet, testKvAddSemantics,
    testEndToEndScript
  ].mapM id
  if results.all id then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.MemcachedOracleTest

import Sparkle

/-! # `getWireWidth` and a stale `sparkleWireWidthCache` entry: reproduction

`CompilerM.getWireWidth` (`Sparkle/Compiler/Elab.lean` 210–233) answers from
the global `IO.Ref` `sparkleWireWidthCache` (wire NAME → width) BEFORE it
looks at the builder state. Wire names are allocated per builder state
(`CircuitM.freshName`: `_tmp_{hint}_{counter}`, the counter is a field of
`CircuitState`), so the same name recurs in every module, and again after a
rollback (a `catch` in `CompilerM` restores the builder state, counter
included, but not the `IO.Ref`).

What this file shows, with the REAL helpers (`CompilerM.makeWire`,
`CompilerM.getWireWidth`, a real `try … catch`), each from `CircuitM.init`:

* **R1 — rollback, then the name again with a symbolic width.** A wire
  `t : bitVector 16` is allocated inside a `try` that then fails; the `catch`
  rolls the builder back. The same name is allocated again as `bitVectorDim
  N`. `makeWire` writes the cache only for a concrete width
  (`legacyCacheWidth?`), so the entry `16` of the rolled-back wire stays. The
  ASSERTION is about that state: the cache says 16 for a name the current
  builder declares with another type. What `getWireWidth` then returns is
  LOGGED: `returned 16` is the stale read (a lookup that reads the builder
  first throws "symbolic width" there).
* **R2 — a name the current builder does not declare.** A wire allocated in
  builder A; a fresh builder B (what the legacy arm starts from after the
  machine arm declined: `CircuitM.init` with no cache reset in between) asks
  for that name. Logged: the cache's width, where the builder knows nothing
  (the fallback for an unknown name is 8).
* **R3 — rollback, then the name again with a concrete width.** Logged: the
  new width. `makeWire` overwrites the entry at allocation, which is why a
  stale width is not read for a wire declared with a concrete type.

**NOT reached through a real run of the entry.** By reading (not proved): a
stale read of a DECLARED name needs the redeclaration to skip the cache,
i.e. a symbolic width (R1), after a failed attempt whose `catch` goes on
without `restoreWireCaches`, or in a second builder of the same entry run.
The inline attempts' catches restore the cache (`tryInlineUnfold`, 6276–6297);
the other catches of the translator block wrap no wire allocation (6330,
6395, 6942–6947, 7079–7084, 7257, 7751, 7857) or re-throw (6509, 6521); the
second builder exists only after the machine arm declined, which is never
attempted in symbolic mode (5287); nested entries reset the cache on entry
and restore the parent's on exit (5484, 5508). So the sequences here are
driven by hand on the real helpers; no declaration is exhibited whose
compile reads a stale width.

The test throws only if the asserted STATE of R1 is not reached. -/

open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Type

namespace Sparkle.Tests.Compiler.WireWidthStaleTest

/-- The declared type of `name` in a module, printed; `"<not declared>"`. -/
def declaredType (m : Sparkle.IR.AST.Module) (name : String) : String :=
  match (m.wires ++ m.inputs ++ m.outputs).find? (fun p => p.name == name) with
  | some p => (repr p.ty).pretty
  | none => "<not declared>"

/-- `getWireWidth`, with a failure reported instead of propagated. -/
def readWidth (name : String) : CompilerM String := do
  try
    let k ← CompilerM.getWireWidth name
    pure s!"returned {k}"
  catch _ => pure "THREW"

/-- Allocate `t : ty` and then fail; the `catch` rolls the builder back. The
name the failed attempt allocated is left in `seen`. -/
def failedAttempt (seen : IO.Ref String) (ty : HWType) : CompilerM Unit := do
  try
    let a ← CompilerM.makeWire "t" ty
    CompilerM.liftMetaM (seen.set a : IO Unit)
    CompilerM.liftMetaM (throwError "injected late failure" : MetaM Unit)
  catch _ => pure ()

run_cmd Lean.Elab.Command.liftTermElabM do
  -- R1: rollback, then the same name with a symbolic width
  (sparkleWireWidthCache.set {} : IO Unit)
  let seen1 ← IO.mkRef ""
  let r1 : CompilerM (String × String) := do
    failedAttempt seen1 (.bitVector 16)
    let b ← CompilerM.makeWire "t" (.bitVectorDim (.parameter "N"))
    let k ← readWidth b
    pure (b, k)
  let ((b1, k1), fin1) ← (r1 {}).run (CircuitM.init "StaleR1")
  let a1 ← (seen1.get : IO _)
  let cache1 ← (sparkleWireWidthCache.get : IO _)
  let ty1 := declaredType fin1.module b1
  logInfo m!"WIREWIDTH STALE R1: the failed attempt allocated {a1} : bitVector 16 and was rolled back; the name allocated next is {b1}, declared {ty1}; the cache holds {repr (cache1.get? b1)} for it; getWireWidth {b1}: {k1} (a stale read is 'returned 16'; a builder-first lookup throws: the width is symbolic)"
  -- R2: a name the current builder does not declare
  (sparkleWireWidthCache.set {} : IO Unit)
  let rA : CompilerM String := CompilerM.makeWire "t" (.bitVector 16)
  let (a2, _) ← (rA {}).run (CircuitM.init "StaleR2A")
  let rB : CompilerM String := readWidth a2
  let (k2, fin2) ← (rB {}).run (CircuitM.init "StaleR2B")
  logInfo m!"WIREWIDTH STALE R2: builder A allocated {a2} : bitVector 16; in a FRESH builder B the name is {declaredType fin2.module a2}; getWireWidth {a2} there: {k2} (the fallback for a name unknown to both the cache and the builder is 8)"
  -- R3: rollback, then the same name with a concrete width
  (sparkleWireWidthCache.set {} : IO Unit)
  let seen3 ← IO.mkRef ""
  let r3 : CompilerM (String × String) := do
    failedAttempt seen3 (.bitVector 16)
    let b ← CompilerM.makeWire "t" (.bitVector 4)
    let k ← readWidth b
    pure (b, k)
  let ((b3, k3), fin3) ← (r3 {}).run (CircuitM.init "StaleR3")
  let a3 ← (seen3.get : IO _)
  logInfo m!"WIREWIDTH STALE R3: the failed attempt allocated {a3} : bitVector 16 and was rolled back; the name allocated next is {b3}, declared {declaredType fin3.module b3}; getWireWidth {b3}: {k3} (expected 'returned 4': makeWire overwrites the entry)"
  (sparkleWireWidthCache.set {} : IO Unit)
  -- THE ASSERTION (R1's state): the cache holds the rolled-back wire's width
  -- for a name the current builder declares with another type
  unless a1 == b1 && cache1.get? b1 == some 16 && ty1 != (repr (HWType.bitVector 16)).pretty &&
      ty1 != "<not declared>" do
    throwError "WIREWIDTH STALE: the stale state of R1 was not reached (failed attempt's name {a1}, reallocated name {b1}, cache {repr (cache1.get? b1)}, declared {ty1})"

end Sparkle.Tests.Compiler.WireWidthStaleTest

/-
  Bundle `unsolved` of the U1 coverage work: which generated script a module's registers call for.

  The single-register script (`scriptFor`, `some (r, w)`) unfolds `Signal.register`; a declaration
  built by `circuit do` (`Signal.reg`) is a `Signal.loop` even with ONE register, and needs the
  loop script (`loopScriptFor`).  Untrusted routing only: the kernel checks whatever script runs.
-/
import Lean

namespace Tools.VedU1Uns
open Lean

/-- Does the declaration `decl`, or one of the helper definitions its body mentions, mention
`Signal.loop`? -/
def usesLoop (decl : Name) (helpers : Array Name) : CoreM Bool := do
  let env ← getEnv
  for n in #[decl] ++ helpers do
    if let some (.defnInfo di) := env.find? n then
      if di.value.getUsedConstants.contains `Sparkle.Core.Signal.Signal.loop then return true
  return false

end Tools.VedU1Uns

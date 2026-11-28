import Tests.Compiler.SilentWireProbe
import Tests.Compiler.SilentWireProbeSymbolic
import Tests.Compiler.SilentWireProbeLib

namespace Sparkle.Tests.Compiler.SilentWireProbe
#probeSummary
end Sparkle.Tests.Compiler.SilentWireProbe

/-- Prints one verdict per probe (see notes/compiler/silent-wire-audit.md).
    Always exits 0: an (a) verdict is a finding, not a build failure. -/
def main : IO Unit := do
  IO.println "silent-wire probes (a = silently wrong, b = refused, c = correct, d = unclear)"
  for v in Sparkle.Tests.Compiler.SilentWireProbe.allVerdicts do
    IO.println s!"  {v}"

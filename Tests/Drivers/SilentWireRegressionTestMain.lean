import Tests.Compiler.SilentWireProbe
import Tests.Compiler.SilentWireProbeSymbolic
import Tests.Compiler.SilentWireProbeLib
import Tests.Compiler.SilentWireRegressionTest

namespace Sparkle.Tests.Compiler.SilentWireProbe
#probeSummary
end Sparkle.Tests.Compiler.SilentWireProbe

def main : IO UInt32 :=
  Sparkle.Tests.Compiler.SilentWireRegression.run Sparkle.Tests.Compiler.SilentWireProbe.allVerdicts

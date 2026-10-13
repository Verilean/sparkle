import Sparkle

/-! # Tagged module names through the REAL `#sim` command

Elaborated by `scripts/shipping-coverage/tagged_names_sim.sh`; not part of
any library. Each case is the command `#sim` itself on a declaration whose
module name is tagged (or whose file name is derived from a name `#sim`
does not keep apart). The command writes
`.lake/build/gen/sim/<ns>_jit.c` and `<ns>.sv`, with
`<ns>` = the LAST component of the declaration name, every character other
than an ASCII letter, a digit or `_` replaced by `_`
(`Sparkle/Compiler/Elab.lean`, `simLeanIdent`).

The driver reads the log between the `START` and `END` lines of a case
(errors of that case), then compiles the C file the case left behind with
the flags of `Sparkle.Core.JIT.compile`.

A failing case is EXPECTED to print a Lean error and the process to exit
with 1; the cases are independent commands. If a case fails after its
`namespace <ns>.Sim` was opened, that namespace stays open for the rest of
the file; every later case names root declarations only, so they still
resolve. WRITTEN, not run. -/

open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

@[hardware_module]
private def tnzPrivKid (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 13#8 : Signal defaultDomain (BitVec 8))

def tnzPrivTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  tnzPrivKid x + x

def «module» (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 3#8 : Signal defaultDomain (BitVec 8))

def «1bad» (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 7#8 : Signal defaultDomain (BitVec 8))

def «tnzé» (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 16#8 : Signal defaultDomain (BitVec 8))

def «tnzè» (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 32#8 : Signal defaultDomain (BitVec 8))

-- a private declaration as the top: ns `tnzPrivKid`
#eval IO.println "TAGGEDNAMES-SIMCMD privself START"
#sim tnzPrivKid
#eval IO.println "TAGGEDNAMES-SIMCMD privself END"

-- a parent of a private (tagged) child: ns `tnzPrivTop`
#eval IO.println "TAGGEDNAMES-SIMCMD priv START"
#sim tnzPrivTop
#eval IO.println "TAGGEDNAMES-SIMCMD priv END"

-- two declarations whose last components differ in one non-ASCII character:
-- ns `tnz_` for both
#eval IO.println "TAGGEDNAMES-SIMCMD uni1 START"
#sim «tnzé»
#eval IO.println "TAGGEDNAMES-SIMCMD uni1 END"

#eval IO.println "TAGGEDNAMES-SIMCMD uni2 START"
#sim «tnzè»
#eval IO.println "TAGGEDNAMES-SIMCMD uni2 END"

-- a keyword: ns `module`
#eval IO.println "TAGGEDNAMES-SIMCMD kw START"
#sim «module»
#eval IO.println "TAGGEDNAMES-SIMCMD kw END"

-- digit-initial: ns `1bad`
#eval IO.println "TAGGEDNAMES-SIMCMD dig START"
#sim «1bad»
#eval IO.println "TAGGEDNAMES-SIMCMD dig END"

import Sparkle

/-! # Tagged module names through the REAL `#sim` command

Elaborated by `scripts/shipping-coverage/tagged_names_sim.sh`; not part of
any library. Each case is the command `#sim` itself on a declaration whose
module name is tagged (or whose file name is derived from a name `#sim`
did not keep apart). Before the J5 fix the command wrote
`.lake/build/gen/sim/<ns>_jit.c` and `<ns>.sv`, with
`<ns>` = the LAST component of the declaration name, every character other
than an ASCII letter, a digit or `_` replaced by `_`. Since the fix
(`Sparkle/Compiler/SimNames.lean`) the stem is `declFileKey` of the
declaration (its module name) and the namespace is the qualified name, each
component between `«` and `»`: every case below is expected to elaborate
without an error (`uni2`, `kw` and `dig` were refused or collided before).

The driver reads the log between the `START` and `END` lines of a case
(errors of that case), then compiles the C file the case left behind with
the flags of `Sparkle.Core.JIT.compile`.

The cases are independent commands. A case that fails restores the scopes
(the command's `finally`), so the later cases are not affected.
WRITTEN, not run. -/

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

-- a private declaration as the top: namespace `tnzPrivKid.Sim`, PRIVATE wrappers,
-- stem `Sp$D$__private$<main module>$_0$tnzPrivKid`
#eval IO.println "TAGGEDNAMES-SIMCMD privself START"
#sim tnzPrivKid
#eval IO.println "TAGGEDNAMES-SIMCMD privself END"

-- a parent of a private (tagged) child: ns `tnzPrivTop`
#eval IO.println "TAGGEDNAMES-SIMCMD priv START"
#sim tnzPrivTop
#eval IO.println "TAGGEDNAMES-SIMCMD priv END"

-- two declarations whose last components differ in one non-ASCII character:
-- before, ns `tnz_` for both; now `«tnzé».Sim` / `«tnzè».Sim`, stems
-- `Sp$D$tnz_233_` / `Sp$D$tnz_232_`
#eval IO.println "TAGGEDNAMES-SIMCMD uni1 START"
#sim «tnzé»
#eval IO.println "TAGGEDNAMES-SIMCMD uni1 END"

#eval IO.println "TAGGEDNAMES-SIMCMD uni2 START"
#sim «tnzè»
#eval IO.println "TAGGEDNAMES-SIMCMD uni2 END"

-- a keyword: namespace `«module».Sim`, stem `Sp$D$module`
#eval IO.println "TAGGEDNAMES-SIMCMD kw START"
#sim «module»
#eval IO.println "TAGGEDNAMES-SIMCMD kw END"

-- digit-initial: namespace `«1bad».Sim` (before: a parse error), stem `Sp$D$1bad`
#eval IO.println "TAGGEDNAMES-SIMCMD dig START"
#sim «1bad»
#eval IO.println "TAGGEDNAMES-SIMCMD dig END"

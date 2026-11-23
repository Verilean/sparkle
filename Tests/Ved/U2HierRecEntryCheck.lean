import Tests.Ved.MultiOutCheck
import Tools.VedU2HierRecPar

/-!
# Nested toy through the entry (CANDIDATE; Tools/VedU2HierRec*.lean)
-/

namespace Tests.Ved.RecEntry

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil
open Tests.Ved.MultiOutCheck

/-- a struct middle module (2 outputs, one register of its own) that instantiates the sequential struct child `kidr` -/
@[hardware_module] def midn {dom : DomainConfig} (x y : Signal dom (BitVec 4)) : P2 dom :=
  circuit do
    let r ← Signal.reg 0#4
    let rS := (r : Signal dom (BitVec 4))
    let c := kidr x y
    r <~ (rS + c.s : Signal dom (BitVec 4))
    return ({ s := rS, d := c.d } : P2 dom)

/-- the top: a register feeds the middle module -/
def topn (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let c := midn accS inp
    acc <~ (c.s - c.d : Signal defaultDomain (BitVec 4))
    return accS

#eval show CommandElabM Unit from do
  let (m, d) ← synthOf ``topn
  logInfo m!"top: {repr m.body}\nmodules: {d.modules.map (·.name)}"
  for cm in d.modules do
    logInfo m!"{cm.name}: outputs {cm.outputs.map (·.name)} body {repr cm.body}"

end Tests.Ved.RecEntry

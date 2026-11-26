import Tools.VedU2HierRegEntry
import Tests.Ved.ComposeCheckUtil
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for `ved.sseq.dwLemma` on a SEVEN-output sequential struct child (sparkle-ved-multiout unit 9)

`chainW` is a sequential struct child with two registers, a 12-wire chain of `+` / `^^^` and seven output ports read from the
last wires (the shape of R184's `wPointOp`: 7 outputs over a long chain of wires, at 560 statements instead of 36).  Its child
theorem (`stmtOfStruct` + `checkU1E`, as the multi-output child loop, `ved.sseq.fastOrder` on) is accepted both with the default
script and with `ved.sseq.dwLemma` (the input widths of the module for `hin` by ONE closed `decide +kernel` instead of `simp` unfolding the
module and `declWidth` at `hin hrst`): type `U1Stmt`, std3, no `sorryAx`.  The option changes only the generated script; the statement is
the same.  The cost on R184's `wPointOp` (82 s at `hin hrst`) and the refusal of the real child are in docs/VED-COMPOSE-CONNECT.md, unit 22.
-/

namespace Tests.Ved.U1StructWireCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil

structure P7 (dom : DomainConfig) where
  o0 : Signal dom (BitVec 8)
  o1 : Signal dom (BitVec 8)
  o2 : Signal dom (BitVec 8)
  o3 : Signal dom (BitVec 8)
  o4 : Signal dom (BitVec 8)
  o5 : Signal dom (BitVec 8)
  o6 : Signal dom (BitVec 8)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (P7 dom) dom := ⟨⟩

@[hardware_module] def chainW {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : P7 dom :=
  circuit do
    let r ← Signal.reg 0#8
    let q ← Signal.reg 1#8
    let rS := (r : Signal dom (BitVec 8))
    let qS := (q : Signal dom (BitVec 8))
    let w1 := (y ^^^ y : Signal dom (BitVec 8))
    let w2 := (w1 + rS : Signal dom (BitVec 8))
    let w3 := (w2 ^^^ qS : Signal dom (BitVec 8))
    let w4 := (w3 + x : Signal dom (BitVec 8))
    let w5 := (w4 ^^^ y : Signal dom (BitVec 8))
    let w6 := (w5 + rS : Signal dom (BitVec 8))
    let w7 := (w6 ^^^ qS : Signal dom (BitVec 8))
    let w8 := (w7 + x : Signal dom (BitVec 8))
    let w9 := (w8 ^^^ y : Signal dom (BitVec 8))
    let w10 := (w9 + rS : Signal dom (BitVec 8))
    let w11 := (w10 ^^^ qS : Signal dom (BitVec 8))
    let w12 := (w11 + x : Signal dom (BitVec 8))
    r <~ w12
    q <~ w6 + rS
    return ({ o0 := w12, o1 := w11, o2 := w10, o3 := w9, o4 := w8, o5 := w7, o6 := w6 } : P7 dom)

def topW (inp inp2 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let c := chainW inp2 inp
    acc <~ (c.o0 - c.o1 + c.o2 - c.o3 + c.o4 - c.o5 + c.o6 : Signal defaultDomain (BitVec 8))
    return accS

def wireCheck (tag : String) (dw : Bool) : CommandElabM Unit := do
  let (_, d) ← synthOf ``topW
  let some cm := d.modules.head? | throwError "no child"
  liftTermElabM do
    withOptions (fun o => (o.setBool `ved.sseq.fastOrder true).setBool `ved.sseq.dwLemma dw) do
      let (b, _, names) ← Tools.VedU1StructOut.stmtOfStruct ``chainW
      unless names.length == 7 do throwError "expected 7 output ports, got {names}"
      let thm ← Tools.VedU1Entry.checkU1E ``chainW (``chainW ++ Name.mkSimple tag) b cm .generated names
      let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
      unless ti.type.getAppFn.isConstOf ``Tools.VedU1Contract.U1Stmt do throwError "{thm}: type is not U1Stmt"
      let axs ← collectAxioms thm
      unless axs.all (std3.contains ·) do throwError "{thm}: axioms outside std3: {axs}"
      if axs.contains ``sorryAx then throwError "{thm}: sorryAx"
      logInfo m!"CHILD THEOREM chainW (7 outputs, 12 wires) dwLemma={dw}: {thm} U1Stmt, std3, no sorryAx"

#eval wireCheck "ved_dw0" false
#eval wireCheck "ved_dw1" true

end Tests.Ved.U1StructWireCheck

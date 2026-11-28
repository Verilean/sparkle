import Tools.VedU2HierRegEntry
import Tests.Ved.ComposeCheckUtil
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for the struct child script options `ved.sseq.fastOrder` + `ved.sseq.share` on a generated chain
(sparkle-ved-multiout unit 8; heavy cases live here, not in `Tests/Ved/MultiOutCheck.lean`)

`chainS` is a sequential 2-output struct child with two registers and a 20-wire chain of `+` / `^^^` (54 statements of the
generated module).  Its child theorem (`stmtOfStruct` + `checkU1E`, as the multi-output child loop) is accepted with
`ved.sseq.fastOrder` and `ved.sseq.share` both on (the packing stage is `ved_ss_pack_share`: `ved_pack_wire` per goal with a
heartbeat budget of its own, `ved_wire_bits` as the fallback), type `U1Stmt`, std3, no `sorryAx`, and the leaf fast order
lemma is used.  Candidate option for R184 `wScalarMul` (class (b): the packing stage reads DAGs of at most 579 nodes as trees
of up to 85.6k nodes); the real child is NOT accepted by it (notes/ved/VED-COMPOSE-CONNECT.md, unit 21).
-/

namespace Tests.Ved.U1StructShareCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil

structure P2 (dom : DomainConfig) where
  s : Signal dom (BitVec 8)
  d : Signal dom (BitVec 8)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (P2 dom) dom := ⟨⟩

@[hardware_module] def chainS {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : P2 dom :=
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
    let w13 := (w12 ^^^ y : Signal dom (BitVec 8))
    let w14 := (w13 + rS : Signal dom (BitVec 8))
    let w15 := (w14 ^^^ qS : Signal dom (BitVec 8))
    let w16 := (w15 + x : Signal dom (BitVec 8))
    let w17 := (w16 ^^^ y : Signal dom (BitVec 8))
    let w18 := (w17 + rS : Signal dom (BitVec 8))
    let w19 := (w18 ^^^ qS : Signal dom (BitVec 8))
    let w20 := (w19 + x : Signal dom (BitVec 8))
    r <~ w20
    q <~ w10 + rS
    return ({ s := w20, d := w10 - qS } : P2 dom)

def topS (inp inp2 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let c := chainS inp2 inp
    acc <~ (c.s - c.d : Signal defaultDomain (BitVec 8))
    return accS


def shareCheck (tag : String) (fo sh : Bool) : CommandElabM Unit := do
  let (_, d) ← synthOf ``topS
  let some cm := d.modules.head? | throwError "no child"
  liftTermElabM do
    withOptions (fun o => (o.setBool `ved.sseq.fastOrder fo).setBool `ved.sseq.share sh) do
      let (b, _, names) ← Tools.VedU1StructOut.stmtOfStruct ``chainS
      let thm ← Tools.VedU1Entry.checkU1E ``chainS (``chainS ++ Name.mkSimple tag) b cm .generated names
      let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
      unless ti.type.getAppFn.isConstOf ``Tools.VedU1Contract.U1Stmt do throwError "{thm}: type is not U1Stmt"
      let axs ← collectAxioms thm
      unless axs.all (std3.contains ·) do throwError "{thm}: axioms outside std3: {axs}"
      if axs.contains ``sorryAx then throwError "{thm}: sorryAx"
      let usesFast := (ti.value.getUsedConstants.contains ``Tools.VedU1OrderFast.orderOkLeafFast_sound)
      unless usesFast == fo do throwError "{thm}: orderOkLeafFast_sound used = {usesFast}, option = {fo}"
      logInfo m!"CHILD THEOREM chainS (54 statements) fastOrder={fo} share={sh}: {thm} U1Stmt, std3, no sorryAx, orderOkLeafFast_sound used = {usesFast}"

#eval shareCheck "ved_fs" true true

end Tests.Ved.U1StructShareCheck

import Tools.VedU2HierRegEntry
import Tests.Ved.ComposeCheckUtil
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for `ved.sseq.wires` (sparkle-ved-multiout unit 10): the struct sequential script over a NAMED loop

`chainN` is a sequential struct child with THREE registers, a 6-wire chain of `+` / `-` and seven output ports (the shape of
R184's `wPointOp`).  Its child theorem (`stmtOfStruct` + `checkU1E`, `ved.sseq.fastOrder` on) is
accepted

* with the default script (option off, unchanged), and
* with `ved.sseq.wires` (`Tools/VedU1StructWires.lean`): the invariant is `∃ L, IsLoop F L ∧ ⋀ register_k = toNat (proj_k (L.val t))`,
  the per-cycle value lemma `hU : ∀ t, L.val (t+1) = (F L).val (t+1)` is proved once, the loop term is not repeated in every equation
  and output wire.  Type `U1Stmt`, std3, no `sorryAx`; the statement is the same.

Controls (option on): the statement of `chainN` against a module whose REGISTER UPDATE is wrong (`chainNR`: `q <~ w3 + qS` instead of `w3 + rS`), and against a
module whose OUTPUT WIRE is wrong (`chainNO`: port `o3` reads `w2` instead of `w3`) are refused by the checker (`VED U1 REFUSED`, observed stage pinned
below).  The scaling numbers and the cost on the real children are in docs/VED-COMPOSE-CONNECT.md, unit 23.
-/

namespace Tests.Ved.U1StructNamedCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil

structure PN (dom : DomainConfig) where
  o0 : Signal dom (BitVec 8)
  o1 : Signal dom (BitVec 8)
  o2 : Signal dom (BitVec 8)
  o3 : Signal dom (BitVec 8)
  o4 : Signal dom (BitVec 8)
  o5 : Signal dom (BitVec 8)
  o6 : Signal dom (BitVec 8)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (PN dom) dom := ⟨⟩

@[hardware_module] def chainN {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : PN dom :=
  circuit do
    let r ← Signal.reg 0#8
    let q ← Signal.reg 1#8
    let p ← Signal.reg 2#8
    let rS := (r : Signal dom (BitVec 8))
    let qS := (q : Signal dom (BitVec 8))
    let pS := (p : Signal dom (BitVec 8))
    let w1 := (y - y : Signal dom (BitVec 8))
    let w2 := (w1 + rS : Signal dom (BitVec 8))
    let w3 := (w2 - qS : Signal dom (BitVec 8))
    let w4 := (w3 + x : Signal dom (BitVec 8))
    let w5 := (w4 - y : Signal dom (BitVec 8))
    let w6 := (w5 + pS : Signal dom (BitVec 8))
    r <~ w6
    q <~ w3 + rS
    p <~ w5 + pS
    return ({ o0 := w6, o1 := w5, o2 := w4, o3 := w3, o4 := w2, o5 := w1, o6 := w6 } : PN dom)

/-- control: the register `q` is updated from `qS`, not from `rS` -/
@[hardware_module] def chainNR {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : PN dom :=
  circuit do
    let r ← Signal.reg 0#8
    let q ← Signal.reg 1#8
    let p ← Signal.reg 2#8
    let rS := (r : Signal dom (BitVec 8))
    let qS := (q : Signal dom (BitVec 8))
    let pS := (p : Signal dom (BitVec 8))
    let w1 := (y - y : Signal dom (BitVec 8))
    let w2 := (w1 + rS : Signal dom (BitVec 8))
    let w3 := (w2 - qS : Signal dom (BitVec 8))
    let w4 := (w3 + x : Signal dom (BitVec 8))
    let w5 := (w4 - y : Signal dom (BitVec 8))
    let w6 := (w5 + pS : Signal dom (BitVec 8))
    r <~ w6
    q <~ w3 + qS
    p <~ w5 + pS
    return ({ o0 := w6, o1 := w5, o2 := w4, o3 := w3, o4 := w2, o5 := w1, o6 := w6 } : PN dom)

/-- control: the output port `o3` reads `w8`, not `w9` -/
@[hardware_module] def chainNO {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : PN dom :=
  circuit do
    let r ← Signal.reg 0#8
    let q ← Signal.reg 1#8
    let p ← Signal.reg 2#8
    let rS := (r : Signal dom (BitVec 8))
    let qS := (q : Signal dom (BitVec 8))
    let pS := (p : Signal dom (BitVec 8))
    let w1 := (y - y : Signal dom (BitVec 8))
    let w2 := (w1 + rS : Signal dom (BitVec 8))
    let w3 := (w2 - qS : Signal dom (BitVec 8))
    let w4 := (w3 + x : Signal dom (BitVec 8))
    let w5 := (w4 - y : Signal dom (BitVec 8))
    let w6 := (w5 + pS : Signal dom (BitVec 8))
    r <~ w6
    q <~ w3 + rS
    p <~ w5 + pS
    return ({ o0 := w6, o1 := w5, o2 := w4, o3 := w2, o4 := w2, o5 := w1, o6 := w6 } : PN dom)

def topN (inp inp2 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let c := chainN inp2 inp
    acc <~ (c.o0 - c.o1 + c.o2 - c.o3 + c.o4 - c.o5 + c.o6 : Signal defaultDomain (BitVec 8))
    return accS

def topNR (inp inp2 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let c := chainNR inp2 inp
    acc <~ (c.o0 - c.o1 + c.o2 - c.o3 + c.o4 - c.o5 + c.o6 : Signal defaultDomain (BitVec 8))
    return accS

def topNO (inp inp2 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let c := chainNO inp2 inp
    acc <~ (c.o0 - c.o1 + c.o2 - c.o3 + c.o4 - c.o5 + c.o6 : Signal defaultDomain (BitVec 8))
    return accS

/-- the child theorem of `chainN`'s statement against the module synthesised from `top`'s child (the checker's `checkU1E`) -/
def childRun (top : Name) (tag : String) (wires : Bool) : CommandElabM (Option String × Option Name) := do
  let (_, d) ← synthOf top
  let some cm := d.modules.head? | throwError "no child module of {top}"
  liftTermElabM do
    withOptions (fun o => (o.setBool `ved.sseq.fastOrder true).setBool `ved.sseq.wires wires) do
      let (b, _, names) ← Tools.VedU1StructOut.stmtOfStruct ``chainN
      unless names.length == 7 do throwError "expected 7 output ports, got {names}"
      try
        let thm ← Tools.VedU1Entry.checkU1E ``chainN (``chainN ++ Name.mkSimple tag) b cm .generated names
        return (none, some thm)
      catch e => return (some (← e.toMessageData.toString), none)

def accepted (tag : String) (wires : Bool) : CommandElabM Unit := do
  let (msg, thm?) ← childRun ``topN tag wires
  let some thm := thm? | throwError "chainN (wires={wires}) refused: {msg.getD ""}"
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type.getAppFn.isConstOf ``Tools.VedU1Contract.U1Stmt do throwError "{thm}: type is not U1Stmt"
    let axs ← collectAxioms thm
    unless axs.all (std3.contains ·) do throwError "{thm}: axioms outside std3: {axs}"
    if axs.contains ``sorryAx then throwError "{thm}: sorryAx"
    logInfo m!"CHILD THEOREM chainN (3 registers, 7 outputs, 6 wires) wires={wires}: {thm} U1Stmt, std3, no sorryAx"

def refused (top : Name) (tag : String) (what : String) (stages : List String) : CommandElabM Unit := do
  let (msg?, thm?) ← childRun top tag true
  if thm?.isSome then throwError "control ({what}): the checker ACCEPTED a wrong module"
  let some msg := msg? | throwError "control ({what}): neither refused nor accepted"
  unless stages.any (fun st => msg.startsWith s!"VED U1 REFUSED {``chainN} [{st}]") do
    throwError "control ({what}): unexpected refusal: {msg.take 300}"
  logInfo m!"CONTROL {what}: refused (observed stage), {msg.take 160}"

#eval accepted "ved_nm0" false
#eval accepted "ved_nm1" true
#eval refused ``topNR "ved_nmR" "wrong register update" ["proof"]
#eval refused ``topNO "ved_nmO" "wrong output wire" ["proof"]


/-! ## Unit 11: `ved.sseq.slice`, `ved.sseq.zeta`, `ved.sseq.ratio` (slice lemmas of the packed register file, non-recursive zeta)

`chainN` again with the three options on (accepted, `U1Stmt`, std3, no `sorryAx`), `chainW` (registers of WIDTHS 8, 4, 8: the pack shape
`A % 256 * 2^12 + B % 2^12`, then `A % 16 * 2^8 + B % 2^8`) with the options on, the two wrong modules of unit 10 with the options on (refused at
`[proof]`), and the lemma-level controls: a wrong width / wrong modulus in a slice statement is REFUTED. -/

structure PW (dom : DomainConfig) where
  a : Signal dom (BitVec 8)
  b : Signal dom (BitVec 4)
  c : Signal dom (BitVec 8)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (PW dom) dom := ⟨⟩

@[hardware_module] def chainW {dom : DomainConfig} (x : Signal dom (BitVec 8)) (z : Signal dom (BitVec 4)) : PW dom :=
  circuit do
    let r ← Signal.reg 0#8
    let q ← Signal.reg 1#4
    let p ← Signal.reg 2#8
    let rS := (r : Signal dom (BitVec 8))
    let qS := (q : Signal dom (BitVec 4))
    let pS := (p : Signal dom (BitVec 8))
    let w1 := (x + rS : Signal dom (BitVec 8))
    let w2 := (w1 - pS : Signal dom (BitVec 8))
    let w3 := (qS + z : Signal dom (BitVec 4))
    r <~ w2
    q <~ w3
    p <~ w1 + pS
    return ({ a := w2, b := w3, c := w1 } : PW dom)

def topW (inp : Signal defaultDomain (BitVec 8)) (inz : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let c := chainW inp inz
    acc <~ (c.a - c.c : Signal defaultDomain (BitVec 8))
    return accS

def u11Opts : List (Name × Bool) :=
  [(`ved.sseq.fastOrder, true), (`ved.sseq.wires, true), (`ved.sseq.slice, true), (`ved.sseq.zeta, true), (`ved.sseq.ratio, false)]

def childRunU (child : Name) (n : Nat) (top : Name) (tag : String) (opts : List (Name × Bool)) :
    CommandElabM (Option String × Option Name) := do
  let (_, d) ← synthOf top
  let some cm := d.modules.head? | throwError "no child module of {top}"
  liftTermElabM do
    withOptions (fun o => opts.foldl (fun o p => o.setBool p.1 p.2) o) do
      let (b, _, names) ← Tools.VedU1StructOut.stmtOfStruct child
      unless names.length == n do throwError "expected {n} output ports, got {names}"
      try
        let thm ← Tools.VedU1Entry.checkU1E child (child ++ Name.mkSimple tag) b cm .generated names
        return (none, some thm)
      catch e => return (some (← e.toMessageData.toString), none)

def acceptedU (child : Name) (n : Nat) (top : Name) (tag : String) (opts : List (Name × Bool)) : CommandElabM Unit := do
  let (msg, thm?) ← childRunU child n top tag opts
  let some thm := thm? | throwError "{child} (options {opts}) refused: {msg.getD ""}"
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type.getAppFn.isConstOf ``Tools.VedU1Contract.U1Stmt do throwError "{thm}: type is not U1Stmt"
    let axs ← collectAxioms thm
    unless axs.all (std3.contains ·) do throwError "{thm}: axioms outside std3: {axs}"
    if axs.contains ``sorryAx then throwError "{thm}: sorryAx"
    logInfo m!"CHILD THEOREM {child} (slice+zeta+wires+ratio false): {thm} U1Stmt, std3, no sorryAx"

def refusedU (top : Name) (tag : String) (what : String) : CommandElabM Unit := do
  let (msg?, thm?) ← childRunU ``chainN 7 top tag u11Opts
  if thm?.isSome then throwError "control ({what}): the checker ACCEPTED a wrong module"
  let some msg := msg? | throwError "control ({what}): neither refused nor accepted"
  unless msg.startsWith s!"VED U1 REFUSED {``chainN} [proof]" do
    throwError "control ({what}): unexpected refusal: {msg.take 300}"
  logInfo m!"CONTROL {what} (slice+zeta on): refused at [proof], {msg.take 160}"

#eval acceptedU ``chainN 7 ``topN "ved_u11a" u11Opts
#eval acceptedU ``chainW 3 ``topW "ved_u11w" u11Opts
#eval acceptedU ``chainW 3 ``topW "ved_u11w0" [(`ved.sseq.fastOrder, true)]
#eval refusedU ``topNR "ved_u11R" "wrong register update"
#eval refusedU ``topNO "ved_u11O" "wrong output wire"

open Tools.VedU1StructSlice in
/-- lemma-level controls: the slice statements with a wrong register width / modulus / index are FALSE (so no such lemma can be
supplied), the right ones are the three lemmas -/
example : ¬ (∀ A B : Nat, (A % 256 * 65536 + B % 65536) / 65536 = A % 255) := by
  intro h; have := h 255 0; revert this; decide

example : ¬ (∀ A B : Nat, (A % 256 * 65536 + B % 65536) % 65536 = A % 65536) := by
  intro h; have := h 1 0; revert this; decide

example : ¬ (∀ A B : Nat, (A % 256 * 65536 + B % 65536) / 256 = A % 256) := by
  intro h; have := h 1 0; revert this; decide

example (A B : Nat) : (A % 256 * 65536 + B % 65536) / 65536 = A % 256 := Tools.VedU1StructSlice.ved_slice_div A B 256 65536 (by decide)
example (A B : Nat) : (A % 256 * 65536 + B % 65536) % 65536 = B % 65536 := Tools.VedU1StructSlice.ved_slice_mod A B 256 65536
example (A B : Nat) : (A % 256 * 65536 + B % 65536) % 16777216 = A % 256 * 65536 + B % 65536 :=
  Tools.VedU1StructSlice.ved_slice_modM A B 256 65536 16777216 (by decide) (by decide)

end Tests.Ved.U1StructNamedCheck

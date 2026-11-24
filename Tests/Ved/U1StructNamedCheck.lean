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

/-! ## Unit 12: `ved.sseq.wireEqs` (per-wire value lemmas of the source value), `ved.sseq.wireK`, `ved.sseq.muxCond`

Positives: `chainN` (7 ports) and `chainW` (3 ports, widths 8/4/8) with the unit-11 options plus `wireEqs` (cut height 3, so that the small
modules do cut wires and loops: the value lemmas `hV_i` and the restoration run) plus `muxCond`; a theorem with std3 axioms, no `sorryAx`.
Controls: the wrong register update / the wrong output wire are still refused at `[proof]` with the options on (a wrong module cannot be
proved through the cut wires), option off = the unit-11 checks above (unchanged).  Lemma level: `ved_mux_val_cond` is the `cond` form of
`mux_val` (instantiated), and the swapped branches are not equal (refuted). -/

def u12Opts : List (Name × Bool) :=
  u11Opts ++ [(`ved.sseq.wireEqs, true), (`ved.sseq.muxCond, true)]

def childRunV (child : Name) (n : Nat) (top : Name) (tag : String) (opts : List (Name × Bool)) :
    CommandElabM (Option String × Option Name) := do
  let (_, d) ← synthOf top
  let some cm := d.modules.head? | throwError "no child module of {top}"
  liftTermElabM do
    withOptions (fun o => (opts.foldl (fun o p => o.setBool p.1 p.2) o).insert `ved.sseq.wireK (Lean.DataValue.ofNat 3)) do
      let (b, _, names) ← Tools.VedU1StructOut.stmtOfStruct child
      unless names.length == n do throwError "expected {n} output ports, got {names}"
      try
        let thm ← Tools.VedU1Entry.checkU1E child (child ++ Name.mkSimple tag) b cm .generated names
        return (none, some thm)
      catch e => return (some (← e.toMessageData.toString), none)

def acceptedV (child : Name) (n : Nat) (top : Name) (tag : String) (opts := u12Opts) : CommandElabM Unit := do
  let (msg, thm?) ← childRunV child n top tag opts
  let some thm := thm? | throwError "{child} (wireEqs+muxCond) refused: {msg.getD ""}"
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type.getAppFn.isConstOf ``Tools.VedU1Contract.U1Stmt do throwError "{thm}: type is not U1Stmt"
    let axs ← collectAxioms thm
    unless axs.all (std3.contains ·) do throwError "{thm}: axioms outside std3: {axs}"
    if axs.contains ``sorryAx then throwError "{thm}: sorryAx"
    logInfo m!"CHILD THEOREM {child} (wireEqs K=3 + muxCond + slice+zeta+wires): {thm} U1Stmt, std3, no sorryAx"

def refusedV (top : Name) (tag : String) (what : String) (opts := u12Opts) : CommandElabM Unit := do
  let (msg?, thm?) ← childRunV ``chainN 7 top tag opts
  if thm?.isSome then throwError "control ({what}): the checker ACCEPTED a wrong module"
  let some msg := msg? | throwError "control ({what}): neither refused nor accepted"
  unless msg.startsWith s!"VED U1 REFUSED {``chainN} [proof]" do
    throwError "control ({what}): unexpected refusal: {msg.take 300}"
  logInfo m!"CONTROL {what} (wireEqs+muxCond on): refused at [proof], {msg.take 160}"

#eval acceptedV ``chainN 7 ``topN "ved_u12a"
#eval acceptedV ``chainW 3 ``topW "ved_u12w"
#eval refusedV ``topNR "ved_u12R" "wrong register update"
#eval refusedV ``topNO "ved_u12O" "wrong output wire"

example {dom : Sparkle.Core.Domain.DomainConfig} (c : Sparkle.Core.Signal.Signal dom Bool) (a b : Sparkle.Core.Signal.Signal dom (BitVec 8)) (s : Nat) :
    (Sparkle.Core.Signal.Signal.mux c a b).val s = cond (c.val s) (a.val s) (b.val s) :=
  Tools.VedU1StructSlice.ved_mux_val_cond c a b s

/-- the `cond` form is not symmetric in its branches: a lemma with the branches swapped is false -/
example : ¬ (∀ (c a b : Bool), cond c a b = cond c b a) := by decide

/-! ## Unit 13: `ved.sseq.iteNorm` (closing stage tries the ite normal form first) and `ved_ss_R2` with the DAG loop walk

`iteNorm` on, together with the unit-12 options: the accepted children are still accepted (the normal-form step either closes a leaf or
falls back to the unchanged closing), the two wrong modules are still refused at `[proof]`. -/

def u13Opts : List (Name × Bool) := u12Opts ++ [(`ved.sseq.iteNorm, true)]

#eval acceptedV ``chainN 7 ``topN "ved_u13a" u13Opts
#eval acceptedV ``chainW 3 ``topW "ved_u13w" u13Opts
#eval refusedV ``topNR "ved_u13R" "wrong register update (iteNorm on)" u13Opts
#eval refusedV ``topNO "ved_u13O" "wrong output wire (iteNorm on)" u13Opts

/-- the two local facts `ved.sseq.iteNorm` rewrites with, on the shape of `faddMod` / `fsubMod` (`mux (ule p s) (s - p) s`): the flipped condition and the
operand order (`Nat.add_comm`, ordered) make the spec side and the module side the same term -/
example (x y p K M N : Nat) :
    (if p ≤ x + y then (K + (x + y)) % M else x + y) % N = (if x + y < p then x + y else (x + y + K) % M) % N := by
  simp only [← Nat.not_lt, ite_not, Nat.add_comm]

/-- control: the rewriting does not identify different branches -/
example : ¬ (∀ (x p K M N : Nat), (if p ≤ x then (K + x) % M else x) % N = (if x < p then (x + K) % M else x) % N) := by
  intro h
  have := h 5 1 3 100 1000
  simp at this

/-! ## Unit 14: `ved.sseq.kshape` (proof-carrying wrappers of core's `rfl` lemmas; kernel cost of a large literal added to a symbolic operand)

Core states `BitVec.toNat_add`, `BitVec.extractLsb'_toNat`, `Option.getD_some`, … by `rfl`; `simp` applies such a theorem without recording a proof
term (the kernel must then prove the difference by definitional unfolding, which evaluates `p ≤ x + p` one successor at a time).  The wrappers
`Tools.VedU1StructSlice.nr.<n>` have the type of `n` and the value `n`, so `simp` records the step.  Controls: (1) the core theorems ARE rfl theorems
and the wrappers are NOT; (2) each wrapper has exactly the type of its core theorem (no new proposition); (3) the accepted children are still accepted
and the wrong modules still refused with `kshape` on. -/

open Lean Meta in
#eval show CoreM Unit from do
  for n in Tools.VedU1StructSlice.kshapeNames do
    let w := Tools.VedU1StructSlice.nrName n
    let some ci := (← getEnv).find? n | throwError "{n} missing"
    let some cw := (← getEnv).find? w | throwError "{w} missing"
    unless ci.type == cw.type && ci.levelParams == cw.levelParams do throwError "wrapper {w}: type differs from {n}"
    unless ← isRflTheorem n do throwError "{n} is not a rfl theorem (the list is stale)"
    if ← isRflTheorem w then throwError "wrapper {w} is a rfl theorem"
    let ax ← Tools.VedStrictAudit.strictAudit w
    unless Tools.VedStrictAudit.showNames ax.axioms == Tools.VedStrictAudit.showNames (← Tools.VedStrictAudit.strictAudit n).axioms do
      throwError "wrapper {w}: axioms differ from {n}"
  logInfo m!"CONTROL kshape: {Tools.VedU1StructSlice.kshapeNames.length} wrappers: same type as the core rfl theorem, not rfl themselves, same axioms"

def u14Opts : List (Name × Bool) := u13Opts ++ [(`ved.sseq.kshape, true)]

#eval acceptedV ``chainN 7 ``topN "ved_u14a" u14Opts
#eval acceptedV ``chainW 3 ``topW "ved_u14w" u14Opts
#eval refusedV ``topNR "ved_u14R" "wrong register update (kshape on)" u14Opts
#eval refusedV ``topNO "ved_u14O" "wrong output wire (kshape on)" u14Opts

/-! ## Unit 28 (P2-1 remainder): the recovery handlers reached by a RUNTIME failure
`ved.sseq.ctlFail` (control only, default 0 = inert) gives one recovery site a heartbeat budget of 1: bit 1 = `ved_wire_bits`-first of
the ratio route of `ved_ss_pack_share` (the route is forced on the toy), bit 2 = the first per-wire hV simp of `ved_ss_wiresimp`, bit 4 = its
atoms simp once under the failing budget and then normally, bit 8 = its atoms simp only under the failing budget.  For each site the run must reach the handler (the counter `ctlReached`, independent of `VED_MS_LOG`), continue through the
state restore / fallback, and end as without the failure: the toy theorem is accepted (`U1Stmt`, std3, no `sorryAx`) and the wrong
modules (register update / output wire) are still refused at `[proof]`. -/

def ctlOpts (extra : List (Name × Bool)) (ctl : Nat) (o : Options) : Options :=
  ((extra.foldl (fun o p => o.setBool p.1 p.2) o).insert `ved.sseq.wireK (Lean.DataValue.ofNat 3)).insert `ved.sseq.ctlFail
    (Lean.DataValue.ofNat ctl)

/-- the child theorem run with `ctl`; the handler counters (reset before) are returned -/
def childRunC (child : Name) (n : Nat) (top : Name) (tag : String) (extra : List (Name × Bool)) (ctl : Nat) :
    CommandElabM ((Option String × Option Name) × Array Nat) := do
  let (_, d) ← synthOf top
  let some cm := d.modules.head? | throwError "no child module of {top}"
  Tools.VedU1StructSeqTac.ctlReached.set (Array.replicate 4 0)
  let r ← liftTermElabM do
    withOptions (ctlOpts extra ctl) do
      let (b, _, names) ← Tools.VedU1StructOut.stmtOfStruct child
      unless names.length == n do throwError "expected {n} output ports, got {names}"
      try
        let thm ← Tools.VedU1Entry.checkU1E child (child ++ Name.mkSimple tag) b cm .generated names
        return (none, some thm)
      catch e => return (some (← e.toMessageData.toString), none)
  return (r, ← Tools.VedU1StructSeqTac.ctlReached.get)

def acceptedC (child : Name) (n : Nat) (top : Name) (tag : String) (extra : List (Name × Bool)) (ctl : Nat) (sites : List Nat) :
    CommandElabM Unit := do
  let ((msg, thm?), cnt) ← childRunC child n top tag extra ctl
  for k in sites do
    unless cnt[k]! > 0 do throwError "ctlFail={ctl}: handler {k} not reached ({cnt})"
  if ctl == 0 then unless cnt.all (· == 0) do throwError "ctlFail=0: a handler ran ({cnt})"
  let some thm := thm? | throwError "{child} (ctlFail={ctl}) refused: {msg.getD ""}"
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type.getAppFn.isConstOf ``Tools.VedU1Contract.U1Stmt do throwError "{thm}: type is not U1Stmt"
    let axs ← collectAxioms thm
    unless axs.all (std3.contains ·) do throwError "{thm}: axioms outside std3: {axs}"
    if axs.contains ``sorryAx then throwError "{thm}: sorryAx"
    logInfo m!"CHILD THEOREM {child} ctlFail={ctl}: handlers reached {sites.map (fun k => decide (cnt[k]! > 0))}: {thm} U1Stmt, std3, no sorryAx"

def refusedC (top : Name) (tag : String) (extra : List (Name × Bool)) (ctl : Nat) (sites : List Nat) : CommandElabM Unit := do
  let ((msg?, thm?), cnt) ← childRunC ``chainN 7 top tag extra ctl
  for k in sites do
    unless cnt[k]! > 0 do throwError "ctlFail={ctl}: handler {k} not reached ({cnt})"
  if thm?.isSome then throwError "control (ctlFail={ctl}): the checker ACCEPTED a wrong module"
  let some msg := msg? | throwError "control (ctlFail={ctl}): neither refused nor accepted"
  unless msg.startsWith s!"VED U1 REFUSED {``chainN} [proof]" do
    throwError "control (ctlFail={ctl}): unexpected refusal: {msg.take 300}"
  logInfo m!"CONTROL ctlFail={ctl} {top}: handlers reached {sites.map (fun k => decide (cnt[k]! > 0))}, refused at [proof], {msg.take 160}"

def ctlShare : List (Name × Bool) := [(`ved.sseq.fastOrder, true), (`ved.sseq.share, true)]
def ctlWire : List (Name × Bool) := u12Opts

-- without the failure: the baseline, no handler runs
#eval acceptedC ``chainN 7 ``topN "ved_c0a" ctlShare 0 []
#eval acceptedC ``chainN 7 ``topN "ved_c0b" ctlWire 0 []
-- site 1: `ved_wire_bits`-first of the ratio route
#eval acceptedC ``chainN 7 ``topN "ved_c1a" ctlShare 1 [0]
#eval refusedC ``topNR "ved_c1R" ctlShare 1 [0]
#eval refusedC ``topNO "ved_c1O" ctlShare 1 [0]
-- site 2: the first per-wire hV simp (the wire stays unsimplified, the run continues)
#eval acceptedC ``chainN 7 ``topN "ved_c2a" ctlWire 2 [2]
#eval acceptedC ``chainW 3 ``topW "ved_c2w" ctlWire 2 [2]
#eval refusedC ``topNR "ved_c2R" ctlWire 2 [2]
#eval refusedC ``topNO "ved_c2O" ctlWire 2 [2]
-- site 3: the atoms simp, once under the failing budget (handler, state restored), then normally
#eval acceptedC ``chainN 7 ``topN "ved_c4a" ctlWire 4 [3]
#eval acceptedC ``chainW 3 ``topW "ved_c4w" ctlWire 4 [3]
#eval refusedC ``topNR "ved_c4R" ctlWire 4 [3]
#eval refusedC ``topNO "ved_c4O" ctlWire 4 [3]

/-- site 3 with the atoms simp only under the failing budget (the skipped simp is the fallback): the handler runs, no exception leaves
it; the downstream stage then cannot close the goal, so the run ends refused at `[proof]` (a refusal, not a crash) -/
def skippedC (child : Name) (n : Nat) (top : Name) (tag : String) : CommandElabM Unit := do
  let ((msg?, thm?), cnt) ← childRunC child n top tag ctlWire 8
  unless cnt[3]! > 0 do throwError "ctlFail=8: handler 3 not reached ({cnt})"
  match msg?, thm? with
  | some msg, none =>
    unless msg.startsWith s!"VED U1 REFUSED {child} [proof]" do throwError "ctlFail=8: unexpected refusal: {msg.take 300}"
    logInfo m!"CONTROL ctlFail=8 {child}: handler 3 reached, atoms simp skipped, refused at [proof]"
  | _, some _ => logInfo m!"CONTROL ctlFail=8 {child}: handler 3 reached, atoms simp skipped, accepted"
  | none, none => throwError "ctlFail=8: neither refused nor accepted"

#eval skippedC ``chainN 7 ``topN "ved_c8a"
#eval skippedC ``chainW 3 ``topW "ved_c8w"

end Tests.Ved.U1StructNamedCheck

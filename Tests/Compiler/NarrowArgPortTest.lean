import Tests.Compiler.ShippingHierarchySoundnessTest
import Sparkle.Backend.Verilog

/-! # A NARROWER argument into a WIDER child port (worker W, unit 2)

WRITTEN, NOT BUILT. TARGET-ONLY (`lake build Tests.Compiler.NarrowArgPortTest`;
not in `Tests.AllTests`). The `run_cmd` below logs `NARROWARG …` lines and
FAILS the build if a prediction is wrong.

Question (reviewer): is there a TYPE-CORRECT source the compiler accepts in
which an instance call passes a narrower argument to a wider child port?

How widths flow. A `@[hardware_module]` child is compiled ONCE, standalone,
at the widths its own binder types give (`extractWidth`; a free `Nat` width
falls back to 8). The certified arm and the legacy handlers translate each
argument to a parent wire declared at the ARGUMENT's width, then run
`instLinkCheck` before every `emitInstance` (all four emit sites,
`Sparkle/Compiler/Elab.lean`): every connected parent wire must be declared at
exactly the child port's width, else the compile throws. The machine route
(`closeInsts`) has no such guard, but its call reader (`machInstCall?` →
`instSignature?` → `telescopeKinds`) reads only children whose binders are
literal-width `Signal dom (BitVec n)` (n > 0) / `Signal dom Bool` / domain,
and the argument `let` is typed at the child's binder kind; Lean's typing of
the call then forces the argument to exactly that type.

Lean's typing does NOT force widths for a WIDTH-GENERIC child:

(1) `parentW4`: `childW 4 a b` type-checks (w := 4) and passes 4-bit wires to
    `childW`'s ports, which are 8 bits (compiled once at the fallback 8).
    PREDICTION: REFUSED by `instLinkCheck` ("a connected wire's width differs
    from the port's width"), the twin of the BUILT `parentW16` check in
    `ShippingHierarchySoundnessTest` (wider-into-narrower). No module is
    emitted.

(2) `parentZext`: the only way to feed an 8-bit Signal to a fixed 16-bit port
    is an explicit widening in the source (`Signal.map (BitVec.setWidth 16)`);
    there is no width-changing coercion between Signals (`Signal.lean` has
    `Coe (BitVec n) (Signal dom (BitVec n))` and `Coe Bool (Signal dom Bool)`
    only). PREDICTION: compiles; ONE instance of `child16`, every connection
    width-linked (`designLinked`), each argument a 16-bit parent wire holding
    the zero-extended byte. The emitted SV computes `out = zext a + zext b`
    (mod 2^16) — exactly the source. Not a narrow-into-wide connection: the
    widening is in the source and in the parent's logic, the port sees 16 bits.

(3) the same call WITHOUT the widening does not elaborate (`#check_failure`).

The general statement is `Tools.ShippingInstanceMeaningP.instUncached_linkedE`
(argument width = port width by the compiler's guard, for a call with ANY
prefix — width arguments included). -/
namespace Sparkle.Tests.Compiler.NarrowArgPortTest
open Lean Elab Command Meta Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest (childW designLinked)

/-- (1) 4-bit arguments into the 8-bit ports of the width-generic `childW`. -/
def parentW4 {dom : DomainConfig} (a b : Signal dom (BitVec 4)) :
    Signal dom (BitVec 4) := childW 4 a b

/-- A fixed-width child with 16-bit ports and no domain binder. -/
@[hardware_module] def child16 (x y : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain (BitVec 16) := x + y

/-- (2) 8-bit Signals widened IN THE SOURCE, then passed to the 16-bit ports. -/
def parentZext (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 16) :=
  child16 (Signal.map (BitVec.setWidth 16) a) (Signal.map (BitVec.setWidth 16) b)

-- (3) Without the widening the call is ill-typed.
#check_failure (fun (a b : Signal defaultDomain (BitVec 8)) => child16 a b)

run_cmd liftTermElabM do
  -- the child's compiled port widths
  try
    let (mcW, _) ← synthesizeCombinationalCore ``childW [] false
    logInfo m!"NARROWARG childW compiled ports: inputs {mcW.inputs.map fun p => (p.name, p.ty.bitWidth)}, outputs {mcW.outputs.map fun p => (p.name, p.ty.bitWidth)}"
  catch ex =>
    logInfo m!"NARROWARG childW standalone compile threw (informational): {ex.toMessageData}"
  -- (1) narrower arguments into wider ports: predicted REFUSED
  let r1 ← try
      let (m, d) ← synthesizeCombinationalCore ``parentW4 [] false
      pure (some s!"COMPILED: {m.body.length} statements, designLinked {designLinked m d}, inputs {m.inputs.map fun p => (p.name, p.ty.bitWidth)}")
    catch ex =>
      logInfo m!"NARROWARG parentW4 REFUSED: {ex.toMessageData}"
      pure none
  if let some msg := r1 then
    throwError "NARROWARG parentW4 was NOT refused (prediction wrong — a narrow-into-wide instance may have been emitted): {msg}"
  -- (2) explicit widening: predicted to compile, linked, one instance
  let (m2, d2) ← synthesizeCombinationalCore ``parentZext [] false
  let insts := (m2.body.filter fun st => match st with
    | .inst .. => true
    | _ => false).length
  logInfo m!"NARROWARG parentZext: {m2.body.length} statements, {insts} instance statements, designLinked {designLinked m2 d2}, wires {m2.wires.map fun p => (p.name, p.ty.bitWidth)}"
  unless insts == 1 do throwError "NARROWARG parentZext: expected one instance, got {insts}"
  unless designLinked m2 d2 do throwError "NARROWARG parentZext: an instance is not width-linked"
  -- the emitted SystemVerilog, for reading
  let design ← synthesizeHierarchical ``parentZext
  logInfo m!"NARROWARG parentZext SV:\n{Sparkle.Backend.Verilog.toVerilogDesign design}"

end Sparkle.Tests.Compiler.NarrowArgPortTest

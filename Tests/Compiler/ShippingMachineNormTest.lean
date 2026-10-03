import Sparkle.Core.CircuitDo
import Tools.ShippingMachineCommand

/-! Normal forms on the state-machine route.

A `circuit do` writes the same hardware in several ways; the gates accept
one form of each, and `Sparkle.Compiler.Elab.machNorm` rewrites the others
to it (machine route only):

* a constant computed in Lean — `BitVec.ofInt`, powers and products, a user
  constant such as a state encoding — also as a reset value, read by the
  KERNEL's reduction (`kernelNat`);
* `Signal.lit`;
* an operator with one operand a plain `BitVec` (`sig + c`, `c ^^^ sig`);
* a `BitVec` operator lifted through `<$>`/`<*>` or a `map` with a constant;
* `~~~` on a `BitVec` Signal, and `BitVec.not` through `map`;
* a slice whose start is computed in Lean; a concatenation with a computed
  constant operand.

Each declaration below uses forms the gates do not accept as written (they
are the measured reasons real IP modules missed the route), and takes the
machine route through its normal form. `#machine_endpoint` then gives it the
end-to-end theorem — the kernel checks the declaration AS WRITTEN against
the terms of the normalised transition, so each rewrite is proved for the
declaration that uses it. -/
namespace Sparkle.Tests.Compiler.ShippingMachineNormTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

/-! ## Declarations -/

/-- State encodings, as an IP module writes them. -/
def sIdle : BitVec 2 := 0#2
def sRun : BitVec 2 := 2#2

section
variable {dom : DomainConfig}

/-- Computed constants: an `Int` expression, a user constant, and both as
reset values. -/
def nConst (en : Signal dom Bool) : Signal dom (BitVec 16) :=
  circuit do
    let acc ← Signal.reg (BitVec.ofNat 16 (2 ^ 4 + 3))
    let st ← Signal.reg sIdle
    let k := (Signal.pure (BitVec.ofInt 16 (-3 * 2 ^ 4)) : Signal dom (BitVec 16))
    let accS := (acc : Signal dom (BitVec 16))
    let stS := (st : Signal dom (BitVec 2))
    acc <~ Signal.mux en (accS + k) accS
    st <~ Signal.mux (Signal.beq stS (Signal.pure sRun)) (Signal.pure sIdle) (Signal.pure sRun)
    return accS

/-- `Signal.lit`, and a Bool computed in Lean. -/
def nLit (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  circuit do
    let c ← Signal.reg (0#8)
    let cS := (c : Signal dom (BitVec 8))
    let on := (Signal.pure (decide (3 < 5)) : Signal dom Bool)
    c <~ Signal.mux (en &&& on) (cS + Signal.lit dom 3#8) cS
    return cS

/-- One operand a plain `BitVec`, on either side, and a shift by one. -/
def nMixed (d : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  circuit do
    let c ← Signal.reg (1#8)
    let cS := (c : Signal dom (BitVec 8))
    let a := (cS + (5#8 : BitVec 8) : Signal dom (BitVec 8))
    let b := ((0x0F#8 : BitVec 8) &&& d : Signal dom (BitVec 8))
    let s := (a >>> (1#8 : BitVec 8) : Signal dom (BitVec 8))
    c <~ (s ^^^ b : Signal dom (BitVec 8))
    return cS

/-- Operators lifted through the applicative, and maps with a constant. -/
def nLift (d : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  circuit do
    let c ← Signal.reg (0#8)
    let cS := (c : Signal dom (BitVec 8))
    let o := ((· ||| ·) <$> cS <*> d : Signal dom (BitVec 8))
    let sh := ((· >>> ·) <$> o <*> d : Signal dom (BitVec 8))
    let lo := cS.map (· &&& 1#8)
    let up := ((fun x => x + 7#8) <$> sh : Signal dom (BitVec 8))
    c <~ (up - lo : Signal dom (BitVec 8))
    return cS

/-- `~~~` on a `BitVec` Signal. -/
def nNot (d : Signal dom (BitVec 4)) : Signal dom (BitVec 4) :=
  circuit do
    let c ← Signal.reg (0#4)
    let cS := (c : Signal dom (BitVec 4))
    c <~ (~~~(cS ^^^ d) : Signal dom (BitVec 4))
    return cS

/-- `BitVec.not` through `map` (the ICMP checksum). -/
def nMapNot (d : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  circuit do
    let c ← Signal.reg (0#16)
    let cS := (c : Signal dom (BitVec 16))
    c <~ (cS + d).map (BitVec.not ·)
    return cS

/-- A slice whose start is computed, a concatenation with a computed
constant. -/
def nSlice (d : Signal dom (BitVec 24)) : Signal dom (BitVec 16) :=
  circuit do
    let c ← Signal.reg (0#16)
    let cS := (c : Signal dom (BitVec 16))
    let byte := d.map (BitVec.extractLsb' (2 * 8) 8 ·)
    c <~ ((BitVec.ofNat 8 (2 ^ 3 + 1)) ++ byte : Signal dom (BitVec 16))
    return cS
end

/-! ## The route -/

-- Each declaration is a machine shape, and the real entry emits a module
-- with registers for it.
run_cmd liftTermElabM do
  let env ← getEnv
  let senv := structEnv env
  for n in [``nConst, ``nLit, ``nMixed, ``nLift, ``nNot, ``nMapNot, ``nSlice] do
    let ci ← getConstInfo n
    let entry := entryConst true false [] ci (instancePredicate env) (userInliner env) senv
    unless (machineShape? false [] entry senv).isSome do
      throwError "{n}: not on the machine route"
    let (m, _) ← synthesizeCombinational n
    unless m.body.any (fun st => match st with | .register .. => true | _ => false) do
      throwError "{n}: the emitted module has no register"

/-! ## The endpoints -/

#machine_endpoint nConst
#machine_endpoint nLit
#machine_endpoint nMixed
#machine_endpoint nLift
#machine_endpoint nNot
#machine_endpoint nMapNot
#machine_endpoint nSlice

run_cmd do
  if (← get).messages.hasErrors then throwError "machine normal-form regression failed"
  for name in [``nConst.machine_sound, ``nLit.machine_sound, ``nMixed.machine_sound,
      ``nLift.machine_sound, ``nNot.machine_sound, ``nMapNot.machine_sound,
      ``nSlice.machine_sound] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  logInfo m!"MACHINE NORMAL FORMS: seven declarations the gates refuse as written, each with its kernel-checked endpoint"

end Sparkle.Tests.Compiler.ShippingMachineNormTest

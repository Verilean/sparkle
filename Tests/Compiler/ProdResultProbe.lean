import Sparkle

/-! # Probe: calls of `@[hardware_module]`s with pair results

PROBE (never-failing; prints). Reviewer 2026-10-19: the parent reads a call
whose result is a pair of Signals with `machOuts?` (`out_0`, `out_1`); does the
callee's own compile have those ports, or one packed `out`? Prints, for each
parent, the machine shape (entries, fields, origins), and for the certified and
legacy routes the top's instance statements with their connections and every
child module's ports. Callees: a pair OF Signals, and a Signal of a pair. -/
namespace Sparkle.Tests.Compiler.ProdResultProbe
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- A pair of Signals: `(a + b, a ^^^ b)`. -/
@[hardware_module]
def pairOf (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) × Signal defaultDomain (BitVec 8) :=
  (a + b, a ^^^ b)

/-- A Signal of a pair: `(a + b, a ^^^ b)` bundled. -/
@[hardware_module]
def sigPair (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × BitVec 8) :=
  bundle2 (a + b) (a ^^^ b)

def useFst (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 8 × BitVec 8)) =>
    let p := pairOf a b
    bundle2 (Signal.register 0#8 p.1) (Signal.register 0#8 p.2)
  Signal.fst st

def useBoth (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 8 × BitVec 8)) =>
    let p := pairOf a b
    bundle2 (Signal.register 0#8 (p.1 + Signal.snd st)) (Signal.register 0#8 p.2)
  Signal.fst st

def useSig (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 8 × BitVec 8)) =>
    let p := sigPair a b
    bundle2 (Signal.register 0#8 (Signal.fst p)) (Signal.register 0#8 (Signal.snd p))
  Signal.fst st

/-- A pair of Signals of DIFFERENT widths (as `CallWidthHuntTest.kPair`). -/
@[hardware_module]
def kPair (w : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain (BitVec 4) × Signal defaultDomain (BitVec 12) :=
  (w.map (BitVec.extractLsb' 0 4 ·), w.map (BitVec.extractLsb' 4 12 ·))

/-- Both components of `kPair` read in a `circuit do`. -/
def cPair (w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 12) :=
  circuit do
    let r ← Signal.reg 0#12
    let rs := (r : Signal defaultDomain (BitVec 12))
    let k := kPair w
    r <~ Signal.mux (k.1 === (Signal.pure 3#4 : Signal defaultDomain (BitVec 4))) (rs + k.2) rs
    return rs

/-- Only the second component. -/
def cSnd (w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 12) :=
  circuit do
    let r ← Signal.reg 0#12
    let rs := (r : Signal defaultDomain (BitVec 12))
    let k := kPair w
    r <~ rs + k.2
    return rs

/-- `pairOf` (equal widths) in a `circuit do`. -/
def cSame (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let p := pairOf a b
    r <~ rs + (p.1 ^^^ p.2)
    return rs

/-- `sigPair` (a Signal of a pair) in a `circuit do`. -/
def cSig (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let p := sigPair a b
    r <~ rs + (Signal.fst p ^^^ Signal.snd p)
    return rs

/-- The call is the parent's result (a pair of Signals, `out_0`/`out_1`). -/
def pRet (w : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain (BitVec 4) × Signal defaultDomain (BitVec 12) :=
  kPair w

/-- The call destructured by a `match` (a pattern `let` is not `circuit do` syntax). -/
def cMatch (w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 12) :=
  match kPair w with
  | (_x, y) =>
    circuit do
      let r ← Signal.reg 0#12
      let rs := (r : Signal defaultDomain (BitVec 12))
      r <~ rs + y
      return rs

/-- A structure of Signals (control: the field path that does read). -/
structure Two where
  lo : Signal defaultDomain (BitVec 4)
  hi : Signal defaultDomain (BitVec 12)

@[hardware_module]
def kTwo (w : Signal defaultDomain (BitVec 16)) : Two :=
  { lo := w.map (BitVec.extractLsb' 0 4 ·), hi := w.map (BitVec.extractLsb' 4 12 ·) }

def cTwo (w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 12) :=
  circuit do
    let r ← Signal.reg 0#12
    let rs := (r : Signal defaultDomain (BitVec 12))
    let k := kTwo w
    r <~ rs + k.hi
    return rs

run_cmd liftTermElabM do
  let env ← getEnv
  let senv := Sparkle.Compiler.Elab.structEnv env
  for c in [``pairOf, ``sigPair, ``kPair] do
    logInfo m!"{c}: inst {repr (senv.inst c)} instS kinds {repr ((senv.instS c).map (·.1))}"
  for n in [``useFst, ``useBoth, ``useSig, ``cPair, ``cSnd, ``cSame, ``cSig, ``pRet, ``cMatch, ``cTwo] do
    let ci ← getConstInfo n
    let ec := Sparkle.Compiler.Elab.entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate env) (Sparkle.Compiler.Elab.userInliner env) senv
    match Sparkle.Compiler.Elab.machineShape? false [] ec senv with
    | some sp =>
      logInfo m!"{n}: shape insts {sp.insts.map (fun i => (i.1, i.2.1, repr i.2.2))} instFields {sp.instFields} origins {repr sp.instOrigins}"
    | none => logInfo m!"{n}: NO machine shape at the entry constant"
    for cfe in [true, false] do
      try
        let (top, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCoreWith
          (fun env e h t n => Sparkle.Compiler.Elab.translateExprToWire env e h t n) n [] false
          (certifiedFrontEnd := cfe)
        logInfo m!"{n} cfe={cfe}: top {top.name} inputs {top.inputs.map (·.name)} outputs {top.outputs.map (·.name)}"
        for s in top.body do
          match s with
          | .inst mn iname conns =>
            logInfo m!"  inst {mn} {iname}: {conns.map (fun (p, e) => (p, repr e))}"
          | s => if (toString n).endsWith "cSnd" then logInfo m!"  stmt {repr s}" else pure ()
        for m in D.modules do
          if m.name != D.topModule then
            logInfo m!"  child {m.name}: inputs {m.inputs.map (fun p => (p.name, repr p.ty))} outputs {m.outputs.map (fun p => (p.name, repr p.ty))}"
      catch e => logInfo m!"{n} cfe={cfe}: threw {e.toMessageData}"

end Sparkle.Tests.Compiler.ProdResultProbe

import Tools.Prototype.ReaderFixpointSpec
import Sparkle.Core.Domain
import Sparkle.Core.CircuitDo
import Sparkle.Compiler.Elab

/-! # SDOM: a reachable-at-the-reader-level example for the `ShapeInOk.startDom` gap

TARGET-ONLY (`./.cluster/qbuild.sh build Tests.Compiler.StartDomExampleTest`); not in `Tests.AllTests`.  EVIDENCE, not
proof.  Part 1 is the READER only; part 2 (`srcDecl`) traces a source declaration through the real `machineShape?`.
The constant of the domain is the DECLARED `dsig`; its type is checked by `inferType`/`isDefEq` (the earlier version used an
undeclared constant, so "well-typed" was not established).

The domain expression `dom = let s : Signal D (BitVec 8) := c; (fun (_ : Signal D (BitVec 8)) => D) s` is converted from
`{}` (what `shapeStart` does).  The `let` is a hardware `let` (`mixedGateBinderKind?` = `.bits 8`, value not a variable),
so `machBindLet` pushes it and the body's `s` becomes the placeholder `_machLet 0`; `dom'` mentions it, and the state is
discarded by `shapeStart`.  We check on BOTH the prototype `machConvF` and the production `machConv`:
`LetOk 0 dom' = false` while `LetOk st'.lets.size dom' = true` (the conversion's own state is consistent),
and that `shapeStart` then reserves the machine with `dom := some dom'` in a state with NO lets. -/
namespace Tests.Compiler.StartDomExampleTest
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec

def bv8 : Expr := mkApp (.const ``BitVec []) (inlNatLit 8)
def D : Expr := .const ``Sparkle.Core.Domain.defaultDomain []
def sigTy : Expr := mkApp2 (.const ``Sparkle.Core.Signal.Signal [.zero]) D bv8
/-- A declared signal (the `let` value of the domain). -/
def dsig : Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain (BitVec 8) :=
  Sparkle.Core.Signal.Signal.pure 5#8

def cval : Expr := .const ``dsig []
def dom : Expr := .letE `s sigTy cval (mkApp (.lam `_x sigTy D .default) (.bvar 0)) false

def senv0 : StructEnv := { proj := fun _ => none, fields := fun _ => none }

def alphas : Expr :=
  mkApp3 (.const ``List.cons [.succ .zero]) (.sort (.succ .zero)) (.const ``Bool [])
    (mkApp (.const ``List.nil [.succ .zero]) (.sort (.succ .zero)))
def inits : Expr :=
  mkApp4 (.const ``Prod.mk [.zero, .zero]) (.const ``Bool []) (.const ``Unit [])
    (.const ``Bool.true []) (.const ``Unit.unit [])

def mid : ShapeMid :=
  { rootLets := [], sel := none, root := .const `r [], wrap? := none
    run? := some (dom, alphas, inits, .const `body []) }

def chk (c : Bool) (msg : String) : IO Unit := unless c do throw (IO.userError msg)

-- the domain is well-typed: it has type `DomainConfig`
run_meta do
  let ty ← inferType dom
  unless (← isDefEq ty (.const ``Sparkle.Core.Domain.DomainConfig [])) do
    throwError "dom : {ty}, not DomainConfig"
  unless (← isDefEq (← inferType cval) sigTy) do throwError "dsig : wrong type"
  Lean.logInfo "dom : DomainConfig  (inferType/isDefEq)"

#eval show IO Unit from do
  -- (a) shapeStart succeeds, no lets, dom mentions the placeholder, LetOk 0 false
  match (shapeStart senv0 mid).run (wtab senv0 60) with
  | some (some st0) =>
    chk (st0.lets.size == 0) "shapeStart: lets.size != 0"
    match st0.dom with
    | some d' =>
      chk (LetOk 0 d' == false) "shapeStart: LetOk 0 dom' is true (placeholder gone)"
      IO.println s!"(a) shapeStart ok: lets=0 dom'={d'} LetOk0=false"
    | none => throw (IO.userError "shapeStart: dom = none")
  | r => throw (IO.userError s!"shapeStart refused: {repr (r.map (·.isSome))}")
  -- (b) run machNorm, feed ITS OUTPUT to machConvF / machConv
  let nd := machNorm senv0 dom
  IO.println s!"machNorm dom = {nd}"
  chk (nd.hasLooseBVars == false) "machNorm output has loose bvars"
  match machConvF 60 senv0 [] 0 nd ({} : MachRead) with
  | some (some (dom', st)) =>
    IO.println s!"(b) proto: lets={st.lets.size} LetOk0={LetOk 0 dom'} LetOkSize={LetOk st.lets.size dom'} dom'={dom'}"
    chk (st.lets.size == 1) "proto/norm: lets.size != 1"
    chk (LetOk 0 dom' == false) "proto/norm: LetOk 0 dom' true"
    -- (c) production side, own state
    chk (LetOk st.lets.size dom' == true) "proto/norm: LetOk size false"
  | r => throw (IO.userError s!"proto/norm: conv gave {repr (r.map (·.map (·.1)))}")
  match machConv senv0 [] 0 nd ({} : MachRead) with
  | some (dom', st) =>
    IO.println s!"(b,c) prod: lets={st.lets.size} LetOk0={LetOk 0 dom'} LetOkSize={LetOk st.lets.size dom'}"
    chk (st.lets.size == 1) "prod/norm: lets.size != 1"
    chk (LetOk 0 dom' == false) "prod/norm: LetOk 0 dom' true"
    chk (LetOk st.lets.size dom' == true) "prod: LetOk (lets.size) dom' false"
  | none => throw (IO.userError "prod: conv refused")

/-! ## Part 2: a source declaration through the real `machineShape?`

`srcDecl` writes the domain argument of its type as the `let`/redex above.  What is observed is printed. -/
section
open Sparkle.Core.Signal Sparkle.Core.Circuit
def srcDecl :
    Sparkle.Core.Signal.Signal
      (let s : Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain (BitVec 8) := dsig
       (fun (_ : Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain (BitVec 8)) =>
         Sparkle.Core.Domain.defaultDomain) s)
      (BitVec 8) :=
  circuit do
    let c ← Signal.reg (0#8)
    let cS := (c : Sparkle.Core.Signal.Signal _ (BitVec 8))
    c <~ cS + cS
    return cS

/-- CONTROL: the same body, the plain domain in the type. -/
def srcCtl : Signal Sparkle.Core.Domain.defaultDomain (BitVec 8) :=
  circuit do
    let c ← Signal.reg (0#8)
    let cS := (c : Signal _ (BitVec 8))
    c <~ cS + cS
    return cS
end

def shapeOf (n : Name) : MetaM Bool := do
  let env ← getEnv
  let senv := structEnv env
  let ci ← getConstInfo n
  let entry := entryConst true false [] ci (instancePredicate env) (userInliner env) senv
  return (machineShape? false [] entry senv).isSome

run_meta do
  unless (← shapeOf ``srcCtl) do throwError "control srcCtl: no machine shape"
  if (← shapeOf ``srcDecl) then
    throwError "srcDecl now HAS a machine shape: re-examine (placeholder domain accepted?)"
  Lean.logInfo "srcCtl: machineShape? = some; srcDecl: machineShape? = none (asserted)"

run_meta do
  let env ← getEnv
  let senv := structEnv env
  let ci ← getConstInfo ``srcDecl
  Lean.logInfo m!"srcDecl type: {ci.type}"
  Lean.logInfo m!"srcDecl value: {ci.value!}"
  let entry := entryConst true false [] ci (instancePredicate env) (userInliner env) senv
  match entry with
  | .defnInfo d =>
    let e := d.value
    let some (_, e0) := mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs e) | Lean.logInfo "peel failed"
    let e1 := machLoopAsLet (Sparkle.Compiler.MachRawSurface.rootFloat
      (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? (inlFoldNat (machNorm senv e0))))
    let (rl, _, run?, _) := machRoot senv.proj e1 []
    Lean.logInfo m!"rootLets={rl.length}\nrun dom = {(run?.bind machRunApp?).map (·.1)}"
    -- what the reader does with that domain, and why the shape is refused
    let some (dm, _, _, _) := run?.bind machRunApp? | throwError "no run"
    match machConv senv (rl.map fun _ => .unit) 0 dm ({} : MachRead) with
    | some (dom', st) =>
      Lean.logInfo m!"real-path machConv dom: dom'={dom'} lets={st.lets.size} LetOk0={LetOk 0 dom'} machDom?={(machDom? 0 dom').isSome}"
      unless LetOk 0 dom' == false && (machDom? 0 dom').isNone do
        throwError "real path: expected placeholder dom' refused by machDom?"
    | none => Lean.logInfo "real-path machConv dom: refused"
  | _ => Lean.logInfo "entry not a defn"
  Lean.logInfo m!"machineShape? = {(machineShape? false [] entry senv).isSome}"

end Tests.Compiler.StartDomExampleTest

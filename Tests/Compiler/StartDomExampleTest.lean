import Tools.Prototype.ReaderFixpointSpec
import Sparkle.Core.Domain

/-! # SDOM: a reachable-at-the-reader-level example for the `ShapeInOk.startDom` gap

TARGET-ONLY (`./.cluster/qbuild.sh build Tests.Compiler.StartDomExampleTest`); not in `Tests.AllTests`.  EVIDENCE, not
proof, and about the READER only (typing / elaboration of a source declaration is NOT exercised).

The domain expression `dom = let s : Signal D (BitVec 8) := c; (fun (_ : Signal D (BitVec 8)) => D) s` is converted from
`{}` (what `shapeStart` does).  The `let` is a hardware `let` (`mixedGateBinderKind?` = `.bits 8`, value not a variable),
so `machBindLet` pushes it and the body's `s` becomes the placeholder `_machLet 0`; `dom'` mentions it, and the state is
discarded by `shapeStart`.  We check on BOTH the prototype `machConvF` and the production `machConv`:
`LetOk 0 dom' = false` while `LetOk st'.lets.size dom' = true` (the conversion's own state is consistent),
and that `shapeStart` then reserves the machine with `dom := some dom'` in a state with NO lets. -/
namespace Tests.Compiler.StartDomExampleTest
open Lean Sparkle.Compiler.Elab Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec

def bv8 : Expr := mkApp (.const ``BitVec []) (inlNatLit 8)
def D : Expr := .const ``Sparkle.Core.Domain.defaultDomain []
def sigTy : Expr := mkApp2 (.const ``Sparkle.Core.Signal.Signal [.zero]) D bv8
def cval : Expr := .const `someHardwareValue []
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

#eval show IO Unit from do
  -- prototype
  match machConvF 60 senv0 [] 0 dom ({} : MachRead) with
  | some (some (dom', st)) =>
    IO.println s!"proto: lets={st.lets.size} LetOk0={LetOk 0 dom'} LetOkSize={LetOk st.lets.size dom'}"
    IO.println s!"proto dom' = {dom'}"
    unless st.lets.size == 1 && LetOk 0 dom' == false && LetOk st.lets.size dom' == true do
      throw (IO.userError "proto: not the expected shape")
  | r => throw (IO.userError s!"proto: conv gave {repr (r.map (·.map (·.1)))}")
  -- production
  match machConv senv0 [] 0 dom ({} : MachRead) with
  | some (dom', st) =>
    IO.println s!"prod : lets={st.lets.size} LetOk0={LetOk 0 dom'} LetOkSize={LetOk st.lets.size dom'}"
    unless st.lets.size == 1 && LetOk 0 dom' == false do
      throw (IO.userError "prod: not the expected shape")
  | none => throw (IO.userError "prod: conv refused")
  -- does `machNorm` (run on the whole body before the reader) remove the redex?
  IO.println s!"machNorm dom = {machNorm senv0 dom}"
  -- shapeStart (prototype) on a ShapeMid with this enclosing domain
  match (shapeStart senv0 mid).run (wtab senv0 60) with
  | some (some st0) =>
    IO.println s!"shapeStart: dom={st0.dom.map (fun d => s!"{d}")} lets={st0.lets.size} dom LetOk 0 = {st0.dom.map (LetOk 0)}"
  | r => IO.println s!"shapeStart: no state ({repr (r.map (·.isSome))})"

end Tests.Compiler.StartDomExampleTest

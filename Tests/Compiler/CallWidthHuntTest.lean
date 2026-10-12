import Sparkle
import Tests.Compiler.HierBindsCensusTest
import Tests.Compiler.PrintArtifactCensusTest
import Tools.ShippingPortsMatchRaw
import Tools.ShippingCallWidths

/-! # A hunt for a call whose widths disagree although the compilation succeeds (findings A, A')

Compiled evidence, LOGS ONLY — nothing here throws and nothing is a theorem.
The divergence classes are those of `docs/parallel/B-callwidths.md` §2; the
declarations below are one tiny parent / child pair per class.

For every candidate parent (the hunt's own, then the 37 declarations of
`PrintArtifactCensusTest.candidates`, which contain the 30 of
`HierBindsCensusTest.candidates`), with `(raw, D)` the core run, `b` the
full entry's module (before the optimizer), `C = childMap D.modules`:

    CALLWIDTH <name>: compiled=<T/F> route=<gate|mixed|machine|fallthrough|legacy|machine?(…)>
      callWidthsOk=<T/F/none> callArgsOk=<T/F/none> instOutWidthsOk(raw)=<T/F> portsMatchB(raw)=<T/F>
      inst=<T/F> instOutWidthsOk(b)=.. portsMatchB(b)=.. res=<ok>/<n> args=<ok>/<n> arity=<T/F/none>
      kids=[<child>:<its route>, …] bad=[…]

* `route`: `gate` / `mixed` — a certified gate accepts the entry constant;
  `legacy` — no gate and no machine shape; otherwise the machine arm
  (`synthesizeMachineCertified`) is RE-RUN on the shape, from reset refs at
  depth 1 as inside the entry: `machine` when it returns the core run's
  module, `fallthrough` when it returns `none` (the entry then took the
  legacy arm: finding E), `machine?(…)` when the re-run threw or returned
  another module (undetermined);
* `callWidthsOk` / `callArgsOk`: `Tools.ShippingCallWidths.callWidthsOk` and
  `Tools.ShippingPortsMatchRaw.callArgsOk` with `d.shape` replaced by the
  shape read in this run (`callWidthsOkS`, `callArgsOkS`: the same
  expressions, `MachineData` is not built here), `kidOuts k` the real
  child's output ports with their types' widths, `kidIns k` the EMITTED
  widths (`weS`) of the real child's argument ports. `-` without a shape or
  without calls. NOTE: `callWidthsOk` tests the port named
  `instFields.getD k ""`, so it is vacuous on the one-output closing
  (`instFields = []`); hence
* `res` / `args`: the STRICT per-pair comparison — for entry `k` the width
  of the type of `binders[nDecl + k]` against the child's output port the
  closing connects (the field, or the only output when `instFields = []`);
  for argument `j` the width of the `let` binder against the declared type
  of the child's `j`-th argument port; `arity`: as many argument ports as
  argument wires;
* `bad`: every reference connection of `raw` whose two emitted widths
  differ, `inst.port<->wire:parent/child`, and every failing pair.

A row counts as "width mismatch with success" when it compiled, its raw
module has an instance, and one of the four module checks is false or — on
the confirmed machine route only — a pair, the arity or a mirror is false.

    CALLWIDTH HUNT: candidates n; compiled k; width mismatch with success j [names]

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.CallWidthHuntTest
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

/-! ## The candidates -/

/-- The plain child: a combinational byte function. -/
@[hardware_module]
def kPlain (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + x

/-- Known shape (`ShippingMachineInstTest.caller`), the hunt's own baseline. -/
def pPlain (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := kPlain (accS + x)
    acc <~ y
    return y

/-! ### A width that is not a literal in the child's TYPE -/

/-- The result width is a literal sum. -/
@[hardware_module]
def kSum (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec (4 + 4)) :=
  (x + x : Signal defaultDomain (BitVec 8))

def pSum (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := (kSum (accS + x) : Signal defaultDomain (BitVec 8))
    acc <~ y
    return y

abbrev W8 : Nat := 8

/-- The widths are a reducible constant. -/
@[hardware_module]
def kAbbrev (x : Signal defaultDomain (BitVec W8)) : Signal defaultDomain (BitVec W8) :=
  x + x

def pAbbrev (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := (kAbbrev (accS + x) : Signal defaultDomain (BitVec 8))
    acc <~ y
    return y

def WD : Nat := 8

/-- The widths are an ordinary definition (unfolded by `userInliner`, which
`inlinedConst` applies to the TYPE too). -/
@[hardware_module]
def kDef (x : Signal defaultDomain (BitVec WD)) : Signal defaultDomain (BitVec WD) :=
  x

def pDef (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := (kDef (accS + x) : Signal defaultDomain (BitVec 8))
    acc <~ y
    return y

abbrev Byte : Type := BitVec 8

/-- The payload type is a type alias. -/
@[hardware_module]
def kByte (x : Signal defaultDomain Byte) : Signal defaultDomain Byte :=
  x

def pByte (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := (kByte (accS + x) : Signal defaultDomain (BitVec 8))
    acc <~ y
    return y

/-! ### `Bool` and `BitVec 1` -/

/-- One-bit vectors in and out (the legacy oracle's `.bit`). -/
@[hardware_module]
def kBit1 (b : Signal defaultDomain (BitVec 1)) : Signal defaultDomain (BitVec 1) :=
  b ^^^ (Signal.pure 1#1 : Signal defaultDomain (BitVec 1))

def pBit1 (x : Signal defaultDomain (BitVec 1)) : Signal defaultDomain (BitVec 1) :=
  circuit do
    let acc ← Signal.reg 0#1
    let accS := (acc : Signal defaultDomain (BitVec 1))
    let y := kBit1 (accS ^^^ x)
    acc <~ y
    return y

/-- A Bool argument and a Bool result. -/
@[hardware_module]
def kBool (x : Signal defaultDomain (BitVec 8)) (en : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  Signal.mux en (x === (Signal.pure 7#8 : Signal defaultDomain (BitVec 8))) en

def pBool (x : Signal defaultDomain (BitVec 8)) (en : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let h := kBool (accS + x) en
    acc <~ Signal.mux h (accS + x) accS
    return accS

/-! ### Structure results: field order and mixed kinds -/

structure Two (dom : DomainConfig) where
  lo : Signal dom (BitVec 4)
  hi : Signal dom (BitVec 12)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (Two dom) dom := ⟨⟩

/-- A combinational child with two fields of different widths. -/
@[hardware_module]
def kTwo {dom : DomainConfig} (w : Signal dom (BitVec 16)) : Two dom :=
  { lo := w.map (BitVec.extractLsb' 0 4 ·), hi := w.map (BitVec.extractLsb' 4 12 ·) }

def pTwo (w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 12) :=
  circuit do
    let r ← Signal.reg 0#12
    let rs := (r : Signal defaultDomain (BitVec 12))
    let k := kTwo w
    r <~ Signal.mux (k.lo === (Signal.pure 3#4 : Signal defaultDomain (BitVec 4))) (rs + k.hi) rs
    return rs

structure Tri (dom : DomainConfig) where
  a : Signal dom (BitVec 3)
  f : Signal dom Bool
  c : Signal dom (BitVec 11)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (Tri dom) dom := ⟨⟩

/-- A sequential child with three fields, narrow / Bool / wide. -/
@[hardware_module]
def kTri {dom : DomainConfig} (en : Signal dom Bool) : Tri dom :=
  circuit do
    let s ← Signal.reg 0#11
    let ss := (s : Signal dom (BitVec 11))
    s <~ Signal.mux en (ss + (Signal.pure 1#11 : Signal dom (BitVec 11))) ss
    return ({ a := ss.map (BitVec.extractLsb' 0 3 ·)
              f := ss === (Signal.pure 5#11 : Signal dom (BitVec 11))
              c := ss } : Tri dom)

/-- The fields read in the reverse of their declaration order. -/
def pTri (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 11) :=
  circuit do
    let r ← Signal.reg 0#11
    let rs := (r : Signal defaultDomain (BitVec 11))
    let k := kTri en
    r <~ Signal.mux k.f (rs + k.c)
      (Signal.mux (k.a === (Signal.pure 1#3 : Signal defaultDomain (BitVec 3))) k.c rs)
    return rs

abbrev TwoD : Type := Two defaultDomain

/-- The result type is an alias of a structure. -/
@[hardware_module]
def kAlias (w : Signal defaultDomain (BitVec 16)) : TwoD :=
  { lo := w.map (BitVec.extractLsb' 0 4 ·), hi := w.map (BitVec.extractLsb' 4 12 ·) }

def pAlias (w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 12) :=
  circuit do
    let r ← Signal.reg 0#12
    let rs := (r : Signal defaultDomain (BitVec 12))
    let k := kAlias w
    r <~ Signal.mux (k.lo === (Signal.pure 3#4 : Signal defaultDomain (BitVec 4))) (rs + k.hi) rs
    return rs

/-- A pair of Signals (`out_0`, `out_1`). -/
@[hardware_module]
def kPair (w : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain (BitVec 4) × Signal defaultDomain (BitVec 12) :=
  (w.map (BitVec.extractLsb' 0 4 ·), w.map (BitVec.extractLsb' 4 12 ·))

def pPair (w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 12) :=
  circuit do
    let r ← Signal.reg 0#12
    let rs := (r : Signal defaultDomain (BitVec 12))
    let k := kPair w
    r <~ Signal.mux (k.1 === (Signal.pure 3#4 : Signal defaultDomain (BitVec 4))) (rs + k.2) rs
    return rs

/-! ### Children whose port width is computed from the BODY (gate / legacy routes) -/

/-- Concatenation: the body's type is `BitVec (8 + 8)`. -/
@[hardware_module]
def kCat (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 16) :=
  (x ++ x : Signal defaultDomain (BitVec (8 + 8)))

def pCat (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let acc ← Signal.reg 0#16
    let accS := (acc : Signal defaultDomain (BitVec 16))
    let y := kCat x
    acc <~ accS + y
    return accS

/-- A slice. -/
@[hardware_module]
def kSlice (w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 4) :=
  w.map (BitVec.extractLsb' 6 4 ·)

def pSlice (w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let y := kSlice w
    acc <~ accS + y
    return accS

/-- A zero extension. -/
@[hardware_module]
def kZext (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 16) :=
  x.map (BitVec.setWidth 16 ·)

def pZext (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let acc ← Signal.reg 0#16
    let accS := (acc : Signal defaultDomain (BitVec 16))
    let y := kZext x
    acc <~ accS + y
    return accS

/-- A truncation. -/
@[hardware_module]
def kTrunc (w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 4) :=
  w.map (BitVec.setWidth 4 ·)

def pTrunc (w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let y := kTrunc w
    acc <~ accS + y
    return accS

/-! ### Argument ports -/

/-- An argument the body does not read. -/
@[hardware_module]
def kUnused (a : Signal defaultDomain (BitVec 8)) (_b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8) :=
  a + a

def pUnused (x : Signal defaultDomain (BitVec 8)) (z : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := kUnused (accS + x) z
    acc <~ y
    return y

/-- A data argument named `clk` (the closing filters the child's inputs by
the NAMES `clk` / `rst`). -/
@[hardware_module]
def kClkName (clk : Signal defaultDomain (BitVec 8)) (x : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  clk + x

def pClkName (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := kClkName x accS
    acc <~ y
    return y

/-- A sequential child with ONE Signal result (the one-output closing
refuses a child with a clock). -/
@[hardware_module]
def kCount (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 5) :=
  circuit do
    let c ← Signal.reg 0#5
    let cS := (c : Signal defaultDomain (BitVec 5))
    c <~ Signal.mux en (cS + (Signal.pure 1#5 : Signal defaultDomain (BitVec 5))) cS
    return cS

def pCount (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 5) :=
  circuit do
    let r ← Signal.reg 0#5
    let rs := (r : Signal defaultDomain (BitVec 5))
    let k := kCount en
    r <~ rs + k
    return rs

/-- The PARENT has a data input named `clk` and a sequential child (whose
`clk` port the closing connects to the name `clk`). -/
def pClkIn (clk : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let k := Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (clk === (Signal.pure 1#8 : Signal defaultDomain (BitVec 8)))
    r <~ Signal.mux k.hit (rs + k.n) rs
    return rs

/-! ### Wrappers around the call, shared argument `let`s -/

/-- Width changes around the call, on the argument and on the result. -/
def pMapWrap (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let y := (kPlain (accS.map (BitVec.setWidth 8 ·) + x)).map (BitVec.setWidth 4 ·)
    acc <~ y
    return y

/-- One `let` as the argument of two calls of different children. -/
def pLetReuse (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let t := accS + x
    let y := kPlain t
    let z := kUnused t (t.map (BitVec.extractLsb' 0 4 ·))
    acc <~ y + z
    return y

/-- A polymorphic parent calling a polymorphic sequential child and a
monomorphic-typed field. -/
def pPoly {dom : DomainConfig} (en : Signal dom Bool) : Signal dom (BitVec 11) :=
  circuit do
    let r ← Signal.reg 0#11
    let rs := (r : Signal dom (BitVec 11))
    let k := kTri en
    r <~ Signal.mux k.f k.c rs
    return rs

/-- The hunt's parents, by name (an absent name — a declaration above that
did not elaborate — is logged, not an error). -/
def huntParents : List Name := [
  `Tests.Compiler.CallWidthHuntTest.pPlain,
  `Tests.Compiler.CallWidthHuntTest.pSum,
  `Tests.Compiler.CallWidthHuntTest.pAbbrev,
  `Tests.Compiler.CallWidthHuntTest.pDef,
  `Tests.Compiler.CallWidthHuntTest.pByte,
  `Tests.Compiler.CallWidthHuntTest.pBit1,
  `Tests.Compiler.CallWidthHuntTest.pBool,
  `Tests.Compiler.CallWidthHuntTest.pTwo,
  `Tests.Compiler.CallWidthHuntTest.pTri,
  `Tests.Compiler.CallWidthHuntTest.pAlias,
  `Tests.Compiler.CallWidthHuntTest.pPair,
  `Tests.Compiler.CallWidthHuntTest.pCat,
  `Tests.Compiler.CallWidthHuntTest.pSlice,
  `Tests.Compiler.CallWidthHuntTest.pZext,
  `Tests.Compiler.CallWidthHuntTest.pTrunc,
  `Tests.Compiler.CallWidthHuntTest.pUnused,
  `Tests.Compiler.CallWidthHuntTest.pClkName,
  `Tests.Compiler.CallWidthHuntTest.pCount,
  `Tests.Compiler.CallWidthHuntTest.pClkIn,
  `Tests.Compiler.CallWidthHuntTest.pMapWrap,
  `Tests.Compiler.CallWidthHuntTest.pLetReuse,
  `Tests.Compiler.CallWidthHuntTest.pPoly]

/-- The hunt's children (for the fall-through census). -/
def huntChildren : List Name := [
  `Tests.Compiler.CallWidthHuntTest.kPlain,
  `Tests.Compiler.CallWidthHuntTest.kSum,
  `Tests.Compiler.CallWidthHuntTest.kAbbrev,
  `Tests.Compiler.CallWidthHuntTest.kDef,
  `Tests.Compiler.CallWidthHuntTest.kByte,
  `Tests.Compiler.CallWidthHuntTest.kBit1,
  `Tests.Compiler.CallWidthHuntTest.kBool,
  `Tests.Compiler.CallWidthHuntTest.kTwo,
  `Tests.Compiler.CallWidthHuntTest.kTri,
  `Tests.Compiler.CallWidthHuntTest.kAlias,
  `Tests.Compiler.CallWidthHuntTest.kPair,
  `Tests.Compiler.CallWidthHuntTest.kCat,
  `Tests.Compiler.CallWidthHuntTest.kSlice,
  `Tests.Compiler.CallWidthHuntTest.kZext,
  `Tests.Compiler.CallWidthHuntTest.kTrunc,
  `Tests.Compiler.CallWidthHuntTest.kUnused,
  `Tests.Compiler.CallWidthHuntTest.kClkName,
  `Tests.Compiler.CallWidthHuntTest.kCount]

/-! ## The measurement -/

abbrev Mod := Sparkle.IR.AST.Module
abbrev Dsn := Sparkle.IR.AST.Design

def bs (b : Bool) : String := if b then "T" else "F"

/-- The width of a port type (`0` for a type that is not a scalar; no panic,
unlike `HWType.bitWidth` on a symbolic width). -/
def tyW : Sparkle.IR.Type.HWType → Nat
  | .bit => 1
  | .bitVector w => w
  | _ => 0

/-- The width of the type of a binder kind (`kindTy`). -/
def kindW (k : MixedGateBinder) : Nat := tyW (Tools.ShippingMachineEntry.kindTy k)

/-- The refs the entry clears at depth 0 (`synthesizeCombinationalCoreWith`). -/
def resetRefs : MetaM Unit := do
  sparkleTypeCache.set {}
  sparkleSubModuleCache.set {}
  sparkleChildCache.set {}
  sparkleSubInstanceOutputs.set {}
  sparkleSingleOutInstanceCache.set {}
  sparkleFvarValueMap.set {}
  sparkleWireWidthCache.set {}
  sparkleLetWireCache.set {}
  sparkleLoopWireCache.set {}
  sparkleWireCanon.set {}

/-- What the entry's dispatch reads of a declaration: the entry constant
and the three gates on it (the expressions of `MachineDefines`). -/
structure Gates where
  ec : ConstantInfo
  gate : Bool
  mixed : Bool
  shape : Option MachineShape

def gatesOf (n : Name) : MetaM Gates := do
  let ci ← getConstInfo n
  let env ← getEnv
  let ec := entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)
  return {
    ec := ec
    gate := (certifiedShape? false [] ec).isSome
    mixed := (mixedCertifiedShape? false [] ec (instancePredicate env)).isSome
    shape := machineShape? false [] ec (structEnv env) }

/-- The machine arm alone, from reset refs, at depth 1 (so that the
children's entries are nested ones, as inside the real entry). -/
def machineArm (n : Name) (shape : MachineShape) : MetaM (Option (Mod × Dsn)) := do
  resetRefs
  sparkleSynthDepth.set 1
  try
    synthesizeMachineCertified (fun e hint top named => translateExprToWire e hint top named)
      (fun _ => pure ()) n shape
  finally
    sparkleSynthDepth.set 0

/-- The route of the run that returned `raw` (see the header). -/
def routeOf (n : Name) (raw : Mod) : MetaM (String × Option MachineShape × ConstantInfo) := do
  let g ← gatesOf n
  if g.gate then return ("gate", none, g.ec)
  if g.mixed then return ("mixed", none, g.ec)
  match g.shape with
  | none => return ("legacy", none, g.ec)
  | some shape =>
    let arm? : Option (Option (Mod × Dsn)) ←
      try
        let r ← machineArm n shape
        pure (some r)
      catch _ => pure none
    match arm? with
    | none => return ("machine?(arm threw)", some shape, g.ec)
    | some none => return ("fallthrough", some shape, g.ec)
    | some (some r) =>
      return (if r.1 == raw then "machine" else "machine?(arm differs)", some shape, g.ec)

/-- The route of a declaration from its gates only (no run). -/
def staticRoute (n : Name) : MetaM String := do
  try
    let g ← gatesOf n
    if g.gate then return "gate"
    if g.mixed then return "mixed"
    if g.shape.isSome then return "machine-shape"
    return "legacy"
  catch _ => return "?"

/-- The child module of an entry, as the closing obtains it. -/
def childOf (c : Name) : MetaM (Option Mod) := do
  match Sparkle.Compiler.MachMemory.memChild? c with
  | some md => return some md.1
  | none =>
    try
      let r ← synthesizeChild c
      return some r.1
    catch _ => return none

/-- `Tools.ShippingCallWidths.callWidthsOk` on a shape, the child's outputs
as `(name, width)`. -/
def callWidthsOkS (shape : MachineShape) (nDecl : Nat) (kidOuts : Nat → List (String × Nat)) :
    Bool :=
  (List.range shape.insts.length).all fun k =>
    (kidOuts k).all fun o =>
      o.1 != shape.instFields.getD k "" ||
        ((shape.binders[nDecl + k]?).map (fun bn => kindW bn.2) == some o.2)

/-- `Tools.ShippingPortsMatchRaw.callArgsOk` on a shape. -/
def callArgsOkS (shape : MachineShape) (nDecl : Nat) (kidIns : Nat → List Nat) : Bool :=
  (List.range shape.insts.length).all fun k =>
    (List.range (kidIns k).length).all fun j =>
      ((((shape.insts[k]?).bind fun c => c.2.1[j]?).bind fun a =>
        (shape.binders[nDecl + (shape.insts.length +
          (shape.layout.slots.length + a))]?).map fun bn => kindW bn.2) ==
        (kidIns k)[j]?)

/-- The reference connections whose two emitted widths differ. -/
def connMismatches (C : String → Option (Mod × Sparkle.IR.Semantics.WEnv)) (o : Mod) :
    List String :=
  o.body.flatMap fun st => match st with
    | .inst mn iname conns =>
      match C mn with
      | some (child, _) =>
        conns.filterMap fun c => match c.2 with
          | .ref w =>
            if Tools.ShippingDesignSV.weS o w == Tools.ShippingDesignSV.weS child c.1 then none
            else some (s!"{iname}.{c.1}<->{w}:{Tools.ShippingDesignSV.weS o w}/" ++
              s!"{Tools.ShippingDesignSV.weS child c.1}")
          | _ => none
      | none => [s!"{iname}: module {mn} not in the design"]
    | _ => []

/-- What the shape side says. -/
structure PairRow where
  cwo : String := "-"
  cao : String := "-"
  resOk : Nat := 0
  resN : Nat := 0
  argOk : Nat := 0
  argN : Nat := 0
  arity : String := "-"
  kids : List String := []
  bad : List String := []
  /-- A pair, the arity or a mirror is false. -/
  fails : Bool := false

/-- The per-pair comparison of a shape against the real children. -/
def pairsOf (shape : MachineShape) : MetaM PairRow := do
  if shape.insts.isEmpty then return {}
  let kI := shape.insts.length
  let nS := shape.layout.slots.length
  let nDecl := shape.binders.length - kI - nS - shape.layout.lets
  let mut kidMods : Array (Option Mod) := #[]
  let mut kids : List String := []
  let mut seen : List Name := []
  for (c, _, _) in shape.insts do
    let m? ← childOf c
    kidMods := kidMods.push m?
    unless seen.contains c do
      seen := seen ++ [c]
      let r ← if (Sparkle.Compiler.MachMemory.memChild? c).isSome then pure "memory"
        else staticRoute c
      let tag := if m?.isSome then "" else "(no module)"
      kids := kids ++ [s!"{c}:{r}{tag}"]
  let kidOf (k : Nat) : Option Mod := (kidMods[k]?).bind id
  let kidOuts (k : Nat) : List (String × Nat) := match kidOf k with
    | some m => m.outputs.map fun p => (p.name, tyW p.ty)
    | none => []
  let kidIns (k : Nat) : List Nat := match kidOf k with
    | some m => (Tools.ShippingInstStmtG.inPortsOf m).map fun p =>
        Tools.ShippingDesignSV.weS m p.name
    | none => []
  let mut resOk := 0
  let mut resN := 0
  let mut argOk := 0
  let mut argN := 0
  let mut arity := true
  let mut bad : List String := []
  for k in [0:kI] do
    let some (c, args, _) := shape.insts[k]? | continue
    let some m := kidOf k | continue
    -- the result side: the port the closing connects
    let port? : Option Sparkle.IR.AST.Port :=
      if shape.instFields.isEmpty then
        (match m.outputs with
         | [p] => some p
         | _ => none)
      else m.outputs.find? (fun p => p.name == shape.instFields.getD k "")
    let pW? := (shape.binders[nDecl + k]?).map fun bn => kindW bn.2
    resN := resN + 1
    match port?, pW? with
    | some p, some pW =>
      if tyW p.ty == pW then resOk := resOk + 1
      else bad := bad ++ [s!"res {k} {c}.{p.name}: binder {pW} / port {tyW p.ty}"]
    | _, _ => bad := bad ++ [s!"res {k} {c}: no port or no binder"]
    -- the argument side
    let ins := Tools.ShippingInstStmtG.inPortsOf m
    if ins.length != args.length then
      arity := false
      bad := bad ++ [s!"arity {k} {c}: {args.length} wires / {ins.length} ports"]
    for j in [0:args.length] do
      let some a := args[j]? | continue
      let lW? := (shape.binders[nDecl + (kI + (nS + a))]?).map fun bn => kindW bn.2
      argN := argN + 1
      match ins[j]?, lW? with
      | some q, some lW =>
        if tyW q.ty == lW then argOk := argOk + 1
        else bad := bad ++ [s!"arg {k}.{j} {c}.{q.name}: let {lW} / port {tyW q.ty}"]
      | _, _ => bad := bad ++ [s!"arg {k}.{j} {c}: no port or no let binder"]
  let cwo := callWidthsOkS shape nDecl kidOuts
  let cao := callArgsOkS shape nDecl kidIns
  return {
    cwo := bs cwo, cao := bs cao, resOk := resOk, resN := resN, argOk := argOk, argN := argN
    arity := bs arity, kids := kids, bad := bad
    fails := !cwo || !cao || !arity || resOk != resN || argOk != argN }

/-- One candidate: its line and whether it is a width mismatch with success. -/
def hunt (n : Name) : MetaM (String × Bool) := do
  let (raw, D) ← synthesizeCombinationalCore n [] false
  let (route, shape?, _) ← routeOf n raw
  -- the full entry (it also fills the child cache again)
  let (b, _) ← synthesizeCombinational n
  let C := Tools.ShippingMachineLinked.childMap D.modules
  let hasInst := raw.body.any Sparkle.IR.Machine.isInst
  let widRaw := Tools.ShippingHierOpen.instOutWidthsOk C (Sparkle.IR.RegDedup.declWidth raw) raw.body
  let pmRaw := Tools.ShippingDesignSV.portsMatchB C raw
  let widB := Tools.ShippingHierOpen.instOutWidthsOk C (Sparkle.IR.RegDedup.declWidth b) b.body
  let pmB := Tools.ShippingDesignSV.portsMatchB C b
  let pr ← match shape? with
    | some shape => pairsOf shape
    | none => pure ({} : PairRow)
  let bad := connMismatches C raw ++ pr.bad
  let mismatch := hasInst &&
    (!widRaw || !pmRaw || !widB || !pmB || (route == "machine" && pr.fails))
  let line :=
    s!"compiled=T route={route} callWidthsOk={pr.cwo} callArgsOk={pr.cao} " ++
    s!"instOutWidthsOk(raw)={bs widRaw} portsMatchB(raw)={bs pmRaw} inst={bs hasInst} " ++
    s!"instOutWidthsOk(b)={bs widB} portsMatchB(b)={bs pmB} " ++
    s!"res={pr.resOk}/{pr.resN} args={pr.argOk}/{pr.argN} arity={pr.arity} " ++
    s!"kids={pr.kids} bad={bad}"
  return (line, mismatch)

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let all := huntParents ++
    (Tests.Compiler.PrintArtifactCensusTest.candidates.filter fun n => !huntParents.contains n)
  let mut total := 0
  let mut compiled := 0
  let mut absent : List Name := []
  let mut failed : List Name := []
  let mut hits : List Name := []
  for n in all do
    total := total + 1
    if !env.contains n then
      absent := absent ++ [n]
      logInfo m!"CALLWIDTH {n}: ABSENT (no such declaration in this build)"
    else
      try
        let (line, mismatch) ← hunt n
        compiled := compiled + 1
        if mismatch then hits := hits ++ [n]
        logInfo m!"CALLWIDTH {n}: {line}"
      catch e =>
        failed := failed ++ [n]
        let r ← staticRoute n
        logInfo m!"CALLWIDTH {n}: compiled=F route={r} callWidthsOk=- callArgsOk=- instOutWidthsOk(raw)=- portsMatchB(raw)=- error: {e.toMessageData}"
  logInfo m!"CALLWIDTH HUNT: candidates {total}; compiled {compiled}; width mismatch with success {hits.length} {hits}; absent {absent.length} {absent}; compile failed {failed.length} {failed}"

end Tests.Compiler.CallWidthHuntTest

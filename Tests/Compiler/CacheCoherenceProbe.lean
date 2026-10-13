import Lean.Elab.Command
import Tests.Compiler.SubInstanceKeyTest
import Tests.Compiler.ShippingMachineSeqTest

/-! # The child cache and module NAMES: two declarations whose modules have one name (probe)

LOGS ONLY — nothing here asserts, nothing throws. Not in `Tests.AllTests`.
WRITTEN, NOT BUILT (par/a-31): every "PREDICTED" below is a prediction from
reading `Sparkle/Compiler/Elab.lean` at `edd9496c`
(`docs/parallel/A-cache-coherence.md` §1), not an observation.

## The claim that is probed

"In the child cache, two modules of one NAME held by the entries of two
different declarations are EQUAL" (`Tools.ShippingCallsKidsS.Agree`, asked
of the end world of a closing). The cache is keyed by the declaration
`Name` (`synthesizeChild`, Elab 8845–8849); a module is named by a STRING,
and every design is joined BY NAME, first come first kept
(`instAddModules` 8456–8461, `Rec.handleDefinitionUnfold` 6545–6551,
`Sparkle.IR.Machine.designWith`). So the claim needs: different
declarations never give one module name. Two source-level ways to break it:

* **N** — `Name.toString` is not injective. A name whose ROOT component
  starts with `#` (or `?`) is printed WITHOUT escaping
  (`Lean.Name.toStringWithToken`, `maybePseudoSyntax`): `«#ccp.k»` (one
  component) and `«#ccp».k` (two) both print `#ccp.k`.
* **M** — a memory child is BUILT, not compiled, under the fixed name
  `SparkleMem_{combo|sync}_{aw}_{dw}` (`MachMemory.memModule`); a declaration
  of that name at the root gives a different module of the same name.

## The declarations

* `«#ccp.k»` (`x + 1`), `«#ccp».k` (`x + 2`): combinational children.
  `nA` calls the first, `nB` the second, `nTop = nA x + nB x`.
  `nDirect` calls both itself.
* `«#ccp.c»` / `«#ccp».c`: `cnt` (`ShippingMachineSeqTest`) counting by 1 /
  by 2. `mA` / `mB`: `mid2`'s shape over each. `mTop`: `mixDeep`'s shape
  over `mA`, `mB`.
* `SparkleMem_combo_4_8` at the root (`wd + 1`); `memKid`: `memCounter`
  with the tag; `mmTop = memKid we wa wd + SparkleMem_combo_4_8 wa wd`.

## The lines

    CACHECOH NAMES: <n1> / <n2> print <s1> / <s2>: equal=<T/F>
    CACHECOH <label> top <top>: route=<…> threw=<T/F> [<message>]
    CACHECOH <label> ENTRY <decl>: module=<name> design=[<names>]
    CACHECOH <label> CLASH <decl> / <decl'> @ <module name>
    CACHECOH <label> COHERENT=<T/F> (<n> clashes)
    CACHECOH <label> DESIGN: modules=[<names>] named <shared>: <n>
    CACHECOH <label> DESIGN MODULE <name> STMT <i>: <statement>
    CACHECOH <label> TEXT: <the SystemVerilog>
    CACHECOH <label> MACHINE ARM: shape=<T/F> returned some=<T/F/threw>

PREDICTED:

* `NAMES`: `equal=T` for the two pairs.
* `N` (`nTop`): `COHERENT=F`; the design holds ONE module named `#ccp.k`
  (the first registered, `x + 1`) and `nB`'s instance of `#ccp.k` is bound
  to it — source `nB x = (x + 2) + x`, emitted `(x + 1) + x`. No error.
* `Nd` (`nDirect`): `COHERENT=F`, one module `#ccp.k`, both instances on it.
* `Mc` (`mTop`): `COHERENT=F`; `MACHINE ARM: shape=T returned some=F` (the
  pure closing finds two visited modules of one name, MachineInstG 140–141)
  although the callees `mA`, `mB` print differently, neither prints as a
  descendant of itself, and the parent prints as none of them — the name
  hypotheses of `Tools.ShippingCallsKidsS.closes_of_agree`; the real entry
  then takes the legacy arm, and the design holds one module `#ccp.c`.
* `M` (`mmTop`): `COHERENT=F` if `memKid` took the machine route (its design
  then holds the built memory module); the design holds one module named
  `SparkleMem_combo_4_8` with the ports of whichever came first.

NOT established: all of the above; whether a later stage (the checked
printer, `designCheck`) refuses any of these designs; whether the entry
accepts a declaration whose name starts with `#` at all (if it throws, the
`threw=T` line says so and `N`, `Nd`, `Mc` show nothing). -/
namespace Tests.Compiler.CacheCoherenceProbe
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tests.Compiler.CallWidthHuntTest (Mod Dsn bs gatesOf resetRefs machineArm)
open Tests.Compiler.NestedLetCacheTest (stmtStr routeStr designOf)
open Tests.Compiler.SubInstanceKeyTest (runFull)
open Sparkle.Tests.Compiler.ShippingMachineSeqTest (CntOut)

/-! ### N: two declarations printing `#ccp.k` -/

@[hardware_module]
def _root_.«#ccp.k» {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  x + (Signal.pure 1#8 : Signal dom (BitVec 8))

@[hardware_module]
def _root_.«#ccp».k {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  x + (Signal.pure 2#8 : Signal dom (BitVec 8))

@[hardware_module]
def nA {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  «#ccp.k» x + x

@[hardware_module]
def nB {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  «#ccp».k x + x

def nTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  nA x + nB x

def nDirect (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  «#ccp.k» x + «#ccp».k x

/-! ### Mc: the same under a machine parent (`mixDeep`'s shape) -/

@[hardware_module]
def _root_.«#ccp.c» {dom : DomainConfig} (en : Signal dom Bool) : CntOut dom :=
  circuit do
    let c ← Signal.reg 0#8
    let cs := (c : Signal dom (BitVec 8))
    c <~ Signal.mux en (cs + (Signal.pure 1#8 : Signal dom (BitVec 8))) cs
    return ({ n := cs, hit := cs === (Signal.pure 7#8 : Signal dom (BitVec 8)) } : CntOut dom)

@[hardware_module]
def _root_.«#ccp».c {dom : DomainConfig} (en : Signal dom Bool) : CntOut dom :=
  circuit do
    let c ← Signal.reg 0#8
    let cs := (c : Signal dom (BitVec 8))
    c <~ Signal.mux en (cs + (Signal.pure 2#8 : Signal dom (BitVec 8))) cs
    return ({ n := cs, hit := cs === (Signal.pure 7#8 : Signal dom (BitVec 8)) } : CntOut dom)

@[hardware_module]
def mA {dom : DomainConfig} (en : Signal dom Bool) : CntOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let k := «#ccp.c» en
    r <~ Signal.mux k.hit (rs + k.n) rs
    return ({ n := rs, hit := k.hit } : CntOut dom)

@[hardware_module]
def mB {dom : DomainConfig} (en : Signal dom Bool) : CntOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let k := «#ccp».c en
    r <~ Signal.mux k.hit (rs + k.n) rs
    return ({ n := rs, hit := k.hit } : CntOut dom)

def mTop (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let a := mA en
    let b := mB en
    r <~ Signal.mux a.hit (rs + b.n) rs
    return rs

/-! ### M: a declaration with the built memory module's name -/

@[hardware_module]
def _root_.SparkleMem_combo_4_8 {dom : DomainConfig} (wa : Signal dom (BitVec 4))
    (wd : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  wd + (Signal.pure 1#8 : Signal dom (BitVec 8))

@[hardware_module]
def memKid (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let rd := Signal.memoryComboRead wa wd we addr
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 rd)
  Signal.snd st

def mmTop (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  memKid we wa wd + SparkleMem_combo_4_8 wa wd

def k1Name : Name := Name.mkStr Name.anonymous "#ccp.k"
def k2Name : Name := Name.mkStr (Name.mkStr Name.anonymous "#ccp") "k"
def c1Name : Name := Name.mkStr Name.anonymous "#ccp.c"
def c2Name : Name := Name.mkStr (Name.mkStr Name.anonymous "#ccp") "c"
def nTopName : Name := `Tests.Compiler.CacheCoherenceProbe.nTop
def nDirectName : Name := `Tests.Compiler.CacheCoherenceProbe.nDirect
def mTopName : Name := `Tests.Compiler.CacheCoherenceProbe.mTop
def mmTopName : Name := `Tests.Compiler.CacheCoherenceProbe.mmTop

/-- The modules an entry holds: its module and its design's. -/
def modsOf (y : Mod × Dsn) : List Mod := y.1 :: y.2.modules

/-- The entries of two DIFFERENT declarations holding two unequal modules of
one name: `decl / decl' @ name`. -/
def clashes (es : List (Name × (Mod × Dsn))) : List String := Id.run do
  let mut out : Array String := #[]
  for e in es do
    for e' in es do
      if e.1 != e'.1 then
        for a in modsOf e.2 do
          for b in modsOf e'.2 do
            if a.name == b.name && a != b then
              out := out.push (toString e.1 ++ " / " ++ toString e'.1 ++ " @ " ++ a.name)
  return out.toList

/-- One top: the real entry from reset refs at depth 0, the cache it leaves,
the clashes, the design; then the machine arm alone at depth 1. Returns
whether the cache the run left is incoherent. -/
def probe (label : String) (top : Name) (shared : String) : MetaM Bool := do
  let (t?, tmsg) ← runFull top
  let es : List (Name × (Mod × Dsn)) := (← (sparkleChildCache.get : IO _)).toList
  let route ← routeStr top
  logInfo m!"CACHECOH {label} top {top}: route={route} threw={bs t?.isNone} {tmsg}"
  for e in es do
    let names : List String := e.2.2.modules.map fun m => m.name
    logInfo m!"CACHECOH {label} ENTRY {e.1}: module={e.2.1.name} design={names}"
  let cl : List String := clashes es
  for c in cl do
    logInfo m!"CACHECOH {label} CLASH {c}"
  logInfo m!"CACHECOH {label} COHERENT={bs cl.isEmpty} ({cl.length} clashes)"
  match t? with
  | none => pure ()
  | some t =>
    let d : Dsn := designOf t
    let names : List String := d.modules.map fun m => m.name
    let same : List Mod := d.modules.filter fun m => m.name == shared
    logInfo m!"CACHECOH {label} DESIGN: modules={names} named {shared}: {same.length}"
    for m in d.modules do
      let mut i : Nat := 0
      for s in m.body do
        logInfo m!"CACHECOH {label} DESIGN MODULE {m.name} STMT {i}: {stmtStr s}"
        i := i + 1
    let text := Sparkle.Backend.Verilog.toVerilogDesignChecked d
    logInfo m!"CACHECOH {label} TEXT:\n{text}"
  -- the machine arm alone (the statement `MachineClosesAt` is about)
  let shape? : Option MachineShape ←
    try
      let g ← gatesOf top
      pure g.shape
    catch _ => pure none
  match shape? with
  | none => logInfo m!"CACHECOH {label} MACHINE ARM: shape=F"
  | some shape =>
    let arm : String ←
      try
        let r ← machineArm top shape
        pure (bs r.isSome)
      catch _ => pure "threw"
    logInfo m!"CACHECOH {label} MACHINE ARM: shape=T returned some={arm}"
  resetRefs
  sparkleSynthDepth.set 0
  return !cl.isEmpty

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let s1 : String := toString k1Name
  let s2 : String := toString k2Name
  logInfo m!"CACHECOH NAMES: {repr k1Name} / {repr k2Name} print {s1} / {s2}: equal={bs (s1 == s2)}"
  let t1 : String := toString c1Name
  let t2 : String := toString c2Name
  logInfo m!"CACHECOH NAMES: {repr c1Name} / {repr c2Name} print {t1} / {t2}: equal={bs (t1 == t2)}"
  let n ← probe "N" nTopName s1
  let nd ← probe "Nd" nDirectName s1
  let mc ← probe "Mc" mTopName t1
  let m ← probe "M" mmTopName "SparkleMem_combo_4_8"
  resetRefs
  sparkleSynthDepth.set 0
  logInfo m!"CACHECOH: incoherent N={bs n} Nd={bs nd} Mc={bs mc} M={bs m} (logged only; nothing is asserted)"

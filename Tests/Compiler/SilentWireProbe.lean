/-
  Silent-wire audit probes (see notes/compiler/silent-wire-audit.md).
  Each probe is a tiny module whose correct wiring is unambiguous; the verdict
  per probe is computed at elaboration time and printed by
  `silent-wire-probe` (Tests/Drivers/SilentWireProbeMain.lean).  Nothing here
  aborts the build.
-/
import Sparkle
import Sparkle.Compiler.Elab
import Tests.Compiler.SilentWireProbeLib

namespace Sparkle.Tests.Compiler.SilentWireProbe

open Sparkle.Core.Domain
open Sparkle.Core.Signal

set_option linter.deprecated false

-- ---------------------------------------------------------------------------
-- Records.  `TwoOut`/`counter` mirror ProjRegisterInputTest.
-- ---------------------------------------------------------------------------
structure TwoOut (dom : DomainConfig) where
  val  : Signal dom (BitVec 8)
  done : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (TwoOut dom) dom := ⟨⟩

@[hardware_module]
def counter {dom : DomainConfig} (start : Signal dom Bool) : TwoOut dom := circuit do
  let cR ← Signal.reg (0#8)
  let c := (cR : Signal dom (BitVec 8))
  cR <~ Signal.mux start (Signal.pure 0#8) (c + (Signal.pure 1#8 : Signal dom (BitVec 8)))
  return ({ val := c, done := (c === 3#8) } : TwoOut dom)

structure Pair2 (dom : DomainConfig) where
  a    : Signal dom (BitVec 8)
  flag : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (Pair2 dom) dom := ⟨⟩

/-- plain (non-attributed) 2-field record of DIFFERENT widths -/
def plainPair {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Pair2 dom :=
  { a := x + (Signal.pure 1#8 : Signal dom (BitVec 8)), flag := (x === 5#8) }

structure ThreeOut (dom : DomainConfig) where
  a    : Signal dom (BitVec 8)
  flag : Signal dom Bool
  b    : Signal dom (BitVec 4)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (ThreeOut dom) dom := ⟨⟩

def plainThree {dom : DomainConfig} (x : Signal dom (BitVec 8)) : ThreeOut dom :=
  { a := x + (Signal.pure 1#8 : Signal dom (BitVec 8)),
    flag := (x === 5#8),
    b := x.map (fun v => v.extractLsb' 0 4) }

-- ---------------------------------------------------------------------------
-- `.proj` case, 2-field slice (Elab.lean `.proj`): field read off a record
-- that the port-map branches cannot see (`id` hides the call head).
-- ---------------------------------------------------------------------------
def pj01 {dom : DomainConfig} (start : Signal dom Bool) : Signal dom Bool := circuit do
  let r ← Signal.reg false
  r <~ (id (counter start)).done
  return (r : Signal dom Bool)
#probe "pj01_hwmod_id_done" pj01 "reg" "counter.done"

def pj02 {dom : DomainConfig} (start : Signal dom Bool) : Signal dom (BitVec 8) := circuit do
  let r ← Signal.reg (0#8)
  r <~ (id (counter start)).val
  return (r : Signal dom (BitVec 8))
#probe "pj02_hwmod_id_val" pj02 "reg" "counter.val"

def pj03 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom Bool := circuit do
  let r ← Signal.reg false
  r <~ (plainPair x).flag
  return (r : Signal dom Bool)
#probe "pj03_plain2_direct_flag" pj03 "reg" "plainPair.flag"

def pj04 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom Bool := circuit do
  let r ← Signal.reg false
  let p := plainPair x
  r <~ p.flag
  return (r : Signal dom Bool)
#probe "pj04_plain2_let_flag" pj04 "reg" "plainPair.flag"

def pj05 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom Bool := circuit do
  let r ← Signal.reg false
  r <~ (id (plainPair x)).flag
  return (r : Signal dom Bool)
#probe "pj05_plain2_id_flag" pj05 "reg" "plainPair.flag"

def pj06 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := circuit do
  let r ← Signal.reg (0#8)
  r <~ (id (plainPair x)).a
  return (r : Signal dom (BitVec 8))
#probe "pj06_plain2_id_a" pj06 "reg" "plainPair.a"

def pj07 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom Bool := circuit do
  let r ← Signal.reg false
  r <~ (id (plainThree x)).flag
  return (r : Signal dom Bool)
#probe "pj07_plain3_id_flag" pj07 "reg" "plainThree.flag"

def pj08 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := circuit do
  let r ← Signal.reg (0#8)
  r <~ (id (plainThree x)).a
  return (r : Signal dom (BitVec 8))
#probe "pj08_plain3_id_a" pj08 "reg" "plainThree.a"

def pj09 {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 4) := circuit do
  let r ← Signal.reg (0#4)
  r <~ (id (plainThree x)).b
  return (r : Signal dom (BitVec 4))
#probe "pj09_plain3_id_b" pj09 "reg" "in:x[3:0]"

def pj10 {dom : DomainConfig} (x : Signal dom (BitVec 8)) (f : Signal dom Bool) :
    Signal dom Bool := circuit do
  let r ← Signal.reg false
  r <~ ({ a := x, flag := f } : Pair2 dom).flag
  return (r : Signal dom Bool)
#probe "pj10_ctor_flag" pj10 "reg" "in:f"

def pj11 {dom : DomainConfig} (x : Signal dom (BitVec 8)) (f : Signal dom Bool) :
    Signal dom (BitVec 8) := circuit do
  let r ← Signal.reg (0#8)
  r <~ ({ a := x, flag := f } : Pair2 dom).a
  return (r : Signal dom (BitVec 8))
#probe "pj11_ctor_a" pj11 "reg" "in:x"

-- Record update `{ c with val := v }` builds `TwoOut.mk v c.done` around a call.
def pj12 {dom : DomainConfig} (start : Signal dom Bool) (v : Signal dom (BitVec 8)) :
    Signal dom Bool := circuit do
  let r ← Signal.reg false
  r <~ ({ counter start with val := v } : TwoOut dom).done
  return (r : Signal dom Bool)
#probe "pj12_update_done" pj12 "reg" "counter.done"

def pj13 {dom : DomainConfig} (start : Signal dom Bool) (v : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := circuit do
  let r ← Signal.reg (0#8)
  r <~ ({ counter start with val := v } : TwoOut dom).val
  return (r : Signal dom (BitVec 8))
#probe "pj13_update_val" pj13 "reg" "in:v"

-- ---------------------------------------------------------------------------
-- Prod.fst / Prod.snd / Signal.fst / Signal.snd on packed products.
-- Packed layout: fst in the high bits, snd in the low bits.
-- ---------------------------------------------------------------------------
def ps01 {dom : DomainConfig} (p : Signal dom (BitVec 8 × Bool)) : Signal dom (BitVec 8) := circuit do
  let r ← Signal.reg (0#8)
  r <~ Signal.fst p
  return (r : Signal dom (BitVec 8))
#probe "ps01_Signal_fst_8x1" ps01 "reg" "in:p[8:1]"

def ps02 {dom : DomainConfig} (p : Signal dom (BitVec 8 × Bool)) : Signal dom Bool := circuit do
  let r ← Signal.reg false
  r <~ Signal.snd p
  return (r : Signal dom Bool)
#probe "ps02_Signal_snd_8x1" ps02 "reg" "in:p[0:0]"

def ps03 {dom : DomainConfig} (p : Signal dom (BitVec 8 × Bool)) : Signal dom (BitVec 8) := circuit do
  let r ← Signal.reg (0#8)
  r <~ p.map Prod.fst
  return (r : Signal dom (BitVec 8))
#probe "ps03_map_Prod_fst_8x1" ps03 "reg" "in:p[8:1]"

def ps04 {dom : DomainConfig} (p : Signal dom (BitVec 8 × Bool)) : Signal dom Bool := circuit do
  let r ← Signal.reg false
  r <~ p.map Prod.snd
  return (r : Signal dom Bool)
#probe "ps04_map_Prod_snd_8x1" ps04 "reg" "in:p[0:0]"

def ps05 {dom : DomainConfig} (q : Signal dom (BitVec 8 × (BitVec 4 × Bool))) :
    Signal dom (BitVec 8) := circuit do
  let r ← Signal.reg (0#8)
  r <~ Signal.fst q
  return (r : Signal dom (BitVec 8))
#probe "ps05_nested_fst" ps05 "reg" "in:q[12:5]"

def ps06 {dom : DomainConfig} (q : Signal dom (BitVec 8 × (BitVec 4 × Bool))) :
    Signal dom (BitVec 4) := circuit do
  let r ← Signal.reg (0#4)
  r <~ Signal.fst (Signal.snd q)
  return (r : Signal dom (BitVec 4))
#probe "ps06_nested_snd_fst" ps06 "reg" "in:q[4:0][4:1]"

def ps07 {dom : DomainConfig} (q : Signal dom (BitVec 8 × (BitVec 4 × Bool))) :
    Signal dom Bool := circuit do
  let r ← Signal.reg false
  r <~ Signal.snd (Signal.snd q)
  return (r : Signal dom Bool)
#probe "ps07_nested_snd_snd" ps07 "reg" "in:q[4:0][0:0]"

def ps08 {dom : DomainConfig} (p : Signal dom (Bool × BitVec 8)) : Signal dom Bool := circuit do
  let r ← Signal.reg false
  r <~ Signal.fst p
  return (r : Signal dom Bool)
#probe "ps08_fst_1x8" ps08 "reg" "in:p[8:8]"

def ps09 {dom : DomainConfig} (a : Signal dom (BitVec 8)) (b : Signal dom Bool) :
    Signal dom Bool := circuit do
  let r ← Signal.reg false
  r <~ Signal.snd (Sparkle.Core.Signal.bundle2 a b)
  return (r : Signal dom Bool)
#probe "ps09_bundle2_snd" ps09 "reg" "cat(in:a, in:b)[0:0]"

-- ---------------------------------------------------------------------------
-- Prod.rec continuation (`pure (t1, t1)` fallback): destructuring a product
-- signal via the deprecated `unbundle2`.
-- ---------------------------------------------------------------------------
def usePair {dom : DomainConfig} (t : Signal dom (BitVec 8) × Signal dom Bool) : Signal dom Bool :=
  match t with | (_, b) => b

def pr01 {dom : DomainConfig} (p : Signal dom (BitVec 8 × Bool)) : Signal dom Bool :=
  usePair (unbundle2 p)
#probe "pr01_match_unbundle2_snd" pr01 "out" "in:p[0:0]"

-- ---------------------------------------------------------------------------
-- Width defaults (`| _ => 8`, `extractWidth ... return 8`).
-- ---------------------------------------------------------------------------
@[irreducible] def W12 : Nat := 12

def pw01 {dom : DomainConfig} (x : Signal dom (BitVec W12)) : Signal dom (BitVec W12) :=
  x + x

open Lean Elab Command in
/-- Width (in bits) of the named input port, compared with `n`. -/
elab "#probeInputWidth " tag:str id:ident port:str n:num : command => do
  let declName ← liftCoreM (Lean.resolveGlobalConstNoOverload id)
  let r ← liftTermElabM do
    try
      let (m, _) ← Sparkle.Compiler.Elab.synthesizeCombinational declName
      return Except.ok (m.inputs.find? (·.name == port.getString) |>.map (·.ty))
    catch ex => return Except.error (← ex.toMessageData.toString)
  match r with
  | .error msg => record tag.getString s!"(b) REFUSED with error: {((msg.splitOn "\n").headD msg).take 160}"
  | .ok none => record tag.getString "(d) port not found"
  | .ok (some ty) =>
    if ty.bitWidth == n.getNat then record tag.getString s!"(c) correct: input {port.getString} is {repr ty}"
    else record tag.getString s!"(a) SILENT WRONG: input {port.getString} is {repr ty}, expected {n.getNat} bits"

#probeInputWidth "pw01_irreducible_width_input" pw01 "_gen_x" 12

def pw02 {dom : DomainConfig} {n : Nat} (x : Signal dom (BitVec n)) : Signal dom (BitVec n) :=
  x + x
#probeInputWidth "pw02_fvar_width_input" pw02 "_gen_x" 16

-- ---------------------------------------------------------------------------
-- Instance bookkeeping: two calls with DIFFERENT arguments must stay two instances.
-- ---------------------------------------------------------------------------
def pd01 {dom : DomainConfig} (s1 s2 : Signal dom Bool) : Signal dom Bool := circuit do
  let r ← Signal.reg false
  r <~ (counter s1).done &&& (counter s2).done
  return (r : Signal dom Bool)
#probe "pd01_two_calls_two_instances" pd01 "ninst:counter" "2"

-- ---------------------------------------------------------------------------
-- `extends` record: `w.done` is `.proj TwoOut 1 (.proj Wide 0 w)`.
-- ---------------------------------------------------------------------------
structure Wide (dom : DomainConfig) extends TwoOut dom where
  extra : Signal dom (BitVec 4)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (Wide dom) dom := ⟨⟩

@[hardware_module]
def wide {dom : DomainConfig} (start : Signal dom Bool) : Wide dom :=
  let c := counter start
  { val := c.val, done := c.done, extra := c.val.map (fun v => v.extractLsb' 0 4) }

def pe01 {dom : DomainConfig} (start : Signal dom Bool) : Signal dom Bool := circuit do
  let r ← Signal.reg false
  let w := wide start
  r <~ w.done
  return (r : Signal dom Bool)
#probe "pe01_extends_done" pe01 "reg" "wide.done"

def pe02 {dom : DomainConfig} (start : Signal dom Bool) : Signal dom (BitVec 4) := circuit do
  let r ← Signal.reg (0#4)
  let w := wide start
  r <~ w.extra
  return (r : Signal dom (BitVec 4))
#probe "pe02_extends_extra" pe02 "reg" "wide.extra"

-- ---------------------------------------------------------------------------
-- Name-based dispatch (`name.toString.endsWith ".mux" / ".register"`).
-- ---------------------------------------------------------------------------
def Mine.mux {dom : DomainConfig} (c : Signal dom Bool) (t e : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := Signal.mux c e t   -- deliberately swapped

def pn01 {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := circuit do
  let r ← Signal.reg (0#8)
  r <~ Mine.mux c a b
  return (r : Signal dom (BitVec 8))
#probe "pn01_user_mux_swapped" pn01 "reg" "mux(in:c, in:b, in:a)"

def Mine.register {dom : DomainConfig} (i : BitVec 8) (s : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := Signal.register i (s + (Signal.pure 1#8 : Signal dom (BitVec 8)))

def pn02 {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Mine.register 0#8 a
#probe "pn02_user_register_adds_one" pn02 "out" "~add"

end Sparkle.Tests.Compiler.SilentWireProbe

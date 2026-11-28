/-
  Unary `Signal.map` / `<$>` lambdas whose body is `!` (or `~~~`, `-`) applied
  to a COMPOUND term, e.g. `(fun c => !(c == 0#7)) <$> s`.

  The unary-primitive shortcut in the elaborator used to key on the head of
  the lambda body only: `not (c == 0)` has head `not`, so it was lowered as
  `~c` (a bitwise NOT of the signal), dropping the inner comparison.  For a
  7-bit `c` that is `(7'(c ^ 7'd127)) & 1'd1`, i.e. NOT bit 0 of `c`.

  This test synthesises each variant with `synthesizeCombinational`, evaluates
  the SOURCE (`Signal.atTime`) and the returned IR (`Sparkle.IR.Semantics`) at
  several input values and requires equal results.  The checks are
  `run_meta`, so a mismatch fails the build of this module.

  Counts: 7 forms x 7 width/constant cases = 49 BitVec synthesis calls, plus
  6 Bool forms = 55 synthesis calls in the equivalence block (1 synthesis
  each); value checks are 17 inputs per BitVec call (`testVals`), 2 per
  `chkB1` call, 4 per `chkB2` call.

  Controls: the operators `!=`, `==`, `~~~`, `-` must use the standard
  instances.  Non-standard `BEq`/`Neg`/`Complement` instances over a compound
  body must be REFUSED at synthesis; standard `-(c + k)` must evaluate like the
  source.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.IR.Semantics

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.IR.Semantics
open Lean

namespace Sparkle.Tests.Compiler.MapNotEq

set_option maxRecDepth 100000

def mNotEq_1_1 {dom : DomainConfig} (s : Signal dom (BitVec 1)) : Signal dom (Bool) :=
  (fun c => !(c == 1#1)) <$> s

def mNotNe_1_1 {dom : DomainConfig} (s : Signal dom (BitVec 1)) : Signal dom (Bool) :=
  (fun c => !(c != 1#1)) <$> s

def mNe_1_1 {dom : DomainConfig} (s : Signal dom (BitVec 1)) : Signal dom (Bool) :=
  (fun c => c != 1#1) <$> s

def mEq_1_1 {dom : DomainConfig} (s : Signal dom (BitVec 1)) : Signal dom (Bool) :=
  (fun c => c == 1#1) <$> s

def mNotNotEq_1_1 {dom : DomainConfig} (s : Signal dom (BitVec 1)) : Signal dom (Bool) :=
  (fun c => !(!(c == 1#1))) <$> s

def mInv_1_1 {dom : DomainConfig} (s : Signal dom (BitVec 1)) : Signal dom (BitVec 1) :=
  (fun c => ~~~c) <$> s

def mInvAdd_1_1 {dom : DomainConfig} (s : Signal dom (BitVec 1)) : Signal dom (BitVec 1) :=
  (fun c => ~~~(c + 1#1)) <$> s

def mNotEq_7_0 {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (Bool) :=
  (fun c => !(c == 0#7)) <$> s

def mNotNe_7_0 {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (Bool) :=
  (fun c => !(c != 0#7)) <$> s

def mNe_7_0 {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (Bool) :=
  (fun c => c != 0#7) <$> s

def mEq_7_0 {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (Bool) :=
  (fun c => c == 0#7) <$> s

def mNotNotEq_7_0 {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (Bool) :=
  (fun c => !(!(c == 0#7))) <$> s

def mInv_7_0 {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (BitVec 7) :=
  (fun c => ~~~c) <$> s

def mInvAdd_7_0 {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (BitVec 7) :=
  (fun c => ~~~(c + 0#7)) <$> s

def mNotEq_7_5 {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (Bool) :=
  (fun c => !(c == 5#7)) <$> s

def mNotNe_7_5 {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (Bool) :=
  (fun c => !(c != 5#7)) <$> s

def mNe_7_5 {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (Bool) :=
  (fun c => c != 5#7) <$> s

def mEq_7_5 {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (Bool) :=
  (fun c => c == 5#7) <$> s

def mNotNotEq_7_5 {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (Bool) :=
  (fun c => !(!(c == 5#7))) <$> s

def mInv_7_5 {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (BitVec 7) :=
  (fun c => ~~~c) <$> s

def mInvAdd_7_5 {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (BitVec 7) :=
  (fun c => ~~~(c + 5#7)) <$> s

def mNotEq_8_0 {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (Bool) :=
  (fun c => !(c == 0#8)) <$> s

def mNotNe_8_0 {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (Bool) :=
  (fun c => !(c != 0#8)) <$> s

def mNe_8_0 {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (Bool) :=
  (fun c => c != 0#8) <$> s

def mEq_8_0 {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (Bool) :=
  (fun c => c == 0#8) <$> s

def mNotNotEq_8_0 {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (Bool) :=
  (fun c => !(!(c == 0#8))) <$> s

def mInv_8_0 {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun c => ~~~c) <$> s

def mInvAdd_8_0 {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun c => ~~~(c + 0#8)) <$> s

def mNotEq_8_200 {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (Bool) :=
  (fun c => !(c == 200#8)) <$> s

def mNotNe_8_200 {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (Bool) :=
  (fun c => !(c != 200#8)) <$> s

def mNe_8_200 {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (Bool) :=
  (fun c => c != 200#8) <$> s

def mEq_8_200 {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (Bool) :=
  (fun c => c == 200#8) <$> s

def mNotNotEq_8_200 {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (Bool) :=
  (fun c => !(!(c == 200#8))) <$> s

def mInv_8_200 {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun c => ~~~c) <$> s

def mInvAdd_8_200 {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun c => ~~~(c + 200#8)) <$> s

def mNotEq_32_0 {dom : DomainConfig} (s : Signal dom (BitVec 32)) : Signal dom (Bool) :=
  (fun c => !(c == 0#32)) <$> s

def mNotNe_32_0 {dom : DomainConfig} (s : Signal dom (BitVec 32)) : Signal dom (Bool) :=
  (fun c => !(c != 0#32)) <$> s

def mNe_32_0 {dom : DomainConfig} (s : Signal dom (BitVec 32)) : Signal dom (Bool) :=
  (fun c => c != 0#32) <$> s

def mEq_32_0 {dom : DomainConfig} (s : Signal dom (BitVec 32)) : Signal dom (Bool) :=
  (fun c => c == 0#32) <$> s

def mNotNotEq_32_0 {dom : DomainConfig} (s : Signal dom (BitVec 32)) : Signal dom (Bool) :=
  (fun c => !(!(c == 0#32))) <$> s

def mInv_32_0 {dom : DomainConfig} (s : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  (fun c => ~~~c) <$> s

def mInvAdd_32_0 {dom : DomainConfig} (s : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  (fun c => ~~~(c + 0#32)) <$> s

def mNotEq_32_1000 {dom : DomainConfig} (s : Signal dom (BitVec 32)) : Signal dom (Bool) :=
  (fun c => !(c == 1000#32)) <$> s

def mNotNe_32_1000 {dom : DomainConfig} (s : Signal dom (BitVec 32)) : Signal dom (Bool) :=
  (fun c => !(c != 1000#32)) <$> s

def mNe_32_1000 {dom : DomainConfig} (s : Signal dom (BitVec 32)) : Signal dom (Bool) :=
  (fun c => c != 1000#32) <$> s

def mEq_32_1000 {dom : DomainConfig} (s : Signal dom (BitVec 32)) : Signal dom (Bool) :=
  (fun c => c == 1000#32) <$> s

def mNotNotEq_32_1000 {dom : DomainConfig} (s : Signal dom (BitVec 32)) : Signal dom (Bool) :=
  (fun c => !(!(c == 1000#32))) <$> s

def mInv_32_1000 {dom : DomainConfig} (s : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  (fun c => ~~~c) <$> s

def mInvAdd_32_1000 {dom : DomainConfig} (s : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  (fun c => ~~~(c + 1000#32)) <$> s

def bNot {dom : DomainConfig} (a : Signal dom Bool) : Signal dom Bool :=
  (fun x => !x) <$> a
def bNotNot {dom : DomainConfig} (a : Signal dom Bool) : Signal dom Bool :=
  (fun x => !(!x)) <$> a
def bAndT {dom : DomainConfig} (a : Signal dom Bool) : Signal dom Bool :=
  (fun x => !(x && true)) <$> a
def bAnd {dom : DomainConfig} (a b : Signal dom Bool) : Signal dom Bool :=
  (fun x y => !(x && y)) <$> a <*> b
def bOr {dom : DomainConfig} (a b : Signal dom Bool) : Signal dom Bool :=
  (fun x y => !(x || y)) <$> a <*> b
def bAndN {dom : DomainConfig} (a b : Signal dom Bool) : Signal dom Bool :=
  (fun x y => !(x && !y)) <$> a <*> b

def mNegAdd_8_3 {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun c => -(c + 3#8)) <$> s

/-! Non-standard instances: must be refused. -/
def alwaysBEq7 : BEq (BitVec 7) := ⟨fun _ _ => true⟩
def badNeg8 : Neg (BitVec 8) := ⟨fun x => x⟩
def badCompl8 : Complement (BitVec 8) := ⟨fun x => x⟩

def badNe {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (Bool) :=
  (fun c => @bne (BitVec 7) alwaysBEq7 c 0#7) <$> s
def badNotEq {dom : DomainConfig} (s : Signal dom (BitVec 7)) : Signal dom (Bool) :=
  (fun c => !(@BEq.beq (BitVec 7) alwaysBEq7 c 0#7)) <$> s
def badNegAdd {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun c => @Neg.neg (BitVec 8) badNeg8 (c + 3#8)) <$> s
def badComplAdd {dom : DomainConfig} (s : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun c => @Complement.complement (BitVec 8) badCompl8 (c + 3#8)) <$> s

/-- `true` iff synthesis of `declName` is refused with the non-standard-instance message. -/
def refused (declName : Name) : MetaM Bool := do
  try
    let _ ← Sparkle.Compiler.Elab.synthesizeCombinational declName
    IO.println s!"[map-not-eq] {declName}: ACCEPTED (expected refusal)"
    return false
  catch e =>
    let msg ← e.toMessageData.toString
    if (msg.splitOn "non-standard instance").length > 1 then
      IO.println s!"[map-not-eq] {declName}: refused ok"
      return true
    IO.println s!"[map-not-eq] {declName}: refused for the wrong reason: {msg}"
    return false

private def portWidth : HWType → Nat
  | .bitVector w => w
  | .bit => 1
  | _ => 0

/-- Evaluate the module's single non-clock output with data inputs bound
    positionally to `vals`. -/
def irEval (m : Sparkle.IR.AST.Module) (vals : List Nat) : MetaM Nat := do
  let ins := m.inputs.filter (fun p => p.name != "clk" && p.name != "rst")
  unless ins.length == vals.length do
    throwError "expected {vals.length} data inputs, got {ins.map (·.name)}"
  let ports := m.inputs ++ m.outputs ++ m.wires
  let we : WEnv := fun n => match ports.find? (·.name == n) with
    | some p => portWidth p.ty | none => 0
  let bound := ins.map (·.name) |>.zip vals
  let env0 : Env := fun n => match bound.find? (·.1 == n) with | some (_, v) => v | none => 0
  let some env := evalAssigns we (fun _ _ => 0) m.body env0
    | throwError "IR evaluator: body outside the evaluable fragment"
  let [o] := m.outputs | throwError "expected 1 output"
  return env o.name

def testVals (n k : Nat) : List Nat :=
  let top := 2 ^ n - 1
  [0, 1, 2, 3, k, k + 1, k + 2, 64, 127, 128, 129, 255, 256, 1000, 1001, top, top - 1].map (· % 2 ^ n)

def chkGen {r : Type} (declName : Name) (vals : List Nat) (src : Nat → r) (toNat : r → Nat) :
    MetaM Bool := do
  let some (m, _) ← (try some <$> Sparkle.Compiler.Elab.synthesizeCombinational declName
      catch e => do
        IO.println s!"[map-not-eq] {declName}: synthesis FAILED: {← e.toMessageData.toString}"
        pure none)
    | return false
  let mut ok := true
  for v in vals do
    let s := toNat (src v)
    let i ← irEval m [v]
    if s != i then
      IO.println s!"[map-not-eq] {declName}: input={v} source={s} ir={i} MISMATCH"
      ok := false
      break
  if ok then IO.println s!"[map-not-eq] {declName}: ok ({vals.length} inputs)"
  return ok

def chk (declName : Name) {n : Nat} (f : Signal defaultDomain (BitVec n) → Signal defaultDomain Bool)
    (_n k : Nat) : MetaM Bool :=
  chkGen declName (testVals n k) (fun v => (f ⟨fun _ => BitVec.ofNat n v⟩).atTime 0)
    (fun b => if b then 1 else 0)

def chkBV (declName : Name) {n : Nat} (f : Signal defaultDomain (BitVec n) → Signal defaultDomain (BitVec n))
    (_n k : Nat) : MetaM Bool :=
  chkGen declName (testVals n k) (fun v => (f ⟨fun _ => BitVec.ofNat n v⟩).atTime 0)
    (fun b => b.toNat)

def chkB1 (declName : Name) (f : Signal defaultDomain Bool → Signal defaultDomain Bool) : MetaM Bool :=
  chkGen declName [0, 1] (fun v => (f ⟨fun _ => v == 1⟩).atTime 0) (fun b => if b then 1 else 0)

/-- Two Bool inputs, all four combinations. -/
def chkB2 (declName : Name)
    (f : Signal defaultDomain Bool → Signal defaultDomain Bool → Signal defaultDomain Bool) :
    MetaM Bool := do
  let some (m, _) ← (try some <$> Sparkle.Compiler.Elab.synthesizeCombinational declName
      catch e => do
        IO.println s!"[map-not-eq] {declName}: synthesis FAILED: {← e.toMessageData.toString}"
        pure none)
    | return false
  let mut ok := true
  for (a, b) in [(0, 0), (0, 1), (1, 0), (1, 1)] do
    let s := if (f ⟨fun _ => a == 1⟩ ⟨fun _ => b == 1⟩).atTime 0 then 1 else 0
    let i ← irEval m [a, b]
    if s != i then
      IO.println s!"[map-not-eq] {declName}: a={a} b={b} source={s} ir={i} MISMATCH"
      ok := false
  if ok then IO.println s!"[map-not-eq] {declName}: ok (4 inputs)"
  return ok

run_meta do
  let mut bad : List Name := []
  unless (← chk ``mNotEq_1_1 (mNotEq_1_1 (dom := defaultDomain)) 1 1) do bad := bad ++ [``mNotEq_1_1]
  unless (← chk ``mNotNe_1_1 (mNotNe_1_1 (dom := defaultDomain)) 1 1) do bad := bad ++ [``mNotNe_1_1]
  unless (← chk ``mNe_1_1 (mNe_1_1 (dom := defaultDomain)) 1 1) do bad := bad ++ [``mNe_1_1]
  unless (← chk ``mEq_1_1 (mEq_1_1 (dom := defaultDomain)) 1 1) do bad := bad ++ [``mEq_1_1]
  unless (← chk ``mNotNotEq_1_1 (mNotNotEq_1_1 (dom := defaultDomain)) 1 1) do bad := bad ++ [``mNotNotEq_1_1]
  unless (← chkBV ``mInv_1_1 (mInv_1_1 (dom := defaultDomain)) 1 1) do bad := bad ++ [``mInv_1_1]
  unless (← chkBV ``mInvAdd_1_1 (mInvAdd_1_1 (dom := defaultDomain)) 1 1) do bad := bad ++ [``mInvAdd_1_1]
  unless (← chk ``mNotEq_7_0 (mNotEq_7_0 (dom := defaultDomain)) 7 0) do bad := bad ++ [``mNotEq_7_0]
  unless (← chk ``mNotNe_7_0 (mNotNe_7_0 (dom := defaultDomain)) 7 0) do bad := bad ++ [``mNotNe_7_0]
  unless (← chk ``mNe_7_0 (mNe_7_0 (dom := defaultDomain)) 7 0) do bad := bad ++ [``mNe_7_0]
  unless (← chk ``mEq_7_0 (mEq_7_0 (dom := defaultDomain)) 7 0) do bad := bad ++ [``mEq_7_0]
  unless (← chk ``mNotNotEq_7_0 (mNotNotEq_7_0 (dom := defaultDomain)) 7 0) do bad := bad ++ [``mNotNotEq_7_0]
  unless (← chkBV ``mInv_7_0 (mInv_7_0 (dom := defaultDomain)) 7 0) do bad := bad ++ [``mInv_7_0]
  unless (← chkBV ``mInvAdd_7_0 (mInvAdd_7_0 (dom := defaultDomain)) 7 0) do bad := bad ++ [``mInvAdd_7_0]
  unless (← chk ``mNotEq_7_5 (mNotEq_7_5 (dom := defaultDomain)) 7 5) do bad := bad ++ [``mNotEq_7_5]
  unless (← chk ``mNotNe_7_5 (mNotNe_7_5 (dom := defaultDomain)) 7 5) do bad := bad ++ [``mNotNe_7_5]
  unless (← chk ``mNe_7_5 (mNe_7_5 (dom := defaultDomain)) 7 5) do bad := bad ++ [``mNe_7_5]
  unless (← chk ``mEq_7_5 (mEq_7_5 (dom := defaultDomain)) 7 5) do bad := bad ++ [``mEq_7_5]
  unless (← chk ``mNotNotEq_7_5 (mNotNotEq_7_5 (dom := defaultDomain)) 7 5) do bad := bad ++ [``mNotNotEq_7_5]
  unless (← chkBV ``mInv_7_5 (mInv_7_5 (dom := defaultDomain)) 7 5) do bad := bad ++ [``mInv_7_5]
  unless (← chkBV ``mInvAdd_7_5 (mInvAdd_7_5 (dom := defaultDomain)) 7 5) do bad := bad ++ [``mInvAdd_7_5]
  unless (← chk ``mNotEq_8_0 (mNotEq_8_0 (dom := defaultDomain)) 8 0) do bad := bad ++ [``mNotEq_8_0]
  unless (← chk ``mNotNe_8_0 (mNotNe_8_0 (dom := defaultDomain)) 8 0) do bad := bad ++ [``mNotNe_8_0]
  unless (← chk ``mNe_8_0 (mNe_8_0 (dom := defaultDomain)) 8 0) do bad := bad ++ [``mNe_8_0]
  unless (← chk ``mEq_8_0 (mEq_8_0 (dom := defaultDomain)) 8 0) do bad := bad ++ [``mEq_8_0]
  unless (← chk ``mNotNotEq_8_0 (mNotNotEq_8_0 (dom := defaultDomain)) 8 0) do bad := bad ++ [``mNotNotEq_8_0]
  unless (← chkBV ``mInv_8_0 (mInv_8_0 (dom := defaultDomain)) 8 0) do bad := bad ++ [``mInv_8_0]
  unless (← chkBV ``mInvAdd_8_0 (mInvAdd_8_0 (dom := defaultDomain)) 8 0) do bad := bad ++ [``mInvAdd_8_0]
  unless (← chk ``mNotEq_8_200 (mNotEq_8_200 (dom := defaultDomain)) 8 200) do bad := bad ++ [``mNotEq_8_200]
  unless (← chk ``mNotNe_8_200 (mNotNe_8_200 (dom := defaultDomain)) 8 200) do bad := bad ++ [``mNotNe_8_200]
  unless (← chk ``mNe_8_200 (mNe_8_200 (dom := defaultDomain)) 8 200) do bad := bad ++ [``mNe_8_200]
  unless (← chk ``mEq_8_200 (mEq_8_200 (dom := defaultDomain)) 8 200) do bad := bad ++ [``mEq_8_200]
  unless (← chk ``mNotNotEq_8_200 (mNotNotEq_8_200 (dom := defaultDomain)) 8 200) do bad := bad ++ [``mNotNotEq_8_200]
  unless (← chkBV ``mInv_8_200 (mInv_8_200 (dom := defaultDomain)) 8 200) do bad := bad ++ [``mInv_8_200]
  unless (← chkBV ``mInvAdd_8_200 (mInvAdd_8_200 (dom := defaultDomain)) 8 200) do bad := bad ++ [``mInvAdd_8_200]
  unless (← chk ``mNotEq_32_0 (mNotEq_32_0 (dom := defaultDomain)) 32 0) do bad := bad ++ [``mNotEq_32_0]
  unless (← chk ``mNotNe_32_0 (mNotNe_32_0 (dom := defaultDomain)) 32 0) do bad := bad ++ [``mNotNe_32_0]
  unless (← chk ``mNe_32_0 (mNe_32_0 (dom := defaultDomain)) 32 0) do bad := bad ++ [``mNe_32_0]
  unless (← chk ``mEq_32_0 (mEq_32_0 (dom := defaultDomain)) 32 0) do bad := bad ++ [``mEq_32_0]
  unless (← chk ``mNotNotEq_32_0 (mNotNotEq_32_0 (dom := defaultDomain)) 32 0) do bad := bad ++ [``mNotNotEq_32_0]
  unless (← chkBV ``mInv_32_0 (mInv_32_0 (dom := defaultDomain)) 32 0) do bad := bad ++ [``mInv_32_0]
  unless (← chkBV ``mInvAdd_32_0 (mInvAdd_32_0 (dom := defaultDomain)) 32 0) do bad := bad ++ [``mInvAdd_32_0]
  unless (← chk ``mNotEq_32_1000 (mNotEq_32_1000 (dom := defaultDomain)) 32 1000) do bad := bad ++ [``mNotEq_32_1000]
  unless (← chk ``mNotNe_32_1000 (mNotNe_32_1000 (dom := defaultDomain)) 32 1000) do bad := bad ++ [``mNotNe_32_1000]
  unless (← chk ``mNe_32_1000 (mNe_32_1000 (dom := defaultDomain)) 32 1000) do bad := bad ++ [``mNe_32_1000]
  unless (← chk ``mEq_32_1000 (mEq_32_1000 (dom := defaultDomain)) 32 1000) do bad := bad ++ [``mEq_32_1000]
  unless (← chk ``mNotNotEq_32_1000 (mNotNotEq_32_1000 (dom := defaultDomain)) 32 1000) do bad := bad ++ [``mNotNotEq_32_1000]
  unless (← chkBV ``mInv_32_1000 (mInv_32_1000 (dom := defaultDomain)) 32 1000) do bad := bad ++ [``mInv_32_1000]
  unless (← chkBV ``mInvAdd_32_1000 (mInvAdd_32_1000 (dom := defaultDomain)) 32 1000) do bad := bad ++ [``mInvAdd_32_1000]
  unless (← chkB1 ``bNot (bNot (dom := defaultDomain))) do bad := bad ++ [``bNot]
  unless (← chkB1 ``bNotNot (bNotNot (dom := defaultDomain))) do bad := bad ++ [``bNotNot]
  unless (← chkB1 ``bAndT (bAndT (dom := defaultDomain))) do bad := bad ++ [``bAndT]
  unless (← chkB2 ``bAnd (bAnd (dom := defaultDomain))) do bad := bad ++ [``bAnd]
  unless (← chkB2 ``bOr (bOr (dom := defaultDomain))) do bad := bad ++ [``bOr]
  unless (← chkB2 ``bAndN (bAndN (dom := defaultDomain))) do bad := bad ++ [``bAndN]
  unless (← chkBV ``mNegAdd_8_3 (mNegAdd_8_3 (dom := defaultDomain)) 8 3) do bad := bad ++ [``mNegAdd_8_3]
  for n in [``badNe, ``badNotEq, ``badNegAdd, ``badComplAdd] do
    unless (← refused n) do bad := bad ++ [n]
  unless bad.isEmpty do
    throwError "source/IR mismatch (or non-refusal) for {bad}"

end Sparkle.Tests.Compiler.MapNotEq

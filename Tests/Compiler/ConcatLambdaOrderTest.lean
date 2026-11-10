/-
  Concat lambda argument order: source semantics vs the synthesised IR.

  `(fun x y => y ++ x) <$> a <*> b` means `b ++ a`.  This test synthesises
  each variant through `synthesizeCombinational` (the function
  `#synthesizeVerilog` uses), evaluates the SOURCE at an asymmetric input
  (a = 1#8, b = 2#8) via `Signal.atTime`, evaluates the returned IR module at
  the same input with the IR evaluator (`Sparkle.IR.Semantics`), and requires
  equal values.  It does not use the U1 tools.

  The checks are `run_meta`, so a mismatch fails the build of this module.
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

namespace Sparkle.Tests.Compiler.ConcatLambdaOrder

set_option maxRecDepth 100000

def dcat8s {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 16) :=
  (fun x y => y ++ x) <$> a <*> b

def dcat8u {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 16) :=
  (fun x y => x ++ y) <$> a <*> b

def dsub8s {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun x y => y - x) <$> a <*> b

def dcatAB {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 16) :=
  a ++ b

def dcatBA {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 16) :=
  b ++ a

def dsubxx {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun x _y => x - x) <$> a <*> b
def dsuby1 {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun _x y => y - 1#8) <$> a <*> b
def dadd3 {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun x y => x + y + 1#8) <$> a <*> b
def dsub3 {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun x y => (x - y) - x) <$> a <*> b
def dproj {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun x _y => x) <$> a <*> b
def dshlyx {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun x y => y <<< x) <$> a <*> b
def dsubyy {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun _x y => 3#8 - y) <$> a <*> b
def dcatxx {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 16) :=
  (fun x _y => x ++ x) <$> a <*> b
def dnotsub {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun x y => ~~~(y - x)) <$> a <*> b
/-- Outside the supported fragment: must be refused, not miscompiled. -/
def dshlmix {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun x y => (x <<< y) + y) <$> a <*> b

def dsra {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun x y => BitVec.sshiftRight x y.toNat) <$> a <*> b
def dsraS {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  (fun x y => BitVec.sshiftRight y x.toNat) <$> a <*> b
/-- Seen in the IP tests: `d && !b0`; the head-operator shortcut used to emit `d & b0`. -/
def dandn {dom : DomainConfig} (a b : Signal dom Bool) : Signal dom Bool :=
  (fun d b0 => d && !b0) <$> a <*> b
def dnandn {dom : DomainConfig} (a b : Signal dom Bool) : Signal dom Bool :=
  (fun d b0 => !b0 && d) <$> a <*> b

/-- The synthesis must fail with the "Unsupported 2-argument lambda" error. -/
def checkRefused (declName : Name) : MetaM Bool := do
  try
    let _ ← Sparkle.Compiler.Elab.synthesizeCombinational declName
    IO.println s!"[concat-order] {declName}: compiled (expected refusal)"
    return false
  catch e =>
    let msg ← e.toMessageData.toString
    IO.println s!"[concat-order] {declName}: refused"
    return (msg.splitOn "Unsupported 2-argument lambda").length > 1

/-- Source value at time 0, a = 1#8, b = 2#8 (as `Nat`). -/
def srcVal {n : Nat} (f : Signal defaultDomain (BitVec 8) → Signal defaultDomain (BitVec 8) →
    Signal defaultDomain (BitVec n)) : Nat :=
  (f ⟨fun _ => 1#8⟩ ⟨fun _ => 2#8⟩).atTime 0 |>.toNat

private def portWidth : HWType → Nat
  | .bitVector w => w
  | .bit => 1
  | _ => 0

/-- Evaluate the module's single non-clock output at a = 1, b = 2, inputs
    bound positionally (first data input = a, second = b). -/
def irVal (m : Sparkle.IR.AST.Module) : MetaM Nat := do
  let ins := m.inputs.filter (fun p => p.name != "clk" && p.name != "rst")
  let [pa, pb] := ins | throwError "expected 2 data inputs, got {ins.map (·.name)}"
  let ports := m.inputs ++ m.outputs ++ m.wires
  let we : WEnv := fun n => match ports.find? (·.name == n) with
    | some p => portWidth p.ty | none => 0
  let env0 : Env := fun n => if n == pa.name then 1 else if n == pb.name then 2 else 0
  let some env := evalAssigns we (fun _ _ => 0) m.body env0
    | throwError "IR evaluator: body outside the evaluable fragment"
  let [o] := m.outputs | throwError "expected 1 output"
  return env o.name

/-- a = true, b = false. -/
def checkBool (declName : Name)
    (f : Signal defaultDomain Bool → Signal defaultDomain Bool → Signal defaultDomain Bool)
    (expected : Nat) : MetaM Bool := do
  let (m, _) ← Sparkle.Compiler.Elab.synthesizeCombinational declName
  let s := (if (f ⟨fun _ => true⟩ ⟨fun _ => false⟩).atTime 0 then 1 else 0 : Nat)
  let ins := m.inputs.filter (fun p => p.name != "clk" && p.name != "rst")
  let [pa, pb] := ins | throwError "expected 2 data inputs, got {ins.map (·.name)}"
  let ports := m.inputs ++ m.outputs ++ m.wires
  let we : WEnv := fun n => match ports.find? (·.name == n) with
    | some p => portWidth p.ty | none => 0
  let env0 : Env := fun n => if n == pa.name then 1 else 0
  let _ := pb
  let some env := evalAssigns we (fun _ _ => 0) m.body env0
    | throwError "IR evaluator: body outside the evaluable fragment"
  let [o] := m.outputs | throwError "expected 1 output"
  let i := env o.name
  IO.println s!"[concat-order] {declName}: source={s} ir={i} expected={expected}"
  unless s == expected do throwError "{declName}: source value {s} /= expected {expected}"
  return s == i

def check {n : Nat} (declName : Name)
    (f : Signal defaultDomain (BitVec 8) → Signal defaultDomain (BitVec 8) →
      Signal defaultDomain (BitVec n)) (expected : Nat) : MetaM Bool := do
  let (m, _) ← Sparkle.Compiler.Elab.synthesizeCombinational declName
  let s := srcVal f
  let i ← irVal m
  IO.println s!"[concat-order] {declName}: source={s} ir={i} expected={expected}"
  unless s == expected do throwError "{declName}: source value {s} /= expected {expected}"
  return s == i

-- a = 1, b = 2: a ++ b = 0x0102 = 258, b ++ a = 0x0201 = 513
run_meta do
  let mut bad : List Name := []
  -- b - a = 2 - 1 = 1 (a - b would be 255)
  unless (← check ``dsub8s (dsub8s (dom := defaultDomain)) 1) do bad := bad ++ [``dsub8s]
  unless (← check ``dcat8s (dcat8s (dom := defaultDomain)) 513) do bad := bad ++ [``dcat8s]
  unless (← check ``dcat8u (dcat8u (dom := defaultDomain)) 258) do bad := bad ++ [``dcat8u]
  unless (← check ``dcatAB (dcatAB (dom := defaultDomain)) 258) do bad := bad ++ [``dcatAB]
  unless (← check ``dcatBA (dcatBA (dom := defaultDomain)) 513) do bad := bad ++ [``dcatBA]
  -- Non-exact lambda bodies (a = 1, b = 2): lowered over both parameters.
  unless (← check ``dsubxx (dsubxx (dom := defaultDomain)) 0) do bad := bad ++ [``dsubxx]
  unless (← check ``dsuby1 (dsuby1 (dom := defaultDomain)) 1) do bad := bad ++ [``dsuby1]
  unless (← check ``dadd3 (dadd3 (dom := defaultDomain)) 4) do bad := bad ++ [``dadd3]
  unless (← check ``dsub3 (dsub3 (dom := defaultDomain)) 254) do bad := bad ++ [``dsub3]
  unless (← check ``dproj (dproj (dom := defaultDomain)) 1) do bad := bad ++ [``dproj]
  unless (← check ``dshlyx (dshlyx (dom := defaultDomain)) 4) do bad := bad ++ [``dshlyx]
  unless (← check ``dsubyy (dsubyy (dom := defaultDomain)) 1) do bad := bad ++ [``dsubyy]
  unless (← check ``dcatxx (dcatxx (dom := defaultDomain)) 257) do bad := bad ++ [``dcatxx]
  unless (← check ``dnotsub (dnotsub (dom := defaultDomain)) 254) do bad := bad ++ [``dnotsub]
  unless (← check ``dsra (dsra (dom := defaultDomain)) 0) do bad := bad ++ [``dsra]
  unless (← check ``dsraS (dsraS (dom := defaultDomain)) 1) do bad := bad ++ [``dsraS]
  unless (← checkBool ``dandn (dandn (dom := defaultDomain)) 1) do bad := bad ++ [``dandn]
  unless (← checkBool ``dnandn (dnandn (dom := defaultDomain)) 1) do bad := bad ++ [``dnandn]
  unless (← checkRefused ``dshlmix) do bad := bad ++ [``dshlmix]
  unless bad.isEmpty do
    throwError "source/IR mismatch for {bad}"

end Sparkle.Tests.Compiler.ConcatLambdaOrder

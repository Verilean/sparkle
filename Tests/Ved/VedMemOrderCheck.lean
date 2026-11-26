import Tools.VedMemEntry
import Tools.VedMemOrder

/-!
# Checks for the kernel-cheap order check (`Tools/VedMemOrder.lean`; sparkle-ved-memory-rest)

`OrderOkM'` replaces the kernel `decide` of `OrderOkM` (quadratic String / `Stmt` search; 23 GB on the SoC) by a
name table of Nat codes.  `OrderOkM'_sound : OrderOkM' m b = true → OrderOkM m b = true`.

* POSITIVE: a small module whose body is in the REVERSE of its order; both checks accept it; `OrderOkM'_sound`
  depends on the three standard axioms only.
* SIZE: a generated module (150 statements: registers, assigns, a sync memory; the body in a scrambled order) is accepted
  by `OrderOkM'` by `decide +kernel` (the old check needs minutes at this size).
* CONTROLS (each must be `false` for BOTH checks): a read before its write, a name driven twice, a body that is not
  a permutation of the module's, a read of an undriven name, an undriven output, a register output also driven.
-/

namespace Tests.Ved.VedMemOrderCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Reorder Tools.VedMem Tools.VedMemOrder

def mkP (n : String) (t : HWType) : Port := Port.mk n t

def sAdd (l a b : String) : Stmt := .assign l (.op .add [.ref a, .ref b])
def s1 : Stmt := sAdd "w1" "a" "r"
def s2 : Stmt := sAdd "w2" "w1" "a"
def s3 : Stmt := .register "r" "clk" ("rst", .synchronous) (.ref "w2") 0
def s4 : Stmt := .memory "mem" 4 8 "clk" (.ref "a") (.ref "w2") (.ref "a") (.ref "w1") "rd" false

def modOf (body : List Stmt) (outs : List String := ["w2"]) : Sparkle.IR.AST.Module :=
  { Module.empty "m" with
    inputs := [mkP "a" (HWType.bitVector 8), mkP "clk" HWType.bit, mkP "rst" HWType.bit],
    outputs := outs.map (mkP · (HWType.bitVector 8)), body := body }

def good : List Stmt := [s1, s2, s3, s4]

example : OrderOkM (modOf [s4, s3, s2, s1]) good = true := by decide +kernel
example : OrderOkM' (modOf [s4, s3, s2, s1]) good = true := by decide +kernel
example : OrderOkM (modOf [s4, s3, s2, s1]) good = true :=
  OrderOkM'_sound _ _ (by decide +kernel)

/-- info: OrderOkM'_sound: axioms within std3 -/
#guard_msgs in
run_cmd liftTermElabM do
  let axs ← collectAxioms ``OrderOkM'_sound
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless axs.all (std.contains ·) do throwError "axioms {axs}"
  logInfo m!"OrderOkM'_sound: axioms within std3"

/-! controls: both checks refuse -/

/-- a read before its write -/
example : OrderOkM (modOf [s4, s3, s2, s1]) [s2, s1, s3, s4] = false := by decide +kernel
example : OrderOkM' (modOf [s4, s3, s2, s1]) [s2, s1, s3, s4] = false := by decide +kernel

/-- a name driven twice -/
def dup : List Stmt := [s1, s2, sAdd "w1" "a" "a", s3, s4]
example : OrderOkM (modOf dup) dup = false := by decide +kernel
example : OrderOkM' (modOf dup) dup = false := by decide +kernel

/-- the body is not a permutation of the module's -/
example : OrderOkM (modOf [s4, s3, s2, s1]) [s1, s2, s3, sAdd "w9" "a" "a"] = false := by decide +kernel
example : OrderOkM' (modOf [s4, s3, s2, s1]) [s1, s2, s3, sAdd "w9" "a" "a"] = false := by decide +kernel

/-- a read of an undriven name -/
def undriven : List Stmt := [s1, sAdd "w2" "w1" "zz", s3, s4]
example : OrderOkM (modOf undriven) undriven = false := by decide +kernel
example : OrderOkM' (modOf undriven) undriven = false := by decide +kernel

/-- an undriven output -/
example : OrderOkM (modOf [s4, s3, s2, s1] ["nope"]) good = false := by decide +kernel
example : OrderOkM' (modOf [s4, s3, s2, s1] ["nope"]) good = false := by decide +kernel

/-- an assign drives a register's output (a state key) -/
def clash : List Stmt := [s1, s2, sAdd "r" "a" "a", s3, s4]
example : OrderOkM (modOf clash) clash = false := by decide +kernel
example : OrderOkM' (modOf clash) clash = false := by decide +kernel

/-! size: a generated module -/

def gN : Nat := 150
def gR : Nat := gN / 8
def gA : Nat := gN - gR
def gw (i : Nat) : String := s!"_gen_w_{i + 100}"
def gr (j : Nat) : String := s!"_tmp_r_{j + 500}"
def gAsg : List Stmt := (List.range gA).map fun i =>
  let a := if i == 0 then "in0" else gw (i - 1)
  let c := if i >= 3 then gw (i - 3) else "in1"
  .assign (gw i) (.op .mux [.ref a, .ref (gr (i % gR)), .ref c])
def gRegs : List Stmt := (List.range gR).map fun j =>
  .register (gr j) "clk" ("rst", .synchronous) (.ref (gw (gA - 1 - (j % gA)))) 0
def gMem : Stmt := .memory "mem0" 4 8 "clk" (.ref "in0") (.ref "in1") (.ref "in2") (.ref (gw (gA - 1))) "_gen_rd" false
def gB : List Stmt := gAsg ++ gRegs ++ [gMem]
def gM : Sparkle.IR.AST.Module :=
  { Module.empty "m" with
    inputs := [mkP "in0" (HWType.bitVector 8), mkP "in1" (HWType.bitVector 8), mkP "in2" HWType.bit,
      mkP "clk" HWType.bit, mkP "rst" HWType.bit],
    outputs := [mkP (gw (gA - 1)) (HWType.bitVector 8)], body := gRegs ++ [gMem] ++ gAsg.reverse }

-- closed terms (the strings are literals, as in the entry)
run_cmd liftTermElabM do
  Tools.VedU1Entry.addDefn `Tests.Ved.VedMemOrderCheck.bigM (Lean.mkConst ``Sparkle.IR.AST.Module) (toExpr gM)
  Tools.VedU1Entry.addDefn `Tests.Ved.VedMemOrderCheck.bigB
    (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Stmt)) (toExpr gB)

theorem big_ok : OrderOkM' bigM bigB = true := by decide +kernel

theorem big_sound : OrderOkM bigM bigB = true := OrderOkM'_sound _ _ big_ok

/-- the same body reversed (reads before their writes) is refused -/
example : OrderOkM' bigM bigB.reverse = false := by decide +kernel

end Tests.Ved.VedMemOrderCheck

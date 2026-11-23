import Tools.VedU1OrderFast
import Tools.VedU1Entry

/-!
# Checks for the leaf fast order check (`Tools/VedU1OrderFast.lean`; sparkle-ved-multiout unit 7)

`OrderOkLeafFast m b = true → OrderOk m b = true` (`orderOkLeafFast_sound`).

* POSITIVE: a small module accepted by `OrderOk` and `OrderOkLeafFast`; the soundness theorem is within std3.
* SIZE: generated leaf bodies (registers + assigns, the module's body in another order than the arrangement) of 100 and
  560 statements; the fast check is accepted by `decide +kernel` and `orderOkLeafFast_sound` gives `OrderOk`
  (the old check is also run at 100; at 560 it is the 23 GB kill the fast check replaces).
* CONTROLS (the fast check is `false`, as is `OrderOk`): a read before a write, a duplicate register, an output not
  driven, a self-read, a read of an undriven name, a body that is not a permutation, a memory statement (leaf scope),
  an assign that drives an input.
-/

namespace Tests.Ved.U1OrderFastCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Reorder Tools.VedU1Contract Tools.VedU1OrderFast

def mkP (n : String) (t : HWType) : Port := Port.mk n t

def sAdd (l a b : String) : Stmt := .assign l (.op .add [.ref a, .ref b])
def s1 : Stmt := sAdd "w1" "a" "r"
def s2 : Stmt := sAdd "w2" "w1" "a"
def s3 : Stmt := .register "r" "clk" ("rst", .synchronous) (.ref "w2") 0

def modOf (body : List Stmt) (outs : List String := ["w2"]) : Sparkle.IR.AST.Module :=
  { Module.empty "m" with
    inputs := [mkP "a" (HWType.bitVector 8), mkP "clk" HWType.bit, mkP "rst" HWType.bit],
    outputs := outs.map (mkP · (HWType.bitVector 8)), body := body }

def good : List Stmt := [s1, s2, s3]

example : OrderOk (modOf [s3, s2, s1]) good = true := by decide +kernel
example : OrderOkLeafFast (modOf [s3, s2, s1]) good = true := by decide +kernel
example : OrderOk (modOf [s3, s2, s1]) good = true := orderOkLeafFast_sound (by decide +kernel)

/-- info: orderOkLeafFast_sound: axioms within std3 -/
#guard_msgs in
run_cmd liftTermElabM do
  let axs ← collectAxioms ``orderOkLeafFast_sound
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless axs.all (std.contains ·) do throwError "axioms {axs}"
  logInfo m!"orderOkLeafFast_sound: axioms within std3"

/-! controls: both checks refuse -/

/-- a read before its write -/
example : OrderOk (modOf [s3, s2, s1]) [s2, s1, s3] = false := by decide +kernel
example : OrderOkLeafFast (modOf [s3, s2, s1]) [s2, s1, s3] = false := by decide +kernel

/-- a duplicate register -/
def dupR : List Stmt := [s1, s2, s3, .register "r" "clk" ("rst", .synchronous) (.ref "w1") 0]
example : OrderOk (modOf dupR) dupR = false := by decide +kernel
example : OrderOkLeafFast (modOf dupR) dupR = false := by decide +kernel

/-- a name driven twice by assigns -/
def dupW : List Stmt := [s1, s2, sAdd "w1" "a" "a", s3]
example : OrderOk (modOf dupW) dupW = false := by decide +kernel
example : OrderOkLeafFast (modOf dupW) dupW = false := by decide +kernel

/-- an output that is not driven -/
example : OrderOk (modOf [s3, s2, s1] ["nope"]) good = false := by decide +kernel
example : OrderOkLeafFast (modOf [s3, s2, s1] ["nope"]) good = false := by decide +kernel

/-- a self-read -/
def selfR : List Stmt := [s1, sAdd "w2" "w2" "a", s3]
example : OrderOk (modOf selfR) selfR = false := by decide +kernel
example : OrderOkLeafFast (modOf selfR) selfR = false := by decide +kernel

/-- a read of an undriven name -/
def undriven : List Stmt := [s1, sAdd "w2" "w1" "zz", s3]
example : OrderOk (modOf undriven) undriven = false := by decide +kernel
example : OrderOkLeafFast (modOf undriven) undriven = false := by decide +kernel

/-- the arrangement is not a permutation of the module's body -/
example : OrderOk (modOf [s3, s2, s1]) [s1, s2, s3, sAdd "w9" "a" "a"] = false := by decide +kernel
example : OrderOkLeafFast (modOf [s3, s2, s1]) [s1, s2, s3, sAdd "w9" "a" "a"] = false := by decide +kernel

/-- an assign drives a module input -/
def drvIn : List Stmt := [s1, s2, sAdd "a" "w1" "w1", s3]
example : OrderOk (modOf drvIn) drvIn = false := by decide +kernel
example : OrderOkLeafFast (modOf drvIn) drvIn = false := by decide +kernel

/-- a memory statement is outside the leaf scope: the fast check refuses (a combinational read: well-ordered for `OrderOk`) -/
def withMem : List Stmt := [s1, s2, s3, .memory "mem" 4 8 "clk" (.ref "a") (.ref "w2") (.ref "a") (.ref "w1") "rd" true]
example : OrderOkLeafFast (modOf withMem) withMem = false := by decide +kernel

/-! size: generated leaf bodies (registers and assigns; the module body is the reversed assigns after the registers) -/

def gw (i : Nat) : String := s!"_gen_w_{i + 100}"
def gr (j : Nat) : String := s!"_tmp_r_{j + 500}"
def gAsg (gA gR : Nat) : List Stmt := (List.range gA).map fun i =>
  let a := if i == 0 then "in0" else gw (i - 1)
  let c := if i >= 3 then gw (i - 3) else "in1"
  .assign (gw i) (.op .mux [.ref a, .ref (gr (i % gR)), .ref c])
def gRegs (gA gR : Nat) : List Stmt := (List.range gR).map fun j =>
  .register (gr j) "clk" ("rst", .synchronous) (.ref (gw (gA - 1 - (j % gA)))) 0
/-- `n` statements: `n / 8` registers, the rest assigns -/
def gB (n : Nat) : List Stmt := gAsg (n - n / 8) (n / 8) ++ gRegs (n - n / 8) (n / 8)
def gM (n : Nat) : Sparkle.IR.AST.Module :=
  { Module.empty "m" with
    inputs := [mkP "in0" (HWType.bitVector 8), mkP "in1" (HWType.bitVector 8), mkP "clk" HWType.bit,
      mkP "rst" HWType.bit],
    outputs := [mkP (gw (n - n / 8 - 1)) (HWType.bitVector 8)],
    body := gRegs (n - n / 8) (n / 8) ++ (gAsg (n - n / 8) (n / 8)).reverse }

-- closed terms (the strings are literals, as in the entry)
run_cmd liftTermElabM do
  for n in [100, 560] do
    Tools.VedU1Entry.addDefn (`Tests.Ved.U1OrderFastCheck ++ Name.mkSimple s!"M{n}")
      (Lean.mkConst ``Sparkle.IR.AST.Module) (toExpr (gM n))
    Tools.VedU1Entry.addDefn (`Tests.Ved.U1OrderFastCheck ++ Name.mkSimple s!"B{n}")
      (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Stmt)) (toExpr (gB n))

theorem ok100_old : OrderOk M100 B100 = true := by decide +kernel
theorem ok100 : OrderOk M100 B100 = true := orderOkLeafFast_sound (by decide +kernel)
theorem ok560 : OrderOk M560 B560 = true := orderOkLeafFast_sound (by decide +kernel)

/-- the same body reversed (reads before their writes) is refused -/
example : OrderOkLeafFast M560 B560.reverse = false := by decide +kernel

end Tests.Ved.U1OrderFastCheck

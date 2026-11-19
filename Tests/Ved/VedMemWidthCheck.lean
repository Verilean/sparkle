import Tools.VedMemEntry
import Tools.VedMemWidth

/-!
# Checks for the kernel-cheap width check (`Tools/VedMemWidth.lean`; sparkle-ved-memory-rest)

`WidthOk'` replaces the kernel `decide` of `WidthStmt` (wire-name `Nodup` and "every register has a wire" are String-quadratic;
killed at 12 GB on 1000 wires) by a wire table of Nat codes.  `WidthStmt_of_ok : WidthOk' c m = true → WidthStmt c m`.

* POSITIVE: a small contract and module; both `decide (WidthStmt c m)` and `WidthOk'` accept; `WidthStmt_of_ok` depends on
  the three standard axioms only.
* SIZE: a generated module of 400 wires and 50 registers is accepted by `WidthOk'` by `decide +kernel`.
* CONTROLS (each must be refused by BOTH the old decision and `WidthOk'`): a duplicate wire name, a register without a wire,
  a data input declared with the wrong width, a data input without a wire.
-/

namespace Tests.Ved.VedMemWidthCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Tools.VedU1Contract Tools.VedMemWidth

def mkP (n : String) (t : HWType) : Port := Port.mk n t

def tbl : DeclTable := DeclTable.mk ["x"] [PTy.bv 8] (OTy.leaf (PTy.bv 8))

def cOf (ws : List Port) : Contract :=
  Contract.mk "m" (some ("clk", "rst")) tbl ["a"] ["y"] ws [("r", 0)]

def body : List Stmt :=
  [.assign "y" (.op .add [.ref "a", .ref "r"]),
   .register "r" "clk" ("rst", .synchronous) (.ref "y") 0]

def modOf (ws : List Port) : Sparkle.IR.AST.Module :=
  { Module.empty "m" with
    inputs := [mkP "a" (HWType.bitVector 8), mkP "clk" HWType.bit, mkP "rst" HWType.bit],
    outputs := [mkP "y" (HWType.bitVector 8)], wires := ws, body := body }

def goodW : List Port := [mkP "a" (HWType.bitVector 8), mkP "y" (HWType.bitVector 8), mkP "r" (HWType.bitVector 8)]

example : WidthStmt (cOf goodW) (modOf goodW) := by decide +kernel
example : WidthOk' (cOf goodW) (modOf goodW) = true := by decide +kernel
example : WidthStmt (cOf goodW) (modOf goodW) := WidthStmt_of_ok _ _ (by decide +kernel)
example : WidthStmt (cOf goodW) (modOf goodW) := WidthStmt_of_parts _ _ (by decide +kernel) (by decide +kernel)

/-- info: WidthStmt_of_ok: axioms within std3 -/
#guard_msgs in
run_cmd liftTermElabM do
  let axs ← collectAxioms ``WidthStmt_of_ok
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless axs.all (std.contains ·) do throwError "axioms {axs}"
  logInfo m!"WidthStmt_of_ok: axioms within std3"

/-! controls: both refuse -/

/-- a duplicate wire name -/
def dupW : List Port := goodW ++ [mkP "y" (HWType.bitVector 8)]
example : decide (WidthStmt (cOf dupW) (modOf dupW)) = false := by decide +kernel
example : WidthOk' (cOf dupW) (modOf dupW) = false := by decide +kernel

/-- a register without a wire -/
def noRegW : List Port := [mkP "a" (HWType.bitVector 8), mkP "y" (HWType.bitVector 8)]
example : decide (WidthStmt (cOf noRegW) (modOf noRegW)) = false := by decide +kernel
example : WidthOk' (cOf noRegW) (modOf noRegW) = false := by decide +kernel

/-- a data input declared with the wrong width -/
def badWidthW : List Port := [mkP "a" (HWType.bitVector 4), mkP "y" (HWType.bitVector 8), mkP "r" (HWType.bitVector 8)]
example : decide (WidthStmt (cOf badWidthW) (modOf badWidthW)) = false := by decide +kernel
example : WidthOk' (cOf badWidthW) (modOf badWidthW) = false := by decide +kernel

/-- a data input without a wire -/
def noInW : List Port := [mkP "y" (HWType.bitVector 8), mkP "r" (HWType.bitVector 8)]
example : decide (WidthStmt (cOf noInW) (modOf noInW)) = false := by decide +kernel
example : WidthOk' (cOf noInW) (modOf noInW) = false := by decide +kernel

/-- a register whose wire is not scalar -/
def arrW : List Port := [mkP "a" (HWType.bitVector 8), mkP "y" (HWType.bitVector 8), mkP "r" (HWType.bitVector 0)]
example : decide (WidthStmt (cOf arrW) (modOf arrW)) = false := by decide +kernel
example : WidthOk' (cOf arrW) (modOf arrW) = false := by decide +kernel

/-! size: a generated module -/

def gA : Nat := 350
def gR : Nat := 50
def gw (i : Nat) : String := s!"_gen_w_{i + 100}"
def gr (j : Nat) : String := s!"_tmp_r_{j + 500}"
def gWires : List Port :=
  mkP "a" (HWType.bitVector 8) :: mkP "y" (HWType.bitVector 8) ::
    ((List.range gA).map (fun i => mkP (gw i) (HWType.bitVector 8)) ++
     (List.range gR).map (fun j => mkP (gr j) (HWType.bitVector 8)))
def gBody : List Stmt :=
  (List.range gR).map (fun j => Stmt.register (gr j) "clk" ("rst", .synchronous) (.ref "y") 0) ++
  (List.range gA).map (fun i => Stmt.assign (gw i) (.ref "a"))
def gM : Sparkle.IR.AST.Module := { modOf gWires with body := gBody }
def gC : Contract :=
  Contract.mk "m" (some ("clk", "rst")) tbl ["a"] ["y"] gWires ((List.range gR).map (fun j => (gr j, (0 : Int))))

deriving instance Lean.ToExpr for Contract

run_cmd liftTermElabM do
  Tools.VedU1Entry.addDefn `Tests.Ved.VedMemWidthCheck.bigM (Lean.mkConst ``Sparkle.IR.AST.Module) (toExpr gM)
  Tools.VedU1Entry.addDefn `Tests.Ved.VedMemWidthCheck.bigC (Lean.mkConst ``Tools.VedU1Contract.Contract) (toExpr gC)

theorem big_ok : WidthOk' bigC bigM = true := by decide +kernel
theorem big_sound : WidthStmt bigC bigM := WidthStmt_of_ok _ _ big_ok

end Tests.Ved.VedMemWidthCheck

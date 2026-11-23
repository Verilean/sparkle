import Tools.VedU2HierRecKid

/-!
# Checks for the recursive statement `U2HRStmtR` (CANDIDATE; Tools/VedU2HierRec*.lean)

Concrete designs, NOT rows of the 327 inventory and NOT produced by the generator (there is none yet
for this statement): hand-written IR modules, evaluated with `decide`.

* `leafAcc` (register `r' = r + x`, `out = r`) <- `midAcc` (register `r' = r + t`, instantiates
  `leafAcc` on `x`, `t` = its output, `out = r`) <- `topAcc` (same, instantiates `midAcc`): depth 2;
  `top2` instantiates `mid2` (= `midAcc` around `midAcc`) : depth 3, with the SAME definitions.
* shape (`HierShapeR`), clock/reset, admissible arrangement, the run `runHSR` and the per-path state
  history (the state at `["m0", "l0"]` is the grandchild's own register).
* controls: state collapsed to one slot per level (wrong instance path), a same-NAME but different
  module (the lookup and the run change), a cyclic design (fuel exhaustion = `none`), a missing
  output connection, a register-free non-leaf module (shape refusal), a duplicate module name.
* the local lemmas on the toy: sub-design, fuel, the standalone run of the mid equals the parent's
  slice, the initial state at a path.
Axioms of the main lemmas are printed.
-/

namespace Tests.Ved.U2HierRecCheck

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tools.VedU2HierRec

def bv8 : HWType := .bitVector 8

def leafAcc : Module :=
  { name := "leafAcc"
    inputs := [⟨"x", bv8⟩, ⟨"clk", .bit⟩, ⟨"rst", .bit⟩]
    outputs := [⟨"out", bv8⟩]
    wires := [⟨"x", bv8⟩, ⟨"r", bv8⟩, ⟨"nxt", bv8⟩, ⟨"out", bv8⟩]
    body := [ .assign "nxt" (.op .add [.ref "r", .ref "x"]),
              .register "r" "clk" ("rst", .synchronous) (.ref "nxt") 0,
              .assign "out" (.ref "r") ] }

/-- A register module that instantiates `child` (instance `iname`) on its data input. -/
def wrapAcc (nm child iname : String) : Module :=
  { name := nm
    inputs := [⟨"x", bv8⟩, ⟨"clk", .bit⟩, ⟨"rst", .bit⟩]
    outputs := [⟨"out", bv8⟩]
    wires := [⟨"x", bv8⟩, ⟨"r", bv8⟩, ⟨"t", bv8⟩, ⟨"nxt", bv8⟩, ⟨"out", bv8⟩]
    body := [ .inst child iname [("x", .ref "x"), ("clk", .ref "clk"), ("rst", .ref "rst"),
                                 ("out", .ref "t")],
              .assign "nxt" (.op .add [.ref "r", .ref "t"]),
              .register "r" "clk" ("rst", .synchronous) (.ref "nxt") 0,
              .assign "out" (.ref "r") ] }

def midAcc : Module := wrapAcc "midAcc" "leafAcc" "l0"
def topAcc : Module := wrapAcc "topAcc" "midAcc" "m0"
def mid2 : Module := wrapAcc "mid2" "midAcc" "n0"
def top2 : Module := wrapAcc "top2" "mid2" "p0"

/-- depth 2: the parent's real design (flat list: the mid and the grandchild). -/
def dsn : Design := { topModule := "topAcc", modules := [midAcc, leafAcc] }
/-- the mid's own sub-design (what the mid's stored theorem is stated on). -/
def dsnMid : Design := { topModule := "midAcc", modules := [leafAcc] }
/-- depth 3 with the same definitions. -/
def dsn3 : Design := { topModule := "top2", modules := [mid2, midAcc, leafAcc] }

def arrId : Module → List Stmt := fun c => c.body

/-- x = 1,2,3,4,5; clk, rst = 0. -/
def inpS (t : Nat) (n : String) : Nat := if n = "x" then [1, 2, 3, 4, 5].getD t 0 else 0

def outs (es : Option (List Env)) : Option (List Nat) := es.map (·.map fun e => e "out")

/-! ## depth 2: shape, clock/reset, arrangement -/

example : HierShapeR dsn topAcc = true := by decide
example : HierShapeR dsnMid midAcc = true := by decide
example : clkRstOk dsn topAcc = true := by decide
example : designClkRst dsn topAcc = some ("clk", "rst") := by decide
example : designClkRst dsnMid midAcc = some ("clk", "rst") := by decide
example : AdmArrR dsn topAcc arrId := by
  refine ⟨List.Perm.refl _, by decide, ?_⟩
  intro c hc
  have : c = midAcc ∨ c = leafAcc := by simpa [dsn] using hc
  rcases this with rfl | rfl
  · exact ⟨List.Perm.refl _, fun h => absurd h (by decide), fun _ => by decide⟩
  · exact ⟨List.Perm.refl _, fun _ => woCheck_sound _ _ (by decide), fun h => absurd h (by decide)⟩
example : OrderHS dsn topAcc := ⟨topAcc.body, by decide⟩
example : OrderHS dsn midAcc := ⟨midAcc.body, by decide⟩
example : OrderStmt leafAcc := ⟨leafAcc.body, by decide⟩
example : OrderModsR dsn := by
  intro c hc
  have : c = midAcc ∨ c = leafAcc := by simpa [dsn] using hc
  rcases this with rfl | rfl
  · exact ⟨fun h => absurd h (by decide), fun _ => ⟨midAcc.body, by decide⟩⟩
  · exact ⟨fun _ => ⟨leafAcc.body, by decide⟩, fun h => absurd h (by decide)⟩

/-! ## depth 2: the run, and the state at every instance path -/

-- out = r of the top: r_top' = r_top + r_mid, r_mid' = r_mid + r_leaf, r_leaf' = r_leaf + x
example : outs (runHSR dsn arrId topAcc (seedFwd topAcc 5 inpS) 5 (st0HR dsn topAcc)) =
    some [0, 0, 0, 1, 5] := by decide

def stateTrace (d : Design) (m : Module) (paths : List Path) (K : Nat) : Option (List (List Nat)) :=
  (runHSRTrace d arrId m (seedFwd m K inpS) K (st0HR d m)).map
    (·.2.map fun s => paths.map fun p => s p "r")

-- (top, mid, grandchild) register values before each cycle: three SEPARATE slices
example : stateTrace dsn topAcc [[], ["m0"], ["m0", "l0"]] 5 =
    some [[0, 0, 0], [0, 0, 1], [0, 1, 3], [1, 4, 6], [5, 10, 10]] := by decide

/-! ## depth 3: the same definitions -/

example : HierShapeR dsn3 top2 = true := by decide
example : clkRstOk dsn3 top2 = true := by decide
example : stateTrace dsn3 top2 [[], ["p0"], ["p0", "n0"], ["p0", "n0", "l0"]] 5 =
    some [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 3], [0, 1, 4, 6], [1, 5, 10, 10]] := by decide
example : outs (runHSR dsn3 arrId top2 (seedFwd top2 5 inpS) 5 (st0HR dsn3 top2)) =
    some [0, 0, 0, 0, 1] := by decide

/-! ## coincidence with `U2HRStmtK` on an all-leaf design (instances of the theorem) -/

def dsnLeaf : Design := { topModule := "topAcc", modules := [leafAcc] }
def topLeaf : Module := wrapAcc "topAcc" "leafAcc" "l0"

example : allLeafB dsnLeaf = true := by decide
example : HierShapeR dsnLeaf topLeaf = HierShapeK dsnLeaf topLeaf := by decide
example : HierShapeK dsnLeaf topLeaf = true := by decide
example : outs (runHSR dsnLeaf arrId topLeaf (seedFwd topLeaf 5 inpS) 5 (st0HR dsnLeaf topLeaf)) =
    outs (runHS dsnLeaf arrId topLeaf (seedFwd topLeaf 5 inpS) 5 (st0H dsnLeaf topLeaf)) := by decide
-- depth 2 is NOT an all-leaf design: the K statement does not apply, the R statement does
example : allLeafB dsn = false := by decide
example : HierShapeK dsn topAcc = false := by decide

/-! ## local lemmas on the toy -/

-- L3: the mid's sub-design is part of the parent's real design, strictly smaller; the child's fuel fits
example : SubDesign dsnMid dsn :=
  subDesign_of_subset (by decide) (by intro x hx; simp [dsnMid, dsn] at hx ⊢; exact Or.inr hx)
example : fuelR dsnMid ≤ dsn.modules.length + 1 := by decide
example : findMod dsn "midAcc" = some midAcc := by decide
example : findMod dsnMid "leafAcc" = findMod dsn "leafAcc" := by decide

-- L2: the initial state at the path `["m0", p]` of the parent is the mid's own initial state at `p`
example : st0HR dsn topAcc ["m0", "l0"] "r" = st0HR dsnMid midAcc ["l0"] "r" := by decide
example : st0HR dsn topAcc ["m0"] "r" = st0HR dsnMid midAcc [] "r" := by decide

-- L5: the stand-alone run of the mid (in its own sub-design, its own theorem's run) is the run of the
-- instance inside the parent, on the slice, at the parent's fuel (the stream is the mid's input)
def midIn (t : Nat) (n : String) : Nat := inpS t n
example : outs (runIn dsn arrId midAcc (seedFwd midAcc 5 midIn) 5 (st0HR dsnMid midAcc)) =
    outs (runHSR dsnMid arrId midAcc (seedFwd midAcc 5 midIn) 5 (st0HR dsnMid midAcc)) := by decide
example : outs (runHSR dsnMid arrId midAcc (seedFwd midAcc 5 midIn) 5 (st0HR dsnMid midAcc)) =
    some [0, 0, 1, 4, 10] := by decide

/-! ## controls -/

/-- MUTANT (wrong instance path): the grandchild's register is stored at the mid's path (one slot per
level), so the state slice of the grandchild is the mid's. -/
def applyHCollapsed (st : HSt) (ups : Ups) : HSt :=
  applyH st (ups.map fun u => (u.1.take 1, u.2))

def runCollapsed (d : Design) (arr : Module → List Stmt) (m : Module)
    (seed : Nat → (String → Nat) → Env) : Nat → HSt → Option (List Env)
  | 0, _ => some []
  | k + 1, st => do
    let (envF, ups) ← stepHSR d arr m st (seed k (restrictTo (regOuts (arr m)) (st [])))
    let rest ← runCollapsed d arr m seed k (applyHCollapsed st ups)
    some (envF :: rest)

example : outs (runCollapsed dsn arrId topAcc (seedFwd topAcc 5 inpS) 5 (st0HR dsn topAcc)) ≠
    outs (runHSR dsn arrId topAcc (seedFwd topAcc 5 inpS) 5 (st0HR dsn topAcc)) := by decide

/-- A same-NAME but different module: the mid's register accumulates twice. -/
def midAccB : Module :=
  { midAcc with body := midAcc.body.map fun s => match s with
      | .assign "nxt" _ => .assign "nxt" (.op .add [.ref "r", .op .add [.ref "t", .ref "t"]])
      | s => s }
def dsnB : Design := { topModule := "topAcc", modules := [midAccB, leafAcc] }

example : midAccB.name = midAcc.name := by decide
example : midAccB ≠ midAcc := by decide
example : findMod dsnB "midAcc" = some midAccB := by decide
example : findMod dsnB "midAcc" ≠ some midAcc := by decide
-- the semantics follows the MODULE, not the name; a theorem about `midAcc` is not a theorem about it
example : outs (runHSR dsnB arrId topAcc (seedFwd topAcc 5 inpS) 5 (st0HR dsnB topAcc)) ≠
    outs (runHSR dsn arrId topAcc (seedFwd topAcc 5 inpS) 5 (st0HR dsn topAcc)) := by decide
example : HierShapeR dsnB topAcc = true := by decide

/-- A cyclic design: the mid instantiates itself.  Fuel exhaustion is `none`: the statement is false. -/
def cycMid : Module := wrapAcc "midAcc" "midAcc" "l0"
def dsnCyc : Design := { topModule := "topAcc", modules := [cycMid] }
example : runHSR dsnCyc arrId topAcc (seedFwd topAcc 1 inpS) 1 (st0HR dsnCyc topAcc) = none := by decide

/-- A missing output connection (the mid's `out` is not connected): refused by the shape. -/
def topNoOut : Module :=
  { topAcc with body := topAcc.body.map fun s => match s with
      | .inst mn i cs => .inst mn i (cs.filter fun q => q.1 != "out")
      | s => s }
example : HierShapeR dsn topNoOut = false := by decide

/-- A non-leaf module without a register of its own: refused (documented shape limitation). -/
def midNoReg : Module :=
  { midAcc with body := midAcc.body.filter fun s => match s with
      | .register .. => false
      | _ => true }
def dsnNoReg : Design := { topModule := "topAcc", modules := [midNoReg, leafAcc] }
example : HierShapeR dsnNoReg topAcc = false := by decide

/-- A duplicate module name in the design: refused. -/
def dsnDup : Design := { topModule := "topAcc", modules := [midAcc, midAcc, leafAcc] }
example : HierShapeR dsnDup topAcc = false := by decide

/-- A module of the design that the top does not reach: refused. -/
def dsnExtra : Design := { topModule := "topAcc", modules := [midAcc, leafAcc, mid2] }
example : HierShapeR dsnExtra topAcc = false := by decide

/-! ## axioms -/

#print axioms U2HRStmtR_iff_K
#print axioms combR_sub_fuel
#print axioms upsR_sub_fuel
#print axioms stepR_sub_fuel
#print axioms applyH_slice
#print axioms upsR_slice
#print axioms st0Path_agree
#print axioms fuel_le_of_sub
#print axioms WOH_agree
#print axioms runIn_prefix
#print axioms runIn_congr_seed
#print axioms runHSR_runIn
#print axioms runIn_proj
#print axioms kid_seq_R

end Tests.Ved.U2HierRecCheck

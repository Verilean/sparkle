import Tools.VedU2HierProj

/-!
# Checks for the stateful hierarchical semantics `runHS` (H2 unit 2)

Tiny concrete H2a design (NOT part of the 327 inventory rows): a register-free parent `top` with
TWO instances of the same register child `acc` (`r' = r + x`, `out = r`), asymmetric output
`out = p - q`.  Evaluated with `decide`: the two instances keep SEPARATE state.  Controls: a
shared-state mutant of the update gives different values; a mis-wired design gives different
values; clk/rst judgements refuse a constant reset, a data input as the second instance's reset,
and a clock taken from a data input.  Axioms of the main lemmas are printed.
-/

namespace Tests.Ved.U2HierSemCheck

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier

def bv8 : HWType := .bitVector 8

/-- The register child: `r' = r + x`, `out = r`. -/
def accMod : Module :=
  { name := "acc"
    inputs := [⟨"x", bv8⟩, ⟨"clk", .bit⟩, ⟨"rst", .bit⟩]
    outputs := [⟨"out", bv8⟩]
    wires := [⟨"x", bv8⟩, ⟨"r", bv8⟩, ⟨"nxt", bv8⟩, ⟨"out", bv8⟩]
    body := [ .assign "nxt" (.op .add [.ref "r", .ref "x"]),
              .register "r" "clk" ("rst", .synchronous) (.ref "nxt") 0,
              .assign "out" (.ref "r") ] }

def topWith (c0 c1 r0 r1 : Expr) (o0 o1 : String) : Module :=
  { name := "top"
    inputs := [⟨"a", bv8⟩, ⟨"b", bv8⟩, ⟨"clk", .bit⟩, ⟨"rst", .bit⟩]
    outputs := [⟨"out", bv8⟩]
    wires := [⟨"a", bv8⟩, ⟨"b", bv8⟩, ⟨"p", bv8⟩, ⟨"q", bv8⟩, ⟨"out", bv8⟩,
              ⟨"clk", .bit⟩, ⟨"rst", .bit⟩]
    body := [ .inst "acc" "i0" [("x", .ref "a"), ("clk", c0), ("rst", r0), ("out", .ref o0)],
              .inst "acc" "i1" [("x", .ref "b"), ("clk", c1), ("rst", r1), ("out", .ref o1)],
              .assign "out" (.op .sub [.ref "p", .ref "q"]) ] }

/-- The parent: register-free, `out = p - q`. -/
def topMod : Module := topWith (.ref "clk") (.ref "clk") (.ref "rst") (.ref "rst") "p" "q"

def dsn : Design := { topModule := "top", modules := [accMod] }

def arrId : Module → List Stmt := fun c => c.body

/-- Inputs: a = 1,2,3; b = 10,20,30; clk, rst = 0. -/
def inpS (t : Nat) (n : String) : Nat :=
  if n = "a" then [1, 2, 3, 4].getD t 0 else if n = "b" then [10, 20, 30, 40].getD t 0 else 0

def obs3 (es : Option (List Env)) : Option (List (Nat × Nat × Nat)) :=
  es.map (·.map fun e => (e "out", e "p", e "q"))

/-! ## shape / order -/

example : HierShapeS dsn topMod = true := by decide
example : designClkRst dsn topMod = some ("clk", "rst") := by decide
example : AdmArr dsn topMod arrId := by
  refine ⟨List.Perm.refl _, by decide, ?_⟩
  intro c hc
  have : c = accMod := by simpa [dsn] using hc
  subst this
  exact ⟨List.Perm.refl _, woCheck_sound _ _ (by decide)⟩

/-! ## two instances keep separate state (cycles 0..2) -/

-- out = p - q (mod 256); p = prefix sums of a (0,1,3), q = prefix sums of b (0,10,30)
example : obs3 (runHS dsn arrId topMod (seedFwd topMod 3 inpS) 3 (st0H dsn topMod)) =
    some [(0, 0, 0), (247, 1, 10), (229, 3, 30)] := by decide

/-- the pre-update state history: `[i0]` and `[i1]` hold DIFFERENT register values; the root has
no register. -/
def stateTrace : Option (List (Nat × Nat)) :=
  (runHSTrace dsn arrId topMod (seedFwd topMod 3 inpS) 3 (st0H dsn topMod)).map
    (·.2.map fun s => (s ["i0"] "r", s ["i1"] "r"))

example : stateTrace = some [(0, 0), (1, 10), (3, 30)] := by decide

/-! ## controls -/

/-- MUTANT: a module-wide state.  All updates land in every path (the first entry for a register
name wins), so both instances read the same `r`. -/
def applyHShared (st : HSt) (ups : Ups) : HSt := fun p n => applyNexts (st p) (ups.flatMap (·.2)) n

def runHSShared (d : Design) (arr : Module → List Stmt) (m : Module)
    (seed : Nat → (String → Nat) → Env) : Nat → HSt → Option (List Env)
  | 0, _ => some []
  | k + 1, st => do
    let (envF, ups) ← stepHS d arr m st (seed k (restrictTo (regOuts (arr m)) (st [])))
    let rest ← runHSShared d arr m seed k (applyHShared st ups)
    some (envF :: rest)

-- shared state: both instances show the same `r`, so `out = p - q = 0` and p = q
example : obs3 (runHSShared dsn arrId topMod (seedFwd topMod 3 inpS) 3 (st0H dsn topMod)) =
    some [(0, 0, 0), (0, 1, 1), (0, 3, 3)] := by decide

example : obs3 (runHSShared dsn arrId topMod (seedFwd topMod 3 inpS) 3 (st0H dsn topMod)) ≠
    obs3 (runHS dsn arrId topMod (seedFwd topMod 3 inpS) 3 (st0H dsn topMod)) := by decide

/-- mis-wired: the two instance outputs `p`/`q` swapped. -/
def topSwap : Module := topWith (.ref "clk") (.ref "clk") (.ref "rst") (.ref "rst") "q" "p"

example : obs3 (runHS dsn arrId topSwap (seedFwd topSwap 3 inpS) 3 (st0H dsn topSwap)) =
    some [(0, 0, 0), (9, 10, 1), (27, 30, 3)] := by decide

example : obs3 (runHS dsn arrId topSwap (seedFwd topSwap 3 inpS) 3 (st0H dsn topSwap)) ≠
    obs3 (runHS dsn arrId topMod (seedFwd topMod 3 inpS) 3 (st0H dsn topMod)) := by decide

/-- clk/rst judgement controls (every failure is `none`): the reset of an instance is a constant,
the second instance's reset is a data input (the two instances do not share ONE pair), the clock
of an instance is a data input. -/
def topRstConst : Module := topWith (.ref "clk") (.ref "clk") (.const 0 1) (.ref "rst") "p" "q"
def topRstData : Module := topWith (.ref "clk") (.ref "clk") (.ref "rst") (.ref "a") "p" "q"
def topClkData : Module := topWith (.ref "a") (.ref "clk") (.ref "rst") (.ref "rst") "p" "q"

example : clkRstOk dsn topMod = true := by decide
example : clkRstOk dsn topRstConst = false := by decide
example : clkRstOk dsn topRstData = false := by decide
example : clkRstOk dsn topClkData = false := by decide
example : (runHS dsn arrId topRstConst (seedFwd topRstConst 3 inpS) 3 (st0H dsn topRstConst)) = none := by
  decide
example : (runHS dsn arrId topRstData (seedFwd topRstData 3 inpS) 3 (st0H dsn topRstData)) = none := by
  decide

/-- BOTH instances reset by the data input `a` (a single pair `(clk, a)`): `clkRstOk` alone accepts
a pair of distinct inputs, so the STATEMENT side must tie the pair to the contract's `clkRst`; the
design pair here is `(clk, a)`, a data input of the contract, which `CorrStmt`'s injectivity of
`inNames ++ outNames ++ clkRstNames` refuses (the contract names `_gen_a` for the data input and
a clock/reset pair `(clk, a)` would repeat a port name). -/
def topBothA : Module := topWith (.ref "clk") (.ref "clk") (.ref "a") (.ref "a") "p" "q"

example : clkRstOk dsn topBothA = true := by decide
example : designClkRst dsn topBothA = some ("clk", "a") := by decide

/-! ## leaf correspondence on a concrete module -/

def dsnLeaf : Design := { topModule := "acc", modules := [] }

def inpL (t : Nat) (n : String) : Nat := if n = "x" then [5, 6, 7].getD t 0 else 0

example : (runHS dsnLeaf arrId accMod (seedFwd accMod 3 inpL) 3 (st0H dsnLeaf accMod)).map
      (·.map fun e => e "out") = some [0, 5, 11] := by decide

example : (runModule (declWidth accMod) accMod.body (seedFwd accMod 3 inpL) 3 (st0Of accMod)
      (fun _ _ => 0)).map (·.map fun e => e "out") = some [0, 5, 11] := by decide

/-! ## the lemmas, instantiated on the concrete design -/

theorem dsn_shape : HierShapeS dsn topMod = true := by decide

theorem dsn_adm : AdmArr dsn topMod arrId := by
  refine ⟨List.Perm.refl _, by decide, ?_⟩
  intro c hc
  have : c = accMod := by simpa [dsn] using hc
  subst this
  exact ⟨List.Perm.refl _, woCheck_sound _ _ (by decide)⟩

theorem dsn_supp : ExprsSupp topMod (arrId topMod) := by
  intro s hs
  simp only [arrId, topMod, topWith] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> decide

theorem dsn_child : ∀ c ∈ dsn.modules, ChildSucc c (arrId c) := by
  intro c hc
  have : c = accMod := by simpa [dsn] using hc
  subst this
  exact childSucc_of_step _ _ (fun _ => 0) (by decide)

/-- existence of the hierarchical run (no success assumption: the shape, support and the child's
cycle supply it) -/
theorem dsn_run_exists (K : Nat) (inp : Nat → String → Nat) :
    ∃ envs sts, runHSTrace dsn arrId topMod (seedFwd topMod K inp) K (st0H dsn topMod) =
      some (envs, sts) :=
  runHS_exists dsn arrId topMod dsn_shape dsn_adm dsn_supp dsn_child _ K _

/-- the projection, for instance `i0`, on every run -/
theorem dsn_proj (K : Nat) (inp : Nat → String → Nat) :
    ∃ envs sts, runHSTrace dsn arrId topMod (seedFwd topMod K inp) K (st0H dsn topMod) =
      some (envs, sts) ∧
    ∃ c cenvs, findMod dsn "acc" = some c ∧
      runModule (declWidth c) (arrId c)
        (seedFwd c K (insCOf (declWidth topMod) [("x", .ref "a"), ("clk", .ref "clk"), ("rst", .ref "rst"),
          ("out", .ref "p")] envs)) K (st0Of c) (fun _ _ => 0) = some cenvs := by
  obtain ⟨envs, sts, h⟩ := dsn_run_exists K inp
  refine ⟨envs, sts, h, ?_⟩
  obtain ⟨c, cenvs, cstates, hf, _, hm, _⟩ := runHS_proj dsn arrId topMod dsn_shape dsn_adm inp K envs sts h
    "acc" "i0" [("x", .ref "a"), ("clk", .ref "clk"), ("rst", .ref "rst"), ("out", .ref "p")]
    (by simp [topMod, topWith])
  exact ⟨c, cenvs, hf, hm⟩

/-! ## axioms -/

#print axioms Tools.VedU2Hier.runHS_stateless
#print axioms Tools.VedU2Hier.stepHS_stateless
#print axioms Tools.VedU2Hier.runHS_leaf
#print axioms Tools.VedU2Hier.stepHS_leaf
#print axioms Tools.VedU2Hier.st0H_own
#print axioms Tools.VedU2Hier.st0H_slice
#print axioms Tools.VedU2Hier.runHS_proj_aux
#print axioms Tools.VedU2Hier.runHS_proj
#print axioms Tools.VedU2Hier.stepHS_succ
#print axioms Tools.VedU2Hier.runHS_exists
#print axioms Tools.VedU2Hier.childSucc_of_outputsOn
#print axioms Tools.VedU2Hier.instPair_tie
#print axioms Tools.VedU2Hier.instEvalS_laws
#print axioms Tests.Ved.U2HierSemCheck.dsn_proj

end Tests.Ved.U2HierSemCheck

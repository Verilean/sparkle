/-
  Searching for the RTL shape of a fixed-point expression.

  ## What this is for

  A control law can be written many ways that agree over ℝ but compile to
  different hardware.  Folding two gains saves a multiplier; distributing one
  costs an extra floor.  Choosing by hand means guessing, and the guesses are
  wrong in both directions — see the `0.5 + 0.25` case below.

  This enumerates the ℝ-equivalent rewritings of an expression, prices each
  one, and reports which are FREE (bit-identical in Q15.16) and which cost
  error.  The proofs behind the pricing live in
  `proofs/SparkleProofs/Control/AlgebraicRewrite.lean`:

      uA_eq_uB / div_reassoc  — the ℝ identity is what makes a candidate legal
      add_reassoc_exact       — reassociation is free
      fold_exact              — folding is free IFF one gain is integral
      Vbound_mono             — a non-free rewrite's cost enters the ISS bound
                                monotonically, so "still within budget?" is a
                                numeric check, not a new proof

  ## Deliberately conservative

  The search rejects a candidate unless it agrees over ℝ on every sample, and
  it reports the *measured* fixed-point gap over the sample set.  A measured
  gap is a lower bound on the true worst case; the proved bound from floor
  counting is an upper bound, and §12.2.4 records that the two differ (1 vs
  6 lsb on the PID example).  So: use this to FIND candidates, then discharge
  the chosen one against the proved bound.  It is a search tool, not an
  oracle — the same role `Retype/Falsify.lean` plays for the ℝ proofs.
-/

import IP.Control.FixedPoint

namespace Sparkle.IP.Control.ShapeSearch

open Sparkle.IP.Control.FixedPoint

/-! ### Expressions -/

/-- A fixed-point expression tree over Q15.16 numerators. -/
inductive Expr where
  | const : Int → Expr
  | var   : String → Expr
  | add   : Expr → Expr → Expr
  | sub   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr
deriving Repr, BEq, Inhabited

namespace Expr

/-- Q15.16 scale. -/
def scale : Int := 65536

/-- Evaluate in fixed point — every `mul` floors, exactly as `mulQ` does. -/
def evalQ (e : Expr) (env : List (String × Int)) : Int :=
  match e with
  | .const n => n
  | .var x   => (env.find? (·.1 == x)).map (·.2) |>.getD 0
  | .add a b => evalQ a env + evalQ b env
  | .sub a b => evalQ a env - evalQ b env
  | .mul a b => (evalQ a env * evalQ b env) / scale

/-- Evaluate over ℚ (as a scaled integer with extra headroom) — the ℝ
    reference, with no intermediate flooring.  Uses a 2^32 sub-scale so that
    products of two Q15.16 values keep their fractional part. -/
def evalR (e : Expr) (env : List (String × Int)) : Int :=
  let sub : Int := 65536
  let rec go (e : Expr) : Int :=       -- value × (scale · sub)
    match e with
    | .const n => n * sub
    | .var x   => ((env.find? (·.1 == x)).map (·.2) |>.getD 0) * sub
    | .add a b => go a + go b
    | .sub a b => go a - go b
    | .mul a b => go a * go b / (scale * sub)
  go e

/-- Is `n` a power of two?  A gain that is a power of two lowers to a shift,
    so it costs no multiplier. -/
def isPow2 (n : Int) : Bool :=
  n > 0 && (n.toNat &&& (n.toNat - 1)) == 0

/-- Multiplier count: the cost model.  A product with a power-of-two constant
    is a shift and is free; everything else needs a DSP/LUT multiplier. -/
def mulCost : Expr → Nat
  | .const _ | .var _ => 0
  | .add a b | .sub a b => mulCost a + mulCost b
  | .mul a b =>
    match a, b with
    | .const c, r => if isPow2 c then mulCost r else 1 + mulCost r
    | l, .const c => if isPow2 c then mulCost l else 1 + mulCost l
    | l, r => 1 + mulCost l + mulCost r

/-- Render, with constants shown as their real value. -/
def render : Expr → String
  | .const n => s!"{n}/2^16"
  | .var x   => x
  | .add a b => s!"({render a} + {render b})"
  | .sub a b => s!"({render a} - {render b})"
  | .mul a b => s!"({render a} * {render b})"

end Expr

/-! ### Rewrite rules

Each returns the rewritings available AT THE ROOT; `rewrites` walks subterms. -/

open Expr in
/-- `k*(a±b) → k*a ± k*b`.  Crosses a floor — NOT free. -/
def rDistribute : Expr → List Expr
  | .mul k (.add a b) => [.add (.mul k a) (.mul k b)]
  | .mul k (.sub a b) => [.sub (.mul k a) (.mul k b)]
  | _ => []

open Expr in
/-- `k*a ± k*b → k*(a±b)`.  The inverse; also crosses a floor. -/
def rFactor : Expr → List Expr
  | .add (.mul k a) (.mul k' b) => if k == k' then [.mul k (.add a b)] else []
  | .sub (.mul k a) (.mul k' b) => if k == k' then [.mul k (.sub a b)] else []
  | _ => []

open Expr in
/-- `c₁*x ± c₂*x → (c₁±c₂)*x`.  Saves a multiplier.  Free iff one of the
    constants is integral (`fold_exact`); the search measures which. -/
def rFold : Expr → List Expr
  | .add (.mul (.const c1) x) (.mul (.const c2) y) =>
    if x == y then [.mul (.const (c1 + c2)) x] else []
  | .sub (.mul (.const c1) x) (.mul (.const c2) y) =>
    if x == y then [.mul (.const (c1 - c2)) x] else []
  | _ => []

open Expr in
/-- Reassociate additions.  Free (`add_reassoc_exact`). -/
def rAssoc : Expr → List Expr
  | .add (.add a b) c => [.add a (.add b c)]
  | .add a (.add b c) => [.add (.add a b) c]
  | _ => []

open Expr in
/-- Commute additions.  Free. -/
def rComm : Expr → List Expr
  | .add a b => [.add b a]
  | _ => []

/-- All one-step rewrites, at the root or inside a subterm. -/
partial def rewrites (e : Expr) : List Expr :=
  let atRoot := rDistribute e ++ rFactor e ++ rFold e ++ rAssoc e ++ rComm e
  let inSub :=
    match e with
    | .add a b => (rewrites a).map (Expr.add · b) ++ (rewrites b).map (Expr.add a ·)
    | .sub a b => (rewrites a).map (Expr.sub · b) ++ (rewrites b).map (Expr.sub a ·)
    | .mul a b => (rewrites a).map (Expr.mul · b) ++ (rewrites b).map (Expr.mul a ·)
    | _ => []
  atRoot ++ inSub

/-! ### The search -/

/-- A priced candidate. -/
structure Candidate where
  expr    : Expr
  muls    : Nat
  /-- Measured worst |candidate − original| over the sample set, in lsb.
      Zero means bit-identical on every sample — see the header on why that
      is evidence, not proof. -/
  gapLsb  : Int
deriving Repr

/-- Enumerate rewritings up to `depth`, keep those that agree with `start`
    over ℝ on every sample, and price them.

    Sorted by (multipliers, gap): the head is the cheapest shape, and among
    equally cheap ones the most faithful. -/
def search (start : Expr) (envs : List (List (String × Int)))
    (depth : Nat := 3) : List Candidate := Id.run do
  let mut seen : List Expr := [start]
  let mut frontier : List Expr := [start]
  for _ in [0:depth] do
    let mut next : List Expr := []
    for e in frontier do
      for e2 in rewrites e do
        unless seen.contains e2 do
          seen := e2 :: seen
          next := e2 :: next
    frontier := next
  let refR := envs.map (Expr.evalR start ·)
  let refQ := envs.map (Expr.evalQ start ·)
  let mut out : List Candidate := []
  for e in seen do
    -- ℝ-equivalence is the admission filter
    let sameR := (envs.zip refR).all fun (en, r) => Expr.evalR e en == r
    if sameR then
      let gap := (envs.zip refQ).foldl
        (fun acc (en, q) => max acc (Expr.evalQ e en - q).natAbs) 0
      out := { expr := e, muls := Expr.mulCost e, gapLsb := (gap : Int) } :: out
  return out.toArray.qsort
    (fun a b => if a.muls != b.muls then a.muls < b.muls else a.gapLsb < b.gapLsb)
    |>.toList

/-- Report the search as text. -/
def report (cs : List Candidate) (n : Nat := 6) : String :=
  String.intercalate "\n" <|
    (cs.take n).map fun c =>
      s!"  muls={c.muls} gap={c.gapLsb} lsb  {Expr.render c.expr}"

end Sparkle.IP.Control.ShapeSearch

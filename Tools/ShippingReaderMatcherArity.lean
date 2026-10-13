import Lean

/-! # The machine reader's `prodMatcherArity?`, total (reader generalisation, second unit)

WRITTEN, NOT BUILT (par/h-1). NOT wired into the reader: the compiler is not
edited and does not import this file. Record: `docs/parallel/H-reader-units.md`.

## The function

`Sparkle.Compiler.MachRawSurface.prodMatcherArity? env n` (a `partial def`,
MachRawSurface.lean 26–51) reads the arity of a matcher that destructures one
right-nested pair off the matcher's value:

    match env.find? n with
    | some (.defnInfo d) =>
      match d.value with
      | .lam _ _ (.lam _ _ (.lam _ _ body _) _) _ => go body 1 [] 0
      | _ => none
    | _ => none
    where go : Lean.Expr → Nat → List Nat → Nat → Option Nat
      | e, subj, vars, depth =>
        match e.getAppFn, e.getAppArgs with
        | .const ``Prod.casesOn _, #[_, _, _, .bvar t, .lam _ _ (.lam _ _ rest _) _] =>
          if t != subj then none else
          go rest 0 ((vars.map (· + 2)) ++ [1]) (depth + 2)
        | .bvar hIdx, args =>
          if hIdx != depth then none else
          let expected := vars ++ [subj]
          if args.toList == expected.map Lean.Expr.bvar then some args.size else none
        | _, _ => none

The only recursion is `go`, on `rest`: a proper subterm of `e`, but taken
out of the ARRAY `e.getAppArgs` by a pattern, which the equation compiler
does not see as a subterm. Hence `partial`.

## The decision about `==`

The last test of `go` is `==` on `List Lean.Expr`, i.e. `List.beq` over
`BEq Lean.Expr`, i.e. `Lean.Expr.eqv` — `@[extern "lean_expr_eqv"] opaque`.
Nothing about its value can be proved in the kernel.

Here the test is a PARAMETER `eqv : Expr → Expr → Bool` of the definition,
and the definition is split so that the parameter enters in ONE place:

* `walkT` — the walk down the `Prod.casesOn` chain. Structural recursion, no
  fuel, and NO opaque function: it returns the data of the leaf (`LeafData`:
  the head index, the argument list, and the walk's `subj`, `vars`, `depth`)
  or refuses.
* `leafT eqv` — the leaf's decision, not recursive: the head index is the
  depth and the arguments are `eqv`-equal to the expected bound variables.
* `goT eqv e subj vars depth = (walkT e subj vars depth).bind (leafD eqv)`.

`prodMatcherArityT = prodMatcherArityG exprEqv` (`exprEqv a b = (a == b)`,
the compiler's test: nothing about the extern is assumed) and
`prodMatcherArityS = prodMatcherArityG bvarEqv` (`bvarEqv`: both are the same
bound variable — a structural test). By READING the runtime's meaning of
`Expr.eqv` (equality up to binder names; the second argument here is always a
`.bvar`), the two tests agree on these inputs; that is NOT provable (it is a
statement about the extern) and is not used: `prodMatcherArityS` is a second
candidate that is only measured, and nothing is narrowed (nothing is wired).

## What is proved (this file)

* the walk's equations: `walkT_sol` (for EVERY `e`: one unfolding of the
  recursion, `step leafW walkT`), `walkT_bvar`, `walkT_shape`;
* SUCCESSFUL INPUTS: `walkT_chain` — on every canonical pair-matcher body
  (`chainE`: any number of `Prod.casesOn` levels with any decorations, then
  the alternative applied to the components) the walk returns leaf data whose
  head index is the depth and whose arguments are exactly the expected bound
  variables. NO premise, and `eqv` does not occur;
* `goT_chain` / `valueArityG_matcherE` / `prodMatcherArityG_canon` — with
  the ONE premise `∀ i, eqv (.bvar i) (.bvar i) = true` the result is
  `some (levels + 1)`; `prodMatcherArityS_canon` — for the structural test
  the premise is a theorem, so that statement has none;
* `goT_congr`, `prodMatcherArityG_congr` — two tests that agree on
  `eqv a (.bvar i)` give the same function. So
  `prodMatcherArityT = prodMatcherArityS` under the single premise
  `∀ a i, (a == .bvar i) = bvarEqv a (.bvar i)` about the extern.

`Tools/ShippingReaderMatcherArityUnique.lean` (riskier proofs, separate so
that a failure there does not block this file): the result characterisation
(`goT_some_iff`, `leafT_some_iff`), the recursion equation of `go` in
structural form (`GoEq`), that `goT eqv` satisfies it and that it has exactly
one solution, and the two provable links to the compiler's text.

## The boundary

1. `prodMatcherArity?.go` is `partial`: an opaque constant. No kernel
   equation with it exists; none is assumed.
2. The compiler's text selects by `e.getAppFn` / `e.getAppArgs` and an ARRAY
   pattern; this file by `headT` / `argsT` and a constructor pattern. Both
   sides are total, so the agreement is provable in principle, but
   `Lean.Expr.getAppArgs` is defined through `getAppArgsAux`, a `private`
   definition of a `module` (it cannot be named from here): NOT proved,
   MEASURED on every node the shadow visits (`PIECES`).
3. `Expr.eqv` (see above): a parameter.

Well-typedness premises: none. No expression is type-checked or reduced;
`go` only inspects constructors. -/
namespace Tools.ShippingReaderMatcherArity
open Lean

/-! ## The spine of an application, structurally -/

/-- `e.getAppFn`, by the same text. -/
def headT : Expr → Expr
  | .app f _ => headT f
  | e => e

/-- The arguments of an application in front of `acc`. -/
def argsAcc : Expr → List Expr → List Expr
  | .app f a, acc => argsAcc f (a :: acc)
  | _, acc => acc

/-- `e.getAppArgs.toList`, structurally. -/
def argsT (e : Expr) : List Expr := argsAcc e []

/-- `f a₁ … aₙ`. -/
def mkL : Expr → List Expr → Expr
  | f, [] => f
  | f, a :: as => mkL (.app f a) as

theorem headT_mkL : ∀ (as : List Expr) (f : Expr), headT (mkL f as) = headT f
  | [], _ => rfl
  | a :: as, f => headT_mkL as (.app f a)

theorem argsAcc_mkL : ∀ (as : List Expr) (f : Expr) (acc : List Expr),
    argsAcc (mkL f as) acc = argsAcc f (as ++ acc)
  | [], _, _ => rfl
  | a :: as, f, acc => argsAcc_mkL as (.app f a) acc

theorem argsT_mkL_bvar (d : Nat) (as : List Expr) : argsT (mkL (.bvar d) as) = as :=
  (argsAcc_mkL as (.bvar d) []).trans (List.append_nil as)

/-! ## The test, a parameter -/

/-- `List.beq` over the test `eqv` (the compiler's `==` on `List Expr` is
this at `eqv := Expr.eqv`, `listEqv_exprEqv`). -/
def listEqv (eqv : Expr → Expr → Bool) : List Expr → List Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => eqv a b && listEqv eqv as bs
  | _, _ => false

/-- The compiler's test: `==` on `Lean.Expr` (`Expr.eqv`, an extern). -/
def exprEqv (a b : Expr) : Bool := a == b

/-- A structural test: the same bound variable. -/
def bvarEqv : Expr → Expr → Bool
  | .bvar i, .bvar j => decide (i = j)
  | _, _ => false

theorem bvarEqv_refl (i : Nat) : bvarEqv (.bvar i) (.bvar i) = true :=
  decide_eq_true rfl

theorem and_congr2 {a a' b b' : Bool} (h1 : a = a') (h2 : b = b') :
    (a && b) = (a' && b') := by
  subst h1
  subst h2
  rfl

/-- A test that accepts a bound variable against itself accepts a list of
bound variables against itself. -/
theorem listEqv_refl (eqv : Expr → Expr → Bool) (hrefl : ∀ i, eqv (.bvar i) (.bvar i) = true) :
    ∀ ns : List Nat, listEqv eqv (ns.map Expr.bvar) (ns.map Expr.bvar) = true
  | [] => rfl
  | n :: ns =>
    (and_congr2 (hrefl n) (listEqv_refl eqv hrefl ns) :
      (eqv (.bvar n) (.bvar n) && listEqv eqv (ns.map Expr.bvar) (ns.map Expr.bvar)) =
        (true && true))

/-- Two tests that agree against bound variables agree on the leaf's lists. -/
theorem listEqv_congr (eqv eqv' : Expr → Expr → Bool)
    (h : ∀ a i, eqv a (.bvar i) = eqv' a (.bvar i)) :
    ∀ (l : List Expr) (ns : List Nat),
      listEqv eqv l (ns.map Expr.bvar) = listEqv eqv' l (ns.map Expr.bvar)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, n :: ns => and_congr2 (h a n) (listEqv_congr eqv eqv' h as ns)

/-! ## The leaf -/

/-- What the walk hands to the leaf's decision. -/
structure LeafData where
  hIdx : Nat
  args : List Expr
  subj : Nat
  vars : List Nat
  depth : Nat

/-- The compiler's second arm (the head is a bound variable): the head is
the alternative `h` (index `depth`) and its arguments are the components met
so far and the last subject. -/
def leafT (eqv : Expr → Expr → Bool) (hIdx : Nat) (args : List Expr) (subj : Nat)
    (vars : List Nat) (depth : Nat) : Option Nat :=
  if hIdx != depth then none else
  if listEqv eqv args ((vars ++ [subj]).map Expr.bvar) then some args.length else none

/-- `leafT` on the walk's data. -/
def leafD (eqv : Expr → Expr → Bool) (d : LeafData) : Option Nat :=
  leafT eqv d.hIdx d.args d.subj d.vars d.depth

/-- The walk's leaf: the data, no decision. -/
def leafW (hIdx : Nat) (args : List Expr) (subj : Nat) (vars : List Nat) (depth : Nat) :
    Option LeafData :=
  some ⟨hIdx, args, subj, vars, depth⟩

/-! ## One unfolding of the recursion, as a function of the recursive call -/

/-- The compiler's first arm (`Prod.casesOn` applied to five arguments, the
fourth a bound variable, the fifth two lambdas), the recursive call `r`. -/
def casesArm {ρ : Type} (r : Expr → Nat → List Nat → Nat → Option ρ) (e : Expr) (subj : Nat)
    (vars : List Nat) (depth : Nat) : Option ρ :=
  match e with
  | .app (.app (.app (.app (.app (.const c _) _) _) _) (.bvar t))
      (.lam _ _ (.lam _ _ rest _) _) =>
    if c = ``Prod.casesOn then
      if t != subj then none else r rest 0 ((vars.map (· + 2)) ++ [1]) (depth + 2)
    else none
  | _ => none

/-- The arms, selected by the head `hd` of the term. -/
def stepH {ρ : Type} (leaf : Nat → List Expr → Nat → List Nat → Nat → Option ρ) (hd : Expr)
    (r : Expr → Nat → List Nat → Nat → Option ρ) (e : Expr) (subj : Nat) (vars : List Nat)
    (depth : Nat) : Option ρ :=
  match hd with
  | .bvar hIdx => leaf hIdx (argsT e) subj vars depth
  | _ => casesArm r e subj vars depth

/-- One unfolding of `go`: its text with the recursive call `r` and the
leaf's decision `leaf` as parameters. -/
def step {ρ : Type} (leaf : Nat → List Expr → Nat → List Nat → Nat → Option ρ)
    (r : Expr → Nat → List Nat → Nat → Option ρ) (e : Expr) (subj : Nat) (vars : List Nat)
    (depth : Nat) : Option ρ :=
  stepH leaf (headT e) r e subj vars depth

/-- The shape of the first arm, as a term. -/
def shapeE (c : Name) (us : List Level) (a1 a2 a3 : Expr) (t : Nat) (n1 : Name) (t1 : Expr)
    (bi1 : BinderInfo) (n2 : Name) (t2 : Expr) (bi2 : BinderInfo) (rest : Expr) : Expr :=
  .app (.app (.app (.app (.app (.const c us) a1) a2) a3) (.bvar t))
    (.lam n1 t1 (.lam n2 t2 rest bi2) bi1)

theorem casesArm_shape {ρ : Type} (r : Expr → Nat → List Nat → Nat → Option ρ) (c : Name)
    (us : List Level) (a1 a2 a3 : Expr) (t : Nat) (n1 : Name) (t1 : Expr) (bi1 : BinderInfo)
    (n2 : Name) (t2 : Expr) (bi2 : BinderInfo) (rest : Expr) (subj : Nat) (vars : List Nat)
    (depth : Nat) :
    casesArm r (shapeE c us a1 a2 a3 t n1 t1 bi1 n2 t2 bi2 rest) subj vars depth =
      if c = ``Prod.casesOn then
        if t != subj then none else r rest 0 ((vars.map (· + 2)) ++ [1]) (depth + 2)
      else none := rfl

theorem step_shape {ρ : Type} (leaf : Nat → List Expr → Nat → List Nat → Nat → Option ρ)
    (r : Expr → Nat → List Nat → Nat → Option ρ) (c : Name)
    (us : List Level) (a1 a2 a3 : Expr) (t : Nat) (n1 : Name) (t1 : Expr) (bi1 : BinderInfo)
    (n2 : Name) (t2 : Expr) (bi2 : BinderInfo) (rest : Expr) (subj : Nat) (vars : List Nat)
    (depth : Nat) :
    step leaf r (shapeE c us a1 a2 a3 t n1 t1 bi1 n2 t2 bi2 rest) subj vars depth =
      if c = ``Prod.casesOn then
        if t != subj then none else r rest 0 ((vars.map (· + 2)) ++ [1]) (depth + 2)
      else none := rfl

theorem step_bvar {ρ : Type} (leaf : Nat → List Expr → Nat → List Nat → Nat → Option ρ)
    (r : Expr → Nat → List Nat → Nat → Option ρ) (e : Expr) (subj : Nat) (vars : List Nat)
    (depth : Nat) (h : Nat) (hh : headT e = .bvar h) :
    step leaf r e subj vars depth = leaf h (argsT e) subj vars depth :=
  congrArg (fun hd : Expr => stepH leaf hd r e subj vars depth) hh

/-! ## The walk: structural, no fuel, no opaque function -/

/-- `go` without its last test: down the `Prod.casesOn` chain to the leaf,
whose data it returns. Structural recursion on the term. -/
def walkT (e : Expr) (subj : Nat) (vars : List Nat) (depth : Nat) : Option LeafData :=
  match headT e with
  | .bvar hIdx => leafW hIdx (argsT e) subj vars depth
  | _ =>
    match e with
    | .app (.app (.app (.app (.app (.const c _) _) _) _) (.bvar t))
        (.lam _ _ (.lam _ _ rest _) _) =>
      if c = ``Prod.casesOn then
        if t != subj then none else walkT rest 0 ((vars.map (· + 2)) ++ [1]) (depth + 2)
      else none
    | _ => none
termination_by structural e

/-- THE RECURSION EQUATION of the walk, for every term: one unfolding. -/
theorem walkT_sol (e : Expr) (subj : Nat) (vars : List Nat) (depth : Nat) :
    walkT e subj vars depth = step leafW walkT e subj vars depth := by
  first
    | exact walkT.eq_def e subj vars depth
    | (rw [walkT.eq_def]; done)
    | (rw [walkT.eq_def]; rfl)
    | (unfold walkT; rfl)
    | (rw [walkT]; rfl)
    | (unfold walkT step stepH casesArm; rfl)

theorem walkT_bvar (e : Expr) (subj : Nat) (vars : List Nat) (depth : Nat) (h : Nat)
    (hh : headT e = .bvar h) :
    walkT e subj vars depth = some ⟨h, argsT e, subj, vars, depth⟩ :=
  (walkT_sol e subj vars depth).trans (step_bvar leafW walkT e subj vars depth h hh)

theorem walkT_shape (c : Name)
    (us : List Level) (a1 a2 a3 : Expr) (t : Nat) (n1 : Name) (t1 : Expr) (bi1 : BinderInfo)
    (n2 : Name) (t2 : Expr) (bi2 : BinderInfo) (rest : Expr) (subj : Nat) (vars : List Nat)
    (depth : Nat) :
    walkT (shapeE c us a1 a2 a3 t n1 t1 bi1 n2 t2 bi2 rest) subj vars depth =
      if c = ``Prod.casesOn then
        if t != subj then none else walkT rest 0 ((vars.map (· + 2)) ++ [1]) (depth + 2)
      else none :=
  (walkT_sol (shapeE c us a1 a2 a3 t n1 t1 bi1 n2 t2 bi2 rest) subj vars depth).trans
    (step_shape leafW walkT c us a1 a2 a3 t n1 t1 bi1 n2 t2 bi2 rest subj vars depth)

/-! ## The total `go` and `prodMatcherArity?` -/

/-- `go`, total: the walk, then the leaf's decision. -/
def goT (eqv : Expr → Expr → Bool) (e : Expr) (subj : Nat) (vars : List Nat) (depth : Nat) :
    Option Nat :=
  (walkT e subj vars depth).bind (leafD eqv)

/-- The value of a matcher: three lambdas (`motive`, the subject, the
alternative), then the chain (the compiler's text). -/
def valueArityOf (go : Expr → Nat → List Nat → Nat → Option Nat) : Expr → Option Nat
  | .lam _ _ (.lam _ _ (.lam _ _ body _) _) _ => go body 1 [] 0
  | _ => none

/-- The constant: a definition (the compiler's text). -/
def infoArityOf (go : Expr → Nat → List Nat → Nat → Option Nat) :
    Option ConstantInfo → Option Nat
  | some (.defnInfo d) => valueArityOf go d.value
  | _ => none

/-- `prodMatcherArity?` over the test `eqv`, total. -/
def prodMatcherArityG (eqv : Expr → Expr → Bool) (env : Environment) (n : Name) : Option Nat :=
  infoArityOf (goT eqv) (env.find? n)

/-- `prodMatcherArity?`, total, with the compiler's own test (`==`). -/
def prodMatcherArityT (env : Environment) (n : Name) : Option Nat :=
  prodMatcherArityG exprEqv env n

/-- `prodMatcherArity?`, total, with the structural test. A second candidate;
measured only. -/
def prodMatcherArityS (env : Environment) (n : Name) : Option Nat :=
  prodMatcherArityG bvarEqv env n

/-! ## Successful inputs are preserved -/

/-- The decorations of one `Prod.casesOn` level: what the walk does not read. -/
structure Deco where
  us : List Level
  α : Expr
  β : Expr
  motive : Expr
  n1 : Name
  t1 : Expr
  bi1 : BinderInfo
  n2 : Name
  t2 : Expr
  bi2 : BinderInfo

/-- One level: `Prod.casesOn (bvar t) (fun v s => rest)`. -/
def casesE (dc : Deco) (t : Nat) (rest : Expr) : Expr :=
  shapeE ``Prod.casesOn dc.us dc.α dc.β dc.motive t dc.n1 dc.t1 dc.bi1 dc.n2 dc.t2 dc.bi2 rest

/-- The leaf: the alternative (index `depth`) applied to the components and
the last subject. -/
def leafE (depth subj : Nat) (vars : List Nat) : Expr :=
  mkL (.bvar depth) ((vars ++ [subj]).map Expr.bvar)

/-- The canonical body of a pair matcher: the levels, then the leaf, with
the indices the compiler's `go` expects. -/
def chainE : List Deco → Nat → List Nat → Nat → Expr
  | [], subj, vars, depth => leafE depth subj vars
  | dc :: dcs, subj, vars, depth =>
    casesE dc subj (chainE dcs 0 ((vars.map (· + 2)) ++ [1]) (depth + 2))

/-- The canonical value of a pair matcher with `dcs.length + 1` components. -/
def matcherE (m0 m1 m2 : Name × Expr × BinderInfo) (dcs : List Deco) : Expr :=
  .lam m0.1 m0.2.1 (.lam m1.1 m1.2.1 (.lam m2.1 m2.2.1 (chainE dcs 1 [] 0) m2.2.2) m1.2.2) m0.2.2

theorem natBne_self (n : Nat) : (n != n) = false := by
  first
    | exact bne_self_eq_false n
    | exact bne_self_eq_false' n
    | simp

theorem natBne_ne (n : Nat) : ¬ ((n != n) = true) :=
  fun h => Bool.noConfusion ((natBne_self n).symm.trans h)

theorem walkT_leafE (depth subj : Nat) (vars : List Nat) (subj' : Nat) (vars' : List Nat)
    (depth' : Nat) :
    walkT (leafE depth subj vars) subj' vars' depth' =
      some ⟨depth, (vars ++ [subj]).map Expr.bvar, subj', vars', depth'⟩ :=
  (walkT_bvar (leafE depth subj vars) subj' vars' depth' depth
    (headT_mkL ((vars ++ [subj]).map Expr.bvar) (.bvar depth))).trans
    (congrArg (fun as : List Expr => some (LeafData.mk depth as subj' vars' depth'))
      (argsT_mkL_bvar depth ((vars ++ [subj]).map Expr.bvar)))

theorem walkT_casesE (dc : Deco) (t : Nat) (rest : Expr) (subj : Nat) (vars : List Nat)
    (depth : Nat) :
    walkT (casesE dc t rest) subj vars depth =
      if t != subj then none else walkT rest 0 ((vars.map (· + 2)) ++ [1]) (depth + 2) :=
  (walkT_shape ``Prod.casesOn dc.us dc.α dc.β dc.motive t dc.n1 dc.t1 dc.bi1 dc.n2 dc.t2 dc.bi2
    rest subj vars depth).trans (if_pos rfl)

theorem walkT_casesE_self (dc : Deco) (subj : Nat) (rest : Expr) (vars : List Nat)
    (depth : Nat) :
    walkT (casesE dc subj rest) subj vars depth =
      walkT rest 0 ((vars.map (· + 2)) ++ [1]) (depth + 2) :=
  (walkT_casesE dc subj rest subj vars depth).trans (if_neg (natBne_ne subj))

/-- **The walk succeeds on every canonical pair-matcher body**, and its leaf
data is what the leaf's decision expects. No premise; no test. -/
theorem walkT_chain : ∀ (dcs : List Deco) (subj : Nat) (vars : List Nat) (depth : Nat),
    ∃ d : LeafData, walkT (chainE dcs subj vars depth) subj vars depth = some d ∧
      d.hIdx = d.depth ∧ d.args = (d.vars ++ [d.subj]).map Expr.bvar ∧
      d.args.length = vars.length + 1 + dcs.length
  | [], subj, vars, depth =>
    ⟨⟨depth, (vars ++ [subj]).map Expr.bvar, subj, vars, depth⟩,
      walkT_leafE depth subj vars subj vars depth, rfl, rfl, by
        show ((vars ++ [subj]).map Expr.bvar).length = vars.length + 1 + ([] : List Deco).length
        simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] <;>
          omega⟩
  | dc :: dcs, subj, vars, depth =>
    match walkT_chain dcs 0 ((vars.map (· + 2)) ++ [1]) (depth + 2) with
    | ⟨d, hw, h1, h2, h3⟩ =>
      ⟨d, (walkT_casesE_self dc subj
          (chainE dcs 0 ((vars.map (· + 2)) ++ [1]) (depth + 2)) vars depth).trans hw,
        h1, h2, by
          rw [h3]
          simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] <;>
            omega⟩

/-- The leaf's decision on the expected arguments, for a test that accepts a
bound variable against itself. -/
theorem leafT_canon (eqv : Expr → Expr → Bool) (hrefl : ∀ i, eqv (.bvar i) (.bvar i) = true)
    (hIdx : Nat) (args : List Expr) (subj : Nat) (vars : List Nat) (depth : Nat)
    (h1 : hIdx = depth) (h2 : args = (vars ++ [subj]).map Expr.bvar) :
    leafT eqv hIdx args subj vars depth = some args.length := by
  subst h1
  subst h2
  exact (if_neg (natBne_ne _)).trans (if_pos (listEqv_refl eqv hrefl _))

theorem leafD_canon (eqv : Expr → Expr → Bool) (hrefl : ∀ i, eqv (.bvar i) (.bvar i) = true) :
    ∀ (d : LeafData), d.hIdx = d.depth → d.args = (d.vars ++ [d.subj]).map Expr.bvar →
      leafD eqv d = some d.args.length
  | ⟨hIdx, args, subj, vars, depth⟩, h1, h2 =>
    leafT_canon eqv hrefl hIdx args subj vars depth h1 h2

/-- **`go` succeeds on every canonical pair-matcher body**, for a test that
accepts a bound variable against itself: the result is the number of
components. -/
theorem goT_chain (eqv : Expr → Expr → Bool) (hrefl : ∀ i, eqv (.bvar i) (.bvar i) = true)
    (dcs : List Deco) (subj : Nat) (vars : List Nat) (depth : Nat) :
    goT eqv (chainE dcs subj vars depth) subj vars depth =
      some (vars.length + 1 + dcs.length) :=
  match walkT_chain dcs subj vars depth with
  | ⟨d, hw, h1, h2, h3⟩ =>
    (congrArg (fun o : Option LeafData => o.bind (leafD eqv)) hw).trans
      ((Option.bind_some d (leafD eqv)).trans
        ((leafD_canon eqv hrefl d h1 h2).trans (congrArg some h3)))

theorem valueArityG_matcherE (eqv : Expr → Expr → Bool)
    (hrefl : ∀ i, eqv (.bvar i) (.bvar i) = true) (m0 m1 m2 : Name × Expr × BinderInfo)
    (dcs : List Deco) :
    valueArityOf (goT eqv) (matcherE m0 m1 m2 dcs) = some (dcs.length + 1) :=
  (show valueArityOf (goT eqv) (matcherE m0 m1 m2 dcs) = goT eqv (chainE dcs 1 [] 0) 1 [] 0
      from rfl).trans
    ((goT_chain eqv hrefl dcs 1 [] 0).trans
      (congrArg some (by
        show 0 + 1 + dcs.length = dcs.length + 1
        omega)))

/-- **Successful inputs are preserved**: a constant whose value is a
canonical pair matcher with `k = dcs.length + 1` components has arity `k`. -/
theorem prodMatcherArityG_canon (eqv : Expr → Expr → Bool)
    (hrefl : ∀ i, eqv (.bvar i) (.bvar i) = true) (env : Environment) (n : Name)
    (d : DefinitionVal) (m0 m1 m2 : Name × Expr × BinderInfo) (dcs : List Deco)
    (hf : env.find? n = some (.defnInfo d)) (hv : d.value = matcherE m0 m1 m2 dcs) :
    prodMatcherArityG eqv env n = some (dcs.length + 1) :=
  (congrArg (infoArityOf (goT eqv)) hf).trans
    ((congrArg (valueArityOf (goT eqv)) hv).trans (valueArityG_matcherE eqv hrefl m0 m1 m2 dcs))

/-- The same for the structural test: NO premise about any test. -/
theorem prodMatcherArityS_canon (env : Environment) (n : Name)
    (d : DefinitionVal) (m0 m1 m2 : Name × Expr × BinderInfo) (dcs : List Deco)
    (hf : env.find? n = some (.defnInfo d)) (hv : d.value = matcherE m0 m1 m2 dcs) :
    prodMatcherArityS env n = some (dcs.length + 1) :=
  prodMatcherArityG_canon bvarEqv bvarEqv_refl env n d m0 m1 m2 dcs hf hv

/-- The same for the compiler's own test, under the ONE premise about it
(a statement about the extern `Expr.eqv`: not proved, not assumed anywhere). -/
theorem prodMatcherArityT_canon (hrefl : ∀ i : Nat, ((Expr.bvar i) == (Expr.bvar i)) = true)
    (env : Environment) (n : Name)
    (d : DefinitionVal) (m0 m1 m2 : Name × Expr × BinderInfo) (dcs : List Deco)
    (hf : env.find? n = some (.defnInfo d)) (hv : d.value = matcherE m0 m1 m2 dcs) :
    prodMatcherArityT env n = some (dcs.length + 1) :=
  prodMatcherArityG_canon exprEqv hrefl env n d m0 m1 m2 dcs hf hv

/-! ## The test enters at the leaf only -/

theorem leafT_congr (eqv eqv' : Expr → Expr → Bool)
    (h : ∀ a i, eqv a (.bvar i) = eqv' a (.bvar i)) (hIdx : Nat) (args : List Expr)
    (subj : Nat) (vars : List Nat) (depth : Nat) :
    leafT eqv hIdx args subj vars depth = leafT eqv' hIdx args subj vars depth :=
  congrArg (fun b : Bool => if hIdx != depth then none else if b then some args.length else none)
    (listEqv_congr eqv eqv' h args (vars ++ [subj]))

theorem goT_congr (eqv eqv' : Expr → Expr → Bool)
    (h : ∀ a i, eqv a (.bvar i) = eqv' a (.bvar i)) : goT eqv = goT eqv' :=
  funext fun e => funext fun subj => funext fun vars => funext fun depth =>
    congrArg (fun f : LeafData → Option Nat => (walkT e subj vars depth).bind f)
      (funext fun d => leafT_congr eqv eqv' h d.hIdx d.args d.subj d.vars d.depth)

/-- Two tests that agree against bound variables give the same function. -/
theorem prodMatcherArityG_congr (eqv eqv' : Expr → Expr → Bool)
    (h : ∀ a i, eqv a (.bvar i) = eqv' a (.bvar i)) (env : Environment) (n : Name) :
    prodMatcherArityG eqv env n = prodMatcherArityG eqv' env n :=
  congrArg (fun g : Expr → Nat → List Nat → Nat → Option Nat => infoArityOf g (env.find? n))
    (goT_congr eqv eqv' h)

/-- The compiler's test and the structural one give the same function under
ONE premise about the extern (not proved, not assumed; measured). -/
theorem prodMatcherArityT_eq_S
    (h : ∀ (a : Expr) (i : Nat), (a == Expr.bvar i) = bvarEqv a (.bvar i))
    (env : Environment) (n : Name) : prodMatcherArityT env n = prodMatcherArityS env n :=
  prodMatcherArityG_congr exprEqv bvarEqv h env n

end Tools.ShippingReaderMatcherArity

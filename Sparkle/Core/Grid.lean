/-
  `systolic_grid%` — a two-dimensional array of cells, written once.

  A systolic array is R × C copies of one cell, each wired to its left and
  upper neighbour.  The synthesis elaborator instantiates one sub-module per
  call, so the array has to be R·C separate `let`-bound calls; this macro
  writes them:

    systolic_grid% 4 4
      (cell i j left up => pe left up (Signal.pure (weight i j)))
      (right := aOut) (down := pOut)
      (leftEdge i => activation a i)
      (topEdge j => Signal.pure 0#32)

  expands to

    let cell_0_0 := pe (activation a 0) (Signal.pure 0#32) (Signal.pure (weight 0 0))
    let cell_0_1 := pe cell_0_0.aOut    (Signal.pure 0#32) (Signal.pure (weight 0 1))
    …
    let cell_3_3 := pe cell_3_2.aOut    cell_2_3.pOut      (Signal.pure (weight 3 3))
    cell_3_3.pOut ++ cell_3_2.pOut ++ cell_3_1.pOut ++ cell_3_0.pOut

  * `cell i j left up => e` — the cell at row `i`, column `j`.  `i` and `j`
    are replaced by numerals, `left` / `up` by the neighbours' outputs (or
    the edge terms).  `e` must be a call of a `@[hardware_module]` whose
    result has the two fields named by `right` and `down`.
  * `leftEdge i => e`, `topEdge j => e` — what enters row `i` from the left
    and column `j` from above.
  * The value is the bottom row's `down` outputs concatenated, column
    C-1 in the most significant position.

  The substitution is textual (on the syntax tree), so the binder names
  must not be shadowed inside the templates.  The expansion nests R·C
  `let`s: beyond a few hundred cells, raise the elaborator's limit with
  `set_option maxRecDepth 100000 in` on the definition (and on the
  synthesis command that unfolds it).
-/
import Lean

namespace Sparkle.Core

open Lean

/-- Replace identifiers by name. -/
partial def Grid.subst (subst : List (Name × Syntax)) : Syntax → Syntax
  | stx@(.ident _ _ n _) =>
    match subst.find? (·.1 == n.eraseMacroScopes) with
    | some (_, r) => r
    | none => stx
  | .node info kind args => .node info kind (args.map (Grid.subst subst))
  | stx => stx

syntax (name := systolicGrid) "systolic_grid% " num num
  "(" &"cell " ident ident ident ident " => " term ")"
  "(" &"right" " := " ident ")" "(" &"down" " := " ident ")"
  "(" &"leftEdge " ident " => " term ")"
  "(" &"topEdge " ident " => " term ")" : term

macro_rules
  | `(systolic_grid% $rows:num $cols:num
        (cell $i:ident $j:ident $l:ident $u:ident => $cell:term)
        (right := $right:ident) (down := $down:ident)
        (leftEdge $li:ident => $leftE:term)
        (topEdge $tj:ident => $topE:term)) => do
    let r := rows.getNat
    let c := cols.getNat
    if r == 0 || c == 0 then
      Macro.throwError "systolic_grid%: rows and columns must be positive"
    let cellId (a b : Nat) : Ident := mkIdent (Name.mkSimple s!"cell_{a}_{b}")
    let proj (a b : Nat) (field : Ident) : Ident :=
      mkIdent (Name.mkStr (Name.mkSimple s!"cell_{a}_{b}") field.getId.toString)
    let num (k : Nat) : Syntax := (Syntax.mkNumLit (toString k)).raw
    -- bottom row, most significant column first
    let mut body : TSyntax `term := ⟨(proj (r - 1) (c - 1) down).raw⟩
    for k in [1:c] do
      let next : TSyntax `term := ⟨(proj (r - 1) (c - 1 - k) down).raw⟩
      body ← `($body ++ $next)
    -- cells, last first, so the `let`s nest in row-major order
    for a' in [0:r] do
      for b' in [0:c] do
        let a := r - 1 - a'
        let b := c - 1 - b'
        let leftIn : Syntax ←
          if b == 0 then do
            let e : TSyntax `term := ⟨Grid.subst [(li.getId, num a)] leftE.raw⟩
            pure (← `(($e))).raw
          else pure (proj a (b - 1) right).raw
        let upIn : Syntax ←
          if a == 0 then do
            let e : TSyntax `term := ⟨Grid.subst [(tj.getId, num b)] topE.raw⟩
            pure (← `(($e))).raw
          else pure (proj (a - 1) b down).raw
        let inst : TSyntax `term := ⟨Grid.subst
          [(i.getId, num a), (j.getId, num b), (l.getId, leftIn), (u.getId, upIn)] cell.raw⟩
        body ← `(let $(cellId a b) := $inst; $body)
    return body

end Sparkle.Core

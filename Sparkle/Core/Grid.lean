/-
  `systolic_grid%` — a two-dimensional array of cells, written once.
  (`torus_grid%`, further down: a lattice whose cells read all eight
  neighbours — a stencil.)

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

/-!
  `torus_grid%` — a two-dimensional lattice of cells in which every cell
  reads the registered outputs of its eight neighbours (a stencil).

  Unlike the systolic array, the connections go both ways, so the cells
  cannot be a chain of `let`s: the lattice is one `Signal.loop` over the
  packed outputs of all cells, and every neighbour reference is a slice of
  that state.  (The optimiser resolves each slice to the producing cell's
  output port, so the emitted design has direct cell-to-cell wires.)

    torus_grid% 16 16
      (fields := g0 g1 g2) (width := 32)
      (cell i j nb => myCell nb.w.g1 nb.n.g2 (Signal.pure (init i j)))

  * `cell i j nb => e` — the cell at row `i`, column `j`: a call of a
    `@[hardware_module]` whose result has the listed `fields`, each a
    `Signal dom (BitVec width)`, each a register (the lattice needs a
    register between any two cells).  `i` and `j` are replaced by numerals.
  * `nb.<dir>.<field>` — that field of a neighbour.  Directions: `n` (row
    i−1), `s` (row i+1), `w` (column j−1), `e` (column j+1), `nw`, `ne`,
    `sw`, `se`.  The lattice wraps around in both directions (a torus).
  * The value is all cells' fields concatenated: field `f` (0-based, in the
    order listed) of cell (i, j) occupies bits
    `[((i·C + j)·F + f)·width +: width]`, with F the number of fields.

  The substitution is textual, so the binder names must not be shadowed
  inside the template.
-/

/-- The eight neighbour directions as (row offset, column offset). -/
def Grid.direction? : String → Option (Int × Int)
  | "n" => some (-1, 0) | "s" => some (1, 0)
  | "w" => some (0, -1) | "e" => some (0, 1)
  | "nw" => some (-1, -1) | "ne" => some (-1, 1)
  | "sw" => some (1, -1) | "se" => some (1, 1)
  | _ => none

/-- Replace `i`, `j` by numerals and every `nb.<dir>.<field>` by the term
    `slice dir field` produces. -/
partial def Grid.substStencil (nb : Name) (subst : List (Name × Syntax))
    (slice : Syntax → String → String → MacroM Syntax) : Syntax → MacroM Syntax
  | stx@(.ident _ _ n _) => do
    let n := n.eraseMacroScopes
    match subst.find? (·.1 == n) with
    | some (_, r) => pure r
    | none =>
      match n.components with
      | [root, .str .anonymous dir, .str .anonymous field] =>
        if root == nb then slice stx dir field else pure stx
      | root :: _ =>
        if root == nb then
          Macro.throwErrorAt stx s!"torus_grid%: write `{nb}.<direction>.<field>` (directions: n s w e nw ne sw se)"
        else pure stx
      | [] => pure stx
  | .node info kind args => do
    return .node info kind (← args.mapM (Grid.substStencil nb subst slice))
  | stx => pure stx

syntax (name := torusGrid) "torus_grid% " num num
  "(" &"fields" " := " ident+ ")" "(" &"width" " := " num ")"
  "(" &"cell " ident ident ident " => " term ")" : term

macro_rules
  | `(torus_grid% $rows:num $cols:num
        (fields := $fields:ident*) (width := $width:num)
        (cell $i:ident $j:ident $nb:ident => $cell:term)) => do
    let r := rows.getNat
    let c := cols.getNat
    let w := width.getNat
    let fieldNames := fields.toList.map (·.getId.toString)
    let nf := fieldNames.length
    if r == 0 || c == 0 || w == 0 || nf == 0 then
      Macro.throwError "torus_grid%: rows, columns, width and the field list must be non-empty"
    let cellId (a b : Nat) : Ident := mkIdent (Name.mkSimple s!"cell_{a}_{b}")
    let st : Ident := mkIdent (Name.mkSimple "torus_grid_state")
    let sigT : Ident := mkIdent `Sparkle.Core.Signal.Signal
    let num (k : Nat) : TSyntax `term := ⟨(Syntax.mkNumLit (toString k)).raw⟩
    -- Most significant first, as a BALANCED tree of `++`.  Each `++`
    -- becomes a wire holding its whole result; a left-nested chain of n
    -- elements therefore materialises 1 + 2 + … + n elements (the C
    -- simulation of a 32 × 32 lattice copied 300 000 words per cycle to
    -- assemble its output), a balanced tree n·log₂ n.
    let rec concat (fuel : Nat) (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
      match fuel, xs.size with
      | _, 0 => Macro.throwError "torus_grid%: internal: empty concatenation"
      | _, 1 => return xs[0]!
      | 0, _ => Macro.throwError "torus_grid%: internal: concatenation too deep"
      | fuel + 1, n =>
        let hi ← concat fuel (xs.extract 0 (n / 2))
        let lo ← concat fuel (xs.extract (n / 2) n)
        `(($hi) ++ ($lo))
    let concat (xs : List (TSyntax `term)) : MacroM (TSyntax `term) := concat 64 xs.toArray
    -- No cell refers to another by name (every neighbour is a slice of the
    -- state), so each cell is its own small term: `let cell := …; fields`.
    -- The lattice is rows of such terms concatenated — shallow, where a
    -- chain of R·C nested `let`s overflowed the stack at 32 × 32.
    let mut rowTerms : List (TSyntax `term) := []   -- row R-1 first
    for a' in [0:r] do
      let a := r - 1 - a'
      let mut cellTerms : List (TSyntax `term) := []   -- column C-1 first
      for b' in [0:c] do
        let b := c - 1 - b'
        let fieldTerms : List (TSyntax `term) :=
          (List.range nf).reverse.map fun f =>
            ⟨(mkIdent (Name.mkStr (Name.mkSimple s!"cell_{a}_{b}") (fieldNames.getD f ""))).raw⟩
        let packBody ← concat fieldTerms
        let slice (at_ : Syntax) (dir field : String) : MacroM Syntax := do
          let some (di, dj) := Grid.direction? dir
            | Macro.throwErrorAt at_ s!"torus_grid%: unknown direction '{dir}' (use n s w e nw ne sw se)"
          let some f := fieldNames.idxOf? field
            | Macro.throwErrorAt at_ s!"torus_grid%: '{field}' is not one of the fields {fieldNames}"
          let na := ((Int.ofNat a + di) % Int.ofNat r).toNat
          let nbCol := ((Int.ofNat b + dj) % Int.ofNat c).toNat
          let off := ((na * c + nbCol) * nf + f) * w
          return (← `(($st).map (BitVec.extractLsb' $(num off) $(num w) ·))).raw
        let inst : TSyntax `term := ⟨← Grid.substStencil nb.getId
          [(i.getId, (num a).raw), (j.getId, (num b).raw)] slice cell.raw⟩
        let cellTerm ← `((let $(cellId a b) := $inst
                          ($packBody : $sigT _ (BitVec $(num (nf * w))))))
        cellTerms := cellTerms ++ [cellTerm]
      let rowBody ← concat cellTerms
      let rowTerm ← `(($rowBody : $sigT _ (BitVec $(num (c * nf * w)))))
      rowTerms := rowTerms ++ [rowTerm]
    let body ← concat rowTerms
    let loopFn : Ident := mkIdent `Sparkle.Core.Signal.Signal.loop
    `($loopFn fun $st => $body)

end Sparkle.Core

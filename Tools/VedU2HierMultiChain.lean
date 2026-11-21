import Tools.VedU2HierMultiBundle

/-!
# H3-open: the register-bundle reads in an instance's argument net

Meta-level companion of `bundle_slice_fact` (`Tools/VedU2HierMultiBundle.lean`).  `circuit do` bundles the parent's
registers into NESTED pairs (`concat [r₀, concat [r₁, …]]`) and reads register `k` through a chain of `slice`s that peel
the pairs.  `bundleRead?` follows that chain from a wire to the register it reads and emits the script lines proving
`E wire = E reg` one `bundle_slice_fact` per step (each step is a `slice` of a concatenation that is exactly one element),
instead of evaluating the concatenation into `Nat` arithmetic.
-/

namespace Tools.VedU2HierMultiChain

open Sparkle.IR.AST Tools.VedU2Hier

/-- A wire that reads exactly one register of the bundle: the register and the script lines (at indent 2) that prove
`E <w> = E <reg>` (as `bsr<w-index>`), using the facts `hEr<slot>` and `hlS<slot>`. -/
structure BSlice where
  w : String
  reg : String
  slot : Nat
  /-- the hypothesis of type `E w = E reg` the lines end with -/
  pf : String
  lines : Array String
  deriving Inhabited

/-- What a wire is, for the bundle: a register output, or a concatenation of wires. -/
inductive Ident where
  | reg (r : String)
  | cat (y : String) (names : List String)

structure Res where
  lines : Array String
  /-- a hypothesis of type `E "w" = E "z"` (`rfl` when `z = w`) -/
  pf : String
  z : String
  id : Ident

abbrev M := StateM Nat

def fresh : M Nat := modifyGet fun n => (n, n + 1)

/-- `valOf`: follow aliases, concatenations and slices of concatenations that are exactly one element, to a register or to a
concatenation. -/
partial def valOf (b : List Stmt) (regs : List String) (wd : String → Nat) (modN bodyN : String) (tag : String)
    (fuel : Nat) (w : String) : M (Option Res) := do
  match fuel with
  | 0 => return none
  | f + 1 =>
    if regs.contains w then return some { lines := #[], pf := "rfl", z := w, id := .reg w }
    match asgOf b w with
    | some (.ref w') =>
      let some r ← valOf b regs wd modN bodyN tag f w' | return none
      let c ← fresh
      let u := s!"{tag}a{c}"
      let u2 := s!"{tag}b{c}"
      let ls := r.lines ++ #[
        s!"  have {u} : E {w.quote} = E {w'.quote} := by",
        s!"    have h := hasgF {w.quote} _ rfl",
        s!"    simp only [Sparkle.IR.Semantics.evalExpr, Option.some.injEq] at h",
        s!"    exact h.symm",
        s!"  have {u2} : E {w.quote} = E {r.z.quote} := {u}.trans {r.pf}"]
      return some { r with lines := ls, pf := u2 }
    | some (.concat es) =>
      match es.mapM (fun e => match e with | .ref n => some n | _ => none) with
      | some names => return some { lines := #[], pf := "rfl", z := w, id := .cat w names }
      | none => return none
    | some (.slice (.ref x) hi lo) =>
      let some rx ← valOf b regs wd modN bodyN tag f x | return none
      match rx.id with
      | .cat y names =>
        let ws := names.map wd
        let some k := (List.range names.length).find? (fun k =>
            (ws.drop (k + 1)).foldl (· + ·) 0 == lo && hi + 1 == lo + ws[k]! && 0 < ws[k]!) | return none
        let nk := names[k]!
        let some rn ← valOf b regs wd modN bodyN tag f nk | return none
        let c ← fresh
        let s1 := s!"{tag}s{c}"
        let s2 := s!"{tag}t{c}"
        let hr := s!"{tag}r{c}"
        let nameL := ", ".intercalate (names.map String.quote)
        -- the range of the element: a register (its fact), or a concatenation (its widths)
        let rangeLines : Array String :=
          match rn.id with
          | .reg r =>
            match regs.idxOf? r with
            | some slot => #[
                s!"  have {hr} : E {nk.quote} < 2 ^ (Tools.VedU1Contract.declWidth {modN} {nk.quote}) := by",
                s!"    rw [{if rn.pf == "rfl" then "" else rn.pf ++ ", "}hEr{slot}]",
                s!"    have hwd : Tools.VedU1Contract.declWidth {modN} {nk.quote} = {wd nk} := by decide",
                s!"    rw [hwd]",
                s!"    exact hlS{slot}"]
            | none => #[s!"  fail \"H3: register {r} has no slot\""]
          | .cat z zs =>
            #[s!"  have {hr} : E {nk.quote} < 2 ^ (Tools.VedU1Contract.declWidth {modN} {nk.quote}) := by",
              s!"    {if rn.pf == "rfl" then "skip" else "rw [" ++ rn.pf ++ "]"}",
              s!"    exact Tools.VedU2HierMulti.concat_range (Tools.VedU1Contract.declWidth {modN}) {bodyN} E hasgF {z.quote} [{", ".intercalate (zs.map String.quote)}] (by decide) (by decide)"]
        let ls := rx.lines ++ rn.lines ++ rangeLines ++ #[
          s!"  have {s1} : E {w.quote} = E {nk.quote} := by",
          s!"    exact Tools.VedU2HierMulti.bundle_slice_fact (Tools.VedU1Contract.declWidth {modN}) {bodyN} E hasgF {w.quote} {x.quote} {y.quote} {hi} {lo} [{nameL}] {k} (by decide) (by decide) {rx.pf} (by decide) (by decide) (by decide) (by decide) {hr}",
          s!"  have {s2} : E {w.quote} = E {rn.z.quote} := {s1}.trans {rn.pf}"]
        return some { lines := ls, pf := s2, z := rn.z, id := rn.id }
      | .reg _ => return none
    | _ => return none

/-- Does `w` read exactly one register of the bundle (through slices of concatenations)?  The wire's facts. -/
def bundleRead? (b : List Stmt) (regs : List String) (wd : String → Nat) (modN bodyN : String) (idx : Nat)
    (w : String) : Option BSlice :=
  if regs.contains w then none
  else match asgOf b w with
    | some (.slice _ _ _) =>
      match (valOf b regs wd modN bodyN s!"bs{idx}_" 400 w).run' 0 with
      | some r =>
        match r.id with
        | .reg reg => match regs.idxOf? reg with
          | some slot => some { w, reg, slot, pf := s!"bsr{idx}", lines := r.lines.push s!"  have bsr{idx} : E {w.quote} = E {reg.quote} := {r.pf}" }
          | none => none
        | .cat .. => none
      | none => none
    | _ => none

/-- The wires of the nets read by `x`, in dependency order (dependencies first), stopping at `stops` (inputs, register
outputs) and at the register-bundle reads; and those reads. -/
partial def netChainB (stops : List String) (regs : List String) (b : List Stmt) (wd : String → Nat) (modN bodyN : String)
    (fuel : Nat) (x : String) : StateM Nat (List String × List BSlice) := do
  match fuel with
  | 0 => return ([], [])
  | f + 1 =>
    if stops.contains x then return ([], [])
    else
      let idx ← modifyGet fun n => (n, n + 1)
      match bundleRead? b regs wd modN bodyN idx x with
      | some bs => return ([], [bs])
      | none =>
        match asgOf b x with
        | some r =>
          let mut ws : List String := []
          let mut bss : List BSlice := []
          for y in refsOf r do
            let (w1, b1) ← netChainB stops regs b wd modN bodyN f y
            ws := ws ++ w1
            bss := bss ++ b1
          return (ws ++ [x], bss)
        | none => return ([], [])
where
  refsOf : Expr → List String
    | .ref n => [n]
    | .op _ as => as.flatMap refsOf
    | .concat as => as.flatMap refsOf
    | .slice e _ _ => refsOf e
    | .index a i => refsOf a ++ refsOf i
    | _ => []

end Tools.VedU2HierMultiChain

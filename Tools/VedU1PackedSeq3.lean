import Tools.VedU1PackedSeq2

/-!
# Packed result with registers: the cheap precheck of the per-statement first attempt (`sparkle-ved-packed-seq3`)

The per-statement script of `Tools.VedU1PackedSeq2` substitutes the equations of the earlier statements into each
statement (`ved_seq_simp_nd [hs0, .., hs(k-1)] at hsk`), so the type of statement `k` grows with its fully expanded
expression tree.  `substStats` computes that growth on the module's arrangement, BEFORE any tactic runs: for every
assignment the node count of its right-hand side with every earlier-assigned wire expanded (shared wires counted
every time they are used, as the simp-substituted term does), summed over the body.
-/

/-- The first attempt is skipped (the flat loop script runs at once) when the summed expanded size of the body's assignments
(`substStats`) exceeds this.  Measured (`sparkle-ved-packed-seq3`): the packed rows the per-statement script proves have at most 6424
(R13 6097, R14 6424 [its kernel check fails for another reason], R41 3430, R46 2804, R47 2700, R55 2970); R23 has 44568 and
exhausts the whole proof budget (8·10^9 heartbeats, 520 s) before the fallback runs.  `0` = every body with registers is
skipped (a test hook of the check). -/
register_option ved.packedseq3.maxExp : Nat := {
  defValue := 20000
  descr := "ved.packedseq3.maxExp: largest summed expanded assignment size for which the per-statement first attempt runs"
}

namespace Tools.VedU1PackedSeq3

open Sparkle.IR.AST

/-- node count of an expression with the wires of `sz` expanded (an unknown name — an input, a register — counts 1) -/
partial def exprSize (sz : Std.HashMap String Nat) : Expr → Nat
  | .const .. => 1
  | .ref n => sz.getD n 1
  | .op _ args => args.foldl (fun a e => a + exprSize sz e) 1
  | .concat args => args.foldl (fun a e => a + exprSize sz e) 1
  | .slice e .. => exprSize sz e + 1
  | .sliceDim e .. => exprSize sz e + 1
  | .index a i => exprSize sz a + exprSize sz i + 1

structure Stats where
  nAssign : Nat
  nRegs : Nat
  /-- sum of the plain right-hand-side sizes -/
  own : Nat
  /-- sum / maximum of the expanded sizes of the assignments (capped at 10^15 each) -/
  sumExp : Nat
  maxExp : Nat
  deriving Repr

def substStats (body : List Stmt) : Stats := Id.run do
  let cap := 1000000000000000
  let mut sz : Std.HashMap String Nat := {}
  let mut st : Stats := { nAssign := 0, nRegs := 0, own := 0, sumExp := 0, maxExp := 0 }
  for s in body do
    match s with
    | .assign l r =>
      let e := min cap (exprSize sz r)
      sz := sz.insert l e
      st := { st with nAssign := st.nAssign + 1, own := st.own + exprSize {} r,
                      sumExp := st.sumExp + e, maxExp := max st.maxExp e }
    | .register .. => st := { st with nRegs := st.nRegs + 1 }
    | _ => pure ()
  return st

open Lean in
/-- the first attempt runs only when `substStats body` is within the bound (`ved.packedseq3.maxExp`) -/
def firstAttemptOk (body : List Stmt) : CoreM Bool := do
  let st := substStats body
  let ok := st.sumExp ≤ ved.packedseq3.maxExp.get (← getOptions)
  if ved.packedseq2.dbg.get (← getOptions) ≥ 1 then
    IO.eprintln s!"VED PKSEQ3 gate {if ok then "run" else "skip"} {repr st}"
  return ok

end Tools.VedU1PackedSeq3

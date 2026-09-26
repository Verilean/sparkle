/-
  Sparkle.Core.CircuitSeq — multi-cycle sequential programs on top of
  `circuit do`.

  `circuit seq do` reads like software that takes one clock cycle per
  `step`:

    circuit seq do
      let acc ← Signal.reg 0#8
      let i   ← Signal.reg 0#3
      waitUntil start                 -- idle until `start`
      step                            -- one cycle
        acc <~ 0#8
        i   <~ 0#3
      while Signal.ult i (Signal.pure 4#3) do     -- one cycle per iteration
        step
          acc <~ acc + x
          i   <~ i + 1#3
      return acc

  Statements (`seqStmt`):
    * `step s*`          — one cycle; `s*` are ordinary `circuit do`
                           statements (`<~`, `let _ := _`, `if`, `match`).
    * `pause`            — one idle cycle.
    * `waitUntil c`      — stay until the Signal Bool `c` is true, then
                           continue on the next cycle.
    * `while c do seq+`  — loop.  A body that is a single `step` costs one
                           cycle per iteration (the test and the body share
                           the cycle); otherwise the test takes its own
                           cycle.  Leaving the loop takes one cycle.
    * `if c then seq* else seq*` — branch; the test takes one cycle.
    * `halt`             — stay forever (until reset).
  After the last statement the program restarts from the first one.

  Timing rule: every condition is evaluated in its own state, so it sees
  every register write made by the statements before it — `i <~ 0`
  followed by `while i < 4` tests the new `i`.  Registers not written in
  a cycle hold their value.

  Lowering: each statement becomes one or more states of a hidden
  program-counter register, and the whole program becomes one `match` on
  it inside an ordinary `circuit do`, so simulation and synthesis are
  exactly those of `circuit do` (a `Signal.mux` chain).
-/

import Sparkle.Core.CircuitDo

namespace Sparkle.Core

open Sparkle.Core.Domain
open Sparkle.Core.Signal

declare_syntax_cat seqStmt (behavior := both)

/-- `step s*` — one clock cycle running ordinary `circuit do` statements. -/
syntax &"step" withPosition((colGe cdoStmt)+) : seqStmt
/-- `pause` — one idle clock cycle. -/
syntax &"pause" : seqStmt
/-- `waitUntil c` — stay until `c` is true. -/
syntax &"waitUntil " term:max : seqStmt
/-- `halt` — stay forever (until reset). -/
syntax &"halt" : seqStmt
/-- `while c do seq+` — loop while `c` is true. -/
syntax "while " termBeforeDo " do" withPosition((colGe seqStmt)+) : seqStmt
/-- `if c then seq* else seq*` — sequence-level branch. -/
syntax "if " term " then" withPosition((colGe seqStmt)*)
       "else" withPosition((colGe seqStmt)*) : seqStmt

/-- Top-level items: register declarations, `let`s, the program, `return`. -/
declare_syntax_cat seqTop (behavior := both)
syntax cdoStmt : seqTop
syntax seqStmt : seqTop

syntax "circuit" &"seq" "do" ppLine withPosition((colGe seqTop)*) : term

/-- Number of states a statement occupies. -/
partial def seqSize : Lean.TSyntax `seqStmt → Lean.MacroM Nat
  | `(seqStmt| step $_*) | `(seqStmt| pause) | `(seqStmt| waitUntil $_)
  | `(seqStmt| halt) => pure 1
  | `(seqStmt| while $_ do $body*) => do
    if isSingleStep body then pure 1 else pure (1 + (← seqSizeAll body))
  | `(seqStmt| if $_ then $a* else $b*) => do
    pure (1 + (← seqSizeAll a) + (← seqSizeAll b))
  | _ => Lean.Macro.throwUnsupported
where
  isSingleStep (body : Array (Lean.TSyntax `seqStmt)) : Bool :=
    body.size == 1 && (match body[0]! with
      | `(seqStmt| step $_*) => true
      | _ => false)
  seqSizeAll (xs : Array (Lean.TSyntax `seqStmt)) : Lean.MacroM Nat :=
    xs.foldlM (fun acc x => return acc + (← seqSize x)) 0

/-- Compilation context: the program counter's name and width. -/
structure SeqCtx where
  pc : Lean.Ident
  width : Nat

def SeqCtx.lit (ctx : SeqCtx) (k : Nat) : Lean.MacroM (Lean.TSyntax `term) :=
  `(BitVec.ofNat $(Lean.quote ctx.width) $(Lean.quote k))

def SeqCtx.goto (ctx : SeqCtx) (k : Nat) : Lean.MacroM (Lean.TSyntax `cdoStmt) := do
  `(cdoStmt| $ctx.pc:ident <~ $(← ctx.lit k))

mutual
/-- Compile a statement sequence whose first state is `base`; control
    leaves to state `after`.  Returns `(state, statements)` arms. -/
partial def seqCompile (ctx : SeqCtx) (stmts : Array (Lean.TSyntax `seqStmt))
    (base after : Nat) :
    Lean.MacroM (Array (Nat × Array (Lean.TSyntax `cdoStmt))) := do
  let mut arms := #[]
  let mut p := base
  for i in [:stmts.size] do
    let s := stmts[i]!
    let size ← seqSize s
    let next := if i + 1 == stmts.size then after else p + size
    arms := arms ++ (← seqCompileOne ctx s p next)
    p := p + size
  return arms

partial def seqCompileOne (ctx : SeqCtx) (s : Lean.TSyntax `seqStmt) (p next : Nat) :
    Lean.MacroM (Array (Nat × Array (Lean.TSyntax `cdoStmt))) := do
  match s with
  | `(seqStmt| step $ss*) => return #[(p, ss.push (← ctx.goto next))]
  | `(seqStmt| pause) => return #[(p, #[← ctx.goto next])]
  | `(seqStmt| halt) => return #[(p, #[])]
  | `(seqStmt| waitUntil $c) =>
    let g ← ctx.goto next
    return #[(p, #[← `(cdoStmt| if $c then $g:cdoStmt else)])]
  | `(seqStmt| while $c do $body*) =>
    let g ← ctx.goto next
    if seqSize.isSingleStep body then
      -- Test and body share one state: run the body and stay while `c`.
      match body[0]! with
      | `(seqStmt| step $ss*) =>
        return #[(p, #[← `(cdoStmt| if $c then $ss* else $g:cdoStmt)])]
      | _ => Lean.Macro.throwUnsupported
    else
      let gBody ← ctx.goto (p + 1)
      let header := (p, #[← `(cdoStmt| if $c then $gBody:cdoStmt else $g:cdoStmt)])
      return #[header] ++ (← seqCompile ctx body (p + 1) p)
  | `(seqStmt| if $c then $a* else $b*) =>
    let sizeA ← seqSize.seqSizeAll a
    let entryA := if a.isEmpty then next else p + 1
    let entryB := if b.isEmpty then next else p + 1 + sizeA
    let gA ← ctx.goto entryA
    let gB ← ctx.goto entryB
    let test := (p, #[← `(cdoStmt| if $c then $gA:cdoStmt else $gB:cdoStmt)])
    return #[test] ++ (← seqCompile ctx a (p + 1) next)
      ++ (← seqCompile ctx b (p + 1 + sizeA) next)
  | _ => Lean.Macro.throwUnsupported
end

/-- Smallest `w ≥ 1` with `n ≤ 2^w`. -/
def seqPcWidth (n : Nat) : Nat := Id.run do
  let mut w := 1
  while 2 ^ w < n do w := w + 1
  return w

macro_rules
  | `(circuit seq do $items:seqTop*) => do
    let mut pre : Array (Lean.TSyntax `cdoStmt) := #[]
    let mut program : Array (Lean.TSyntax `seqStmt) := #[]
    let mut retStmt : Option (Lean.TSyntax `cdoStmt) := none
    for item in items do
      match item with
      | `(seqTop| $s:seqStmt) =>
        if retStmt.isSome then
          Lean.Macro.throwError "circuit seq do: `return` must come after the program"
        program := program.push s
      | `(seqTop| $s:cdoStmt) =>
        match s with
        | `(cdoStmt| return $_) | `(cdoStmt| return $_ ;) => retStmt := some s
        | `(cdoStmt| let $_:ident ← Signal.reg $_) | `(cdoStmt| let $_:ident ← Signal.reg $_ ;)
        | `(cdoStmt| let $_:ident := $_) | `(cdoStmt| let $_:ident := $_ ;) =>
          unless program.isEmpty do
            Lean.Macro.throwError
              "circuit seq do: declare registers and `let`s before the first statement of the program"
          pre := pre.push s
        | _ =>
          Lean.Macro.throwError
            "circuit seq do: put `<~`, `if` and `match` inside a `step`"
      | _ => Lean.Macro.throwUnsupported
    if program.isEmpty then
      Lean.Macro.throwError "circuit seq do: the program is empty (add a `step`, `waitUntil`, …)"
    let some ret := retStmt
      | Lean.Macro.throwError "circuit seq do: missing `return`"
    let n ← program.foldlM (fun acc s => return acc + (← seqSize s)) 0
    let pc := Lean.mkIdent (← Lean.Macro.addMacroScope `seqPc)
    let ctx : SeqCtx := { pc, width := seqPcWidth n }
    let arms ← seqCompile ctx program 0 0
    let mut matchArms : Array (Lean.TSyntax `cdoMatchArm) := #[]
    for (k, body) in arms do
      let pat ← ctx.lit k
      matchArms := matchArms.push (← `(cdoMatchArm| | $pat => $body*))
    -- Unused encodings (n < 2^width) restart the program.
    matchArms := matchArms.push (← `(cdoMatchArm| | _ => $(← ctx.goto 0):cdoStmt))
    let pcDecl ← `(cdoStmt| let $ctx.pc:ident ← Signal.reg $(← ctx.lit 0))
    let theMatch ← `(cdoStmt| match $ctx.pc with $matchArms*)
    let stmts := pre.push pcDecl |>.push theMatch |>.push ret
    `(circuit do $stmts*)

end Sparkle.Core

import Tests.Ved.U1EntryCheck

/-!
# Stage of runtime-limit refusals in the U1 checker (`checkU1E`)

A REAL heartbeat / max-recursion exception raised while the checker elaborates
the proof is refused at `[proof]`; one raised in its synchronous kernel
`addDecl` is refused at `[kernel]` (before: both reached the catch-all
`[checker]`).  Each case is pinned through `expectRefused` (stage + none of the
checker's constants left); no OK line is printed.
-/

namespace Tests.Ved.U1StageCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Tools.VedU1Contract Tools.VedU1Entry
open Tests.Ved.U1EntryCheck

/-- Run `act` with a local heartbeat budget of `n` thousand (context field and option,
the latter is what the kernel reads). -/
def withBudget (n : Nat) (act : TermElabM α) : TermElabM α :=
  withOptions (fun o => o.setNat `maxHeartbeats n) <|
  Core.withCurrHeartbeats <|
    withTheReader Core.Context (fun c => { c with maxHeartbeats := n * 1000 }) act

/-- Elaboration of the proof is the expensive part: a `decide` over a long fold. -/
def costlyDecide : TermElabM Syntax :=
  `(by exact (by decide : (List.range 1000).foldl (· + ·) 0 = 499500) ▸ delay8.ved_u1)

-- proof side: heartbeats
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `stHb) do
  discard <| withBudget 20 do
    checkU1 ``delay8 `stHb ``delay8 (← modOf ``delay8) (.term (← costlyDecide))

-- proof side: max recursion depth
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `stRec) do
  discard <| withTheReader Core.Context (fun c => { c with maxRecDepth := 8 }) do
    checkU1 ``delay8 `stRec ``delay8 (← modOf ``delay8)
      (.term (← `(by exact (by decide : (List.range 1000).foldl (· + ·) 0 = 499500) ▸ delay8.ved_u1))))

end Tests.Ved.U1StageCheck

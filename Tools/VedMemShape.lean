import Lean
import Tools.VedU1Loop

/-!
# `Tools.VedMemShape`: the loops of a declaration, including those inside a loop body (`sparkle-ved-memory-rest`)

`Tools.VedU1Loop.loopsOf` keeps the `Signal.loop` applications with no loose bound variable: a loop inside
another's body that is driven by the outer state (a divider fed from pipeline registers) mentions the outer state
variable and is dropped, so its registers (allocated first by the synthesizer) are never paired with a component.
Here the body of every loop is entered with the state variable replaced by the loop itself (the fixpoint form, as
`Tools.VedMemEntry.collectCalls` does for the memory calls), helper definitions are unfolded as chosen by `unf`, and
the loops found are closed terms, children before parents (the order of the synthesizer's register allocation).
-/

namespace Tools.VedMemShape

open Lean Meta

/-- the closed `Signal.loop` terms of `e` (nested loops included, children first, each term once) -/
partial def nestedLoops (unf : Name → Bool) (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let acc ← IO.mkRef (#[] : Array Lean.Expr)
  let seen ← IO.mkRef (∅ : Std.HashSet Lean.Expr)
  let rec go (e : Lean.Expr) : MetaM Unit := do
    if (← seen.get).contains e then return
    seen.modify (·.insert e)
    match e with
    | .app .. =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      if let .const n _ := fn then
        if n == ``Sparkle.Core.Signal.Signal.loop && args.size == 4 then
          let body := match args[3]! with
            | .lam _ _ b _ => b.instantiate1 e
            | f => (mkApp f e).headBeta
          go (← instantiateMVars (← zetaReduce body))
          unless e.hasLooseBVars || (← acc.get).contains e do acc.modify (·.push e)
          return
        if unf n then
          if let some u ← unfoldDefinition? e then
            go (← instantiateMVars (← zetaReduce u.headBeta))
            return
      go fn
      for a in args do go a
    | .lam _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go e
  acc.get

/-- pair the loop state components (by width) with the module's registers when the loops have MORE components than
the module has registers: the synthesizer builds one register for hardware it finds equal (its `Signal.loop` / `let`
caches are keyed by the hardware), so two components, of the same loop or of two loops, can read one register.
Components are taken in order; a component takes (1) the first register not yet taken, when its width agrees, else
(2) a register already taken, of its width, the most recent first, else (3) a later register not yet taken, of its
width; every register must be taken at the end.  Depth-first with backtracking and a step budget; the first pairing
found is returned (among equal widths it is only a choice, the proof compares every register's equation, so a
wrong choice is refused there). -/
def matchRegsShared (widths : List (Option Nat)) (regs : List (String × Nat)) : Option (List String) :=
  if widths.length ≤ regs.length then none else
  let rs := regs.toArray
  let rec go (ws : List (Option Nat)) (taken : Array Bool) (order : List Nat) (acc : List Nat) (fuel : Nat) :
      Option (List Nat) × Nat :=
    match fuel with
    | 0 => (none, 0)
    | fuel + 1 =>
      match ws with
      | [] => (if taken.all id then some acc.reverse else none, fuel)
      | none :: _ => (none, fuel)
      | some w :: ws' =>
        let free := (List.range rs.size).filter fun i => !taken[i]!
        if free.length > ws.length then (none, fuel) else
        let front := match free with
          | i :: _ => if rs[i]!.2 == w then [i] else []
          | [] => []
        let used := order.filter fun i => rs[i]!.2 == w
        let later := free.filter fun i => rs[i]!.2 == w && !front.contains i
        let rec tryAll (cs : List Nat) (fuel : Nat) : Option (List Nat) × Nat :=
          match cs with
          | [] => (none, fuel)
          | i :: cs' =>
            let (r, fuel) := go ws' (taken.set! i true) (i :: order.filter (· != i)) (i :: acc) fuel
            match r with
            | some l => (some l, fuel)
            | none => tryAll cs' fuel
        tryAll (front ++ used ++ later) fuel
  match (go widths (Array.replicate rs.size false) [] [] 20000).1 with
  | some l => some (l.map fun i => rs[i]!.1)
  | none => none

end Tools.VedMemShape

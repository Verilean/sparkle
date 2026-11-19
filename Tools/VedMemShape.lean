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

end Tools.VedMemShape

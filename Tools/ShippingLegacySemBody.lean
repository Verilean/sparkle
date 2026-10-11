import Tools.ShippingLegacySemDispatch

/-! # The body stage of the dispatch, as a list of walks

`BodyReachesInline rec ctx e` (`Tools/ShippingLegacySemDispatch.lean`): a
successful run of the legacy body `Rec.translateExprToWireImpl` on `e`
returns the wire of a run of the inline attempt, same states. For a plain
call (`e.getAppFn = .const name us`) the body does, in order:

1. its prefix and inline arms, then `Rec.translateExprToWireApp` on `e`;
2. in `Rec.translateExprToWireApp`: `handleErrorPatterns`, three inline
   guards, then the chain `handleCircuitMonad`, `handleTupleProjections`,
   `handleApplicative`, `handleBitVecOps`, `handleRegister`, `handleMux`,
   `handleMemory`, `handleLoop` — each returning `none` — and
   `handleDefinitionUnfold`, whose `some w` is returned;
3. in `Rec.handleDefinitionUnfold`: its prefix, then the inline attempt.

**Proved here**: `bodyReachesInline_of_walk` — the composition. Every part
is an explicit hypothesis of the same form (a statement about the successful
runs of ONE program):

| Hypothesis | Program | Says |
|---|---|---|
| `hpre` | `Rec.translateExprToWireImpl` | its run on `e` is a run of `Rec.translateExprToWireApp` on `e` |
| `hchain` | `Rec.translateExprToWireApp` | GIVEN the nine handler facts, its run is a run of `Rec.handleDefinitionUnfold` returning `some` of its wire |
| `PlainChain.errors` | `Rec.handleErrorPatterns` | leaves the builder state |
| `PlainChain.circuit` … `.loop` (8) | one handler each | returns `none` and leaves the builder state (`ReturnsNone`) |
| `hunfold` | `Rec.handleDefinitionUnfold` | a run returning `some w` returns the wire of a run of the inline attempt |

Progress is the number of these removed. `Tools/ShippingLegacySemWalk1.lean`
and `…Walk2.lean` discharge handler facts under conditions on the head's
NAME (the first test of each arm). Nothing here is about the handlers'
arms themselves — a plain head takes none of them. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- Every successful run of `H` from any state returns `none` and leaves the
builder state. -/
def ReturnsNone (H : CompilerM (Option String)) (ctx : CompilerState) : Prop :=
  ∀ (s t : CircuitState) (r : Option String), Returns H ctx s r t → r = none ∧ t = s

/-- The calculus' form of the same fact. -/
theorem returnsNone_of_ensures {H : CompilerM (Option String)} {ctx : CompilerState}
    (h : ∀ s : CircuitState, Ensures H ctx s (fun r t => r = none ∧ t = s)) :
    ReturnsNone H ctx := by
  intro s t r hr
  exact h s r t hr

/-- **The handler facts of a plain call**: what the chain of
`Rec.translateExprToWireApp` does before `Rec.handleDefinitionUnfold`, one
field per handler, for every hint and name flag. -/
structure PlainChain (rec : TranslateFn) (ctx : CompilerState) (e : Lean.Expr) (name : Name)
    (args : Array Lean.Expr) : Prop where
  errors : ∀ (hint : String) (named : Bool) (s t : CircuitState) (u : Unit),
    Returns (Rec.handleErrorPatterns e name args hint named) ctx s u t → t = s
  circuit : ∀ (hint : String) (named : Bool),
    ReturnsNone (Rec.handleCircuitMonad (fun e h t n => rec e h t n) e name args hint named) ctx
  tuple : ∀ (hint : String) (named : Bool),
    ReturnsNone (Rec.handleTupleProjections (fun e h t n => rec e h t n) e name args hint named)
      ctx
  applicative : ∀ (hint : String) (named : Bool),
    ReturnsNone (Rec.handleApplicative (fun e h t n => rec e h t n) e name args hint named) ctx
  bitvec : ∀ (hint : String) (named : Bool),
    ReturnsNone (Rec.handleBitVecOps (fun e h t n => rec e h t n) e name args hint named) ctx
  register : ∀ (hint : String) (named : Bool),
    ReturnsNone (Rec.handleRegister (fun e h t n => rec e h t n) e name args hint named) ctx
  mux : ∀ (hint : String) (named : Bool),
    ReturnsNone (Rec.handleMux (fun e h t n => rec e h t n) e name args hint named) ctx
  memory : ∀ (hint : String) (named : Bool),
    ReturnsNone (Rec.handleMemory (fun e h t n => rec e h t n) e name args hint named) ctx
  loop : ∀ (hint : String) (named : Bool),
    ReturnsNone (Rec.handleLoop (fun e h t n => rec e h t n) e name args hint named) ctx

/-- **The body stage from its walks.** -/
theorem bodyReachesInline_of_walk {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    {name : Name}
    (hpre : ∀ (hint : String) (top named : Bool) (s t : CircuitState) (w : String),
      Returns (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named)
        ctx s w t →
      Returns (Rec.translateExprToWireApp (fun e h t n => rec e h t n) e hint named) ctx s w t)
    (hchain : PlainChain rec ctx e name e.getAppArgs →
      ∀ (hint : String) (named : Bool) (s t : CircuitState) (w : String),
        Returns (Rec.translateExprToWireApp (fun e h t n => rec e h t n) e hint named)
          ctx s w t →
        Returns (Rec.handleDefinitionUnfold (fun e h t n => rec e h t n) e name e.getAppArgs
          hint named) ctx s (some w) t)
    (handlers : PlainChain rec ctx e name e.getAppArgs)
    (hunfold : ∀ (hint : String) (named : Bool) (s t : CircuitState) (w : String),
      Returns (Rec.handleDefinitionUnfold (fun e h t n => rec e h t n) e name e.getAppArgs
        hint named) ctx s (some w) t →
      ∃ r : Option String × Option Exception,
        Returns (Rec.tryInlineUnfold rec e hint named) ctx s r t ∧ r.1 = some w) :
    BodyReachesInline rec ctx e := by
  intro hint top named s t w hr
  exact hunfold hint named s t w (hchain handlers hint named s t w (hpre hint top named s t w hr))

end Tools.ShippingLegacySem

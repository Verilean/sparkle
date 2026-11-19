/-
  The helper Signal/Circuit functions a declaration calls (a nested `circuit do` such as
  `arpRxParser`): they inline on the IR side but stay FOLDED on the Signal side unless a proof
  unfolds them.  Shared by `#verify_elab_deep` (its top-level unfold) and the hierarchical checker
  (which meets the same folded calls in the declaration's argument terms).
-/
import Lean
import Sparkle.Core.Signal
open Lean

namespace Tools.DeepHelpers

/-- The transitive Signal/Circuit-typed (or closed `BitVec`) definitions `declName` uses outside the core
namespaces, in discovery order, `declName` itself excluded. -/
def helperConsts (env : Environment) (declName : Name) : Array Name :=
  let isCore (n : Name) : Bool :=
    -- keep the Sparkle core/compiler namespaces and the stdlib out;
    -- user circuits stay (IP.*, Tests.*, and anything else a design
    -- defines — a helper circuit under `Sparkle.Tests` is a helper)
    let base := (privateToUserName? n).getD n
    let r := base.getRoot
    r == `Init || r == `Lean || r == `Std
      || r == `Nat || r == `BitVec || r == `List || r == `Tools
      || (`Sparkle.Core).isPrefixOf base
      || (`Sparkle.IR).isPrefixOf base
      || (`Sparkle.Compiler).isPrefixOf base
      || (`Sparkle.Backend).isPrefixOf base
  let mentionsSignal (e : Expr) : Bool :=
    Option.isSome <| e.find? fun x =>
      match x with
      | .const n _ =>
        n == ``Sparkle.Core.Signal.Signal
        || n.eraseMacroScopes.components.contains `Circuit
      | _ => false
  let rec go (fuel : Nat) (work : List Name) (seen : List Name) (acc : Array Name) : Array Name :=
    match fuel, work with
    | 0, _ | _, [] => acc
    | fuel + 1, c :: rest =>
      if seen.contains c then go fuel rest seen acc else
      let seen := c :: seen
      -- hygiene suffixes (`._@._internal…`) name compiler-internal
      -- twins; the simp-facing constant is the scope-erased one
      let c := c.eraseMacroScopes
      if (Lean.Meta.Match.Extension.getMatcherInfo? env c).isSome
      then go fuel rest seen acc else
      match env.find? c with
      | some (.defnInfo v) =>
        -- closed BitVec constants (`private abbrev poly : BitVec 32
        -- := …`) ride along: the shallow side carries the literal,
        -- and bv_decide treats an un-unfolded constant as an atom
        let isBvConst := v.type.isAppOf ``BitVec
        if !isCore c && (mentionsSignal v.type || isBvConst) then
          let deps := v.value.getUsedConstants.toList
          go fuel (deps ++ rest) seen (acc.push c)
        else go fuel rest seen acc
      | _ => go fuel rest seen acc
  match env.find? declName with
  | some ci =>
    let deps := (ci.value?.getD ci.type).getUsedConstants.toList
    go 512 deps [declName] #[]
  | none => #[]

end Tools.DeepHelpers

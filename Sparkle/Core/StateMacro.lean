/-
  StateMacro — `declare_signal_state` command macro

  Generates synthesis-compatible state type aliases, accessor defs,
  default values, and Inhabited instances from a field list.

  Each accessor is a regular `def` (.defnInfo), so the synthesis compiler's
  `unfoldDefinition?` can inline it to `projN!` (→ Signal.fst/snd chains).
  No struct constructors appear in the synthesis path.
-/

import Lean
import Sparkle.Core.Signal

namespace Sparkle.Core.StateMacro

open Lean Elab Command

syntax signalStateField := "| " ident " : " term " := " term

/-- `declare_signal_state` generates a synthesis-compatible state type alias,
    accessor defs, default value, and `Inhabited` instance from a field list.

    Example:
    ```
    declare_signal_state BottleneckState
      | fsmReg      : BitVec 2   := 0#2
      | residualReg : BitVec 8   := 0#8
      | resultReg   : BitVec 8   := 0#8
      | doneReg     : Bool       := false
    ```
    Generates:
    - `abbrev BottleneckState := BitVec 2 × BitVec 8 × BitVec 8 × Bool`
    - `BottleneckState.fsmReg`, `.residualReg`, etc. accessor defs using `projN!`
    - `BottleneckState.default : BottleneckState`
    - `instance : Inhabited BottleneckState` -/
elab "declare_signal_state " name:ident fields:signalStateField* : command => do
  -- Parse fields into (name, type, default) triples
  let fieldData := fields.map fun f =>
    let args := f.raw.getArgs
    ((⟨args[1]!⟩ : TSyntax `ident), (⟨args[3]!⟩ : TSyntax `term), (⟨args[5]!⟩ : TSyntax `term))
  let n := fieldData.size
  if n == 0 then throwError "declare_signal_state: need at least one field"

  -- 1. Build right-nested tuple type: T0 × T1 × ... × Tn-1
  let mut tupleType : TSyntax `term := fieldData[n-1]!.2.1
  for i in (List.range (n - 1)).reverse do
    let ty := fieldData[i]!.2.1
    tupleType ← `($ty × $tupleType)
  elabCommand (← `(abbrev $name := $tupleType))

  -- 2. Generate accessor defs in namespace
  let nLit : TSyntax `num := ⟨Syntax.mkNumLit (toString n)⟩
  elabCommand (← `(namespace $name))
  for i in [:n] do
    let (fieldName, fieldType, _) := fieldData[i]!
    let iLit : TSyntax `num := ⟨Syntax.mkNumLit (toString i)⟩
    elabCommand (← `(
      def $fieldName {dom : Sparkle.Core.Domain.DomainConfig}
        (s : Sparkle.Core.Signal.Signal dom $name)
        : Sparkle.Core.Signal.Signal dom $fieldType :=
        projN! s $nLit $iLit))
  elabCommand (← `(end $name))

  -- 3. Build right-nested default tuple: (v0, (v1, (... vn-1)))
  let mut defaultTuple : TSyntax `term := fieldData[n-1]!.2.2
  for i in (List.range (n - 1)).reverse do
    let defVal := fieldData[i]!.2.2
    defaultTuple ← `(($defVal, $defaultTuple))
  let defaultName := mkIdent (name.getId ++ `default)
  elabCommand (← `(def $defaultName : $name := $defaultTuple))

  -- 4. Inhabited instance
  elabCommand (← `(instance : Inhabited $name := ⟨$defaultName⟩))

  -- 5. Generate wireNames: Array String of "_gen_fieldName" for each field
  let wireNameLits : Array (TSyntax `term) := fieldData.map fun (fieldName, _, _) =>
    let wireName := s!"_gen_{fieldName.getId}"
    ⟨Syntax.mkStrLit wireName⟩
  let wireNamesArray ← `(#[$[$wireNameLits],*])
  let wireNamesName := mkIdent (name.getId ++ `wireNames)
  elabCommand (← `(def $wireNamesName : Array String := $wireNamesArray))

  -- 6. Generate fromWires: Array UInt32 → Name
  --    Converts raw UInt32 wire values back to BitVec n / Bool
  --    by pattern-matching on the field type.
  --    Builds a right-nested tuple: (conv ws[0], (conv ws[1], ... conv ws[n-1]))
  --    where conv is .toNat for Bool, BitVec.ofNat n for BitVec n
  let wsIdent := mkIdent `ws
  let mkWireConv (fieldType : TSyntax `term) (idxLit : TSyntax `num) : CommandElabM (TSyntax `term) := do
    let fieldTypeStr := fieldType.raw.getId.toString
    if fieldTypeStr == "Bool" then
      `(($wsIdent[$idxLit]!.toNat != 0 : Bool))
    else
      `((BitVec.ofNat _ $wsIdent[$idxLit]!.toNat : $fieldType))
  let lastIdxLit : TSyntax `num := ⟨Syntax.mkNumLit (toString (n - 1))⟩
  let mut fromWiresBody : TSyntax `term ← mkWireConv fieldData[n-1]!.2.1 lastIdxLit
  for i in (List.range (n - 1)).reverse do
    let (_, fieldType, _) := fieldData[i]!
    let idxLit : TSyntax `num := ⟨Syntax.mkNumLit (toString i)⟩
    let elem ← mkWireConv fieldType idxLit
    fromWiresBody ← `(($elem, $fromWiresBody))
  let fromWiresName := mkIdent (name.getId ++ `fromWires)
  elabCommand (← `(def $fromWiresName ($wsIdent : Array UInt32) : $name := $fromWiresBody))

  -- 7. Generate Name.mk: a named-field constructor that takes one
  --    Signal per field and packages them via bundle2 in the right
  --    order. This makes the OUTPUT side of a Sparkle module
  --    symmetric to the INPUT side (`Name.field state` for read,
  --    `Name.mk (field := sig) ...` for write).
  --
  --    Generated signature:
  --      def Name.mk {dom : DomainConfig}
  --        (field0 : Signal dom T0) ... (fieldN-1 : Signal dom Tn-1)
  --        : Signal dom Name :=
  --        bundleAll! [field0, ..., fieldN-1]
  --
  --    Callers can use named arguments:
  --      Name.mk (count := countOut) (parity := parityOut)
  --
  -- Implemented via a `fun`-binding form so we don't need raw
  -- bracketedBinder Syntax: the macro emits
  --   def Name.mk : ... := fun field0 ... fieldN-1 => bundleBody
  -- with explicit type annotations on each binder.
  let bundleArgs : Array (TSyntax `term) := fieldData.map fun (fieldName, _, _) =>
    ⟨fieldName.raw⟩
  let bundleBody : TSyntax `term ←
    if n == 1 then
      pure bundleArgs[0]!
    else
      let mut acc : TSyntax `term := bundleArgs[n-1]!
      for i in (List.range (n - 1)).reverse do
        acc ← `(Sparkle.Core.Signal.bundle2 $(bundleArgs[i]!) $acc)
      pure acc
  -- Build the full type of `mk`: (f0 : Signal dom T0) → ... → Signal dom Name.
  let mut mkType : TSyntax `term ← `(Sparkle.Core.Signal.Signal dom $name)
  for i in (List.range n).reverse do
    let (fieldName, fieldType, _) := fieldData[i]!
    mkType ← `(($fieldName : Sparkle.Core.Signal.Signal dom $fieldType) → $mkType)
  -- Build the body lambda: fun f0 ... fN-1 => bundle.
  let mut mkBody : TSyntax `term := bundleBody
  for i in (List.range n).reverse do
    let (fieldName, _, _) := fieldData[i]!
    mkBody ← `(fun $fieldName => $mkBody)
  let mkName := mkIdent (name.getId ++ `mk)
  elabCommand (← `(
    def $mkName {dom : Sparkle.Core.Domain.DomainConfig} : $mkType := $mkBody))

end Sparkle.Core.StateMacro

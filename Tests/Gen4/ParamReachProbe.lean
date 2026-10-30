import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.IR.Specialize

/-!
# Reach probe (issue sparkle-gen4-parametric-supply, M4 parametric, g4par-r8)

Runs the EXISTING compiler (`synthesizeCombinationalWithParameters`, unchanged) on declarations whose retained
`Nat` parameter appears under `-`, `/`, `%`, `+`, `min`, and then runs the EXISTING
`Sparkle.IR.Specialize.specializeDesign` at positive bindings. The output is printed at build time with `#eval`
(nothing is written into the source tree). Reading: `ok` = specializeDesign returned `.ok`; `err(...)` = it
returned `.error`. A single `ok`/`err` is an observation of one binding, not a statement for other bindings.
This file proves nothing; it is an observation, and it is not part of any guarantee.
-/

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Lean Meta

namespace Sparkle.Gen4.ReachProbe

def pSubOut {dom : DomainConfig} {W : Nat} (x : Signal dom (BitVec W)) : Signal dom (BitVec (W - 1)) :=
  x.map (BitVec.extractLsb' 0 (W - 1) ·)

def pSubIn {dom : DomainConfig} {W : Nat} (x : Signal dom (BitVec (W - 1))) : Signal dom (BitVec (W - 1)) :=
  x

def pDivOut {dom : DomainConfig} {W : Nat} (x : Signal dom (BitVec W)) : Signal dom (BitVec (W / 2)) :=
  x.map (BitVec.extractLsb' 0 (W / 2) ·)

def pModOut {dom : DomainConfig} {W : Nat} (x : Signal dom (BitVec W)) : Signal dom (BitVec (W % 4)) :=
  x.map (BitVec.extractLsb' 0 (W % 4) ·)

def pAddOut {dom : DomainConfig} {W : Nat} (x : Signal dom (BitVec W)) : Signal dom (BitVec (W + 1)) :=
  x.map (·.zeroExtend (W + 1))

def pAddSubOut {dom : DomainConfig} {W : Nat} (x : Signal dom (BitVec (W + 1))) :
    Signal dom (BitVec ((W + 1) - 1)) :=
  x.map (BitVec.extractLsb' 0 ((W + 1) - 1) ·)

def pDivDom {dom : DomainConfig} {W : Nat} (x : Signal dom (BitVec (W + 4))) :
    Signal dom (BitVec ((W + 4) / 2)) :=
  x.map (BitVec.extractLsb' 0 ((W + 4) / 2) ·)

def pMinOut {dom : DomainConfig} {W : Nat} (x : Signal dom (BitVec W)) : Signal dom (BitVec (min W 8)) :=
  x.map (BitVec.extractLsb' 0 (min W 8) ·)

def pSubTwo {dom : DomainConfig} {W : Nat} (x : Signal dom (BitVec W)) : Signal dom (BitVec (W - 2)) :=
  x.map (BitVec.extractLsb' 0 (W - 2) ·)

def pSubDiff {dom : DomainConfig} {W : Nat} (x : Signal dom (BitVec (W + 8))) :
    Signal dom (BitVec ((W + 8) - W)) :=
  x.map (BitVec.extractLsb' 0 ((W + 8) - W) ·)

open Sparkle.Compiler.Elab in
def probe (decl : Name) (vals : List Nat) : MetaM Unit := do
  let r : Except String (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) ←
    try
      let md ← synthesizeCombinationalWithParameters decl [("W", 8)]
      pure (Except.ok md)
    catch ex => pure (Except.error (← ex.toMessageData.toString))
  match r with
  | .error msg => logInfo m!"{decl}: SYNTH FAILED (compile-time throw, nothing to specialize): {msg}"
  | .ok (m, d) =>
    let design := if d.modules.any (·.name == m.name) then { d with topModule := m.name }
                  else { (d.addModule m) with topModule := m.name }
    let mut out := ""
    for v in vals do
      match Sparkle.IR.Specialize.specializeDesign design [("W", v)] with
      | .ok _ => out := out ++ s!" W={v}:ok"
      | .error e => out := out ++ s!" W={v}:err({e})"
    let tys := m.inputs.map (·.ty.toString) ++ m.outputs.map (·.ty.toString)
    logInfo m!"{decl} [{tys}]{out}"

#eval show MetaM Unit from do
  for n in [``pSubOut, ``pSubIn, ``pDivOut, ``pModOut, ``pAddOut, ``pAddSubOut, ``pDivDom, ``pMinOut,
            ``pSubTwo, ``pSubDiff] do
    probe n [1, 2, 3, 4, 5, 8, 9, 16]

end Sparkle.Gen4.ReachProbe

import Sparkle.Backend.Verilog
import Sparkle.IR.RegDedup

/-! Executable sufficient conditions for the uniform-width combinational
printing fragment. No proof-only `Tools` module is imported here. This is not
a lexical validity check or a general SystemVerilog checker. -/
namespace Sparkle.IR.PrintCheck
open Sparkle.IR.AST Sparkle.IR.Semantics

def widths (m : Module) (x : String) : Option Nat :=
  ((m.wires ++ m.inputs ++ m.outputs).find? fun p =>
    Sparkle.Backend.Verilog.sanitizeName p.name == x).bind fun p =>
      match p.ty with
      | .bitVector n => some n
      | .bit => some 1
      | _ => none

def exprCheck (m : Module) (n : Nat) : Expr → Bool
  | .ref x =>
    Sparkle.Backend.Verilog.sanitizeName x == x &&
      widths m x == some n && Sparkle.IR.RegDedup.declWidth m x == n
  | .const _ k => k == n
  | .op op [a, b] =>
    (match op with | .add | .sub | .mul | .and | .or | .xor => true | _ => false) &&
      exprCheck m n a && exprCheck m n b
  | _ => false

def moduleCheck (m : Module) : Bool :=
  m.body.all fun st => match st with
    | .assign l r =>
      match widths m l with
      | some n => Sparkle.Backend.Verilog.sanitizeName l == l &&
          (0 < n) && exprCheck m n r
      | none => false
    | _ => false

end Sparkle.IR.PrintCheck

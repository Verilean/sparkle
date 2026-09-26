import Tools.SVParser.AST
import Sparkle.IR.ModuleNames

/-! A concrete combinational SystemVerilog subset grammar. Productions
relate source characters to the AST they denote. This specification imports
neither the IR emitter nor the auxiliary AST renderer or in-tree parser.
It deliberately covers only unsigned ANSI logic ports, logic declarations,
continuous assignments and the binary operators used by the source proof.
It is not a claim about all IEEE syntax or any external parser implementation.
-/
namespace Tools.SVParser.ConcreteSyntax
open Tools.SVParser.AST

/-- Nonempty positional numerals, with their mathematical value. Restricting
`base` to 10 or 16 at use sites gives decimal or hexadecimal digit tokens. -/
inductive Numeral (base : Nat) : Nat → String → Prop
  | digit {d} : d < base → Numeral base d (String.singleton (Nat.digitChar d))
  | snoc {n s d} : Numeral base n s → d < base →
      Numeral base (base * n + d) (s ++ String.singleton (Nat.digitChar d))

abbrev Identifier (s : String) : Prop := Sparkle.IR.ModuleNames.legal s = true

abbrev Whitespace (s : String) : Prop :=
  ∀ c ∈ s.toList, c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r'

inductive BinaryToken : SVBinOp → String → Prop
  | add : BinaryToken .add "+"
  | sub : BinaryToken .sub "-"
  | mul : BinaryToken .mul "*"
  | bitAnd : BinaryToken .bitAnd "&"
  | bitOr : BinaryToken .bitOr "|"
  | bitXor : BinaryToken .bitXor "^"
  | shr : BinaryToken .shr ">>"

inductive Expression : SVExpr → String → Prop
  | decimal {w v sw sv} : 0 < w → Numeral 10 w sw → Numeral 10 v sv →
      Expression (.lit (.decimal (some w) v)) (sw ++ "'d" ++ sv)
  | hex {w v sw sv} : 0 < w → Numeral 10 w sw → Numeral 16 v sv →
      Expression (.lit (.hex (some w) v)) (sw ++ "'h" ++ sv)
  | ident {name} : Identifier name → Expression (.ident name) name
  | binary {op a b tok sa sb} : BinaryToken op tok → Expression a sa → Expression b sb →
      Expression (.binary op a b) ("(" ++ sa ++ " " ++ tok ++ " " ++ sb ++ ")")

inductive LogicType : Option (Nat × Nat) → String → Prop
  | scalar : LogicType none "logic"
  | packed {hi lo sh sl} : Numeral 10 hi sh → Numeral 10 lo sl →
      LogicType (some (hi, lo)) ("logic [" ++ sh ++ ":" ++ sl ++ "]")

inductive Port : SVPort → String → Prop
  | input {name w ty} : Identifier name → LogicType w ty →
      Port {dir := .input, name, width := w}
        ("input " ++ ty ++ " " ++ name)
  | output {name w ty} : Identifier name → LogicType w ty →
      Port {dir := .output, name, width := w}
        ("output " ++ ty ++ " " ++ name)

/-- Whitespace can be added around a phrase without changing its AST. -/
inductive Padded {α : Type} (phrase : α → String → Prop) : α → String → Prop
  | mk {a s left right} : Whitespace left → phrase a s → Whitespace right →
      Padded phrase a (left ++ s ++ right)

/-- Comma-separated ANSI port declarations; the comma is mandatory. -/
inductive Ports : List SVPort → String → Prop
  | nil : Ports [] ""
  | one {p s} : Padded Port p s → Ports [p] s
  | cons {p ps s tail} : Padded Port p s → Ports ps tail → ps ≠ [] →
      Ports (p :: ps) (s ++ "," ++ tail)
  | pad {ports s left right} : Whitespace left → Ports ports s → Whitespace right →
      Ports ports (left ++ s ++ right)

inductive Item : SVModuleItem → String → Prop
  | wire {name w ty} : Identifier name → LogicType w ty →
      Item (.wireDecl name w none) (ty ++ " " ++ name ++ ";")
  | assign {name rhs s} : Identifier name → Expression rhs s →
      Item (.contAssign (.ident name) rhs) ("assign " ++ name ++ " = " ++ s ++ ";")

inductive Items : List SVModuleItem → String → Prop
  | nil : Items [] ""
  | cons {item rest s tail} : Padded Item item s → Items rest tail →
      Items (item :: rest) (s ++ tail)
  | pad {items s left right} : Whitespace left → Items items s → Whitespace right →
      Items items (left ++ s ++ right)

/-- A line comment ends only at its explicit newline. CR is excluded too. -/
inductive Comments : String → Prop
  | nil : Comments ""
  | line {label rest} : (∀ c ∈ label.toList, c ≠ '\n' ∧ c ≠ '\r') →
      Comments rest → Comments ("//" ++ label ++ "\n" ++ rest)
  | pad {s left right} : Whitespace left → Comments s → Whitespace right →
      Comments (left ++ s ++ right)

/-- Complete translation unit for one module, with no trailing unparsed text.
Token boundaries are explicit: spaces separate keyword/name tokens; all other
boundaries are punctuation, whitespace, or newline-terminated comments. -/
inductive Module : SVModule → String → Prop
  | module {name ports items comment ps body beforePorts afterPorts afterHeader afterEnd} :
      Identifier name → Comments comment → Ports ports ps → Items items body →
      Whitespace beforePorts → Whitespace afterPorts → Whitespace afterHeader →
      Whitespace afterEnd →
      Module {name, params := [], ports, items}
        (comment ++ "module " ++ name ++ " (" ++ beforePorts ++ ps ++ afterPorts ++
          ");" ++ afterHeader ++ body ++ "endmodule" ++ afterEnd)

/-- A general numeral theorem: this is not a bounded enumeration of examples. -/
theorem numeral_toDigits {base : Nat} (hb : 1 < base) (n : Nat) :
    Numeral base n (String.ofList (Nat.toDigits base n)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_if hb]
    split
    · rename_i hn
      simpa only [String.singleton_eq_ofList] using (Numeral.digit hn)
    · rename_i hn
      have hd : n / base < n := Nat.div_lt_self (by omega) hb
      have hv : base * (n / base) + n % base = n := Nat.div_add_mod n base
      simpa only [String.ofList_append, ← String.singleton_eq_ofList, hv] using
        (Numeral.snoc (ih _ hd) (Nat.mod_lt n (by omega)))

theorem numeral_decimal (n : Nat) : Numeral 10 n (toString n) := by
  rw [Nat.toString_eq_ofList_toDigits]
  exact numeral_toDigits (by decide) n

end Tools.SVParser.ConcreteSyntax

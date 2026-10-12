import Tools.ShippingNameSep

/-! # Name separation, structural test: does the kernel decide it cheaply? (N1)

`Tools.ShippingNameSep.sepC` / `hnames_of'` work on the CHARACTERS of the
components (last component first) and never build a string. This file
measures what the candidate test (`NameSepTest`, `sepB`) is expensive at:
the same five-component pair, and the list forms.

Each `example` is one kernel-checked use; they are ordered so that the
first failure tells what does not evaluate:
1. a name literal is `nameOf` of its characters, by `rfl` (the string
   literals unfold to `String.ofList`);
2. `sepC` by `decide` on the five-component pair;
3. the list forms, stated over `List.map nameOf` and used at a list of name
   literals (the kernel must identify the two lists);
4. `sepFast` on the literals themselves (through `String.toList`): the
   variant whose kernel cost is the least certain — LAST, so that its
   failure or cost does not hide the others.

The `#eval` lines are compiled evidence only (prefixed `NAMESEPFAST`),
including two pairs `sepFast` refuses and `sepB` separates. -/
namespace Tests.Compiler.NameSepFastTest
open Tools.ShippingNameSep

def parentC : CN :=
  [['p', 'a', 'r', 'e', 'n', 't'],
  ['S', 'h', 'i', 'p', 'p', 'i', 'n', 'g', 'M', 'a', 'c', 'h', 'i', 'n', 'e', 'S', 'e', 'q', 'T', 'e', 's', 't'],
  ['C', 'o', 'm', 'p', 'i', 'l', 'e', 'r'],
  ['T', 'e', 's', 't', 's'],
  ['S', 'p', 'a', 'r', 'k', 'l', 'e']]

def cntC : CN :=
  [['c', 'n', 't'],
  ['S', 'h', 'i', 'p', 'p', 'i', 'n', 'g', 'M', 'a', 'c', 'h', 'i', 'n', 'e', 'S', 'e', 'q', 'T', 'e', 's', 't'],
  ['C', 'o', 'm', 'p', 'i', 'l', 'e', 'r'],
  ['T', 'e', 's', 't', 's'],
  ['S', 'p', 'a', 'r', 'k', 'l', 'e']]

def pickC : CN :=
  [['p', 'i', 'c', 'k'],
  ['S', 'h', 'i', 'p', 'p', 'i', 'n', 'g', 'M', 'a', 'c', 'h', 'i', 'n', 'e', 'S', 'e', 'q', 'T', 'e', 's', 't'],
  ['C', 'o', 'm', 'p', 'i', 'l', 'e', 'r'],
  ['T', 'e', 's', 't', 's'],
  ['S', 'p', 'a', 'r', 'k', 'l', 'e']]

#eval IO.println s!"NAMESEPFAST nameOf parentC = {nameOf parentC}"
#eval IO.println s!"NAMESEPFAST sepC parent cnt = {sepC parentC cntC}, same = {sepC cntC cntC}"
#eval IO.println s!"NAMESEPFAST sepFast parent cnt = {sepFast `Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent `Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt}"
#eval IO.println s!"NAMESEPFAST numeric component: sepFast = {sepFast (Lean.Name.mkNum `a 1) `b}, sepB = {sepB (Lean.Name.mkNum `a 1) `b}"
#eval IO.println s!"NAMESEPFAST dotted component: sepFast = {sepFast (Lean.Name.mkStr (Lean.Name.mkSimple "a.b") "c") `d}, sepB = {sepB (Lean.Name.mkStr (Lean.Name.mkSimple "a.b") "c") `d}"

-- 1. the literal is the name of its characters
example : nameOf cntC = `Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt := rfl

-- 2. the five-component pair, structurally
example : (nameOf parentC).toString ≠ (nameOf cntC).toString :=
  sepC_ne (by decide)

-- 2'. the same, stated on the literals
example : (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent : Lean.Name).toString ≠
    (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt : Lean.Name).toString :=
  sepC_ne (A := parentC) (B := cntC) (by decide)

-- 3. `hnames` on a list of literals: the check is `L.all okC`
example : ∀ c ∈ [(`Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt : Lean.Name),
      `Sparkle.Tests.Compiler.ShippingMachineSeqTest.pick],
    ∀ c' ∈ [(`Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt : Lean.Name),
      `Sparkle.Tests.Compiler.ShippingMachineSeqTest.pick],
    c.toString = c'.toString → c = c' :=
  hnames_of' [cntC, pickC] (by decide)

-- 3'. `hparent` on a list of literals
example : ∀ c ∈ [((`Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt : Lean.Name), (0 : Nat)),
      (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.pick, 1)],
    c.1.toString ≠ (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent : Lean.Name).toString :=
  hparent_of' [(cntC, (0 : Nat)), (pickC, 1)] parentC (by decide)

-- 4. on the literals themselves, through `String.toList`
example : (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent : Lean.Name).toString ≠
    (`Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt : Lean.Name).toString :=
  sepFast_ne (by decide)

end Tests.Compiler.NameSepFastTest

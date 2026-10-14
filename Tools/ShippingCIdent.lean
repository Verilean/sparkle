import Sparkle.Backend.CIdent

/-! # The C identifiers of the C backend: injectivity and the reserved head

`Sparkle.Backend.CIdent.cIdent role m = "sparkle_" ++ code role ++ "_" ++ m`
(findings J2–J4 of `docs/parallel/J-tagged-names.md`).

Proved here, for ALL strings `m` (not only compiler-made module names):

* `cIdent_injective` — `cIdent r m = cIdent r' m'` only if `r = r'` and
  `m = m'`. So no two (role, module) pairs share an identifier: the old
  `sparkle_X_eval_tick` of both `X` (eval_tick) and `X_eval` (tick) cannot
  recur, and a struct tag is never a function name.
* `cIdentL_hasHead` — every identifier starts with `sparkle_m`.
* `cIdent_ne_of_no_head` — an identifier never equals a string that does not
  start with `sparkle_m`. Which FIXED names of the backend that covers is a
  grid of `#guard`s (`Tests/Compiler/CIdentTest.lean`, over
  `CIdent.fixedNames`: the trampolines `sparkle_jit_*`, `jit_vtable`,
  `main`, the C library names the text uses, the C and C++ keywords): the
  link from the `#guard` (`String.startsWith`, compiled) to `HasHead` (a
  proposition about `toList`) is by reading, not by a theorem.

Not here: stability under `CSim.sanitizeName` (a `#guard` grid in the same
test); anything about the C text around the identifiers.

WRITTEN, NOT BUILT. -/
namespace Tools.ShippingCIdent
open Sparkle.Backend.CIdent

theorem code_length (r : Role) : r.code.length = 2 := by
  cases r <;> rfl

/-- The codes of two different roles differ. -/
theorem code_injective {r r' : Role} (h : r.code = r'.code) : r = r' := by
  cases r <;> cases r' <;> first | rfl | exact absurd h (by decide)

/-- **Injective on characters**: the role and the module name are read back
from the identifier. -/
theorem cIdentL_injective {r r' : Role} {m m' : List Char}
    (h : cIdentL r m = cIdentL r' m') : r = r' ∧ m = m' := by
  have h0 : prefixL ++ (r.code ++ ('_' :: m)) = prefixL ++ (r'.code ++ ('_' :: m')) := h
  have h1 : r.code ++ ('_' :: m) = r'.code ++ ('_' :: m') := List.append_cancel_left h0
  have hl : r.code.length = r'.code.length := (code_length r).trans (code_length r').symm
  have h2 : r.code = r'.code ∧ '_' :: m = '_' :: m' := List.append_inj h1 hl
  exact ⟨code_injective h2.1, (List.cons.inj h2.2).2⟩

/-- **The C identifier is injective in (role, module name)**, for all
strings. -/
theorem cIdent_injective {r r' : Role} {m m' : String}
    (h : cIdent r m = cIdent r' m') : r = r' ∧ m = m' := by
  have h1 : (String.ofList (cIdentL r m.toList)).toList =
      (String.ofList (cIdentL r' m'.toList)).toList := congrArg String.toList h
  rw [String.toList_ofList, String.toList_ofList] at h1
  have h2 : r = r' ∧ m.toList = m'.toList := cIdentL_injective h1
  have h3 : String.ofList m.toList = String.ofList m'.toList := congrArg String.ofList h2.2
  rw [String.ofList_toList, String.ofList_toList] at h3
  exact ⟨h2.1, h3⟩

/-- Two roles of one module never share an identifier (the struct tag is not
a function name; `eval` is not `eval_tick`). -/
theorem cIdent_role_ne {r r' : Role} (m m' : String) (h : r ≠ r') :
    cIdent r m ≠ cIdent r' m' :=
  fun e => h (cIdent_injective e).1

/-- Two modules never share an identifier of any role. -/
theorem cIdent_module_ne (r r' : Role) {m m' : String} (h : m ≠ m') :
    cIdent r m ≠ cIdent r' m' :=
  fun e => h (cIdent_injective e).2

/-- `l` starts with `sparkle_m`. -/
abbrev HasHead (l : List Char) : Prop :=
  ∃ t, l = 's' :: 'p' :: 'a' :: 'r' :: 'k' :: 'l' :: 'e' :: '_' :: 'm' :: t

/-- **Every identifier starts with `sparkle_m`.** -/
theorem cIdentL_hasHead (r : Role) (m : List Char) : HasHead (cIdentL r m) := by
  cases r <;> exact ⟨_, rfl⟩

/-- **An identifier never equals a string that does not start with
`sparkle_m`** — a keyword, `main`, a C library name, a `sparkle_jit_*`
trampoline, `jit_vtable`. -/
theorem cIdent_ne_of_no_head (r : Role) (m : String) {f : String}
    (hf : ¬ HasHead f.toList) : cIdent r m ≠ f := by
  intro e
  apply hf
  have h1 : (String.ofList (cIdentL r m.toList)).toList = f.toList := congrArg String.toList e
  rw [String.toList_ofList] at h1
  rw [← h1]
  exact cIdentL_hasHead r m.toList

end Tools.ShippingCIdent

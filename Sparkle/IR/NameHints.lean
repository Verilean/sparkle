import Sparkle.IR.FreshNames

/-! Characters allowed in allocated wire names. Normalization is deliberately
not injective: it must run BEFORE fresh-name allocation. The allocator, not
the character replacement, prevents collisions. Leading characters and
keywords are handled by the allocator's `_gen_` / `_tmp_` prefixes; this file
does not claim a lexical contract for arbitrary module or port names. -/
namespace Sparkle.IR.NameHints

def charOk (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'

def Clean (s : String) : Prop := ∀ c ∈ s.toList, charOk c = true

/-- Stronger than sanitizer stability: allocated names start with underscore.
This does not impose a lexical policy on arbitrary module names. -/
def Allocated (s : String) : Prop := Clean s ∧ s.toList.head? = some '_'

/-- The naming class of emitted data declarations: allocated names or the
fixed output name. This is not a specification of the complete SV lexer. -/
def DataName (s : String) : Prop := Allocated s ∨ s = "out"

/-- Keep existing ASCII identifier characters; normalize all others before
allocation. The fast path avoids copying the usual already-clean hint. -/
def clean (s : String) : String :=
  if s.all charOk then s else s.map fun c => if charOk c then c else '_'

theorem clean_ok (s : String) : Clean (clean s) := by
  unfold clean
  split
  · rename_i h
    simpa [Clean, String.all_bool_eq] using h
  · intro c hc
    simp only [String.toList_map, List.mem_map] at hc
    obtain ⟨a, _, rfl⟩ := hc
    split <;> simp_all [charOk]

theorem Clean.append {a b : String} (ha : Clean a) (hb : Clean b) : Clean (a ++ b) := by
  intro c hc
  simp only [String.toList_append, List.mem_append] at hc
  exact hc.elim (ha c) (hb c)

theorem digits (n : Nat) : Clean (toString n) := by
  intro c hc
  simp only [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hc
  have hd := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) hc
  simp [charOk, Char.isAlphanum, hd]

theorem numbered {a : String} (ha : Clean a) (n : Nat) :
    Clean (FreshNames.numbered a n) :=
  (ha.append (by simp [Clean, charOk])).append (digits n)

end Sparkle.IR.NameHints

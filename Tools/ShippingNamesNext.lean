import Tools.ShippingNamesStable

/-! # The next-value wires are sanitize-stable (G1, `designCheck` gap A)

`nextName s = "next" ++ s`: clean when `s` is, hence sanitize-stable for an
allocated slot name. Kept in a file of its own: the proof of
`clean_nextName` evaluates the characters of the literal `"next"`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingNamesNext
open Sparkle.IR.NameHints (Allocated Clean charOk)

/-- The next-value wire of a clean name is clean. -/
theorem clean_nextName {s : String} (h : Clean s) : Clean (Sparkle.IR.Machine.nextName s) := by
  intro c hc
  have h0 : (Sparkle.IR.Machine.nextName s).toList = "next".toList ++ s.toList := by
    unfold Sparkle.IR.Machine.nextName
    rw [String.toList_append]
  rw [h0] at hc
  rcases List.mem_append.mp hc with h1 | h1
  · have h2 : c = 'n' ∨ c = 'e' ∨ c = 'x' ∨ c = 't' := by simpa using h1
    rcases h2 with e | e | e | e <;> rw [e] <;> decide
  · exact h c h1

/-- The next-value wire of an allocated slot is sanitize-stable. -/
theorem sanitizeName_nextName {s : String} (h : Allocated s) :
    Sparkle.Backend.Verilog.sanitizeName (Sparkle.IR.Machine.nextName s) =
      Sparkle.IR.Machine.nextName s :=
  Tools.ShippingSVBridge.sanitizeName_of_clean (clean_nextName h.1)

end Tools.ShippingNamesNext

/-
  Hardware Vector Type

  Fixed-size vectors for hardware synthesis.
  Unlike Lean's dynamic Array type, HWVector has a compile-time known size.
-/

namespace Sparkle.Core.Vector

/--
  Hardware vector with compile-time known size.

  This is a wrapper around an array that carries its size in the type,
  making it suitable for hardware synthesis.
-/
structure HWVector (α : Type) (n : Nat) where
  data : Array α
  size_eq : data.size = n

namespace HWVector

/-- Create a vector from an array (checks size at runtime) -/
def ofArray {α : Type} {n : Nat} (arr : Array α) (h : arr.size = n := by rfl) : HWVector α n :=
  ⟨arr, h⟩

/-- Get element at index i -/
def get {α : Type} {n : Nat} (v : HWVector α n) (i : Fin n) : α :=
  v.data[i.val]'(by rw [v.size_eq]; exact i.isLt)

/-- Set element at index i -/
def set {α : Type} {n : Nat} (v : HWVector α n) (i : Fin n) (val : α) : HWVector α n :=
  have h : i.val < v.data.size := by rw [v.size_eq]; exact i.isLt
  ⟨v.data.set (Fin.mk i.val h) val, by simp [v.size_eq]⟩

/-- Create a vector by replicating a value -/
def replicate {α : Type} (n : Nat) (val : α) : HWVector α n :=
  ⟨Array.mk (List.replicate n val), by simp⟩

/-- Map a function over all elements -/
def map {α β : Type} {n : Nat} (f : α → β) (v : HWVector α n) : HWVector β n :=
  ⟨v.data.map f, by simp [v.size_eq]⟩

/-- Create vector from list (checks size) -/
def ofList {α : Type} (l : List α) : HWVector α l.length :=
  ⟨Array.mk l, by simp⟩

/-- Convert vector to list -/
def toList {α : Type} {n : Nat} (v : HWVector α n) : List α :=
  v.data.toList

instance {α : Type} {n : Nat} [Repr α] : Repr (HWVector α n) where
  reprPrec v _ := repr v.toList

end HWVector

end Sparkle.Core.Vector

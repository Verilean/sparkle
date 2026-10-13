import Tools.ShippingUnifiedSource

/-! # `noRepeat`: no non-variable subterm of a term occurs twice (a decidable MEASUREMENT)

WRITTEN, NOT BUILT (par/a-40). Definitions only; NOTHING is proved here and
nothing uses these definitions in a proof.

## Why this predicate

`Det c` (two real compiles of `c` return the same module,
`Tools/ShippingDetReduce.lean`) is not derivable from the present laws for
the certified route, for one reason (`docs/parallel/A-determinism.md`, item
B): the translator's validated lookup (`cacheLookupValidated`,
`Sparkle/Compiler/Elab.lean` 8003–8014) reads a run-local `IO.Ref`, and no
law says what that read returns. Whatever it returns, the lookup of an
expression `e` answers `some w` only if the builder's own record holds
`w ↦ e'` with `e' = e` — and the record gets `w ↦ e` only when `e` itself was
lowered earlier by this builder (`recordTranslation`, 8018–8024). A variable
is never looked up and never recorded (`translateStepWith`, 8217, 8226).

So: if no non-variable subterm of the walked term is met twice, EVERY
validated lookup misses, whatever the ref holds, and the walk is a function
of its start state without any law about that ref. `noRepeat` is that
condition on the source term, decided on a sort-erased copy (`Key`):

* `key t`: the term with its sorts erased. A node keeps its constructor, its
  explicit parameters and the widths its quotation mentions
  (`Tools.ShippingUnifiedSource.quote`); a BitVec input keeps its position
  only (its quotation is the variable, whatever the declared width).
* `Key.subs`: every subterm occurrence, children before the node (the order
  in which lowerings complete).
* `noRepeat t`: the non-input occurrences are pairwise different keys.
* `noRepeatNonLit t`: the same, literals left out too — it tells whether the
  repeats of a term are literals only.

`noRepeat` is STRICTER than needed (it counts occurrences the translator
never looks up, e.g. a named or top-level one) and is stated on keys, not on
quotations: "equal quotations have equal keys" is what a proof would need,
and is NOT proved (believed by reading `quote`: every component of a key is
a component of the quotation).

This file is the measurement of option 2 of
`docs/parallel/A-det-decision.md`; it commits to nothing. -/
namespace Tools.ShippingNoRepeat
open Sparkle.Compiler.Elab
open Tools.ShippingUnifiedSource Tools.ShippingScalarSoundness

/-- A term with its sorts erased. -/
inductive Key where
  | boolIn (j : Nat)
  | bitsIn (j : Nat)
  | boolLit (b : Bool)
  | bitsLit (w v : Nat)
  | bitsNum (w v : Nat)
  | binary (op : Binary) (w : Nat) (a b : Key)
  | compare (op : SignalCompareKind) (w : Nat) (a b : Key)
  | boolBinary (op : SignalBoolBinKind) (a b : Key)
  | boolNot (a : Key)
  | boolEq (a b : Key)
  | mux (s : SType) (c a b : Key)
  | setw (w w' : Nat) (a : Key)
  | slice (nm : Lean.Name) (start len w : Nat) (a : Key)
  | concat (m n : Nat) (a b : Key)
  | concatLitHi (k v n : Nat) (b : Key)
  | concatLitLo (m : Nat) (a : Key) (k v : Nat)
  | zextMap (nm : Lean.Name) (k n : Nat) (a : Key)
  | sliceF (nm : Lean.Name) (start len w : Nat) (a : Key)
  | appCompare (op : SignalCompareKind) (w : Nat) (a b : Key)
  | appBool (op : SignalBoolBinKind) (a b : Key)
  | appBool2 (f : AppBool2) (a b : Key)

/-- The sort-erased copy of a term. -/
def key : {s : SType} → Term s → Key
  | _, .boolInput j => .boolIn j
  | _, .bitsInput _ j => .bitsIn j
  | _, .boolLit b => .boolLit b
  | _, .bitsLit w v => .bitsLit w v
  | _, .bitsNum w v => .bitsNum w v
  | _, .binary op (w := w) a b => .binary op w (key a) (key b)
  | _, .compare op (w := w) a b => .compare op w (key a) (key b)
  | _, .boolBinary op a b => .boolBinary op (key a) (key b)
  | _, .boolNot a => .boolNot (key a)
  | _, .boolEq a b => .boolEq (key a) (key b)
  | s, .mux c a b => .mux s (key c) (key a) (key b)
  | _, .setw (w := w) w' a => .setw w w' (key a)
  | _, .slice nm start len (w := w) a => .slice nm start len w (key a)
  | _, .concat (m := m) (n := n) a b => .concat m n (key a) (key b)
  | _, .concatLitHi k v (n := n) b => .concatLitHi k v n (key b)
  | _, .concatLitLo (m := m) a k v => .concatLitLo m (key a) k v
  | _, .zextMap nm k (n := n) a => .zextMap nm k n (key a)
  | _, .sliceF nm start len (w := w) a => .sliceF nm start len w (key a)
  | _, .appCompare op (w := w) a b => .appCompare op w (key a) (key b)
  | _, .appBool op a b => .appBool op (key a) (key b)
  | _, .appBool2 f a b => .appBool2 f (key a) (key b)

/-- Equality of sorts, as a `Bool` by cases (no instance to unfold). -/
def stypeEq : SType → SType → Bool
  | .bool, .bool => true
  | .bits a, .bits b => a == b
  | _, _ => false

/-- Structural equality of keys, as a `Bool` by recursion. -/
def Key.beq : Key → Key → Bool
  | .boolIn j, .boolIn j' => j == j'
  | .bitsIn j, .bitsIn j' => j == j'
  | .boolLit b, .boolLit b' => b == b'
  | .bitsLit w v, .bitsLit w' v' => w == w' && v == v'
  | .bitsNum w v, .bitsNum w' v' => w == w' && v == v'
  | .binary op w a b, .binary op' w' a' b' =>
    decide (op = op') && w == w' && Key.beq a a' && Key.beq b b'
  | .compare op w a b, .compare op' w' a' b' =>
    decide (op = op') && w == w' && Key.beq a a' && Key.beq b b'
  | .boolBinary op a b, .boolBinary op' a' b' =>
    decide (op = op') && Key.beq a a' && Key.beq b b'
  | .boolNot a, .boolNot a' => Key.beq a a'
  | .boolEq a b, .boolEq a' b' => Key.beq a a' && Key.beq b b'
  | .mux s c a b, .mux s' c' a' b' =>
    stypeEq s s' && Key.beq c c' && Key.beq a a' && Key.beq b b'
  | .setw w v a, .setw w' v' a' => w == w' && v == v' && Key.beq a a'
  | .slice nm st ln w a, .slice nm' st' ln' w' a' =>
    nm == nm' && st == st' && ln == ln' && w == w' && Key.beq a a'
  | .concat m n a b, .concat m' n' a' b' =>
    m == m' && n == n' && Key.beq a a' && Key.beq b b'
  | .concatLitHi k v n b, .concatLitHi k' v' n' b' =>
    k == k' && v == v' && n == n' && Key.beq b b'
  | .concatLitLo m a k v, .concatLitLo m' a' k' v' =>
    m == m' && k == k' && v == v' && Key.beq a a'
  | .zextMap nm k n a, .zextMap nm' k' n' a' =>
    nm == nm' && k == k' && n == n' && Key.beq a a'
  | .sliceF nm st ln w a, .sliceF nm' st' ln' w' a' =>
    nm == nm' && st == st' && ln == ln' && w == w' && Key.beq a a'
  | .appCompare op w a b, .appCompare op' w' a' b' =>
    decide (op = op') && w == w' && Key.beq a a' && Key.beq b b'
  | .appBool op a b, .appBool op' a' b' =>
    decide (op = op') && Key.beq a a' && Key.beq b b'
  | .appBool2 f a b, .appBool2 f' a' b' =>
    decide (f = f') && Key.beq a a' && Key.beq b b'
  | _, _ => false

/-- An input: a variable of the walk (never looked up, never recorded). -/
def Key.isInput : Key → Bool
  | .boolIn _ => true
  | .bitsIn _ => true
  | _ => false

/-- A literal leaf. -/
def Key.isLit : Key → Bool
  | .boolLit _ => true
  | .bitsLit _ _ => true
  | .bitsNum _ _ => true
  | _ => false

/-- Every subterm occurrence, children before the node. -/
def Key.subs : Key → List Key
  | .boolIn j => [.boolIn j]
  | .bitsIn j => [.bitsIn j]
  | .boolLit b => [.boolLit b]
  | .bitsLit w v => [.bitsLit w v]
  | .bitsNum w v => [.bitsNum w v]
  | .binary op w a b => a.subs ++ b.subs ++ [.binary op w a b]
  | .compare op w a b => a.subs ++ b.subs ++ [.compare op w a b]
  | .boolBinary op a b => a.subs ++ b.subs ++ [.boolBinary op a b]
  | .boolNot a => a.subs ++ [.boolNot a]
  | .boolEq a b => a.subs ++ b.subs ++ [.boolEq a b]
  | .mux s c a b => c.subs ++ a.subs ++ b.subs ++ [.mux s c a b]
  | .setw w v a => a.subs ++ [.setw w v a]
  | .slice nm st ln w a => a.subs ++ [.slice nm st ln w a]
  | .concat m n a b => a.subs ++ b.subs ++ [.concat m n a b]
  | .concatLitHi k v n b => b.subs ++ [.concatLitHi k v n b]
  | .concatLitLo m a k v => a.subs ++ [.concatLitLo m a k v]
  | .zextMap nm k n a => a.subs ++ [.zextMap nm k n a]
  | .sliceF nm st ln w a => a.subs ++ [.sliceF nm st ln w a]
  | .appCompare op w a b => a.subs ++ b.subs ++ [.appCompare op w a b]
  | .appBool op a b => a.subs ++ b.subs ++ [.appBool op a b]
  | .appBool2 f a b => a.subs ++ b.subs ++ [.appBool2 f a b]

/-- `k` is one of the keys of the list. -/
def memK (k : Key) : List Key → Bool
  | [] => false
  | x :: xs => Key.beq k x || memK k xs

/-- The keys of the list are pairwise different. -/
def nodupK : List Key → Bool
  | [] => true
  | x :: xs => !memK x xs && nodupK xs

/-- The non-input occurrences of a list. -/
def nonInputs : List Key → List Key
  | [] => []
  | x :: xs => if x.isInput then nonInputs xs else x :: nonInputs xs

/-- The occurrences that are neither inputs nor literals. -/
def nonLeaves : List Key → List Key
  | [] => []
  | x :: xs => if x.isInput || x.isLit then nonLeaves xs else x :: nonLeaves xs

/-- **No non-variable subterm occurs twice.** -/
def noRepeat {s : SType} (t : Term s) : Bool := nodupK (nonInputs (key t).subs)

/-- No subterm other than an input or a literal occurs twice. -/
def noRepeatNonLit {s : SType} (t : Term s) : Bool := nodupK (nonLeaves (key t).subs)

/-! Three kernel-decided sanity examples on closed terms (not reflected data). -/

example : noRepeat (.binary .add (.bitsInput 8 0) (.bitsInput 8 0) : Term (.bits 8)) = true := by
  decide

example : noRepeat (.binary .add (.bitsLit 8 1) (.bitsLit 8 1) : Term (.bits 8)) = false := by
  decide

example : noRepeatNonLit (.binary .add (.bitsLit 8 1) (.bitsLit 8 1) : Term (.bits 8)) = true := by
  decide

end Tools.ShippingNoRepeat

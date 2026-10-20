import Sparkle.IR.ModuleNames

/-! # Module names: an injective, tagged encoding of what the compiler names

The compiler names two kinds of modules: the module of a DECLARATION (one
per `Lean.Name`) and the built MEMORY module of the machine route (one per
`(combo, aw, dw)`). `Key` is that tag type (plus `aux`, a reserved tagged
namespace nothing produces yet). `encode : Key → String` is injective
(`Tools.ShippingModuleName.encode_injective`, from `decode_encode`) and its
image is left unchanged by the SystemVerilog emitter's `sanitizeName`
(`Tools.ShippingModuleName.sanitizeName_encode`).

Alphabet of the image: ASCII letters and digits, `_`, `$` — exactly the
characters `Sparkle.Backend.Verilog.sanitizeName` keeps.

Three disjoint forms:

* PLAIN (no `$`), a declaration `N1.….Nk.last` with every `Ni` an
  upper-case-initial alphanumeric component other than `SparkleMem`, and
  `last` a lower-case-initial component of letters, digits and `_`, the
  result not a SystemVerilog keyword: `N1_…_Nk_last` (what the emitter
  printed before). Read back: split at `_`; the leading upper-case-initial
  pieces are the `Ni`, the rest joined by `_` is `last`.
* MEMORY (no `$`, first piece `SparkleMem`): `SparkleMem_{combo|sync}_{aw}_{dw}`.
* TAGGED (always contains `$`): `Sp$D$f1$…$fk` for any other declaration,
  `Sp$X$…` for `aux`. One field per component, root first. A string
  component is its letters and digits kept, `_` written `__`, any other
  character written `_<decimal code point>_`; a numeric component `n` is
  `_<decimal n>` (two `_`-pieces; a string component always has an odd
  number of pieces). `Name.anonymous` is `Sp$D` (no field).

Everything here is structural recursion on lists (no `String` operation
besides `toList` / `ofList`), so it evaluates and the lemmas are by
induction. Nothing uses `Name.toString` or a hash. -/
namespace Sparkle.IR.ModuleName
open Lean (Name)

/-- What a compiler-made module is the module OF. -/
inductive Key where
  /-- the module compiled from a declaration -/
  | decl (n : Name)
  /-- the built memory module of the machine route -/
  | mem (combo : Bool) (aw dw : Nat)
  /-- reserved: an auxiliary module derived from a declaration (none today) -/
  | aux (n : Name)
  deriving DecidableEq

/-- A name component. -/
inductive Comp where
  | str (s : List Char)
  | num (n : Nat)
  deriving DecidableEq

/-! ## Splitting and joining at one character -/

/-- Put `c` in front of the first piece. -/
def consHead (c : Char) : List (List Char) → List (List Char)
  | [] => []
  | h :: t => (c :: h) :: t

/-- The pieces between occurrences of `d` (never empty). -/
def splitOn (d : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: r => if c = d then [] :: splitOn d r else consHead c (splitOn d r)

/-- The pieces with `d` between them. -/
def join (d : Char) : List (List Char) → List Char
  | [] => []
  | a :: t =>
    match t with
    | [] => a
    | _ :: _ => a ++ d :: join d t

/-! ## Decimal numbers -/

def digitChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

def digitVal (c : Char) : Nat := c.toNat - 48

/-- Decimal digits, most significant first; the first argument is fuel. -/
def digsF : Nat → Nat → List Nat
  | 0, _ => [0]
  | f + 1, n => if n < 10 then [n] else digsF f (n / 10) ++ [n % 10]

def undigs (acc : Nat) : List Nat → Nat
  | [] => acc
  | d :: ds => undigs (acc * 10 + d) ds

/-- `n` in decimal (as `toString n` prints it). -/
def natChars (n : Nat) : List Char := (digsF (n + 1) n).map digitChar

def natOfChars (l : List Char) : Nat := undigs 0 (l.map digitVal)

/-! ## One string component

The component as `_`-separated pieces, alternately a run of letters and
digits and the code of one other character (empty for `_` itself). -/

def codeOf (c : Char) : List Char := if c = '_' then [] else natChars c.toNat

def charOf (code : List Char) : Char :=
  if code = [] then '_' else Char.ofNat (natOfChars code)

def pieces : List Char → List (List Char)
  | [] => [[]]
  | c :: s =>
    if c.isAlphanum then consHead c (pieces s) else [] :: codeOf c :: pieces s

def unpieces : List (List Char) → Option (List Char)
  | [] => none
  | [lit] => some lit
  | lit :: code :: rest => (unpieces rest).map fun r => lit ++ charOf code :: r

def encStr (s : List Char) : List Char := join '_' (pieces s)

/-! ## Components and fields -/

def encComp : Comp → List Char
  | .str s => encStr s
  | .num n => '_' :: natChars n

/-- Two pieces: a numeric component. Otherwise a string component. -/
def decPs : List (List Char) → Option Comp
  | [_, ds] => some (.num (natOfChars ds))
  | ps => (unpieces ps).map Comp.str

def decComp (f : List Char) : Option Comp := decPs (splitOn '_' f)

def decAll : List (List Char) → Option (List Comp)
  | [] => some []
  | f :: r => (decComp f).bind fun c => (decAll r).map fun cs => c :: cs

/-- The components of a name, LAST component first. -/
def compsRev : Name → List Comp
  | .anonymous => []
  | .str p s => .str s.toList :: compsRev p
  | .num p n => .num n :: compsRev p

def nameOfRev : List Comp → Name
  | [] => .anonymous
  | .str s :: r => .str (nameOfRev r) (String.ofList s)
  | .num n :: r => .num (nameOfRev r) n

/-- The string components, last first; `none` if there is a numeric one. -/
def strComps : Name → Option (List (List Char))
  | .anonymous => some []
  | .str p s => (strComps p).map fun r => s.toList :: r
  | .num _ _ => none

/-! ## The plain form -/

def isUp (c : Char) : Bool := decide (65 ≤ c.toNat ∧ c.toNat ≤ 90)
def isLow (c : Char) : Bool := decide (97 ≤ c.toNat ∧ c.toNat ≤ 122)

def startsUpper : List Char → Bool
  | [] => false
  | c :: _ => isUp c

def startsLower : List Char → Bool
  | [] => false
  | c :: _ => isLow c

/-- `SparkleMem`, the first piece of every memory module name. -/
def memHead : List Char := ['S', 'p', 'a', 'r', 'k', 'l', 'e', 'M', 'e', 'm']
def comboL : List Char := ['c', 'o', 'm', 'b', 'o']
def syncL : List Char := ['s', 'y', 'n', 'c']

def memKind (combo : Bool) : List Char := if combo then comboL else syncL

def kindOf (k : List Char) : Option Bool :=
  if k = comboL then some true else if k = syncL then some false else none

/-- A namespace component of a plain name. -/
def nsOk (s : List Char) : Bool :=
  startsUpper s && s.all Char.isAlphanum && decide (s ≠ memHead)

/-- The last component of a plain name. -/
def lastOk (s : List Char) : Bool :=
  startsLower s && s.all fun c => c.isAlphanum || c == '_'

def plainL (ns : List (List Char)) (last : List Char) : List Char := join '_' (ns ++ [last])

/-- "Safe": the name takes the plain form (`nsRev`: the namespace
components, innermost first). -/
def safeOk (nsRev : List (List Char)) (last : List Char) : Bool :=
  lastOk last && nsRev.all nsOk &&
    !ModuleNames.keywords.contains (String.ofList (plainL nsRev.reverse last))

def safeOf : Option (List (List Char)) → Option (List (List Char) × List Char)
  | some (last :: nsRev) => if safeOk nsRev last then some (nsRev.reverse, last) else none
  | _ => none

/-- The namespace components (root first) and the last component of a safe
name; `none` for every other name. -/
def safeName (n : Name) : Option (List (List Char) × List Char) := safeOf (strComps n)

/-! ## The tagged form -/

def spHead : List Char := ['S', 'p']

def tagged (k : Char) (cs : List Comp) : List Char :=
  join '$' (spHead :: [k] :: cs.map encComp)

/-! ## The encoding -/

def encDeclL (n : Name) : List Char :=
  match safeName n with
  | some (ns, last) => plainL ns last
  | none => tagged 'D' (compsRev n).reverse

def memL (combo : Bool) (aw dw : Nat) : List Char :=
  join '_' [memHead, memKind combo, natChars aw, natChars dw]

def encodeL : Key → List Char
  | .decl n => encDeclL n
  | .mem combo aw dw => memL combo aw dw
  | .aux n => tagged 'X' (compsRev n).reverse

/-- **The module name of a key.** -/
def encode (k : Key) : String := String.ofList (encodeL k)

/-! ## Reading back -/

/-- The leading upper-case-initial pieces are components; the rest is one. -/
def regroup : List (List Char) → List (List Char)
  | [] => []
  | t :: r => if startsUpper t then t :: regroup r else [join '_' (t :: r)]

def decMem : List (List Char) → Option Key
  | [_, k, a, d] => (kindOf k).map fun c => .mem c (natOfChars a) (natOfChars d)
  | _ => none

/-- A string without `$`, as its `_`-pieces. -/
def decPlain : List (List Char) → Option Key
  | [] => none
  | h :: t =>
    if h = memHead then decMem (h :: t)
    else some (.decl (nameOfRev ((regroup (h :: t)).reverse.map Comp.str)))

def decKey (k : List Char) (cs : List Comp) : Option Key :=
  if k = ['D'] then some (.decl (nameOfRev cs.reverse))
  else if k = ['X'] then some (.aux (nameOfRev cs.reverse))
  else none

/-- A string, as its `$`-pieces. -/
def decTop : List (List Char) → Option Key
  | [] => none
  | [p] => decPlain (splitOn '_' p)
  | _ :: k :: fields => (decAll fields).bind (decKey k)

/-- A left inverse of `encode` (it does not reject every other string). -/
def decode (s : String) : Option Key := decTop (splitOn '$' s.toList)

/-! ## What the compiler calls -/

/-- The module name of a declaration. -/
def ofDecl (n : Name) : String := encode (.decl n)

/-- The module name of a machine-route memory. -/
def ofMem (combo : Bool) (aw dw : Nat) : String := encode (.mem combo aw dw)

/-- The name is in the plain form (printed as the emitter printed it before). -/
def isSafe (n : Name) : Bool := (safeName n).isSome

end Sparkle.IR.ModuleName

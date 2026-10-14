import Lean
import Sparkle.IR.ModuleName

/-! # Names the simulator commands derive from a declaration (finding J5)

`#sim f` / `#simChecked f` write two files and generate a Lean namespace.
Both used to be made from the LAST component of the declaration name, with
every character other than an ASCII letter, a digit or `_` replaced by `_`:
`A.f` and `B.f`, or `fé` and `fè`, got ONE path (a silent overwrite across
files) and ONE namespace.

Here both are functions of the QUALIFIED declaration name.

* `declFileKey n` — the file-name stem. It is the module name
  `Sparkle.IR.ModuleName.ofDecl n` (injective:
  `Tools.ShippingModuleName.ofDecl_injective`; alphabet: ASCII letters,
  digits, `_`, `$` — no path separator, no `.`, no `-`), unchanged when it
  has at most `maxKeyLength` characters. A longer one is cut and gets the
  suffix `-h<hash>`; such stems contain `-` and so never equal an uncut one,
  but two LONG names are kept apart only up to the 64-bit hash.
* `declNamespace n` — the text of the ABSOLUTE Lean namespace the wrappers
  go under (the caller appends `.Sim` / `.SimChecked`): the components of the
  user-facing name, each written between `«` and `»`. For `A.f` it is
  `«A».«f»`, i.e. the namespace `A.f` — what the command produced before
  when it was run inside the declaration's own namespace. A name with a
  numeric component, an empty component or a component containing `»` cannot
  be written that way; it gets the single component `«<ofDecl n>»`.
* `declIsPrivate n` — a private declaration: the caller marks every
  generated declaration `private`, so the wrappers of two private
  declarations of two files never meet (their file keys differ by the module
  prefix of the private name).
* `writeDesignPaths` — the two C paths of `#writeDesign`, never equal.
* `svNamespace` — the namespace component of a parsed (`sim!`) design.
* `svFileKey name text` — for `sim!`, whose design is a parsed
  SystemVerilog text, not a declaration: the stem is made from the module
  name AND a hash of the generated C text, and always contains `-`, so it is
  never a `declFileKey` of an uncut name, never a cut one (`-h…`), and two
  different designs with one module name do not share a file.

NOT solved here (stated, not hidden): a case-insensitive file system
(`Foo.bar` and `FOO.bar` have stems differing in case only); two
declarations with the SAME qualified name in two files that are never
imported together (one identity, one path); hash collisions in the two
hashed forms. Everything is a pure function; nothing here writes a file. -/
namespace Sparkle.Compiler.SimNames
open Lean (Name)

/-- The longest stem written unchanged. With the longest suffix the commands
add (`_jit.c`) the file name stays under the usual 255-byte limit. -/
def maxKeyLength : Nat := 180

/-- The number of characters kept from a stem that is too long. -/
def cutLength : Nat := 120

/-- A stem of bounded length: `key` itself, or a cut of it and `-h<hash>`. -/
def boundKey (key : String) : String :=
  let cs := key.toList
  if cs.length ≤ maxKeyLength then key
  else String.ofList (cs.take cutLength) ++ "-h" ++ toString (Hashable.hash key)

/-- **The file-name stem of a declaration.** -/
def declFileKey (declName : Name) : String :=
  boundKey (Sparkle.IR.ModuleName.ofDecl declName)

/-- A component that can be written as `«…»`. -/
def quotable (s : String) : Bool :=
  !s.isEmpty && s.toList.all fun c => c != '»' && c != '«' && c != '\n'

/-- The components, root first; `none` if one cannot be written as `«…»`. -/
def quotableComponents : Name → Option (List String)
  | .anonymous => some []
  | .str p s => if quotable s then (quotableComponents p).map (· ++ [s]) else none
  | .num _ _ => none

/-- **The absolute Lean namespace (as text) of the wrappers of a declaration**,
without the command's own last component. -/
def declNamespace (declName : Name) : String :=
  match quotableComponents (Lean.privateToUserName declName) with
  | some (c :: cs) => String.intercalate "." ((c :: cs).map fun s => "«" ++ s ++ "»")
  | _ => "«" ++ Sparkle.IR.ModuleName.ofDecl declName ++ "»"

/-- Is the declaration private (its wrappers are generated `private`)? -/
def declIsPrivate (declName : Name) : Bool := Lean.isPrivateName declName

/-- Put `private` in front of a generated declaration command. Commands that
declare nothing (`namespace`, `open`, `end`) are returned unchanged. -/
def withVisibility (isPrivate : Bool) (cmd : String) : String :=
  if isPrivate &&
      (cmd.startsWith "def " || cmd.startsWith "structure " || cmd.startsWith "instance ") then
    "private " ++ cmd
  else cmd

/-- A module name of a parsed design kept as is in a file name. -/
def plainSvName (name : String) : Bool :=
  !name.isEmpty && name.toList.all fun c => c.isAlphanum || c == '_'

/-- **The file-name stem of a parsed (`sim!`) design**: the module name (as
is when it has only letters, digits and `_`; otherwise its injective
`ModuleName.encStr` form behind `Sp$S$`), cut like `boundKey`, then `-` and
the hash of the generated C text. -/
def svFileKey (moduleName : String) (cText : String) : String :=
  let stem :=
    if plainSvName moduleName then moduleName
    else "Sp$S$" ++ String.ofList (Sparkle.IR.ModuleName.encStr moduleName.toList)
  let cs := stem.toList
  let cut := if cs.length ≤ cutLength then stem else String.ofList (cs.take cutLength)
  cut ++ "-" ++ toString (Hashable.hash (moduleName ++ "|" ++ cText))

/-- **The Lean namespace (as text) of a parsed (`sim!`) design**, without
`.Sim`: the module name is ONE component — written as is when it is a plain
identifier (as before), between `«` and `»` otherwise (before: every other
character replaced by `_`, so `a$b` and `a_b` shared `a_b.Sim`). It is
relative to the namespace the command is run in: a parsed module has no Lean
namespace of its own. -/
def svNamespace (moduleName : String) : String :=
  let digitFirst := (moduleName.toList.head?.map Char.isDigit).getD true
  if plainSvName moduleName && !digitFirst then moduleName
  else if quotable moduleName then "«" ++ moduleName ++ "»"
  else "«Sp$S$" ++ String.ofList (Sparkle.IR.ModuleName.encStr moduleName.toList) ++ "»"

/-- **The two C paths of `#writeDesign`** for its `cppPath` argument:
`(C text, JIT text)`. With `_cppsim.h` in the path: `cppPath` and the path
with `_jit.c` in its place (unchanged). Without it the old derivation gave
the JIT text the SAME path and it silently replaced the C text; now the JIT
text stays at `cppPath` (what that file held before) and the C text goes to
`cppPath ++ "_cppsim.h"`. The two components always differ. -/
def writeDesignPaths (cppPath : String) : String × String :=
  let jitPath := cppPath.replace "_cppsim.h" "_jit.c"
  if jitPath == cppPath then (cppPath ++ "_cppsim.h", cppPath) else (cppPath, jitPath)

end Sparkle.Compiler.SimNames

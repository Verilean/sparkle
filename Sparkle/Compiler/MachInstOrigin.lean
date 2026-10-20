import Sparkle.Compiler.MachMemory

/-! # Where a call entry of a machine came from

The machine reader records every child call as an entry `(c, js, kind)`
(`MachRead.insts`). A memory call is recorded under a placeholder name
(`MachMemory.memChildName`), and a declaration can carry that very name
(metaprogramming can make one), so the NAME does not say which kind of call an
entry is. The reader therefore records the origin of every entry next to it, and
the closing builds an entry's child from the origin (`InstOrigin.child?`): a
memory entry gets the memory module, every other entry the compile of its
declaration. Two entries are the same call only when their origins agree too. -/
namespace Sparkle.Compiler.MachInstOrigin

/-- The origin of a call entry. -/
inductive InstOrigin where
  /-- a call of a `@[hardware_module]` with a one-Signal (BitVec or Bool) result -/
  | ord
  /-- field `i` of a call of a `@[hardware_module]` with a structure result -/
  | field (i : Nat)
  /-- a memory (`Signal.memory` / `memoryComboRead`), combinational read or not,
      address and data widths -/
  | mem (combo : Bool) (aw dw : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The child a closing builds for an entry of this origin without compiling a
declaration: the memory module for a memory entry, none for any other. -/
def InstOrigin.child? : InstOrigin → Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)
  | .mem combo aw dw => some (Sparkle.Compiler.MachMemory.memModule combo aw dw)
  | _ => none

end Sparkle.Compiler.MachInstOrigin

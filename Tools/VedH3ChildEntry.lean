import Tools.VedH3ChildTblEntry
import Tools.VedH3ChildChainEntry

/-!
# The proof source of a combinational child (issue sparkle-ved-hier3-child)

`childProofSrc` is what the hierarchical entries use for a register-free child: an add-stage chain
(`Tools/VedH3ChildChainEntry.lean`), a named constant table (`Tools/VedH3ChildTblEntry.lean`), else the
generated script of `Tools/VedU1Entry.lean`.  The choice only picks the script; the kernel checks the proof.
-/

namespace Tools.VedH3ChildEntry

open Tools.VedU1Entry

def childProofSrc (cdecl : Lean.Name) (cdom : Nat) (cm : Sparkle.IR.AST.Module) : ProofSrc :=
  match Tools.VedH3ChildChainEntry.chainProofSrc? cdecl cdom cm with
  | some p => p
  | none => Tools.VedH3ChildTblEntry.childProofSrc cdecl cdom cm

end Tools.VedH3ChildEntry

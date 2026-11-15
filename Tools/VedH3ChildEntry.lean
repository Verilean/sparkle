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

open Lean Elab Term Meta in
/-- The child step of the hierarchical entries for a REGISTER-FREE child: the proof source chosen by
`childProofSrc`; when that source is refused, the generated script is tried (what the entries did before
this unit), so a child the older route proved is still proved.  A refusal of both is the generated
script's. -/
def checkCombChild (cdecl : Name) (cdom : Nat) (base : Name) (cstmt : Expr) (cm : Sparkle.IR.AST.Module) :
    TermElabM Name := do
  match childProofSrc cdecl cdom cm with
  | .generated => checkU1E cdecl base cstmt cm .generated
  | src =>
    try checkU1E cdecl base cstmt cm src
    catch e =>
      if ← isRefusal e then checkU1E cdecl base cstmt cm .generated else throw e

end Tools.VedH3ChildEntry

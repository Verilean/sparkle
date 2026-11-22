import Tools.VedH3ChildTblEntry
import Tools.VedH3ChildChainEntry
import Tools.VedU2HierDbg

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
  -- measurement only (`VED_CHILD_TICK` and `VED_HIER_PHASE_FILE`): the child check's stages on the phase clock, ahead of
  -- `checkU1E` (module/contract/body definitions and the order check), script generation, proof elaboration (the proof
  -- source is wrapped in two `ved_tick`s), and the rest (`instantiateMVars`, the logged-error scan, kernel `addDecl`).  A
  -- generated script (`ProofSrc.generated`) is built inside `checkU1E` and has no inner stage.  Off: nothing is wrapped.
  let tickOn := (← IO.getEnv "VED_CHILD_TICK").isSome
  let lbl := s!"child {cdecl}"
  let mark (what : String) : IO Unit := Tools.VedU2HierDbg.phaseLog s!"{lbl}: {what}"
  let wrap (src : ProofSrc) : ProofSrc :=
    if !tickOn then src else
    match src with
    | .generated => src
    | .term s => .term s
    | .built mk => .built fun nm m => do
        mark "script generation begin"
        let s ← mk nm m
        mark "script generation end"
        let t : Term := ⟨s⟩
        let b := Syntax.mkStrLit s!"{lbl}: proof elaboration begin"
        let e := Syntax.mkStrLit s!"{lbl}: proof elaboration end"
        `(by ved_tick $b; refine ($t); ved_tick $e)
  let run (src : ProofSrc) : TermElabM Name := do
    if tickOn then mark "checkU1E begin"
    let r ← checkU1E cdecl base cstmt cm (wrap src)
    if tickOn then mark "checkU1E end (kernel addDecl included)"
    pure r
  match childProofSrc cdecl cdom cm with
  | .generated => run .generated
  | src =>
    try run src
    catch e =>
      if ← isRefusal e then run .generated else throw e

end Tools.VedH3ChildEntry

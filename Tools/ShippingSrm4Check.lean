import Tools.ShippingSrm4Core6
-- UNBUILT (unit SRM4): see REPORT-SRM4.md for the run names and exits.
-- SCOPE (binding): a PROVED OBSTRUCTION, not a theorem about a class.  The depth-indexed child check `kidCheck C (m + 1)` is `designCheck C m`, whose text check `textCheckI` asks `seqStmtOkI` of every
-- statement of the module; `seqStmtOkI (.memory ..) = false` (memories "have their own layer").  So the built memory module of a memory entry fails `kidCheck C (m + 1)` for EVERY module list `C` and EVERY
-- `m`: a memory module can be checked as a child only at `kidCheck C 0` (`leafCheck`, `leafCheck_memModule`).  Consequently the `check` field of `KidFactsA` (`Tools/ShippingSeqChildDeepKidFactsA.lean`), which asks
-- `kidCheck (childMap ms) m g` of the kid's module AND of EVERY module of its served design at the SAME depth `m`, is UNSATISFIABLE at `m ≥ 1` for a callee whose served design contains a memory module
-- (`kidFactsA_check_false`), and a callee that has an instance cannot be `kidCheck _ 0` at all (`leafCheck` asks `seqStmtOkA`).  Hence the A-form `KidFactsA` chain is not the right statement for a callee with a memory
-- child, and `Tools/ShippingSrm4Core6.lean` proves `KidFactsNC` / `KidFactsTNC` (all fields but `check`).  What replaces `check` is OPEN: a per-module HEIGHT-indexed check (a memory module at height 0, a
-- module at height 1 + its kids' heights), which changes the statement of `designCheck`'s consumers (`kids_designCheck_inA`, the parent's `designCheck` block).
-- No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.

namespace Tools.ShippingSrm4Check
open Sparkle.IR.AST Sparkle.IR.Machine Tools.ShippingDesignSV
open Sparkle.Compiler.MachMemory (memModule)

/-- a memory module fails the text check at every module list -/
theorem textCheckI_memModule (C : String → Option (Module × Sparkle.IR.Semantics.WEnv)) (cb : Bool) (aw dw : Nat) :
    textCheckI C (memModule cb aw dw).1 = false := by
  simp [textCheckI, memModule, Tools.ShippingHierSVSoundness.seqStmtOkI]

/-- **a memory module fails `designCheck` at every depth** -/
theorem designCheck_memModule (C : String → Option (Module × Sparkle.IR.Semantics.WEnv)) (cb : Bool) (aw dw : Nat) (n : Nat) :
    designCheck C n (memModule cb aw dw).1 = false := by
  cases n <;> simp [designCheck, textCheckI_memModule]

/-- **a memory module fails `kidCheck` at every positive depth** (at depth 0 it passes: `leafCheck_memModule`) -/
theorem kidCheck_memModule_succ (C : String → Option (Module × Sparkle.IR.Semantics.WEnv)) (cb : Bool) (aw dw : Nat) (m : Nat) :
    Tools.ShippingChecksDesign.kidCheck C (m + 1) (memModule cb aw dw).1 = false :=
  designCheck_memModule C cb aw dw m

end Tools.ShippingSrm4Check

namespace Tools.ShippingSrm4Check
open Lean Meta
open Tools.ShippingChildCacheA Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingSeqChildDeepKidFactsA
open Sparkle.Compiler.Elab Sparkle.IR.Machine Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingChildInv
open Sparkle.Compiler.MachMemory (memModule)

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The `check` field of `KidFactsA` is unsatisfiable at a positive depth for a callee whose served design contains a memory module**: for any module list `ms` satisfying the field's own premises, the
field's conclusion fails (it asks `kidCheck (childMap ms) (m + 1) g` of every module `g` of the served design). -/
theorem kidFactsA_check_false (O : RefLawsAOps MkRefd mref cref) {c : Name} {outs : List OutField} {ins : List Nat} {m : Nat}
    (h : KidFactsA O c outs ins (m + 1)) {y : Res} (hy : RealChildA O c y) {cb : Bool} {aw dw : Nat}
    (hmem : (memModule cb aw dw).1 ∈ y.2.modules) (ms : List Sparkle.IR.AST.Module)
    (hy1 : moduleByName ms y.1.name = some y.1) (hy2 : ∀ g ∈ y.2.modules, moduleByName ms g.name = some g) : False := by
  have h1 := (h.check y hy ms hy1 hy2).2 _ hmem
  rw [kidCheck_memModule_succ] at h1
  cases h1

end Tools.ShippingSrm4Check

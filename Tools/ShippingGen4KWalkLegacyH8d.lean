import Tools.ShippingGen4KWalkLegacyH8a
-- NOT BUILT (rt179). LegacyImplK part 8d: the PROFILE BLOCK of Elab.lean 6973-6977 (eprintln, flushStderr, Handle.mk, putStrLn, flush: five lifts)
-- as ONE `KeepsCP` unit followed by the rest of the program (the memo law is `MemoFamily.logProf`, already in the approved family).
-- Why: in H11 the walk had no rule for this block; the fallback `keepsK_framedNM … constructor` (a search over every `FramedNM` constructor, which has none for
-- `IO.eprintln` / `Handle.mk`) cost 58-60M raw heartbeats per attempt and failed.
-- Takes `MemoFamily` as a HYPOTHESIS; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkLegacyH8d
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslateA
open Tools.ShippingGen4KWalkTac2
open Tools.ShippingChildWalkA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingGen4KWalkLegacyH8a
open Tools.ShippingGen4KWalkDiag

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000

/-- Two lifts then a continuation, with the second depending on the first result. -/
theorem liftMetaM_bind_dep {α β : Type} (a : MetaM α) (f : α → MetaM Unit) (k : Unit → CompilerM β) :
    ((CompilerM.liftMetaM a : CompilerM α) >>= fun x => (CompilerM.liftMetaM (f x) : CompilerM Unit) >>= k) =
      ((CompilerM.liftMetaM (a >>= f) : CompilerM Unit) >>= k) := by
  funext ctx st
  unfold CompilerM.liftMetaM
  simp only [liftM, monadLift, MonadLift.monadLift]
  show (((a >>= fun x => pure (x, st) : MetaM _) >>= fun p =>
      (((f p.1 >>= fun y => pure (y, p.2) : MetaM _)) >>= fun q => k q.1 ctx q.2 : MetaM _)) : MetaM _) =
    ((((a >>= f) >>= fun y => pure (y, st) : MetaM _)) >>= fun p => k p.1 ctx p.2 : MetaM _)
  simp only [metaM_bind_assoc, metaM_pure_bind]

section H8d
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (hA : AdmCtx O.quiet mctx cctx)
include M hS hA

/-- `profLogIO b msg` keeps the invariant. -/
theorem keepsK_profLog (b : Bool) (s : String) :
    Keeps mctx mref cctx cref I (liftM (profLogIO b s) : MetaM Unit) := by
  intro w hw
  have hq := hS.1 w hw
  have hk := O.diag hA _ (Diag.profLog b s) w hq
  have hmv := M.logProf hA b s w hq
  refine ⟨hS.2 w _ hk.1.1 hk.1.2.1 hk.1.2.2 hmv (fun _ => hk.2) hw, ?_⟩
  unfold ErrOk
  cases hmm : (liftM (profLogIO b s) : MetaM Unit) mctx mref cctx cref w with
  | ok a w1 => exact True.intro
  | error e' w1 => exact O.excOk hA _ (.diag (Diag.profLog b s)) w e' w1 hq hmm

/-- The profile block as ONE `CompilerM` unit, followed by the rest of the program. -/
theorem profBlockCPk {β : Type} (s : String) (k : Unit → CompilerM β)
    (hk : ∀ u, KeepsCP mctx mref cctx cref I (k u)) :
    KeepsCP mctx mref cctx cref I ((CompilerM.liftMetaM (liftM (IO.eprintln s) : MetaM Unit) : CompilerM Unit) >>= fun _ =>
      (CompilerM.liftMetaM (liftM Sparkle.Compiler.flushStderr : MetaM Unit) : CompilerM Unit) >>= fun _ =>
      (CompilerM.liftMetaM (liftM (IO.FS.Handle.mk "/tmp/sparkle-profile.log" IO.FS.Mode.append) : MetaM IO.FS.Handle) : CompilerM IO.FS.Handle) >>= fun h =>
      (CompilerM.liftMetaM (liftM (h.putStrLn s) : MetaM Unit) : CompilerM Unit) >>= fun _ =>
      (CompilerM.liftMetaM (liftM h.flush : MetaM Unit) : CompilerM Unit) >>= k) := by
  simp only [liftMetaM_bind_k, liftMetaM_bind_dep]
  rw [profBlock_eq]
  exact KeepsCP.bind (KeepsCP.lift (keepsK_profLog M hS hA true s)) hk

end H8d

end Tools.ShippingGen4KWalkLegacyH8d

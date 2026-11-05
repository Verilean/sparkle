import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4FKidsCanon
import Tools.ShippingGen4KWalkLegacyH8a
import Tools.ShippingGen4FKidsLegacyH8a
-- NOT BUILT (rt179). LegacyImplKS part 8d: the PROFILE BLOCK of Elab.lean 6973-6977 (eprintln, flushStderr, Handle.mk, putStrLn, flush: five lifts)
-- as ONE `KeepsCS` unit followed by the rest of the program (the memo law is `MemoFamily.logProf`, already in the approved family).
-- Why: in H11 the walk had no rule for this block; the fallback `keepsK_framedNM … constructor` (a search over every `FramedNM` constructor, which has none for
-- `IO.eprintln` / `Handle.mk`) cost 58-60M raw heartbeats per attempt and failed.
-- Takes `MemoFamily` as a HYPOTHESIS; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4FKidsLegacyH8d
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
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingGen4FKidsHelpers
open Tools.ShippingGen4KWalkLegacyH8a
open Tools.ShippingGen4FKidsLegacyH8a
open Tools.ShippingGen4KWalkDiag
open Tools.ShippingGen4FKidsDiag

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000

/-- Two lifts then a continuation, with the second depending on the first result. -/
theorem liftMetaM_bind_depS {α β : Type} (a : MetaM α) (f : α → MetaM Unit) (k : Unit → CompilerM β) :
    ((CompilerM.liftMetaM a : CompilerM α) >>= fun x => (CompilerM.liftMetaM (f x) : CompilerM Unit) >>= k) =
      ((CompilerM.liftMetaM (a >>= f) : CompilerM Unit) >>= k) := by
  funext ctx st
  unfold CompilerM.liftMetaM
  simp only [liftM, monadLift, MonadLift.monadLift]
  show (((a >>= fun x => pure (x, st) : MetaM _) >>= fun p =>
      (((f p.1 >>= fun y => pure (y, p.2) : MetaM _)) >>= fun q => k q.1 ctx q.2 : MetaM _)) : MetaM _) =
    ((((a >>= f) >>= fun y => pure (y, st) : MetaM _)) >>= fun p => k p.1 ctx p.2 : MetaM _)
  simp only [metaM_bind_assocS, metaM_pure_bindS]

section H8d
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (hA : AdmCtx O.quiet mctx cctx)
include M hS hA

/-- `profLogIO b msg` keeps the invariant. -/
theorem keepsK_profLogS (b : Bool) (s : String) :
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

/-- The profile block as a `MetaM` program (the form the walk meets after the `CompilerM` lifts are opened). -/
theorem keepsK_profBlockS (s : String) :
    Keeps mctx mref cctx cref I ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ =>
      (liftM Sparkle.Compiler.flushStderr : MetaM Unit) >>= fun _ =>
      (liftM (IO.FS.Handle.mk "/tmp/sparkle-profile.log" IO.FS.Mode.append) : MetaM IO.FS.Handle) >>= fun h =>
      (liftM (h.putStrLn s) : MetaM Unit) >>= fun _ =>
      (liftM h.flush : MetaM Unit)) := by
  rw [profBlock_eq]
  exact keepsK_profLogS M hS hA true s

/-- The profile block as ONE `CompilerM` unit, followed by the rest of the program. -/
theorem profBlockCPkS {β : Type} (s : String) (k : Unit → CompilerM β)
    (hk : ∀ u, KeepsCS mctx mref cctx cref I (k u)) :
    KeepsCS mctx mref cctx cref I ((CompilerM.liftMetaM (liftM (IO.eprintln s) : MetaM Unit) : CompilerM Unit) >>= fun _ =>
      (CompilerM.liftMetaM (liftM Sparkle.Compiler.flushStderr : MetaM Unit) : CompilerM Unit) >>= fun _ =>
      (CompilerM.liftMetaM (liftM (IO.FS.Handle.mk "/tmp/sparkle-profile.log" IO.FS.Mode.append) : MetaM IO.FS.Handle) : CompilerM IO.FS.Handle) >>= fun h =>
      (CompilerM.liftMetaM (liftM (h.putStrLn s) : MetaM Unit) : CompilerM Unit) >>= fun _ =>
      (CompilerM.liftMetaM (liftM h.flush : MetaM Unit) : CompilerM Unit) >>= k) := by
  simp only [liftMetaM_bind_kS, liftMetaM_bind_depS]
  rw [profBlock_eq]
  exact KeepsCS.bind (KeepsCS.lift (keepsK_profLogS M hS hA true s)) hk

/-- The same block as it is elaborated in `CompilerM`: five `IO` actions lifted DIRECTLY (`liftM : IO → CompilerM`). -/
theorem profBlockCPk2S {β : Type} (s : String) (k : Unit → CompilerM β)
    (hk : ∀ u, KeepsCS mctx mref cctx cref I (k u)) :
    KeepsCS mctx mref cctx cref I ((liftM (IO.eprintln s) : CompilerM Unit) >>= fun _ =>
      (liftM Sparkle.Compiler.flushStderr : CompilerM Unit) >>= fun _ =>
      (liftM (IO.FS.Handle.mk "/tmp/sparkle-profile.log" IO.FS.Mode.append) : CompilerM IO.FS.Handle) >>= fun h =>
      (liftM (h.putStrLn s) : CompilerM Unit) >>= fun _ =>
      (liftM h.flush : CompilerM Unit) >>= k) :=
  profBlockCPkS M hS hA s k hk

end H8d

end Tools.ShippingGen4FKidsLegacyH8d

import Tools.Assume.MemoFamily
import Tools.ShippingChildKeeps
import Tools.ShippingGen4KWalk
import Tools.ShippingGen4KWalkEntry
import Tools.ShippingGen4KWalkHelpers
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
-- NOT BUILT (scratch, rt172): scratch check for scripts/gen4/MEMO_FAMILY_FREEZE.md rev3.

open Lean Elab Command Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildBndCore Tools.Assume.MemoFamily
open Sparkle.Compiler.Elab

namespace Tests.Gen4.MemoFamilyRev3Check

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

theorem liftIOCore_bind {α β : Type} (x : IO α) (f : α → IO β) :
    (Core.liftIOCore (x >>= f) : CoreM β) = (Core.liftIOCore x >>= fun a => Core.liftIOCore (f a) : CoreM β) := by
  funext c s w
  unfold Core.liftIOCore
  cases h : x w with
  | ok a w1 =>
    simp [StateRefT'.instMonad._aux_13, StateRefT'.instMonad._aux_5, instMonadEIO._aux_13, EIO.adapt, EStateM.adaptExcept,
      EStateM.bind, ReaderT.bind, readThe, MonadReaderOf.read, ReaderT.read, StateRefT'.lift, h, pure, ReaderT.pure,
      EStateM.pure, ReaderT.run, StateRefT'.get, StateRefT'.set, bind, getRef, EST.bind, liftM, monadLift,
      MonadLift.monadLift, IO.toEIO, EST.pure, EStateM.adaptExcept, EIO.adapt, EST.Out.ok, read, MonadReader.read, instMonadEIO._aux_5, EST.Out.ok, EStateM.pure]
  | error e w1 =>
    simp [StateRefT'.instMonad._aux_13, StateRefT'.instMonad._aux_5, instMonadEIO._aux_13, EIO.adapt, EStateM.adaptExcept,
      EStateM.bind, ReaderT.bind, readThe, MonadReaderOf.read, ReaderT.read, StateRefT'.lift, h, pure, ReaderT.pure,
      EStateM.pure, ReaderT.run, StateRefT'.get, StateRefT'.set, bind, getRef, EST.bind, liftM, monadLift,
      MonadLift.monadLift, IO.toEIO, EST.pure, EStateM.adaptExcept, EIO.adapt, EST.Out.ok, read, MonadReader.read, instMonadEIO._aux_5, EST.Out.ok, EStateM.pure]

theorem liftM_bind_metaM {α β : Type} (x : IO α) (f : α → IO β) :
    (liftM (x >>= f) : MetaM β) = ((liftM x : MetaM α) >>= fun a => (liftM (f a) : MetaM β)) := by
  funext mctx mref cctx cref w
  simp only [liftM, monadLift, MonadLift.monadLift]
  show Core.liftIOCore (x >>= f) cctx cref w = ((Core.liftIOCore x : CoreM α) >>= fun a => Core.liftIOCore (f a)) cctx cref w
  rw [liftIOCore_bind]

/-- The profile block of Elab.lean 6973-6977 (five separate lifts) equals one lift of `profLogIO true`. -/
theorem profBlock_eq (s : String) :
    ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ =>
      (liftM Sparkle.Compiler.flushStderr : MetaM Unit) >>= fun _ =>
      (liftM (IO.FS.Handle.mk "/tmp/sparkle-profile.log" IO.FS.Mode.append) : MetaM IO.FS.Handle) >>= fun h =>
      (liftM (h.putStrLn s) : MetaM Unit) >>= fun _ =>
      (liftM h.flush : MetaM Unit)) = (liftM (profLogIO true s) : MetaM Unit) := by
  simp only [profLogIO, ↓reduceIte, liftM_bind_metaM]

end Tests.Gen4.MemoFamilyRev3Check

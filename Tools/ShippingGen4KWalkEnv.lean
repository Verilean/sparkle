import Tools.ShippingChildInv

-- BUILT: kjob lake build Tools.ShippingGen4KWalkEnv exit 0 (308 jobs, rt165, source as of 3ce5d54f); axioms standard only. Clean build is the coder's. No sorry/axiom/native_decide; no Check file (one theorem).

/-!
# KWalkEnv: `IO.getEnv`, lifted to `MetaM`, always returns (KWALK_PLAN §4 (a))

`IO.getEnv : String → BaseIO (Option String)` (`@[extern "lean_io_getenv"] opaque`, Init/System/IO.lean:951
in toolchain v4.32.1). The lift to `MetaM` goes through `BaseIO.toEIO`, which only builds `.ok`; the
extern is never inspected, only that its result is a `BaseIO` value (an `EStateM.Result` with no error case).
-/

namespace Tools.ShippingGen4KWalkEnv
open Lean Meta
open Tools.ShippingChildInv
open Tools.ShippingEntrySoundness

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

theorem ioEnv_runs (n : String) (w : Void IO.RealWorld) :
    ∃ a w', RunsTo (IO.getEnv n : MetaM (Option String)) mctx mref cctx cref w a w' := by
  unfold RunsTo
  cases h : (IO.getEnv n : BaseIO (Option String)) w with
  | mk a w' =>
    refine ⟨a, w', ?_⟩
    change (match (IO.getEnv n : BaseIO (Option String)) w with | .mk a s => EST.Out.ok a s) = _
    rw [h]

end Tools.ShippingGen4KWalkEnv

#print axioms Tools.ShippingGen4KWalkEnv.ioEnv_runs

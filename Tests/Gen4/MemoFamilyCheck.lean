import Tools.Assume.MemoFamily
import Tools.ShippingGen2Defs
import Tools.ShippingGen5T1ND
import Tools.ShippingGen4KWalkDiag
set_option autoImplicit false
-- NOT BUILT (rt173, base c595b472): rev3 Check; the build SHA is recorded in the next comment-only commit. Clean build is the coder's.

/-! # Audit of Tools/Assume/MemoFamily.lean (scripts/gen4/MEMO_FAMILY_FREEZE.md rev3, c595b472)

`MemoFamily` is a TRUSTED hypothesis structure (a hypothesis about the runtime behaviour of the memo / child-cache /
depth cells). This file audits its TYPE only.

1. TYPE: each of the 15 statements (11 fields of `MemoFamily` + 4 of `MemoTele`) is `isDefEq` to `Expected.*` below,
   which was written separately from the freeze section 2 text (not copied from the implementation file;
   `mv` is spelled `readOf sparkleSubModuleCache`, `cv/sv/dv` as `readOf` of their refs).
2. MUTANT (M1-M7; M6 has two variants; L1-L6 for `lamTelescopeT`; D1-D5 for the three Diag statements): signature/defeq REJECTIONS only. A mutant is rejected because its type is not
   defeq to the field's type. This is NOT a semantic counterexample and says nothing about whether the mutated
   statement is true or false at runtime.
3. AXIOMS: only propext / Classical.choice / Quot.sound (no sorryAx, no ofReduceBool).
4. CLOSURE: transitive constant closure (types, thm/def bodies; opaque bodies are not tracked) contains no
   `Laws` / `T1Hyp` / `T1HypND` constant. The detector is run on `T1Hyp` and `T1HypND` as positive controls.
   OUTSIDE: six expressible statements (arbitrary path/handle/stream/printer, `PpMvK`, `MsgMvK`) are NOT defeq to any of
   the three Diag fields (they are not in the family).
5. MODEL: `vacuous_model` (quiet = False) shows the TYPE is satisfiable. This is a satisfiability check of the type,
   not evidence about the runtime. -/

open Lean Elab Command Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh
open Sparkle.Compiler.Elab

namespace Tests.Gen4.MemoFamilyCheck

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## Expected (from the freeze text) -/
namespace Expected

def frame (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {α : Type} (p : MetaM α), Tools.Assume.MemoFamily.FramedNM MkRefd p → ∀ w, O.quiet w →
    readOf sparkleSubModuleCache (endW mctx mref cctx cref p w) = readOf sparkleSubModuleCache w
def frameCacheSet (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
def frameDepthSet (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
def memoGet (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ m w w',
    RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref w m w' → O.quiet w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
def memoSet (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = v
def memoModify (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleSubModuleCache.modify f : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = f (readOf sparkleSubModuleCache w)
def frameCacheModify (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
def frameDepthModify (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Nat → Nat) w u w',
    RunsTo (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w

/-- The invariant-preservation premise shared by the four tele statements. -/
def TeleI (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) : Prop :=
  ∀ w w', readOf sparkleChildCache w' = readOf sparkleChildCache w →
    readOf sparkleChildSynth w' = readOf sparkleChildSynth w →
    readOf sparkleSynthDepth w' = readOf sparkleSynthDepth w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w → (O.quiet w → O.quiet w') →
    I w → I w'
def telescope (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    TeleI O I →
    ∀ (ty : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.forallTelescopeReducing ty k)
/-- The rev2 `Keeps` statement; in rev3 it is the derived theorem `MemoTele.lamTelescope` (not a field). -/
def lamTelescope (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    TeleI O I →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup)
def localDecl (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    TeleI O I →
    ∀ (n : Name) (ty : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLocalDeclD n ty k)
def letDecl (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    TeleI O I →
    ∀ (n : Name) (ty v : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLetDecl n ty v k)
def lamTelescopeT (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (P : Void IO.RealWorld → Prop) (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop),
    AdmCtx O.quiet mctx cctx →
    (∀ w, P w → O.quiet w) → (∀ a w, Q a w → O.quiet w) → (∀ w, R w → O.quiet w) →
    TeleI O P →
    (∀ a, TeleI O (Q a)) →
    TeleI O R →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      ∀ w, P w → match k xs b mctx' mref cctx' cref w with
        | .ok a w' => Q a w'
        | .error ex w' => R w' ∧ OkExc ex) →
    ∀ w, P w → match Lean.Meta.lambdaTelescope e k cleanup mctx mref cctx cref w with
      | .ok a w' => Q a w'
      | .error ex w' => R w' ∧ OkExc ex
def logProf (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (b : Bool) (msg : String) w,
    O.quiet w →
    readOf sparkleSubModuleCache (endW mctx mref cctx cref (liftM (profLogIO b msg) : MetaM Unit) w) =
      readOf sparkleSubModuleCache w
def stderrLine (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (s : String) w, O.quiet w →
    readOf sparkleSubModuleCache (endW mctx mref cctx cref
      ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ => (liftM Sparkle.Compiler.flushStderr : MetaM Unit)) w) =
      readOf sparkleSubModuleCache w
def printersMv (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ w, O.quiet w → ∀ ctx : PPContext, ctx.env = (readOf cref w).env →
    (∀ e : Lean.Expr, ∀ v, match Lean.ppExprWithInfos ctx e v with
      | .mk _ v' => readOf sparkleSubModuleCache v' = readOf sparkleSubModuleCache v) ∧
    (∀ n : Name, ∀ v, match Lean.ppConstNameWithInfos ctx n v with
      | .mk _ v' => readOf sparkleSubModuleCache v' = readOf sparkleSubModuleCache v)
end Expected

/-! ## Mutants: each changes one thing; rejected by signature/defeq (not semantic counterexamples) -/
namespace Mutant

/-- M1: memoSet conclusion `= v` replaced by `= mv w`. -/
def M1 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
/-- M2: memoSet without `O.quiet w →`. -/
def M2 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w' →
    readOf sparkleSubModuleCache w' = v
/-- M3: memoSet without `AdmCtx O.quiet mctx cctx →`. -/
def M3 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, ∀ v w u w',
    RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = v
/-- M4: frame over `FramedA` (which contains the memo cell's own get/set/modify) instead of `FramedNM`. -/
def M4 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {α : Type} (p : MetaM α), FramedA MkRefd p → ∀ w, O.quiet w →
    readOf sparkleSubModuleCache (endW mctx mref cctx cref p w) = readOf sparkleSubModuleCache w
/-- M5: memoModify conclusion `= f (mv w)` replaced by `= mv w`. -/
def M5 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleSubModuleCache.modify f : MetaM Unit) mctx mref cctx cref w u w' →
    O.quiet w → readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
/-- M6a: frameCacheModify without `O.quiet w →`. -/
def M6a (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w' →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
/-- M6b: frameDepthModify without `O.quiet w →`. -/
def M6b (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Nat → Nat) w u w',
    RunsTo (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) mctx mref cctx cref w u w' →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
/-- M7: frameDepthModify with `RunsTo (set …)` in place of `RunsTo (modify …)` (the function argument becomes a value). -/
def M7 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (v : Nat) w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
open Expected in
/-- L1: no `Q a w → quiet w`. -/
def L1 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (P : Void IO.RealWorld → Prop) (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop),
    AdmCtx O.quiet mctx cctx →
    (∀ w, P w → O.quiet w) → (∀ w, R w → O.quiet w) →
    TeleI O P → (∀ a, TeleI O (Q a)) → TeleI O R →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Triple mctx' mref cctx' cref P (k xs b) Q (fun ex w => R w ∧ OkExc ex)) →
    Triple mctx mref cctx cref P (Lean.Meta.lambdaTelescope e k cleanup) Q (fun ex w => R w ∧ OkExc ex)
open Expected in
/-- L2: failure side without `OkExc`. -/
def L2 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (P : Void IO.RealWorld → Prop) (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop),
    AdmCtx O.quiet mctx cctx →
    (∀ w, P w → O.quiet w) → (∀ a w, Q a w → O.quiet w) → (∀ w, R w → O.quiet w) →
    TeleI O P → (∀ a, TeleI O (Q a)) → TeleI O R →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Triple mctx' mref cctx' cref P (k xs b) Q (fun _ w => R w)) →
    Triple mctx mref cctx cref P (Lean.Meta.lambdaTelescope e k cleanup) Q (fun _ w => R w)
open Expected in
/-- L3: no transfer premise for `R`. -/
def L3 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (P : Void IO.RealWorld → Prop) (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop),
    AdmCtx O.quiet mctx cctx →
    (∀ w, P w → O.quiet w) → (∀ a w, Q a w → O.quiet w) → (∀ w, R w → O.quiet w) →
    TeleI O P → (∀ a, TeleI O (Q a)) →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Triple mctx' mref cctx' cref P (k xs b) Q (fun ex w => R w ∧ OkExc ex)) →
    Triple mctx mref cctx cref P (Lean.Meta.lambdaTelescope e k cleanup) Q (fun ex w => R w ∧ OkExc ex)
open Expected in
/-- L4: the conclusion's success postcondition is `True`, not the continuation's `Q`. -/
def L4 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (P : Void IO.RealWorld → Prop) (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop),
    AdmCtx O.quiet mctx cctx →
    (∀ w, P w → O.quiet w) → (∀ a w, Q a w → O.quiet w) → (∀ w, R w → O.quiet w) →
    TeleI O P → (∀ a, TeleI O (Q a)) → TeleI O R →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Triple mctx' mref cctx' cref P (k xs b) Q (fun ex w => R w ∧ OkExc ex)) →
    Triple mctx mref cctx cref P (Lean.Meta.lambdaTelescope e k cleanup) (fun _ _ => True) (fun ex w => R w ∧ OkExc ex)
open Expected in
/-- L5: the rev2 `Keeps` statement (a different type: this is what the Triple form replaces). -/
def L5 (O : RefLawsAOps MkRefd mref cref) : Prop := Expected.lamTelescope O
open Expected in
/-- L6: no `P w → quiet w`. -/
def L6 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (P : Void IO.RealWorld → Prop) (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop),
    AdmCtx O.quiet mctx cctx →
    (∀ a w, Q a w → O.quiet w) → (∀ w, R w → O.quiet w) →
    TeleI O P → (∀ a, TeleI O (Q a)) → TeleI O R →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Triple mctx' mref cctx' cref P (k xs b) Q (fun ex w => R w ∧ OkExc ex)) →
    Triple mctx mref cctx cref P (Lean.Meta.lambdaTelescope e k cleanup) Q (fun ex w => R w ∧ OkExc ex)
/-- D1: logProf without `O.quiet w →`. -/
def D1 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (b : Bool) (msg : String) w,
    readOf sparkleSubModuleCache (endW mctx mref cctx cref (liftM (profLogIO b msg) : MetaM Unit) w) =
      readOf sparkleSubModuleCache w
/-- D2: stderrLine without the flush (the print alone). -/
def D2 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (s : String) w, O.quiet w →
    readOf sparkleSubModuleCache (endW mctx mref cctx cref (liftM (IO.eprintln s) : MetaM Unit) w) =
      readOf sparkleSubModuleCache w
/-- D3: printersMv without `O.quiet w →`. -/
def D3 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ w, ∀ ctx : PPContext, ctx.env = (readOf cref w).env →
    (∀ e : Lean.Expr, ∀ v, match Lean.ppExprWithInfos ctx e v with
      | .mk _ v' => readOf sparkleSubModuleCache v' = readOf sparkleSubModuleCache v) ∧
    (∀ n : Name, ∀ v, match Lean.ppConstNameWithInfos ctx n v with
      | .mk _ v' => readOf sparkleSubModuleCache v' = readOf sparkleSubModuleCache v)
/-- D4: printersMv with the three-ref class `OkEnv` in place of the memo class (a different, weaker-looking claim). -/
def D4 (O : RefLawsAOps MkRefd mref cref) : Prop := ∀ w, O.quiet w → OkEnv (readOf cref w).env
/-- D5: logProf without `AdmCtx`. -/
def D5 (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, ∀ (b : Bool) (msg : String) w, O.quiet w →
    readOf sparkleSubModuleCache (endW mctx mref cctx cref (liftM (profLogIO b msg) : MetaM Unit) w) =
      readOf sparkleSubModuleCache w
end Mutant

/-! ## Statements OUTSIDE the boundary: expressible Props that are NOT any new field's type -/
namespace Outside
/-- B1: an arbitrary path and mode. -/
def arbPath (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (p : System.FilePath) (m : IO.FS.Mode)
    (s : String) w, O.quiet w →
    Tools.Assume.MemoFamily.mv (endW mctx mref cctx cref
      ((liftM (IO.FS.Handle.mk p m) : MetaM IO.FS.Handle) >>= fun h =>
        (liftM (h.putStrLn s) : MetaM Unit) >>= fun _ => (liftM h.flush : MetaM Unit)) w) = Tools.Assume.MemoFamily.mv w
/-- B2: `putStrLn` on an arbitrary handle. -/
def arbHandlePut (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (h : IO.FS.Handle) (s : String) w,
    O.quiet w → Tools.Assume.MemoFamily.mv (endW mctx mref cctx cref (liftM (h.putStrLn s) : MetaM Unit) w) = Tools.Assume.MemoFamily.mv w
/-- B3: `flush` on an arbitrary handle. -/
def arbHandleFlush (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (h : IO.FS.Handle) w,
    O.quiet w → Tools.Assume.MemoFamily.mv (endW mctx mref cctx cref (liftM h.flush : MetaM Unit) w) = Tools.Assume.MemoFamily.mv w
/-- B4: `flush` of an arbitrary stream (`IO.FS.Stream` is a structure of closures). -/
def arbStreamFlush (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ (h : IO.FS.Stream) w,
    O.quiet w → Tools.Assume.MemoFamily.mv (endW mctx mref cctx cref (liftM h.flush : MetaM Unit) w) = Tools.Assume.MemoFamily.mv w
/-- B5: `ppExpr` of an arbitrary printer, unconditionally (this is `PpMvK`). -/
def arbPrinter (O : RefLawsAOps MkRefd mref cref) : Prop := Tools.ShippingGen4KWalkHelpers.PpMvK O
/-- B6: rendering a message of the class `OkMsg` (this is `MsgMvK`). -/
def msgRender (O : RefLawsAOps MkRefd mref cref) : Prop := Tools.ShippingGen4KWalkDiag.MsgMvK O
end Outside

/-! ## Vacuous model (satisfiability of the type only) -/
def vacO : RefLawsAOps MkRefd mref cref := RefLawsAOps.quietFalse MkRefd mref cref
theorem vacuous_model : Tools.Assume.MemoFamily.MemoFamily (mref := mref) (cref := cref) vacO where
  frame := by intro _ _ _ _ _ _ _ hq; exact False.elim hq
  frameCacheSet := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  frameDepthSet := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  memoGet := by intro _ _ _ _ _ _ _ hq; exact False.elim hq
  memoSet := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  memoModify := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  frameCacheModify := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  frameDepthModify := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  logProf := by intro _ _ _ _ _ _ hq; exact False.elim hq
  stderrLine := by intro _ _ _ _ _ hq; exact False.elim hq
  printersMv := by intro _ hq; exact False.elim hq
  tele :=
    { telescope := by intro _ _ _ I _ hIq _ _ _ _ w hw; exact False.elim (hIq w hw)
      lamTelescopeT := by intro _ _ _ P _ _ _ hPq _ _ _ _ _ _ _ _ _ w hw; exact False.elim (hPq w hw)
      localDecl := by intro _ _ _ I _ hIq _ _ _ _ _ w hw; exact False.elim (hIq w hw)
      letDecl := by intro _ _ _ I _ hIq _ _ _ _ _ _ w hw; exact False.elim (hIq w hw) }

/-! ## The checker -/

/-- Transitive constant closure; `thmInfo`/`defnInfo` bodies and all types are traversed; `opaqueInfo` bodies are not
(reached opaque constants are returned so the log can say so). -/
private partial def closure (env : Environment) (todo : List Name) (seen : NameSet) (opq : NameSet) :
    NameSet × NameSet :=
  match todo with
  | [] => (seen, opq)
  | n :: rest =>
    if seen.contains n then closure env rest seen opq else
    let seen := seen.insert n
    match env.find? n with
    | none => closure env rest seen opq
    | some ci =>
      let (body, opq) : List Name × NameSet := match ci with
        | .thmInfo v => (v.value.getUsedConstants.toList, opq)
        | .defnInfo v => (v.value.getUsedConstants.toList, opq)
        | .opaqueInfo _ => ([], opq.insert n)
        | _ => ([], opq)
      closure env (ci.type.getUsedConstants.toList ++ body ++ rest) seen opq

private def forbidden : List Name :=
  [`Tools.ShippingGen2.Laws, `Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND]

private def closureBad (n : Name) : CoreM (List Name × Nat) := do
  let (seen, _) := closure (← getEnv) [n] {} {}
  return (seen.toList.filter fun m => forbidden.any fun f => f.isPrefixOf m, seen.size)

/-- The projection `S.field : ∀ {mref cref} {O}, S O → T`; return `T` with `mref cref O` as given. -/
private def fieldDefEq (field : Name) (E : Name) : MetaM Bool := do
  let info ← getConstInfo field
  forallBoundedTelescope info.type (some 4) fun xs body => do
    let some mrefF := xs[0]? | throwError "{field}: no mref"
    let some crefF := xs[1]? | throwError "{field}: no cref"
    let some oF := xs[2]? | throwError "{field}: no O"
    let lvls := (← getConstInfo E).levelParams.map fun _ => levelZero
    let exp := mkConst E lvls
    let expApplied := mkApp3 exp mrefF crefF oF
    isDefEq body expApplied

elab "#memo_family_check" : command => liftTermElabM do
  let fam := `Tools.Assume.MemoFamily.MemoFamily
  let tele := `Tools.Assume.MemoFamily.MemoTele
  let pre := `Tests.Gen4.MemoFamilyCheck
  let ex := pre ++ `Expected
  let typeCases : List (Name × Name) :=
    [(fam ++ `frame, ex ++ `frame), (fam ++ `frameCacheSet, ex ++ `frameCacheSet),
     (fam ++ `frameDepthSet, ex ++ `frameDepthSet), (fam ++ `memoGet, ex ++ `memoGet),
     (fam ++ `memoSet, ex ++ `memoSet), (fam ++ `memoModify, ex ++ `memoModify),
     (fam ++ `frameCacheModify, ex ++ `frameCacheModify), (fam ++ `frameDepthModify, ex ++ `frameDepthModify),
     (tele ++ `telescope, ex ++ `telescope), (tele ++ `localDecl, ex ++ `localDecl), (tele ++ `letDecl, ex ++ `letDecl),
     (tele ++ `lamTelescopeT, ex ++ `lamTelescopeT), (fam ++ `logProf, ex ++ `logProf),
     (fam ++ `stderrLine, ex ++ `stderrLine), (fam ++ `printersMv, ex ++ `printersMv)]
  let mutCases : List (String × Name × Name) :=
    [("M1", fam ++ `memoSet, `M1), ("M2", fam ++ `memoSet, `M2), ("M3", fam ++ `memoSet, `M3),
     ("M4", fam ++ `frame, `M4), ("M5", fam ++ `memoModify, `M5), ("M6a", fam ++ `frameCacheModify, `M6a),
     ("M6b", fam ++ `frameDepthModify, `M6b), ("M7", fam ++ `frameDepthModify, `M7),
     ("L1", tele ++ `lamTelescopeT, `L1), ("L2", tele ++ `lamTelescopeT, `L2), ("L3", tele ++ `lamTelescopeT, `L3),
     ("L4", tele ++ `lamTelescopeT, `L4), ("L5", tele ++ `lamTelescopeT, `L5), ("L6", tele ++ `lamTelescopeT, `L6),
     ("D1", fam ++ `logProf, `D1), ("D2", fam ++ `stderrLine, `D2), ("D3", fam ++ `printersMv, `D3),
     ("D4", fam ++ `printersMv, `D4), ("D5", fam ++ `logProf, `D5)]
  let outCases : List Name := [`arbPath, `arbHandlePut, `arbHandleFlush, `arbStreamFlush, `arbPrinter, `msgRender]
  let newFields : List Name := [fam ++ `logProf, fam ++ `stderrLine, fam ++ `printersMv]
  -- TYPE
  let mut ok : Nat := 0
  for (f, e) in typeCases do
    unless ← fieldDefEq f e do throwError "TYPE mismatch for {f}"
    ok := ok + 1
  unless ok == 15 do throwError "TYPE count {ok} ≠ 15"
  -- MUTANT
  let mut rej : Nat := 0
  for (lbl, f, m) in mutCases do
    if ← fieldDefEq f (pre ++ `Mutant ++ m) then throwError "mutant {lbl} NOT rejected for {f}"
    rej := rej + 1
  let labels := (mutCases.map (·.1)).map (·.take 2) |>.eraseDups
  unless labels.length == 18 do throwError "mutant labels {labels} ≠ M1..M7, L1..L6, D1..D5"
  -- OUTSIDE: expressible, not defeq to any of the 3 new fields
  let mut outRej : Nat := 0
  for o in outCases do
    for f in newFields do
      if ← fieldDefEq f (pre ++ `Outside ++ o) then throwError "outside statement {o} IS the type of {f}"
      outRej := outRej + 1
  -- AXIOMS
  let dg := `Tools.ShippingGen4KWalkDiag
  let mf := `Tools.Assume.MemoFamily
  let audited : List Name :=
    [fam, tele, fam ++ `mk, tele ++ `mk, pre ++ `vacuous_model, mf ++ `FramedNM, mf ++ `SideRefNM, mf ++ `mv,
     mf ++ `OkEnvMv, mf ++ `MvInert, tele ++ `lamTelescope, dg ++ `logMvK_of, dg ++ `ppMvK_of, dg ++ `ppExpr_mv,
     dg ++ `profBlock_eq, dg ++ `profBlock_mv, dg ++ `stderrPair_mv, dg ++ `profLogIO_false, dg ++ `MsgMvK]
  let mut axOk : Nat := 0
  for n in audited do
    let axs ← collectAxioms n
    let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
    unless bad.isEmpty do throwError "{n}: axioms {bad}"
    axOk := axOk + 1
  -- CLOSURE (of the TRUSTED structures and the types they use)
  let mut clOk : Nat := 0
  for n in [fam, tele, mf ++ `OkEnvMv, mf ++ `MvInert, mf ++ `FramedNM, mf ++ `SideRefNM, mf ++ `mv] do
    let (bad, _) ← closureBad n
    unless bad.isEmpty do throwError "{n}: forbidden constants {bad}"
    clOk := clOk + 1
  -- positive controls: the same detector flags T1Hyp / T1HypND
  for c in [`Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND] do
    let (bad, _) ← closureBad c
    if bad.isEmpty then throwError "closure detector MISSED {c}"
  -- MODEL
  let mi ← getConstInfo (pre ++ `vacuous_model)
  let mut modelOk : Nat := 0
  if mi.type.getUsedConstants.contains fam then modelOk := 1
  unless modelOk == 1 do throwError "vacuous_model does not state MemoFamily"
  logInfo m!"MEMOFAMILY CHECK (rev3): TYPE {ok}/15 / MUTANT {rej}/19 variants of 18 labels (signature/defeq rejections, not semantic counterexamples) / OUTSIDE {outRej}/18 (6 statements x 3 Diag fields, none defeq) / AXIOMS {axOk} standard-only / CLOSURE {clOk} clean (+2 positive controls) / MODEL {modelOk} (vacuous quiet=False; type satisfiability only)"

#memo_family_check

end Tests.Gen4.MemoFamilyCheck

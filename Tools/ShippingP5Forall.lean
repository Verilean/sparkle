import Tools.ShippingCallWidthsChildReal
import Tools.ShippingInlTypeReads

/-! # `P5` for callees whose type is a `∀`, over the CANDIDATE inliner (unit U5a)

UNBUILT at the time of writing (worker O-INLC, branch par/o-inlc, base a230f9d1; written without
running Lean). No `sorry`, no axiom, no `native_decide`. Nothing added to `RefLaws`, `ChildLaws` or
any trust / allowed-premise list. Production unchanged; no existing file changed.

* `P5AtC` is `P5At` (Tools/ShippingCallWidthsChildReal.lean 147) with `userInlinerC` in place of
  `userInliner` (both in the `entryConst` antecedent and in the conclusion).
* `ResDeclFAt` = `ResDeclAt` plus `dD.type.isForall = true` (same class: a read of the declared
  type; the callee has at least one binder).
* `ReadConstsAt` — LOCALISED environment premise: every environment the run reads
  (`Lean.getEnv`) satisfies `ReadConstsPlain` (six `userAbbrev? env c = none` facts for the
  library constants of the reading positions). Explicit premise, NOT a guard in the candidate.

Results:

| theorem | premises | status |
|---|---|---|
| `p5AtC_of_resDeclF` | `ResDeclFAt`, `ReadConstsAt` | `P5AtC` DISCHARGED for `∀` callees (candidate inliner) |
| `resDeclAt_of_resDeclF` | `ResDeclFAt` | projection |
| `p5At_of_switch` | `SwitchF` (below), `ResDeclFAt`, `ReadConstsAt` | production `P5At`, CONDITIONAL on the switch |
| `childLink_realF` | as `childLink_real` with `P5` replaced by `SwitchF` + `ReadConstsAt` + `ResDeclFAt` | CONDITIONAL on the switch |

`SwitchF` (`userInliner env ty = userInlinerC env ty` on `∀` types) is NOT provable today and is NOT
claimed: production `userInliner` runs the `partial` `passM` (opaque) and the extern
`Expr.replace`. It becomes `rfl` only after the ruled switch (production `userInliner` defined as
the candidate). Its runtime content is (i) `passF ≈ passM` — a runtime compatibility argument, not a
kernel proof — and (ii) `replaceNoCache f e = replace f e` — OPEN, no claim. -/
namespace Tools.ShippingP5Forall
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv
open Tools.ShippingCallWidthsChildReal (ResDeclAt P5At childLink_real)
open Tools.ShippingInlCand (userInlinerC ReadConstsPlain)
open Tools.ShippingInlTypeReads (resKind_userInlinerC)

section Defs
variable (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)

/-- The declared callee's result kind AND that its type is a `∀`, for every read the entry makes
of `c`. -/
def ResDeclFAt (c : Name) (res : MixedGateBinder) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) (w1 : Void IO.RealWorld) (ci : ConstantInfo)
    (w2 : Void IO.RealWorld) (dD : DefinitionVal),
    RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 → ci = .defnInfo dD →
    machResultKind? dD.type = some res ∧ dD.type.isForall = true

/-- LOCALISED environment premise: every environment the run reads has no user abbreviation
named `Signal`, `Bool`, `BitVec`, `OfNat.ofNat`, `Nat` or `instOfNatNat`. -/
def ReadConstsAt : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) (w5 : Void IO.RealWorld) (envR : Environment)
    (w6 : Void IO.RealWorld),
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
    ReadConstsPlain envR

/-- `P5At` over the CANDIDATE inliner. -/
def P5AtC (c : Name) (res : MixedGateBinder) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) (w1 : Void IO.RealWorld) (ci : ConstantInfo)
    (w2 w5 : Void IO.RealWorld) (envR : Environment) (w6 : Void IO.RealWorld)
    (dD : DefinitionVal),
    RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
    ci = .defnInfo dD →
    entryConst true false [] ci (instancePredicate envR) (userInlinerC envR) (structEnv envR) ≠ ci →
    machResultKind? (userInlinerC envR dD.type) = some res

end Defs

/-- **The switch hypothesis** (NOT provable today, NOT claimed): production `userInliner` agrees
with the candidate on `∀` types. `rfl` only after the ruled switch. -/
def SwitchF : Prop :=
  ∀ (env : Environment) (ty : Lean.Expr), ty.isForall = true → userInliner env ty = userInlinerC env ty

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

theorem resDeclAt_of_resDeclF {c : Name} {res : MixedGateBinder}
    (RD : ResDeclFAt mref cref c res) : ResDeclAt mref cref c res :=
  fun mctx cctx w1 ci w2 dD get hci => (RD mctx cctx w1 ci w2 dD get hci).1

/-- **`P5AtC` discharged for `∀` callees.** No `partial` value, no extern, no law; the only
environment fact is the localised `ReadConstsAt`. The `entryConst` antecedent is not used (the kind
is kept on every run, unfolding or not). -/
theorem p5AtC_of_resDeclF {c : Name} {res : MixedGateBinder}
    (RD : ResDeclFAt mref cref c res) (RC : ReadConstsAt mref cref) :
    P5AtC mref cref c res := by
  intro mctx cctx w1 ci w2 w5 envR w6 dD get henv hci _
  obtain ⟨hres, hf⟩ := RD mctx cctx w1 ci w2 dD get hci
  exact resKind_userInlinerC envR (RC mctx cctx w5 envR w6 henv) dD.type hf hres

/-- Production `P5At`, CONDITIONAL on the switch hypothesis `SwitchF`. -/
theorem p5At_of_switch {c : Name} {res : MixedGateBinder} (hsw : SwitchF)
    (RD : ResDeclFAt mref cref c res) (RC : ReadConstsAt mref cref) :
    P5At mref cref c res := by
  intro mctx cctx w1 ci w2 w5 envR w6 dD get henv hci _
  obtain ⟨hres, hf⟩ := RD mctx cctx w1 ci w2 dD get hci
  rw [hsw envR dD.type hf]
  exact resKind_userInlinerC envR (RC mctx cctx w5 envR w6 henv) dD.type hf hres

/-- `childLink_real` with `P5` replaced by the switch hypothesis plus the localised environment
premise, for callees whose declared type is a `∀`. CONDITIONAL on `SwitchF`. -/
theorem childLink_realF {mctx : Meta.Context} {cctx : Core.Context}
    {c : Name} {sc : MachineShape} {res : MixedGateBinder} {y : Res}
    (entry : MachineDefines mctx mref cctx cref c sc)
    (RD : ResDeclFAt mref cref c res) (RC : ReadConstsAt mref cref) (hsw : SwitchF)
    (hy : RealChild mref cref c y) :
    ∃ (dE : DefinitionVal) (senv : StructEnv),
      machineShape? false [] (.defnInfo dE) senv = some sc ∧
      machResultKind? dE.type = some res :=
  childLink_real entry (resDeclAt_of_resDeclF RD) (p5At_of_switch hsw RD RC) hy

end Tools.ShippingP5Forall

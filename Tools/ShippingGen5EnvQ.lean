import Tools.ShippingGen5Env
import Tools.ShippingGen5T1ND
import Tools.ShippingGen5RunReads
set_option autoImplicit false
-- NOT BUILT yet.

/-! # DG-ENV unit (d): TQ connection lemmas, CONDITIONAL (scripts/gen5/DG_ENV_FREEZE.md rev2.2 §4.5, par/gen5-t2 4c841bba)

Two NAMED premises, supplied nowhere: `QuietStrength L L' env₀` (an `L'` whose `quiet` is `quiet ∧ ReadsAt env₀` is
GIVEN; it is not built) and `AdmDown L L'` (C-ADM new ⇒ old, OPEN).
(Q1-Q6) new ⇒ old transport of `quiet`, `ReadsAt`, `JQ`, `RealChildA` (induction on its `cache` field), `CacheInvA`,
`JQC`. (Q7) `MachineClosesAtA` old ⇒ new (its `JQC` is negative). (Q8) `T1HypND` old ⇒ new: it KEEPS the old
all-world `defines` (no switch to `MachineDefinesR`, no `defines` supply). (Q9) `Start L` + E1 give `JQ` at `L'`
(no cache half). (Q10) RR1 at `L'.O` on the SAME `coreHead` run; `hA'` stays a premise; no `Start L'`, no FG wrapper.

No new law; no shared-definition change (`T1Hyp`/`T1HypND` unchanged). Q1-Q9 use no `RefLawsAOps` field other than
`quiet` and no `RefLawsATele` field; Q10 uses `L'.O`'s fields through RR1 (instantiation at the given `L'`). Audit in
Tests/Gen5/EnvQCheck.lean. Not M5 or FG completion. -/
namespace Tools.ShippingGen5EnvQ
open Lean
open Sparkle.Core.Domain (DomainConfig)
open Sparkle.Compiler.Elab (MachineShape)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildVCA (JQ)
open Tools.ShippingChildCacheA (RealChildA CacheInvA JQC)
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingGen2 (Laws Start Pkgs Pkg T1HypND)
open Tools.ShippingGen5Env (ReadsAt readsAt_self)

variable {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
  {cref : ST.Ref IO.RealWorld Core.State}

/-- TQ's relation between two law bundles (the body of `EnvLawsQ`, §4.4.2). -/
def QuietStrength (L L' : Laws mref cref) (env₀ : Environment) : Prop :=
  ∀ w, L'.O.quiet w ↔ (L.O.quiet w ∧ ReadsAt env₀ cref w)

/-- C-ADM new ⇒ old as a named premise (OPEN, §4.4.7 (c)). -/
def AdmDown (L L' : Laws mref cref) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L'.O.quiet mctx cctx → AdmCtx L.O.quiet mctx cctx

/-- (Q1) -/
theorem quiet_down {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    {w : Void IO.RealWorld} (h : L'.O.quiet w) : L.O.quiet w :=
  ((hq w).mp h).1

/-- (Q2) -/
theorem readsAt_of_quiet {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    {w : Void IO.RealWorld} (h : L'.O.quiet w) : ReadsAt env₀ cref w :=
  ((hq w).mp h).2

/-- (Q3) -/
theorem jq_down {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    {D : Nat} {w : Void IO.RealWorld} (h : JQ L'.O.quiet D w) : JQ L.O.quiet D w := by
  unfold JQ at h ⊢
  exact ⟨quiet_down hq h.1, h.2⟩

/-- (Q4) by induction on `RealChildA` (its `cache` field is the recursive occurrence). -/
theorem realChildA_down {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') {c : Name} {r : Res} (h : RealChildA L'.O c r) : RealChildA L.O c r := by
  induction h with
  | run mctx cctx w w' adm _ synth quiet hr ih =>
    exact .run mctx cctx w w' (hd _ _ adm) (fun c' r' hc => ih c' r' hc) synth (quiet_down hq quiet) hr

/-- (Q5) -/
theorem cacheInvA_down {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') {m : Std.HashMap Name Res} (h : CacheInvA L'.O m) : CacheInvA L.O m :=
  fun c r hc => realChildA_down hq hd (h c r hc)

/-- (Q6) -/
theorem jqc_down {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') {D : Nat} {w : Void IO.RealWorld} (h : JQC L'.O D w) : JQC L.O D w :=
  ⟨jq_down hq h.1, cacheInvA_down hq hd h.2⟩

/-- (Q7) the negative `JQC` of `MachineClosesAtA` (ChildRunAKids.lean:158-163). -/
theorem closesA_up {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') {mctx : Meta.Context} {cctx : Core.Context} {c : Name} {shape : MachineShape}
    (h : MachineClosesAtA L.O mctx cctx c shape) : MachineClosesAtA L'.O mctx cctx c shape := by
  intro tenv b n w r w' hw hn hr
  exact @h tenv b n w r w' (jqc_down hq hd hw) hn hr

/-- (Q8) C-RESTRICT's supply rows for the dec-free hypotheses (`defines`: contexts only, the OLD all-world form is
kept; `closes`: Q7). -/
theorem t1HypND_up {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L P Reach DataOk) : T1HypND L' P Reach DataOk where
  pkg := H.pkg
  defines c hR q hP mctx cctx hA := H.defines c hR q hP mctx cctx (hd _ _ hA)
  closes c hR q hP mctx cctx hA := closesA_up hq hd (H.closes c hR q hP mctx cctx (hd _ _ hA))
  closed := H.closed

/-- (Q9) the start: `Start L` and E1 give `JQ` at `L'` (no cache half needed, §4.4.7 (b)). -/
theorem jq_start {L L' : Laws mref cref} {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld}
    (hq : QuietStrength L L' (envAt cref w₀)) (hS : Start L mctx cctx w₀) : JQ L'.O.quiet 0 w₀ := by
  obtain ⟨-, hj, -⟩ := hS
  unfold JQ at hj ⊢
  exact ⟨(hq w₀).mpr ⟨hj.1, readsAt_self cref w₀⟩, hj.2⟩

/-- (Q10) the after-head entry: RR1 at `L'.O` with `Or.inl rfl`, on the same `coreHead` run. Uses `L'`'s laws
(instantiation, the given `L'`); `hA'` (C-ADM old ⇒ new at the top context) is a premise. -/
theorem head_jqc_start {L L' : Laws mref cref} {mctx : Meta.Context} {cctx : Core.Context}
    {w₀ w1 : Void IO.RealWorld} {X : Name} {s : Tools.ShippingEntryReadsLinked.CoreSaved}
    (hq : QuietStrength L L' (envAt cref w₀)) (hA' : AdmCtx L'.O.quiet mctx cctx) (hS : Start L mctx cctx w₀)
    (hh : RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref w₀ s w1) :
    JQC L'.O 1 w1 ∧ ReadsAt (envAt cref w₀) cref w1 := by
  have h : JQC L'.O (0 + 1) w1 :=
    Tools.ShippingGen5RunReads.coreHead_jqcA L'.O hA' (jq_start hq hS) (Or.inl rfl) hh
  exact ⟨h, readsAt_of_quiet hq h.1.1⟩

end Tools.ShippingGen5EnvQ

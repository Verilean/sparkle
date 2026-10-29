import Tools.ShippingGen3ArgSupply
import Tests.Gen3.ExpectedType        -- checkExpected / checkMutant / checkAxioms / cmpTele / stmtOf
import Tests.Gen3.ArgWidthSrcCheck    -- SA0/SA1 synthetic fixtures: shSyn, senvI, senvS, senvBad
set_option autoImplicit false
-- NOT BUILT: written without running Lean (agent rule). No `sorry`, no `axiom`, no `native_decide`.

/-! # Checks for Tools/ShippingGen3ArgSupply.lean (SRC-ARGW SC0 / SC1 / LK0; SRC_ARGW_SUPPLY_FREEZE.md rev0)

CONDITIONAL / NOT ACTUAL-RUN SUPPLY / NOT FG COMPLETION. Every control below is on hand-written data or under
explicit premises; nothing here is a reader run, a package of the corpus, or a supplier of KD/LK/ENV/VT/P5/O1/O2.

1. **Expected types** (Tests/Gen3/ExpectedType.lean): every SC0/SC1/LK0 declaration against an INDEPENDENT `Exp_…`
   restatement of the freeze text (§1, §2, §3.1), and meaning-changing mutants `Mut_…` that must be REJECTED.
   `PhKindingLaws` is a structure: its CONSTRUCTOR type is compared (`checkCtor`). SC1's mutant with the PRODUCTION
   `machineShape?` premise is rejected: SC1 is on the fuel model only (O1/O2 not assumed).
2. **SC0 data controls** on SA0's synthetic `shSyn` (layout `lets := 2`, so `closingNDecl = 1`):
   * POSITIVE (CONDITIONAL): `ShapeSigProv` / `ShapeArgKinds` hold for `senvI`; with `senv = senv₀ = senvI`
     (ENV by `rfl`), `argWidthAt_of_read` gives `∀ k, ArgWidthAt P p k` for every `P`, `p` with this shape and
     `kD = 1`, UNDER the premise `hTEL` (VT ∧ P5 is NOT supplied here);
   * NEGATIVE: `ShapeSigProv` fails without an `inst` signature at an `.ord` entry (`senvS`); `ShapeArgKinds`
     fails for a 16-bit callee kind (`senvBad`);
   * VACUOUS (NOT supply): at a `.mem` origin `ShapeSigProv` holds for ANY table (the entry is excluded by `hnone`).
3. **LK0 evaluation controls**: `phKind` on `machIn` (counted from the LAST input), `machLet`, a non-placeholder.
4. Axioms: only `propext`, `Classical.choice`, `Quot.sound` (machine assertion). -/
set_option maxHeartbeats 4000000

namespace Tests.Gen3.ArgSupplyCheck
open Lean Meta Elab Command
open Sparkle.Compiler.Elab (StructEnv MachineShape MixedGateBinder MachRead machIn machLet)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Core.Domain
open Tools.ShippingMachineEntry (kindTy)
open Tools.ShippingGen2 (Pkg Pkgs callArgsOkAt)
open Tools.ShippingGen3ArgWidthSrc
open Tools.ShippingCallWidthsEntry (closingNDecl)
open Tools.ShippingGen3ArgSupply
open Tests.Gen3.ExpectedType (checkExpected checkMutant checkAxioms cmpTele stmtOf)
open Tests.Gen3.ArgWidthSrcCheck (shSyn senvI senvS senvBad)

/-! ## 1. Expected types: independent restatements of the freeze text -/

def Exp_ShapeSigProv (senv : StructEnv) (sp : MachineShape) : Prop :=
  sp.instOrigins.length = sp.insts.length ∧
  ∀ k (hk : k < sp.insts.length), (sp.instOrigins.getD k .ord).child? = none →
    ∃ kinds, SigKindsAt senv sp k (sp.insts[k]).1 kinds

def Exp_ShapeArgKinds (senv : StructEnv) (sp : MachineShape) : Prop :=
  ∀ k, ArgKindsAt senv sp (closingNDecl sp) k ∧ ArgKindsAtS senv sp (closingNDecl sp) k

def Exp_SigEq (s s₀ : StructEnv) (c : Name) : Prop := s.inst c = s₀.inst c ∧ s.instS c = s₀.instS c

def Exp_CalleeTeleAll {ι : Type} {dom : ι → DomainConfig} (senv : StructEnv) (c : Name) (q : Pkg ι dom) : Prop :=
  CalleeTeleAt senv c q ∧ CalleeTeleAtS senv c q

def Exp_argWidthAt_of_read : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p : Pkg ι dom) {senv senv₀ : StructEnv}
    (hKD  : p.kD = closingNDecl p.d.shape)
    (hSIG : ShapeSigProv senv p.d.shape)
    (hARG : ShapeArgKinds senv p.d.shape)
    (hENV : ∀ c q, P c = some q → SigEq senv senv₀ c)
    (hTEL : ∀ c q, P c = some q → CalleeTeleAll senv₀ c q),
    ∀ k, ArgWidthAt P p k

def Exp_shapeSigProv_of_fuel : Prop :=
  ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {senv : StructEnv} {ai : Bool}
    {sp : MachineShape} (h : Tools.ShippingReaderFuel.machineShapeF n sm ps ci senv ai = some (some sp)),
    ShapeSigProv senv sp

def Exp_phKind (bs : List (Name × MixedGateBinder)) (st : MachRead) : Lean.Expr → Option MixedGateBinder
  | .fvar ⟨.num (.str .anonymous "_machIn") i⟩   => (bs.reverse[i]?).map (·.2)
  | .fvar ⟨.num (.str .anonymous "_machSlot") i⟩ => st.kinds[i]?
  | .fvar ⟨.num (.str .anonymous "_machLet") j⟩  => (st.lets[j]?).map (·.2.1)
  | .fvar ⟨.num (.str .anonymous "_machInst") k⟩ => (st.insts[k]?).map (·.2.2)
  | _ => none

def Exp_PhKinding : Type := (Lean.Expr → Option MixedGateBinder) → Lean.Expr → MixedGateBinder → Prop

/-- The constructor type of `PhKindingLaws` (parameter implicit, fields `var` / `uniq` / `mono`). -/
def Exp_PhKindingLaws_mk : Prop :=
  ∀ {HK : PhKinding}
    (var  : ∀ (Γ : Lean.Expr → Option MixedGateBinder) (e : Lean.Expr) (k : MixedGateBinder),
      (phKind [] {} e).isSome ∨ (∃ x, e = .fvar x) → (HK Γ e k ↔ Γ e = some k))
    (uniq : ∀ (Γ : Lean.Expr → Option MixedGateBinder) (e : Lean.Expr) (k k' : MixedGateBinder),
      HK Γ e k → HK Γ e k' → k = k')
    (mono : ∀ (Γ Γ' : Lean.Expr → Option MixedGateBinder) (e : Lean.Expr) (k : MixedGateBinder),
      (∀ (x : Lean.Expr) (kx : MixedGateBinder), Γ x = some kx → Γ' x = some kx) → HK Γ e k → HK Γ' e k),
    PhKindingLaws HK

def Exp_LetKindOk (HK : PhKinding) (bs : List (Name × MixedGateBinder)) (st : MachRead) : Prop :=
  ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) →
    HK (phKind bs st) v kd

/-! ### Meaning-changing mutants (each must be REJECTED) -/

/-- the alignment conjunct dropped -/
def Mut_ShapeSigProv_noLen (senv : StructEnv) (sp : MachineShape) : Prop :=
  ∀ k (hk : k < sp.insts.length), (sp.instOrigins.getD k .ord).child? = none →
    ∃ kinds, SigKindsAt senv sp k (sp.insts[k]).1 kinds

/-- origin ignored: every entry asked for an `inst` signature -/
def Mut_ShapeSigProv_inst (senv : StructEnv) (sp : MachineShape) : Prop :=
  sp.instOrigins.length = sp.insts.length ∧
  ∀ k (hk : k < sp.insts.length), (sp.instOrigins.getD k .ord).child? = none →
    ∃ kinds res, senv.inst (sp.insts[k]).1 = some (kinds, res)

/-- the `instS` half dropped -/
def Mut_ShapeArgKinds_noS (senv : StructEnv) (sp : MachineShape) : Prop :=
  ∀ k, ArgKindsAt senv sp (closingNDecl sp) k

/-- `instS` not compared -/
def Mut_SigEq_instOnly (s s₀ : StructEnv) (c : Name) : Prop := s.inst c = s₀.inst c

/-- the `instS` callee half dropped -/
def Mut_CalleeTeleAll_noS {ι : Type} {dom : ι → DomainConfig} (senv : StructEnv) (c : Name) (q : Pkg ι dom) :
    Prop :=
  CalleeTeleAt senv c q

/-- the callee half read at the PARENT's table `senv` instead of `senv₀` -/
def Mut_argWidthAt_of_read_telSenv : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p : Pkg ι dom) {senv senv₀ : StructEnv}
    (hKD  : p.kD = closingNDecl p.d.shape)
    (hSIG : ShapeSigProv senv p.d.shape)
    (hARG : ShapeArgKinds senv p.d.shape)
    (hENV : ∀ c q, P c = some q → SigEq senv senv₀ c)
    (hTEL : ∀ c q, P c = some q → CalleeTeleAll senv c q),
    ∀ k, ArgWidthAt P p k

/-- the conclusion weakened to entry 0 -/
def Mut_argWidthAt_of_read_k0 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p : Pkg ι dom) {senv senv₀ : StructEnv}
    (hKD  : p.kD = closingNDecl p.d.shape)
    (hSIG : ShapeSigProv senv p.d.shape)
    (hARG : ShapeArgKinds senv p.d.shape)
    (hENV : ∀ c q, P c = some q → SigEq senv senv₀ c)
    (hTEL : ∀ c q, P c = some q → CalleeTeleAll senv₀ c q),
    ArgWidthAt P p 0

/-- the PRODUCTION reader as premise (this is the O1/O2 link, NOT claimed by SC1) -/
def Mut_shapeSigProv_of_fuel_prod : Prop :=
  ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {senv : StructEnv} {ai : Bool}
    {sp : MachineShape} (h : Sparkle.Compiler.Elab.machineShape? sm ps ci senv ai = some sp),
    ShapeSigProv senv sp

/-- inputs counted from the FIRST instead of the last -/
def Mut_phKind_noRev (bs : List (Name × MixedGateBinder)) (st : MachRead) : Lean.Expr → Option MixedGateBinder
  | .fvar ⟨.num (.str .anonymous "_machIn") i⟩   => (bs[i]?).map (·.2)
  | .fvar ⟨.num (.str .anonymous "_machSlot") i⟩ => st.kinds[i]?
  | .fvar ⟨.num (.str .anonymous "_machLet") j⟩  => (st.lets[j]?).map (·.2.1)
  | .fvar ⟨.num (.str .anonymous "_machInst") k⟩ => (st.insts[k]?).map (·.2.2)
  | _ => none

/-- not history-carrying: the context is the EMPTY state's -/
def Mut_LetKindOk_emptyCtx (HK : PhKinding) (bs : List (Name × MixedGateBinder)) (st : MachRead) : Prop :=
  ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) →
    HK (phKind bs {}) v kd

/-- `mono` in the wrong direction -/
def Mut_PhKindingLaws_mk_monoRev : Prop :=
  ∀ {HK : PhKinding}
    (var  : ∀ (Γ : Lean.Expr → Option MixedGateBinder) (e : Lean.Expr) (k : MixedGateBinder),
      (phKind [] {} e).isSome ∨ (∃ x, e = .fvar x) → (HK Γ e k ↔ Γ e = some k))
    (uniq : ∀ (Γ : Lean.Expr → Option MixedGateBinder) (e : Lean.Expr) (k k' : MixedGateBinder),
      HK Γ e k → HK Γ e k' → k = k')
    (mono : ∀ (Γ Γ' : Lean.Expr → Option MixedGateBinder) (e : Lean.Expr) (k : MixedGateBinder),
      (∀ (x : Lean.Expr) (kx : MixedGateBinder), Γ' x = some kx → Γ x = some kx) → HK Γ e k → HK Γ' e k),
    PhKindingLaws HK

/-- a width-only (`Nat`-indexed) judgment instead of a kind-indexed one -/
def Mut_PhKinding_width : Type := (Lean.Expr → Option MixedGateBinder) → Lean.Expr → Nat → Prop

/-- A structure's constructor type against an expected `Prop` statement. -/
def checkCtor (ctor exp : Name) : MetaM Unit := do
  let ci ← getConstInfo ctor
  cmpTele s!"{ctor}" ci.type (← stmtOf exp)
  logInfo m!"GEN3 TYPE OK {ctor} against {exp}"

/-- A mutant of a constructor type must be rejected. -/
def checkCtorMutant (ctor mt : Name) : MetaM Unit := do
  let a := (← getConstInfo ctor).type
  let e ← stmtOf mt
  let accepted ← withoutModifyingState do
    try
      cmpTele s!"{ctor} vs mutant {mt}" a e
      pure true
    catch _ => pure false
  if accepted then
    throwError "GEN3 MUTANT ACCEPTED: {mt} matches {ctor}"
  if (← withoutModifyingState (isDefEq a e)) then
    throwError "GEN3 MUTANT ACCEPTED (isDefEq of the whole statements): {mt} vs {ctor}"
  logInfo m!"GEN3 MUTANT REJECTED {mt} (against {ctor})"

run_cmd liftTermElabM do
  for (t, e) in [(``ShapeSigProv, ``Exp_ShapeSigProv), (``ShapeArgKinds, ``Exp_ShapeArgKinds),
      (``SigEq, ``Exp_SigEq), (``CalleeTeleAll, ``Exp_CalleeTeleAll),
      (``argWidthAt_of_read, ``Exp_argWidthAt_of_read), (``shapeSigProv_of_fuel, ``Exp_shapeSigProv_of_fuel),
      (``phKind, ``Exp_phKind), (``PhKinding, ``Exp_PhKinding), (``LetKindOk, ``Exp_LetKindOk)] do
    checkExpected t e
  checkCtor ``PhKindingLaws.mk ``Exp_PhKindingLaws_mk
  for (t, m) in [(``ShapeSigProv, ``Mut_ShapeSigProv_noLen), (``ShapeSigProv, ``Mut_ShapeSigProv_inst),
      (``ShapeArgKinds, ``Mut_ShapeArgKinds_noS), (``SigEq, ``Mut_SigEq_instOnly),
      (``CalleeTeleAll, ``Mut_CalleeTeleAll_noS), (``argWidthAt_of_read, ``Mut_argWidthAt_of_read_telSenv),
      (``argWidthAt_of_read, ``Mut_argWidthAt_of_read_k0),
      (``shapeSigProv_of_fuel, ``Mut_shapeSigProv_of_fuel_prod), (``phKind, ``Mut_phKind_noRev),
      (``LetKindOk, ``Mut_LetKindOk_emptyCtx), (``PhKinding, ``Mut_PhKinding_width)] do
    checkMutant t m
  checkCtorMutant ``PhKindingLaws.mk ``Mut_PhKindingLaws_mk_monoRev
  -- the checker itself: an expected statement against its own mutant must fail too
  checkMutant ``Exp_ShapeSigProv ``Mut_ShapeSigProv_noLen

/-! ## 2. SC0 data controls (SYNTHETIC data; CONDITIONAL on `hTEL`; not a run, not supply) -/

/-- SA0's `shSyn` with `lets := 2` in the layout: `closingNDecl = 4 - 1 - 0 - 2 = 1`, the row index of SA0's controls. -/
def shSyn2 : MachineShape := { shSyn with layout := { shSyn.layout with lets := 2 } }
/-- The same entry with a memory origin. -/
def shSynM2 : MachineShape := { shSyn2 with instOrigins := [.mem false 4 8] }

theorem shSyn2_nDecl : closingNDecl shSyn2 = 1 := by first | rfl | decide

theorem argKindsAt_ge {senv : StructEnv} {sp : MachineShape} {nDecl k : Nat} (h : sp.insts.length ≤ k) :
    ArgKindsAt senv sp nDecl k := by
  intro c js r kinds res h1 _
  rw [List.getElem?_eq_none_iff.mpr h] at h1
  cases h1

theorem argKindsAtS_ge {senv : StructEnv} {sp : MachineShape} {nDecl k : Nat} (h : sp.insts.length ≤ k) :
    ArgKindsAtS senv sp nDecl k := by
  intro c js r kinds ty h1 _
  rw [List.getElem?_eq_none_iff.mpr h] at h1
  cases h1

/-- **DATA CONTROL (SIG, positive)**: the `.ord` entry has its `inst` signature in `senvI`. -/
theorem sig_shSyn2 : ShapeSigProv senvI shSyn2 := by
  refine And.intro rfl ?_
  intro k hk _
  have hl : shSyn2.insts.length = 1 := rfl
  have hk0 : k = 0 := by omega
  subst hk0
  exact ⟨[.domain, .bits 8, .bool],
    (show ∃ res, senvI.inst `f = some ([.domain, .bits 8, .bool], res) from ⟨.bits 4, rfl⟩)⟩

/-- **DATA CONTROL (LK, positive)**: the argument lets have the callee's kinds at `closingNDecl`; the `instS`
half is VACUOUS for `senvI` (no structure signature). -/
theorem argk_shSyn2 : ShapeArgKinds senvI shSyn2 := by
  intro k
  cases k with
  | zero =>
    refine ⟨argKindsAt_intro (c0 := `f) (js0 := [0, 1]) (r0 := .bits 4) (kinds0 := [.domain, .bits 8, .bool])
      (res0 := .bits 4) rfl rfl ?_, ?_⟩
    · first | decide | rfl
    · intro c js r kinds ty _ h2
      have e : senvI.instS c = none := rfl
      rw [e] at h2
      cases h2
  | succ k =>
    have hl : shSyn2.insts.length ≤ k + 1 := by
      have hl1 : shSyn2.insts.length = 1 := rfl
      omega
    exact ⟨argKindsAt_ge hl, argKindsAtS_ge hl⟩

/-- **DATA CONTROL (SC0, positive, CONDITIONAL on `hTEL`)**: with `senv = senv₀ = senvI` (ENV by `rfl`), every
package with this shape and `kD = 1` satisfies `ArgWidthAt P` at every entry. VT ∧ P5 (`hTEL`) is a PREMISE. -/
theorem ctl_read_positive {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p : Pkg ι dom)
    (hp : p.d.shape = shSyn2) (hkD : p.kD = 1)
    (hTEL : ∀ c q, P c = some q → CalleeTeleAll senvI c q) : ∀ k, ArgWidthAt P p k := by
  have hKD : p.kD = closingNDecl p.d.shape := by
    rw [hkD, hp, shSyn2_nDecl]
  have hSIG : ShapeSigProv senvI p.d.shape := by
    rw [hp]
    exact sig_shSyn2
  have hARG : ShapeArgKinds senvI p.d.shape := by
    rw [hp]
    exact argk_shSyn2
  exact argWidthAt_of_read P p (senv := senvI) (senv₀ := senvI) hKD hSIG hARG
    (fun _ _ _ => And.intro rfl rfl) hTEL

/-- **NEGATIVE (SIG)**: an `.ord` entry without an `inst` signature fails `ShapeSigProv`. -/
theorem ctl_sig_missing : ¬ ShapeSigProv senvS shSyn2 := by
  intro h
  obtain ⟨kinds, hs⟩ := h.2 0 (by decide) rfl
  obtain ⟨res, h2⟩ := hs
  have e : senvS.inst `f = none := rfl
  have hn : (shSyn2.insts[0]'(by decide)).1 = `f := rfl
  simp only [hn, e] at h2
  cases h2

/-- **NEGATIVE (LK)**: a 16-bit callee kind fails `ShapeArgKinds` (so SC0 cannot be applied). -/
theorem ctl_argKinds_bad : ¬ ShapeArgKinds senvBad shSyn2 := by
  intro h
  have h1 := (h 0).1 `f [0, 1] (.bits 4) [.domain, .bits 16, .bool] (.bits 4) rfl rfl
  exact absurd h1 (by decide)

/-- **VACUOUS (NOT supply)**: at a `.mem` origin `ShapeSigProv` holds for ANY table: the entry is excluded by
`hnone` (its `child?` is the memory module), so SC0 says nothing about memory entries. -/
theorem ctl_sig_mem_vacuous (senv : StructEnv) : ShapeSigProv senv shSynM2 := by
  refine And.intro rfl ?_
  intro k hk hn
  have hl : shSynM2.insts.length = 1 := rfl
  have hk0 : k = 0 := by omega
  subst hk0
  first
    | exact absurd hn (fun h => Option.noConfusion h)
    | exact absurd hn (by simp [shSynM2, shSyn2, shSyn, Sparkle.Compiler.MachInstOrigin.InstOrigin.child?])
    | cases hn

run_cmd logInfo "GEN3 VACUOUS: ctl_sig_mem_vacuous holds for every table (memory entries are outside `hnone`). It carries NO width and is NOT supply."
run_cmd logInfo "GEN3 CONDITIONAL: ctl_read_positive is under the premise hTEL (VT ∧ P5); SC0/SC1 are not actual-run supply and not FG completion."

/-! ## 3. LK0 evaluation controls (`phKind`) -/

/-- `_machIn 0` is the LAST peeled input. -/
theorem ctl_phKind_in : phKind [(`a, .bits 8), (`b, .bool)] {} (machIn 0) = some .bool := by
  first | rfl | decide

/-- `_machLet j` reads the stored let kind. -/
theorem ctl_phKind_let :
    phKind [] { lets := #[(`x, .bits 4, .bvar 0)] } (machLet 0) = some (.bits 4) := by
  first | rfl | decide

/-- A non-placeholder has no kind. -/
theorem ctl_phKind_other : phKind [] {} (.bvar 0) = none := by
  first | rfl | decide

/-! ## 4. Axioms -/

#print axioms Tools.ShippingGen3ArgSupply.calleeTeleAt_of_eq
#print axioms Tools.ShippingGen3ArgSupply.calleeTeleAtS_of_eq
#print axioms Tools.ShippingGen3ArgSupply.callArgsOk_of_sigKinds
#print axioms Tools.ShippingGen3ArgSupply.argWidthAt_of_read
#print axioms Tools.ShippingGen3ArgSupply.sigKindsAt_of_originTAt
#print axioms Tools.ShippingGen3ArgSupply.shapeSigProv_of_fuel
#print axioms ctl_read_positive

run_cmd liftTermElabM do
  for n in [``Tools.ShippingGen3ArgSupply.calleeTeleAt_of_eq, ``Tools.ShippingGen3ArgSupply.calleeTeleAtS_of_eq,
      ``Tools.ShippingGen3ArgSupply.callArgsOk_of_sigKinds, ``Tools.ShippingGen3ArgSupply.argWidthAt_of_read,
      ``Tools.ShippingGen3ArgSupply.sigKindsAt_of_originTAt, ``Tools.ShippingGen3ArgSupply.shapeSigProv_of_fuel,
      ``shSyn2_nDecl, ``argKindsAt_ge, ``argKindsAtS_ge, ``sig_shSyn2, ``argk_shSyn2, ``ctl_read_positive,
      ``ctl_sig_missing, ``ctl_argKinds_bad, ``ctl_sig_mem_vacuous, ``ctl_phKind_in, ``ctl_phKind_let,
      ``ctl_phKind_other] do
    checkAxioms n

end Tests.Gen3.ArgSupplyCheck

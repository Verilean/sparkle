import Tools.ShippingGen3ArgWidthSrc        -- SA0/SA1: ArgKindsAt(S), CalleeTeleAt(S), argWidth_of_halves(S), SigKindsAt, ArgWidthAt
import Tools.ShippingCallWidthsEntry        -- closingNDecl (:62-63)
import Tools.ShippingReaderFuelShapeProv    -- machineShapeF_instOrigins_length, instOrigins_getD_eq, machineShapeF_originT
set_option autoImplicit false
-- NOT BUILT: written without running Lean (agent rule). No `sorry`, no `axiom`, no `native_decide`.

/-! # SRC-ARGW SC0 / SC1 / LK0 (scripts/gen3/SRC_ARGW_SUPPLY_FREEZE.md rev0 at be4e0b9b, §1, §2, §3.1, §5)

CONDITIONAL INTERMEDIATE WORK ONLY. Nothing here is an actual-run supply, nothing here completes FG or SRC-ARGW
(completion = §1's target for every successful run with every supplier proved). No shared definition is edited
(`T1Hyp`, `ChildShips`, `DataOkB`, FG, `callArgsOkAt`, the compiler are unchanged).

* **SC0** (§1, C-CORE, pure). The four shared definitions `ShapeSigProv` / `ShapeArgKinds` / `SigEq` /
  `CalleeTeleAll` (text of §1) and `argWidthAt_of_read`: `∀ k, ArgWidthAt P p k` FROM the named suppliers
  `hKD` / `hSIG` / `hARG` / `hENV` / `hTEL`, all EXPLICIT hypotheses. Sufficiency only: none of the suppliers is
  proved here, and nothing says they hold for any run (KD, LK, ENV, VT, P5 are owned elsewhere, §4/§5).
* **SC1** (§2, the missing projection). `shapeSigProv_of_fuel`: a successful FUEL-model result
  `machineShapeF n sm ps ci senv ai = some (some sp)` gives `ShapeSigProv senv sp`. A projection of
  `machineShapeF_instOrigins_length` / `instOrigins_getD_eq` / `machineShapeF_originT`
  (Tools/ShippingReaderFuelShapeProv.lean). Stated on the FUEL MODEL ONLY: the O1/O2 boundary
  (`ShapeFuelBridge`, production `machineShape?` ↦ fuel shape; §2 / §5 D2, owned by DG-COVER) is NOT assumed and
  NOT stated here, so SC1 says nothing about production `machineShape?`.
* **LK0** (§3.1, definitions only). `phKind`, `PhKinding`, `PhKindingLaws`, `LetKindOk` as in the freeze text
  (binder types annotated; meaning unchanged). No theorem about them: preservation (LK1), placement (LK2) and the
  `HK` instantiation (LK3) wait for rev1 types. -/
namespace Tools.ShippingGen3ArgSupply
open Lean
open Sparkle.Compiler.Elab (StructEnv MachineShape MixedGateBinder MachRead)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Core.Domain
open Tools.ShippingGen2 (Pkg Pkgs callArgsOkAt)
open Tools.ShippingGen3ArgWidthSrc
open Tools.ShippingCallWidthsEntry (closingNDecl)

variable {ι : Type} {dom : ι → DomainConfig}

/-! ## SC0: the shared definitions (§1 text) -/

def ShapeSigProv (senv : StructEnv) (sp : MachineShape) : Prop :=
  sp.instOrigins.length = sp.insts.length ∧
  ∀ k (hk : k < sp.insts.length), (sp.instOrigins.getD k .ord).child? = none →
    ∃ kinds, SigKindsAt senv sp k (sp.insts[k]).1 kinds

def ShapeArgKinds (senv : StructEnv) (sp : MachineShape) : Prop :=
  ∀ k, ArgKindsAt senv sp (closingNDecl sp) k ∧ ArgKindsAtS senv sp (closingNDecl sp) k

def SigEq (s s₀ : StructEnv) (c : Name) : Prop := s.inst c = s₀.inst c ∧ s.instS c = s₀.instS c

def CalleeTeleAll (senv : StructEnv) (c : Name) (q : Pkg ι dom) : Prop :=
  CalleeTeleAt senv c q ∧ CalleeTeleAtS senv c q

/-! ## SC0: transport and the per-entry core -/

/-- The callee half transported along an equal `inst` table. -/
theorem calleeTeleAt_of_eq {senv senv₀ : StructEnv} {c : Name} {q : Pkg ι dom}
    (he : senv.inst c = senv₀.inst c) (h : CalleeTeleAt senv₀ c q) : CalleeTeleAt senv c q := by
  intro kinds res hs
  rw [he] at hs
  exact h kinds res hs

/-- The same along an equal `instS` table. -/
theorem calleeTeleAtS_of_eq {senv senv₀ : StructEnv} {c : Name} {q : Pkg ι dom}
    (he : senv.instS c = senv₀.instS c) (h : CalleeTeleAtS senv₀ c q) : CalleeTeleAtS senv c q := by
  intro kinds ty hs
  rw [he] at hs
  exact h kinds ty hs

/-- One entry: the origin-indexed signature picks `argWidth_of_halves` (`.ord`) or `argWidth_of_halvesS`
(`.field i`); a `.mem` origin admits no signature (`SigKindsAt` is `False`). All facts are hypotheses. -/
theorem callArgsOk_of_sigKinds {senv senv₀ : StructEnv} (p q : Pkg ι dom) {k : Nat}
    (hk : k < p.d.shape.insts.length) {kinds : List MixedGateBinder}
    (hsk : SigKindsAt senv p.d.shape k (p.d.shape.insts[k]).1 kinds)
    (hA : ArgKindsAt senv p.d.shape p.kD k) (hAS : ArgKindsAtS senv p.d.shape p.kD k)
    (hE : SigEq senv senv₀ (p.d.shape.insts[k]).1) (hT : CalleeTeleAll senv₀ (p.d.shape.insts[k]).1 q) :
    callArgsOkAt p.d p.kD k q.portWidths = true := by
  revert hsk
  first
    | unfold SigKindsAt
    | delta SigKindsAt
  cases p.d.shape.instOrigins.getD k .ord with
  | ord =>
    intro hsk
    obtain ⟨res, hs⟩ := hsk
    exact argWidth_of_halves senv p q hk hs hA (calleeTeleAt_of_eq hE.1 hT.1)
  | field i =>
    intro hsk
    obtain ⟨ty, hs⟩ := hsk
    exact argWidth_of_halvesS senv p q hk hs hAS (calleeTeleAtS_of_eq hE.2 hT.2)
  | mem combo aw dw =>
    intro hsk
    exact False.elim hsk

/-- **SC0 (C-CORE, pure, CONDITIONAL)**: every ordinary call of ONE read shape, from the named suppliers
(KD, SIG, LK, ENV, VT ∧ P5 — all hypotheses; sufficiency only, nothing about a run). -/
theorem argWidthAt_of_read (P : Pkgs ι dom) (p : Pkg ι dom) {senv senv₀ : StructEnv}
    (hKD  : p.kD = closingNDecl p.d.shape)
    (hSIG : ShapeSigProv senv p.d.shape)
    (hARG : ShapeArgKinds senv p.d.shape)
    (hENV : ∀ c q, P c = some q → SigEq senv senv₀ c)
    (hTEL : ∀ c q, P c = some q → CalleeTeleAll senv₀ c q) :
    ∀ k, ArgWidthAt P p k := by
  intro k hk hn q hq
  obtain ⟨kinds, hsk⟩ := hSIG.2 k hk hn
  have hA : ArgKindsAt senv p.d.shape p.kD k := by
    rw [hKD]
    exact (hARG k).1
  have hAS : ArgKindsAtS senv p.d.shape p.kD k := by
    rw [hKD]
    exact (hARG k).2
  exact callArgsOk_of_sigKinds p q hk hsk hA hAS (hENV _ q hq) (hTEL _ q hq)

/-! ## SC1: projection from the fuel-model provenance (FUEL MODEL ONLY; no O1/O2) -/

/-- A stored tag with its `OriginTAt` facts and no closing child gives the origin-indexed signature. -/
theorem sigKindsAt_of_originTAt {senv : StructEnv} {sp : MachineShape} {k : Nat}
    {e : Name × List Nat × MixedGateBinder} {nm? : Option String} {o : InstOrigin}
    (hgo : sp.instOrigins.getD k .ord = o)
    (hT : Tools.ShippingReaderFuelShapeProv.OriginTAt senv e nm? o) (hn : o.child? = none) :
    ∃ kinds, SigKindsAt senv sp k e.1 kinds := by
  first
    | unfold SigKindsAt
    | delta SigKindsAt
  rw [hgo]
  cases o with
  | ord =>
    obtain ⟨⟨kinds, hs⟩, _⟩ := hT
    exact ⟨kinds, e.2.2, hs⟩
  | field i =>
    obtain ⟨nm, ⟨kinds, ty, _, _, _, _, hs, _⟩, _⟩ := hT
    exact ⟨kinds, ty, hs⟩
  | mem combo aw dw =>
    first
      | exact absurd hn (by simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?])
      | exact absurd hn (fun h => Option.noConfusion h)
      | cases hn
      | (simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?] at hn)

/-- **SC1**: a successful FUEL-model shape satisfies `ShapeSigProv` at the SAME `senv`. Says nothing about
production `machineShape?` (that link is `ShapeFuelBridge` = the O1/O2 / DG-COVER boundary, NOT assumed here). -/
theorem shapeSigProv_of_fuel {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : Tools.ShippingReaderFuel.machineShapeF n sm ps ci senv ai = some (some sp)) :
    ShapeSigProv senv sp := by
  refine And.intro (Tools.ShippingReaderFuelShapeProv.machineShapeF_instOrigins_length h) ?_
  intro k hk hn
  have hlt : k < sp.instOrigins.length := by
    rw [Tools.ShippingReaderFuelShapeProv.machineShapeF_instOrigins_length h]
    exact hk
  have ho : sp.instOrigins[k]? = some (sp.instOrigins.getD k .ord) := by
    rw [Tools.ShippingReaderFuelShapeProv.instOrigins_getD_eq h hk]
    exact List.getElem?_eq_getElem hlt
  exact sigKindsAt_of_originTAt rfl
    (Tools.ShippingReaderFuelShapeProv.machineShapeF_originT h k (sp.insts[k]) _
      (List.getElem?_eq_getElem hk) ho) hn

/-! ## LK0: definitions only (§3.1 text; binder types annotated, meaning unchanged) -/

/-- The kind each placeholder denotes in reader state `st` over peeled inputs `bs`. -/
def phKind (bs : List (Name × MixedGateBinder)) (st : MachRead) : Lean.Expr → Option MixedGateBinder
  | .fvar ⟨.num (.str .anonymous "_machIn") i⟩   => (bs.reverse[i]?).map (·.2)
  | .fvar ⟨.num (.str .anonymous "_machSlot") i⟩ => st.kinds[i]?
  | .fvar ⟨.num (.str .anonymous "_machLet") j⟩  => (st.lets[j]?).map (·.2.1)
  | .fvar ⟨.num (.str .anonymous "_machInst") k⟩ => (st.insts[k]?).map (·.2.2)
  | _ => none

/-- A kinding judgment on placeholder-form Exprs (PARAMETER; instantiation is unit LK3). -/
abbrev PhKinding := (Lean.Expr → Option MixedGateBinder) → Lean.Expr → MixedGateBinder → Prop

/-- The laws LK1 will use (PARAMETER; `uniq` is kind-exact: `Bool ≠ .bits 1`). Nothing here proves them. -/
structure PhKindingLaws (HK : PhKinding) : Prop where
  var  : ∀ (Γ : Lean.Expr → Option MixedGateBinder) (e : Lean.Expr) (k : MixedGateBinder),
    (phKind [] {} e).isSome ∨ (∃ x, e = .fvar x) → (HK Γ e k ↔ Γ e = some k)
  uniq : ∀ (Γ : Lean.Expr → Option MixedGateBinder) (e : Lean.Expr) (k k' : MixedGateBinder),
    HK Γ e k → HK Γ e k' → k = k'
  mono : ∀ (Γ Γ' : Lean.Expr → Option MixedGateBinder) (e : Lean.Expr) (k : MixedGateBinder),
    (∀ (x : Lean.Expr) (kx : MixedGateBinder), Γ x = some kx → Γ' x = some kx) → HK Γ e k → HK Γ' e k

/-- THE invariant: every stored let value has its stored kind, in the context of the SAME state. -/
def LetKindOk (HK : PhKinding) (bs : List (Name × MixedGateBinder)) (st : MachRead) : Prop :=
  ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) →
    HK (phKind bs st) v kd

end Tools.ShippingGen3ArgSupply

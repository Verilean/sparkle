import Tools.ShippingGen2Adapt   -- callArgsOkAt (:73-77), Pkg.portWidths (:80); Pkg/Pkgs, kindTy, StructEnv
set_option autoImplicit false
-- Built: g3sb-7813bf32 (clean snapshot, exit 0, standard axioms).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # SRC-ARGW SA0 / SA1 (scripts/gen3/SRC_ARGW_FREEZE.md rev1 §2.1-§2.3, §3 (iii-b))

LIMITED INTERMEDIATE WORK ONLY (FREEZE §3.1). Nothing here edits a shared definition (`T1Hyp`, `ChildShips`,
`DataOkB`, FG, `callArgsOkAt` are unchanged); nothing here is a run, a trace or coverage.

* **SA0** (pure bridges, §2.2/§2.3). `ArgKindsAt`/`CalleeTeleAt`/`argWidth_of_halves` for `senv.inst` (one-Signal
  signatures, origin `.ord`), and the SEPARATE `ArgKindsAtS`/`CalleeTeleAtS`/`argWidth_of_halvesS` for `senv.instS`
  (origin `.field i`); the existing types are not widened. The origin-indexed `SigKindsAt`/`ArgKindsAtG` are given as
  definitions only (rev1 gives no theorem type for them).
  - `hsig`/`hsigS` is an EXPLICIT hypothesis. It is NOT derived from `hnone`: `hnone` only excludes the `.mem`
    origin; that the signature exists is a reader-provenance fact (FREEZE §2.3, last paragraph).
  - Strength (FREEZE §2.2): the list equation of `ArgKindsAt…` is STRICTLY STRONGER than `callArgsOkAt` (it also fixes
    the argument count). The common core is `callArgsOkAt_of_map` / `argWidth_of_halvesW` (width list `ws` instead of a
    package, so that the controls can use synthetic data).
* **SA1** (§3 (iii-b)). `ArgWidthAt` (§2.1, the target row; data-level), `kidWsP` (full definition, as `kidOutsP`,
  Tools/ShippingGen2DataBridge.lean:62-65), `kidWsP_eq`, `kidWsP_none`, `callArgsOkAt_nil`, `argWidthAt_iff_rowP`.
  - Transport: under `P c = some q` the row at `kidWsP P p k` IS the row at `q.portWidths`.
  - The vacuous case `P c = none ↦ []` gives `true` through `callArgsOkAt_nil`. That `true` carries no width and is
    NOT supply; it agrees with `ArgWidthAt` only because `ArgWidthAt` quantifies over `q` with `P c = some q`.
  - A decided row is supply only at the concrete `P` it is decided for. -/
namespace Tools.ShippingGen3ArgWidthSrc
open Lean
open Sparkle.Compiler.Elab (StructEnv MachineShape MixedGateBinder)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Core.Domain
open Tools.ShippingMachineEntry (kindTy)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingGen2 (Pkg Pkgs callArgsOkAt)

variable {ι : Type} {dom : ι → DomainConfig}

/-! ## SA0 common core (a width list instead of a package) -/

/-- Pointwise form: a full list equation of `option`-widths gives the Bool row. -/
theorem all_of_map {js : List Nat} {F : Nat → Option Nat} {ws : List Nat} (h : js.map F = ws.map some) :
    (List.range ws.length).all (fun j => decide ((js[j]?).bind F = ws[j]?)) = true := by
  apply List.all_eq_true.mpr
  intro j hj
  have hj' : j < ws.length := List.mem_range.mp hj
  apply decide_eq_true
  have e : (js.map F)[j]? = (ws.map some)[j]? := by rw [h]
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem hj'] at e
  rw [List.getElem?_eq_getElem hj']
  revert e
  cases js[j]? with
  | none => intro e; exact absurd e (by simp)
  | some a => intro e; exact Option.some.inj e

/-- The row from the full list equation at entry `k` (the shape of `ArgKindsAt`'s conclusion). -/
theorem callArgsOkAt_of_map (d : MachineData) (nDecl k : Nat) (ws : List Nat) (hk : k < d.shape.insts.length)
    (h : (d.shape.insts[k]).2.1.map (fun a =>
      (d.shape.binders[nDecl + (d.shape.insts.length + (d.shape.layout.slots.length + a))]?).map
        fun bn => (kindTy bn.2).bitWidth) = ws.map some) :
    callArgsOkAt d nDecl k ws = true := by
  unfold callArgsOkAt
  rw [List.getElem?_eq_getElem hk]
  exact all_of_map h

/-! ## SA0 for P-ord (`senv.inst`; FREEZE §2.2, types unchanged from rev0) -/

def ArgKindsAt (senv : StructEnv) (sp : MachineShape) (nDecl k : Nat) : Prop :=
  ∀ c js r kinds res, sp.insts[k]? = some (c, js, r) → senv.inst c = some (kinds, res) →
    js.map (fun a => (sp.binders[nDecl + (sp.insts.length + (sp.layout.slots.length + a))]?).map
      fun bn => (kindTy bn.2).bitWidth) = (kinds.filter (· != .domain)).map fun b => some (kindTy b).bitWidth

def CalleeTeleAt (senv : StructEnv) (c : Name) (q : Pkg ι dom) : Prop :=
  ∀ kinds res, senv.inst c = some (kinds, res) →
    (kinds.filter (· != .domain)).map (fun b => (kindTy b).bitWidth) = q.portWidths

/-- The core of `argWidth_of_halves`, against a width list `ws`. ASSUMES `hsig` (not derived from `hnone`). -/
theorem argWidth_of_halvesW (senv : StructEnv) (d : MachineData) (nDecl k : Nat) (ws : List Nat)
    (hk : k < d.shape.insts.length) {kinds : List MixedGateBinder} {res : MixedGateBinder}
    (hsig : senv.inst (d.shape.insts[k]).1 = some (kinds, res))
    (hA : ArgKindsAt senv d.shape nDecl k)
    (hC : (kinds.filter (· != .domain)).map (fun b => (kindTy b).bitWidth) = ws) :
    callArgsOkAt d nDecl k ws = true := by
  apply callArgsOkAt_of_map d nDecl k ws hk
  have h1 := hA (d.shape.insts[k]).1 (d.shape.insts[k]).2.1 (d.shape.insts[k]).2.2 kinds res
    (List.getElem?_eq_getElem hk) hsig
  refine h1.trans ?_
  subst hC
  rw [List.map_map]
  all_goals first | rfl | simp only [Function.comp_def] | simp

/-- Pure. ASSUMES `hsig`; `hsig` is not derived here (§2.3, last paragraph). -/
theorem argWidth_of_halves (senv : StructEnv) (p q : Pkg ι dom) {k : Nat} (hk : k < p.d.shape.insts.length)
    {kinds : List MixedGateBinder} {res : MixedGateBinder}
    (hsig : senv.inst (p.d.shape.insts[k]).1 = some (kinds, res))
    (hA : ArgKindsAt senv p.d.shape p.kD k) (hC : CalleeTeleAt senv (p.d.shape.insts[k]).1 q) :
    callArgsOkAt p.d p.kD k q.portWidths = true :=
  argWidth_of_halvesW senv p.d p.kD k q.portWidths hk hsig hA (hC kinds res hsig)

/-! ## SA0 for P-fld (`senv.instS`; FREEZE §2.3, NEW separate types) -/

def ArgKindsAtS (senv : StructEnv) (sp : MachineShape) (nDecl k : Nat) : Prop :=
  ∀ c js r kinds ty, sp.insts[k]? = some (c, js, r) → senv.instS c = some (kinds, ty) →
    js.map (fun a => (sp.binders[nDecl + (sp.insts.length + (sp.layout.slots.length + a))]?).map
      fun bn => (kindTy bn.2).bitWidth) = (kinds.filter (· != .domain)).map fun b => some (kindTy b).bitWidth

def CalleeTeleAtS (senv : StructEnv) (c : Name) (q : Pkg ι dom) : Prop :=
  ∀ kinds ty, senv.instS c = some (kinds, ty) →
    (kinds.filter (· != .domain)).map (fun b => (kindTy b).bitWidth) = q.portWidths

/-- The core of `argWidth_of_halvesS`, against a width list `ws`. ASSUMES `hsigS`. -/
theorem argWidth_of_halvesSW (senv : StructEnv) (d : MachineData) (nDecl k : Nat) (ws : List Nat)
    (hk : k < d.shape.insts.length) {kinds : List MixedGateBinder} {ty : Lean.Expr}
    (hsigS : senv.instS (d.shape.insts[k]).1 = some (kinds, ty))
    (hA : ArgKindsAtS senv d.shape nDecl k)
    (hC : (kinds.filter (· != .domain)).map (fun b => (kindTy b).bitWidth) = ws) :
    callArgsOkAt d nDecl k ws = true := by
  apply callArgsOkAt_of_map d nDecl k ws hk
  have h1 := hA (d.shape.insts[k]).1 (d.shape.insts[k]).2.1 (d.shape.insts[k]).2.2 kinds ty
    (List.getElem?_eq_getElem hk) hsigS
  refine h1.trans ?_
  subst hC
  rw [List.map_map]
  all_goals first | rfl | simp only [Function.comp_def] | simp

theorem argWidth_of_halvesS (senv : StructEnv) (p q : Pkg ι dom) {k : Nat} (hk : k < p.d.shape.insts.length)
    {kinds : List MixedGateBinder} {ty : Lean.Expr}
    (hsigS : senv.instS (p.d.shape.insts[k]).1 = some (kinds, ty))
    (hA : ArgKindsAtS senv p.d.shape p.kD k) (hC : CalleeTeleAtS senv (p.d.shape.insts[k]).1 q) :
    callArgsOkAt p.d p.kD k q.portWidths = true :=
  argWidth_of_halvesSW senv p.d p.kD k q.portWidths hk hsigS hA (hC kinds ty hsigS)

/-! ## SA0, origin-indexed alternative (FREEZE §2.3; definitions only) -/

/-- The kinds list the reader used for entry `k`, chosen by its ORIGIN (`.mem` admits none). -/
def SigKindsAt (senv : StructEnv) (sp : MachineShape) (k : Nat) (c : Name) (kinds : List MixedGateBinder) : Prop :=
  match sp.instOrigins.getD k .ord with
  | .ord     => ∃ res, senv.inst c = some (kinds, res)
  | .field _ => ∃ ty, senv.instS c = some (kinds, ty)
  | .mem ..  => False

def ArgKindsAtG (senv : StructEnv) (sp : MachineShape) (nDecl k : Nat) : Prop :=
  ∀ c js r kinds, sp.insts[k]? = some (c, js, r) → SigKindsAt senv sp k c kinds →
    js.map (fun a => (sp.binders[nDecl + (sp.insts.length + (sp.layout.slots.length + a))]?).map
      fun bn => (kindTy bn.2).bitWidth) = (kinds.filter (· != .domain)).map fun b => some (kindTy b).bitWidth

/-! ## Intro forms (one concrete signature decides the ∀ of `ArgKindsAt…`; used by the controls) -/

theorem argKindsAt_intro {senv : StructEnv} {sp : MachineShape} {nDecl k : Nat} {c0 : Name} {js0 : List Nat}
    {r0 : MixedGateBinder} {kinds0 : List MixedGateBinder} {res0 : MixedGateBinder}
    (hi : sp.insts[k]? = some (c0, js0, r0)) (hs : senv.inst c0 = some (kinds0, res0))
    (he : js0.map (fun a => (sp.binders[nDecl + (sp.insts.length + (sp.layout.slots.length + a))]?).map
      fun bn => (kindTy bn.2).bitWidth) = (kinds0.filter (· != .domain)).map fun b => some (kindTy b).bitWidth) :
    ArgKindsAt senv sp nDecl k := by
  intro c js r kinds res h1 h2
  rw [hi] at h1
  cases h1
  rw [hs] at h2
  cases h2
  exact he

theorem argKindsAtS_intro {senv : StructEnv} {sp : MachineShape} {nDecl k : Nat} {c0 : Name} {js0 : List Nat}
    {r0 : MixedGateBinder} {kinds0 : List MixedGateBinder} {ty0 : Lean.Expr}
    (hi : sp.insts[k]? = some (c0, js0, r0)) (hs : senv.instS c0 = some (kinds0, ty0))
    (he : js0.map (fun a => (sp.binders[nDecl + (sp.insts.length + (sp.layout.slots.length + a))]?).map
      fun bn => (kindTy bn.2).bitWidth) = (kinds0.filter (· != .domain)).map fun b => some (kindTy b).bitWidth) :
    ArgKindsAtS senv sp nDecl k := by
  intro c js r kinds ty h1 h2
  rw [hi] at h1
  cases h1
  rw [hs] at h2
  cases h2
  exact he

/-! ## SA1: the target row and the decided row through a concrete `P` (FREEZE §2.1, §3 (iii-b)) -/

/-- G-ARG-WID at one call (the target row). DATA-level: no trace, no run, no `RunsTo` inside. -/
def ArgWidthAt (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
    ∀ q, P (p.d.shape.insts[k]).1 = some q → callArgsOkAt p.d p.kD k q.portWidths = true

/-- Entry `k`'s callee's declared non-domain port widths, read through `P` (`[]` off the range or for `P c = none`). -/
def kidWsP (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom) (k : Nat) : List Nat :=
  ((((p.d.shape.insts.map (·.1))[k]?).bind P).map Tools.ShippingGen2.Pkg.portWidths).getD []

theorem insts_map_fst_getElem? (s : MachineShape) {k : Nat} (hk : k < s.insts.length) :
    (s.insts.map (·.1))[k]? = some (s.insts[k]).1 := by
  first
    | (rw [List.getElem?_map, List.getElem?_eq_getElem hk]; rfl)
    | (rw [List.getElem?_map, List.getElem?_eq_getElem hk])
    | simp [hk]

/-- **Agreement** with the served package at an entry in range (as `kidOutsP_eq`, DataBridge:77-87). -/
theorem kidWsP_eq (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom) {k : Nat}
    (hk : k < p.d.shape.insts.length) {q : Tools.ShippingGen2.Pkg ι dom} (hq : P (p.d.shape.insts[k]).1 = some q) :
    kidWsP P p k = q.portWidths := by
  have h1 := insts_map_fst_getElem? p.d.shape hk
  have h2 : kidWsP P p k =
      ((P (p.d.shape.insts[k]).1).map Tools.ShippingGen2.Pkg.portWidths).getD [] := by
    unfold kidWsP
    rw [h1]
    rfl
  rw [h2, hq]
  rfl

/-- The vacuous case (as `kidOutsP_none`, DataBridge:90-100): no package gives the empty entry. -/
theorem kidWsP_none (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom) {k : Nat}
    (hk : k < p.d.shape.insts.length) (hn : P (p.d.shape.insts[k]).1 = none) :
    kidWsP P p k = [] := by
  have h1 := insts_map_fst_getElem? p.d.shape hk
  have h2 : kidWsP P p k =
      ((P (p.d.shape.insts[k]).1).map Tools.ShippingGen2.Pkg.portWidths).getD [] := by
    unfold kidWsP
    rw [h1]
    rfl
  rw [h2, hn]
  rfl

/-- The empty width list passes the row. This `true` carries NO width: it is not supply. -/
theorem callArgsOkAt_nil (d : MachineData) (nDecl k : Nat) : callArgsOkAt d nDecl k [] = true := by
  first
    | rfl
    | (unfold callArgsOkAt; rfl)
    | simp [callArgsOkAt]

/-- **Transport**: the decided row through `kidWsP P p` for every ordinary entry is exactly `∀ k, ArgWidthAt P p k`.
The `P c = none` entries are vacuous on both sides (left: `callArgsOkAt_nil`; right: no `q`). -/
theorem argWidthAt_iff_rowP (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom) :
    (∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      callArgsOkAt p.d p.kD k (kidWsP P p k) = true) ↔ ∀ k, ArgWidthAt P p k := by
  constructor
  · intro h k hk hn q hq
    rw [← kidWsP_eq P p hk hq]
    exact h k hk hn
  · intro h k hk hn
    cases hc : P (p.d.shape.insts[k]).1 with
    | none =>
      rw [kidWsP_none P p hk hc]
      exact callArgsOkAt_nil p.d p.kD k
    | some q =>
      rw [kidWsP_eq P p hk hc]
      exact h k hk hn q hc

end Tools.ShippingGen3ArgWidthSrc

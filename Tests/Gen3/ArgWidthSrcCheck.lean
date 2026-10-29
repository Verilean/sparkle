import Tools.ShippingGen3ArgWidthSrc
import Tests.Gen2.DataBridgeCheck   -- callerL data, `PL` (pickByteH ↦ pbhPkg), `PN`, `callerL_insts_len`
set_option autoImplicit false
-- NOT BUILT (written without running Lean; the integrator builds it).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # Checks for Tools/ShippingGen3ArgWidthSrc.lean (SRC-ARGW SA0/SA1; scripts/gen3/SRC_ARGW_FREEZE.md rev1)

1. **Expected types** (style of Tests/Gen2/PMem4Check.lean §1). Each declared statement of rev1 §2.1-§2.3/§3 (iii-b) is
   compared, binder by binder (names with macro scopes erased, binder infos, types; the bodies instantiated with the SAME
   fresh fvar), against an INDEPENDENT `Exp_…` restatement of the freeze text below; the comparison is `==` after
   `instantiateMVars`, with a logged `isDefEq` fallback (`SRCARGW DEFEQ`), else `throwError`. Meaning-changing MUTANTS
   (`Mut_…`) must be REJECTED (also as whole statements by `isDefEq`); an accepted mutant throws.
2. **SA0 controls on SYNTHETIC data** (labelled DATA CONTROLS: a hand-written `MachineShape`/`MachineData` and
   hand-written `StructEnv`s; no reader run, no package, no source):
   * inst-only (`senvI`): `ArgKindsAt` holds, the row follows through `argWidth_of_halvesW`; the `…S` relation is
     VACUOUSLY true there (no `instS` signature) — the reason `hsigS` is an explicit hypothesis;
   * instS-only (`senvS`): the same through `argWidth_of_halvesSW`;
   * both (`senvB`, `inst` and `instS` with DIFFERENT kinds for the same name): `ArgKindsAt` holds and `ArgKindsAtS`
     fails; the origin-indexed `ArgKindsAtG` holds at origin `.ord` and fails at origin `.field 0`; `SigKindsAt` is
     `False` at a `.mem` origin;
   * width mismatch (negative): the row is `false` for `[16, 1]`, and `ArgKindsAt` is false for a 16-bit callee kind;
   * strength: the row also holds for the SHORTER lists `[8]` and `[]` (the extra argument is not checked), while the
     list equation of `ArgKindsAt` fixes the count (FREEZE §2.2).
3. **SA1 controls**: positive `callerL` through `PL` (data: the decided row at `kidWsP PL`, then `∀ k, ArgWidthAt PL p`
   for every package `p` with `callerL`'s data and `kD = 1` — premises; no `callerL` package exists in the tree);
   negative: a mismatched width list `[16, 16]` fails the row; VACUOUS: `PN` (no packages) makes the row true for EVERY
   parent package, through `none ↦ []` — logged as NOT supply.
4. `#print axioms` and a machine assertion that only `propext`, `Classical.choice`, `Quot.sound` occur. -/
set_option maxHeartbeats 4000000

namespace Tests.Gen3.ArgWidthSrcCheck
open Lean Meta Elab Command
open Sparkle.Compiler.Elab (StructEnv MachineShape MixedGateBinder)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Core.Domain
open Tools.ShippingMachineEntry (kindTy)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingGen2 (Pkg Pkgs callArgsOkAt)
open Tools.ShippingGen3ArgWidthSrc
open Tests.Gen2.DataBridgeCheck (PL PN pbhPkg callerL_insts_len U)
open Sparkle.Tests.Compiler.ShippingMachineLinkedTest

/-! ## 1. Expected types -/

/-- `==` after `instantiateMVars`; on a mismatch log it and fall back to `isDefEq` (logged); else fail. -/
def cmpEq (what : String) (a e : Expr) : MetaM Unit := do
  let a ← instantiateMVars a
  let e ← instantiateMVars e
  if a == e then return
  logInfo m!"SRCARGW NOTE {what}: not syntactically equal, trying isDefEq:{indentExpr a}\nexpected{indentExpr e}"
  if (← isDefEq a e) then
    logInfo m!"SRCARGW DEFEQ {what}: accepted by isDefEq (NOT syntactic)"
  else
    throwError "SRCARGW CHECK FAILED {what}:{indentExpr a}\nexpected{indentExpr e}"

/-- Binder-by-binder comparison of two `∀`/`fun` telescopes. -/
partial def cmpTele (what : String) (a e : Expr) (i : Nat := 0) : MetaM Unit := do
  match a, e with
  | .forallE na ta ba bia, .forallE ne te be bie =>
    unless na.eraseMacroScopes == ne.eraseMacroScopes do
      throwError "SRCARGW CHECK FAILED {what}: binder {i} is named {na}, expected {ne}"
    unless bia == bie do
      throwError "SRCARGW CHECK FAILED {what}: binder {i} ({na}) has a different binder info"
    cmpEq s!"{what} binder {i} ({na})" ta te
    withLocalDecl na bia ta fun x => cmpTele what (ba.instantiate1 x) (be.instantiate1 x) (i + 1)
  | .lam na ta ba bia, .lam ne te be bie =>
    unless na.eraseMacroScopes == ne.eraseMacroScopes do
      throwError "SRCARGW CHECK FAILED {what}: parameter {i} is named {na}, expected {ne}"
    unless bia == bie do
      throwError "SRCARGW CHECK FAILED {what}: parameter {i} ({na}) has a different binder info"
    cmpEq s!"{what} parameter {i} ({na})" ta te
    withLocalDecl na bia ta fun x => cmpTele what (ba.instantiate1 x) (be.instantiate1 x) (i + 1)
  | .forallE na .., _ =>
    throwError "SRCARGW CHECK FAILED {what}: extra binder {i} ({na}) not in the expected statement"
  | _, .forallE ne .. =>
    throwError "SRCARGW CHECK FAILED {what}: expected binder {i} ({ne}) is missing"
  | .lam na .., _ =>
    throwError "SRCARGW CHECK FAILED {what}: extra parameter {i} ({na}) not in the expected definition"
  | _, .lam ne .. =>
    throwError "SRCARGW CHECK FAILED {what}: expected parameter {i} ({ne}) is missing"
  | _, _ => cmpEq s!"{what} conclusion" a e

/-- The statement of `n`: a theorem's type, or a definition's value. -/
def stmtOf (n : Name) : MetaM Expr := do
  match ← getConstInfo n with
  | .thmInfo t => pure t.type
  | .defnInfo d => pure d.value
  | _ => throwError "SRCARGW CHECK FAILED: {n} is neither a theorem nor a definition"

def checkExpected (thm exp : Name) : MetaM Unit := do
  let ciT ← getConstInfo thm
  let ciE ← getConstInfo exp
  unless ciT.levelParams.length == ciE.levelParams.length do
    throwError "SRCARGW CHECK FAILED {thm}: universe parameters {ciT.levelParams} vs {ciE.levelParams}"
  -- a definition must be compared with a definition (value), a theorem with a Prop-valued definition (its value)
  if ciT matches .defnInfo _ then
    cmpEq s!"{thm} type" ciT.type ciE.type
  cmpTele s!"{thm}" (← stmtOf thm) (← stmtOf exp)
  logInfo m!"SRCARGW TYPE OK {thm} against {exp}"

def checkMutant (thm mt : Name) : MetaM Unit := do
  let a ← stmtOf thm
  let e ← stmtOf mt
  let accepted ← withoutModifyingState do
    try
      cmpTele s!"{thm} vs mutant {mt}" a e
      pure true
    catch _ => pure false
  if accepted then
    throwError "SRCARGW MUTANT ACCEPTED: {mt} matches {thm}"
  if (← withoutModifyingState (isDefEq a e)) then
    throwError "SRCARGW MUTANT ACCEPTED (isDefEq of the whole statements): {mt} vs {thm}"
  logInfo m!"SRCARGW MUTANT REJECTED {mt} (against {thm})"

/-- Only the standard axioms. -/
def checkAxioms (n : Name) : MetaM Unit := do
  let ax ← Lean.collectAxioms n
  for a in ax do
    unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
      throwError "SRCARGW CHECK FAILED {n}: uses the axiom {a}"
  logInfo m!"SRCARGW AXIOMS OK {n}: {ax}"

/-! ### Independent restatements of FREEZE rev1 (copied from the freeze text, not from the Tools file) -/

def Exp_ArgKindsAt (senv : StructEnv) (sp : MachineShape) (nDecl k : Nat) : Prop :=
  ∀ c js r kinds res, sp.insts[k]? = some (c, js, r) → senv.inst c = some (kinds, res) →
    js.map (fun a => (sp.binders[nDecl + (sp.insts.length + (sp.layout.slots.length + a))]?).map
      fun bn => (kindTy bn.2).bitWidth) = (kinds.filter (· != .domain)).map fun b => some (kindTy b).bitWidth

def Exp_CalleeTeleAt {ι : Type} {dom : ι → DomainConfig} (senv : StructEnv) (c : Name) (q : Pkg ι dom) : Prop :=
  ∀ kinds res, senv.inst c = some (kinds, res) →
    (kinds.filter (· != .domain)).map (fun b => (kindTy b).bitWidth) = q.portWidths

def Exp_argWidth_of_halves : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (senv : StructEnv) (p q : Pkg ι dom) {k : Nat}
    (hk : k < p.d.shape.insts.length) {kinds : List MixedGateBinder} {res : MixedGateBinder}
    (hsig : senv.inst (p.d.shape.insts[k]).1 = some (kinds, res))
    (hA : ArgKindsAt senv p.d.shape p.kD k) (hC : CalleeTeleAt senv (p.d.shape.insts[k]).1 q),
    callArgsOkAt p.d p.kD k q.portWidths = true

def Exp_ArgKindsAtS (senv : StructEnv) (sp : MachineShape) (nDecl k : Nat) : Prop :=
  ∀ c js r kinds ty, sp.insts[k]? = some (c, js, r) → senv.instS c = some (kinds, ty) →
    js.map (fun a => (sp.binders[nDecl + (sp.insts.length + (sp.layout.slots.length + a))]?).map
      fun bn => (kindTy bn.2).bitWidth) = (kinds.filter (· != .domain)).map fun b => some (kindTy b).bitWidth

def Exp_CalleeTeleAtS {ι : Type} {dom : ι → DomainConfig} (senv : StructEnv) (c : Name) (q : Pkg ι dom) : Prop :=
  ∀ kinds ty, senv.instS c = some (kinds, ty) →
    (kinds.filter (· != .domain)).map (fun b => (kindTy b).bitWidth) = q.portWidths

def Exp_argWidth_of_halvesS : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (senv : StructEnv) (p q : Pkg ι dom) {k : Nat}
    (hk : k < p.d.shape.insts.length) {kinds : List MixedGateBinder} {ty : Lean.Expr}
    (hsigS : senv.instS (p.d.shape.insts[k]).1 = some (kinds, ty))
    (hA : ArgKindsAtS senv p.d.shape p.kD k) (hC : CalleeTeleAtS senv (p.d.shape.insts[k]).1 q),
    callArgsOkAt p.d p.kD k q.portWidths = true

def Exp_SigKindsAt (senv : StructEnv) (sp : MachineShape) (k : Nat) (c : Name) (kinds : List MixedGateBinder) :
    Prop :=
  match sp.instOrigins.getD k .ord with
  | .ord     => ∃ res, senv.inst c = some (kinds, res)
  | .field _ => ∃ ty, senv.instS c = some (kinds, ty)
  | .mem ..  => False

def Exp_ArgKindsAtG (senv : StructEnv) (sp : MachineShape) (nDecl k : Nat) : Prop :=
  ∀ c js r kinds, sp.insts[k]? = some (c, js, r) → SigKindsAt senv sp k c kinds →
    js.map (fun a => (sp.binders[nDecl + (sp.insts.length + (sp.layout.slots.length + a))]?).map
      fun bn => (kindTy bn.2).bitWidth) = (kinds.filter (· != .domain)).map fun b => some (kindTy b).bitWidth

def Exp_ArgWidthAt {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
    ∀ q, P (p.d.shape.insts[k]).1 = some q → callArgsOkAt p.d p.kD k q.portWidths = true

def Exp_kidWsP {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom)
    (p : Tools.ShippingGen2.Pkg ι dom) (k : Nat) : List Nat :=
  ((((p.d.shape.insts.map (·.1))[k]?).bind P).map Tools.ShippingGen2.Pkg.portWidths).getD []

def Exp_kidWsP_eq : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom)
    {k : Nat} (hk : k < p.d.shape.insts.length) {q : Tools.ShippingGen2.Pkg ι dom}
    (hq : P (p.d.shape.insts[k]).1 = some q), kidWsP P p k = q.portWidths

def Exp_kidWsP_none : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom)
    {k : Nat} (hk : k < p.d.shape.insts.length) (hn : P (p.d.shape.insts[k]).1 = none), kidWsP P p k = []

def Exp_callArgsOkAt_nil : Prop :=
  ∀ (d : MachineData) (nDecl k : Nat), callArgsOkAt d nDecl k [] = true

def Exp_argWidthAt_iff_rowP : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom),
    (∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      callArgsOkAt p.d p.kD k (kidWsP P p k) = true) ↔ ∀ k, ArgWidthAt P p k

/-! ### Meaning-changing mutants (each must be REJECTED) -/

/-- the domain binders are NOT filtered -/
def Mut_ArgKindsAt_noFilter (senv : StructEnv) (sp : MachineShape) (nDecl k : Nat) : Prop :=
  ∀ c js r kinds res, sp.insts[k]? = some (c, js, r) → senv.inst c = some (kinds, res) →
    js.map (fun a => (sp.binders[nDecl + (sp.insts.length + (sp.layout.slots.length + a))]?).map
      fun bn => (kindTy bn.2).bitWidth) = kinds.map fun b => some (kindTy b).bitWidth

/-- the slot block is skipped in the binder index -/
def Mut_ArgKindsAt_noSlots (senv : StructEnv) (sp : MachineShape) (nDecl k : Nat) : Prop :=
  ∀ c js r kinds res, sp.insts[k]? = some (c, js, r) → senv.inst c = some (kinds, res) →
    js.map (fun a => (sp.binders[nDecl + (sp.insts.length + a)]?).map
      fun bn => (kindTy bn.2).bitWidth) = (kinds.filter (· != .domain)).map fun b => some (kindTy b).bitWidth

/-- the S relation reads `inst` instead of `instS` -/
def Mut_ArgKindsAtS_inst (senv : StructEnv) (sp : MachineShape) (nDecl k : Nat) : Prop :=
  ∀ c js r kinds ty, sp.insts[k]? = some (c, js, r) → senv.inst c = some (kinds, ty) →
    js.map (fun a => (sp.binders[nDecl + (sp.insts.length + (sp.layout.slots.length + a))]?).map
      fun bn => (kindTy bn.2).bitWidth) = (kinds.filter (· != .domain)).map fun b => some (kindTy b).bitWidth

/-- reversed callee widths -/
def Mut_CalleeTeleAt_rev {ι : Type} {dom : ι → DomainConfig} (senv : StructEnv) (c : Name) (q : Pkg ι dom) : Prop :=
  ∀ kinds res, senv.inst c = some (kinds, res) →
    (kinds.filter (· != .domain)).map (fun b => (kindTy b).bitWidth) = q.portWidths.reverse

/-- the weakened (vacuous) conclusion at `[]` -/
def Mut_argWidth_of_halves_nil : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (senv : StructEnv) (p q : Pkg ι dom) {k : Nat}
    (hk : k < p.d.shape.insts.length) {kinds : List MixedGateBinder} {res : MixedGateBinder}
    (hsig : senv.inst (p.d.shape.insts[k]).1 = some (kinds, res))
    (hA : ArgKindsAt senv p.d.shape p.kD k) (hC : CalleeTeleAt senv (p.d.shape.insts[k]).1 q),
    callArgsOkAt p.d p.kD k [] = true

/-- `.ord`/`.field` arms swapped -/
def Mut_SigKindsAt_swap (senv : StructEnv) (sp : MachineShape) (k : Nat) (c : Name) (kinds : List MixedGateBinder) :
    Prop :=
  match sp.instOrigins.getD k .ord with
  | .ord     => ∃ ty, senv.instS c = some (kinds, ty)
  | .field _ => ∃ res, senv.inst c = some (kinds, res)
  | .mem ..  => False

/-- a memory origin admits every kinds list -/
def Mut_SigKindsAt_memTrue (senv : StructEnv) (sp : MachineShape) (k : Nat) (c : Name) (kinds : List MixedGateBinder) :
    Prop :=
  match sp.instOrigins.getD k .ord with
  | .ord     => ∃ res, senv.inst c = some (kinds, res)
  | .field _ => ∃ ty, senv.instS c = some (kinds, ty)
  | .mem ..  => True

/-- `hnone` negated -/
def Mut_ArgWidthAt_ne {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? ≠ none →
    ∀ q, P (p.d.shape.insts[k]).1 = some q → callArgsOkAt p.d p.kD k q.portWidths = true

/-- a non-empty default -/
def Mut_kidWsP_getD {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom)
    (p : Tools.ShippingGen2.Pkg ι dom) (k : Nat) : List Nat :=
  ((((p.d.shape.insts.map (·.1))[k]?).bind P).map Tools.ShippingGen2.Pkg.portWidths).getD [0]

/-- agreement weakened to the vacuous value -/
def Mut_kidWsP_eq_nil : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom)
    {k : Nat} (hk : k < p.d.shape.insts.length) {q : Tools.ShippingGen2.Pkg ι dom}
    (hq : P (p.d.shape.insts[k]).1 = some q), kidWsP P p k = []

/-- the row side read at `[]` (the vacuous row) -/
def Mut_argWidthAt_iff_rowP_nil : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom),
    (∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      callArgsOkAt p.d p.kD k [] = true) ↔ ∀ k, ArgWidthAt P p k

run_cmd liftTermElabM do
  for (t, e) in [(``ArgKindsAt, ``Exp_ArgKindsAt), (``CalleeTeleAt, ``Exp_CalleeTeleAt),
      (``argWidth_of_halves, ``Exp_argWidth_of_halves), (``ArgKindsAtS, ``Exp_ArgKindsAtS),
      (``CalleeTeleAtS, ``Exp_CalleeTeleAtS), (``argWidth_of_halvesS, ``Exp_argWidth_of_halvesS),
      (``SigKindsAt, ``Exp_SigKindsAt), (``ArgKindsAtG, ``Exp_ArgKindsAtG), (``ArgWidthAt, ``Exp_ArgWidthAt),
      (``kidWsP, ``Exp_kidWsP), (``kidWsP_eq, ``Exp_kidWsP_eq), (``kidWsP_none, ``Exp_kidWsP_none),
      (``callArgsOkAt_nil, ``Exp_callArgsOkAt_nil), (``argWidthAt_iff_rowP, ``Exp_argWidthAt_iff_rowP)] do
    checkExpected t e
  for (t, m) in [(``ArgKindsAt, ``Mut_ArgKindsAt_noFilter), (``ArgKindsAt, ``Mut_ArgKindsAt_noSlots),
      (``ArgKindsAtS, ``Mut_ArgKindsAtS_inst), (``CalleeTeleAt, ``Mut_CalleeTeleAt_rev),
      (``argWidth_of_halves, ``Mut_argWidth_of_halves_nil), (``SigKindsAt, ``Mut_SigKindsAt_swap),
      (``SigKindsAt, ``Mut_SigKindsAt_memTrue), (``ArgWidthAt, ``Mut_ArgWidthAt_ne), (``kidWsP, ``Mut_kidWsP_getD),
      (``kidWsP_eq, ``Mut_kidWsP_eq_nil), (``argWidthAt_iff_rowP, ``Mut_argWidthAt_iff_rowP_nil)] do
    checkMutant t m
  -- the checker itself: an expected statement against its own mutant must fail too
  checkMutant ``Exp_ArgKindsAt ``Mut_ArgKindsAt_noFilter

/-! ## 2. SA0 controls on SYNTHETIC data (DATA CONTROLS: hand-written shape and signatures; no run, no package) -/

/-- One declaration input (`i0`), one call output binder (`o0`), no slots, two argument lets `l0 : BitVec 8`,
`l1 : Bool`; one call entry `f` with arguments `[0, 1]` and origin `.ord`. Row index: `1 + (1 + (0 + a))`. -/
def shSyn : MachineShape :=
  { binders := [(`i0, .bits 8), (`o0, .bits 4), (`l0, .bits 8), (`l1, .bool)], body := .bvar 0,
    layout := { slots := [], outs := [], resetKind := .synchronous },
    insts := [(`f, [0, 1], .bits 4)], instOrigins := [.ord] }

/-- The same entry with a `.field 0` origin, and with a memory origin. -/
def shSynF : MachineShape := { shSyn with instOrigins := [.field 0] }
def shSynM : MachineShape := { shSyn with instOrigins := [.mem false 4 8] }

def dSyn : MachineData :=
  { shape := shSyn, nIn := 1, dom := .bvar 0, bposL := [], vposL := [], vwL := [], ss := [], ls := [], outs := [],
    nexts := .nil }

/-- inst-only: `f : Domain → BitVec 8 → Bool → BitVec 4` (kinds include the domain). -/
def senvI : StructEnv :=
  { proj := fun _ => none, fields := fun _ => none, inst := fun _ => some ([.domain, .bits 8, .bool], .bits 4) }
/-- instS-only: the same binder kinds, a structure result type. -/
def senvS : StructEnv :=
  { proj := fun _ => none, fields := fun _ => none,
    instS := fun _ => some ([.domain, .bits 8, .bool], .const `T []) }
/-- both, with DIFFERENT kinds (possible for an arbitrary `StructEnv`, FREEZE §1.1). -/
def senvB : StructEnv :=
  { proj := fun _ => none, fields := fun _ => none, inst := fun _ => some ([.domain, .bits 8, .bool], .bits 4),
    instS := fun _ => some ([.domain, .bits 16], .const `T []) }
/-- a 16-bit callee kind (mismatch). -/
def senvBad : StructEnv :=
  { proj := fun _ => none, fields := fun _ => none, inst := fun _ => some ([.domain, .bits 16, .bool], .bits 4) }

theorem shSyn_hi : shSyn.insts[0]? = some (`f, [0, 1], .bits 4) := rfl
theorem shSynF_hi : shSynF.insts[0]? = some (`f, [0, 1], .bits 4) := rfl
theorem dSyn_hk : 0 < dSyn.shape.insts.length := by decide

/-- The argument widths at the row index (8, 1). -/
theorem shSyn_eq :
    [0, 1].map (fun a => (shSyn.binders[1 + (shSyn.insts.length + (shSyn.layout.slots.length + a))]?).map
      fun bn => (kindTy bn.2).bitWidth) =
    (([.domain, .bits 8, .bool] : List MixedGateBinder).filter (· != .domain)).map
      fun b => some (kindTy b).bitWidth := by
  first | decide | rfl

theorem kinds8_widths :
    (([.domain, .bits 8, .bool] : List MixedGateBinder).filter (· != .domain)).map (fun b => (kindTy b).bitWidth)
      = [8, 1] := by
  first | decide | rfl

/-! ### inst-only -/

theorem ctlI_argKinds : ArgKindsAt senvI shSyn 1 0 :=
  argKindsAt_intro (kinds0 := [.domain, .bits 8, .bool]) (res0 := .bits 4) shSyn_hi rfl shSyn_eq

/-- **DATA CONTROL (inst-only)**: the row through the SA0 core. -/
theorem ctlI_row : callArgsOkAt dSyn 1 0 [8, 1] = true :=
  argWidth_of_halvesW senvI dSyn 1 0 [8, 1] dSyn_hk (kinds := [.domain, .bits 8, .bool]) (res := .bits 4)
    rfl ctlI_argKinds kinds8_widths

/-- Cross-check by evaluation. -/
theorem ctlI_row_decide : callArgsOkAt dSyn 1 0 [8, 1] = true := by first | decide | rfl

/-- inst-only: the `…S` relation is VACUOUS (no `instS` signature at all) — why `hsigS` is explicit. -/
theorem ctlI_S_vacuous : ArgKindsAtS senvI shSyn 1 0 := by
  intro c js r kinds ty _ h2
  have e : senvI.instS c = none := rfl
  rw [e] at h2
  cases h2

/-! ### instS-only -/

theorem ctlS_argKinds : ArgKindsAtS senvS shSyn 1 0 :=
  argKindsAtS_intro (kinds0 := [.domain, .bits 8, .bool]) (ty0 := .const `T []) shSyn_hi rfl shSyn_eq

/-- **DATA CONTROL (instS-only)**. -/
theorem ctlS_row : callArgsOkAt dSyn 1 0 [8, 1] = true :=
  argWidth_of_halvesSW senvS dSyn 1 0 [8, 1] dSyn_hk (kinds := [.domain, .bits 8, .bool]) (ty := .const `T [])
    rfl ctlS_argKinds kinds8_widths

/-- instS-only: the `inst` relation is vacuous there. -/
theorem ctlS_I_vacuous : ArgKindsAt senvS shSyn 1 0 := by
  intro c js r kinds res _ h2
  have e : senvS.inst c = none := rfl
  rw [e] at h2
  cases h2

/-! ### both (different kinds for the same name) -/

theorem ctlB_argKinds : ArgKindsAt senvB shSyn 1 0 :=
  argKindsAt_intro (kinds0 := [.domain, .bits 8, .bool]) (res0 := .bits 4) shSyn_hi rfl shSyn_eq

/-- **DATA CONTROL (both)**: the `instS` kinds of the same name do NOT fit the argument lets. -/
theorem ctlB_not_argKindsS : ¬ ArgKindsAtS senvB shSyn 1 0 := by
  intro h
  have h1 := h `f [0, 1] (.bits 4) [.domain, .bits 16] (.const `T []) shSyn_hi rfl
  exact absurd h1 (by decide)

/-- Origin-indexed: at origin `.ord` the reader's (`inst`) kinds are the ones constrained. -/
theorem ctlB_argKindsG_ord : ArgKindsAtG senvB shSyn 1 0 := by
  intro c js r kinds h1 hsig
  rw [shSyn_hi] at h1
  cases h1
  have hsig' : ∃ res, senvB.inst `f = some (kinds, res) := hsig
  obtain ⟨res, h2⟩ := hsig'
  have e : senvB.inst `f = some ([.domain, .bits 8, .bool], .bits 4) := rfl
  rw [e] at h2
  cases h2
  exact shSyn_eq

/-- Origin-indexed: at origin `.field 0` the `instS` kinds are the ones constrained, and they do not fit. -/
theorem ctlB_not_argKindsG_field : ¬ ArgKindsAtG senvB shSynF 1 0 := by
  intro h
  have hs : SigKindsAt senvB shSynF 0 `f [.domain, .bits 16] :=
    (show ∃ ty, senvB.instS `f = some ([.domain, .bits 16], ty) from ⟨.const `T [], rfl⟩)
  have h1 := h `f [0, 1] (.bits 4) [.domain, .bits 16] shSynF_hi hs
  exact absurd h1 (by decide)

/-- A memory origin admits no signature. -/
theorem ctl_sigKinds_mem (kinds : List MixedGateBinder) : ¬ SigKindsAt senvB shSynM 0 `f kinds := by
  intro h
  first | exact h | simp [SigKindsAt, shSynM, shSyn] at h

/-! ### width mismatch (negative) and strength -/

/-- **NEGATIVE**: a 16-bit width at position 0 fails the row. -/
theorem ctl_row_mismatch : callArgsOkAt dSyn 1 0 [16, 1] = false := by first | decide | rfl

/-- **NEGATIVE**: a 16-bit callee kind fails `ArgKindsAt` (so the SA0 bridge cannot be applied). -/
theorem ctl_not_argKinds_bad : ¬ ArgKindsAt senvBad shSyn 1 0 := by
  intro h
  have h1 := h `f [0, 1] (.bits 4) [.domain, .bits 16, .bool] (.bits 4) shSyn_hi rfl
  exact absurd h1 (by decide)

/-- Strength (FREEZE §2.2): the row holds for SHORTER lists (the extra argument is unchecked) … -/
theorem ctl_row_short : callArgsOkAt dSyn 1 0 [8] = true := by first | decide | rfl
theorem ctl_row_empty : callArgsOkAt dSyn 1 0 [] = true := callArgsOkAt_nil dSyn 1 0

/-- … while the list equation of `ArgKindsAt` fixes the count: a one-port callee does not satisfy it. -/
theorem ctl_not_argKinds_short :
    ¬ ArgKindsAt { senvI with inst := fun _ => some ([.domain, .bits 8], .bits 4) } shSyn 1 0 := by
  intro h
  have h1 := h `f [0, 1] (.bits 4) [.domain, .bits 8] (.bits 4) shSyn_hi rfl
  exact absurd h1 (by decide)

/-! ## 3. SA1 controls (`kidWsP`) -/

set_option maxRecDepth 100000 in
/-- `pickByteH`'s declared port widths (decided). -/
theorem pbh_portWidths' : pbhPkg.portWidths = [16, 2] := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
/-- The decided row through `PL` at `callerL`'s entry 0 (`nDecl = 1`). DATA control. -/
theorem callerL_rowPL :
    callArgsOkAt callerL.machineData 1 0
      (((((callerL.machineData.shape.insts.map (·.1))[0]?).bind PL).map Tools.ShippingGen2.Pkg.portWidths).getD [])
      = true := by
  first | decide | decide +kernel

/-- **POSITIVE (SA1)**: every package with `callerL`'s data and `kD = 1` satisfies `ArgWidthAt PL` at every `k`
(premises; no `callerL` package is exhibited). Supply only at this concrete `PL`. -/
theorem callerL_argWidthAt (p : Pkg Unit U) (hp : p.d = callerL.machineData) (hkD : p.kD = 1) :
    ∀ k, ArgWidthAt PL p k := by
  apply (argWidthAt_iff_rowP PL p).mp
  intro k hk _
  have hk1 : k = 0 := by
    rw [hp, callerL_insts_len] at hk
    omega
  subst hk1
  have e : kidWsP PL p 0 =
      ((((callerL.machineData.shape.insts.map (·.1))[0]?).bind PL).map Tools.ShippingGen2.Pkg.portWidths).getD [] := by
    unfold kidWsP
    rw [hp]
  rw [e, hp, hkD]
  exact callerL_rowPL

set_option maxRecDepth 100000 in
/-- **NEGATIVE (SA1)**: a mismatched width list fails the row on `callerL`'s data. -/
theorem callerL_row_mismatch : callArgsOkAt callerL.machineData 1 0 [16, 16] = false := by
  first | decide | decide +kernel

/-- **VACUOUS (NOT supply)**: with no packages the table is `[]` everywhere and the row is `true` for EVERY parent
package, whatever its argument widths. -/
theorem vacuous_rowPN (p : Pkg Unit U) :
    ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      callArgsOkAt p.d p.kD k (kidWsP PN p k) = true := by
  intro k hk _
  rw [kidWsP_none PN p hk rfl]
  exact callArgsOkAt_nil p.d p.kD k

theorem vacuous_argWidthAtPN (p : Pkg Unit U) : ∀ k, ArgWidthAt PN p k :=
  (argWidthAt_iff_rowP PN p).mp (vacuous_rowPN p)

run_cmd logInfo "SRCARGW VACUOUS: vacuous_rowPN / vacuous_argWidthAtPN are true from `P c = none ↦ []` (callArgsOkAt_nil). This carries NO width and is NOT counted as supply."

/-! ## 4. Axioms -/

#print axioms Tools.ShippingGen3ArgWidthSrc.all_of_map
#print axioms Tools.ShippingGen3ArgWidthSrc.callArgsOkAt_of_map
#print axioms Tools.ShippingGen3ArgWidthSrc.argWidth_of_halvesW
#print axioms Tools.ShippingGen3ArgWidthSrc.argWidth_of_halves
#print axioms Tools.ShippingGen3ArgWidthSrc.argWidth_of_halvesSW
#print axioms Tools.ShippingGen3ArgWidthSrc.argWidth_of_halvesS
#print axioms Tools.ShippingGen3ArgWidthSrc.argKindsAt_intro
#print axioms Tools.ShippingGen3ArgWidthSrc.argKindsAtS_intro
#print axioms Tools.ShippingGen3ArgWidthSrc.insts_map_fst_getElem?
#print axioms Tools.ShippingGen3ArgWidthSrc.kidWsP_eq
#print axioms Tools.ShippingGen3ArgWidthSrc.kidWsP_none
#print axioms Tools.ShippingGen3ArgWidthSrc.callArgsOkAt_nil
#print axioms Tools.ShippingGen3ArgWidthSrc.argWidthAt_iff_rowP
#print axioms ctlI_row
#print axioms ctlS_row
#print axioms ctlB_not_argKindsS
#print axioms ctlB_argKindsG_ord
#print axioms ctlB_not_argKindsG_field
#print axioms ctl_not_argKinds_bad
#print axioms callerL_argWidthAt
#print axioms vacuous_argWidthAtPN

run_cmd liftTermElabM do
  for n in [``Tools.ShippingGen3ArgWidthSrc.all_of_map, ``Tools.ShippingGen3ArgWidthSrc.callArgsOkAt_of_map,
      ``Tools.ShippingGen3ArgWidthSrc.argWidth_of_halvesW, ``Tools.ShippingGen3ArgWidthSrc.argWidth_of_halves,
      ``Tools.ShippingGen3ArgWidthSrc.argWidth_of_halvesSW, ``Tools.ShippingGen3ArgWidthSrc.argWidth_of_halvesS,
      ``Tools.ShippingGen3ArgWidthSrc.argKindsAt_intro, ``Tools.ShippingGen3ArgWidthSrc.argKindsAtS_intro,
      ``Tools.ShippingGen3ArgWidthSrc.insts_map_fst_getElem?, ``Tools.ShippingGen3ArgWidthSrc.kidWsP_eq,
      ``Tools.ShippingGen3ArgWidthSrc.kidWsP_none, ``Tools.ShippingGen3ArgWidthSrc.callArgsOkAt_nil,
      ``Tools.ShippingGen3ArgWidthSrc.argWidthAt_iff_rowP,
      ``ctlI_row, ``ctlI_row_decide, ``ctlI_S_vacuous, ``ctlS_row, ``ctlS_I_vacuous, ``ctlB_argKinds,
      ``ctlB_not_argKindsS, ``ctlB_argKindsG_ord, ``ctlB_not_argKindsG_field, ``ctl_sigKinds_mem,
      ``ctl_row_mismatch, ``ctl_not_argKinds_bad, ``ctl_row_short, ``ctl_row_empty, ``ctl_not_argKinds_short,
      ``pbh_portWidths', ``callerL_rowPL, ``callerL_argWidthAt, ``callerL_row_mismatch, ``vacuous_rowPN,
      ``vacuous_argWidthAtPN] do
    checkAxioms n

end Tests.Gen3.ArgWidthSrcCheck

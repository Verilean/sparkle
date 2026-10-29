import Tools.ShippingGen3ArgSupply        -- SC0/SC1/LK0 rev0 (ShapeSigProv, SigEq, CalleeTeleAll, phKind, PhKindingLaws, LetKindOk)
import Tools.ShippingReaderFuelShapeR5    -- shapePost / ShapePre / ShapeMid; ite_none_inv, bind_inv, instBinders
import Tools.ShippingReaderFuelProv       -- InstProv, CallPreP, instProv_init; Call.inSt / Call.outSt, HasSt (FuelR5)
import Tools.ShippingReaderFuelR1         -- SigDisj
import Tools.ShippingReaderMatcherArityArray  -- getAppArgs_eq, argsT_app (argsT / argsAcc: ShippingReaderMatcherArity)
set_option autoImplicit false
-- Built: g3se-e134c63a (clean snapshot, exit 0, standard axioms). No `sorry`, no `axiom`, no `native_decide`.

/-! # SRC-ARGW batch 2: SC0 G-form, InstSite, `shapePost_binders`, LK0 lemmas, closable LK1 arms
(scripts/gen3/SRC_ARGW_SUPPLY_FREEZE.md rev2 at cbddde96: §1.1, §3.1, §3.3, §3.4)

CONDITIONAL INTERMEDIATE WORK ONLY. NOT an L-RUN1 discharge, NOT L-FG supply, NOT FG completion (§1.3). Nothing
here is a reader run of a corpus declaration. No shared definition, no compiler file, no FG statement is edited.

* **SC0 G-form** (§1.1 rev1/rev2 R2). `argWidthAt_of_read` (THIS namespace; it supersedes rev0's
  `Tools.ShippingGen3ArgSupply.argWidthAt_of_read`, whose `hARG` was the withdrawn `ShapeArgKinds`): the premise is
  the origin-indexed `∀ k, ArgKindsAtG senv p.d.shape (closingNDecl p.d.shape) k`. No `SigDisj` is used. Every
  supplier (KD, SIG, LK2, ENV, VT ∧ P5) is an explicit hypothesis. Optional `argKinds_both_of_G` (needs `SigDisj`).
* **Definitions** copied from the freeze text (binder types annotated, meaning unchanged): §3.1 `SigKindsSt`,
  `InstArgKinds`, `ReadInv`, `SrcCtx`, `inCtx`, `EnvKindOk`, `midExpr`, `ReadSub`; §3.3 `SrcKinding`, `CallSrcKinds`,
  `MemSrcKinds`; §3.4 `memNatOf`, `InstSite`, `CallPreK`, `GoodK`. NOT written in this batch: `SrcKindingLaws`,
  `ConvKind`, `LetSrcKinds`, `ReadTyped`, `EqvSound`, `ReadTypedAt`, `LoopSrcKinds` (no lemma here uses them).
* **V1** `instSite_args` / `instSiteS_args` exactly as typed in rev2 §3.4 (per-arg SK + length equality).
* **LK2 piece** `shapePost_binders`: the binder list the fuel `shapePost` builds (FS:186-187), the let part
  `st.lets.toList.map (fun l => (l.1, l.2.1))` explicit (`shapePost_decomp`, ShapeR5:318-323, leaves it existential).
* **LK0 lemmas**: `phKind` on the four placeholders, `PhExt` (state extension of the three lookups) and
  `phKind_ext`, `letKindOk_ext` / `letKindOk_sameLets` / `letKindOk_empty`, `readInv_empty`, the `var`-law
  consequences `phKindingLaws_fvar_iff` / `phKindingLaws_let_iff` / `phKindingLaws_let_kind` (§3.2 row R1).
* **LK1 closable arms** (rev2 §3.4 G-table), each its own lemma, CONDITIONAL on the call table `h` being `GoodK`
  (`SatK` = every OK result of the arm's body against `h` satisfies `ReadInv`):
  - G1  `satK_conv_bvar` (state unchanged, `convBvar_st`);
  - G10 `satK_conv_letFloat` (issued call by `ReadSub.float`, `callPreK_conv_float`);
  - G13 `satK_conv_letRegs`, `satK_conv_letHandle` (new env entry vacuous, `envKindOk_cons_vac`);
  - G15 `satK_conv_mdata`, `satK_conv_proj` (FAIL);
  - G16 `pure'` sub-arm `satK_chain_pure` (H1, `ReadSub.appA`);
  - G17 float / `.regs` / `.handle` sub-arms `satK_chain_letFloat`, `satK_chain_letRegs`, `satK_chain_letHandle`.
* **OPEN arms (not attempted / not closable from existing facts):**
  - G12, G20 (loop root; `EnvKindOk` at `.state b 1`; candidate `LoopSrcKinds`) — skipped as instructed;
  - G11 / G18 / G21 (user-let value: `v ↦ rootFloat v` kind transport D5, `ConvKind`, `EqvSound`, `uniq`) — skipped;
  - NOT AUDITED rows G2, G3, G4, G6, G8, G14 — skipped as instructed;
  - G5 (inst: `ConvKind`/`EqvSound`/`uniq` per arg) — open;
  - **STOP (revision review): G7, G9, G16 `next`, G17 user-let, G19 and every arm issuing a SECOND sub-call at
    the state returned by a first one.** `CallPreK` of the second call needs `EnvKindOk HK p st₁ Δ env d` at the NEW
    state `st₁`, but `EnvKindOk` is state-indexed through `convBvar … st` (FD:240-255): for an env entry
    `.state b n` with `n ≠ 1`, `convBvar` reads `st.dom` and `st.kinds` (FD:247-252), so (i) a state with
    `st.dom = none` has NO obligation there while `st₁.dom = some _` does, and (ii) `dom` may be replaced by an
    `==`-equal (extern `Expr.eqv`) but different term (`domGuard` then `dom := some dom'`, FD:313-317). Neither is
    derivable from `ReadInv`/`EnvKindOk`/`GoodK` as typed; the `.val`/`.state b 1` entries additionally need a
    state-extension table invariant (provable, not written). The type needing review is `EnvKindOk` (§3.1) and
    with it `CallPreK`/`GoodK` (§3.4). No premise was added. -/
namespace Tools.ShippingGen3ArgSupply2
open Lean
open Sparkle.Compiler.Elab
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Core.Domain
open Tools.ShippingGen2 (Pkg Pkgs callArgsOkAt)
open Tools.ShippingGen3ArgWidthSrc
open Tools.ShippingCallWidthsEntry (closingNDecl)
open Tools.ShippingGen3ArgSupply (ShapeSigProv SigEq CalleeTeleAll calleeTeleAt_of_eq calleeTeleAtS_of_eq
  phKind PhKinding PhKindingLaws LetKindOk)
open Tools.ShippingReaderFuel
open Tools.ShippingReaderFuelProv (InstProv CallPreP instProv_init)
open Tools.ShippingReaderFuelR1 (SigDisj)
open Tools.ShippingReaderMatcherArity (argsT argsAcc)
open Tools.ShippingReaderMatcherArityArray (getAppArgs_eq argsT_app)
open Tools.ShippingMachineShapeUnfold (instBinders ite_none_inv ite_else_none_inv bind_inv)

/-! ## 1. SC0 G-form (§1.1, origin-indexed `ArgKindsAtG`) -/

theorem sigKindsAt_of_ord {senv : StructEnv} {sp : MachineShape} {k : Nat} {c : Name}
    {kinds : List MixedGateBinder} (ho : sp.instOrigins.getD k .ord = .ord) :
    SigKindsAt senv sp k c kinds ↔ ∃ res, senv.inst c = some (kinds, res) := by
  first
    | (unfold SigKindsAt; rw [ho]; done)
    | (unfold SigKindsAt; rw [ho]; exact Iff.rfl)
    | (simp only [SigKindsAt, ho])
    | (delta SigKindsAt; rw [ho]; exact Iff.rfl)

theorem sigKindsAt_of_field {senv : StructEnv} {sp : MachineShape} {k : Nat} {c : Name}
    {kinds : List MixedGateBinder} {i : Nat} (ho : sp.instOrigins.getD k .ord = .field i) :
    SigKindsAt senv sp k c kinds ↔ ∃ ty, senv.instS c = some (kinds, ty) := by
  first
    | (unfold SigKindsAt; rw [ho]; done)
    | (unfold SigKindsAt; rw [ho]; exact Iff.rfl)
    | (simp only [SigKindsAt, ho])
    | (delta SigKindsAt; rw [ho]; exact Iff.rfl)

theorem sigKindsAt_of_mem {senv : StructEnv} {sp : MachineShape} {k : Nat} {c : Name}
    {kinds : List MixedGateBinder} {combo : Bool} {aw dw : Nat}
    (ho : sp.instOrigins.getD k .ord = .mem combo aw dw) :
    SigKindsAt senv sp k c kinds ↔ False := by
  first
    | (unfold SigKindsAt; rw [ho]; done)
    | (unfold SigKindsAt; rw [ho]; exact Iff.rfl)
    | (simp only [SigKindsAt, ho])
    | (delta SigKindsAt; rw [ho]; exact Iff.rfl)

/-- At an `.ord` entry the origin-indexed row is the `inst` row. -/
theorem argKindsAt_of_G {senv : StructEnv} {sp : MachineShape} {nDecl k : Nat}
    (ho : sp.instOrigins.getD k .ord = .ord) (hG : ArgKindsAtG senv sp nDecl k) :
    ArgKindsAt senv sp nDecl k := by
  intro c js r kinds res h1 h2
  exact hG c js r kinds h1 ((sigKindsAt_of_ord ho).mpr ⟨res, h2⟩)

/-- At a `.field i` entry the origin-indexed row is the `instS` row. -/
theorem argKindsAtS_of_G {senv : StructEnv} {sp : MachineShape} {nDecl k i : Nat}
    (ho : sp.instOrigins.getD k .ord = .field i) (hG : ArgKindsAtG senv sp nDecl k) :
    ArgKindsAtS senv sp nDecl k := by
  intro c js r kinds ty h1 h2
  exact hG c js r kinds h1 ((sigKindsAt_of_field ho).mpr ⟨ty, h2⟩)

/-- One entry, per origin: `argWidth_of_halves` (`.ord`) or `argWidth_of_halvesS` (`.field i`); `.mem` admits no
signature. No `SigDisj`. -/
theorem callArgsOk_of_sigKindsG {ι : Type} {dom : ι → DomainConfig} {senv senv₀ : StructEnv}
    (p q : Pkg ι dom) {k : Nat} (hk : k < p.d.shape.insts.length) {kinds : List MixedGateBinder}
    (hsk : SigKindsAt senv p.d.shape k (p.d.shape.insts[k]).1 kinds)
    (hG : ArgKindsAtG senv p.d.shape p.kD k)
    (hE : SigEq senv senv₀ (p.d.shape.insts[k]).1) (hT : CalleeTeleAll senv₀ (p.d.shape.insts[k]).1 q) :
    callArgsOkAt p.d p.kD k q.portWidths = true := by
  cases ho : p.d.shape.instOrigins.getD k .ord with
  | ord =>
    obtain ⟨res, hs⟩ := (sigKindsAt_of_ord ho).mp hsk
    exact argWidth_of_halves senv p q hk hs (argKindsAt_of_G ho hG) (calleeTeleAt_of_eq hE.1 hT.1)
  | field i =>
    obtain ⟨ty, hs⟩ := (sigKindsAt_of_field ho).mp hsk
    exact argWidth_of_halvesS senv p q hk hs (argKindsAtS_of_G ho hG) (calleeTeleAtS_of_eq hE.2 hT.2)
  | mem combo aw dw =>
    exact False.elim ((sigKindsAt_of_mem ho).mp hsk)

/-- **SC0 (C-CORE, pure, CONDITIONAL), G-form (§1.1 rev1 type)**: every ordinary call of ONE read shape, from the
named suppliers (KD, SIG, LK2, ENV, VT ∧ P5 — all hypotheses; sufficiency only, nothing about a run). -/
theorem argWidthAt_of_read {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p : Pkg ι dom)
    {senv senv₀ : StructEnv}
    (hKD  : p.kD = closingNDecl p.d.shape)
    (hSIG : ShapeSigProv senv p.d.shape)
    (hARG : ∀ k, ArgKindsAtG senv p.d.shape (closingNDecl p.d.shape) k)
    (hENV : ∀ c q, P c = some q → SigEq senv senv₀ c)
    (hTEL : ∀ c q, P c = some q → CalleeTeleAll senv₀ c q) :
    ∀ k, ArgWidthAt P p k := by
  intro k hk hn q hq
  obtain ⟨kinds, hsk⟩ := hSIG.2 k hk hn
  have hG : ArgKindsAtG senv p.d.shape p.kD k := by
    rw [hKD]
    exact hARG k
  exact callArgsOk_of_sigKindsG p q hk hsk hG (hENV _ q hq) (hTEL _ q hq)

/-- Optional (§1.1): both forms at a TARGET entry, given `SigDisj` (for `structEnv`: `sigDisj_structEnv`). -/
theorem argKinds_both_of_G {senv : StructEnv} {sp : MachineShape} {nDecl k : Nat}
    (hD : SigDisj senv)
    (hk : k < sp.insts.length) (htgt : (sp.instOrigins.getD k .ord).child? = none)
    (hS : ∃ kinds, SigKindsAt senv sp k (sp.insts[k]).1 kinds)
    (hG : ArgKindsAtG senv sp nDecl k) :
    ArgKindsAt senv sp nDecl k ∧ ArgKindsAtS senv sp nDecl k := by
  obtain ⟨kinds0, hs0⟩ := hS
  have hfst : ∀ (c : Name) (js : List Nat) (r : MixedGateBinder), sp.insts[k]? = some (c, js, r) →
      (sp.insts[k]).1 = c := by
    intro c js r h1
    have h2 : some sp.insts[k] = some (c, js, r) := (List.getElem?_eq_getElem hk).symm.trans h1
    exact congrArg Prod.fst (Option.some.inj h2)
  cases ho : sp.instOrigins.getD k .ord with
  | ord =>
    obtain ⟨res0, hi0⟩ := (sigKindsAt_of_ord ho).mp hs0
    refine ⟨argKindsAt_of_G ho hG, ?_⟩
    intro c js r kinds ty h1 h2
    rw [← hfst c js r h1] at h2
    exact (hD _ _ _ h2 hi0).elim
  | field i =>
    obtain ⟨ty0, hs0'⟩ := (sigKindsAt_of_field ho).mp hs0
    refine ⟨?_, argKindsAtS_of_G ho hG⟩
    intro c js r kinds res h1 h2
    rw [← hfst c js r h1] at h2
    exact (hD _ _ _ hs0' h2).elim
  | mem combo aw dw =>
    exact False.elim ((sigKindsAt_of_mem ho).mp hs0)

/-! ## 2. Definitions (§3.1, §3.3, §3.4; freeze text, binder types annotated) -/

/-- The kinds a STATE's entry `k` was read with, by its stored tag. -/
def SigKindsSt (senv : StructEnv) (st : MachRead) (k : Nat) (c : Name) (kinds : List MixedGateBinder) : Prop :=
  match st.instOrigins.toList.getD k .ord with
  | .ord     => ∃ res, senv.inst c = some (kinds, res)
  | .field _ => ∃ ty, senv.instS c = some (kinds, ty)
  | .mem ..  => False

/-- Each call entry's argument lets carry the callee's non-domain kinds, in port order. -/
def InstArgKinds (senv : StructEnv) (st : MachRead) : Prop :=
  ∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder) (kinds : List MixedGateBinder),
    st.insts[k]? = some (c, js, r) → SigKindsSt senv st k c kinds →
    js.map (fun a => (st.lets[a]?).map (·.2.1)) = (kinds.filter (· != .domain)).map some

/-- THE state invariant: provenance + let kinds + argument kinds, over the run's own inputs `p.bs`. -/
def ReadInv (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (st : MachRead) : Prop :=
  InstProv senv st ∧ LetKindOk HK p.bs st ∧ InstArgKinds senv st

/-- Source binder context (innermost first), entries `mixedGateBinderKind?`. -/
abbrev SrcCtx := List (Option MixedGateBinder)

def inCtx (p : ShapePre) : SrcCtx := p.bs.reverse.map fun b => some b.2

/-- The reader's environment agrees with the source context (state-indexed through `convBvar`). -/
def EnvKindOk (HK : PhKinding) (p : ShapePre) (st : MachRead) (Δ : SrcCtx) (env : List MachVal) (d : Nat) :
    Prop :=
  Δ.length = d + env.length ∧
  ∀ (j : Nat) (k : MixedGateBinder) (x : Lean.Expr) (st' : MachRead), d ≤ j → j < d + env.length →
    Δ[j]? = some (some k) → k ≠ .domain →
    convBvar env d j st = some (x, st') → HK (phKind p.bs st) x k

/-- The run's normalised root expression (the local `e` of `shapeMid`, FS:133-135). -/
def midExpr (en : Lean.Expr) : Lean.Expr :=
  machLoopAsLet (Sparkle.Compiler.MachRawSurface.rootFloat
    (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? (inlFoldNat en)))

/-- Reader inputs of ONE run: subterms of `r` with their source context, closed under the terms the reader
constructs and then reads (`float`, `floatV`, `sparam`). -/
inductive ReadSub (senv : StructEnv) (r : Lean.Expr) : SrcCtx → Lean.Expr → Prop
  | root : ReadSub senv r [] r
  | appF {Δ : SrcCtx} {f a : Lean.Expr} : ReadSub senv r Δ (.app f a) → ReadSub senv r Δ f
  | appA {Δ : SrcCtx} {f a : Lean.Expr} : ReadSub senv r Δ (.app f a) → ReadSub senv r Δ a
  | lamT {Δ : SrcCtx} {n : Name} {t b : Lean.Expr} {bi : BinderInfo} :
      ReadSub senv r Δ (.lam n t b bi) → ReadSub senv r Δ t
  | lamB {Δ : SrcCtx} {n : Name} {t b : Lean.Expr} {bi : BinderInfo} :
      ReadSub senv r Δ (.lam n t b bi) → ReadSub senv r (mixedGateBinderKind? t :: Δ) b
  | allT {Δ : SrcCtx} {n : Name} {t b : Lean.Expr} {bi : BinderInfo} :
      ReadSub senv r Δ (.forallE n t b bi) → ReadSub senv r Δ t
  | allB {Δ : SrcCtx} {n : Name} {t b : Lean.Expr} {bi : BinderInfo} :
      ReadSub senv r Δ (.forallE n t b bi) → ReadSub senv r (mixedGateBinderKind? t :: Δ) b
  | letV {Δ : SrcCtx} {n : Name} {t v b : Lean.Expr} {nd : Bool} :
      ReadSub senv r Δ (.letE n t v b nd) → ReadSub senv r Δ v
  | letB {Δ : SrcCtx} {n : Name} {t v b : Lean.Expr} {nd : Bool} :
      ReadSub senv r Δ (.letE n t v b nd) → ReadSub senv r (mixedGateBinderKind? t :: Δ) b
  /-- let arm, `rootFloat v` is a `let` (FD:363-366, :512-515). -/
  | float {Δ : SrcCtx} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {n2 : Name} {t2 v2 w : Lean.Expr}
      {nd2 : Bool} : ReadSub senv r Δ (.letE nm ty v b nd) →
      Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2 →
      ReadSub senv r Δ (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2)
  /-- let arm, non-let branch: `| v =>` re-binds `v := rootFloat v` (FD:367, :516). -/
  | floatV {Δ : SrcCtx} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} :
      ReadSub senv r Δ (.letE nm ty v b nd) →
      ReadSub senv r Δ (Sparkle.Compiler.MachRawSurface.rootFloat v)
  /-- `instSStep` converts the parameters of the CONSTRUCTED `instRes ty args` (FD:266-269, :472-474). -/
  | sparam {Δ : SrcCtx} {e : Lean.Expr} {c : Name} {ks : List MixedGateBinder} {ty : Lean.Expr}
      {args : List Lean.Expr} {resTy q : Lean.Expr} : ReadSub senv r Δ e →
      machInstCallS? senv e = some (c, ks, ty, args) → instRes ty args = some resTy →
      q ∈ resTy.getAppArgs.toList → ReadSub senv r Δ q

/-- Source kinding of a pre-conversion Expr in source context Γ (PARAMETER). -/
abbrev SrcKinding := SrcCtx → Lean.Expr → MixedGateBinder → Prop

/-- (TY-3) at every call node of the run's body, each non-domain argument has the callee's kind. -/
def CallSrcKinds (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  (∀ (Δ : SrcCtx) (e : Lean.Expr) (c : Name) (kinds : List MixedGateBinder) (res : MixedGateBinder)
      (args : List Lean.Expr) (kind : MixedGateBinder) (arg : Lean.Expr),
    ReadSub senv (midExpr en) Δ e → machInstCall? senv e = some (c, kinds, res, args) →
    (kind, arg) ∈ kinds.zip args → kind ≠ .domain → SK (Δ ++ inCtx p) arg kind) ∧
  (∀ (Δ : SrcCtx) (e : Lean.Expr) (c : Name) (kinds : List MixedGateBinder) (ty : Lean.Expr)
      (args : List Lean.Expr) (kind : MixedGateBinder) (arg : Lean.Expr),
    ReadSub senv (midExpr en) Δ e → machInstCallS? senv e = some (c, kinds, ty, args) →
    (kind, arg) ∈ kinds.zip args → kind ≠ .domain → SK (Δ ++ inCtx p) arg kind)

/-- (TY-4) memory operands have the hard-coded kinds at the `aw`/`dw` the recogniser returned. -/
def MemSrcKinds (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ (Δ : SrcCtx) (e : Lean.Expr) (combo : Bool) (aw dw : Nat) (dom : Lean.Expr) (ops : List Lean.Expr)
    (kind : MixedGateBinder) (arg : Lean.Expr),
    ReadSub senv (midExpr en) Δ e →
    Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) e =
      some (combo, aw, dw, dom, ops) →
    (kind, arg) ∈ [MixedGateBinder.bits aw, .bits dw, .bool, .bits aw].zip ops → SK (Δ ++ inCtx p) arg kind

/-- The `natOf` of `convStep`'s memory arm (FD:338). -/
def memNatOf (senv : StructEnv) : Lean.Expr → Option Nat := fun e => canonicalNatLitValue? e <|> senv.natOf e

/-- rev2 V1: the recogniser success that dispatched an `.inst` call, per origin (FD:330-345). -/
def InstSite (senv : StructEnv) (e : Lean.Expr) :
    InstOrigin → Name → List MixedGateBinder → MixedGateBinder → List Lean.Expr → Prop
  | .ord, c, ks, res, args => machInstCall? senv e = some (c, ks, res, args)
  | .mem combo aw dw, c, ks, res, args => ∃ (dom : Lean.Expr) (ops : List Lean.Expr),
      Sparkle.Compiler.MachMemory.memCall? (memNatOf senv) e = some (combo, aw, dw, dom, ops) ∧
      c = Sparkle.Compiler.MachMemory.memChildName combo aw dw ∧
      ks = [.domain, .bits aw, .bits dw, .bool, .bits aw] ∧ res = .bits dw ∧ args = dom :: ops
  | .field _, _, _, _, _ => False

/-- rev2 V1: the call precondition keeps the CALL SITE. -/
def CallPreK (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Call → Prop
  | Call.conv env d e st => ∃ Δ, EnvKindOk HK p st Δ env d ∧ ReadSub senv (midExpr en) Δ e
  | Call.nested env dom αs initsE body st => ∃ Δ e, EnvKindOk HK p st Δ env 0 ∧
      ReadSub senv (midExpr en) Δ e ∧ machRunApp? e = some (dom, αs, initsE, body)
  | Call.inst env c org ks res args st => CallPreP senv (Call.inst env c org ks res args st) ∧
      ∃ Δ e, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e ∧ InstSite senv e org c ks res args
  | Call.instS env c ks ty args st => senv.instS c = some (ks, ty) ∧
      ∃ Δ e, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e ∧
        machInstCallS? senv e = some (c, ks, ty, args)
  | Call.chain env e st => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
  | Call.loopBody _ env e st => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
  | Call.loopRoot env e st => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e

/-- A call table that keeps `ReadInv` for every `CallPreK` call. -/
def GoodK (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) (h : Hs) : Prop :=
  ∀ c, CallPreK HK senv p en c → ReadInv HK senv p (Call.inSt c) → ∀ v, h c = some (some v) →
    ReadInv HK senv p (Call.outSt c v)

/-! ## 3. Spines, arrays and the recognisers (pure) -/

theorem readSub_inlSpine {senv : StructEnv} {r : Lean.Expr} {Δ : SrcCtx} (e : Lean.Expr) :
    ∀ (acc : List Lean.Expr), ReadSub senv r Δ e → (∀ a ∈ acc, ReadSub senv r Δ a) →
      ∀ a ∈ (inlSpine e acc).2, ReadSub senv r Δ a := by
  induction e with
  | app f a ihf iha =>
    intro acc he hacc
    have := ihf (a :: acc) (ReadSub.appF he) (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ReadSub.appA he
      · exact hacc x hx)
    simpa only [inlSpine] using this
  | _ =>
    intro acc _ hacc
    simp only [inlSpine]
    exact hacc

theorem readSub_argsAcc {senv : StructEnv} {r : Lean.Expr} {Δ : SrcCtx} :
    ∀ (e : Lean.Expr) (acc : List Lean.Expr), ReadSub senv r Δ e →
      (∀ a ∈ acc, ReadSub senv r Δ a) → ∀ a ∈ argsAcc e acc, ReadSub senv r Δ a
  | .app f a, acc, he, hacc => by
    refine readSub_argsAcc f (a :: acc) (ReadSub.appF he) ?_
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ReadSub.appA he
    · exact hacc x hx
  | .bvar _, _, _, hacc => hacc
  | .fvar _, _, _, hacc => hacc
  | .mvar _, _, _, hacc => hacc
  | .sort _, _, _, hacc => hacc
  | .const _ _, _, _, hacc => hacc
  | .lit _, _, _, hacc => hacc
  | .lam _ _ _ _, _, _, hacc => hacc
  | .forallE _ _ _ _, _, _, hacc => hacc
  | .letE _ _ _ _ _, _, _, hacc => hacc
  | .mdata _ _, _, _, hacc => hacc
  | .proj _ _ _, _, _, hacc => hacc

theorem readSub_getAppArgs {senv : StructEnv} {r : Lean.Expr} {Δ : SrcCtx} {e : Lean.Expr}
    (hR : ReadSub senv r Δ e) : ∀ a ∈ e.getAppArgs, ReadSub senv r Δ a := by
  intro a ha
  rw [getAppArgs_eq] at ha
  exact readSub_argsAcc e [] hR (fun x hx => by cases hx) a (Array.mem_toArray.mp ha)

theorem readSub_getElem! {senv : StructEnv} {r : Lean.Expr} {Δ : SrcCtx} {a : Array Lean.Expr}
    (h : ∀ x ∈ a, ReadSub senv r Δ x) {i : Nat} (hi : i < a.size) : ReadSub senv r Δ a[i]! := by
  rw [getElem!_pos a i hi]
  exact h _ (Array.getElem_mem hi)

theorem bool_false_true {b : Bool} (h : b = true) (hf : b = false) : False := by
  rw [hf] at h
  cases h

/-- `isAppOfArity nm k` fixes the argument count. -/
theorem argsT_length_of_arity : ∀ (e : Lean.Expr) (nm : Name) (k : Nat),
    e.isAppOfArity nm k = true → (argsT e).length = k
  | .app f _, nm, k + 1, h => by
    rw [argsT_app, List.length_append, argsT_length_of_arity f nm k h]
    all_goals rfl
  | .app _ _, _, 0, h => (bool_false_true h rfl).elim
  | .const _ _, _, 0, _ => rfl
  | .const _ _, _, _ + 1, h => (bool_false_true h rfl).elim
  | .bvar _, _, _, h => (bool_false_true h rfl).elim
  | .fvar _, _, _, h => (bool_false_true h rfl).elim
  | .mvar _, _, _, h => (bool_false_true h rfl).elim
  | .sort _, _, _, h => (bool_false_true h rfl).elim
  | .lit _, _, _, h => (bool_false_true h rfl).elim
  | .lam _ _ _ _, _, _, h => (bool_false_true h rfl).elim
  | .forallE _ _ _ _, _, _, h => (bool_false_true h rfl).elim
  | .letE _ _ _ _ _, _, _, h => (bool_false_true h rfl).elim
  | .mdata _ _, _, _, h => (bool_false_true h rfl).elim
  | .proj _ _ _, _, _, h => (bool_false_true h rfl).elim

theorem machInstCall?_args {senv : StructEnv} {e : Lean.Expr} {c : Name} {ks : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr}
    (h : machInstCall? senv e = some (c, ks, res, args)) :
    (inlSpine e []).2 = args ∧ ks.length = args.length := by
  unfold machInstCall? at h
  split at h
  · rename_i heq0
    split at h
    · split at h
      · rename_i hlen
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, -, rfl⟩ := h
        refine ⟨?_, ?_⟩
        · rw [heq0]
          all_goals rfl
        · first
            | exact (beq_iff_eq.mp hlen).symm
            | exact (Nat.eq_of_beq_eq_true hlen).symm
            | (simp at hlen; omega)
      · cases h
    · cases h
  · cases h

theorem machInstCallS?_args {senv : StructEnv} {e : Lean.Expr} {c : Name} {ks : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr}
    (h : machInstCallS? senv e = some (c, ks, ty, args)) :
    (inlSpine e []).2 = args ∧ ks.length = args.length := by
  unfold machInstCallS? at h
  split at h
  · rename_i heq0
    split at h
    · split at h
      · rename_i hlen
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, -, rfl⟩ := h
        refine ⟨?_, ?_⟩
        · rw [heq0]
          all_goals rfl
        · first
            | exact (beq_iff_eq.mp hlen).symm
            | exact (Nat.eq_of_beq_eq_true hlen).symm
            | (simp at hlen; omega)
      · cases h
    · cases h
  · cases h

/-- `memCall?`'s operands are the array entries 0, 3, 4, 5, 6 (MachMemory.lean:36-38). -/
theorem memCall?_ops {natOf : Lean.Expr → Option Nat} {e : Lean.Expr} {combo : Bool} {aw dw : Nat}
    {dom : Lean.Expr} {ops : List Lean.Expr}
    (h : Sparkle.Compiler.MachMemory.memCall? natOf e = some (combo, aw, dw, dom, ops)) :
    dom = e.getAppArgs[0]! ∧
      ops = [e.getAppArgs[3]!, e.getAppArgs[4]!, e.getAppArgs[5]!, e.getAppArgs[6]!] := by
  unfold Sparkle.Compiler.MachMemory.memCall? at h
  simp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, -, rfl, rfl⟩ := h
        exact ⟨rfl, rfl⟩
    · cases h

/-- `memCall?` succeeds only at a 7-argument memory application (MachMemory.lean:27-30). -/
theorem memCall?_arity {natOf : Lean.Expr → Option Nat} {e : Lean.Expr}
    {r : Bool × Nat × Nat × Lean.Expr × List Lean.Expr}
    (h : Sparkle.Compiler.MachMemory.memCall? natOf e = some r) :
    e.isAppOfArity ``Sparkle.Core.Signal.Signal.memory 7 = true ∨
      e.isAppOfArity ``Sparkle.Core.Signal.Signal.memoryComboRead 7 = true := by
  cases h1 : e.isAppOfArity ``Sparkle.Core.Signal.Signal.memory 7
  · cases h2 : e.isAppOfArity ``Sparkle.Core.Signal.Signal.memoryComboRead 7
    · exfalso
      unfold Sparkle.Compiler.MachMemory.memCall? at h
      first
        | (simp [h1, h2] at h; done)
        | (simp [h1, h2] at h)
        | (simp only [h1, h2, Bool.false_eq_true, if_false, ite_false] at h; cases h)
    · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## 4. V1: the kept call site gives every argument (rev2 §3.4, exact types) -/

/-- rev2 V1, consumption at `instStep`: from the kept call site, every argument is a reader input at the same `Δ`
and every non-domain argument has its callee kind; lengths agree. -/
theorem instSite_args {SK : SrcKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {Δ : SrcCtx}
    {e : Lean.Expr} {org : InstOrigin} {c : Name} {ks : List MixedGateBinder} {res : MixedGateBinder}
    {args : List Lean.Expr}
    (hC : CallSrcKinds SK senv p en) (hM : MemSrcKinds SK senv p en)
    (hR : ReadSub senv (midExpr en) Δ e) (hS : InstSite senv e org c ks res args) :
    ks.length = args.length ∧
    ∀ kind arg, (kind, arg) ∈ ks.zip args →
      ReadSub senv (midExpr en) Δ arg ∧ (kind ≠ .domain → SK (Δ ++ inCtx p) arg kind) := by
  cases org with
  | ord =>
    have hS' : machInstCall? senv e = some (c, ks, res, args) := hS
    obtain ⟨hsp, hlen⟩ := machInstCall?_args hS'
    refine ⟨hlen, ?_⟩
    intro kind arg hmem
    refine ⟨?_, fun hk => hC.1 Δ e c ks res args kind arg hR hS' hmem hk⟩
    have harg : arg ∈ args := (List.of_mem_zip hmem).2
    rw [← hsp] at harg
    exact readSub_inlSpine e [] hR (fun a ha => by cases ha) arg harg
  | field i => exact False.elim hS
  | mem combo aw dw =>
    obtain ⟨dom, ops, hm, -, hks, -, hargs⟩ := hS
    subst hks
    subst hargs
    obtain ⟨hdom, hops⟩ := memCall?_ops hm
    have hlen7 : (argsT e).length = 7 := by
      rcases memCall?_arity hm with ha | ha
      · exact argsT_length_of_arity e _ 7 ha
      · exact argsT_length_of_arity e _ 7 ha
    have hsz : e.getAppArgs.size = 7 := by
      first
        | (rw [getAppArgs_eq, List.size_toArray]; exact hlen7)
        | (rw [getAppArgs_eq]; simp [hlen7])
    have hall := readSub_getAppArgs hR
    have hRd : ReadSub senv (midExpr en) Δ dom := by
      rw [hdom]
      exact readSub_getElem! hall (by omega)
    have hRo : ∀ o ∈ ops, ReadSub senv (midExpr en) Δ o := by
      rw [hops]
      intro o ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> exact readSub_getElem! hall (by omega)
    refine ⟨?_, ?_⟩
    · rw [hops]
      all_goals rfl
    · intro kind arg hmem
      have hmem' : (kind, arg) ∈ (MixedGateBinder.domain, dom) ::
          [MixedGateBinder.bits aw, .bits dw, .bool, .bits aw].zip ops := hmem
      rcases List.mem_cons.mp hmem' with h0 | h1
      · have hk : kind = .domain := congrArg Prod.fst h0
        have ha : arg = dom := congrArg Prod.snd h0
        subst hk
        subst ha
        exact ⟨hRd, fun hne => (hne rfl).elim⟩
      · exact ⟨hRo arg (List.of_mem_zip h1).2, fun _ => hM Δ e combo aw dw dom ops kind arg hR hm h1⟩

/-- rev2 V1, consumption at `instSStep` (args as above with `hC.2`; params by `sparam`). -/
theorem instSiteS_args {SK : SrcKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {Δ : SrcCtx}
    {e : Lean.Expr} {c : Name} {ks : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr}
    (hC : CallSrcKinds SK senv p en) (hR : ReadSub senv (midExpr en) Δ e)
    (hS : machInstCallS? senv e = some (c, ks, ty, args)) :
    ks.length = args.length ∧
    (∀ kind arg, (kind, arg) ∈ ks.zip args →
      ReadSub senv (midExpr en) Δ arg ∧ (kind ≠ .domain → SK (Δ ++ inCtx p) arg kind)) ∧
    (∀ resTy q, instRes ty args = some resTy → q ∈ resTy.getAppArgs.toList →
      ReadSub senv (midExpr en) Δ q) := by
  obtain ⟨hsp, hlen⟩ := machInstCallS?_args hS
  refine ⟨hlen, ?_, fun resTy q hres hq => ReadSub.sparam hR hS hres hq⟩
  intro kind arg hmem
  refine ⟨?_, fun hk => hC.2 Δ e c ks ty args kind arg hR hS hmem hk⟩
  have harg : arg ∈ args := (List.of_mem_zip hmem).2
  rw [← hsp] at harg
  exact readSub_inlSpine e [] hR (fun a ha => by cases ha) arg harg

/-! ## 5. LK2 piece: the binder list of the fuel `shapePost` (FS:186-187) -/

/-- `shapePost` succeeded: its binders are the inputs, one per call entry, the slot names with their kinds, and
the stored lets `(name, kind)` of the FINAL state (explicit, not existential as in `shapePost_decomp`). -/
theorem shapePost_binders {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead}
    {v : Lean.Expr} {sp : MachineShape} (h : shapePost ai p m st v = some sp) :
    sp.binders = p.bs ++ instBinders sp.insts ++ st.names.toList.zip st.kinds.toList ++
      st.lets.toList.map (fun l => (l.1, l.2.1)) := by
  unfold shapePost at h
  try dsimp only at h
  repeat' first
    | (replace h := ite_none_inv h)
    | (replace h := bind_inv h; obtain ⟨_, _, h⟩ := h)
    | (replace h := Option.bind_eq_some_iff.mp h; obtain ⟨_, _, h⟩ := h)
    | (split at h)
  all_goals first
    | (cases h; done)
    | skip
  all_goals
    try (replace h := ite_else_none_inv h)
    have hsp := Option.some.inj h
    subst hsp
    first
      | rfl
      | (congr 1; congr 1; funext l; obtain ⟨a, b, c⟩ := l; rfl)
      | (congr 2; funext l; obtain ⟨a, b, c⟩ := l; rfl)

/-- The LET part of `shapePost_binders`, by index (for LK2: the binder of let `a`). -/
theorem shapePost_letBinders {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead}
    {v : Lean.Expr} {sp : MachineShape} (h : shapePost ai p m st v = some sp) :
    ∃ pre : List (Name × MixedGateBinder),
      sp.binders = pre ++ st.lets.toList.map (fun l => (l.1, l.2.1)) ∧
      pre = p.bs ++ instBinders sp.insts ++ st.names.toList.zip st.kinds.toList :=
  ⟨_, shapePost_binders h, rfl⟩

/-! ## 6. LK0 lemmas (`phKind`, `PhKindingLaws`, `LetKindOk`) -/

theorem phKind_in (bs : List (Name × MixedGateBinder)) (st : MachRead) (i : Nat) :
    phKind bs st (machIn i) = (bs.reverse[i]?).map (·.2) := rfl

theorem phKind_slot (bs : List (Name × MixedGateBinder)) (st : MachRead) (i : Nat) :
    phKind bs st (machSlot i) = st.kinds[i]? := rfl

theorem phKind_let (bs : List (Name × MixedGateBinder)) (st : MachRead) (j : Nat) :
    phKind bs st (machLet j) = (st.lets[j]?).map (·.2.1) := rfl

theorem phKind_inst (bs : List (Name × MixedGateBinder)) (st : MachRead) (k : Nat) :
    phKind bs st (machInstOut k) = (st.insts[k]?).map (·.2.2) := rfl

theorem phKind_bvar (bs : List (Name × MixedGateBinder)) (st : MachRead) (j : Nat) :
    phKind bs st (.bvar j) = none := rfl

/-- State extension of the three lookups `phKind` reads (kinds, lets, call entries). -/
def PhExt (st st' : MachRead) : Prop :=
  (∀ (i : Nat) (k : MixedGateBinder), st.kinds[i]? = some k → st'.kinds[i]? = some k) ∧
  (∀ (j : Nat) (l : Name × MixedGateBinder × Lean.Expr), st.lets[j]? = some l → st'.lets[j]? = some l) ∧
  (∀ (k : Nat) (c : Name × List Nat × MixedGateBinder), st.insts[k]? = some c → st'.insts[k]? = some c)

theorem phExt_refl (st : MachRead) : PhExt st st :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

theorem phExt_trans {st₁ st₂ st₃ : MachRead} (h₁ : PhExt st₁ st₂) (h₂ : PhExt st₂ st₃) : PhExt st₁ st₃ :=
  ⟨fun i k h => h₂.1 i k (h₁.1 i k h), fun j l h => h₂.2.1 j l (h₁.2.1 j l h),
    fun k c h => h₂.2.2 k c (h₁.2.2 k c h)⟩

/-- `phKind` only extends along a state extension (§3.2: "`phKind` only extends → `mono`"). -/
theorem phKind_ext {bs : List (Name × MixedGateBinder)} {st st' : MachRead} (hx : PhExt st st')
    {x : Lean.Expr} {k : MixedGateBinder} (h : phKind bs st x = some k) : phKind bs st' x = some k := by
  obtain ⟨hK, hL, hI⟩ := hx
  revert h
  unfold phKind
  split
  · exact id
  · exact hK _ k
  · intro h
    obtain ⟨l, hl, hk⟩ := Option.map_eq_some_iff.mp h
    exact Option.map_eq_some_iff.mpr ⟨l, hL _ l hl, hk⟩
  · intro h
    obtain ⟨l, hl, hk⟩ := Option.map_eq_some_iff.mp h
    exact Option.map_eq_some_iff.mpr ⟨l, hI _ l hl, hk⟩
  · intro h
    cases h

/-- `LetKindOk` along a state extension: old lets by `mono`, new lets by `hnew`. -/
theorem letKindOk_ext {HK : PhKinding} (HKL : PhKindingLaws HK) {bs : List (Name × MixedGateBinder)}
    {st st' : MachRead} (h : LetKindOk HK bs st) (hx : PhExt st st')
    (hnew : ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr),
      st'.lets[j]? = some (nm, kd, v) → st.lets[j]? = none → HK (phKind bs st') v kd) :
    LetKindOk HK bs st' := by
  intro j nm kd v hj
  cases hs : st.lets[j]? with
  | none => exact hnew j nm kd v hj hs
  | some l =>
    have h' := hx.2.1 j l hs
    rw [hj] at h'
    injection h' with h''
    subst h''
    exact HKL.mono _ _ v kd (fun x kx hk => phKind_ext hx hk) (h j nm kd v hs)

/-- No push (same lets, e.g. a slot push G2/G20 or an entry push): `LetKindOk` by `mono` alone. -/
theorem letKindOk_sameLets {HK : PhKinding} (HKL : PhKindingLaws HK) {bs : List (Name × MixedGateBinder)}
    {st st' : MachRead} (h : LetKindOk HK bs st) (hx : PhExt st st') (hL : st'.lets = st.lets) :
    LetKindOk HK bs st' := by
  refine letKindOk_ext HKL h hx ?_
  intro j nm kd v hj hs
  rw [hL, hs] at hj
  cases hj

theorem letKindOk_empty {HK : PhKinding} {bs : List (Name × MixedGateBinder)} {st : MachRead}
    (h : st.lets = #[]) : LetKindOk HK bs st := by
  intro j nm kd v hj
  rw [h] at hj
  first
    | cases hj
    | (simp at hj)

theorem instArgKinds_empty {senv : StructEnv} {st : MachRead} (h : st.insts = #[]) :
    InstArgKinds senv st := by
  intro k c js r kinds hk _
  rw [h] at hk
  first
    | cases hk
    | (simp at hk)

/-- The start state `{}` (G21: no lets, no entries) satisfies `ReadInv` for every `HK`. -/
theorem readInv_empty {HK : PhKinding} {senv : StructEnv} {p : ShapePre} :
    ReadInv HK senv p ({} : MachRead) :=
  ⟨instProv_init, letKindOk_empty rfl, instArgKinds_empty rfl⟩

/-- `var` at any free variable (every placeholder is one). -/
theorem phKindingLaws_fvar_iff {HK : PhKinding} (HKL : PhKindingLaws HK)
    (Γ : Lean.Expr → Option MixedGateBinder) (x : FVarId) (k : MixedGateBinder) :
    HK Γ (.fvar x) k ↔ Γ (.fvar x) = some k :=
  HKL.var Γ (.fvar x) k (Or.inr ⟨x, rfl⟩)

/-- `var` at `_machLet j` in a state's context: the stored let kind. -/
theorem phKindingLaws_let_iff {HK : PhKinding} (HKL : PhKindingLaws HK) (bs : List (Name × MixedGateBinder))
    (st : MachRead) (j : Nat) (k : MixedGateBinder) :
    HK (phKind bs st) (machLet j) k ↔ (st.lets[j]?).map (·.2.1) = some k :=
  HKL.var (phKind bs st) (machLet j) k (Or.inr ⟨_, rfl⟩)

/-- §3.2 row R1: a `_machLet j` of kind `k` names a let STORED at kind `k`. -/
theorem phKindingLaws_let_kind {HK : PhKinding} (HKL : PhKindingLaws HK) {bs : List (Name × MixedGateBinder)}
    {st : MachRead} {j : Nat} {k : MixedGateBinder} {nm : Name} {kd : MixedGateBinder} {v : Lean.Expr}
    (hk : HK (phKind bs st) (machLet j) k) (hj : st.lets[j]? = some (nm, kd, v)) : k = kd := by
  have h := (phKindingLaws_let_iff HKL bs st j k).mp hk
  rw [hj] at h
  have h2 : some kd = some k := h
  exact (Option.some.inj h2).symm

/-! ## 7. LK1 bookkeeping: `convBvar`, vacuous env entries, issued calls -/

/-- G1: the `.bvar` arm returns its input state. -/
theorem convBvar_st {env : List MachVal} {d j : Nat} {st : MachRead} {r : Lean.Expr × MachRead}
    (hr : convBvar env d j st = some r) : r.2 = st := by
  unfold convBvar at hr
  split at hr
  · injection hr with hr1
    subst hr1
    rfl
  · split at hr
    all_goals first
      | (cases hr; done)
      | (injection hr with hr1; subst hr1; rfl)
      | (try simp only [Option.bind_eq_bind] at hr
         obtain ⟨_, _, hr⟩ := Option.bind_eq_some_iff.mp hr
         obtain ⟨_, _, hr⟩ := Option.bind_eq_some_iff.mp hr
         obtain ⟨⟨_, _⟩, _, hr⟩ := Option.bind_eq_some_iff.mp hr
         injection hr with hr1
         subst hr1
         rfl)

/-- A new outermost env entry shifts the index by one (at depth 0). -/
theorem convBvar_cons0 (m : MachVal) (env : List MachVal) (j : Nat) (st : MachRead) :
    convBvar (m :: env) 0 (j + 1) st = convBvar env 0 j st := by
  first
    | (unfold convBvar; simp only [Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, List.getElem?_cons_succ,
        List.length_cons, Nat.add_sub_add_right]; done)
    | (unfold convBvar; simp; done)
    | (simp [convBvar]; done)
    | (unfold convBvar; simp; omega)

theorem convBvar_regs0 (q : Nat) (env : List MachVal) (st : MachRead) :
    convBvar (.regs q :: env) 0 0 st = none := by
  first
    | rfl
    | (simp [convBvar])

theorem convBvar_handle0 (i : Nat) (env : List MachVal) (st : MachRead) :
    convBvar (.handle i :: env) 0 0 st = none := by
  first
    | rfl
    | (simp [convBvar])

theorem convBvar_unit0 (env : List MachVal) (st : MachRead) :
    convBvar (.unit :: env) 0 0 st = none := by
  first
    | rfl
    | (simp [convBvar])

/-- A new env entry on which `convBvar` fails (`.regs`/`.handle`/`.unit`, FD:254) carries no obligation. -/
theorem envKindOk_cons_vac {HK : PhKinding} {p : ShapePre} {st : MachRead} {Δ : SrcCtx}
    {env : List MachVal} (o : Option MixedGateBinder) (m : MachVal)
    (hm : ∀ st' : MachRead, convBvar (m :: env) 0 0 st' = none)
    (h : EnvKindOk HK p st Δ env 0) : EnvKindOk HK p st (o :: Δ) (m :: env) 0 := by
  obtain ⟨hlen, hk⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [List.length_cons]
    omega
  · intro j k x st' _ hj hΔ hk0 hc
    cases j with
    | zero =>
      first
        | exact Option.noConfusion (hc.symm.trans (hm st))
        | (rw [hm] at hc; cases hc)
        | simp_all
    | succ j =>
      have hc' : convBvar env 0 j st = some (x, st') := (convBvar_cons0 m env j st).symm.trans hc
      have hj' : j < 0 + env.length := by
        simp only [List.length_cons] at hj
        omega
      have hΔ' : Δ[j]? = some (some k) := by
        first
          | exact hΔ
          | simpa using hΔ
      exact hk j k x st' (Nat.zero_le j) hj' hΔ' hk0 hc'

theorem eq_zero_of_not_bne {d : Nat} (h : ¬ (d != 0) = true) : d = 0 := by
  cases d with
  | zero => rfl
  | succ k => exact (h rfl).elim

/-- C8 / G10: the float call keeps the call site (`ReadSub.float`), same `Δ`, `env`, `st`. -/
theorem callPreK_conv_float {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead}
    {n2 : Name} {t2 v2 w : Lean.Expr} {nd2 : Bool}
    (hpre : CallPreK HK senv p en (Call.conv env d (.letE nm ty v b nd) st)) (hd : d = 0)
    (hf : Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2) :
    CallPreK HK senv p en
      (Call.conv env 0 (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2) st) := by
  subst hd
  obtain ⟨Δ, hE, hR⟩ := hpre
  exact ⟨Δ, hE, ReadSub.float hR hf⟩

/-- C10 / G13: the let body under a vacuous new env entry, same `st`. -/
theorem callPreK_conv_letVac {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead}
    (m : MachVal) (hm : ∀ st' : MachRead, convBvar (m :: env) 0 0 st' = none)
    (hpre : CallPreK HK senv p en (Call.conv env d (.letE nm ty v b nd) st)) (hd : d = 0) :
    CallPreK HK senv p en (Call.conv (m :: env) 0 b st) := by
  subst hd
  obtain ⟨Δ, hE, hR⟩ := hpre
  exact ⟨_, envKindOk_cons_vac (mixedGateBinderKind? ty) m hm hE, ReadSub.letB hR⟩

/-- H3 (chain let, float). -/
theorem callPreK_chain_float {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    {env : List MachVal} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead}
    {n2 : Name} {t2 v2 w : Lean.Expr} {nd2 : Bool}
    (hpre : CallPreK HK senv p en (Call.chain env (.letE nm ty v b nd) st))
    (hf : Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2) :
    CallPreK HK senv p en
      (Call.chain env (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2) st) := by
  obtain ⟨Δ, hE, hR⟩ := hpre
  exact ⟨Δ, hE, ReadSub.float hR hf⟩

/-- H3 (chain let, vacuous new env entry). -/
theorem callPreK_chain_letVac {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    {env : List MachVal} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead}
    (m : MachVal) (hm : ∀ st' : MachRead, convBvar (m :: env) 0 0 st' = none)
    (hpre : CallPreK HK senv p en (Call.chain env (.letE nm ty v b nd) st)) :
    CallPreK HK senv p en (Call.chain (m :: env) b st) := by
  obtain ⟨Δ, hE, hR⟩ := hpre
  exact ⟨_, envKindOk_cons_vac (mixedGateBinderKind? ty) m hm hE, ReadSub.letB hR⟩

/-- H1 (chain `pure'`): the converted value is the last argument (`appA`), same `Δ`, `env`, `st`. -/
theorem callPreK_chain_pureArg {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    {env : List MachVal} {f x : Lean.Expr} {st : MachRead}
    (hpre : CallPreK HK senv p en (Call.chain env (.app f x) st)) :
    CallPreK HK senv p en (Call.conv env 0 x st) := by
  obtain ⟨Δ, hE, hR⟩ := hpre
  exact ⟨Δ, hE, ReadSub.appA hR⟩

/-! ## 8. LK1 arms (CONDITIONAL on `GoodK` of the table; Hoare-style as `SatP`, FP:476-560) -/

/-- The result's state satisfies `ReadInv`. -/
abbrev StK {α : Type} [HasSt α] (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (a : α) : Prop :=
  ReadInv HK senv p (HasSt.st a)

/-- Every OK result of `x` (against `h`) has a state satisfying `ReadInv`. -/
abbrev SatK {α : Type} [HasSt α] (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (h : Hs)
    (x : BM (Option α)) : Prop :=
  ∀ a, x.run h = some (some a) → StK HK senv p a

section Comb
variable {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs} {α β : Type} [HasSt α]

theorem satK_pure {o : Option α} (ho : ∀ a, o = some a → StK HK senv p a) :
    SatK HK senv p h (FM.pure o) := by
  intro a ha
  rw [run_pure] at ha
  exact ho a (Option.some.inj ha)

theorem satK_okO {a : α} (ha : StK HK senv p a) : SatK HK senv p h (okO a) :=
  satK_pure fun b hb => by
    injection hb with hb1
    subst hb1
    exact ha

theorem satK_failO : SatK HK senv p h (failO : BM (Option α)) :=
  satK_pure fun b hb => by cases hb

theorem satK_bindO [HasSt β] {x : BM (Option β)} {f : β → BM (Option α)} (hx : SatK HK senv p h x)
    (hf : ∀ b, StK HK senv p b → SatK HK senv p h (f b)) : SatK HK senv p h (bindO x f) := by
  intro a ha
  rw [run_bindO] at ha
  obtain ⟨o, ho, ha⟩ := Option.bind_eq_some_iff.mp ha
  cases o with
  | none =>
    have hn : (some none : Option (Option α)) = some (some a) := ha
    cases hn
  | some b => exact hf b (hx b ho) a ha

theorem satK_ite2 {c : Prop} [Decidable c] {x y : BM (Option α)} (hx : c → SatK HK senv p h x)
    (hy : ¬c → SatK HK senv p h y) : SatK HK senv p h (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact hx hc
  · rw [if_neg hc]
    exact hy hc

end Comb

theorem satK_cConv {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodK HK senv p en h) {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead}
    (hpre : CallPreK HK senv p en (Call.conv env d e st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (cConv env d e st) :=
  fun a ha => hG (Call.conv env d e st) hpre hst a ha

theorem satK_cChain {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodK HK senv p en h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hpre : CallPreK HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (cChain env e st) :=
  fun a ha => hG (Call.chain env e st) hpre hst a ha

/-- **G1** (conv `.bvar`, FD:303): no sub-call; the state is unchanged. -/
theorem satK_conv_bvar {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d j : Nat} {st : MachRead} (hst : ReadInv HK senv p st) :
    SatK HK senv p h (convStep senv env d (.bvar j) st) := by
  refine satK_pure ?_
  intro r hr
  show ReadInv HK senv p r.2
  rw [convBvar_st hr]
  exact hst

/-- **G15** (conv `.mdata`, FD:380): FAIL, vacuous. -/
theorem satK_conv_mdata {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d : Nat} {md : MData} {x : Lean.Expr} {st : MachRead} :
    SatK HK senv p h (convStep senv env d (.mdata md x) st) :=
  satK_failO

/-- **G15** (conv `.proj`, FD:381): FAIL, vacuous. -/
theorem satK_conv_proj {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d : Nat} {s : Name} {i : Nat} {x : Lean.Expr} {st : MachRead} :
    SatK HK senv p h (convStep senv env d (.proj s i x) st) :=
  satK_failO

/-- **G10** (conv let, float, FD:363-366): one issued call, same `env`/`st`, `ReadSub.float`. -/
theorem satK_conv_letFloat {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodK HK senv p en h) {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool}
    {st : MachRead} (hpre : CallPreK HK senv p en (Call.conv env d (.letE nm ty v b nd) st))
    (hst : ReadInv HK senv p st) {n2 : Name} {t2 v2 w : Lean.Expr} {nd2 : Bool}
    (hf : Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2) :
    SatK HK senv p h (convStep senv env d (.letE nm ty v b nd) st) := by
  refine satK_ite2 (fun _ => satK_failO) ?_
  intro hd0
  have hd : d = 0 := eq_zero_of_not_bne hd0
  split
  · exact satK_cConv hG (callPreK_conv_float hpre hd ‹_›) hst
  · exfalso
    first
      | (rename_i hne; exact hne _ _ _ _ _ hf)
      | simp_all

/-- **G13** (conv let, `.regs`, FD:371-372): the new env entry is vacuous, same `st`. -/
theorem satK_conv_letRegs {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodK HK senv p en h) {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool}
    {st : MachRead} (hpre : CallPreK HK senv p en (Call.conv env d (.letE nm ty v b nd) st))
    (hst : ReadInv HK senv p st)
    (hnf : ∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2)
    (hnl : (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = false)
    {q : Nat} (hq : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = some q) :
    SatK HK senv p h (convStep senv env d (.letE nm ty v b nd) st) := by
  refine satK_ite2 (fun _ => satK_failO) ?_
  intro hd0
  have hd : d = 0 := eq_zero_of_not_bne hd0
  split
  · exfalso
    first
      | exact hnf _ _ _ _ _ ‹_›
      | simp_all
  · refine satK_ite2 (fun hc => ?_) (fun _ => ?_)
    · exfalso
      first
        | exact bool_false_true hc hnl
        | (rw [hnl] at hc; cases hc)
        | simp_all
    · split
      · exact satK_cConv hG (callPreK_conv_letVac _ (convBvar_regs0 _ env) hpre hd) hst
      · exfalso
        first
          | (have hn : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = none := ‹_›
             rw [hq] at hn
             cases hn)
          | simp_all

/-- **G13** (conv let, `.handle`, FD:373-375): the new env entry is vacuous, same `st`. -/
theorem satK_conv_letHandle {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodK HK senv p en h) {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool}
    {st : MachRead} (hpre : CallPreK HK senv p en (Call.conv env d (.letE nm ty v b nd) st))
    (hst : ReadInv HK senv p st)
    (hnf : ∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2)
    (hnl : (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = false)
    (hq0 : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = none)
    {i : Nat} (hi : machHandleV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = some i) :
    SatK HK senv p h (convStep senv env d (.letE nm ty v b nd) st) := by
  refine satK_ite2 (fun _ => satK_failO) ?_
  intro hd0
  have hd : d = 0 := eq_zero_of_not_bne hd0
  split
  · exfalso
    first
      | exact hnf _ _ _ _ _ ‹_›
      | simp_all
  · refine satK_ite2 (fun hc => ?_) (fun _ => ?_)
    · exfalso
      first
        | exact bool_false_true hc hnl
        | (rw [hnl] at hc; cases hc)
        | simp_all
    · split
      · exfalso
        first
          | (have hn : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = some _ := ‹_›
             rw [hq0] at hn
             cases hn)
          | simp_all
      · split
        · exact satK_cConv hG (callPreK_conv_letVac _ (convBvar_handle0 _ env) hpre hd) hst
        · exfalso
          first
            | (have hn : machHandleV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = none := ‹_›
               rw [hi] at hn
               cases hn)
            | simp_all

/-- **G16, `pure'` sub-arm** (chain, FD:498-499): one issued call at the same `st`, `appA`. -/
theorem satK_chain_pure {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodK HK senv p en h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    {us : List Level} {a1 a2 a3 x : Lean.Expr}
    (he : e = .app (.app (.app (.app (.const ``Sparkle.Core.Circuit.pure' us) a1) a2) a3) x)
    (hpre : CallPreK HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (chainStep senv env e st) := by
  revert he hpre
  unfold chainStep
  split
  · intro _ hpre
    refine satK_bindO (satK_cConv hG (callPreK_chain_pureArg hpre) hst) ?_
    rintro ⟨v', st1⟩ h1
    exact satK_okO h1
  · intro he
    cases he
  · intro he
    cases he
  · intro _ _
    exact satK_failO

/-- **G17, float sub-arm** (chain let, FD:512-515). -/
theorem satK_chain_letFloat {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodK HK senv p en h) {env : List MachVal} {e : Lean.Expr} {nm : Name} {ty v b : Lean.Expr}
    {nd : Bool} {st : MachRead} (he : e = .letE nm ty v b nd)
    (hpre : CallPreK HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st)
    {n2 : Name} {t2 v2 w : Lean.Expr} {nd2 : Bool}
    (hf : Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2) :
    SatK HK senv p h (chainStep senv env e st) := by
  revert he hpre
  unfold chainStep
  split
  · intro he
    cases he
  · intro he
    cases he
  · intro he hpre
    injection he with e1 e2 e3 e4 e5
    subst e1
    subst e2
    subst e3
    subst e4
    subst e5
    split
    · exact satK_cChain hG (callPreK_chain_float hpre ‹_›) hst
    · exfalso
      first
        | (rename_i hne; exact hne _ _ _ _ _ hf)
        | simp_all
  · intro _ _
    exact satK_failO

/-- **G17, `.regs` sub-arm** (chain let, FD:519-520). -/
theorem satK_chain_letRegs {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodK HK senv p en h) {env : List MachVal} {e : Lean.Expr} {nm : Name} {ty v b : Lean.Expr}
    {nd : Bool} {st : MachRead} (he : e = .letE nm ty v b nd)
    (hpre : CallPreK HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st)
    (hnf : ∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2)
    (hnl : (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = false)
    {q : Nat} (hq : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = some q) :
    SatK HK senv p h (chainStep senv env e st) := by
  revert he hpre
  unfold chainStep
  split
  · intro he
    cases he
  · intro he
    cases he
  · intro he hpre
    injection he with e1 e2 e3 e4 e5
    subst e1
    subst e2
    subst e3
    subst e4
    subst e5
    split
    · exfalso
      first
        | exact hnf _ _ _ _ _ ‹_›
        | simp_all
    · refine satK_ite2 (fun hc => ?_) (fun _ => ?_)
      · exfalso
        first
          | exact bool_false_true hc hnl
          | (rw [hnl] at hc; cases hc)
          | simp_all
      · split
        · exact satK_cChain hG (callPreK_chain_letVac _ (convBvar_regs0 _ env) hpre) hst
        · exfalso
          first
            | (have hn : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat _) = none := ‹_›
               rw [hq] at hn
               cases hn)
            | simp_all
  · intro _ _
    exact satK_failO

/-- **G17, `.handle` sub-arm** (chain let, FD:521-522). -/
theorem satK_chain_letHandle {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodK HK senv p en h) {env : List MachVal} {e : Lean.Expr} {nm : Name} {ty v b : Lean.Expr}
    {nd : Bool} {st : MachRead} (he : e = .letE nm ty v b nd)
    (hpre : CallPreK HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st)
    (hnf : ∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2)
    (hnl : (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = false)
    (hq0 : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = none)
    {i : Nat} (hi : machHandleV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = some i) :
    SatK HK senv p h (chainStep senv env e st) := by
  revert he hpre
  unfold chainStep
  split
  · intro he
    cases he
  · intro he
    cases he
  · intro he hpre
    injection he with e1 e2 e3 e4 e5
    subst e1
    subst e2
    subst e3
    subst e4
    subst e5
    split
    · exfalso
      first
        | exact hnf _ _ _ _ _ ‹_›
        | simp_all
    · refine satK_ite2 (fun hc => ?_) (fun _ => ?_)
      · exfalso
        first
          | exact bool_false_true hc hnl
          | (rw [hnl] at hc; cases hc)
          | simp_all
      · split
        · exfalso
          first
            | (have hn : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat _) = some _ := ‹_›
               rw [hq0] at hn
               cases hn)
            | simp_all
        · split
          · exact satK_cChain hG (callPreK_chain_letVac _ (convBvar_handle0 _ env) hpre) hst
          · exfalso
            first
              | (have hn : machHandleV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat _) = none := ‹_›
                 rw [hi] at hn
                 cases hn)
              | simp_all
  · intro _ _
    exact satK_failO

end Tools.ShippingGen3ArgSupply2

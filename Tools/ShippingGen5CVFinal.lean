import Tools.ShippingGen5SM1
import Tools.ShippingGen5RowTypedV
import Tools.ShippingGen5EnvDeclClosed
set_option autoImplicit false
-- D.D-4 final carrier (Issue sparkle-ledger-dd4-final; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §Final). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # The final carrier `CVFinal PT` and the statement `FGLedgerPremisesStmtCV`

* `CVFinal PT : ConstValueRel` is the valuation carrier over the syntactic level instantiation (`CVEKVL`, i.e. `Tools.ShippingGen5ConstValueEVL.CVEKV`) at the fixed level choice `LS env X`
  (`CVLSKV`): `CVFinal PT env X α v := ∃ τ, CVEKVL PT env [] (.const X (LS env X)) τ α v`. `ConstValueFunctional (CVFinal PT)` is proved for EVERY `PT` (no hypothesis).
* `FGLedgerPremisesStmtCV` is `FGLedgerPremisesStmtH` (SM1) with the binder `CV : ConstValueRel` replaced by the explicit parameter `PT : PrimTableK` and `CV := CVFinal PT`.
  The unresolved obligations are NAMED premises (ordinary hypotheses, not axioms): outer `h_D_LBR : OblLbrZero`; inside the entry run (they speak about `envAt cref w`):
  `KernelClosedInvariant`, the two literal rows `LitRows`, `OblRowTypedV` (the `RowTypedAtV` rows, incl. the dependent ones), and the `RowTeleEvAt` rows.
* `fgLedgerPremisesStmtCV_of_H` : H → CV statement (specialise `CV := CVFinal PT`, drop the extra premises). `PT` stays an explicit parameter: neither G-PRIM nor TRUSTED is adopted.
* `DeclConnect (CVFinal PT)`: the unfolding, the uniqueness of the value, and (from `EnvDeclClosed` + the literal rows) the typing of the label. The existence rows stay open (named premises). -/

namespace Tools.ShippingGen5CVFinal
open Lean Sparkle.Compiler.Elab Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Sparkle.IR.Semantics Sparkle.IR.Machine Sparkle.Core Sparkle.Core.Signal
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5SM1
open Tools.ShippingGen5ConstValueEKey (PrimTableK)
open Tools.ShippingGen5ConstValueE (LS)
open Tools.ShippingGen5ConstValueESL (EnvDeclClosed)
open Tools.ShippingGen5ConstValueESoundK (OblLbrZero)
open Tools.ShippingGen5EnvDeclClosed (KernelClosedInvariant envDeclClosed_of_kernel)
open Tools.ShippingGen5ConstValueEVL (RowTeleEvAt CVLSKV cvlskv_functional TDenV WfValV wfValV_nil)
open Tools.ShippingGen5RowTypedV (OblRowTypedV)

/-- The final carrier: `CVEKVL` at the root `const X (LS env X)`, valuation `[]`. Same term as `CVLSKV`. -/
def CVFinal (PT : PrimTableK) : ConstValueRel := fun env X α v => CVLSKV PT env X α v

theorem cvFinal_functional (PT : PrimTableK) : ConstValueFunctional (CVFinal PT) :=
  fun env c _ _ _ _ h h' => cvlskv_functional PT env c h h'

/-- Unfolding: a derivation of `const X (LS env X)` on the valuation carrier. -/
theorem cvFinal_iff (PT : PrimTableK) (env : Environment) (X : Name) (α : Type) (v : α) :
    CVFinal PT env X α v ↔ ∃ τ : Expr, Tools.ShippingGen5ConstValueEVL.CVEKV PT env [] (.const X (LS env X)) τ α v := Iff.rfl

theorem cvFinal_value_unique (PT : PrimTableK) {env : Environment} {X : Name} {α : Type} {v w : α}
    (h : CVFinal PT env X α v) (h' : CVFinal PT env X α w) : v = w :=
  eq_of_heq (cvFinal_functional PT env X α α v w h h').2

theorem cvFinal_levels (PT : PrimTableK) {env : Environment} {X : Name} {α : Type} {v : α} (_ : CVFinal PT env X α v)
    {ci : ConstantInfo} (hci : env.find? X = some ci) : (LS env X).length = ci.levelParams.length :=
  Tools.ShippingGen5ConstValueE.LS_length env X ci hci

/-- The full relation is not functional, so it is never `CVFinal PT` (the step that refutes `FGLedgerPremisesStmtG` at `CV := ⊤`, `Tests/Gen5/CVTopCheck.lean`). -/
theorem not_functional_top (env : Environment) : ¬ ConstValueFunctional (fun (_ : Environment) (_ : Name) (_ : Type) (_ : _) => True) := by
  intro h
  have e : (Unit : Type) = Bool := (h env .anonymous Unit Bool () true trivial trivial).1
  have hb : ∀ a b : Bool, a = b := e ▸ (fun (a b : Unit) => Subsingleton.elim a b)
  exact Bool.noConfusion (hb true false)

theorem cvFinal_ne_top (PT : PrimTableK) (env : Environment) :
    ¬ (CVFinal PT = fun (_ : Environment) (_ : Name) (_ : Type) (_ : _) => True) := by
  intro e
  have := cvFinal_functional PT
  rw [e] at this
  exact not_functional_top env this

/-! ## Named premises -/

/-- The `Nat` / `String` literal rows of `PT` (nullary `tys` rows, not definitions): the condition on `PT` of `denTypedVL_of_rows`. -/
def LitRows (PT : PrimTableK) (env : Environment) : Prop :=
  ∃ rn rs : Tools.ShippingGen5ConstValueE.TyRow,
    PT.tys `Nat [] = some rn ∧ ¬ Tools.ShippingGen5ConstValueE.IsDefn env `Nat ∧ rn.kinds = [] ∧ rn.den [] = some Nat ∧
    PT.tys `String [] = some rs ∧ ¬ Tools.ShippingGen5ConstValueE.IsDefn env `String ∧ rs.kinds = [] ∧ rs.den [] = some String

/-- Soundness of the label: with `EnvDeclClosed` and the literal rows, the derivation's label denotes the Lean type. -/
theorem cvFinal_typed {PT : PrimTableK} {env : Environment} (hcl : EnvDeclClosed env) (hl : LitRows PT env)
    {X : Name} {α : Type} {v : α} (h : CVFinal PT env X α v) : ∃ τ : Expr, TDenV PT env [] τ α := by
  obtain ⟨τ, hd⟩ := h
  obtain ⟨rn, rs, hn, hnnd, hnk, hnT, hs, hsnd, hsk, hsT⟩ := hl
  exact ⟨τ, Tools.ShippingGen5RowTypedV.denTypedVL_of_rows hcl hn hnnd hnk hnT hs hsnd hsk hsT [] _ τ α v (wfValV_nil PT env) hd⟩

/-! ## `DeclConnect (CVFinal PT)` -/

section
variable {ι : Type} {dom : ι → DomainConfig}

/-- What `DeclConnect (CVFinal PT)` says (the definition unfolded: the shape recognizer, the package match, the value of `X` on the carrier, the observation). -/
theorem declConnect_cvFinal_iff (PT : PrimTableK) (env : Environment) (P : Pkgs ι dom) (Tgt : Name → Prop) :
    DeclConnect (CVFinal PT) env P Tgt ↔ ∀ X, Tgt X → ∀ p, P X = some p →
      ∃ (ci : ConstantInfo) (sh : SigShape) (v : sh.Ty), env.find? X = some ci ∧ shapeOf ci = some sh ∧ ShapeMatches sh p.d p.kD ∧
        (∃ τ : Expr, Tools.ShippingGen5ConstValueEVL.CVEKV PT env [] (.const X (LS env X)) τ sh.Ty v) ∧
        ∀ i bools bits, sh.obs (dom := dom) v i bools bits = p.src i bools bits := by
  rw [declConnect_eq]; exact Iff.rfl

/-- The value `DeclConnect` relates to `X` is unique (functionality): two shapes of the same type give the same value. -/
theorem declConnect_cvFinal_unique (PT : PrimTableK) {env : Environment} {X : Name} {sh : SigShape} {v w : sh.Ty}
    (h : CVFinal PT env X sh.Ty v) (h' : CVFinal PT env X sh.Ty w) : v = w := cvFinal_value_unique PT h h'

/-- With `EnvDeclClosed` and the literal rows the label of every related value is typed: the `CV` leg of `DeclConnect` carries a `TDenV`-typed derivation. -/
theorem declConnect_cvFinal_typed {PT : PrimTableK} {env : Environment} (hcl : EnvDeclClosed env) (hl : LitRows PT env)
    {P : Pkgs ι dom} {Tgt : Name → Prop} (h : DeclConnect (CVFinal PT) env P Tgt) :
    ∀ X, Tgt X → ∀ p, P X = some p →
      ∃ (ci : ConstantInfo) (sh : SigShape) (v : sh.Ty), env.find? X = some ci ∧ shapeOf ci = some sh ∧ ShapeMatches sh p.d p.kD ∧
        CVFinal PT env X sh.Ty v ∧ (∃ τ : Expr, TDenV PT env [] τ sh.Ty) ∧
        ∀ i bools bits, sh.obs (dom := dom) v i bools bits = p.src i bools bits := by
  intro X hX p hp
  obtain ⟨ci, sh, v, h1, h2, h3, h4, h5⟩ := (declConnect_eq _ env P Tgt ▸ h) X hX p hp
  exact ⟨ci, sh, v, h1, h2, h3, h4, cvFinal_typed hcl hl h4, h5⟩

end

/-! ## The statement -/

def FGLedgerPremisesStmtCV : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    -- carriers (binders, NOT hypotheses; their characterizing rows are in the registry)
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)        -- D.D-1
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)             -- A.P-05
    -- D.D-3 fixed (GP := genGP lvl (dataOfSound_initsOf lvl) genData₀); D.D-4 fixed (CV := CVFinal PT, PT explicit)
    (lvl : Lean.Expr → Nat)
    (genData₀ : (env : Environment) → (E : ConstantInfo) →
      Option (GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)))
    (PT : PrimTableK)                                                         -- D.D-4 (the table is a parameter; no G-PRIM, no TRUSTED)
    (L : Laws mref cref)                                                      -- A.P-01  (= T1L-01)
    -- outer hypotheses (closed Props)
    (h_C_EN4 : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref)   -- C.EN-4
    (h_C_RK6 : Tools.Prototype.DGenStored2.ReflExprAgree)                                        -- C.RK-6
    (h_C_CV4 : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),                      -- C.CV-4 (= T1L-43)
        machineShape? false [] E senv = some sp →
        ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp))
    (h_D_LBR : OblLbrZero),                                                                      -- named premise: lbr bridge (unresolved)
    ConstValueFunctional (CVFinal PT) ∧
    ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →     -- A.P-02 Start, A.P-04 run, D.D-1 ReflectsAll
      -- named premises on the entry environment (unresolved obligations of the carrier; ordinary hypotheses)
      KernelClosedInvariant (envAt cref w) →                                    -- EnvDeclClosed via OblLbrZero (audit: 0 counterexamples)
      LitRows PT (envAt cref w) →                                               -- Nat / String rows of PT
      OblRowTypedV PT (envAt cref w) →                                          -- RowTypedAtV rows (incl. the dependent ones)
      (∀ (c : Name) (ls : List Level), RowTeleEvAt PT (envAt cref w) c ls) →    -- RowTeleEvAt rows
      -- inner hypotheses; P := genGP lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w), Reach := TgtRun P declName  (Q-F2)
      (∀ c, TgtRun (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) declName c → ∀ q : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) c = some q →      -- h_A_P06
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ c, TgtRun (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) declName c → ∀ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) c = some p →      -- h_D_T4
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
          Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
          ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
            (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
              = some pt.ty.bitWidth) →
      -- conclusion: the tail of the FG_CONNECT body (FG.lean), unchanged except CV := CVFinal PT
      (∃ raw, Post b raw) ∧
      (∃ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) declName = some p) ∧
      (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat),
          genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
      DeclConnect (CVFinal PT) (envAt cref w) (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) (TgtRun (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) declName)

/-- `FGLedgerPremisesStmtCV` follows from `FGLedgerPremisesStmtH`: `CV := CVFinal PT`, `ConstValueFunctional` is `cvFinal_functional` (so the H conjunct is not needed), the extra premises are dropped. -/
theorem fgLedgerPremisesStmtCV_of_H : FGLedgerPremisesStmtH → FGLedgerPremisesStmtCV := by
  unfold FGLedgerPremisesStmtH FGLedgerPremisesStmtCV
  intro h ι dom mref cref ReflectsAll Post lvl genData₀ PT L h_C_EN4 h_C_RK6 h_C_CV4 _
  obtain ⟨-, hmain⟩ := h ReflectsAll Post lvl genData₀ (CVFinal PT) L h_C_EN4 h_C_RK6 h_C_CV4
  exact ⟨cvFinal_functional PT, fun declName parameters mctx cctx w w' b D hw _ _ _ _ hA6 hT4 =>
    hmain declName parameters mctx cctx w w' b D hw hA6 hT4⟩

theorem fgLedgerPremisesStmtCV_of_G : Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtG → FGLedgerPremisesStmtCV :=
  fun h => fgLedgerPremisesStmtCV_of_H (fgLedgerPremisesStmtH_of_G h)

/-- The first conjunct is a theorem, not a hypothesis on a carrier: for the inner premise, `EnvDeclClosed` follows from the kernel invariant and the bridge. -/
theorem envDeclClosed_of_premises {env : Environment} (hz : OblLbrZero) (h : KernelClosedInvariant env) : EnvDeclClosed env :=
  envDeclClosed_of_kernel hz h

end Tools.ShippingGen5CVFinal

#print axioms Tools.ShippingGen5CVFinal.cvFinal_functional
#print axioms Tools.ShippingGen5CVFinal.cvFinal_ne_top
#print axioms Tools.ShippingGen5CVFinal.cvFinal_typed
#print axioms Tools.ShippingGen5CVFinal.declConnect_cvFinal_iff
#print axioms Tools.ShippingGen5CVFinal.declConnect_cvFinal_typed
#print axioms Tools.ShippingGen5CVFinal.fgLedgerPremisesStmtCV_of_H
#print axioms Tools.ShippingGen5CVFinal.fgLedgerPremisesStmtCV_of_G

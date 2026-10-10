import Tools.ShippingChildLegacy

/-! # The body of a child synthesis keeps the child invariant

`synthesizeFromConst` — the body the memoised entry runs — on its four
routes: the certified shape (`synthesizeCertified`), the mixed certified shape
(`synthesizeMixedCertified`, the harness), the machine route
(`synthesizeMachineCertified`), and the legacy tail (`openRecordInputs`, the
`lambdaTelescope`, `splitReturnLeaves`, `bindInputsLegacy`, `emitLeaves`,
`finishSynth`). Each is walked (`vc`) on every outcome, given the memoised
child entry keeps the invariant; the translator inside is `translateRel`.

So `BodyRel` holds under the generic laws alone (`bodyRel`), and with it the
entry keeps the invariant at every depth with no compiler-specific premise. -/
namespace Tools.ShippingChildInv
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
variable (L : RefLaws mref cref) (D : Nat)

@[keeps] theorem bindInputPort_keepsC {α : Type} (fv : FVarId) (bn : String)
    (ty : Sparkle.IR.Type.HWType) (k : CompilerM α)
    (hk : KeepsC mctx mref cctx cref (J L D) k) :
    KeepsC mctx mref cctx cref (J L D) (bindInputPort fv bn ty k) :=
  keepsC_iff.mpr (bindInputPort_tripleC L D fv bn ty k (keepsC_iff.mp hk))

@[keeps] theorem bindCertifiedInputs_keepsC {α : Type} (k : CompilerM α)
    (hk : KeepsC mctx mref cctx cref (J L D) k) :
    ∀ l : List ((Name × GateBinder) × FVarId),
      KeepsC mctx mref cctx cref (J L D) (bindCertifiedInputs k l)
  | [] => by unfold bindCertifiedInputs; exact hk
  | ((_, .domain), _) :: rest => by
    unfold bindCertifiedInputs; exact bindCertifiedInputs_keepsC k hk rest
  | ((nm, .signal n), id) :: rest => by
    unfold bindCertifiedInputs
    exact bindInputPort_keepsC L D _ _ _ _ (bindCertifiedInputs_keepsC k hk rest)

@[keeps] theorem emitLeaves_keepsC (hC : ChildKeeps L D) (b : Bool) (cacheRef : IO.Ref (Lean.ExprStructMap String))
    (leaves : List (String × Lean.Expr)) (fw : Option String) (idx : Nat) :
    KeepsC mctx mref cctx cref (J L D)
      (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cacheRef
        (profLogIO b) leaves fw idx) :=
  keepsC_iff.mpr (emitLeaves_tripleC L D b cacheRef
    (fun e hint top named => keepsC_iff.mp (translateRel L D hC mctx cctx e hint top named)) leaves fw idx)

@[keeps] theorem finishSynth_keeps (declName : Name) (st : Sparkle.IR.Builder.CircuitState) :
    Keeps mctx mref cctx cref (J L D) (finishSynth declName [] false st) :=
  keeps_iff.mpr (finishSynth_triple L D declName st)

@[keeps] theorem synthesizeMixedCertified_keeps (hC : ChildKeeps L D) (b : Bool) (declName : Name)
    (bs : List (Name × MixedGateBinder)) (body : Lean.Expr) :
    Keeps mctx mref cctx cref (J L D)
      (synthesizeMixedCertified (fun e hint top named => translateExprToWire e hint top named)
        (profLogIO b) declName bs body) :=
  harnessRel_of L (translateRel L) D hC mctx cctx b declName bs body

@[keeps] theorem synthesizeMachineCertified_keeps (hC : ChildKeeps L D) (b : Bool) (declName : Name)
    (shape : MachineShape) :
    Keeps mctx mref cctx cref (J L D)
      (synthesizeMachineCertified (fun e hint top named => translateExprToWire e hint top named)
        (profLogIO b) declName shape) :=
  machine_keeps L (harnessRel_of L (translateRel L)) D hC b declName shape

@[keeps] theorem synthesizeCertified_keeps (hC : ChildKeeps L D) (b : Bool) (declName : Name)
    (bs : List (Name × GateBinder)) (body : Lean.Expr) :
    Keeps mctx mref cctx cref (J L D)
      (synthesizeCertified (fun e hint top named => translateExprToWire e hint top named)
        (profLogIO b) declName bs body) := by
  vc

theorem bindInputsLegacy_keepsC (xs : Array Lean.Expr) (k : CompilerM String)
    (hk : KeepsC mctx mref cctx cref (J L D) k) :
    ∀ (n i : Nat), xs.size - i < n →
      KeepsC mctx mref cctx cref (J L D) (bindInputsLegacy [] false xs i k)
  | 0, _, h => by omega
  | n + 1, i, h => by
    have ih := fun (h' : xs.size - (i + 1) < n) => bindInputsLegacy_keepsC xs k hk n (i + 1) h'
    unfold bindInputsLegacy
    vc


theorem arrayMapM_map_keeps {α β : Type} (f : α → MetaM β) (as : Array α)
    (hf : ∀ a, Keeps mctx mref cctx cref (J L D) (f a)) :
    ∀ (n i : Nat) (bs : Array β), as.size - i < n →
      Keeps mctx mref cctx cref (J L D) ((privConst% Init.Data.Array.Basic Array.mapM.map) f as i bs)
  | 0, _, _, h => by omega
  | n + 1, i, bs, h => by
    have ih := fun bs (h' : as.size - (i + 1) < n) => arrayMapM_map_keeps f as hf n (i + 1) bs h'
    unfoldPriv Init.Data.Array.Basic Array.mapM.map
    vc

@[keeps] theorem Keeps.arrayMapM {α β : Type} (f : α → MetaM β) (as : Array α)
    (hf : ∀ a, Keeps mctx mref cctx cref (J L D) (f a)) :
    Keeps mctx mref cctx cref (J L D) (as.mapM f) := by
  unfold Array.mapM
  exact arrayMapM_map_keeps L D f as hf _ 0 _ (Nat.lt_succ_self _)

theorem anyM_loop_keeps {α : Type} (p : α → MetaM Bool) (as : Array α)
    (hp : ∀ a, Keeps mctx mref cctx cref (J L D) (p a)) (stop : Nat) (hs : stop ≤ as.size) :
    ∀ (n j : Nat), stop - j < n → Keeps mctx mref cctx cref (J L D) (Array.anyM.loop p as stop hs j)
  | 0, _, h => by omega
  | n + 1, j, h => by
    have ih := fun (h' : stop - (j + 1) < n) => anyM_loop_keeps p as hp stop hs n (j + 1) h'
    unfold Array.anyM.loop
    vc

@[keeps] theorem Keeps.allM {α : Type} (p : α → MetaM Bool) (as : Array α) (start stop : Nat)
    (hp : ∀ a, Keeps mctx mref cctx cref (J L D) (p a)) :
    Keeps mctx mref cctx cref (J L D) (Array.allM p as start stop) := by
  have hl := fun (q : α → MetaM Bool) (hq : ∀ a, Keeps mctx mref cctx cref (J L D) (q a)) stop hs j =>
    anyM_loop_keeps L D q as hq stop hs (stop - j + 1) j (Nat.lt_succ_self _)
  unfold Array.allM Array.anyM
  vc

theorem openRecordInputs_walk_keeps (body : Lean.Expr) (params : Array Lean.Expr) (inner : Lean.Expr) :
    ∀ (fuel : Nat) (mctx : Meta.Context) (cctx : Core.Context) (idx : Nat) (binders : Array Lean.Expr)
      (subst : Array (Lean.FVarId × Lean.Expr)) (opened : Bool),
      Keeps mctx mref cctx cref (J L D) (openRecordInputs.walk body params inner fuel idx binders subst opened)
  | 0, mctx, cctx, idx, binders, subst, opened => by unfold openRecordInputs.walk; vc
  | fuel + 1, mctx, cctx, idx, binders, subst, opened => by
    have ih := fun (mctx : Meta.Context) (cctx : Core.Context) idx binders subst opened =>
      openRecordInputs_walk_keeps body params inner fuel mctx cctx idx binders subst opened
    unfold openRecordInputs.walk
    vc

@[keeps] theorem openRecordInputs_keeps (body : Lean.Expr) :
    Keeps mctx mref cctx cref (J L D) (openRecordInputs body) := by
  have hw := fun (params : Array Lean.Expr) (inner : Lean.Expr) (mctx : Meta.Context) (cctx : Core.Context) fuel idx binders subst opened =>
    openRecordInputs_walk_keeps L D body params inner fuel mctx cctx idx binders subst opened
  vc

@[keeps] theorem splitReturnLeaves_keeps (e : Lean.Expr) (pre : Option String) :
    Keeps mctx mref cctx cref (J L D) (splitReturnLeaves e pre) := by
  unfold splitReturnLeaves
  vc

theorem body_keeps (hC : ChildKeeps L D) (b : Bool) (declName : Name) (ci : ConstantInfo) (isInst : Lean.Expr → Bool) :
    Keeps mctx mref cctx cref (J L D)
      (synthesizeFromConst (fun e h t n => translateExprToWire e h t n) (profLogIO b)
        declName [] false true ci isInst) := by
  have hb := fun (mctx : Meta.Context) (cctx : Core.Context) (xs : Array Lean.Expr) i (k : CompilerM String)
      (hk : KeepsC mctx mref cctx cref (J L D) k) =>
    bindInputsLegacy_keepsC L D xs k hk (xs.size - i + 1) i (Nat.lt_succ_self _)
  vc

/-- **`BodyRel`, proved.** -/
theorem bodyRel : BodyRel L :=
  fun D hC mctx cctx b declName ci isInst => body_keeps L D hC b declName ci isInst

/-- **The memoised child entry keeps the invariant at every depth** — under
the generic laws alone. -/
theorem childKeeps (D : Nat) : ChildKeeps L D :=
  childKeeps_all L (bodyRel L) D

end Tools.ShippingChildInv

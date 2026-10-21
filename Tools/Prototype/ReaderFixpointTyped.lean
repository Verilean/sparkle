import Tools.Prototype.ReaderFixpointSpec
import Tools.ShippingMachineClosesData

/-! # Unit LCQ prototype: the Expr → typed `letFields` / `quote` bridge for the reader's `let` table

BUILT: runs q22 (parts), q24 (final) exit 0.  No sorry / axiom / native_decide.  Production unchanged.

Consumer (step 1): `letsClose_of_data` (Tools/ShippingMachineClosesData.lean:177) takes `d.ok`, `hbody : d.shape.body =
quote d.dom … d.packed` and `halias : d.letsAliasOk = true`, i.e. `aliasOk bpos vpos (nIn+|ss|) d.letFields` on the TYPED
`d.letFields = d.ls.map toField`.  The generation path (`ShippingMachineCommand.readMachine`) obtains `d.ls` by `unq`
(a `partial def`: opaque, not unfoldable) + `splitLets` + `unField` and CHECKS `quote … packed = shape.body`; that checked
equation `hbody` is the only link between `d.ls` and the shape, so the bridge goes through it.

Bridge (step 2), all PROVED:
* `canon_machConcatE`, `canon_eq_bvar`: `machCanonAp` keeps the `machConcatE` spine and a `bvar`;
* `peel`: from `machPack dom (lfs ++ rest) = some (w,P)` and `machCanonAp P = quote … (packLets Ls core).2`
  (`rest ≠ []`) field `i` of `lfs` canonicalises to the `quote` of typed field `i` (`quote` of the `concat` spine is
  `concatE`, so the `i`-th operand of both spines is read off by `Expr.app` injectivity);
* `shapePost_pack`: a `shapePost` success is `machCanonAp (machPack dom' (lfs ++ outF ++ slotF))` with `lfs` the `mapM` of
  `machField dom' kind (machClose kI n k 0 value)` over `st.lets` (and `outF ≠ []` when `p.outs ≠ []`),
  `layout.lets = st.lets.size`; `shapePre_outs_ne` gives `p.outs ≠ []`;
* `typed_letsAlias`: `shapePost ai p m st v = some sp`, `NoLetAlias st.lets`, `NoLetBvar st.lets`, `d.shape = sp`,
  `d.ok`, `hbody` ⟹ `d.letsAliasOk`.  Proof idea: a typed `let` field that is `bitsInput q` quotes to
  `bvar (count-1-vpos q)`; its Expr field is `machClose … value` for a non-placeholder value, which is a `bvar` only at
  an index `≥ k` (`machClose_bvar`), so `vpos q < nIn+|ss|` and the alias check holds vacuously; a Bool `let` field is
  `mux …`, never a variable.
* `machineShapeN_typed` (step 3): on `machineShapeN … = some (some sp)` the SAME `st`, `v` carry `RdOk`/`NoLetAlias`/
  `LetOk` AND `shapePost … = some sp`, and `NoLetBvar st.lets → ∀ d, … → d.letsAliasOk ∧ LetsClose`.

Premises: those of `machineShapeN_lets` (`RootFloatRange`, `LiftRange`, `Inst1Range`, `SigTyRange senv`, `ShapeInOk`),
plus OPEN `NoLetBvar st.lets` (no `let` value is a bare loose `bvar`; not derived from `RdOk`).  Not covered: the shipped
`machineShape?` (needs `machNorm = execNorm`, `TwinCoverAt`), existence of `d` (the `unq` step) and `d.ok`/`hbody`
themselves (the endpoint's own checks, assumed as the consumer assumes them). -/
namespace Tools.Prototype.ReaderTyped
open Lean Sparkle.Compiler.Elab Tools.ShippingUnifiedSource Tools.ShippingMachineDenote
open Tools.ShippingMachineEntry

theorem canon_machConcatE (dom : Lean.Expr) (m n : Nat) (a b : Lean.Expr) :
    ∃ K, machCanonAp (machConcatE dom m n a b) = .app (.app K (machCanonAp a)) (machCanonAp b) := by
  refine ⟨machCanonAp (mkApp4 (.const ``HAppend.hAppend [.zero, .zero, .zero]) (machSigT dom m)
    (machSigT dom n) (machSigT dom (m + n))
    (mkApp3 (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat []) dom (inlNatLit m)
      (inlNatLit n))), ?_⟩
  unfold machConcatE
  simp [mkApp6, machCanonAp, machCanonApNode]

theorem canon_eq_bvar {e : Lean.Expr} {b : Nat} (h : machCanonAp e = .bvar b) : e = .bvar b := by
  cases e <;> simp only [machCanonAp] at h <;> first | exact h | skip
  all_goals
    exfalso
    unfold machCanonApNode at h
    split at h <;> simp_all [mkApp, mkApp4, mkApp5]


theorem machPack_cons_ne {dom : Lean.Expr} {f g : Nat × Lean.Expr} {t : List (Nat × Lean.Expr)}
    {r : Nat × Lean.Expr} (h : machPack dom (f :: g :: t) = some r) :
    ∃ n b, machPack dom (g :: t) = some (n, b) ∧ r = (f.1 + n, machConcatE dom f.1 n f.2 b) := by
  conv at h => lhs; unfold machPack
  cases hp : machPack dom (g :: t) with
  | none => simp [hp] at h
  | some nb =>
    obtain ⟨n, b⟩ := nb
    simp only [hp, Option.some.injEq] at h
    exact ⟨n, b, rfl, h.symm⟩

/-- The `quote` of a `packLets` spine is the `concatE` spine; matched against the `machPack` of the
`machCanonAp`-canonicalised packed value, the fields line up one by one. -/
theorem peel (dom dom2 : Lean.Expr) (bB bV : Nat → Lean.Expr) :
    ∀ (Ls : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c))
      (lfs rest : List (Nat × Lean.Expr)), lfs.length = Ls.length → rest ≠ [] →
      ∀ (w : Nat) (P : Lean.Expr), machPack dom (lfs ++ rest) = some (w, P) →
      machCanonAp P = quote dom2 bB bV (packLets Ls core).2 →
      ∀ (i : Nat) (x : Nat × Lean.Expr) (y : Σ w : Nat, Term (.bits w)), lfs[i]? = some x →
        Ls[i]? = some y → machCanonAp x.2 = quote dom2 bB bV y.2
  | [], _, _, _, _, _, _, _, _, _, _, i, x, y, _, hy => by simp at hy
  | L :: Ls, c, core, lfs, rest, hlen, hne, w, P, hP, hq, i, x, y, hx, hy => by
    cases lfs with
    | nil => simp at hlen
    | cons f lfs' =>
      have hlen' : lfs'.length = Ls.length := by simpa using hlen
      cases hr : (lfs' ++ rest) with
      | nil => exact absurd (by simpa using (by simpa using hr : lfs' = [] ∧ rest = []).2) hne
      | cons g t =>
        rw [List.cons_append, hr] at hP
        obtain ⟨n, b, hb, hPe⟩ := machPack_cons_ne hP
        have hP' : P = machConcatE dom f.1 n f.2 b := by
          have := congrArg Prod.snd hPe; simpa using this
        subst hP'
        obtain ⟨K, hK⟩ := canon_machConcatE dom f.1 n f.2 b
        rw [hK] at hq
        have hq' : (Lean.Expr.app (Lean.Expr.app K (machCanonAp f.2)) (machCanonAp b)) =
            concatE dom2 _ _ (quote dom2 bB bV L.2) (quote dom2 bB bV (packLets Ls core).2) := hq
        unfold concatE mkApp6 at hq'
        injection hq' with h1 hb'
        injection h1 with _ ha'
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
          subst hx; subst hy; exact ha'
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx hy
          exact peel dom dom2 bB bV Ls core lfs' rest hlen' hne n b (by rw [hr]; exact hb) hb' i x y hx hy


theorem mapM_get {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r →
      r.length = l.length ∧ ∀ (i : Nat) (y : β), r[i]? = some y → ∃ x, l[i]? = some x ∧ f x = some y
  | [], r, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases hb : f a with
    | none => simp [hb] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hb, hl] at h
      | some bs =>
        simp [hb, hl] at h
        subst h
        obtain ⟨hl', hg⟩ := mapM_get f l bs hl
        refine ⟨by simp [hl'], ?_⟩
        intro i y hy
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hy; subst hy
          exact ⟨a, rfl, hb⟩
        | succ i => simp only [List.getElem?_cons_succ] at hy ⊢; exact hg i y hy

open Tools.ShippingReaderFuel in
/-- What the `body` of a `shapePost` success is: `machCanonAp` of the `machPack` of the closed `let`
fields, then the results and slots (the results are non-empty when `p.outs` is). -/
theorem shapePost_pack {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr}
    {sp : MachineShape} (hne : p.outs ≠ []) (h : shapePost ai p m st v = some sp) :
    ∃ (dom' : Lean.Expr) (lfs outF slotF : List (Nat × Lean.Expr)) (w : Nat) (P : Lean.Expr),
      st.lets.toList.mapM (fun x => machField dom' x.2.1
        (machClose st.insts.size st.kinds.size (Array.size st.lets) 0 x.2.2)) = some lfs ∧
      outF ≠ [] ∧ machPack dom' (lfs ++ outF ++ slotF) = some (w, P) ∧
      sp.body = machCanonAp P ∧ sp.layout.lets = st.lets.size := by
  unfold shapePost at h
  dsimp only at h
  split at h; · simp at h
  split at h; · simp at h
  split at h; · simp at h

  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨domE, _, dm, _, lfs, hlfs, h⟩ := h
  cases ht : p.tup? with
  | some ks =>
    simp only [ht, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨parts, _, fs, _, packed, _, outF, hoF, slotF, _, pk, hpk, h⟩ := h
    subst hoF
    split at h
    · cases h
      exact ⟨dm.1, lfs, [packed], slotF, pk.1, pk.2, hlfs, by simp, hpk, rfl, rfl⟩
    · simp at h
  | none =>
    simp only [ht, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨outEs, _, h⟩ := h
    by_cases hl : (outEs.length != p.outs.length) = true
    · simp [hl] at h
    · rw [if_neg hl] at h
      have hl' : outEs.length = p.outs.length := by simpa using hl
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨outF, hout, slotF, _, pk, hpk, h⟩ := h
      split at h
      · cases h
        refine ⟨dm.1, lfs, outF, slotF, pk.1, pk.2, hlfs, ?_, hpk, rfl, rfl⟩
        intro hnil
        subst hnil
        have := (mapM_get _ _ _ hout).1
        simp only [List.length_nil, List.length_zip, hl', Nat.min_self] at this
        exact hne (List.length_eq_zero_iff.mp this.symm)
      · simp at h


open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingLetsAliasInv
open Tools.ShippingReaderFuel Tools.ShippingMixedSourceBridge

/-- **PREMISE (OPEN, not derived)**: no `let` value is a bare loose `bvar`.  `machClose` leaves a `bvar`
alone, so a `let` value `bvar b` could be read back as a variable at a `let` position; the reader
instantiates every binder with a placeholder, so no such value is expected, but this has not been
proved for `machConv`/`machChain`/`machLoopBody` (LC2 lists it as missing too). -/
def NoLetBvar (lets : MachLets) : Prop := ∀ l ∈ lets.toList, ∀ b, l.2.2 ≠ .bvar b

theorem aliasOk_of_lt {bpos vpos : Nat → Nat} {base : Nat} {fs : List (Σ w : Nat, Term (.bits w))}
    (h : ∀ (i : Nat) (fi : Σ w : Nat, Term (.bits w)) (n : Nat), fs[i]? = some fi →
      varPos? bpos vpos fi.2 = some n → n < base) :
    aliasOk bpos vpos base fs = true := by
  unfold aliasOk
  rw [List.all_eq_true]
  intro fi hmem
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
  cases hv : varPos? bpos vpos fi.2 with
  | none => simp
  | some n => simp [h i fi n hi hv]

/-- **The typed bridge.**  For the shape `shapePost … st v` of a reader state `st` whose `let` table has
no `let`-placeholder value (`NoLetAlias`) and no bare `bvar` value (`NoLetBvar`), every typed `MachineData`
that passes `ok` and whose `shape.body` is the `quote` of its packed term (the equation the generation
path checks, `ShippingMachineCommand.readMachine`: `q.equal shape.body`) passes `letsAliasOk`.  The
typed data are NOT assumed: `d.ls` is only constrained by that checked equation and `ok`. -/
theorem typed_letsAlias {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr}
    {sp : MachineShape} (hne : p.outs ≠ []) (h : shapePost ai p m st v = some sp)
    (hna : NoLetAlias st.lets) (hnb : NoLetBvar st.lets) (d : MachineData) (hs : d.shape = sp)
    (hok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) :
    d.letsAliasOk = true := by
  obtain ⟨dom', lfs, outF, slotF, w, P, hlfs, hoF, hpk, hbd, hlay⟩ := shapePost_pack hne h
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hok
  obtain ⟨hlen, hlets, _, _, _, _, _, _, _, _, _, _, _, hscoped, _⟩ := hok
  rw [hs] at hlets
  rw [hlay] at hlets
  obtain ⟨hfitL, _⟩ := scoped_fit d.letBs d.letFields _ hscoped
  have hcount : d.shape.binders.length = (d.nIn + d.ss.length) + st.lets.size := by
    have : d.letBs.length = d.shape.binders.length - (d.nIn + d.ss.length) := by
      simp [MachineData.letBs]
    omega
  have hq : machCanonAp P = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) (packLets d.letFields d.core.2).2 := by
    rw [← hbd, ← hs]; exact hbody
  obtain ⟨hlfsLen, hlfsGet⟩ := mapM_get _ _ _ hlfs
  have hLs : lfs.length = d.letFields.length := by
    simp only [Array.length_toList] at hlfsLen; omega
  have hpeel := peel dom' d.dom _ _ d.letFields d.core.2 lfs (outF ++ slotF) hLs
    (List.append_ne_nil_of_left_ne_nil hoF _) w P (by rw [← List.append_assoc]; exact hpk) hq
  refine aliasOk_of_lt ?_
  intro i fi n hi hv
  have hik : i < st.lets.size := by
    have := (List.getElem?_eq_some_iff.mp hi).1; omega
  have hil : i < lfs.length := by omega
  obtain ⟨w', t⟩ := fi
  cases t <;> simp [varPos?] at hv
  rename_i q
  have hx := hpeel i lfs[i] _ (by simp) hi
  obtain ⟨y, hy, hyf⟩ := hlfsGet i lfs[i] (by simp)
  have hymem : y ∈ st.lets.toList := List.mem_of_getElem? hy
  have hnl := hna y hymem
  have hnbv := hnb y hymem
  obtain ⟨nm, kind, val⟩ := y
  simp only at hyf hnl hnbv
  have hxq : machCanonAp lfs[i].2 = .bvar (d.shape.binders.length - 1 - d.vpos q) := hx
  have hcb := canon_eq_bvar hxq
  cases kind with
  | bool =>
    simp only [machField, Option.some.injEq] at hyf
    rw [← hyf] at hcb
    exact absurd hcb (by intro hh; injection hh)
  | domain => simp [machField] at hyf
  | bits k =>
    simp only [machField, Option.some.injEq] at hyf
    rw [← hyf] at hcb
    have := machClose_bvar hnl (hnbv) _ hcb
    omega


open Tools.ShippingReaderFuel in
theorem shapePre_outs_ne {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo}
    {senv : StructEnv} {p : ShapePre} (h : shapePre sm ps ci senv = some p) : p.outs ≠ [] := by
  unfold shapePre at h
  split at h
  · split at h
    · simp at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a, _, h⟩ := h
      split at h
      · simp only [Option.bind_some] at h
        split at h
        · simp at h
        · cases h; simp
      · obtain ⟨x, _, h⟩ := Option.bind_eq_some_iff.mp h
        split at h
        · simp at h
        · rename_i hc
          cases h
          intro hnil
          have hnil' : x.snd = [] := hnil
          apply hc
          simp [hnil']
  · simp at h




open Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec

/-- **Consumer-ready lemma on `machineShapeN` success** (PROVED, conditional on the four named reader premises
`RootFloatRange`, `LiftRange`, `Inst1Range`, `SigTyRange senv` and the input condition `ShapeInOk`, exactly as
`machineShapeN_lets`).  A success `sp` is `shapePost … st v` of a final state `st` and body value `v` (the SAME
`st`, `v` that carry `RdOk st`, `NoLetAlias st.lets`, `LetOk st.lets.size v`), and — if that `st` also has no
bare-`bvar` `let` value (`NoLetBvar`, OPEN premise) — every typed `MachineData` over `sp` that passes `ok`
and whose body is the `quote` of its packed term passes `letsAliasOk`, hence `LetsClose` (`letsClose_of_data`)
in every context.  Nothing about the typed data is assumed beyond the two checks the generation path makes. -/
theorem machineShapeN_typed {senv : StructEnv}
    (hroot : RootFloatRange) (hlift : LiftRange) (hinst1 : Inst1Range) (hsig : SigTyRange senv)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hin : ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p →
      execNorm senv p.e = some en → ShapeInOk senv (shapeMid senv p en))
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      (NoLetBvar st.lets → ∀ (d : MachineData), d.shape = sp → d.ok = true →
        d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
          (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed →
        d.letsAliasOk = true ∧
        ∀ {declName : Name} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
          (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State),
          Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape) := by
  obtain ⟨p, en, st, v, hp, hen, hrd, hna, hlo, hpost⟩ :=
    machineShapeN_lets hroot hlift hinst1 hsig Tools.ShippingLetsReaderInv.bundleIotaRange hin h
  refine ⟨p, en, st, v, hp, hen, hrd, hna, hlo, hpost, ?_⟩
  intro hnb d hs hok hbody
  have halias := typed_letsAlias (shapePre_outs_ne hp) hpost hna hnb d hs hok hbody
  exact ⟨halias, fun mctx mref cctx cref => letsClose_of_data d hok hbody halias mctx mref cctx cref⟩

#print axioms canon_machConcatE
#print axioms peel
#print axioms shapePost_pack
#print axioms shapePre_outs_ne
#print axioms typed_letsAlias
#print axioms machineShapeN_typed

end Tools.Prototype.ReaderTyped

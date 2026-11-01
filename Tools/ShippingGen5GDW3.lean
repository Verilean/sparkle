import Tools.ShippingGen5GDCover1
import Tools.ShippingGen5Cover3Canon
import Tools.Prototype.ReaderFixpointTyped
import Tools.ShippingGen5DataOfPure2
set_option autoImplicit false
-- NOT BUILT (draft). Freeze scripts/gen5/GD_W3_WITNESS.md.

namespace Tools.ShippingGen5GDW3
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingReaderFuel Tools.ShippingReaderLenOk
  Tools.ShippingReaderFuelShapeR5 Tools.ShippingShapeDecomp Tools.ShippingMachineAuto Tools.ShippingGen5Cover5
  Tools.ShippingGen5GDCover1 Tools.ShippingGen5Cover3Canon Tools.Prototype.ReaderTyped
  Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMixedSourceBridge Tools.ShippingMachineEntry Tools.ShippingGen5Sem

/-- The binders of a `shapePost` success end with the `let` binders (`kd` of each `st.lets` entry). -/
theorem shapePost_binders {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr}
    {sp : MachineShape} (h : shapePost ai p m st v = some sp) :
    ∃ A : List (Name × MixedGateBinder),
      sp.binders = A ++ st.lets.toList.map (fun l => (l.1, l.2.1)) := by
  unfold shapePost at h
  dsimp only at h
  split at h; · simp at h
  split at h; · simp at h
  split at h; · simp at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨domE, _, dm, _, lfs, hlfs, h⟩ := h
  cases ht : p.tup? with
  | some ks =>
    simp only [ht, Option.bind_eq_some_iff] at h
    obtain ⟨parts, _, fs, _, packed, _, outF, hoF, slotF, _, pk, hpk, h⟩ := h
    split at h
    · cases h; exact ⟨_, rfl⟩
    · simp at h
  | none =>
    simp only [ht, Option.bind_eq_some_iff] at h
    obtain ⟨outEs, _, h⟩ := h
    by_cases hl : (outEs.length != p.outs.length) = true
    · simp [hl] at h
    · rw [if_neg hl] at h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨outF, hout, slotF, _, pk, hpk, h⟩ := h
      split at h
      · cases h; exact ⟨_, rfl⟩
      · simp at h


theorem letsTyped_get {bpos vpos : Nat → Nat} {kb kv : Nat} {vw : Nat → Nat} {K : Nat → Option SType} :
    ∀ (ls : List (Σ s : SType, Term s)) (p j : Nat) (l : Σ s : SType, Term s),
      LetsTyped bpos vpos kb kv vw K p ls → ls[j]? = some l → K (p + j) = some l.1
  | [], _, _, _, _, h => by simp at h
  | l0 :: ls, p, j, l, ht, h => by
    obtain ⟨_, _, hk, ht'⟩ := ht
    cases j with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; simpa using hk
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have := letsTyped_get ls (p + 1) j l ht' h
      rwa [show p + 1 + j = p + (j + 1) by omega] at this

/-- `machCanonAp` of a Bool field: the condition is `machCanonAp` of the condition (no assumption on `dom`). -/
theorem machCanonAp_machBoolBits' (dom e : Lean.Expr) :
    machCanonAp (machBoolBits dom e) = machBoolBits (machCanonAp dom) (machCanonAp e) := by
  simp [machBoolBits, machLitE, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB, machCanonAp, machCanonApNode,
    machCanonAp_natLit]


/-- The core: the `let` equation, from the final `shapePost` and the structural facts of `d`. -/
theorem letQuoteEqC_of_post {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v0 : Lean.Expr}
    {sp : MachineShape} (hne : p.outs ≠ []) (hpost : shapePost ai p m st v0 = some sp)
    {d : MachineData} (hs : d.shape = sp) (hok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hag : ShapeAgree d st) : LetQuoteEqC d st := by
  obtain ⟨dom', lfs, outF, slotF, w, P, hlfs, hoF, hpk, hbd, hlay⟩ := shapePost_pack hne hpost
  obtain ⟨A, hA⟩ := shapePost_binders hpost
  have hlt := Tools.ShippingGen5DataOfPure2.ok_letsTyped hok
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hok
  obtain ⟨hlen, hlets, _⟩ := hok
  rw [hs, hlay] at hlets
  have hcount : d.shape.binders.length = (d.nIn + d.ss.length) + st.lets.size := by
    have : d.letBs.length = d.shape.binders.length - (d.nIn + d.ss.length) := by
      simp [MachineData.letBs]
    omega
  have hAlen : A.length = d.nIn + d.ss.length := by
    have h1 : d.shape.binders.length = A.length + st.lets.size := by
      rw [hs, hA]; simp
    omega
  have hq : machCanonAp P = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) (packLets d.letFields d.core.2).2 := by
    rw [← hbd, ← hs]; exact hbody
  obtain ⟨hlfsLen, hlfsGet⟩ := mapM_get _ _ _ hlfs
  have hLs : lfs.length = d.letFields.length := by
    simp only [Array.length_toList, MachineData.letFields, List.length_map] at hlfsLen ⊢
    have := hag.lets
    omega
  have hpeel := peel dom' d.dom _ _ d.letFields d.core.2 lfs (outF ++ slotF) hLs
    (List.append_ne_nil_of_left_ne_nil hoF _) w P (by rw [← List.append_assoc]; exact hpk) hq
  have hbin : kDOf d + st.insts.size + st.kinds.size + st.lets.size = d.shape.binders.length := by
    have h1 := hag.insts
    have h2 := hag.nIn
    have h3 := hag.slots
    have h4 : d.shape.insts.length = st.insts.size := by rw [h1]; simp
    unfold kDOf
    omega
  intro j hj nm kd v hv
  rw [hbin]
  have hjl : j < st.lets.size := by rw [← hag.lets]; exact hj
  have hjlfs : j < lfs.length := by rw [hLs]; simp [MachineData.letFields]; exact hj
  have hLj : d.letFields[j]? = some (toField (d.ls[j]'hj).1 (d.ls[j]'hj).2) := by
    simp [MachineData.letFields, hj]
  have hx := hpeel j lfs[j] _ (by simp) hLj
  obtain ⟨y, hy, hyf⟩ := hlfsGet j lfs[j] (by simp)
  have hyv : y = (nm, kd, v) := by
    have : st.lets.toList[j]? = some (nm, kd, v) := by simpa using hv
    rw [hy] at this; exact Option.some.inj this
  subst hyv
  simp only at hyf
  -- the sort of the `let`
  have hK : sortOf kd = some (d.ls[j]'hj).1 := by
    have := letsTyped_get d.ls (d.nIn + d.ss.length) j (d.ls[j]'hj) hlt (by simp [hj])
    unfold MachineData.K at this
    rw [hs, hA, ← hAlen, List.getElem?_append_right (by omega)] at this
    simpa [hv] using this
  generalize d.ls[j]'hj = lj at hK hx ⊢
  obtain ⟨s, t⟩ := lj
  cases kd with
  | domain => simp [sortOf] at hK
  | bits n =>
    simp only [sortOf, Option.some.injEq] at hK
    subst hK
    simp only [machField, Option.some.injEq] at hyf
    rw [← hyf] at hx
    exact hx.symm
  | bool =>
    simp only [sortOf, Option.some.injEq] at hK
    subst hK
    simp only [machField, Option.some.injEq] at hyf
    rw [← hyf, machCanonAp_machBoolBits'] at hx
    simp only [toField, Tools.ShippingUnifiedSource.quote] at hx
    injection hx with h1 _
    injection h1 with h2 _
    injection h2 with _ h4
    exact h4.symm

/-- W3 (body): for the SAME `st` as `stateSide_of_production` / `shapeAgree_witness_from`, `ShapeAgree d st` and `LetQuoteEqC d st`.
Assumed: `hbr` (C.CV-4, as in G1/W1). Not shown: that production's fuel supplies `hbr`'s `n`. -/
theorem letQuoteEqC_witness_from
    (hbr : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, machineShapeF n false [] E senv true = some (some sp))
    {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfFrom lvl E senv sp tin fl = some d) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st ∧ LetQuoteEqC d st := by
  obtain ⟨n, p, en, st0, env, st1, st, v, w, hag⟩ := shapeAgree_witness_from hbr h hd
  obtain ⟨hsp, hok, hbody, _⟩ := Tools.ShippingGen5DataOf.dataOfFrom_sound lvl hd
  obtain ⟨hpre, _, _, _, _, hpost, _⟩ := id w
  exact ⟨n, p, en, st0, env, st1, st, v, w, hag,
    letQuoteEqC_of_post (shapePre_outs_ne hpre) hpost hsp hok hbody hag⟩

theorem letQuoteEqC_witness
    (hbr : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, machineShapeF n false [] E senv true = some (some sp))
    {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st ∧ LetQuoteEqC d st := by
  unfold Tools.ShippingGen5DataOf.dataOfAt at hd
  split at hd
  · cases hd
  · exact letQuoteEqC_witness_from hbr h hd

end Tools.ShippingGen5GDW3

#print axioms Tools.ShippingGen5GDW3.shapePost_binders
#print axioms Tools.ShippingGen5GDW3.letsTyped_get
#print axioms Tools.ShippingGen5GDW3.machCanonAp_machBoolBits'
#print axioms Tools.ShippingGen5GDW3.letQuoteEqC_of_post
#print axioms Tools.ShippingGen5GDW3.letQuoteEqC_witness_from
#print axioms Tools.ShippingGen5GDW3.letQuoteEqC_witness

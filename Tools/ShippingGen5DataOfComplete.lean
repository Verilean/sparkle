import Tools.ShippingGen5ReadKinds
import Tools.ShippingGen5DataOfDims
import Tools.ShippingMachineClose
set_option autoImplicit false
-- NOT BUILT by an issue-linked clean build (agent build: Tools.ShippingGen5DataOfComplete 371 jobs, Tests.Gen5.DataOfCompleteCheck 768 jobs, exit 0; the clean build is the coder's). No sorry / axiom / native_decide.

/-! # G6: `dataOfFrom_complete_of_quote`

The converse of `dataOfFrom_sound`: if `d` is built from a quotation (`shape.body = quote … d.packed`) and passes `d.ok`,
`dataOfFrom` returns `some d`. Statement: `scripts/gen5/DG_G6_COMPLETE_FREEZE.md`. No new premise; `houts` (the sort of each
output field) is a hypothesis of the theorem, NOT discharged here (G8). Not proved: that such a `d` exists (G8 / G9). -/

namespace Tools.ShippingGen5DataOf
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineCommand
open Tools.ShippingMachineEntry Tools.ShippingReaderInputs Tools.ShippingReaderApp
open Tools.ShippingReaderTerm Tools.ShippingGen5DataOfPure Tools.ShippingGen5DataOfPure2
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingReaderMachine Tools.ShippingGen5ReadKinds Tools.ShippingReaderKinds Tools.ShippingReaderComplete
open Sparkle.Core Sparkle.IR.Machine Sparkle.Compiler.Elab

theorem splitLets_pack : ∀ (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c)),
    splitLets fs.length (packLets fs core) = some (fs, ⟨c, core⟩)
  | [], _, _ => rfl
  | f :: rest, c, core => by
    have ih := splitLets_pack rest core
    show splitLets (rest.length + 1) ⟨_, Term.concat f.2 (packLets rest core).2⟩ = _
    simp only [splitLets]
    have : splitLets rest.length ⟨_, (packLets rest core).2⟩ = some (rest, ⟨c, core⟩) := ih
    rw [this]
    rfl

theorem splitFields_packList : ∀ (rest : List (Σ w : Nat, Term (.bits w))) (f : Σ w : Nat, Term (.bits w)),
    splitFields (rest.length + 1) (packList f rest) = some (f :: rest)
  | [], f => rfl
  | g :: gs, f => by
    have ih := splitFields_packList gs g
    show splitFields (gs.length + 2) ⟨_, Term.concat f.2 (packList g gs).2⟩ = _
    simp only [splitFields]
    have : splitFields (gs.length + 1) ⟨_, (packList g gs).2⟩ = some (g :: gs) := ih
    rw [this]
    rfl

theorem splitFields_pack (fs : List (Σ w : Nat, Term (.bits w))) (h : 0 < fs.length) :
    splitFields fs.length (packAll fs) = some fs := by
  cases fs with
  | nil => simp at h
  | cons f rest => exact splitFields_packList rest f

theorem unField_toField {k : MixedGateBinder} {s : SType} (t : Term s) (h : sortOf k = some s) :
    unField k (toField s t) = some ⟨s, t⟩ := by
  cases k with
  | domain => simp [sortOf] at h
  | bool =>
    simp only [sortOf, Option.some.injEq] at h
    subst h
    rfl
  | bits n =>
    simp only [sortOf, Option.some.injEq] at h
    subst h
    rfl

theorem typedFields_of_quote_fields {ks : List MixedGateBinder} {ts : List (Σ s : SType, Term s)}
    (h : Tools.ShippingMachineClose.Zip₂ (fun k t => sortOf k = some t.1) ks ts) :
    typedFields ks (ts.map fun t => toField t.1 t.2) = some ts := by
  induction h with
  | nil => rfl
  | @cons k t ks' ts' hk _ ih =>
    unfold typedFields at ih ⊢
    simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons]
    have e := unField_toField t.2 hk
    simp only [e, ih]
    rfl

def anyTerms : {ss : List SType} → Terms ss → List (Σ s : SType, Term s)
  | _, .nil => []
  | _, .cons (s := s) t ts => ⟨s, t⟩ :: anyTerms ts

theorem anyTerms_sorts : ∀ {ss : List SType} (ts : Terms ss), (anyTerms ts).map (·.1) = ss
  | _, .nil => rfl
  | _, .cons (s := s) t ts => by simp [anyTerms, anyTerms_sorts ts]

theorem terms_cons_heq {s : SType} {ss ss' : List SType} (t : Term s) (a : Terms ss') (b : Terms ss)
    (h : ss' = ss) (hab : HEq a b) : HEq (Terms.cons t a : Terms (s :: ss')) (Terms.cons t b) := by
  subst h
  rw [eq_of_heq hab]

theorem anyTerms_heq : ∀ {ss : List SType} (ts : Terms ss), HEq (termsOfAny (anyTerms ts)) ts
  | _, .nil => HEq.rfl
  | _, .cons (s := s) t ts =>
    terms_cons_heq t _ ts (anyTerms_sorts ts) (anyTerms_heq ts)

open Tools.ShippingMachineClose (Zip₂)

theorem zip_of_K (ks : List MixedGateBinder) (K : Nat → Option SType)
    (hK : ∀ p, K p = ks[p]?.bind sortOf) :
    ∀ (ts : List (Σ s : SType, Term s)) (p : Nat),
      (∀ i t, ts[i]? = some t → K (p + i) = some t.1) → p + ts.length ≤ ks.length →
      Zip₂ (fun k t => sortOf k = some t.1) ((ks.drop p).take ts.length) ts
  | [], _, _, _ => by simpa using Zip₂.nil
  | t :: ts, p, h, hl => by
    have hp : p < ks.length := by simp at hl; omega
    have hk0 : K p = some t.1 := by simpa using h 0 t rfl
    rw [hK p, List.getElem?_eq_getElem hp] at hk0
    have hd : ks.drop p = ks[p] :: ks.drop (p + 1) := List.drop_eq_getElem_cons hp
    rw [hd, List.length_cons, List.take_succ_cons]
    refine Zip₂.cons ?_ (zip_of_K ks K hK ts (p + 1) ?_ ?_)
    · simpa using hk0
    · intro i t' ht'
      have := h (i + 1) t' (by simpa using ht')
      have e : p + (i + 1) = p + 1 + i := by omega
      rwa [e] at this
    · simp at hl; omega

theorem zip_map_left {α β γ : Type} {R : α → β → Prop} {S : γ → β → Prop} (f : α → γ)
    (hRS : ∀ a b, R a b → S (f a) b) : ∀ {as : List α} {bs : List β},
    Zip₂ R as bs → Zip₂ S (as.map f) bs
  | _, _, .nil => .nil
  | _, _, .cons h rest => .cons (hRS _ _ h) (zip_map_left f hRS rest)

theorem letsTyped_get {bpos vpos : Nat → Nat} {kb kv : Nat} {vw : Nat → Nat} {K : Nat → Option SType} :
    ∀ (ls : List (Σ s : SType, Term s)) (p : Nat), LetsTyped bpos vpos kb kv vw K p ls →
      ∀ i t, ls[i]? = some t → K (p + i) = some t.1
  | [], _, _, i, t, h => by simp at h
  | l :: ls, p, h, 0, t, ht => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
    subst ht
    simpa using h.2.2.1
  | l :: ls, p, h, i + 1, t, ht => by
    have := letsTyped_get ls (p + 1) h.2.2.2 i t (by simpa using ht)
    have e : p + (i + 1) = p + 1 + i := by omega
    rw [e]; exact this

theorem ok_packed_wf {d : MachineData} (h : d.ok = true) : d.packed.WF d.kb d.kv d.vw := by
  unfold MachineData.ok at h
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.2.2.2.2.2.2.2.2.1

theorem ok_fields_ne {d : MachineData} (h : d.ok = true) : d.fields.isEmpty = false := by
  unfold MachineData.ok at h
  simp only [Bool.and_eq_true] at h
  have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  simpa using this

theorem dataOfTail_complete_mk (shape : MachineShape) (nIn : Nat) (dom : Lean.Expr)
    (ls outs : List (Σ s : SType, Term s)) (nl : List (Σ s : SType, Term s))
    (hok : (mkData shape nIn dom ls outs nl).ok = true)
    (hbl : shape.binders.length = nIn + shape.layout.slots.length + shape.layout.lets)
    (hss : nl.length = shape.layout.slots.length) (hls : ls.length = shape.layout.lets)
    (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs outs) :
    dataOfTail shape nIn dom _ (mkData shape nIn dom ls outs nl).packed = some (mkData shape nIn dom ls outs nl) := by
  have hfl : (mkData shape nIn dom ls outs nl).fields =
      outs.map (fun t => toField t.1 t.2) ++ nl.map (fun t => toField t.1 t.2) := by
    simp only [MachineData.fields, mkData]
    rw [termsOfAny_fields]
  have hlf : (mkData shape nIn dom ls outs nl).letFields = ls.map (fun t => toField t.1 t.2) := rfl
  have hco : (mkData shape nIn dom ls outs nl).core =
      packAll (outs.map (fun t => toField t.1 t.2) ++ nl.map (fun t => toField t.1 t.2)) := by
    simp only [MachineData.core]; rw [hfl]
  have hnO : shape.layout.outs.length = outs.length := houts.length_eq
  have hne := ok_fields_ne hok
  rw [hfl] at hne
  have hpos : 0 < (outs.map (fun t => toField t.1 t.2) ++ nl.map (fun t => toField t.1 t.2)).length := by
    cases hh : (outs.map (fun t => toField t.1 t.2) ++ nl.map (fun t => toField t.1 t.2)) with
    | nil => rw [hh] at hne; simp at hne
    | cons _ _ => simp
  have e1 : splitLets shape.layout.lets ⟨_, (mkData shape nIn dom ls outs nl).packed⟩ =
      some (ls.map (fun t => toField t.1 t.2), (mkData shape nIn dom ls outs nl).core) := by
    have h := splitLets_pack (mkData shape nIn dom ls outs nl).letFields (mkData shape nIn dom ls outs nl).core.2
    rw [hlf] at h
    have hl : (ls.map (fun t => toField t.1 t.2)).length = shape.layout.lets := by simp [hls]
    rw [hl] at h
    exact h
  have e2 : splitFields (shape.layout.outs.length + shape.layout.slots.length)
      (mkData shape nIn dom ls outs nl).core =
      some (outs.map (fun t => toField t.1 t.2) ++ nl.map (fun t => toField t.1 t.2)) := by
    rw [hco, hnO, ← hss]
    have := splitFields_pack _ hpos
    simpa using this
  have hK : ∀ p, (mkData shape nIn dom ls outs nl).K p = (shape.binders.map (·.2))[p]?.bind sortOf := by
    intro p
    show (shape.binders[p]?).bind (fun b => sortOf b.2) = _
    rw [List.getElem?_map]
    cases shape.binders[p]? <;> rfl
  have hkl : (shape.binders.map (·.2)).length = shape.binders.length := List.length_map ..
  -- lets
  have hz1 : Zip₂ (fun k t => sortOf k = some t.1) ((shape.binders.map (·.2)).drop (nIn + shape.layout.slots.length)) ls := by
    have hlt := ok_letsTyped hok
    have hg := letsTyped_get _ _ hlt
    have hz := zip_of_K (shape.binders.map (·.2)) _ hK ls (nIn + shape.layout.slots.length)
      (by intro i t ht; have := hg i t ht; simpa [mkData, hss] using this)
      (by omega)
    have : ((shape.binders.map (·.2)).drop (nIn + shape.layout.slots.length)).length ≤ ls.length := by
      simp; omega
    rwa [List.take_of_length_le this] at hz
  have hz2 : Zip₂ (fun k t => sortOf k = some t.1) ((shape.binders.map (·.2)).drop nIn |>.take shape.layout.slots.length) nl := by
    have hn := ok_K_nexts hok
    have hz := zip_of_K (shape.binders.map (·.2)) _ hK nl nIn
      (by
        intro i t ht
        have hi : i < nl.length := (List.getElem?_eq_some_iff.1 ht).1
        have := hn i (by simpa [mkData] using hi)
        simp only [mkData] at this ⊢
        rw [this]; simp [List.getElem?_map, ht])
      (by omega)
    rwa [hss] at hz
  have hz3 : Zip₂ (fun k t => sortOf k = some t.1) (shape.layout.outs.map outKind) outs :=
    zip_map_left outKind (fun _ _ h => h) houts
  unfold dataOfTail
  rw [e1]
  simp only [Option.bind_some]
  rw [e2]
  simp only [Option.bind_some]
  rw [typedFields_of_quote_fields hz1]
  simp only [Option.bind_some]
  have t1 : (outs.map (fun t => toField t.1 t.2) ++ nl.map (fun t => toField t.1 t.2)).take shape.layout.outs.length =
      outs.map (fun t => toField t.1 t.2) := by
    rw [hnO]; exact List.take_left' (by simp)
  have t2 : (outs.map (fun t => toField t.1 t.2) ++ nl.map (fun t => toField t.1 t.2)).drop shape.layout.outs.length =
      nl.map (fun t => toField t.1 t.2) := by
    rw [hnO]; exact List.drop_left' (by simp)
  rw [t1, typedFields_of_quote_fields hz3]
  simp only [Option.bind_some]
  rw [t2, typedFields_of_quote_fields hz2]
  simp only [Option.bind_some]
  unfold checked
  simp [bitsBeq_refl, hok]

theorem dataOfTail_complete (D : MachineData) (shape : MachineShape) (nIn : Nat) (dom : Lean.Expr)
    (ls outs nl : List (Σ s : SType, Term s)) (hD : D = mkData shape nIn dom ls outs nl)
    (hok : D.ok = true)
    (hbl : shape.binders.length = nIn + shape.layout.slots.length + shape.layout.lets)
    (hss : nl.length = shape.layout.slots.length) (hls : ls.length = shape.layout.lets)
    (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs outs) :
    dataOfTail shape nIn dom _ D.packed = some D := by
  subst hD
  exact dataOfTail_complete_mk shape nIn dom ls outs nl hok hbl hss hls houts

theorem mkData_eta (d : MachineData)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d)) :
    d = mkData d.shape d.nIn d.dom d.ls d.outs (anyTerms d.nexts) := by
  obtain ⟨shape, nIn, dom, bposL, vposL, vwL, ss, ls, outs, nexts⟩ := d
  have key : ∀ (nl : List (Σ s : SType, Term s)) (hs : nl.map (·.1) = ss) (hn : HEq (termsOfAny nl) nexts),
      (⟨shape, nIn, dom, bposL, vposL, vwL, ss, ls, outs, nexts⟩ : MachineData) =
        mkData shape nIn dom ls outs nl := by
    intro nl hs hn
    subst hs
    have := eq_of_heq hn
    subst this
    have hb' : bposL = posB 0 (shape.binders.map (·.2)) := hb
    have hv' : vposL = posV 0 (shape.binders.map (·.2)) := hv
    have hw' : vwL = widV (shape.binders.map (·.2)) := hw
    subst hb' hv' hw'
    simp only [mkData]
    congr 1
    · exact (bposL_eq _).symm
    · exact (vposL_eq _).symm
    · exact (vwL_eq _).symm
  exact key _ (anyTerms_sorts nexts) (anyTerms_heq nexts)

theorem dataOfFrom_complete_of_quote (lvl : Lean.Expr → Nat)
    {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom))
    (hshape : d.shape = shape)
    (hok : d.ok = true)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d))
    (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hlvl : liftDepth d.packed ≤ lvl shape.body)
    (hss : d.ss.length = shape.layout.slots.length)
    (hls : d.ls.length = shape.layout.lets)
    (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs) :
    dataOfFrom lvl E senv shape tin fl = some d := by
  obtain ⟨-, hbl⟩ := dataOfFront_some hfront
  subst hshape
  unfold dataOfFrom
  rw [hfront]
  simp only [Option.bind_some]
  unfold dataOfCore
  have hc := kindsCfg_complete' d.dom (isExpr d.dom) (isExpr_self d.dom) (kindsOf d)
  obtain ⟨h1, h2⟩ := kindsCfg_quote_args d (isExpr d.dom) hb hv
  have hq' : d.shape.body = quote (kindsCfg d.dom (isExpr d.dom) (kindsOf d)).dom
      (kindsCfg d.dom (isExpr d.dom) (kindsOf d)).bools (kindsCfg d.dom (isExpr d.dom) (kindsOf d)).bits
      d.packed := by
    rw [h1, h2]
    exact hq
  have hwf := packed_wf_cfg d (isExpr d.dom) hb hv hw (ok_packed_wf hok)
  have hread := readN_quote hc d.packed (lvl d.shape.body) hlvl hwf
  rw [← hq'] at hread
  have hread' : readN (kindsCfg d.dom (isExpr d.dom) (d.shape.binders.map (·.2))) (lvl d.shape.body)
      d.shape.body = some ⟨.bits _, d.packed⟩ := hread
  rw [hread']
  have hD := mkData_eta d hb hv hw
  have hnl : (anyTerms d.nexts).length = d.shape.layout.slots.length := by
    rw [← hss]
    have := congrArg List.length (anyTerms_sorts d.nexts)
    simpa using this
  exact dataOfTail_complete d d.shape d.nIn d.dom d.ls d.outs (anyTerms d.nexts) hD hok hbl hnl hls houts

end Tools.ShippingGen5DataOf

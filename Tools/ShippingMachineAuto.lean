import Tools.ShippingMachineDenote

/-! # The machine endpoint from data

`machine_endpoint` reduces the declaration's part of the source-to-RTL
theorem of a state machine to data and facts about data. Here every one of
those facts is DECIDED:

* `MachineData`: the transition (`MachineShape`), the typed terms read off
  its body (the hardware `let`s, the results, the next values), and the
  positions of the Bool and BitVec binders.
* `MachineData.ok`: one Boolean check of all the side conditions.
* `machine_trace_of_data`: from `ok = true` and five equations that hold by
  `rfl` for a declaration — the body is the quotation of the terms, the
  reset values are the layout's, the body's pending writes are the typed
  values of the next-value terms, its result is the typed values of the
  result terms (both on an ARBITRARY state signal), and the declaration is
  the result of its body on the state loop — a run of the real synthesis entry returns a
  module whose every output port shows, at every cycle, the SOURCE
  declaration's value (`MachineTrace`).

A declaration therefore needs no proof script: a command computes the data
and the kernel checks six `Eq.refl`s (`Tools.ShippingMachineCommand`). -/
namespace Tools.ShippingMachineAuto
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource
open Tools.ShippingMachineDenote
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness Sparkle.IR.AST

/-! ## Deciding the facts -/

/-- Well-formedness of a term is decidable, by recursion on the term. -/
instance wfDec (kb kv : Nat) (vw : Nat → Nat) :
    ∀ {s : SType} (e : Term s), Decidable (e.WF kb kv vw)
  | _, .boolInput j => inferInstanceAs (Decidable (j < kb))
  | _, .bitsInput w j => inferInstanceAs (Decidable (j < kv ∧ vw j = w ∧ 0 < w))
  | _, .boolLit _ => isTrue trivial
  | _, .bitsLit w v => inferInstanceAs (Decidable (v < 2 ^ w ∧ 0 < w))
  | _, .bitsNum w v => inferInstanceAs (Decidable (v < 2 ^ w ∧ 0 < w))
  | _, .binary _ a b => @instDecidableAnd _ _ (wfDec kb kv vw a) (wfDec kb kv vw b)
  | _, .compare _ a b => @instDecidableAnd _ _ (wfDec kb kv vw a) (wfDec kb kv vw b)
  | _, .boolBinary _ a b => @instDecidableAnd _ _ (wfDec kb kv vw a) (wfDec kb kv vw b)
  | _, .boolNot a => wfDec kb kv vw a
  | _, .boolEq a b => @instDecidableAnd _ _ (wfDec kb kv vw a) (wfDec kb kv vw b)
  | _, .mux c a b =>
    @instDecidableAnd _ _ (wfDec kb kv vw c)
      (@instDecidableAnd _ _ (wfDec kb kv vw a) (wfDec kb kv vw b))
  | _, .setw w' a =>
    @instDecidableAnd _ _ (wfDec kb kv vw a) (inferInstanceAs (Decidable (0 < w')))
  | _, .appCompare _ a b => @instDecidableAnd _ _ (wfDec kb kv vw a) (wfDec kb kv vw b)
  | _, .appBool _ a b => @instDecidableAnd _ _ (wfDec kb kv vw a) (wfDec kb kv vw b)
  | _, .appBool2 _ a b => @instDecidableAnd _ _ (wfDec kb kv vw a) (wfDec kb kv vw b)
  | _, .slice _ start len (w := w) a =>
    @instDecidableAnd _ _ (wfDec kb kv vw a)
      (inferInstanceAs (Decidable (0 < len ∧ start + len ≤ w)))
  | _, .concat a b => @instDecidableAnd _ _ (wfDec kb kv vw a) (wfDec kb kv vw b)
  | _, .concatLitHi k v b =>
    @instDecidableAnd _ _ (wfDec kb kv vw b) (inferInstanceAs (Decidable (0 < k ∧ v < 2 ^ k)))
  | _, .concatLitLo a k v =>
    @instDecidableAnd _ _ (wfDec kb kv vw a) (inferInstanceAs (Decidable (0 < k ∧ v < 2 ^ k)))
  | _, .zextMap _ k a =>
    @instDecidableAnd _ _ (wfDec kb kv vw a) (inferInstanceAs (Decidable (0 < k)))
  | _, .sliceF _ start len (w := w) a =>
    @instDecidableAnd _ _ (wfDec kb kv vw a)
      (inferInstanceAs (Decidable (0 < len ∧ start + len ≤ w)))

instance letsScopedDec (bpos vpos : Nat → Nat) :
    ∀ (p : Nat) (bs : List (Name × MixedGateBinder)) (fs : List (Σ w : Nat, Term (.bits w))),
      Decidable (LetsScoped bpos vpos p bs fs)
  | _, [], [] => isTrue trivial
  | p, b :: bs, f :: fs =>
    have := letsScopedDec bpos vpos (p + 1) bs fs
    inferInstanceAs (Decidable
      (reads (fun j => decide (bpos j < p)) (fun j => decide (vpos j < p)) f.2 = true ∧
        machWidth b.2 = f.1 ∧ b.2 ≠ .domain ∧ LetsScoped bpos vpos (p + 1) bs fs))
  | _, [], _ :: _ => isFalse id
  | _, _ :: _, [] => isFalse id

instance letsTypedDec (bpos vpos : Nat → Nat) (kb kv : Nat) (vw : Nat → Nat)
    (K : Nat → Option SType) :
    ∀ (p : Nat) (ls : List (Σ s : SType, Term s)),
      Decidable (LetsTyped bpos vpos kb kv vw K p ls)
  | _, [] => isTrue trivial
  | p, l :: ls =>
    have := letsTypedDec bpos vpos kb kv vw K (p + 1) ls
    inferInstanceAs (Decidable
      (l.2.WF kb kv vw ∧
        reads (fun j => decide (bpos j < p)) (fun j => decide (vpos j < p)) l.2 = true ∧
        K p = some l.1 ∧ LetsTyped bpos vpos kb kv vw K (p + 1) ls))

/-- A relation checked along two lists of the same length. -/
def zipAllB {α β : Type} (p : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => p a b && zipAllB p as bs
  | _, _ => false

theorem zip_of_all {α β : Type} {R : α → β → Prop} {p : α → β → Bool}
    (h : ∀ a b, p a b = true → R a b) :
    ∀ {as : List α} {bs : List β}, zipAllB p as bs = true → Zip₂ R as bs
  | [], [], _ => .nil
  | a :: as, b :: bs, hz => by
    simp only [zipAllB, Bool.and_eq_true] at hz
    exact .cons (h _ _ hz.1) (zip_of_all h hz.2)
  | [], _ :: _, hz => by simp [zipAllB] at hz
  | _ :: _, [], hz => by simp [zipAllB] at hz

/-- Slot `i` of the layout is field `nOuts + i` of the packed core. -/
def slotsFitB (fields : List (Σ w : Nat, Term (.bits w))) (nOuts : Nat)
    (slots : List SlotField) : Bool :=
  (List.range slots.length).all fun i =>
    match slots[i]?, fields[nOuts + i]? with
    | some f, some g =>
      decide (f.width = g.1) &&
        decide (f.lo = ((fields.drop (nOuts + i + 1)).map (·.1)).sum)
    | _, _ => false

theorem slotsFit_of {fields : List (Σ w : Nat, Term (.bits w))} {nOuts : Nat}
    {slots : List SlotField} (h : slotsFitB fields nOuts slots = true) :
    SlotsFit fields nOuts slots := by
  intro i f hf
  have hi : i < slots.length := (List.getElem?_eq_some_iff.mp hf).1
  have hall := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  cases hg : fields[nOuts + i]? with
  | none => simp [hf, hg] at hall
  | some g =>
    simp only [hf, hg, Bool.and_eq_true, decide_eq_true_eq] at hall
    exact ⟨g, rfl, hall.1, hall.2⟩

/-- Output port `k` of the layout is field `k` of the packed core, the field
of the typed result term `k`. -/
def outsFitB (kb kv : Nat) (vw : Nat → Nat) (fields : List (Σ w : Nat, Term (.bits w)))
    (ports : List OutField) (outs : List (Σ s : SType, Term s)) : Bool :=
  (List.range ports.length).all fun k =>
    match ports[k]?, outs[k]? with
    | some o, some t =>
      decide (t.2.WF kb kv vw) && (decide (o.width = (toField t.1 t.2).1) &&
        decide (o.lo = ((fields.drop (k + 1)).map (·.1)).sum))
    | _, _ => false

theorem outsFit_get {kb kv : Nat} {vw : Nat → Nat}
    {fields : List (Σ w : Nat, Term (.bits w))} {ports : List OutField}
    {outs : List (Σ s : SType, Term s)} (h : outsFitB kb kv vw fields ports outs = true)
    {k : Nat} {o : OutField} {t : Σ s : SType, Term s} (ho : ports[k]? = some o)
    (ht : outs[k]? = some t) :
    t.2.WF kb kv vw ∧ o.width = (toField t.1 t.2).1 ∧
      o.lo = ((fields.drop (k + 1)).map (·.1)).sum := by
  have hk : k < ports.length := (List.getElem?_eq_some_iff.mp ho).1
  have hall := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simpa only [ho, ht, Bool.and_eq_true, decide_eq_true_eq] using hall

/-! ## The data of a machine -/

/-- The sort of a hardware binder. -/
def sortOf : MixedGateBinder → Option SType
  | .bool => some .bool
  | .bits w => some (.bits w)
  | .domain => none

/-- The fields packed, the first in the high bits (a placeholder for none). -/
def packAll : List (Σ w : Nat, Term (.bits w)) → Σ W : Nat, Term (.bits W)
  | [] => ⟨1, .bitsLit 1 0⟩
  | f :: rest => packList f rest

/-- A machine, as data: the transition the front end reads off the
declaration, the typed terms its body is the quotation of, and where the
Bool and BitVec binders sit. -/
structure MachineData where
  shape : MachineShape
  /-- The declaration's own binders come first. -/
  nIn : Nat
  /-- The domain, as the body mentions it. -/
  dom : Lean.Expr
  /-- The positions of the Bool binders, in order. -/
  bposL : List Nat
  /-- The positions of the BitVec binders, in order, and their widths. -/
  vposL : List Nat
  vwL : List Nat
  /-- The sorts of the state. -/
  ss : List SType
  /-- The hardware `let`s. -/
  ls : List (Σ s : SType, Term s)
  /-- The results, one per output port. -/
  outs : List (Σ s : SType, Term s)
  /-- The next values, one per slot. -/
  nexts : Terms ss

namespace MachineData
variable (d : MachineData)

def bsIn : List (Name × MixedGateBinder) := d.shape.binders.take d.nIn
def slotBs : List (Name × MixedGateBinder) := (d.shape.binders.drop d.nIn).take d.ss.length
def letBs : List (Name × MixedGateBinder) := d.shape.binders.drop (d.nIn + d.ss.length)
def kb : Nat := d.bposL.length
def kv : Nat := d.vposL.length
def bpos (j : Nat) : Nat := d.bposL.getD j 0
def vpos (j : Nat) : Nat := d.vposL.getD j 0
def vw (j : Nat) : Nat := d.vwL.getD j 0
/-- The sort of every binder position. -/
def K (p : Nat) : Option SType := d.shape.binders[p]?.bind fun b => sortOf b.2
def letFields : List (Σ w : Nat, Term (.bits w)) := d.ls.map fun l => toField l.1 l.2
def fields : List (Σ w : Nat, Term (.bits w)) :=
  (d.outs.map fun t => toField t.1 t.2) ++ d.nexts.fields
def core : Σ W : Nat, Term (.bits W) := packAll d.fields
/-- The term the transition's body is the quotation of. -/
def packed : Term (.bits (packLets d.letFields d.core.2).1) := (packLets d.letFields d.core.2).2

theorem binders_split : d.shape.binders = d.bsIn ++ d.slotBs ++ d.letBs := by
  unfold bsIn slotBs letBs
  rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

/-- Every side condition of the machine endpoint, as one check. -/
def ok : Bool :=
  decide (d.nIn + d.ss.length ≤ d.shape.binders.length) && (
  decide (d.shape.layout.lets = d.letBs.length) && (
  (d.shape.binders.all fun b => match b.2 with | .bits n => decide (0 < n) | _ => true) && (
  decide (∀ b ∈ d.slotBs, b.2 ≠ .domain) && (
  decide (∀ b ∈ d.letBs, b.2 ≠ .domain) && (
  zipAllB (fun (f : SlotField) (b : Name × MixedGateBinder) =>
    decide (f.width = machWidth b.2) && (decide (b.2 ≠ .domain) &&
      decide (f.init < 2 ^ f.width))) d.shape.layout.slots d.slotBs && (
  decide (∀ o ∈ d.shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true) && (
  decide (d.shape.layout.outs.map (·.name)).Nodup && (
  decide (d.packed.WF d.kb d.kv d.vw) && (
  decide (∀ j, j < d.kb → d.shape.binders[d.bpos j]?.map (·.2) = some .bool) && (
  decide (∀ j, j < d.kv →
    d.shape.binders[d.vpos j]?.map (·.2) = some (.bits (d.vw j))) && (
  decide (∀ f ∈ d.shape.layout.slots, f.lo + f.width ≤ d.core.1) && (
  decide (∀ o ∈ d.shape.layout.outs, o.lo + o.width ≤ d.core.1) && (
  decide (LetsScoped d.bpos d.vpos (d.nIn + d.ss.length) d.letBs d.letFields) && (
  slotsFitB d.fields d.outs.length d.shape.layout.slots && (
  decide (∀ j, j < d.kb →
    d.K (d.bpos j) = some .bool ∧ d.bpos j < d.nIn + d.ss.length + d.ls.length) && (
  decide (∀ j, j < d.kv →
    d.K (d.vpos j) = some (.bits (d.vw j)) ∧
      d.vpos j < d.nIn + d.ss.length + d.ls.length) && (
  decide (∀ i, i < d.ss.length → d.K (d.nIn + i) = d.ss[i]?) && (
  decide (LetsTyped d.bpos d.vpos d.kb d.kv d.vw d.K (d.nIn + d.ss.length) d.ls) && (
  decide (∀ g ∈ d.nexts.fields, g.2.WF d.kb d.kv d.vw) && (
  outsFitB d.kb d.kv d.vw d.fields d.shape.layout.outs d.outs &&
  !d.fields.isEmpty))))))))))))))))))))

/-- The reset values of the source are the layout's. -/
def initOk (inits : HList (tys d.ss)) : Bool :=
  (List.range d.ss.length).all fun i =>
    encState d.ss inits i == (d.shape.layout.slots[i]?.map (·.init)).getD 0

end MachineData

/-- **What a machine module shows.** `dom` is the family of domains the
declaration is stated for (every domain, for a declaration with a domain
binder; one, for a declaration in a concrete domain). For input Signals
`bools`/`bits` (by binder position) in any of them, a run of `m` for any
number of cycles from the reset values with reset low drives output port
`k`, at every cycle `j`, with the `k`-th source observation at time `j`. -/
def MachineTrace (declName : Name) (d : MachineData) (m : Sparkle.IR.AST.Module)
    {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
      (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
        (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
        (seed t st)) →
      (∀ t st r, r ∈ regs → seed t st r = st r) →
      (∀ t st, seed t st "rst" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ∃ envs, runModule (weOf m) m.body seed T st0 mems = some envs ∧ envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j

set_option maxHeartbeats 2000000 in
/-- **Source to RTL for a state machine, from data.** The check `ok` and
five equations — each `rfl` for a declaration — give the trace theorem of
every module a run of the real synthesis entry returns at the machine
boundary. -/
theorem machine_trace_of_data {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) [Inhabited (HList (tys d.ss))] {ρ : ι → Type}
    (inits : HList (tys d.ss))
    (body : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      valsAt (tys d.ss) (body i bools bits
          (mkRegList S (tys d.ss) (fun s => s) (fun f => f)) (mkHolds (tys d.ss) S)).snd t =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (S.val t)).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (S.val t)).v
            (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (obsR i (body i bools bits (mkRegList S (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (S.val t)).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (S.val t)).v
            (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i
        (body i bools bits
          (mkRegList (stateLoop inits (body i bools bits)) (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) (stateLoop inits (body i bools bits)))).fst)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTrace declName d m dom src := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, hslots, fb, fv, fslots, flets, nextsWF, houts, hne⟩ := ok
  have hkIn : d.bsIn.length = d.nIn := by
    simp only [MachineData.bsIn, List.length_take]; omega
  have hn : d.slotBs.length = d.ss.length := by
    simp only [MachineData.slotBs, List.length_take, List.length_drop]; omega
  have layW : Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) =>
      f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  have hpres : MachinePreserves declName d.shape d.bsIn d.slotBs d.letBs m :=
    synthesizeCombinationalCore_machine_sound hr entry closes d.binders_split hlets
      (by
        intro name n hmem
        have := List.all_eq_true.mp positive _ hmem
        simpa using this)
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  cases hf : d.fields with
  | nil => simp [hf] at hne
  | cons f0 rest =>
  have hcore : d.core = packList f0 rest := by
    simp only [MachineData.core, hf, packAll]
  simp only [MachineData.packed] at hwf hbody
  generalize d.core = c at hcore hwf hbody hfit houtfit
  subst hcore
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => simp [h] at this
    | some b =>
      obtain ⟨nm, k⟩ := b
      simp only [h, Option.map_some, Option.some.injEq] at this
      subst this
      exact ⟨nm, rfl⟩
  have hv' : ∀ j, j < d.kv →
      ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => simp [h] at this
    | some b =>
      obtain ⟨nm, k⟩ := b
      simp only [h, Option.map_some, Option.some.injEq] at this
      subst this
      exact ⟨nm, rfl⟩
  have hnexts : (f0 :: rest).drop d.outs.length = d.nexts.fields := by
    rw [← hf]
    unfold MachineData.fields
    have hl : d.outs.length = (d.outs.map fun t => toField t.1 t.2).length := by simp
    rw [hl, List.drop_left]
  have facts : TermFacts d.bsIn.length d.kb d.kv d.vw d.bpos d.vpos d.K d.ss d.ls := by
    rw [hkIn]
    exact ⟨fb, fv, fun i s hs => by
      have hi : i < d.ss.length := (List.getElem?_eq_some_iff.mp hs).1
      rw [fslots i hi, hs], flets⟩
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, h⟩ :=
    machine_endpoint hpres (K := d.K) (nOuts := d.outs.length) layW hwf hb' hv' hbody hfit
      houtfit (by rw [hkIn, hn]; exact hscoped) hn hnexts (hf ▸ slotsFit_of hslots) facts
      nextsWF
  refine ⟨ids, nd, len, cache, regs, rnd, rlen.trans hn, ?_⟩
  intro ix bools bits T seed st0 mems inputs pass rst init
  have hinit' : ∀ i, encState d.ss inits i =
      (d.shape.layout.slots[i]?.map (·.init)).getD 0 := by
    intro i
    by_cases hi : i < d.ss.length
    · have := List.all_eq_true.mp hinit i (List.mem_range.mpr hi)
      simpa using this
    · rw [encState_ge _ _ _ (by omega)]
      have hnone : d.shape.layout.slots[i]? = none := by
        rw [List.getElem?_eq_none]
        rw [layW.length_eq, hn]; omega
      rw [hnone]; rfl
  obtain ⟨envs, hrun, hlen', hobs⟩ := h inits (body ix bools bits) bools bits hinit'
    (by rw [hkIn]; exact writes ix bools bits) T seed st0 mems inputs pass rst init
  refine ⟨envs, hrun, hlen', ?_⟩
  intro j hj k o f ho hfk
  rw [hsrc ix bools bits] at hfk
  have h1 := congrArg (fun l => l[k]?)
    (hres ix bools bits (stateLoop inits (body ix bools bits)) j)
  simp only [List.getElem?_map, hfk, Option.map_some] at h1
  cases ht : d.outs[k]? with
  | none => simp [ht] at h1
  | some t =>
    simp only [ht, Option.map_some, Option.some.injEq] at h1
    obtain ⟨hwt, hw, hlo⟩ := outsFit_get houts ho ht
    have hk : k < d.outs.length := (List.getElem?_eq_some_iff.mp ht).1
    have hfield : (f0 :: rest)[k]? = some (toField t.1 t.2) := by
      rw [← hf]
      unfold MachineData.fields
      rw [List.getElem?_append_left (by simpa using hk), List.getElem?_map, ht]
      rfl
    have := hobs j hj o (List.mem_of_getElem? ho) t.2 hwt k hfield (hf ▸ hlo) hw
    rw [hkIn] at this
    rw [this]
    exact h1.symm

end Tools.ShippingMachineAuto

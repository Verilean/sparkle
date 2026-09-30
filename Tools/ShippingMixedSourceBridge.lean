import Tools.ShippingMixedGateSoundness
import Tools.ShippingMixedPostSoundness

/-! Identify source inputs by their positions in the actual mixed telescope.
Freshness derives the prepared valuation lookup facts; callers do not supply
facts about the compiler's intermediate environment. -/
namespace Tools.ShippingMixedSourceBridge
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedGateSoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingEntrySoundness

abbrev Binder := (Name × MixedGateBinder) × FVarId

theorem prepare_bool_absent {bools bits} (L : List Binder) (a : Setup) (id : FVarId)
    (hn : id ∉ L.map Prod.snd) :
    (prepare bools bits L a).bools id = a.bools id := by
  induction L generalizing a with
  | nil => rfl
  | cons binder rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    rw [prepare, ih _ hn.2]
    obtain ⟨⟨name, kind⟩, key⟩ := binder
    cases kind <;> simp [extend, hn.1]

theorem prepare_bits_absent {bools bits} (L : List Binder) (a : Setup) (id : FVarId)
    (hn : id ∉ L.map Prod.snd) :
    (prepare bools bits L a).bits id = a.bits id := by
  induction L generalizing a with
  | nil => rfl
  | cons binder rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    rw [prepare, ih _ hn.2]
    obtain ⟨⟨name, kind⟩, key⟩ := binder
    cases kind <;> simp [extend, hn.1]

theorem prepare_bool_lookup {bools bits} (L : List Binder) (a : Setup)
    (nd : (L.map Prod.snd).Nodup) {name id}
    (mem : ((name, .bool), id) ∈ L) :
    (prepare bools bits L a).bools id = some (bools id) := by
  induction L generalizing a with
  | nil => cases mem
  | cons binder rest ih =>
    simp only [List.map_cons, List.nodup_cons] at nd
    rcases List.mem_cons.mp mem with rfl | mem
    · rw [prepare, prepare_bool_absent rest _ id nd.1]
      simp [extend]
    · exact ih _ nd.2 mem

theorem prepare_bits_lookup {bools bits} (L : List Binder) (a : Setup)
    (nd : (L.map Prod.snd).Nodup) {name id n}
    (mem : ((name, .bits n), id) ∈ L) :
    (prepare bools bits L a).bits id = some ⟨n, bits id n⟩ := by
  induction L generalizing a with
  | nil => cases mem
  | cons binder rest ih =>
    simp only [List.map_cons, List.nodup_cons] at nd
    rcases List.mem_cons.mp mem with rfl | mem
    · rw [prepare, prepare_bits_absent rest _ id nd.1]
      simp [extend]
    · exact ih _ nd.2 mem

/-- Reverse de Bruijn indexing of a source argument in the complete telescope. -/
def inputExpr (count position : Nat) : Lean.Expr := .bvar (count - 1 - position)

theorem instantiated_input {bs : List (Name × MixedGateBinder)} {ids : List FVarId}
    (len : ids.length = bs.length) {j : Nat} (hj : j < bs.length) :
    instFVars (ids.map Lean.Expr.fvar).toArray 0 (inputExpr bs.length j) = .fvar ids[j]! := by
  simp only [inputExpr, instFVars, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero,
    List.size_toArray, List.length_map]
  rw [if_pos (by omega)]
  have eq : ids.length - 1 - (bs.length - 1 - j) = j := by omega
  rw [eq]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by omega : j < ids.length)]

theorem zip_ids {bs : List (Name × MixedGateBinder)} {ids : List FVarId}
    (len : ids.length = bs.length) : (bs.zip ids).map Prod.snd = ids := by
  exact List.map_snd_zip (by omega)

theorem zip_member {bs : List (Name × MixedGateBinder)} {ids : List FVarId}
    (len : ids.length = bs.length) {j : Nat} {binder : Name × MixedGateBinder}
    (hj : bs[j]? = some binder) : (binder, ids[j]!) ∈ bs.zip ids := by
  have bound : j < bs.length := (List.getElem_of_getElem? hj).choose
  have hi : j < ids.length := by omega
  apply List.mem_of_getElem? (i := j)
  exact List.getElem?_zip_eq_some.mpr ⟨hj, by simp [List.getElem?_eq_getElem hi, List.getElem!_eq_getElem?_getD]⟩

/-- A pure source declaration body and typed argument positions suffice to
instantiate the earlier relational theorem. Arbitrary argument ordering and
unused arguments are allowed. -/
theorem source_inputs {declName bs dom n kb kv e P} {bpos vpos : Nat → Nat}
    (source : MixedSourcePreserves declName bs
      (quoteB dom n (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e) P)
    (hn : 0 < n) (he : e.WF kb kv n)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits n)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Admissible bools bits initial (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString) →
      P initial mems (Tools.ShippingMuxLoweringSoundness.encodeBool
        (evalB n (fun j => bools ids[bpos j]!) (fun j => bits ids[vpos j]! n) e)) := by
  obtain ⟨ids, nd, len, cache, source⟩ := source
  refine ⟨ids, nd, len, cache, ?_⟩
  intro bools bits initial mems values
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  apply source bools bits initial mems values (instFVars (ids.map Lean.Expr.fvar).toArray 0 dom)
    n kb kv (fun j => ids[bpos j]!) (fun j => ids[vpos j]!) _ _ e hn he
  · intro j hj
    obtain ⟨name, pos⟩ := hb j hj
    exact prepare_bool_lookup _ _ fresh (zip_member len pos)
  · intro j hj
    obtain ⟨name, pos⟩ := hv j hj
    exact prepare_bits_lookup _ _ fresh (zip_member len pos)
  · apply instantiated_quoteB _ _ e he
    · intro j hj
      obtain ⟨name, pos⟩ := hb j hj
      exact instantiated_input len ((List.getElem_of_getElem? pos).choose)
    · intro j hj
      obtain ⟨name, pos⟩ := hv j hj
      exact instantiated_input len ((List.getElem_of_getElem? pos).choose)

/-- Fresh compiler IDs recover their source position, independently of spelling. -/
theorem index_fresh (ids : List FVarId) (nd : ids.Nodup) (j : Nat) (hj : j < ids.length) :
    ids.idxOf ids[j]! = j := by
  induction ids generalizing j with
  | nil => simp at hj
  | cons id rest ih =>
    obtain ⟨absent, nd⟩ := List.nodup_cons.mp nd
    cases j with
    | zero => simp only [List.getElem!_cons_zero, List.idxOf_cons, (fvarId_beq_iff id id).mpr rfl, Bool.cond_true]
    | succ j =>
      have bound : j < rest.length := by simpa using hj
      have mem : rest[j]! ∈ rest := by simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem bound]; exact List.getElem_mem bound
      have ne : id ≠ rest[j]! := by intro eq; exact absent (eq ▸ mem)
      have neq : (id == rest[j]!) = false := by
        cases eq : (id == rest[j]!) with
        | false => rfl
        | true => exact (ne ((fvarId_beq_iff _ _).mp eq)).elim
      simp only [List.getElem!_cons_succ, List.idxOf_cons, neq, Bool.cond_false]
      rw [ih nd j bound]

/-- Source values are indexed by declaration positions, not opaque fresh IDs. -/
def boolValues (ids : List FVarId) (values : Nat → Bool) : FVarId → Bool :=
  fun id => values (ids.idxOf id)
def bitValues (ids : List FVarId) (values : (j : Nat) → (n : Nat) → BitVec n) :
    (id : FVarId) → (n : Nat) → BitVec n := fun id n => values (ids.idxOf id) n

def SourceInputs (declName : Name) (bs : List (Name × MixedGateBinder)) (ids : List FVarId)
    (cache : IO.Ref (ExprStructMap String)) (bools : Nat → Bool)
    (bits : (j : Nat) → (n : Nat) → BitVec n) (initial : Env) : Prop :=
  Admissible (boolValues ids bools) (bitValues ids bits) initial (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString)

/-- Close intermediate valuation lookups and body instantiation from the
source telescope alone. The remaining input premise is port-value agreement. -/
theorem source_positions {declName bs dom n kb kv e P} {bpos vpos : Nat → Nat}
    (source : MixedSourcePreserves declName bs
      (quoteB dom n (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e) P)
    (hn : 0 < n) (he : e.WF kb kv n)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits n)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits initial →
      P initial mems (Tools.ShippingMuxLoweringSoundness.encodeBool
        (evalB n (fun j => bools (bpos j)) (fun j => bits (vpos j) n) e)) := by
  obtain ⟨ids, nd, len, cache, source⟩ := source
  refine ⟨ids, nd, len, cache, ?_⟩
  intro bools bits initial mems values
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  apply source (boolValues ids bools) (bitValues ids bits) initial mems values
    (instFVars (ids.map Lean.Expr.fvar).toArray 0 dom)
    n kb kv (fun j => ids[bpos j]!) (fun j => ids[vpos j]!) _ _ e hn he
  · intro j hj
    obtain ⟨name, pos⟩ := hb j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bool_lookup (bools := boolValues ids bools) (bits := bitValues ids bits)
      (bs.zip ids) (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [boolValues, index_fresh ids nd (bpos j) (by omega)] using lookup
  · intro j hj
    obtain ⟨name, pos⟩ := hv j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bits_lookup (bools := boolValues ids bools) (bits := bitValues ids bits)
      (bs.zip ids) (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [bitValues, index_fresh ids nd (vpos j) (by omega)] using lookup
  · apply instantiated_quoteB _ _ e he
    · intro j hj
      obtain ⟨name, pos⟩ := hb j hj
      exact instantiated_input len (List.getElem_of_getElem? pos).choose
    · intro j hj
      obtain ⟨name, pos⟩ := hv j hj
      exact instantiated_input len (List.getElem_of_getElem? pos).choose

/-- The same theorem observes actual library Signals at any source time.
No equality about the prepared compiler valuation remains a premise. -/
theorem source_signals {declName bs dom n kb kv e P} {bpos vpos : Nat → Nat}
    (source : MixedSourcePreserves declName bs
      (quoteB dom n (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e) P)
    (hn : 0 < n) (he : e.WF kb kv n)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits n)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : Sparkle.Core.Domain.DomainConfig}
        (bools : Nat → Sparkle.Core.Signal.Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs declName bs ids cache (fun j => (bools j).val tick)
        (fun j n => (bits j n).val tick) initial →
      P initial mems (Tools.ShippingMuxLoweringSoundness.encodeBool
        ((denoteB n (fun j => bools (bpos j)) (fun j => bits (vpos j) n) e).val tick)) := by
  obtain ⟨ids, nd, len, cache, source⟩ := source_positions source hn he hb hv
  refine ⟨ids, nd, len, cache, ?_⟩
  intro D bools bits tick initial mems values
  rw [denoteB_val]
  exact source _ _ initial mems values

theorem mixed_kind_at {bs : List (Name × MixedGateBinder)} {j name kind}
    (pos : bs[j]? = some (name, kind)) :
    mixedGateBVar? (bs.map Prod.snd).toArray (bs.length - 1 - j) = some kind := by
  have bound := (List.getElem_of_getElem? pos).choose
  unfold mixedGateBVar?
  simp only [List.size_toArray, List.length_map]
  rw [if_pos (by omega)]
  have eq : bs.length - 1 - (bs.length - 1 - j) = j := by omega
  rw [eq]
  simp [List.getElem?_map, pos]

theorem mixed_bits_at {bs : List (Name × MixedGateBinder)} {j name n}
    (pos : bs[j]? = some (name, .bits n)) :
    gateBody (mixedBitKinds (bs.map Prod.snd).toArray) n (inputExpr bs.length j) = true := by
  have bound := (List.getElem_of_getElem? pos).choose
  unfold inputExpr gateBody gateBVar? mixedBitKinds
  simp only [Array.size_map, List.size_toArray, List.length_map]
  rw [if_pos (by omega)]
  have eq : bs.length - 1 - (bs.length - 1 - j) = j := by omega
  rw [eq]
  simp [List.getElem?_map, pos]

/-- Mixed-gate acceptance follows from the source positions, not from a
successful or semantically correct body translation. -/
theorem source_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {dom : Lean.Expr} {n kb kv : Nat} {bpos vpos : Nat → Nat} {e : BExpr}
    (peel : mixedGatePeel d.value = some (bs,
      quoteB dom n (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e))
    (hn : 0 < n) (he : e.WF kb kv n)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits n)) :
    ∀ isInst, mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs,
      quoteB dom n (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e) := by
  apply mixedCertifiedShape_of_quote peel hn ?_ ?_ he
  · intro j hj
    obtain ⟨name, pos⟩ := hb j hj
    change (mixedGateBVar? (bs.map Prod.snd).toArray (bs.length - 1 - bpos j) == some .bool) = true
    rw [mixed_kind_at pos]
    rfl
  · intro j hj
    obtain ⟨name, pos⟩ := hv j hj
    exact mixed_bits_at pos

/-- Source Signal observations through actual synthesis, cleanup and checked
optimization. Only pure source syntax/argument positions and port values are
supplied; no intermediate compiler valuation or substitution proof is needed. -/
theorem shipping_source_signals {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, design) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ (bs : List (Name × MixedGateBinder)) (dom : Lean.Expr) (n kb kv : Nat)
        (bpos vpos : Nat → Nat) (e : BExpr),
      certifiedShape? false [] ci = none →
      (∀ isInst, mixedCertifiedShape? false [] ci isInst = some (bs,
        quoteB dom n (fun j => inputExpr bs.length (bpos j))
          (fun j => inputExpr bs.length (vpos j)) e)) →
      0 < n → e.WF kb kv n →
      (∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool)) →
      (∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits n)) →
      ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
      ∃ cache : IO.Ref (ExprStructMap String),
        ∀ {D : Sparkle.Core.Domain.DomainConfig}
          (bools : Nat → Sparkle.Core.Signal.Signal D Bool)
          (bits : (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal D (BitVec n))
          (tick : Nat) (initial : Env) (mems : MEnv),
        SourceInputs declName bs ids cache (fun j => (bools j).val tick)
          (fun j n => (bits j n).val tick) initial →
        ∃ result, evalAssigns (weOf (Sparkle.IR.OptCheck.checkedOptimize m)) mems
            (Sparkle.IR.OptCheck.checkedOptimize m).body initial = some result ∧
          result "out" = Tools.ShippingMuxLoweringSoundness.encodeBool
            ((denoteB n (fun j => bools (bpos j)) (fun j => bits (vpos j) n) e).val tick) ∧
          "out" ∈ (Sparkle.IR.OptCheck.checkedOptimize m).outputs.map (·.name) := by
  obtain ⟨ci, w1, w2, get, source⟩ := Tools.ShippingMixedPostSoundness.synthesizeCombinational_mixed_checked hr
  refine ⟨ci, w1, w2, get, ?_⟩
  intro bs dom n kb kv bpos vpos e old shape hn he hb hv
  exact source_signals (source bs _ old shape) hn he hb hv

/-- Explicit runtime-environment boundary for source declarations whose mixed
Bool telescope is not accepted by the old BitVec-only binder walk. The two
syntax premises concern the declaration value alone and are purely checkable. -/
theorem shipping_source_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {n kb kv : Nat} {bpos vpos : Nat → Nat} {e : BExpr}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : gatePeel value = none)
    (peel : mixedGatePeel value = some (bs,
      quoteB dom n (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e))
    (hn : 0 < n) (he : e.WF kb kv n)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits n)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : Sparkle.Core.Domain.DomainConfig}
        (bools : Nat → Sparkle.Core.Signal.Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs declName bs ids cache (fun j => (bools j).val tick)
        (fun j n => (bits j n).val tick) initial →
      ∃ result, evalAssigns (weOf (Sparkle.IR.OptCheck.checkedOptimize m)) mems
          (Sparkle.IR.OptCheck.checkedOptimize m).body initial = some result ∧
        result "out" = Tools.ShippingMuxLoweringSoundness.encodeBool
          ((denoteB n (fun j => bools (bpos j)) (fun j => bits (vpos j) n) e).val tick) ∧
        "out" ∈ (Sparkle.IR.OptCheck.checkedOptimize m).outputs.map (·.name) := by
  obtain ⟨ci, w1, w2, get, source⟩ := shipping_source_signals hr
  obtain ⟨d, rfl, definition⟩ := env w1 ci w2 get
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := by
    simp [certifiedShape?, definition, old]
  have mixedGate := source_gate (d := d) (by rw [definition]; exact peel) hn he hb hv
  exact source bs dom n kb kv bpos vpos e oldGate mixedGate hn he hb hv

end Tools.ShippingMixedSourceBridge

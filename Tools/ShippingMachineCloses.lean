import Tools.ShippingCloseLetsRun
import Tools.ShippingSpineOrder
import Tools.ShippingClosedOrder
import Tools.ShippingClosesSplit

variable {tenv : Lean.Environment}

/-! # `closeLets` accepts the harness' transition: the six conditions, assembled

From a run of the certified harness on a packed machine body
(`transition_spine`, `spine_links`) and the pure ordering theorem
(`closed_acyclic`) to `(closeLets …).isSome`, and with
`machineCloses_noCalls_iff` to `MachineCloses` for shapes without calls. -/
namespace Tools.ShippingMachineCloses
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.IR.Machine Sparkle.IR.Type
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingMixedInputSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingTypedPostSoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineClose Tools.ShippingMachineTrace
open Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSpine Tools.ShippingCloseLetsSplit Tools.ShippingHarnessSpine
open Tools.ShippingSettledSoundness (Acyclic)
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingSpineOrder Tools.ShippingClosedOrder Tools.ShippingCloseLetsRun
open Sparkle.IR.Reorder

/-- Binders bound later do not change an earlier binding. -/
theorem prepare_visible_keep {bools bits} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup) (id : FVarId),
      id ∉ L.map Prod.snd →
      visible (prepare bools bits L a).context (prepare bools bits L a).state.sourceBindings id =
        visible a.context a.state.sourceBindings id
  | [], _, _, _ => rfl
  | ((name, kind), id') :: rest, a, id, hid => by
    rw [List.map_cons, List.mem_cons, not_or] at hid
    rw [prepare, prepare_visible_keep rest _ id hid.2]
    cases kind with
    | domain => rfl
    | bool => exact visible_old hid.1
    | bits n => exact visible_old hid.1

/-- **The wire bound to the `k`-th binder is the `k`-th input port's**, for a
walk over binders none of which is a domain. -/
theorem prepare_visible_port {bools bits} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup), (L.map Prod.snd).Nodup →
      (∀ b ∈ L, b.1.2 ≠ .domain) → ∀ (k : Nat) (b : (Name × MixedGateBinder) × FVarId) (port : Port),
      L[k]? = some b → (inputPorts bools bits L a)[k]? = some port →
      visible (prepare bools bits L a).context (prepare bools bits L a).state.sourceBindings b.2 =
        some port.name
  | [], _, _, _, _, _, _, hb, _ => by cases hb
  | ((name, kind), id) :: rest, a, nd, hk, k, b, port, hb, hp => by
    rw [List.map_cons, List.nodup_cons] at nd
    have hrest : ∀ b ∈ rest, b.1.2 ≠ .domain := fun b hb => hk b (List.mem_cons_of_mem _ hb)
    cases k with
    | zero =>
      cases hb
      rw [prepare, prepare_visible_keep rest _ id nd.1]
      cases kind with
      | domain => exact absurd rfl (hk _ List.mem_cons_self)
      | bool => cases hp; exact visible_new
      | bits n => cases hp; exact visible_new
    | succ k =>
      rw [prepare]
      cases kind with
      | domain => exact absurd rfl (hk _ List.mem_cons_self)
      | bool => exact prepare_visible_port rest _ nd.2 hrest k b port hb hp
      | bits n => exact prepare_visible_port rest _ nd.2 hrest k b port hb hp

/-- A non-domain binder is bound to one of the walk's input ports. -/
theorem prepare_visible_mem {bools bits} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup), (L.map Prod.snd).Nodup →
      ∀ (b : (Name × MixedGateBinder) × FVarId), b ∈ L → b.1.2 ≠ .domain →
      ∃ port ∈ inputPorts bools bits L a,
        visible (prepare bools bits L a).context (prepare bools bits L a).state.sourceBindings b.2 =
          some port.name
  | ((name, kind), id) :: rest, a, nd, b, hb, hk => by
    rw [List.map_cons, List.nodup_cons] at nd
    rcases List.mem_cons.mp hb with rfl | hin
    · rw [prepare, prepare_visible_keep rest _ id nd.1]
      cases kind with
      | domain => exact absurd rfl hk
      | bool =>
        exact ⟨{ name := inputWire a.state name.toString .bit, ty := .bit },
          by simp only [inputPorts]; exact List.mem_cons_self, visible_new⟩
      | bits n =>
        exact ⟨{ name := inputWire a.state name.toString (.bitVector n), ty := .bitVector n },
          by simp only [inputPorts]; exact List.mem_cons_self, visible_new⟩
    · obtain ⟨port, hp, hv⟩ := prepare_visible_mem rest (extend a ((name, kind), id) bools bits)
        nd.2 b hin hk
      refine ⟨port, ?_, by rw [prepare]; exact hv⟩
      cases kind with
      | domain => simpa only [inputPorts] using hp
      | bool => simp only [inputPorts]; exact List.mem_cons_of_mem _ hp
      | bits n => simp only [inputPorts]; exact List.mem_cons_of_mem _ hp

/-- **Bindings after a two-part walk** `L1 ++ L2` (`L2` without domains): a
binder of `L2` is bound to the port at its index among `L2`'s ports; a
non-domain binder of `L1` is bound to one of `L1`'s ports. -/
theorem binding_split {bools bits} (L1 L2 : List ((Name × MixedGateBinder) × FVarId)) (a : Setup)
    (nd : ((L1 ++ L2).map Prod.snd).Nodup) (hk2 : ∀ b ∈ L2, b.1.2 ≠ .domain) :
    (∀ (k : Nat) (b : (Name × MixedGateBinder) × FVarId) (port : Port), L2[k]? = some b →
      (inputPorts bools bits L2 (prepare bools bits L1 a))[k]? = some port →
      visible (prepare bools bits (L1 ++ L2) a).context
        (prepare bools bits (L1 ++ L2) a).state.sourceBindings b.2 = some port.name) ∧
    (∀ b ∈ L1, b.1.2 ≠ .domain → ∃ port ∈ inputPorts bools bits L1 a,
      visible (prepare bools bits (L1 ++ L2) a).context
        (prepare bools bits (L1 ++ L2) a).state.sourceBindings b.2 = some port.name) := by
  rw [List.map_append, List.nodup_append] at nd
  refine ⟨fun k b port hb hp => ?_, fun b hb hk => ?_⟩
  · rw [prepare_append]
    exact prepare_visible_port L2 _ nd.2.1 hk2 k b port hb hp
  · obtain ⟨port, hp, hv⟩ := prepare_visible_mem (bools := bools) (bits := bits) L1 a nd.1 b hb hk
    refine ⟨port, hp, ?_⟩
    rw [prepare_append, prepare_visible_keep L2 _ b.2 ?_]
    · exact hv
    · intro hin
      exact nd.2.2 b.2 (List.mem_map_of_mem hb) b.2 hin rfl

/-- **Where the binder at position `pos` is bound**, after a walk `L1 ++ L2`
(`L2` without domains, the `let`s): to one of `L1`'s ports when `pos` is in
`L1`, to the port at its index among `L2`'s when it is in `L2`. -/
theorem bound_where {bools bits} (L1 L2 : List ((Name × MixedGateBinder) × FVarId)) (a : Setup)
    (nd : ((L1 ++ L2).map Prod.snd).Nodup) (hk2 : ∀ b ∈ L2, b.1.2 ≠ .domain)
    (hlen : (inputPorts bools bits L2 (prepare bools bits L1 a)).length = L2.length)
    {pos : Nat} {b : (Name × MixedGateBinder) × FVarId} (hb : (L1 ++ L2)[pos]? = some b)
    (hk : b.1.2 ≠ .domain) :
    (pos < L1.length ∧ ∃ port ∈ inputPorts bools bits L1 a,
      visible (prepare bools bits (L1 ++ L2) a).context
        (prepare bools bits (L1 ++ L2) a).state.sourceBindings b.2 = some port.name) ∨
    (∃ i port, pos = L1.length + i ∧
      (inputPorts bools bits L2 (prepare bools bits L1 a))[i]? = some port ∧
      visible (prepare bools bits (L1 ++ L2) a).context
        (prepare bools bits (L1 ++ L2) a).state.sourceBindings b.2 = some port.name) := by
  obtain ⟨hA, hB⟩ := binding_split (bools := bools) (bits := bits) L1 L2 a nd hk2
  by_cases hlt : pos < L1.length
  · rw [List.getElem?_append_left hlt] at hb
    obtain ⟨port, hp, hv⟩ := hB b (List.mem_of_getElem? hb) hk
    exact Or.inl ⟨hlt, port, hp, hv⟩
  · have hge : L1.length ≤ pos := Nat.le_of_not_lt hlt
    rw [List.getElem?_append_right hge] at hb
    have hi : pos - L1.length < L2.length := (List.getElem?_eq_some_iff.mp hb).1
    have hp : (inputPorts bools bits L2 (prepare bools bits L1 a))[pos - L1.length]? =
        some ((inputPorts bools bits L2 (prepare bools bits L1 a))[pos - L1.length]'(hlen ▸ hi)) :=
      List.getElem?_eq_getElem _
    exact Or.inr ⟨pos - L1.length, _, by omega, hp, hA _ b _ hb hp⟩

/-! ## The aliases `letOperands` picks, with what the run says of each -/

/-- What the run says of the alias list, position by position from `i`: the
operand is declared at the width `m`; there is a suffix `pre` of the builder's
body with the operand's source (`Src`) and reads within `Vk i`; and the
operand, if protected, is in `Vk i`. -/
def Facts (P : String → Prop) (bnd : FVarId → Option String) (Vk : Nat → String → Prop)
    (wires : List Port) (body bodyB : List Stmt) :
    Nat → List (Port × String) → List Lean.Expr → List Nat → Prop
  | _, [], [], [] => True
  | i, pa :: al, e :: es, m :: ws =>
    wireWidth wires pa.2 = m ∧ (∃ x b, concatParts? body x = some (pa.2, b)) ∧
      (∃ pre, pre <:+ bodyB ∧ Src P bnd pre e pa.2 ∧
        ∀ l r, Stmt.assign l r ∈ pre → ReadsOK P (Vk i) r) ∧
      (P pa.2 → Vk i pa.2) ∧ Facts P bnd Vk wires body bodyB (i + 1) al es ws
  | _, _, _, _ => False

/-- The facts of the alias at index `k`. -/
theorem Facts.get {P : String → Prop} {bnd : FVarId → Option String} {Vk : Nat → String → Prop}
    {wires : List Port} {body bodyB : List Stmt} :
    ∀ {al : List (Port × String)} {es : List Lean.Expr} {ws : List Nat} {i : Nat} (k : Nat)
      {pa : Port × String}, Facts P bnd Vk wires body bodyB i al es ws → al[k]? = some pa →
      ∃ e m, es[k]? = some e ∧ ws[k]? = some m ∧ wireWidth wires pa.2 = m ∧
        (∃ x b, concatParts? body x = some (pa.2, b)) ∧
        (∃ pre, pre <:+ bodyB ∧ Src P bnd pre e pa.2 ∧
          ∀ l r, Stmt.assign l r ∈ pre → ReadsOK P (Vk (i + k)) r) ∧
        (P pa.2 → Vk (i + k) pa.2)
  | pa' :: al, e :: es, m :: ws, i, 0, pa, hf, hk => by
    cases hk
    exact ⟨e, m, rfl, rfl, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩
  | pa' :: al, e :: es, m :: ws, i, k + 1, pa, hf, hk => by
    obtain ⟨e', m', h1, h2, h3⟩ := Facts.get (i := i + 1) k hf.2.2.2.2 (by simpa using hk)
    refine ⟨e', m', by simpa using h1, by simpa using h2, ?_⟩
    rw [show i + (k + 1) = i + 1 + k by omega]
    exact h3
  | [], _, _, _, _, _, _, hk => by simp at hk
  | _ :: _, [], _, _, _, _, hf, _ => by cases hf
  | _ :: _, _ :: _, [], _, _, _, hf, _ => by cases hf

/-- **The aliases are the run's links.** With the spine (and its widths) on
the final body and the per-field facts on the builder's body — the same
statements, by the body's one-driver order — `letOperands` succeeds, on
exactly the operands the facts are about. -/
theorem letOperands_facts {P : String → Prop} {bnd : FVarId → Option String}
    {Vk : Nat → String → Prop} {wires : List Port} {body bodyB : List Stmt}
    (hacy : Acyclic body) (hsub : ∀ st ∈ bodyB, st ∈ body) :
    ∀ (ls : List Port) (ws : List Nat) (es : List Lean.Expr) (i : Nat) (w : String),
      ls.length = ws.length → SpineW wires body ws w → LP P bnd Vk bodyB i es w →
      es.length = ws.length →
      ∃ al core, letOperands body ls w = some (al, core) ∧ al.map (·.1) = ls ∧
        Facts P bnd Vk wires body bodyB i al es ws ∧
        (ws ≠ [] → ∃ x a, concatParts? body x = some (a, core))
  | [], [], [], _, w, _, _, _, _ => ⟨[], w, rfl, rfl, trivial, fun h => absurd rfl h⟩
  | p :: ls, m :: ws, e :: es, i, w, hl, hs, hlp, he => by
    obtain ⟨a, b, hc, hw, hs'⟩ := hs
    obtain ⟨x, y, pre, hm, hpre, hsrc, hv, hrd, hlp'⟩ := hlp
    have hxy := concatParts?_of_mem hacy (hsub _ hm)
    rw [hc] at hxy
    cases hxy
    obtain ⟨al, core, hlo, hmap, hf, hcore⟩ := letOperands_facts hacy hsub ls ws es (i + 1) b
      (by simpa using hl) hs' hlp' (by simpa using he)
    refine ⟨(p, a) :: al, core, ?_, by rw [List.map_cons, hmap],
      ⟨hw, ⟨w, b, hc⟩, ⟨pre, hpre, hsrc, hrd⟩, hv, hf⟩,
      fun _ => ?_⟩
    · simp only [letOperands, hc, hlo]
    · by_cases hws : ws = []
      · subst hws
        cases ls with
        | nil =>
          simp only [letOperands] at hlo
          cases hlo
          exact ⟨w, a, hc⟩
        | cons _ _ => simp at hl
      · exact hcore hws
  | [], _ :: _, _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, _, _, _, he => by simp at he
  | [], [], _ :: _, _, _, _, _, _, he => by simp at he

/-! ## From the facts to `closeLets` -/

theorem mem_of_writes {X : List Stmt} (h : Acyclic X) {x : String} (hx : x ∈ writesOf X) :
    ∃ r, Stmt.assign x r ∈ X := by
  unfold writesOf at hx
  obtain ⟨st, hst, hw⟩ := List.mem_flatMap.mp hx
  obtain ⟨l, r, rfl⟩ := Acyclic.assign h st hst
  have : x = l := by simpa [stmtWrites] using hw
  subst this
  exact ⟨r, hst⟩

/-- A prefix that does not contain `st` lies before `st`. -/
theorem prefix_before {α : Type} {X pre post : List α} {st : α}
    (h : X <+: pre ++ st :: post) (hn : st ∉ X) : X <+: pre := by
  rcases List.prefix_or_prefix_of_prefix h (List.prefix_append pre (st :: post)) with h1 | h1
  · exact h1
  · obtain ⟨Z, rfl⟩ := h1
    have hZ : Z <+: st :: post := by
      obtain ⟨Y, hY⟩ := h
      rw [List.append_assoc] at hY
      exact ⟨Y, List.append_cancel_left hY⟩
    cases Z with
    | nil => simp
    | cons z Z' =>
      have : z = st := by
        obtain ⟨Y, hY⟩ := hZ
        simp at hY
        exact hY.1
      subst this
      exact absurd (List.mem_append_right _ List.mem_cons_self) hn

theorem writes_prefix {X Y : List Stmt} (h : X <+: Y) : ∀ x ∈ writesOf X, x ∈ writesOf Y := by
  obtain ⟨Z, rfl⟩ := h
  intro x hx
  exact mem_writes_left hx

/-- **`closeLets` accepts**, from the run's facts about the transition module
and the per-field order facts. `hS2` is the one shape-side condition: a field
that is the variable of `let` `j` requires field `j` to be a variable too (the
case the real `closeLets` refuses otherwise). -/
theorem closeLets_isSome_of_facts {P : String → Prop} {bnd : FVarId → Option String}
    {Vk : Nat → String → Prop} {t : Sparkle.IR.AST.Module} {K : Nat} (hK : K ≠ 0)
    {bodyB : List Stmt} {w : String} {ws : List Nat} {es : List Lean.Expr}
    (hbody : t.body = bodyB.reverse ++ [.assign "out" (.ref w)])
    (hacy : Acyclic t.body)
    (hlsK : (t.inputs.drop (t.inputs.length - K)).length = K)
    (hlsnd : ((t.inputs.drop (t.inputs.length - K)).map (·.name)).Nodup)
    (hlsw : ∀ p ∈ t.inputs.drop (t.inputs.length - K), p.name ∉ writesOf t.body)
    (hlen : (t.inputs.drop (t.inputs.length - K)).length = ws.length) (hes : es.length = ws.length)
    (hwid : ∀ (k : Nat) (p : Port) (m : Nat), (t.inputs.drop (t.inputs.length - K))[k]? = some p → ws[k]? = some m →
      m = p.ty.bitWidth ∧ 0 < p.ty.bitWidth)
    (hspine : SpineW t.wires t.body ws w)
    (hout : ∀ x a b, concatParts? t.body x = some (a, b) → a ≠ "out" ∧ b ≠ "out")
    (hlp : LP P bnd Vk bodyB 0 es w)
    (hP : ∀ p ∈ t.inputs.drop (t.inputs.length - K), P p.name)
    (hnw : ∀ l r, Stmt.assign l r ∈ bodyB → ¬ P l)
    (hVk : ∀ (k k' : Nat) (p : Port), (t.inputs.drop (t.inputs.length - K))[k']? = some p → k ≤ k' → ¬ Vk k p.name)
    (hS2 : ∀ (i j : Nat) (id : FVarId) (p : Port), es[i]? = some (Lean.Expr.fvar id) →
      (t.inputs.drop (t.inputs.length - K))[j]? = some p → bnd id = some p.name →
      ∃ id', es[j]? = some (Lean.Expr.fvar id')) :
    (closeLets K t).isSome = true := by
  generalize hls : t.inputs.drop (t.inputs.length - K) = ls at *
  have hsub : ∀ st ∈ bodyB, st ∈ t.body := fun st hs => by
    rw [hbody]; exact List.mem_append_left _ (List.mem_reverse.mpr hs)
  have hB : Acyclic (bodyB.reverse ++ [Stmt.assign "out" (.ref w)]) := hbody ▸ hacy
  have hBw : ∀ x, x ∈ writesOf bodyB.reverse → x ∈ writesOf t.body := fun x hx => by
    rw [hbody]; exact mem_writes_left hx
  have hBmem : ∀ x, x ∈ writesOf bodyB.reverse → ∃ r, Stmt.assign x r ∈ bodyB := fun x hx => by
    obtain ⟨r, hr⟩ := mem_of_writes (Acyclic.prefix hB) hx
    exact ⟨r, List.mem_reverse.mp hr⟩
  have houtw : "out" ∈ writesOf t.body := by
    rw [hbody]; exact mem_writes_right (by simp [writesOf, stmtWrites])
  obtain ⟨al, core, hlo, hmap, hf, hcore⟩ := letOperands_facts hacy hsub ls ws es 0 w hlen hspine
    hlp hes
  have hwsne : ws ≠ [] := by
    intro h; rw [h] at hlen; rw [hlen] at hlsK; exact hK hlsK.symm
  have hidx : ∀ (k : Nat) (pa : Port × String), al[k]? = some pa → ls[k]? = some pa.1 := by
    intro k pa hk
    rw [← hmap, List.getElem?_map, hk]; rfl
  -- what each alias satisfies
  have hal : ∀ (k : Nat) (pa : Port × String), al[k]? = some pa →
      pa.1.name ∉ writesOf t.body ∧ P pa.1.name ∧ pa.2 ≠ "out" ∧
      wireWidth t.wires pa.2 = pa.1.ty.bitWidth ∧ 0 < pa.1.ty.bitWidth ∧
      ∃ e, es[k]? = some e ∧ (P pa.2 → Vk k pa.2) ∧
        ∃ pre, pre <:+ bodyB ∧ Src P bnd pre e pa.2 ∧
          ∀ l r, Stmt.assign l r ∈ pre → ReadsOK P (Vk k) r := by
    intro k pa hk
    have hp := hidx k pa hk
    have hmem : pa.1 ∈ ls := List.mem_of_getElem? hp
    obtain ⟨e, m, he, hm, hw, ⟨x, b, hc⟩, hpre, hv⟩ := hf.get k hk
    obtain ⟨hm1, hm2⟩ := hwid k pa.1 m hp hm
    refine ⟨hlsw _ hmem, hP _ hmem, (hout x pa.2 b hc).1, by rw [hw, hm1], hm2, e, he,
      by simpa using hv, ?_⟩
    obtain ⟨pre, h1, h2, h3⟩ := hpre
    exact ⟨pre, h1, h2, by simpa using h3⟩
  have hgetAl : ∀ pa ∈ al, ∃ k, al[k]? = some pa := fun pa h => List.mem_iff_getElem?.mp h
  -- an operand is its port's name only if it is protected
  have hne : ∀ (k k' : Nat) (pa pb : Port × String), al[k]? = some pa → al[k']? = some pb → k ≤ k' →
      pa.2 ≠ pb.1.name := by
    intro k k' pa pb hk hk' hle heq
    obtain ⟨-, -, -, -, -, e, -, hv, -⟩ := hal k pa hk
    obtain ⟨-, hPb, -⟩ := hal k' pb hk'
    exact hVk k k' pb.1 (hidx k' pb hk') hle (heq ▸ hv (heq ▸ hPb))
  rw [closeLets_isSome_iff hK]
  refine ⟨w, al, core, by simp [packedWire?, hbody], hls ▸ hlo, ?_, ?_, ?_, ?_⟩
  · intro pa hpa
    obtain ⟨k, hk⟩ := hgetAl pa hpa
    obtain ⟨h1, -, h3, h4, h5, -⟩ := hal k pa hk
    exact ⟨h4, h5, fun h => h1 (h ▸ houtw), h3⟩
  · intro pa hpa
    obtain ⟨k, hk⟩ := hgetAl pa hpa
    exact (hal k pa hk).1
  · obtain ⟨x, a, hc⟩ := hcore hwsne
    exact (hout x a core hc).2
  · rw [Tools.ShippingSettledSoundness.assignmentOrderCheck_iff]
    unfold closedBody
    have hdrop : t.body.dropLast = bodyB.reverse := by rw [hbody]; simp
    rw [hdrop]
    refine closed_acyclic al hB ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [show al.map (·.1.name) = (al.map (·.1)).map (·.name) by simp, hmap]; exact hlsnd
    · intro pa hpa
      obtain ⟨k, hk⟩ := hgetAl pa hpa
      obtain ⟨h1, -⟩ := hal k pa hk
      exact ⟨fun h => h1 (hBw _ h), fun h => h1 (h ▸ houtw)⟩
    · intro pa hpa
      obtain ⟨k, hk⟩ := hgetAl pa hpa
      exact ⟨(hal k pa hk).2.2.1, hne k k pa pa hk hk (Nat.le_refl _)⟩
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      exact hne i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) (Nat.le_of_lt hij)
    · -- an operand that is another alias' port: that alias' operand is driven by nothing
      intro pa hpa pa' hpa' heq hw'
      obtain ⟨i, hi⟩ := hgetAl pa hpa
      obtain ⟨j, hj⟩ := hgetAl pa' hpa'
      obtain ⟨-, -, -, -, -, e, he, -, pre, hpre, hsrc, -⟩ := hal i pa hi
      obtain ⟨-, hPp, -, -, -, e', he', -, pre', hpre', hsrc', -⟩ := hal j pa' hj
      have hPa : P pa.2 := heq ▸ hPp
      rcases hsrc with ⟨-, rhs, hm⟩ | ⟨id, hid, hb, -⟩
      · exact hnw _ rhs (hpre.subset hm) hPa
      · obtain ⟨id', hid'⟩ := hS2 i j id pa'.1 (hid ▸ he) (hidx j pa' hj) (heq ▸ hb)
        rw [he'] at hid'
        cases hid'
        rcases hsrc' with ⟨hf', -⟩ | ⟨-, -, -, hP'⟩
        · cases hf'
        · obtain ⟨r, hr⟩ := hBmem _ hw'
          exact hnw _ r hr hP'
    · obtain ⟨x, a, hc⟩ := hcore hwsne
      exact (hout x a core hc).2
    · -- every reader of a port comes after the driver of its operand
      intro pa hpa pre0 l r post hsplit hx
      obtain ⟨k, hk⟩ := hgetAl pa hpa
      obtain ⟨-, hPp, -, -, -, e, -, -, pre, hpre, hsrc, hrd⟩ := hal k pa hk
      rcases hsrc with ⟨-, rhs, hm⟩ | ⟨-, -, -, hPa⟩
      · left
        have hnotin : Stmt.assign l r ∉ pre.reverse := by
          intro hin
          have := hrd l r (List.mem_reverse.mp hin) _ hx hPp
          exact hVk k k pa.1 (hidx k pa hk) (Nat.le_refl _) this
        have hpfx : pre.reverse <+: bodyB.reverse := List.reverse_prefix.mpr hpre
        rw [hsplit] at hpfx
        exact writes_prefix (prefix_before hpfx hnotin) _
          (mem_writes_assign (List.mem_reverse.mpr hm))
      · right
        intro hw'
        obtain ⟨r', hr'⟩ := hBmem _ hw'
        exact hnw _ r' hr' hPa

/-! ## The shape-side predicates -/

/-- The term is an input variable. -/
def IsVar : {s : SType} → Term s → Prop
  | _, .boolInput _ => True
  | _, .bitsInput _ _ => True
  | _, _ => False

/-- The term is the input variable whose binder position is `n`. -/
def VarPos (bpos vpos : Nat → Nat) : {s : SType} → Term s → Nat → Prop
  | _, .boolInput q, n => bpos q = n
  | _, .bitsInput _ q, n => vpos q = n
  | _, _, _ => False

theorem quote_isVar {dom : Lean.Expr} {bi vi : Nat → FVarId} {s : SType} (e : Term s)
    (h : IsVar e) : ∃ id, quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e = .fvar id := by
  cases e <;> first | exact ⟨_, rfl⟩ | exact h.elim

/-- A quoted well-formed term that is a variable is an input variable, at its
binder's position. -/
theorem quote_fvar_var {dom : Lean.Expr} {bi vi : Nat → FVarId} {bpos vpos : Nat → Nat}
    {kb kv : Nat} {vw : Nat → Nat} {id : FVarId} {s : SType} (e : Term s) (hwf : e.WF kb kv vw)
    (h : quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e = .fvar id) :
    (∃ q, q < kb ∧ VarPos bpos vpos e (bpos q) ∧ id = bi q) ∨
      (∃ q, q < kv ∧ VarPos bpos vpos e (vpos q) ∧ id = vi q) := by
  cases e
  case boolInput q => exact Or.inl ⟨q, hwf, rfl, by cases h; rfl⟩
  case bitsInput w q => exact Or.inr ⟨q, hwf.1, rfl, by cases h; rfl⟩
  all_goals (first | cases h | (simp [quote] at h))

/-- A well-formed term uses only variables below its bounds. -/
theorem uses_of_wf {ub uv : Nat → Prop} {kb kv : Nat} {vw : Nat → Nat}
    (hub : ∀ j, j < kb → ub j) (huv : ∀ j, j < kv → uv j) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → Uses ub uv e
  | _, .boolInput j, h => hub j h
  | _, .bitsInput _ j, h => ⟨huv j h.1, trivial, trivial⟩
  | _, .boolLit _, _ => trivial
  | _, .bitsLit _ _, _ => trivial
  | _, .bitsNum _ _, _ => trivial
  | _, .binary _ a b, h => ⟨uses_of_wf hub huv a h.1, uses_of_wf hub huv b h.2⟩
  | _, .compare _ a b, h => ⟨uses_of_wf hub huv a h.1, uses_of_wf hub huv b h.2⟩
  | _, .boolBinary _ a b, h => ⟨uses_of_wf hub huv a h.1, uses_of_wf hub huv b h.2⟩
  | _, .boolNot a, h => uses_of_wf hub huv a h
  | _, .boolEq a b, h => ⟨uses_of_wf hub huv a h.1, uses_of_wf hub huv b h.2⟩
  | _, .mux c a b, h => ⟨uses_of_wf hub huv c h.1, uses_of_wf hub huv a h.2.1, uses_of_wf hub huv b h.2.2⟩
  | _, .setw _ a, h => ⟨uses_of_wf hub huv a h.1, trivial⟩
  | _, .appCompare _ a b, h => ⟨uses_of_wf hub huv a h.1, uses_of_wf hub huv b h.2⟩
  | _, .appBool _ a b, h => ⟨uses_of_wf hub huv a h.1, uses_of_wf hub huv b h.2⟩
  | _, .appBool2 _ a b, h => ⟨uses_of_wf hub huv a h.1, uses_of_wf hub huv b h.2⟩
  | _, .slice _ _ _ a, h => ⟨uses_of_wf hub huv a h.1, trivial, trivial⟩
  | _, .concat a b, h => ⟨uses_of_wf hub huv a h.1, uses_of_wf hub huv b h.2⟩
  | _, .concatLitHi _ _ b, h => ⟨uses_of_wf hub huv b h.1, trivial, trivial⟩
  | _, .concatLitLo a _ _, h => ⟨uses_of_wf hub huv a h.1, trivial, trivial⟩
  | _, .zextMap _ _ a, h => ⟨uses_of_wf hub huv a h.1, trivial⟩
  | _, .sliceF _ _ _ a, h => ⟨uses_of_wf hub huv a h.1, trivial, trivial⟩

theorem fieldsOK_get {ubk uvk : Nat → Nat → Prop} {kb kv : Nat} {vw : Nat → Nat} :
    ∀ {fs : List (Σ w : Nat, Term (.bits w))} {i : Nat} (k : Nat) {f : Σ w : Nat, Term (.bits w)},
      FieldsOK ubk uvk kb kv vw i fs → fs[k]? = some f →
      f.2.WF kb kv vw ∧ Uses (ubk (i + k)) (uvk (i + k)) f.2
  | _ :: _, _, 0, _, h, hk => by cases hk; exact ⟨h.1, h.2.1⟩
  | _ :: fs, i, k + 1, f, h, hk => by
    have := fieldsOK_get (i := i + 1) k h.2.2 (by simpa using hk)
    rw [show i + (k + 1) = i + 1 + k by omega]
    exact this
  | [], _, _, _, _, hk => by simp at hk

theorem nodup_index {l : List Port} (h : (l.map Port.name).Nodup) {i j : Nat} {p q : Port}
    (hi : l[i]? = some p) (hj : l[j]? = some q) (hn : p.name = q.name) : i = j := by
  have hi' : (l.map Port.name)[i]? = some p.name := by rw [List.getElem?_map, hi]; rfl
  have hj' : (l.map Port.name)[j]? = some q.name := by rw [List.getElem?_map, hj]; rfl
  have hpw := List.pairwise_iff_getElem.mp h
  have bi := (List.getElem?_eq_some_iff.mp hi').1
  have bj := (List.getElem?_eq_some_iff.mp hj').1
  have ei := (List.getElem?_eq_some_iff.mp hi').2
  have ej := (List.getElem?_eq_some_iff.mp hj').2
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact absurd (ei.trans (hn.trans ej.symm)) (hpw i j bi bj hlt)
  · exact heq
  · exact absurd (ej.trans (hn.symm.trans ei.symm)) (hpw j i bj bi hgt)

/-! ## The transition of a packed machine body closes -/

set_option maxHeartbeats 1000000 in
/-- **`closeLets` accepts the transition of every run of the harness** on a
packed machine body whose binders are `bsIn ++ letBs`, under two shape-side
conditions on the fields: `hscope` — field `k` uses only variables whose
binder comes before `let` `k`; `hS2` — a field that is the variable of `let`
`j` requires field `j` to be a variable too (otherwise the real `closeLets`
refuses). Nothing is assumed of the run. -/
theorem transition_closes {logProf : String → IO Unit} {declName : Name}
    {bs : List (Name × MixedGateBinder)} {body : Lean.Expr} {m : Sparkle.IR.AST.Module}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} {returned : String}
    {st : CircuitState}
    (nd : ids.Nodup) (len : ids.length = bs.length)
    (run : Returns (bindMixedCertifiedInputs
        (emitLeaves (fun e hint top named => translateExprToWire tenv e hint top named) cache logProf
          [("out", instFVars (ids.map Lean.Expr.fvar).toArray 0 body)] none 0) (bs.zip ids))
        (entryCompilerState false cache) (CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName)) returned st)
    (hm : m = (addClockResetIfSequential st.module).finalize)
    (nameLegal : Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true)
    (positive : PositiveBinders bs)
    {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c))
    (he : (packLets fs core).2.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (hbody : body = quote dom (fun j => inputExpr bs.length (bpos j))
      (fun j => inputExpr bs.length (vpos j)) (packLets fs core).2)
    {bsIn letBs : List (Name × MixedGateBinder)} (hbs : bs = bsIn ++ letBs) (hK : letBs ≠ [])
    (letKinds : ∀ b ∈ letBs, b.2 ≠ .domain)
    (hfitL : fs.length = letBs.length)
    (hfit : ∀ (k : Nat) (b : Name × MixedGateBinder) (f : Σ w : Nat, Term (.bits w)),
      letBs[k]? = some b → fs[k]? = some f → machWidth b.2 = f.1)
    (hscope : FieldsOK (fun k j => j < kb ∧ bpos j < bsIn.length + k)
      (fun k j => j < kv ∧ vpos j < bsIn.length + k) kb kv vw 0 fs)
    (hS2 : ∀ (i j : Nat) (fi fj : Σ w : Nat, Term (.bits w)), fs[i]? = some fi → fs[j]? = some fj →
      VarPos bpos vpos fi.2 (bsIn.length + j) → IsVar fj.2) :
    (closeLets letBs.length m).isSome = true := by
  -- the run's facts about the module
  have facts := transition_facts nd len run hm nameLegal he hb hv hbody
  obtain ⟨B, w, hB, hspine, hports, hlink⟩ :=
    transition_spine nd len run hm nameLegal positive fs core he hb hv hbody
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  have zero : SourceInputs declName bs ids cache (fun _ => false) (fun _ n => 0#n)
      (fun _ => 0) := admissible_zero _ _
  obtain ⟨_, _, _, ready, _, _, _, _, base⟩ := facts.1 _ _ _ (fun _ _ => 0) zero
  have pb := base positive
  have hin := facts.2.2 (boolValues ids fun _ => false) (bitValues ids fun _ n => 0#n)
  -- the port walk in two parts
  let a := start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName)
  let zb := boolValues ids fun _ => false
  let zv := bitValues ids fun _ n => 0#n
  let L1 := bsIn.zip (ids.take bsIn.length)
  let L2 := letBs.zip (ids.drop bsIn.length)
  have hidsLen : ids.length = bsIn.length + letBs.length := by rw [len, hbs, List.length_append]
  have hzip : bs.zip ids = L1 ++ L2 := by
    show bs.zip ids = bsIn.zip (ids.take bsIn.length) ++ letBs.zip (ids.drop bsIn.length)
    conv => lhs; rw [hbs, ← List.take_append_drop bsIn.length ids]
    rw [List.zip_append (by simp; omega)]
  have hL1 : L1.length = bsIn.length := by simp [L1]; omega
  have hL2 : L2.length = letBs.length := by simp [L2]; omega
  have hL2dom : ∀ b ∈ L2, b.1.2 ≠ .domain := fun b hb' => letKinds b.1 (List.of_mem_zip hb').1
  let PI := inputPorts zb zv L1 a
  let ls := inputPorts zb zv L2 (prepare zb zv L1 a)
  have hinputs : m.inputs = PI ++ ls := by
    rw [hin, hzip, inputPorts_append]
  have lsTypes := inputPorts_types (bools := zb) (bits := zv) L2 (prepare zb zv L1 a) hL2dom
  have lsLen : ls.length = letBs.length := by rw [lsTypes.length_eq, hL2]
  have hdrop : m.inputs.drop (m.inputs.length - letBs.length) = ls := by
    rw [hinputs, List.length_append, lsLen, Nat.add_sub_cancel, List.drop_left]
  have inNodup : ((PI ++ ls).map Port.name).Nodup := hinputs ▸ pb.inputNames
  rw [List.map_append, List.nodup_append] at inNodup
  have ndz : ((L1 ++ L2).map Prod.snd).Nodup := hzip ▸ fresh
  -- where a term variable is bound
  have hwhere : ∀ (pos : Nat) (binder : Name × MixedGateBinder), bs[pos]? = some binder →
      binder.2 ≠ .domain → ∀ z,
      visible (prepare zb zv (bs.zip ids) a).context
        (prepare zb zv (bs.zip ids) a).state.sourceBindings ids[pos]! = some z →
      (pos < bsIn.length ∧ ∃ port ∈ PI, z = port.name) ∨
        (∃ i port, pos = bsIn.length + i ∧ ls[i]? = some port ∧ z = port.name) := by
    intro pos binder hpos hk z hz
    have hmem : (L1 ++ L2)[pos]? = some (binder, ids[pos]!) := by
      rw [← hzip]
      have bound : pos < bs.length := (List.getElem?_eq_some_iff.mp hpos).1
      exact List.getElem?_zip_eq_some.mpr ⟨hpos, by
        simp [List.getElem?_eq_getElem (show pos < ids.length by omega),
          List.getElem!_eq_getElem?_getD]⟩
    rw [hzip] at hz
    rcases bound_where (bools := zb) (bits := zv) L1 L2 a ndz hL2dom
      (by rw [lsTypes.length_eq]) hmem hk with ⟨hlt, port, hp, hv'⟩ | ⟨i, port, hi, hp, hv'⟩
    · rw [hv'] at hz
      cases hz
      exact Or.inl ⟨hL1 ▸ hlt, port, hp, rfl⟩
    · rw [hv'] at hz
      cases hz
      exact Or.inr ⟨i, port, hL1 ▸ hi, hp, rfl⟩
  have lsNodup : (ls.map Port.name).Nodup := inNodup.2.1
  have lsDisj : ∀ p ∈ PI, ∀ q ∈ ls, p.name ≠ q.name := fun p hp q hq =>
    inNodup.2.2 p.name (List.mem_map_of_mem hp) q.name (List.mem_map_of_mem hq)
  -- the ports a position may read: not the `let` ports from it on
  let Vk : Nat → String → Prop := fun k x => ∀ (j : Nat) (p : Port), k ≤ j → ls[j]? = some p → x ≠ p.name
  have hbind : ∀ k id z,
      Bk (fun j => ids[bpos j]!) (fun j => ids[vpos j]!) (fun k j => j < kb ∧ bpos j < bsIn.length + k)
        (fun k j => j < kv ∧ vpos j < bsIn.length + k) k id →
      visible (prepare zb zv (bs.zip ids) a).context
        (prepare zb zv (bs.zip ids) a).state.sourceBindings id = some z → Vk k z := by
    rintro k id z (⟨q, ⟨hq, hpos⟩, rfl⟩ | ⟨q, ⟨hq, hpos⟩, rfl⟩) hz j p hkj hp heq
    · obtain ⟨name, hbq⟩ := hb q hq
      rcases hwhere (bpos q) (name, .bool) hbq (by simp) z hz with
        ⟨-, port, hport, rfl⟩ | ⟨i, port, hi, hpi, rfl⟩
      · exact lsDisj port hport p (List.mem_of_getElem? hp) heq
      · have := nodup_index lsNodup hpi hp heq
        omega
    · obtain ⟨name, hvq⟩ := hv q hq
      rcases hwhere (vpos q) (name, .bits (vw q)) hvq (by simp) z hz with
        ⟨-, port, hport, rfl⟩ | ⟨i, port, hi, hpi, rfl⟩
      · exact lsDisj port hport p (List.mem_of_getElem? hp) heq
      · have := nodup_index lsNodup hpi hp heq
        omega
  have hbsLen : bs.length = bsIn.length + fs.length := by rw [hbs, List.length_append, hfitL]
  have hcoreU : Uses (fun j => j < kb ∧ bpos j < bsIn.length + fs.length)
      (fun j => j < kv ∧ vpos j < bsIn.length + fs.length) core :=
    uses_of_wf (fun j hj => ⟨hj, by
        obtain ⟨name, h⟩ := hb j hj
        have := (List.getElem?_eq_some_iff.mp h).1
        omega⟩)
      (fun j hj => ⟨hj, by
        obtain ⟨name, h⟩ := hv j hj
        have := (List.getElem?_eq_some_iff.mp h).1
        omega⟩) core (packLets_wf fs core he)
  subst hbody
  obtain ⟨bodyB, w', hbody', hlp, hnw, hused⟩ := harness_links_at run hm zb zv (fun _ => 0) zero
    (instFVars (ids.map Lean.Expr.fvar).toArray 0 dom)
    kb kv vw (fun j => ids[bpos j]!) (fun j => ids[vpos j]!) (fun _ => false) (fun _ n => 0#n)
    fs core he
    (by
      intro j hj
      obtain ⟨name, pos⟩ := hb j hj
      have bound := (List.getElem_of_getElem? pos).choose
      have lookup := prepare_bool_lookup (bools := boolValues ids fun _ => false)
        (bits := bitValues ids fun _ n => 0#n) (bs.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName)) fresh (zip_member len pos)
      simpa only [boolValues, index_fresh ids nd (bpos j) (by omega)] using lookup)
    (by
      intro j hj
      obtain ⟨name, pos⟩ := hv j hj
      have bound := (List.getElem_of_getElem? pos).choose
      have lookup := prepare_bits_lookup (bools := boolValues ids fun _ => false)
        (bits := bitValues ids fun _ n => 0#n) (bs.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName)) fresh (zip_member len pos)
      simpa only [bitValues, index_fresh ids nd (vpos j) (by omega)] using lookup)
    (by
      apply instantiated_quote _ _ _ he
      · intro j hj
        obtain ⟨name, pos⟩ := hb j hj
        exact instantiated_input len (List.getElem_of_getElem? pos).choose
      · intro j hj
        obtain ⟨name, pos⟩ := hv j hj
        exact instantiated_input len (List.getElem_of_getElem? pos).choose)
    (Vk := Vk) (fun k x h j p hkj hp => h j p (by omega) hp) hbind hscope hcoreU
  -- the two decompositions of the body are the same
  have hsame := hB.symm.trans hbody'
  obtain ⟨hBeq, hweq⟩ := List.append_inj' hsame rfl
  cases hweq
  refine closeLets_isSome_of_facts (Vk := Vk) (ws := fs.map (·.1))
    (fun h => hK (List.length_eq_zero_iff.mp h)) hbody' pb.order
    (by rw [hdrop]; exact lsLen) (by rw [hdrop]; exact lsNodup)
    (by rw [hdrop]; exact fun p hp => hports p (hinputs ▸ List.mem_append_right _ hp))
    (by rw [hdrop, lsLen, List.length_map, hfitL]) (by simp) ?_ hspine hlink hlp ?_ hnw
    (by rw [hdrop]; exact fun k k' p hp hle h => h k' p hle hp rfl) ?_
  · -- a `let` port is as wide as its field, and that is positive
    rw [hdrop]
    intro k p mm hp hm'
    rw [List.getElem?_map] at hm'
    cases hfk : fs[k]? with
    | none => rw [hfk] at hm'; cases hm'
    | some f =>
      rw [hfk] at hm'
      cases hm'
      have hk : k < L2.length := by
        rw [hL2, ← lsLen]; exact (List.getElem?_eq_some_iff.mp hp).1
      have hty := lsTypes.get k p _ hp (List.getElem?_eq_getElem hk)
      have hb2 : letBs[k]? = some (L2[k]).1 := by
        have := List.getElem?_eq_getElem hk
        obtain ⟨h1, -⟩ := List.getElem?_zip_eq_some.mp this
        exact h1
      rw [hty, kindTy_bitWidth _ (hL2dom _ (List.getElem_mem hk)), hfit k _ f hb2 hfk]
      exact ⟨rfl, f.2.wf_pos (fieldsOK_get k hscope hfk).1⟩
  · -- the `let` ports are in use before the translation
    rw [hdrop]
    intro p hp
    apply hused
    rw [prepare_inputs, ← hin]
    simp only [start, CircuitM.init, Module.empty, List.append_nil, List.mem_reverse]
    exact hinputs ▸ List.mem_append_right _ hp
  · -- a field that is the variable of `let` `j`
    rw [hdrop]
    intro i j id p hei hlj hbnd
    rw [List.getElem?_map] at hei
    cases hfi : fs[i]? with
    | none => rw [hfi] at hei; cases hei
    | some fi =>
      rw [hfi] at hei
      have hq : quote (instFVars (ids.map Lean.Expr.fvar).toArray 0 dom)
          (fun j => .fvar (ids[bpos j]!)) (fun j => .fvar (ids[vpos j]!)) fi.2 = .fvar id := by
        simpa using hei
      have hjlt : j < fs.length := by
        rw [hfitL, ← lsLen]; exact (List.getElem?_eq_some_iff.mp hlj).1
      have key : ∀ (pos : Nat) (binder : Name × MixedGateBinder), bs[pos]? = some binder →
          binder.2 ≠ .domain → id = ids[pos]! → VarPos bpos vpos fi.2 pos →
          ∃ id', (fs.map fun f => quote (instFVars (ids.map Lean.Expr.fvar).toArray 0 dom)
            (fun j => Lean.Expr.fvar (ids[bpos j]!)) (fun j => Lean.Expr.fvar (ids[vpos j]!)) f.2)[j]? =
              some (Lean.Expr.fvar id') := by
        intro pos binder hpos hk hid hvp
        subst hid
        rcases hwhere pos binder hpos hk p.name hbnd with ⟨-, port, hport, heq⟩ | ⟨i', port, hi', hpi, heq⟩
        · exact absurd heq.symm (lsDisj port hport p (List.mem_of_getElem? hlj))
        · have hij := nodup_index lsNodup hpi hlj heq.symm
          subst hij
          subst hi'
          have hfj := List.getElem?_eq_getElem hjlt
          obtain ⟨id', hid'⟩ := quote_isVar (dom := instFVars (ids.map Lean.Expr.fvar).toArray 0 dom)
            (bi := fun j => ids[bpos j]!) (vi := fun j => ids[vpos j]!) _ (hS2 i i' fi _ hfi hfj hvp)
          exact ⟨id', by rw [List.getElem?_map, hfj]; exact congrArg some hid'⟩
      rcases quote_fvar_var (bpos := bpos) (vpos := vpos) fi.2 (fieldsOK_get i hscope hfi).1 hq with
        ⟨q, hq', hvp, hid⟩ | ⟨q, hq', hvp, hid⟩
      · obtain ⟨name, hbq⟩ := hb q hq'
        exact key (bpos q) _ hbq (by simp) hid hvp
      · obtain ⟨name, hvq⟩ := hv q hq'
        exact key (vpos q) _ hvq (by simp) hid hvp

/-! ## `MachineCloses`, proved -/

/-- **`closeLets` accepts the transition of every run of the harness** — for
a shape with or without calls, in every Meta and Core context. The premises
are about the SHAPE (its binders, its packed body, the two conditions on the
fields); none is about a run. -/
theorem letsClose_of_lets {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {declName : Name}
    {shape : MachineShape}
    (positive : PositiveBinders shape.binders)
    {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c))
    (he : (packLets fs core).2.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, shape.binders[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, shape.binders[vpos j]? = some (name, .bits (vw j)))
    (hbody : shape.body = quote dom (fun j => inputExpr shape.binders.length (bpos j))
      (fun j => inputExpr shape.binders.length (vpos j)) (packLets fs core).2)
    {bsIn letBs : List (Name × MixedGateBinder)} (hbs : shape.binders = bsIn ++ letBs)
    (hlets : shape.layout.lets = letBs.length)
    (letKinds : ∀ b ∈ letBs, b.2 ≠ .domain)
    (hfitL : fs.length = letBs.length)
    (hfit : ∀ (k : Nat) (b : Name × MixedGateBinder) (f : Σ w : Nat, Term (.bits w)),
      letBs[k]? = some b → fs[k]? = some f → machWidth b.2 = f.1)
    (hscope : FieldsOK (fun k j => j < kb ∧ bpos j < bsIn.length + k)
      (fun k j => j < kv ∧ vpos j < bsIn.length + k) kb kv vw 0 fs)
    (hS2 : ∀ (i j : Nat) (fi fj : Σ w : Nat, Term (.bits w)), fs[i]? = some fi → fs[j]? = some fj →
      VarPos bpos vpos fi.2 (bsIn.length + j) → IsVar fj.2) :
    Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName shape := by
  intro logProf w t d w' hr
  by_cases hK : letBs = []
  · rw [hlets, hK]
    rfl
  · obtain ⟨ids, cache, returned, st, nd, len, run, hm, -, nameLegal⟩ :=
      synthesizeMixedCertified_returns hr.mreturns
    rw [hlets]
    exact transition_closes nd len run hm nameLegal positive fs core he hb hv hbody hbs hK letKinds
      hfitL hfit hscope hS2

/-- **`MachineCloses` for a shape with `let`s and no calls** — in every Meta
and Core context, for every run: the machine synthesis does not fall back.
The premises are about the SHAPE; none is about a run. -/
theorem machineCloses_of_lets {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {declName : Name}
    {shape : MachineShape} (hi : shape.insts = [])
    (positive : PositiveBinders shape.binders)
    {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c))
    (he : (packLets fs core).2.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, shape.binders[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, shape.binders[vpos j]? = some (name, .bits (vw j)))
    (hbody : shape.body = quote dom (fun j => inputExpr shape.binders.length (bpos j))
      (fun j => inputExpr shape.binders.length (vpos j)) (packLets fs core).2)
    {bsIn letBs : List (Name × MixedGateBinder)} (hbs : shape.binders = bsIn ++ letBs)
    (hlets : shape.layout.lets = letBs.length)
    (letKinds : ∀ b ∈ letBs, b.2 ≠ .domain)
    (hfitL : fs.length = letBs.length)
    (hfit : ∀ (k : Nat) (b : Name × MixedGateBinder) (f : Σ w : Nat, Term (.bits w)),
      letBs[k]? = some b → fs[k]? = some f → machWidth b.2 = f.1)
    (hscope : FieldsOK (fun k j => j < kb ∧ bpos j < bsIn.length + k)
      (fun k j => j < kv ∧ vpos j < bsIn.length + k) kb kv vw 0 fs)
    (hS2 : ∀ (i j : Nat) (fi fj : Σ w : Nat, Term (.bits w)), fs[i]? = some fi → fs[j]? = some fj →
      VarPos bpos vpos fi.2 (bsIn.length + j) → IsVar fj.2) :
    MachineCloses mctx mref cctx cref declName shape :=
  Tools.ShippingClosesSplit.machineCloses_of_letsClose hi
    (letsClose_of_lets positive fs core he hb hv hbody hbs hlets letKinds hfitL hfit hscope hS2)

end Tools.ShippingMachineCloses

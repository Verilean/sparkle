import Tools.ShippingReaderFuelShape
import Tools.ShippingReaderFuelR5
import Tools.ShippingShapeDecomp

/-! # Wrapper-level R5 for the fuel CANDIDATE `machineShapeF`, keeping the reader state

BUILT on poc after fbb445d0 (run `h1`; integrator fixes in okO_run_inv and shapePost_decomp) (worker H, branch `par/r-12`, from poc `a3a1d2d4`;
reviewer ruling 2026-10-16 "wrapper-level R5"). No `sorry`, no axiom, no
`native_decide`. Nothing here is imported by the compiler; no compiler change.

SCOPE. Every statement is about the fuel candidate wrapper `machineShapeF`
(`Tools/ShippingReaderFuelShape.lean`) and the fuel readers it calls. NONE of
it is a statement about the old `machineShape?` (whose readers are `partial`,
i.e. opaque): connecting the two needs O1/O2 and is NOT done here.

## What is new compared to `Tools/ShippingShapeDecomp.lean`

`machineShape?_decomp` decomposes the REAL wrapper but throws the reader
state away: it says `sp.binders = bs ++ … ++ names.zip kinds ++ letB` with
`names`, `kinds`, `inits` arbitrary lists, so R5 stays a hypothesis. Here the
decomposition of the candidate keeps the state through every phase:

* `shapePre_facts` — the pure prefix (`ci` is a definition, the peel, the
  output list `declOuts?`);
* `machineShapeF_steps` — the run equations of ALL phases with their states:
  `machNormF` → `shapeStart` (state `st0`) → root-let fold (`st1`) →
  `shapeBody` (`st`) → `shapePost`;
* `shapeStart_inv` — initial state `{}` (no enclosing machine), or domain
  conversion (`machConvF … {}`) then `machReserve … {}`;
* `shapeBody_inv` — the enclosing machine's chain (`machChainF`, state with
  `ws` appended) or the root conversion (`machConvF`);
* `shapePost_decomp` — the shape built from the FINAL state: binders, slots,
  outputs, `lets`, with `names / kinds / inits = st.names / st.kinds /
  st.inits` (not existential lists);
* `machineShapeF_lenOk` — `LenOk` of the state at each phase, from
  `machReserve_lenOk_init`, the update lemmas and `readF_good`
  (`Tools/ShippingReaderFuelR5.lean`).

## The R5 conditions derived from EVERY successful candidate result

From `machineShapeF n … ci … = some (some sp)`:

* `machineShapeF_decomp` — `ci = .defnInfo d` and a `ShapeDecomp` (the SAME
  bundle the old line uses) whose `names`, `kinds`, `inits` have one length;
* `machineShapeF_r5` — R5: `(names.zip kinds).length = sp.layout.slots.length`;
* `machineShapeF_binderCount` — `sp.binders.length = bs.length +
  sp.insts.length + sp.layout.slots.length + sp.layout.lets` for the peel
  `bs` of the definition's value (the "binder count" the generator checks at
  the meta level);
* `machineShapeF_nDecl` — the closing's `nDecl` (`closeInstsM` /
  `closeInstsGM`) is `bs.length`;
* `machineShapeF_callBinder` — the binder at `nDecl + k` has call entry
  `k`'s kind (R4 at the closing's position, R5 discharged);
* `machineShapeF_slots_length` — the layout has as many slots as the state
  has kinds, names and reset values.

MEASURED axioms (run `ax18`, poc after 3a1938a3): `machineShapeF_nDecl`, `machineShapeF_single_out`:
[propext, Classical.choice, Quot.sound]. (Originally predicted: `propext`, `Quot.sound` (from `omega` / `simp`-free
rewriting; `Classical.choice` only if a library lemma used pulls it).) -/
namespace Tools.ShippingReaderFuelShapeR5
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingReaderFuel
open Tools.ShippingReaderLenOk
open Tools.ShippingMachineShapeUnfold
open Tools.ShippingShapeDecomp

/-! ## Inversions of the `FM` combinators (generic) -/

theorem bind_some_inv {κ : Type} {R : κ → Type} {α β : Type} {h : (c : κ) → Option (R c)}
    {x : FM κ R α} {f : α → FM κ R β} {b : β}
    (hr : (FM.bind x f).run h = some b) : ∃ a, x.run h = some a ∧ (f a).run h = some b := by
  rw [run_bind] at hr
  exact Option.bind_eq_some_iff.mp hr

theorem bindO_some_inv {κ : Type} {R : κ → Type} {α β : Type} {h : (c : κ) → Option (R c)}
    {x : FM κ R (Option α)} {f : α → FM κ R (Option β)} {b : β}
    (hr : (bindO x f).run h = some (some b)) :
    ∃ a, x.run h = some (some a) ∧ (f a).run h = some (some b) := by
  rw [run_bindO] at hr
  obtain ⟨o, ho, hr⟩ := Option.bind_eq_some_iff.mp hr
  cases o with
  | none =>
    have hn : (some none : Option (Option β)) = some (some b) := hr
    cases hn
  | some a => exact ⟨a, ho, hr⟩

theorem optK_some_inv {κ : Type} {R : κ → Type} {α β : Type} {h : (c : κ) → Option (R c)}
    {o : Option α} {f : α → FM κ R (Option β)} {b : β}
    (hr : (optK o f).run h = some (some b)) : ∃ a, o = some a ∧ (f a).run h = some (some b) := by
  cases o with
  | none =>
    have hn : (some none : Option (Option β)) = some (some b) := hr
    cases hn
  | some a => exact ⟨a, rfl, hr⟩

theorem okO_run_inv {κ : Type} {R : κ → Type} {α : Type} {h : (c : κ) → Option (R c)}
    {a b : α} (hr : (okO a : FM κ R (Option α)).run h = some (some b)) : a = b := by
  have h' : (some (some a) : Option (Option α)) = some (some b) := hr
  exact Option.some.inj (Option.some.inj h')

theorem failO_run_inv {κ : Type} {R : κ → Type} {α : Type} {h : (c : κ) → Option (R c)}
    {b : α} (hr : (failO : FM κ R (Option α)).run h = some (some b)) : False := by
  have h' : (some none : Option (Option α)) = some (some b) := hr
  cases h'

theorem pure_run_inv {κ : Type} {R : κ → Type} {α : Type} {h : (c : κ) → Option (R c)}
    {a b : α} (hr : (FM.pure a : FM κ R α).run h = some b) : a = b := by
  rw [run_pure] at hr
  exact Option.some.inj hr

/-- An invariant of the folded state survives `foldO` (stops at the first
FAIL, like `foldlM`). -/
theorem foldO_inv {κ : Type} {R : κ → Type} {α σ : Type} {h : (c : κ) → Option (R c)}
    (P : σ → Prop) {f : σ → α → FM κ R (Option σ)}
    (hf : ∀ s a s', P s → (f s a).run h = some (some s') → P s') :
    ∀ (l : List α) (s s' : σ), P s → (foldO f s l).run h = some (some s') → P s'
  | [], s, s', hs, hr => by
    have hr' : (okO s : FM κ R (Option σ)).run h = some (some s') := hr
    cases okO_run_inv hr'
    exact hs
  | a :: l, s, s', hs, hr => by
    have hr' : (bindO (f s a) fun s1 => foldO f s1 l).run h = some (some s') := hr
    obtain ⟨s1, h1, h2⟩ := bindO_some_inv hr'
    exact foldO_inv P hf l s1 s' (hf s a s1 hs h1) h2

/-! ## The wrapper's calls keep `LenOk` (from `readF_good`) -/

section Calls
variable {senv : StructEnv} {n : Nat}

theorem wConv_lenOk {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead}
    {r : Lean.Expr} {st' : MachRead}
    (hr : (wConv env d e st).run (wtab senv n) = some (some (r, st'))) (hst : st.LenOk) :
    st'.LenOk :=
  readF_good senv n (Tools.ShippingReaderFuel.Call.conv env d e st) hst (r, st') hr

theorem wChain_lenOk {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} {st' : MachRead}
    (hr : (wChain env e st).run (wtab senv n) = some (some (ws, v, st'))) (hst : st.LenOk) :
    st'.LenOk :=
  readF_good senv n (Tools.ShippingReaderFuel.Call.chain env e st) hst (ws, v, st') hr

theorem wLoopRoot_lenOk {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    {mv : MachVal} {st' : MachRead}
    (hr : (wLoopRoot env e st).run (wtab senv n) = some (some (mv, st'))) (hst : st.LenOk) :
    st'.LenOk :=
  readF_good senv n (Tools.ShippingReaderFuel.Call.loopRoot env e st) hst (mv, st') hr

end Calls

/-! ## The pure prefix -/

/-- `shapePre` (5061–5072) succeeded: the constant is a definition, its value
peels to the recorded binders, its type reads the recorded output list. -/
theorem shapePre_facts {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {p : ShapePre} (h : shapePre sm ps ci senv = some p) :
    ci = .defnInfo p.d ∧
    mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs p.d.value) = some (p.bs, p.e) ∧
    declOuts? senv p.d.type = some (p.ctor?, p.outs) := by
  cases ci with
  | defnInfo d =>
    unfold shapePre at h
    try dsimp only at h
    replace h := ite_none_inv h
    obtain ⟨⟨bs, e⟩, hx, h⟩ := bind_inv h
    try dsimp only at h
    generalize hk : machTupleKinds? d.type = tup at h
    cases tup
    all_goals obtain ⟨⟨ctor?, outs⟩, ho, h⟩ := bind_inv h
    all_goals try dsimp only at h
    all_goals replace h := ite_none_inv h
    all_goals first
      | (have hp := Option.some.inj h; subst hp)
      | (injection h with hp; subst hp)
    all_goals refine ⟨rfl, hx, ?_⟩
    all_goals
      show declOuts? senv d.type = some (ctor?, outs)
      unfold declOuts?
      rw [hk]
      exact ho
  | _ =>
    first
      | cases h
      | (unfold shapePre at h; cases h)
      | (simp [shapePre] at h; done)

/-! ## The phases, with their states -/

section Phases
variable {senv : StructEnv} {n : Nat}

/-- **Initial → domain → reserve** (5097–5104): with no enclosing machine
the state is `{}`; otherwise the domain is converted from `{}` and
`machReserve` reserves the enclosing machine's slots in `{}`, giving `st0`. -/
theorem shapeStart_inv {m : ShapeMid} {st0 : MachRead}
    (hr : (shapeStart senv m).run (wtab senv n) = some (some st0)) :
    (m.run? = none ∧ st0 = ({} : MachRead)) ∨
    ∃ (dom αs initsE body dom' : Lean.Expr) (stc : MachRead) (base : Nat),
      m.run? = some (dom, αs, initsE, body) ∧
      machConvF n senv (m.rootLets.map fun _ => MachVal.unit) 0 dom ({} : MachRead) =
        some (some (dom', stc)) ∧
      machReserve senv.natOf dom' αs initsE body ({} : MachRead) = some (base, st0) := by
  unfold shapeStart at hr
  rcases hm : m.run? with _ | ⟨dom, αs, initsE, body⟩
  · rw [hm] at hr
    try dsimp only at hr
    exact Or.inl ⟨by first | rfl | exact hm, (okO_run_inv hr).symm⟩
  · rw [hm] at hr
    try dsimp only at hr
    obtain ⟨⟨dom', stc⟩, hc, hr⟩ := bindO_some_inv hr
    try dsimp only at hr
    obtain ⟨⟨base, st'⟩, hres, hr⟩ := optK_some_inv hr
    try dsimp only at hr
    have e := okO_run_inv hr
    subst e
    exact Or.inr ⟨dom, αs, initsE, body, dom', stc, base, by first | rfl | exact hm, hc, hres⟩

/-- The state after `shapeStart` is `LenOk`. -/
theorem shapeStart_lenOk {m : ShapeMid} {st0 : MachRead}
    (hr : (shapeStart senv m).run (wtab senv n) = some (some st0)) : st0.LenOk := by
  rcases shapeStart_inv hr with ⟨_, h0⟩ | ⟨_, _, _, _, _, _, _, _, _, hres⟩
  · rw [h0]
    exact lenOk_init
  · exact machReserve_lenOk_init hres

/-- One root `let` (5106–5120) keeps `LenOk` of the state. -/
theorem shapeRootLet_lenOk :
    ∀ (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr)
      (s' : List MachVal × MachRead),
      s.2.LenOk → (shapeRootLet senv s a).run (wtab senv n) = some (some s') → s'.2.LenOk := by
  rintro ⟨env, st⟩ ⟨nm, ty, v⟩ s' hst hr
  have hst' : st.LenOk := hst
  first
    | (simp only [shapeRootLet] at hr)
    | (unfold shapeRootLet at hr; try dsimp only at hr)
  split at hr
  · -- a `Signal.loop` root
    obtain ⟨⟨mv, st2⟩, hl, hr⟩ := bindO_some_inv hr
    have h2 : st2.LenOk := wLoopRoot_lenOk hl hst'
    try dsimp only at hr
    have e := okO_run_inv hr
    subst e
    exact h2
  · split at hr
    · -- an ordinary root `let`
      obtain ⟨⟨v', st2⟩, hc, hr⟩ := bindO_some_inv hr
      have h2 : st2.LenOk := wConv_lenOk hc hst'
      try dsimp only at hr
      revert hr
      first
        | (intro hr; have e := okO_run_inv hr; subst e; exact lenOk_lets h2 _)
        | (split <;> (intro hr; have e := okO_run_inv hr; subst e; exact lenOk_lets h2 _))
        | ((repeat' split) <;>
            (intro hr; have e := okO_run_inv hr; subst e; exact lenOk_lets h2 _))
    · exact (failO_run_inv hr).elim

/-- The state after the root-let fold is `LenOk`. -/
theorem rootLets_lenOk {l : List (Name × Lean.Expr × Lean.Expr)} {env env' : List MachVal}
    {st0 st1 : MachRead}
    (hr : (foldO (shapeRootLet senv) (env, st0) l).run (wtab senv n) = some (some (env', st1)))
    (h0 : st0.LenOk) : st1.LenOk :=
  foldO_inv (fun s : List MachVal × MachRead => s.2.LenOk)
    (shapeRootLet_lenOk (senv := senv) (n := n)) l (env, st0) (env', st1) h0 hr

/-- **Body** (5122–5131): the enclosing machine's chain, the state with the
chain's next-state expressions appended to `ws`; or the root expression's
conversion. -/
theorem shapeBody_inv {m : ShapeMid} {env : List MachVal} {st1 st : MachRead} {v : Lean.Expr}
    (hr : (shapeBody m env st1).run (wtab senv n) = some (some (st, v))) :
    (∃ (dom αs initsE body : Lean.Expr) (ws : List (Nat × Lean.Expr)) (v0 : Lean.Expr)
        (st2 : MachRead),
      m.run? = some (dom, αs, initsE, body) ∧
      machChainF n senv (MachVal.regs 0 :: env) body st1 = some (some (ws, v0, st2)) ∧
      st = { st2 with ws := st2.ws ++ ws.toArray }) ∨
    (m.run? = none ∧ machConvF n senv env 0 m.root st1 = some (some (v, st))) := by
  unfold shapeBody at hr
  rcases hm : m.run? with _ | ⟨dom, αs, initsE, body⟩
  · rw [hm] at hr
    try dsimp only at hr
    obtain ⟨⟨v0, st2⟩, hc, hr⟩ := bindO_some_inv hr
    try dsimp only at hr
    have e := okO_run_inv hr
    injection e with e1 e2
    subst e1
    subst e2
    exact Or.inr ⟨by first | rfl | exact hm, hc⟩
  · rw [hm] at hr
    try dsimp only at hr
    obtain ⟨⟨ws, v0, st2⟩, hc, hr⟩ := bindO_some_inv hr
    try dsimp only at hr
    have e := okO_run_inv hr
    injection e with e1 e2
    exact Or.inl ⟨dom, αs, initsE, body, ws, v0, st2, by first | rfl | exact hm, hc, e1.symm⟩

/-- The state after `shapeBody` is `LenOk`. -/
theorem shapeBody_lenOk {m : ShapeMid} {env : List MachVal} {st1 st : MachRead} {v : Lean.Expr}
    (hr : (shapeBody m env st1).run (wtab senv n) = some (some (st, v))) (h1 : st1.LenOk) :
    st.LenOk := by
  rcases shapeBody_inv hr with ⟨_, _, _, _, ws, v0, st2, _, hc, hst⟩ | ⟨_, hc⟩
  · rw [hst]
    exact lenOk_ws (machChainF_lenOk hc h1) _
  · exact machConvF_lenOk hc h1

end Phases

/-! ## The shape from the final state -/

/-- `shapePost` (5132–5185) succeeded: the shape is built from the FINAL
reader state `st` — slot binders `st.names.zip st.kinds`, slots from
`st.kinds` and `st.inits`. -/
theorem shapePost_decomp {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead}
    {v : Lean.Expr} {sp : MachineShape} (h : shapePost ai p m st v = some sp) :
    ∃ letB : List (Name × MixedGateBinder),
      sp.binders = p.bs ++ instBinders sp.insts ++ st.names.toList.zip st.kinds.toList ++ letB ∧
      sp.layout.slots = machSlotFields ((st.kinds.toList.map machWidth).zip st.inits.toList) ∧
      sp.layout.outs = machOutFields (st.kinds.toList.map machWidth).sum p.outs ∧
      sp.layout.lets = letB.length := by
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
    exact ⟨_, rfl, rfl, rfl, by first | exact (List.length_map ..).symm | simp⟩

/-! ## The whole wrapper, keeping the state -/

section Wrapper
variable {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
  {senv : StructEnv} {ai : Bool} {sp : MachineShape}

/-- **The phases of a successful candidate run, with every intermediate
state** (`st0` after start, `st1` after the root lets, `st` after the
body). -/
theorem machineShapeF_steps (h : machineShapeF n sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0)
          (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp := by
  unfold machineShapeF shapeW at h
  obtain ⟨p, hp, h⟩ := optK_some_inv h
  try dsimp only at h
  obtain ⟨en, hen, h⟩ := bind_some_inv h
  try dsimp only at h
  obtain ⟨st0, h0, h⟩ := bindO_some_inv h
  try dsimp only at h
  obtain ⟨⟨env, st1⟩, h1, h⟩ := bindO_some_inv h
  try dsimp only at h
  obtain ⟨⟨st, v⟩, h2, h⟩ := bindO_some_inv h
  try dsimp only at h
  exact ⟨p, en, st0, env, st1, st, v, hp, hen, h0, h1, h2, pure_run_inv h⟩

/-- **`LenOk` at every phase** of a successful candidate run, and the shape
built from the final state. -/
theorem machineShapeF_lenOk (h : machineShapeF n sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      st0.LenOk ∧ st1.LenOk ∧ st.LenOk ∧
      shapePost ai p (shapeMid senv p en) st v = some sp := by
  obtain ⟨p, en, st0, env, st1, st, v, hp, _, h0, h1, h2, h3⟩ := machineShapeF_steps h
  have l0 : st0.LenOk := shapeStart_lenOk h0
  have l1 : st1.LenOk := rootLets_lenOk h1 l0
  have l2 : st.LenOk := shapeBody_lenOk h2 l1
  exact ⟨p, en, st0, st1, st, v, hp, l0, l1, l2, h3⟩

/-- **The decomposition of every successful candidate result**, with the
reader state's lengths: the `ShapeDecomp` bundle of the old line, its
`names`, `kinds`, `inits` being the final state's arrays, of one length. -/
theorem machineShapeF_decomp (h : machineShapeF n sm ps ci senv ai = some (some sp)) :
    ∃ (d : DefinitionVal) (bs : List (Name × MixedGateBinder)) (e : Lean.Expr)
      (ctor? : Option Name) (outs : List (String × MixedGateBinder)) (names : List Name)
      (kinds : List MixedGateBinder) (inits : List Nat) (letB : List (Name × MixedGateBinder)),
      ci = .defnInfo d ∧ ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB ∧
      names.length = kinds.length ∧ inits.length = kinds.length := by
  obtain ⟨p, _, _, _, st, _, hp, _, _, hL, hpost⟩ := machineShapeF_lenOk h
  obtain ⟨hci, hpeel, hout⟩ := shapePre_facts hp
  obtain ⟨letB, hb, hs, ho, hl⟩ := shapePost_decomp hpost
  have n1 : st.names.toList.length = st.kinds.toList.length := by
    first
      | exact hL.names
      | (rw [Array.length_toList, Array.length_toList]; exact hL.names)
      | simp [hL.names]
  have n2 : st.inits.toList.length = st.kinds.toList.length := by
    first
      | exact hL.inits
      | (rw [Array.length_toList, Array.length_toList]; exact hL.inits)
      | simp [hL.inits]
  exact ⟨p.d, p.bs, p.e, p.ctor?, p.outs, st.names.toList, st.kinds.toList, st.inits.toList,
    letB, hci, ⟨hpeel, hout, hb, hs, ho, hl⟩, n1, n2⟩

/-- **R5 of every successful candidate result.** -/
theorem machineShapeF_r5 (h : machineShapeF n sm ps ci senv ai = some (some sp)) :
    ∃ (d : DefinitionVal) (bs : List (Name × MixedGateBinder)) (e : Lean.Expr)
      (ctor? : Option Name) (outs : List (String × MixedGateBinder)) (names : List Name)
      (kinds : List MixedGateBinder) (inits : List Nat) (letB : List (Name × MixedGateBinder)),
      ci = .defnInfo d ∧ ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB ∧
      (names.zip kinds).length = sp.layout.slots.length := by
  obtain ⟨d, bs, e, ctor?, outs, names, kinds, inits, letB, hci, D, hn, hi⟩ :=
    machineShapeF_decomp h
  exact ⟨d, bs, e, ctor?, outs, names, kinds, inits, letB, hci, D, D.r5_of_lengths hn hi⟩

end Wrapper

/-! ## The consumers' conditions, at a definition -/

section Defn
variable {n : Nat} {sm : Bool} {ps : List (String × Nat)} {d : DefinitionVal}
  {senv : StructEnv} {ai : Bool} {sp : MachineShape}

/-- The decomposition at the definition the wrapper was given. -/
theorem machineShapeF_decomp_defn
    (h : machineShapeF n sm ps (.defnInfo d) senv ai = some (some sp)) :
    ∃ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr)
      (ctor? : Option Name) (outs : List (String × MixedGateBinder)) (names : List Name)
      (kinds : List MixedGateBinder) (inits : List Nat) (letB : List (Name × MixedGateBinder)),
      ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB ∧
      names.length = kinds.length ∧ inits.length = kinds.length := by
  obtain ⟨d', bs, e, ctor?, outs, names, kinds, inits, letB, hci, D, hn, hi⟩ :=
    machineShapeF_decomp h
  injection hci with hd
  subst hd
  exact ⟨bs, e, ctor?, outs, names, kinds, inits, letB, D, hn, hi⟩

/-- **The binder count** (the generator's meta-level "binder count" check):
the shape's binders are the definition's peeled binders, one per call entry,
one per layout slot and one per `let`. -/
theorem machineShapeF_binderCount
    (h : machineShapeF n sm ps (.defnInfo d) senv ai = some (some sp)) :
    ∃ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
      sp.binders.length =
        bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets := by
  obtain ⟨bs, e, _, _, names, kinds, _, letB, D, hn, hi⟩ := machineShapeF_decomp_defn h
  have R5 := D.r5_of_lengths hn hi
  have hI : (instBinders sp.insts).length = sp.insts.length := instBinders_length _
  have hl : sp.layout.lets = letB.length := D.lets
  have hb : sp.binders.length =
      bs.length + (instBinders sp.insts).length + (names.zip kinds).length + letB.length := by
    rw [D.binders, List.length_append, List.length_append, List.length_append]
  exact ⟨bs, e, D.peel, by omega⟩

/-- **The closing's `nDecl` is the number of peeled binders** (no R5
hypothesis). -/
theorem machineShapeF_nDecl
    (h : machineShapeF n sm ps (.defnInfo d) senv ai = some (some sp)) :
    ∃ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
      sp.binders.length - sp.insts.length - sp.layout.slots.length - sp.layout.lets =
        bs.length := by
  obtain ⟨bs, e, _, _, _, _, _, _, D, hn, hi⟩ := machineShapeF_decomp_defn h
  exact ⟨bs, e, D.peel, D.nDecl (D.r5_of_lengths hn hi)⟩

/-- **R4 at the closing's position, R5 discharged**: the binder at the
closing's `nDecl + k` has call entry `k`'s kind. -/
theorem machineShapeF_callBinder
    (h : machineShapeF n sm ps (.defnInfo d) senv ai = some (some sp))
    {k : Nat} (hk : k < sp.insts.length) :
    (sp.binders.map (·.2))[(sp.binders.length - sp.insts.length - sp.layout.slots.length -
        sp.layout.lets) + k]? = (sp.insts.map (·.2.2))[k]? := by
  obtain ⟨_, _, _, _, _, _, _, _, D, hn, hi⟩ := machineShapeF_decomp_defn h
  exact D.callBinder (D.r5_of_lengths hn hi) hk

/-- **Slots vs. state**: the layout has one slot per kind of the final
state, and the slot binders (names) and reset values are as many. -/
theorem machineShapeF_slots_length
    (h : machineShapeF n sm ps (.defnInfo d) senv ai = some (some sp)) :
    ∃ (names : List Name) (kinds : List MixedGateBinder) (inits : List Nat),
      sp.layout.slots.length = kinds.length ∧ names.length = kinds.length ∧
      inits.length = kinds.length ∧
      sp.layout.slots = machSlotFields ((kinds.map machWidth).zip inits) := by
  obtain ⟨_, _, _, _, names, kinds, inits, _, D, hn, hi⟩ := machineShapeF_decomp_defn h
  refine ⟨names, kinds, inits, ?_, hn, hi, D.slots⟩
  rw [D.slots_length, hi, Nat.min_self]

/-- A one-Signal result kind: the candidate's layout is ONE output `out`
(pure part, as `ShapeDecomp.single_out`). -/
theorem machineShapeF_single_out
    (h : machineShapeF n sm ps (.defnInfo d) senv ai = some (some sp))
    {k : MixedGateBinder} (hres : machResultKind? d.type = some k) :
    ∃ kinds : List MixedGateBinder,
      sp.layout.outs = [{ name := "out", lo := (kinds.map machWidth).sum, width := machWidth k,
                          ty := machHWType k }] := by
  obtain ⟨_, _, _, _, _, kinds, _, _, D, _, _⟩ := machineShapeF_decomp_defn h
  exact ⟨kinds, D.single_out hres⟩

end Defn

end Tools.ShippingReaderFuelShapeR5

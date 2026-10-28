import Tools.Prototype.ReaderFixpointNorm
import Tools.ShippingReaderFuelShapeR5
import Tools.ShippingReaderFuelShapeR1
import Tools.ShippingReaderFuelShapeProv
import Tools.ShippingLetsReaderInvMain
import Tools.ShippingBundleIotaRange

/-! # Unit LC12 prototype: SPECIFICATION lemmas for the kernel-visible reader `machineShapeN`

BUILT: runs s1 (part 1), s5 (phases), s14 (main theorem), s15, s16 (final, with `machineShapeN_lets'`) all exit 0 (final = s16).  No sorry / axiom / native_decide.  Production
unchanged; `machineShapeN` is the prototype wrapper of LC11b (`shapeW` against `execNorm` + `execBlock`), NOT the
shipped `machineShape?`; `TwinCoverAt` and `machNorm = execNorm` stay OPEN.

## Part 1 (premise-free transfer)
Every property of a successful result that is PROVED for the fuel wrapper `machineShapeF` is a property of
`machineShapeN`, by `machineShapeN_fuel` (`machineShapeN … = some r → ∃ n, machineShapeF n … = some r`, LC11b).
The lemmas below are those transfers (layout / binder-count / slot / output widths, `ShapeDecomp`, call-entry
R1 and provenance, origin tags).  They add NOTHING that was not already proved for `machineShapeF`; their value
is that the subject is now the kernel-visible executable reader.

## Part 2 (new): the `let`-table properties of the result
`machineShapeN_lets` (conditional on `ShapeInOk`, the wrapper-level form of LC3's INPUT condition `LetOk 0`, and
on the five named premises of LC3/LC5) — the final reader state `st` of any successful run has an alias-free
`let` table (`NoLetAlias st.lets`, the Expr-level half of `letsAliasOk`) and `st` is a `RdOk` state in which the
body value `v` is in range (`LetOk st.lets.size v`), and the shape is `shapePost … st v`.  See the docstring there
for the exact input condition and the one field (`startDom`) that is a genuine gap of the invariant. -/
namespace Tools.Prototype.ReaderExec
open Lean Sparkle.Compiler.Elab Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv
open Tools.ShippingLetsAliasInv Tools.ShippingReaderFuelShapeR5 Tools.ShippingReaderLenOk
open Tools.ShippingShapeDecomp Tools.ShippingReaderFuelProv Tools.ShippingReaderFuelShapeProv

/-! ## Part 1: transfers from `machineShapeF` -/

section Transfer
variable {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {senv : StructEnv}
  {ai : Bool} {sp : MachineShape}

/-- The phases of a successful run (executable reader), with every intermediate state, at ONE common fuel. -/
theorem machineShapeN_steps (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0)
          (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp := by
  obtain ⟨n, hn⟩ := machineShapeN_fuel h
  obtain ⟨p, en, st0, env, st1, st, v, h1, h2, h3, h4, h5, h6⟩ := machineShapeF_steps hn
  exact ⟨n, p, en, st0, env, st1, st, v, h1, h2, h3, h4, h5, h6⟩

theorem machineShapeN_lenOk (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      st0.LenOk ∧ st1.LenOk ∧ st.LenOk ∧
      shapePost ai p (shapeMid senv p en) st v = some sp :=
  machineShapeF_lenOk (machineShapeN_fuel h).choose_spec

theorem machineShapeN_origins_aligned (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    sp.instOrigins.length = sp.insts.length :=
  machineShapeF_origins_aligned (machineShapeN_fuel h).choose_spec

theorem machineShapeN_decomp (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (d : DefinitionVal) (bs : List (Name × MixedGateBinder)) (e : Lean.Expr)
      (ctor? : Option Name) (outs : List (String × MixedGateBinder)) (names : List Name)
      (kinds : List MixedGateBinder) (inits : List Nat) (letB : List (Name × MixedGateBinder)),
      ci = .defnInfo d ∧ ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB ∧
      names.length = kinds.length ∧ inits.length = kinds.length :=
  machineShapeF_decomp (machineShapeN_fuel h).choose_spec

theorem machineShapeN_r5 (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (d : DefinitionVal) (bs : List (Name × MixedGateBinder)) (e : Lean.Expr)
      (ctor? : Option Name) (outs : List (String × MixedGateBinder)) (names : List Name)
      (kinds : List MixedGateBinder) (inits : List Nat) (letB : List (Name × MixedGateBinder)),
      ci = .defnInfo d ∧ ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB ∧
      (names.zip kinds).length = sp.layout.slots.length :=
  machineShapeF_r5 (machineShapeN_fuel h).choose_spec

section Defn
variable {d : DefinitionVal}

/-- Binder count of the shape: declared inputs + call entries + slots + lets. -/
theorem machineShapeN_binderCount (h : machineShapeN sm ps (.defnInfo d) senv ai = some (some sp)) :
    ∃ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
      sp.binders.length =
        bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets :=
  machineShapeF_binderCount (machineShapeN_fuel h).choose_spec

theorem machineShapeN_nDecl (h : machineShapeN sm ps (.defnInfo d) senv ai = some (some sp)) :
    ∃ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
      sp.binders.length - sp.insts.length - sp.layout.slots.length - sp.layout.lets =
        bs.length :=
  machineShapeF_nDecl (machineShapeN_fuel h).choose_spec

/-- The binder at a call entry's position carries the entry's result kind (`PB`-type fact). -/
theorem machineShapeN_callBinder (h : machineShapeN sm ps (.defnInfo d) senv ai = some (some sp))
    {k : Nat} (hk : k < sp.insts.length) :
    (sp.binders.map (·.2))[(sp.binders.length - sp.insts.length - sp.layout.slots.length -
        sp.layout.lets) + k]? = (sp.insts.map (·.2.2))[k]? :=
  machineShapeF_callBinder (machineShapeN_fuel h).choose_spec hk

theorem machineShapeN_slots_length (h : machineShapeN sm ps (.defnInfo d) senv ai = some (some sp)) :
    ∃ (names : List Name) (kinds : List MixedGateBinder) (inits : List Nat),
      sp.layout.slots.length = kinds.length ∧ names.length = kinds.length ∧
      inits.length = kinds.length ∧
      sp.layout.slots = machSlotFields ((kinds.map machWidth).zip inits) :=
  machineShapeF_slots_length (machineShapeN_fuel h).choose_spec

theorem machineShapeN_single_out (h : machineShapeN sm ps (.defnInfo d) senv ai = some (some sp))
    {k : MixedGateBinder} (hres : machResultKind? d.type = some k) :
    ∃ kinds : List MixedGateBinder,
      sp.layout.outs = [{ name := "out", lo := (kinds.map machWidth).sum, width := machWidth k,
                          ty := machHWType k }] :=
  machineShapeF_single_out (machineShapeN_fuel h).choose_spec hres

end Defn

/-- Call-entry provenance (per index). -/
theorem machineShapeN_origin (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder),
      sp.insts[k]? = some e → OriginAt senv e sp.instFields[k]? :=
  machineShapeF_origin (machineShapeN_fuel h).choose_spec

theorem machineShapeN_origin_mem (h : machineShapeN sm ps ci senv ai = some (some sp))
    {e : Name × List Nat × MixedGateBinder} (he : e ∈ sp.insts) :
    OrdOrigin senv e.1 e.2.2 ∨ (∃ nm : String, StructOrigin senv e.1 e.2.2 nm) ∨
      MemOrigin e.1 e.2.2 :=
  machineShapeF_origin_mem (machineShapeN_fuel h).choose_spec he

theorem machineShapeN_originT (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder)
      (o : Sparkle.Compiler.MachInstOrigin.InstOrigin),
      sp.insts[k]? = some e → sp.instOrigins[k]? = some o →
        OriginTAt senv e sp.instFields[k]? o :=
  machineShapeF_originT (machineShapeN_fuel h).choose_spec

theorem machineShapeN_tag_exists (h : machineShapeN sm ps ci senv ai = some (some sp))
    {k : Nat} {e : Name × List Nat × MixedGateBinder} (hk : sp.insts[k]? = some e) :
    ∃ o, sp.instOrigins[k]? = some o :=
  machineShapeF_tag_exists (machineShapeN_fuel h).choose_spec hk

/-- Call-entry R1: a reader-produced entry's result kind is its callee's declared result kind. -/
theorem machineShapeN_instR1 (hM : Tools.ShippingReaderFuelR1.MemR1 senv)
    (hD : Tools.ShippingReaderFuelR1.SigDisj senv)
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∀ (c : Name) (js : List Nat) (r : MixedGateBinder), (c, js, r) ∈ sp.insts →
      ∀ (kinds : List MixedGateBinder) (r' : MixedGateBinder),
        senv.inst c = some (kinds, r') → r = r' :=
  Tools.ShippingReaderFuelShapeR1.machineShapeF_instR1 hM hD (machineShapeN_fuel h).choose_spec

/-- **Refusal side** (premise-free): a refusal in the pure prefix (`shapePre`: not a definition, symbolic mode,
parameters, binders, outputs) is the ordinary refusal `some none` of the executable reader. -/
theorem machineShapeN_of_pre_none (hpre : shapePre sm ps ci senv = none) :
    machineShapeN sm ps ci senv ai = some none :=
  machineShapeN_iff_fuel.mpr ⟨0, machineShapeF_of_pre_none 0 hpre⟩

/-- A success has passed the pure prefix `shapePre`. -/
theorem machineShapeN_pre_some_of_ok (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ p, shapePre sm ps ci senv = some p := by
  obtain ⟨_, p, _, _, _, _, _, _, hp, _⟩ := machineShapeN_steps h
  exact ⟨p, hp⟩

end Transfer

/-! ## Part 2: the `let` table of the result -/

section Lets
open Tools.ShippingReaderLenOk

variable {senv : StructEnv} (hroot : RootFloatRange) (hlift : LiftRange) (hinst1 : Inst1Range)
  (hsig : SigTyRange senv) (hbundle : BundleIotaRange)
include hroot hlift hinst1 hsig hbundle

omit hroot hlift hinst1 hsig hbundle in
/-- The root-`let` bind of `shapeRootLet`: alias-free table, not shorter, bound value in range. -/
theorem rootBind_facts {nm : Name} {ty v' : Lean.Expr} {lets : MachLets} {c : Bool}
    (H : NoLetAlias lets) (hv : LetOk lets.size v' = true) (hc : c = true → machIsSlot v' = true) :
    NoLetAlias (if c = true then machBindLetNamed nm ty v' lets else machBindLet nm ty v' lets).2 ∧
    lets.size ≤ (if c = true then machBindLetNamed nm ty v' lets else machBindLet nm ty v' lets).2.size ∧
    LetOk (if c = true then machBindLetNamed nm ty v' lets else machBindLet nm ty v' lets).2.size
      (if c = true then machBindLetNamed nm ty v' lets else machBindLet nm ty v' lets).1 = true := by
  by_cases h : c = true
  · rw [if_pos h]
    exact ⟨machBindLetNamed_noAlias H (slot_not_letVar (hc h)), (machBindLetNamed_range hv).1,
      (machBindLetNamed_range hv).2⟩
  · rw [if_neg h]
    exact ⟨machBindLet_noAlias H, (machBindLet_range hv).1, (machBindLet_range hv).2⟩

omit hroot hlift hinst1 hsig hbundle in
theorem shapeStart_ok {n : Nat} {m : ShapeMid} {st0 : MachRead}
    (hs : ∀ dom αs initsE body dom' stc, m.run? = some (dom, αs, initsE, body) →
      machConvF n senv (m.rootLets.map fun _ => MachVal.unit) 0 dom ({} : MachRead) =
        some (some (dom', stc)) → LetOk 0 dom' = true)
    (hr : (shapeStart senv m).run (wtab senv n) = some (some st0)) : RdOk st0 := by
  rcases shapeStart_inv hr with ⟨_, h0⟩ | ⟨dom, αs, initsE, body, dom', stc, base, hm, hc, hres⟩
  · rw [h0]; exact rdOk_init
  · obtain ⟨kinds, inits, _, _, _, hst⟩ := machReserve_some hres
    subst hst
    exact rdOk_dom (rdOk_init) (by rfl) (by rfl) (d := dom') (by rfl)
      (letOk_zero (hs dom αs initsE body dom' stc hm hc))

theorem shapeRootLet_ok {n : Nat} (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr)
    (s' : List MachVal × MachRead) (hs : RdOk s.2 ∧ EnvOk s.2.lets.size s.1)
    (ha : LetOk 0 a.2.2 = true)
    (hr : (shapeRootLet senv s a).run (wtab senv n) = some (some s')) :
    RdOk s'.2 ∧ EnvOk s'.2.lets.size s'.1 ∧ s.2.lets.size ≤ s'.2.lets.size := by
  obtain ⟨env, st⟩ := s
  obtain ⟨nm, ty, v⟩ := a
  obtain ⟨hst, hE⟩ := hs
  have hl : LetOk 0 v = true := ha
  first
    | (simp only [shapeRootLet] at hr)
    | (unfold shapeRootLet at hr; try dsimp only at hr)
  split at hr
  · obtain ⟨⟨mv, st2⟩, hl2, hr⟩ := bindO_some_inv hr
    have hp := machLoopRootF_post hroot hlift hinst1 hsig hbundle hst hE hl hl2
    try dsimp only at hr
    have e := okO_run_inv hr
    subst e
    exact ⟨hp.1, envOk_cons (envOk_mono hp.2.1 hE) (fun w hw => by subst hw; exact hp.2.2), hp.2.1⟩
  · split at hr
    · obtain ⟨⟨v', st2⟩, hc, hr⟩ := bindO_some_inv hr
      have hp := machConvF_post hroot hlift hinst1 hsig hbundle hst hE hl hc
      try dsimp only at hr
      have e := okO_run_inv hr
      subst e
      have hv'' : LetOk st2.lets.size v' = true := hp.2.2
      have hF := rootBind_facts (nm := nm) (ty := ty) (c := (!st2.loops.isEmpty && machIsSlot v'))
        hp.1.1 hv'' (fun h => by
          have := (Bool.and_eq_true _ _).mp h
          exact this.2)
      generalize (if (!st2.loops.isEmpty && machIsSlot v') = true then machBindLetNamed nm ty v' st2.lets
        else machBindLet nm ty v' st2.lets) = bl at hF ⊢
      obtain ⟨x, lets'⟩ := bl
      have hA : RdOk { st2 with lets := lets' } := rdOk_lets hp.1 hF.1 hF.2.1 (by rfl) (by rfl)
      refine ⟨hA, ?_, Nat.le_trans hp.2.1 hF.2.1⟩
      exact envOk_cons (envOk_mono (Nat.le_trans hp.2.1 hF.2.1) hE)
        (fun w hw => by injection hw with hw; subst hw; exact hF.2.2)
    · exact (failO_run_inv hr).elim

omit hroot hlift hinst1 hsig hbundle in
/-- `foldO` with an invariant that needs a side condition on the list elements only. -/
theorem foldO_inv_mem {κ : Type} {R : κ → Type} {α σ : Type} {h : (c : κ) → Option (R c)}
    (P : σ → Prop) (Q : α → Prop) {f : σ → α → FM κ R (Option σ)}
    (hf : ∀ s a s', Q a → P s → (f s a).run h = some (some s') → P s') :
    ∀ (l : List α) (s s' : σ), (∀ a ∈ l, Q a) → P s → (foldO f s l).run h = some (some s') → P s'
  | [], s, s', _, hs, hr => by
    have hr' : (okO s : FM κ R (Option σ)).run h = some (some s') := hr
    cases okO_run_inv hr'
    exact hs
  | a :: l, s, s', hQ, hs, hr => by
    have hr' : (bindO (f s a) fun s1 => foldO f s1 l).run h = some (some s') := hr
    obtain ⟨s1, h1, h2⟩ := bindO_some_inv hr'
    exact foldO_inv_mem P Q hf l s1 s' (fun x hx => hQ x (List.mem_cons_of_mem _ hx))
      (hf s a s1 (hQ a List.mem_cons_self) hs h1) h2

theorem rootLets_ok {n : Nat} {l : List (Name × Lean.Expr × Lean.Expr)} {env env' : List MachVal}
    {st0 st1 : MachRead} (hl : ∀ x ∈ l, LetOk 0 x.2.2 = true) (h0 : RdOk st0)
    (hr : (foldO (shapeRootLet senv) (env, st0) l).run (wtab senv n) = some (some (env', st1)))
    (hE : EnvOk st0.lets.size env) : RdOk st1 ∧ EnvOk st1.lets.size env' := by
  have := foldO_inv_mem (h := wtab senv n) (fun s : List MachVal × MachRead =>
      RdOk s.2 ∧ EnvOk s.2.lets.size s.1) (fun a : Name × Lean.Expr × Lean.Expr => LetOk 0 a.2.2 = true)
    (f := shapeRootLet senv)
    (fun s a s' ha hs hr => by
      have := shapeRootLet_ok hroot hlift hinst1 hsig hbundle s a s' hs ha hr
      exact ⟨this.1, this.2.1⟩) l (env, st0) (env', st1) hl ⟨h0, hE⟩ hr
  exact this

theorem shapeBody_ok {n : Nat} {m : ShapeMid} {env : List MachVal} {st1 st : MachRead}
    {v : Lean.Expr} (hs : RdOk st1) (hE : EnvOk st1.lets.size env)
    (hr0 : LetOk 0 m.root = true)
    (hbody : ∀ dom αs initsE body, m.run? = some (dom, αs, initsE, body) → LetOk 0 body = true)
    (hwrap : ∀ c params, m.wrap? = some (c, params) →
      LetOk 0 c = true ∧ ∀ x ∈ params, LetOk 0 x = true)
    (hr : (shapeBody m env st1).run (wtab senv n) = some (some (st, v))) :
    RdOk st ∧ st1.lets.size ≤ st.lets.size ∧ LetOk st.lets.size v = true := by
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
    exact machConvF_post hroot hlift hinst1 hsig hbundle hs hE hr0 hc
  · rw [hm] at hr
    try dsimp only at hr
    obtain ⟨⟨ws, v0, st2⟩, hc, hr⟩ := bindO_some_inv hr
    try dsimp only at hr
    have e := okO_run_inv hr
    injection e with e1 e2
    have hp := machChainF_post hroot hlift hinst1 hsig hbundle hs
      (envOk_cons hE (fun w hw => by cases hw)) (hbody dom αs initsE body hm) hc
    subst e1
    refine ⟨rdOk_congr hp.1 (by rfl) (by rfl) (by rfl), hp.2.1, ?_⟩
    rw [← e2]
    cases hw : m.wrap? with
    | none => exact hp.2.2
    | some cp =>
      obtain ⟨c, params⟩ := cp
      obtain ⟨hc0, hps⟩ := hwrap c params hw
      show LetOk st2.lets.size (mkAppN c (params.push v0)) = true
      refine ok_mkAppN (letOk_zero hc0) ?_
      intro a ha
      rcases Array.mem_push.mp ha with ha | ha
      · exact letOk_zero (hps a ha)
      · rw [ha]; exact hp.2.2

omit hroot hlift hinst1 hsig hbundle in
theorem array_mem_of_mem_pop {a : Array Lean.Expr} {x : Lean.Expr} (h : x ∈ a.pop) : x ∈ a := by
  rw [← Array.mem_toList_iff] at h ⊢
  rw [Array.toList_pop] at h
  exact List.dropLast_subset _ h

omit hroot hlift hinst1 hsig hbundle in
/-- The wrapper `(c, params)` of `shapeMid` is the head and the arguments of the root. -/
theorem shapeMid_wrap_ok (senv : StructEnv) (p : ShapePre) (en : Lean.Expr)
    (hr : LetOk 0 (shapeMid senv p en).root = true) :
    ∀ c params, (shapeMid senv p en).wrap? = some (c, params) →
      LetOk 0 c = true ∧ ∀ x ∈ params, LetOk 0 x = true := by
  intro c params h
  unfold shapeMid at hr h
  dsimp only at hr h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  all_goals
    have e := Option.some.inj h
    injection e with e1 e2
    subst e1
    subst e2
    exact ⟨ok_getAppFn hr, fun x hx => ok_getAppArgs hr x (array_mem_of_mem_pop hx)⟩

/-- **INPUT condition of the let-table specification** (the wrapper-level form of LC3's entry condition `LetOk 0`
and of the start environment).  `m` is `shapeMid senv p en` for the normalised body `en`.
* `rootLets`, `root`, `runBody`: the values the reader is handed (NOT YET DERIVED from `LetOk 0 p.e`: `rootFloat`
  (MachRawSurface.lean:198) is a `partial def`; `machRoot` (Elab.lean:4412), `zeroLit` (MachRawSurface.lean:211), `inlFoldNat`
  (Elab.lean:3290) and `machLoopAsLet` (Elab.lean:5019) are TOTAL `def`s whose `LetOk` preservation has not been proved yet;
  the range of `machNorm`'s output is unknown).  The wrapper
  `(c, params)` is NOT an input: `shapeMid_wrap_ok` derives it from `root`.
* `startDom`: **a genuine gap of LC3's invariant, not a convenience.**  With an enclosing machine the wrapper
  converts the domain from `{}` and DISCARDS that state (`shapeStart`: `bindO (wConv … dom {}) fun (dom', _) …`), then
  reserves in `{}` with `dom := some dom'`.  `RdOk {…, dom := some dom'}` needs `LetOk 0 dom'`, but the conversion only
  gives `LetOk (discarded state).lets.size dom'`.  If the conversion of the domain bound a `let`, `dom'` could mention a
  placeholder `j ≥ 0` the reserved state does not have (a dangling placeholder; reachability NOT shown, NOT excluded). -/
structure ShapeInOk (senv : StructEnv) (m : ShapeMid) : Prop where
  rootLets : ∀ x ∈ m.rootLets, LetOk 0 x.2.2 = true
  root : LetOk 0 m.root = true
  runBody : ∀ dom αs initsE body, m.run? = some (dom, αs, initsE, body) → LetOk 0 body = true
  startDom : ∀ n dom αs initsE body dom' stc, m.run? = some (dom, αs, initsE, body) →
    machConvF n senv (m.rootLets.map fun _ => MachVal.unit) 0 dom ({} : MachRead) =
      some (some (dom', stc)) → LetOk 0 dom' = true

/-- **SPECIFICATION of the `let` table of the executable reader's result** (PROVED, conditional on the named
premises of LC3/LC5 and on the input condition `ShapeInOk`).  If `machineShapeN … = some (some sp)` then the shape is
`shapePost` of a final reader state `st` and body value `v` such that the `let` table of `st` is alias-free (the
Expr-level half of `letsAliasOk`: no `let` value is a `_machLet` placeholder), `st` satisfies the full invariant
`RdOk` and `v` is in range of `st.lets`.  This is the wrapper-level, executable-reader form of LC3's
`machConvF_post`/`_init''`; it says nothing about the shipped reader (needs `machNorm = execNorm` and `TwinCoverAt`)
and nothing about the typed `letFields` (the `quote` link stays OPEN). -/
theorem machineShapeN_lets {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool}
    {sp : MachineShape}
    (hin : ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p →
      execNorm senv p.e = some en → ShapeInOk senv (shapeMid senv p en))
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp := by
  obtain ⟨n, p, en, st0, env, st1, st, v, hp, hen, h0, h1, h2, h3⟩ := machineShapeN_steps h
  have hI := hin p en hp ((execNorm_iff senv).mpr ⟨n, hen⟩)
  have r0 : RdOk st0 := shapeStart_ok (n := n) (fun dom αs initsE body dom' stc hm hc =>
    hI.startDom n dom αs initsE body dom' stc hm hc) h0
  have r1 := rootLets_ok hroot hlift hinst1 hsig hbundle hI.rootLets r0 h1
    (fun v hv => by cases hv)
  have r2 := shapeBody_ok hroot hlift hinst1 hsig hbundle r1.1 r1.2 hI.root hI.runBody
    (shapeMid_wrap_ok senv p en hI.root) h2
  exact ⟨p, en, st, v, hp, (execNorm_iff senv).mpr ⟨n, hen⟩, r2.1, r2.1.1, r2.2.2, h3⟩

omit hbundle in
/-- `machineShapeN_lets` with `BundleIotaRange` discharged by LC4a's `bundleIotaRange` (PROVED): four premises
remain (`RootFloatRange`, `LiftRange`, `Inst1Range`, `SigTyRange senv`) plus the input condition `ShapeInOk`.
(Integrator fix, par/int-r30: the section's `include … hbundle` had inserted an UNUSED `BundleIotaRange` binder into
this signature; `omit hbundle in` removes it, and the binder audit below THROWS if it comes back.) -/
theorem machineShapeN_lets' {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool}
    {sp : MachineShape}
    (hin : ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p →
      execNorm senv p.e = some en → ShapeInOk senv (shapeMid senv p en))
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp :=
  machineShapeN_lets hroot hlift hinst1 hsig Tools.ShippingLetsReaderInv.bundleIotaRange hin h

end Lets

/-! ## Binder-type audit (THROWS; integrator, par/int-r30)
The Prop hypotheses of each audited theorem, by the head constant of their conclusion, must be exactly the listed
ones, in order. Guards against `include` silently adding unused premises (it had added `BundleIotaRange` to
`machineShapeN_lets'`). SCOPE: it checks ONLY the last name component of the head constant of each OUTER Prop
hypothesis; it does NOT check full hypothesis types, nor anything inside the conclusion (e.g. the `NoLetBvar st.lets →`,
`d.ok`, `hbody` antecedents of `machineShapeN_typed`'s conclusion). -/

open Lean Meta in
/-- Head constants (last name component) of the conclusions of the Prop hypotheses of `n`, in binder order. -/
def propBinderHeads (n : Name) : MetaM (List String) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => do
    let mut out : Array String := #[]
    for x in xs do
      let t ← inferType x
      if ← isProp t then
        out := out.push (match t.getForallBody.getAppFn.constName? with
          | some c => c.components.getLast!.toString
          | none => "?")
    return out.toList

open Lean Meta in
/-- THROWS unless the Prop hypotheses of `n` are exactly `expected`. -/
def auditPropBinders (n : Name) (expected : List String) : MetaM Unit := do
  let hs ← propBinderHeads n
  unless hs == expected do
    throwError "BINDER AUDIT FAILED: {n}: Prop hypotheses {hs}, expected exactly {expected}"
  logInfo m!"binder audit {n}: {hs}"

run_meta (auditPropBinders ``machineShapeN_lets
  ["RootFloatRange", "LiftRange", "Inst1Range", "SigTyRange", "BundleIotaRange", "ShapeInOk", "Eq"])
run_meta (auditPropBinders ``machineShapeN_lets'
  ["RootFloatRange", "LiftRange", "Inst1Range", "SigTyRange", "ShapeInOk", "Eq"])

#print axioms machineShapeN_steps
#print axioms machineShapeN_binderCount
#print axioms machineShapeN_originT
#print axioms machineShapeN_instR1
#print axioms machineShapeN_lets
#print axioms shapeMid_wrap_ok
#print axioms machineShapeN_lets'
#print axioms machineShapeN_of_pre_none

end Tools.Prototype.ReaderExec

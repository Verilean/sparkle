import Tools.VedU2HierStep

/-!
# `U2HRStmtK`: the hierarchical statement for children with k ≥ 1 outputs (CANDIDATE, not reviewed)

`U2HRStmt` (Tools/VedU2HierReg.lean) is unchanged and is false for a design with a child that has
two or more outputs, because `HierShapeS` -> `connsOkS` contains `c.outputs.length == 1`.  This file
adds a SEPARATE statement for the wider shape (user decision 2026-11-23, option 3).

* `connsOkK` is `connsOkS` with `c.outputs.length == 1` replaced by `1 ≤ c.outputs.length`, plus two
  clauses that are trivial for one output: the child's output port names are pairwise distinct, and
  the parent wires the child's outputs are connected to are pairwise distinct.
  NO OUTPUT IS DROPPED: the clause `(c.inputs ++ c.outputs).all (fun p => cs.any (· .1 == p.name))`
  (already in `connsOkS`) requires every input AND every output port to be connected, the clause
  `cs.all (… .ref x …)` requires each connection to be a plain wire, and its width test requires
  `declWidth m x == p.ty.bitWidth` (each output wire has the width of its port).
* `HierShapeK` is `HierShapeS` with `connsOkK` (every other clause is the same).
* `U2HRStmtK` is `U2HRStmt` with `HierShapeS d m = true` replaced by `HierShapeK d m = true`; every
  other conjunct is the SAME definition (`CorrStmt`, `ShapeCore`, `designClkRst`, `WidthStmt`,
  `OrderHS`, `OrderStmt`, `AdmArr`, `OutputsStmtHS`), none of which mentions the number of a child's
  outputs: the semantics (`instEvalS`, `outWrites`, `instOuts`/`wrH`) already writes EVERY connected
  output port (`outWrites` filters the connections on all output ports; the order check writes all
  output refs, so a parent wire written by two outputs / instances is refused by `WOH`).
-/

namespace Tools.VedU2Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier

/-- The parent wires the child's output ports are connected to (a connection of an output port to
anything but a plain wire is refused by `connsOkK`). -/
def outRefNames (c : Module) (cs : List (String × Expr)) : List String :=
  (cs.filter (fun q => c.outputs.any (·.name == q.1))).filterMap fun q =>
    match q.2 with
    | .ref x => some x
    | _ => none

/-- One `inst` against the design, k ≥ 1 outputs: `connsOkS` with `c.outputs.length == 1` replaced
by `1 ≤ c.outputs.length`, distinct output port names and distinct output wires added. -/
def connsOkK (d : Design) (m : Module) (mn : String) (cs : List (String × Expr)) : Bool :=
  match findMod d mn with
  | none => false
  | some c =>
    !c.isPrimitive && c.parameters.isEmpty && c.assertions.isEmpty && leafBody c.body &&
    childSane c &&
    decide (1 ≤ c.outputs.length) && decide (c.outputs.map (·.name)).Nodup &&
    decide (outRefNames c cs).Nodup &&
    decide (cs.map (·.1)).Nodup &&
    (c.inputs ++ c.outputs).all (fun p => cs.any (fun q => q.1 == p.name)) &&
    cs.all (fun q => (c.inputs ++ c.outputs).any (fun p => p.name == q.1)) &&
    cs.all (fun q => match q.2 with
      | .ref x => (c.inputs ++ c.outputs).any
          (fun p => p.name == q.1 && scalar p.ty &&
            (declWidth m x == p.ty.bitWidth || isClkRstPort c p.name))
      | _ => false)

/-- `HierShapeS` with `connsOkK`. -/
def HierShapeK (d : Design) (m : Module) : Bool :=
  d.topModule == m.name && decide (d.modules.map (·.name)).Nodup &&
  !((d.modules.map (·.name)).contains m.name) &&
  m.body.all isAsgInstReg &&
  m.body.all (fun s => match s with
    | .inst mn _ cs => connsOkK d m mn cs
    | _ => true) &&
  decide (instNames m.body).Nodup &&
  d.modules.all (fun c => m.body.any (fun s => match s with
    | .inst mn _ _ => mn == c.name
    | _ => false)) &&
  clkRstOk d m

/-- CANDIDATE statement for a parent with registers whose children have one or more outputs:
`U2HRStmt` with `HierShapeS d m = true` replaced by `HierShapeK d m = true`. -/
def U2HRStmtK (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  CorrStmt c ∧ ShapeCore c m ∧ c.clkRst = designClkRst d m ∧ HierShapeK d m = true ∧
  WidthStmt c m ∧ OrderHS d m ∧ (∀ x ∈ d.modules, OrderStmt x) ∧
  (∃ arr, AdmArr d m arr) ∧ OutputsStmtHS c m d f

/-! ## Coincidence with `U2HRStmt` -/

theorem filter_key_le_one {α : Type} (l : List (String × α)) (a : String)
    (h : (l.map Prod.fst).Nodup) : (l.filter (fun q => q.1 == a)).length ≤ 1 := by
  have hn : ((l.filter (fun q => q.1 == a)).map Prod.fst).Nodup :=
    h.sublist ((List.filter_sublist).map _)
  have hall : ∀ q ∈ l.filter (fun q => q.1 == a), q.1 = a := by
    intro q hq; simpa using (List.mem_filter.mp hq).2
  generalize l.filter (fun q => q.1 == a) = r at hn hall
  match r, hn, hall with
  | [], _, _ => simp
  | [_], _, _ => simp
  | x :: y :: t, hn, hall =>
    exfalso
    have h1 := hall x (by simp)
    have h2 := hall y (by simp)
    simp at hn
    exact hn.1.1 (h1.trans h2.symm)

/-- `connsOkS` gives `connsOkK` (a single output: the two added clauses are trivial). -/
theorem connsOkK_of_S {d : Design} {m : Module} {mn : String} {cs : List (String × Expr)}
    (h : connsOkS d m mn cs = true) : connsOkK d m mn cs = true := by
  obtain ⟨c, hf, _, _, _, _, hol, hcsnd, _⟩ := connsOkS_facts h
  have hs := h
  simp only [connsOkS, hf] at hs
  simp only [connsOkK, hf]
  have hn : (c.outputs.map (·.name)).Nodup := by
    match hc : c.outputs, hol with
    | [_], _ => simp
  have hr : (outRefNames c cs).Nodup := by
    unfold outRefNames
    obtain ⟨o, ho⟩ : ∃ o, c.outputs = [o] := by
      match hc : c.outputs, hol with
      | [o], _ => exact ⟨o, rfl⟩
    have hle := filter_key_le_one cs o.name hcsnd
    have hfe : (cs.filter (fun q => c.outputs.any (·.name == q.1))) = cs.filter (fun q => q.1 == o.name) := by
      apply List.filter_congr; intro q _; simp only [ho, List.any_cons, List.any_nil, Bool.or_false]; rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩
    rw [hfe]
    generalize cs.filter (fun q => q.1 == o.name) = r at hle
    have : (r.filterMap fun q => match q.2 with | .ref x => some x | _ => none).length ≤ 1 :=
      Nat.le_trans (List.length_filterMap_le _ _) hle
    generalize (r.filterMap fun q => match q.2 with | .ref x => some x | _ => none) = z at this
    match z, this with
    | [], _ => simp
    | [_], _ => simp
    | _ :: _ :: _, h => simp at h
  have hl : 1 ≤ c.outputs.length := by omega
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq, and_assoc] at hs ⊢
  obtain ⟨a1, a2, a3, a4, a5, _, a7, a8, a9, a10⟩ := hs
  exact ⟨a1, a2, a3, a4, a5, hl, hn, hr, a7, a8, a9, a10⟩

/-- Conversely, when the resolved child has exactly one output, `connsOkK` gives `connsOkS`. -/
theorem connsOkS_of_K {d : Design} {m : Module} {mn : String} {cs : List (String × Expr)}
    (h1 : ∀ x ∈ d.modules, x.outputs.length = 1) (h : connsOkK d m mn cs = true) :
    connsOkS d m mn cs = true := by
  simp only [connsOkK] at h
  cases hf : findMod d mn with
  | none => simp [hf] at h
  | some c =>
    have hl := h1 c (findMod_mem hf)
    simp only [hf] at h
    simp only [connsOkS, hf]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq, and_assoc] at h ⊢
    obtain ⟨a1, a2, a3, a4, a5, _, _, _, a7, a8, a9, a10⟩ := h
    exact ⟨a1, a2, a3, a4, a5, hl, a7, a8, a9, a10⟩

theorem HierShapeK_of_S {d : Design} {m : Module} (h : HierShapeS d m = true) :
    HierShapeK d m = true := by
  have e5 : m.body.all (fun s => match s with
      | .inst mn _ cs => connsOkK d m mn cs
      | _ => true) = true := by
    rw [List.all_eq_true]
    intro s hs
    cases s with
    | inst mn i cs => exact connsOkK_of_S (hierS_inst_ok h hs)
    | _ => rfl
  simp only [HierShapeS, Bool.and_eq_true] at h
  simp only [HierShapeK, Bool.and_eq_true]
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, _⟩, a6⟩, a7⟩, a8⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, e5⟩, a6⟩, a7⟩, a8⟩

theorem HierShapeS_of_K {d : Design} {m : Module} (h1 : ∀ x ∈ d.modules, x.outputs.length = 1)
    (h : HierShapeK d m = true) : HierShapeS d m = true := by
  have e5 : m.body.all (fun s => match s with
      | .inst mn _ cs => connsOkS d m mn cs
      | _ => true) = true := by
    have hK : m.body.all (fun s => match s with
        | .inst mn _ cs => connsOkK d m mn cs
        | _ => true) = true := by
      simp only [HierShapeK, Bool.and_eq_true] at h
      exact h.1.1.1.2
    rw [List.all_eq_true] at hK ⊢
    intro s hs
    have := hK s hs
    cases s with
    | inst mn i cs => exact connsOkS_of_K h1 this
    | _ => rfl
  simp only [HierShapeK, Bool.and_eq_true] at h
  simp only [HierShapeS, Bool.and_eq_true]
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, _⟩, a6⟩, a7⟩, a8⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, e5⟩, a6⟩, a7⟩, a8⟩

/-- COINCIDENCE: when every module of the design has exactly one output, `U2HRStmtK` is `U2HRStmt`
(both directions; `U2HRStmt → U2HRStmtK` needs no hypothesis, see `U2HRStmtK_of_U2HRStmt`). -/
theorem U2HRStmtK_iff (c : Contract) (m : Module) (d : Design) (f : c.table.Ty)
    (h1 : ∀ x ∈ d.modules, x.outputs.length = 1) : U2HRStmtK c m d f ↔ U2HRStmt c m d f := by
  unfold U2HRStmtK U2HRStmt
  constructor
  · rintro ⟨a, b, c', d', e, f', g, h, i⟩
    exact ⟨a, b, c', HierShapeS_of_K h1 d', e, f', g, h, i⟩
  · rintro ⟨a, b, c', d', e, f', g, h, i⟩
    exact ⟨a, b, c', HierShapeK_of_S d', e, f', g, h, i⟩

theorem U2HRStmtK_of_U2HRStmt (c : Contract) (m : Module) (d : Design) (f : c.table.Ty)
    (h : U2HRStmt c m d f) : U2HRStmtK c m d f := by
  obtain ⟨a, b, c', d', e, f', g, h, i⟩ := h
  exact ⟨a, b, c', HierShapeK_of_S d', e, f', g, h, i⟩

/-! ## The K-shape facts (the shape of `hierS_*`, with `1 ≤ c.outputs.length` in place of `= 1`)

The theorems below (`*_multi`) are the statements and proofs of the `HierShapeS` theorems of
Tools/VedU2HierProj.lean, Kid, Net, Step, Reg, State with `HierShapeS` replaced by `HierShapeK`
(textual copy by a script; the proofs never used the length-1 fact). -/

theorem hierK_inst_unique {d : Design} {m : Module} (h : HierShapeK d m = true) :
    (instNames m.body).Nodup := by
  simp only [HierShapeK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

theorem hierK_clk {d : Design} {m : Module} (h : HierShapeK d m = true) : clkRstOk d m = true := by
  simp only [HierShapeK, Bool.and_eq_true] at h
  exact h.2

theorem hierK_body {d : Design} {m : Module} (h : HierShapeK d m = true) :
    ∀ s ∈ m.body, isAsgInstReg s = true := by
  have : m.body.all isAsgInstReg = true := by
    simp only [HierShapeK, Bool.and_eq_true] at h
    exact h.1.1.1.1.2
  exact fun s hs => List.all_eq_true.mp this s hs

theorem hierK_inst_ok {d : Design} {m : Module} (h : HierShapeK d m = true) {mn i : String}
    {cs : List (String × Expr)} (hin : Stmt.inst mn i cs ∈ m.body) : connsOkK d m mn cs = true := by
  have h5 : m.body.all (fun s => match s with
      | .inst mn _ cs => connsOkK d m mn cs
      | _ => true) = true := by
    simp only [HierShapeK, Bool.and_eq_true] at h
    exact h.1.1.1.2
  exact List.all_eq_true.mp h5 _ hin

theorem hierK_ne {d : Design} {m : Module} (h : HierShapeK d m = true) :
    ∀ x ∈ d.modules, x ≠ m := by
  intro x hx hxm
  simp only [HierShapeK, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, hC⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  subst hxm
  have h2 : (d.modules.map (·.name)).contains x.name = false := hC
  have h3 : x.name ∈ d.modules.map (·.name) := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp [List.contains_eq_mem, h3] at h2

/-- What `connsOkK` gives about the resolved child and the connections: the facts of
`connsOkS_facts`, with `1 ≤ c.outputs.length` in place of `c.outputs.length = 1`. -/
theorem connsOkK_facts {d : Design} {m : Module} {mn : String} {cs : List (String × Expr)}
    (h : connsOkK d m mn cs = true) :
    ∃ c, findMod d mn = some c ∧ c.isPrimitive = false ∧ leafBody c.body = true ∧
      childSane c = true ∧ (inNames c).Nodup ∧ 1 ≤ c.outputs.length ∧ (cs.map (·.1)).Nodup ∧
      cs.all (fun p => (c.inputs ++ c.outputs).any (·.name == p.1)) = true ∧
      (∀ p ∈ c.inputs ++ c.outputs, ∃ q ∈ cs, q.1 = p.name) ∧
      (∀ q ∈ cs, ∃ x, q.2 = Expr.ref x) := by
  simp only [connsOkK] at h
  cases hf : findMod d mn with
  | none => simp [hf] at h
  | some c =>
    simp only [hf, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, and_assoc] at h
    obtain ⟨hp, _, _, hl, hsane, hol, _, _, hcsnd, hcov, hall2, hrefs⟩ := h
    refine ⟨c, rfl, hp, hl, hsane, ?_, hol, hcsnd, hall2, ?_, ?_⟩
    · have := hsane
      simp only [childSane, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.1
    · intro p hp
      have := List.all_eq_true.mp hcov p hp
      obtain ⟨q, hq, hqe⟩ := List.any_eq_true.mp this
      exact ⟨q, hq, by simpa using hqe⟩
    · intro q hq
      have := List.all_eq_true.mp hrefs q hq
      cases hq2 : q.2 with
      | ref x => exact ⟨x, rfl⟩
      | _ => simp [hq2] at this

/-! copied from Tools/VedU2HierProj.lean (`instEvalS_succ`): the shape hypothesis is `HierShapeK` -/

theorem instEvalS_succ_multi {d : Design} {m : Module} (arr : Module → List Stmt) (st : HSt) (we : WEnv)
    (mn i : String) (cs : List (String × Expr)) (hok : connsOkK d m mn cs = true)
    (hsucc : ∀ c, findMod d mn = some c → ChildSucc c (arr c))
    (hleafArr : ∀ c, findMod d mn = some c → leafBody (arr c) = true) (env : Env) :
    ∃ l, instEvalS d arr st we mn i cs env = some l := by
  obtain ⟨c, hf, hprim, hleaf, hsane, hnd, hol, hcsnd, hall, hcov, href⟩ := connsOkK_facts hok
  have hinok : instOkS c cs = true := by
    unfold instOkS; rw [hprim, hleaf, hall]; rfl
  obtain ⟨seed0, E0, nx0, hE0, hN0⟩ := hsucc c hf
  have hleafA := hleafArr c hf
  obtain ⟨e, he⟩ := childSeed_some c cs we env (fun p hp => hcov p (List.mem_append_left _ hp)) href
  obtain ⟨E', hE'⟩ := evalAssigns_succ_leaf _ _ _ hleafA seed0 E0 hE0
    (fun n => if (regOuts (arr c)).contains n && !(inNames c).contains n then st [i] n else e n)
  obtain ⟨l, hl⟩ := outWrites_some c cs E' href
  refine ⟨l, ?_⟩
  unfold instEvalS
  simp only [hf, hinok, if_true]
  have : childRunS arr we c cs env (st [i]) = some E' := by
    simp only [childRunS, childSeedS, he, Option.map_some, Option.bind_some]
    exact hE'
  simp only [this, Option.bind_some]
  exact hl

/-! copied from Tools/VedU2HierProj.lean (`stepHS_succ`): the shape hypothesis is `HierShapeK` -/

theorem stepHS_succ_multi (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeK d m = true) (hA : AdmArr d m arr) (hsupp : ExprsSupp m (arr m))
    (hch : ∀ c ∈ d.modules, ChildSucc c (arr c)) (st : HSt) (env0 : Env) :
    ∃ r, stepHS d arr m st env0 = some r := by
  have hmem : ∀ s, s ∈ arr m → s ∈ m.body := fun s hs => hA.1.mem_iff.mp hs
  have hai : ∀ s ∈ arr m, isAsgInstReg s = true := fun s hs => hierK_body hS s (hmem s hs)
  have hinst : ∀ mn i cs, Stmt.inst mn i cs ∈ arr m → ∃ c, findMod d mn = some c ∧
      leafBody (arr c) = true ∧ (∀ p ∈ c.inputs, ∃ q ∈ cs, q.1 = p.name) ∧
      (∀ q ∈ cs, ∃ x, q.2 = Expr.ref x) ∧ ChildSucc c (arr c) ∧ instOkS c cs = true := by
    intro mn i cs hin
    obtain ⟨c, hf, hprim, hleaf, hsane, hnd, hol, hcsnd, hall, hcov, href⟩ :=
      connsOkK_facts (hierK_inst_ok hS (hmem _ hin))
    refine ⟨c, hf, leafBody_perm (hA.2.2 c (findMod_mem hf)).1.symm hleaf,
      fun p hp => hcov p (List.mem_append_left _ hp), href, hch c (findMod_mem hf), ?_⟩
    unfold instOkS; rw [hprim, hleaf, hall]; rfl
  have hfold : ∃ E, evalAssignsI (declWidth m) (instEvalS d arr st (declWidth m)) (arr m) env0 = some E := by
    apply evalAssignsI_succ_S m _ _ _ hai hsupp
    intro mn i cs hin e
    obtain ⟨c, hf, hleaf, hin', href, hsucc, hok⟩ := hinst mn i cs hin
    obtain ⟨envC, nx, hr, _⟩ := childRun_succ arr (declWidth m) c cs e (st [i]) hin' href hsucc hleaf
    obtain ⟨l, hl⟩ := outWrites_some c cs envC href
    exact ⟨l, by simp [instEvalS, hf, hok, hr, hl]⟩
  obtain ⟨E, hE⟩ := hfold
  obtain ⟨nxP, hnxP⟩ := regNexts_succ_supp m (fun _ _ => 0) (arr m) hai hsupp E
  have hkids : ∃ ys, (instDecls (arr m)).mapM (childNexts d arr (declWidth m) st E) = some ys := by
    apply mapM_some_of_forall
    rintro ⟨mn, i, cs⟩ hx
    obtain ⟨c, hf, hleaf, hin', href, hsucc, hok⟩ := hinst mn i cs ((mem_instDecls_iff _ _).mp hx)
    obtain ⟨envC, nx, hr, hn⟩ := childRun_succ arr (declWidth m) c cs E (st [i]) hin' href hsucc hleaf
    exact ⟨_, childNexts_some d arr (declWidth m) st E mn i cs c envC nx hf hok hr hn⟩
  obtain ⟨ys, hys⟩ := hkids
  exact ⟨(E, ([], nxP) :: ys), by simp [stepHS, hierK_clk hS, hE, hnxP, hys]⟩

/-! copied from Tools/VedU2HierProj.lean (`runHS_exists`): the shape hypothesis is `HierShapeK` -/

theorem runHS_exists_multi (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeK d m = true) (hA : AdmArr d m arr) (hsupp : ExprsSupp m (arr m))
    (hch : ∀ c ∈ d.modules, ChildSucc c (arr c)) (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : HSt), ∃ envs sts, runHSTrace d arr m seed k st = some (envs, sts) := by
  intro k
  induction k with
  | zero => intro st; exact ⟨[], [], rfl⟩
  | succ k ih =>
    intro st
    obtain ⟨⟨envF, ups⟩, hr⟩ := stepHS_succ_multi d arr m hS hA hsupp hch st
      (seed k (restrictTo (regOuts (arr m)) (st [])))
    obtain ⟨envs, sts, hrest⟩ := ih (applyH st ups)
    exact ⟨envF :: envs, st :: sts, by simp [runHSTrace, hr, hrest]⟩

/-! ## Projection: helper lemmas -/

/-! copied from Tools/VedU2HierProj.lean (`runHS_proj_aux`): the shape hypothesis is `HierShapeK` -/

theorem runHS_proj_aux_multi (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeK d m = true) (hA : AdmArr d m arr)
    (mn i : String) (cs : List (String × Expr)) (c : Module)
    (hin : Stmt.inst mn i cs ∈ m.body) (hf : findMod d mn = some c) :
    ∀ (k : Nat) (seedK : Nat → (String → Nat) → Env) (st : HSt) (envs : List Env) (sts : List HSt),
      runHSTrace d arr m seedK k st = some (envs, sts) →
      ∃ cenvs cstates,
        runModuleTrace (declWidth c) (arr c) (seedFwd c k (insCOf (declWidth m) cs envs)) k
          (restrictTo (regOuts (arr c)) (st [i])) (fun _ _ => 0) = some (cenvs, cstates) ∧
        ∀ t, t < k → ∃ E Ec S Sc, envs[t]? = some E ∧ cenvs[t]? = some Ec ∧ sts[t]? = some S ∧
          cstates[t]? = some Sc ∧ ProjAt (declWidth m) c cs i E Ec S Sc := by
  have hmemM : Stmt.inst mn i cs ∈ arr m := hA.1.mem_iff.mpr hin
  obtain ⟨c0, hf0, hprim, hleaf, hsane, hnd, hol, hcsnd, hall, hcov, href⟩ :=
    connsOkK_facts (hierK_inst_ok hS hin)
  have hc : c = c0 := by rw [hf] at hf0; exact Option.some.inj hf0
  subst hc
  have hperm := (hA.2.2 c (findMod_mem hf)).1
  have hleafA := leafBody_perm hperm.symm hleaf
  have hinok : instOkS c cs = true := by unfold instOkS; rw [hprim, hleaf, hall]; rfl
  have hdecl : ((instDecls (arr m)).map (·.2.1)).Nodup := by
    rw [← instNames_eq]
    exact (instNames_perm hA.1).nodup_iff.mpr (hierK_inst_unique hS)
  intro k
  induction k with
  | zero =>
    intro seedK st envs sts hrun
    simp only [runHSTrace, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨[], [], rfl, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro seedK st envs sts hrun
    simp only [runHSTrace] at hrun
    cases hs : stepHS d arr m st (seedK k (restrictTo (regOuts (arr m)) (st []))) with
    | none => simp [hs] at hrun
    | some r =>
      obtain ⟨envF, ups⟩ := r
      cases hr : runHSTrace d arr m seedK k (applyH st ups) with
      | none => simp [hs, hr] at hrun
      | some q =>
        obtain ⟨rest, sts'⟩ := q
        simp [hs, hr] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        obtain ⟨_, hfold, nxP, ys, hnxP, hys, hups⟩ := stepHS_some_inv hs
        have hG := good_of_fold d (declWidth m) _ (instEvalS_laws d arr st (declWidth m)) (arr m) _
          envF hA.2.1 hfold
        obtain ⟨l, hl, hlE⟩ := hG.2 _ hmemM
        have hl' : instEvalS d arr st (declWidth m) mn i cs envF = some l := by simpa [cellVals] using hl
        obtain ⟨c', envC, hf', _, hrunC, hw⟩ := instEvalS_some hl'
        have hcc : c' = c := by rw [hf] at hf'; exact (Option.some.inj hf').symm
        subst hcc
        obtain ⟨y, hy, hyc⟩ := mapM_mem_ex _ _ _ hys (mn, i, cs) ((mem_instDecls_iff _ _).mpr hmemM)
        obtain ⟨nx, hnx, hyeq⟩ : ∃ nx, regNexts (declWidth c') (fun _ _ => 0) (arr c') envC = some nx ∧
            y = ([i], nx) := by
          unfold childNexts at hyc
          simp only [hf, hinok, if_true, hrunC, Option.bind_some] at hyc
          cases hn : regNexts (declWidth c') (fun _ _ => 0) (arr c') envC with
          | none => simp [hn] at hyc
          | some nx => simp [hn] at hyc; exact ⟨nx, rfl, hyc.symm⟩
        subst hyeq
        -- the paths of the updates are distinct
        have hpaths : ys.map (·.1) = (instDecls (arr m)).map (fun x => ([x.2.1] : Path)) :=
          mapM_fst_eq _ _ _ (fun x y h => childNexts_fst d arr (declWidth m) st envF x y h) _ _ hys
        have hupsnd : (ups.map (·.1)).Nodup := by
          rw [hups, List.map_cons, hpaths, List.nodup_cons]
          have h2 : (instDecls (arr m)).map (fun x => ([x.2.1] : Path)) =
              ((instDecls (arr m)).map (·.2.1)).map (fun a => [a]) := by
            simp [List.map_map, Function.comp_def]
          refine ⟨?_, ?_⟩
          · intro hmem
            obtain ⟨x, _, hx⟩ := List.mem_map.mp hmem
            exact absurd hx (List.cons_ne_nil _ _)
          · rw [h2]; exact hdecl.map (fun a => [a]) (fun a b h e => h (by simpa using e))
        have hstate : applyH st ups [i] = applyNexts (st [i]) nx :=
          applyH_at st ups hupsnd ([i], nx) (by rw [hups]; exact List.mem_cons_of_mem _ hy)
        have hnames : ∀ p ∈ nx, p.1 ∈ regOuts (arr c') := regNexts_fst_mem _ _ _ _ _ hleafA hnx
        have hstc' : applyNexts (restrictTo (regOuts (arr c')) (st [i])) nx =
            restrictTo (regOuts (arr c')) (applyH st ups [i]) := by
          rw [hstate, restrict_applyNexts _ _ _ hnames]
        obtain ⟨cenvs', cstates', hrunM', hcorr'⟩ := ih seedK (applyH st ups) rest sts' hr
        obtain ⟨seedC, hseedC, hevC⟩ : ∃ seedC, childSeedS c' cs (declWidth m) envF (regOuts (arr c'))
            (st [i]) = some seedC ∧ evalAssigns (declWidth c') (fun _ _ => 0) (arr c') seedC = some envC := by
          unfold childRunS at hrunC
          cases hh : childSeedS c' cs (declWidth m) envF (regOuts (arr c')) (st [i]) with
          | none => simp [hh] at hrunC
          | some sd => exact ⟨sd, rfl, by simpa [hh] using hrunC⟩
        have hseed1 := seedFwd_first c' (declWidth m) cs envF rest k (regOuts (arr c')) (st [i]) seedC
          hnd hseedC
        have hstepM : stepModule (declWidth c') (arr c')
            (seedFwd c' (k + 1) (insCOf (declWidth m) cs (envF :: rest)) k
              (restrictTo (regOuts (arr c')) (st [i]))) (fun _ _ => 0) =
            some (envC, nx, fun _ _ => 0) := by
          rw [hseed1]
          unfold stepModule
          simp [hevC, hnx, memNexts_leaf _ _ _ _ hleafA]
        refine ⟨envC :: cenvs', restrictTo (regOuts (arr c')) (st [i]) :: cstates', ?_, ?_⟩
        · simp only [runModuleTrace]
          rw [hstepM]
          have hcongr := runModuleTrace_congr_seed (declWidth c') (arr c')
            (seedFwd c' (k + 1) (insCOf (declWidth m) cs (envF :: rest)))
            (seedFwd c' k (insCOf (declWidth m) cs rest)) k
            (fun j hj => seedFwd_shift c' _ cs envF rest k j hj)
            (applyNexts (restrictTo (regOuts (arr c')) (st [i])) nx) (fun _ _ => 0)
          simp only [Option.bind_eq_bind, Option.bind_some]
          rw [hcongr, hstc', hrunM']
          rfl
        · intro t ht
          cases t with
          | succ t =>
            obtain ⟨E, Ec, S, Sc, h1, h2, h3, h4, h5⟩ := hcorr' t (by omega)
            exact ⟨E, Ec, S, Sc, by simpa using h1, by simpa using h2, by simpa using h3,
              by simpa using h4, h5⟩
          | zero =>
            refine ⟨envF, envC, st, restrictTo (regOuts (arr c')) (st [i]), rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
            · intro p hpm
              obtain ⟨e0, he0, hsc⟩ := childSeedS_inv c' cs (declWidth m) envF _ _ seedC hseedC
              obtain ⟨hz, hp⟩ := childSeed_val c' cs (declWidth m) envF e0 he0 hnd
              obtain ⟨ex, hl2, hv⟩ := hp p hpm
              have hpn : p.name ∈ inNames c' := List.mem_map.mpr ⟨p, hpm, rfl⟩
              have hkeep := evalAssigns_keeps (declWidth c') (fun _ _ => 0) p.name (arr c') seedC envC
                (leafBody_assign_ne c' (arr c') hperm hsane p.name hpn) hleafA hevC
              refine ⟨ex, hl2, ?_⟩
              rw [hv, hkeep, hsc]
              simp [hpn]
            · intro q hq
              obtain ⟨qq, hqq, hq1⟩ := hcov q (List.mem_append_right _ hq)
              obtain ⟨x, hx⟩ := href qq hqq
              have hqe : qq = (q.name, Expr.ref x) := by
                obtain ⟨a, b⟩ := qq; simp only at hq1 hx; subst hq1; subst hx; rfl
              rw [hqe] at hqq
              refine ⟨x, lookup_of_mem_nodup cs hcsnd _ _ hqq, ?_⟩
              have hmemo := outWrites_mem c' cs envC l hw q.name x hqq
                (List.any_eq_true.mpr ⟨q, hq, by simp⟩)
              exact hlE _ hmemo
            · intro r hr'
              have : r ∈ regOuts (arr c') := (regOuts_perm_mem hperm r).mpr hr'
              simp [restrictTo, this]

/-! copied from Tools/VedU2HierProj.lean (`runHS_proj`): the shape hypothesis is `HierShapeK` -/

theorem runHS_proj_multi (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeK d m = true) (hA : AdmArr d m arr)
    (inp : Nat → String → Nat) (K : Nat) (envs : List Env) (sts : List HSt)
    (hrun : runHSTrace d arr m (seedFwd m K inp) K (st0H d m) = some (envs, sts))
    (mn i : String) (cs : List (String × Expr)) (hin : Stmt.inst mn i cs ∈ m.body) :
    ∃ c cenvs cstates, findMod d mn = some c ∧
      runModuleTrace (declWidth c) (arr c) (seedFwd c K (insCOf (declWidth m) cs envs)) K (st0Of c)
        (fun _ _ => 0) = some (cenvs, cstates) ∧
      runModule (declWidth c) (arr c) (seedFwd c K (insCOf (declWidth m) cs envs)) K (st0Of c)
        (fun _ _ => 0) = some cenvs ∧
      ∀ t, t < K → ∃ E Ec S Sc, envs[t]? = some E ∧ cenvs[t]? = some Ec ∧ sts[t]? = some S ∧
        cstates[t]? = some Sc ∧ ProjAt (declWidth m) c cs i E Ec S Sc := by
  obtain ⟨c, hf, _⟩ := connsOkK_facts (hierK_inst_ok hS hin)
  obtain ⟨cenvs, cstates, hrunM, hcorr⟩ := runHS_proj_aux_multi d arr m hS hA mn i cs c hin hf K _ _ envs sts hrun
  have hslice := st0H_slice d m mn i cs c (hierK_inst_unique hS) hin hf
  have hperm := (hA.2.2 c (findMod_mem hf)).1
  have hres : restrictTo (regOuts (arr c)) (st0H d m [i]) = st0Of c := by
    rw [hslice]
    funext n
    by_cases hn : n ∈ regOuts (arr c)
    · simp [restrictTo, hn]
    · have : n ∉ regOuts c.body := fun h => hn ((regOuts_perm_mem hperm n).mpr h)
      simp [restrictTo, hn, st0Of_off c n this]
  rw [hres] at hrunM
  refine ⟨c, cenvs, cstates, hf, hrunM, ?_, hcorr⟩
  have := runModuleTrace_fst (declWidth c) (arr c) (seedFwd c K (insCOf (declWidth m) cs envs)) K
    (st0Of c) (fun _ _ => 0)
  rw [hrunM] at this
  simpa using this.symm

/-! ## clock / reset: the statement side (reviewer obligation 3) -/

/-! copied from Tools/VedU2HierProj.lean (`runHS_child_clkRst`): the shape hypothesis is `HierShapeK` -/

theorem runHS_child_clkRst_multi (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeK d m = true) (hA : AdmArr d m arr)
    (hwr : ∀ n ∈ wrsH d (arr m), n ∉ inNames m)
    (cc : Contract) (htie : cc.clkRst = designClkRst d m)
    (inp : Nat → String → Nat) (hok : InputsOk cc m inp) (K : Nat) (envs : List Env) (sts : List HSt)
    (hrun : runHSTrace d arr m (seedFwd m K inp) K (st0H d m) = some (envs, sts))
    (mn i : String) (cs : List (String × Expr)) (hin : Stmt.inst mn i cs ∈ m.body)
    (c : Module) (hf : findMod d mn = some c) (hreg : regsOf c.body ≠ []) :
    ∃ x y kc kr cenvs, cc.clkRst = some (x, y) ∧ regClkRst c.body = some (kc, kr) ∧
      runModule (declWidth c) (arr c) (seedFwd c K (insCOf (declWidth m) cs envs)) K (st0Of c)
        (fun _ _ => 0) = some cenvs ∧
      ∀ t, t < K → ∃ Ec, cenvs[t]? = some Ec ∧ Ec kr = 0 ∧ Ec kc = inp t x := by
  obtain ⟨x, y, kc, kr, hrc, h1, h2, hcl, hx, hy, hne, hkc, hkr⟩ :=
    instPair_tie d m (hierK_clk hS) mn i cs c hin hf hreg cc htie
  obtain ⟨c', cenvs, cstates, hf', hrunM, hrunR, hcorr⟩ := runHS_proj_multi d arr m hS hA inp K envs sts hrun
    mn i cs hin
  have hcc : c' = c := by rw [hf] at hf'; exact (Option.some.inj hf').symm
  subst hcc
  refine ⟨x, y, kc, kr, cenvs, hcl, hrc, hrunR, ?_⟩
  intro t ht
  obtain ⟨E, Ec, S, Sc, hE, hEc, _, _, hproj, _, _⟩ := hcorr t ht
  have hin2 := runHS_inputs d arr m hA hwr inp K K (Nat.le_refl K) _ envs sts hrun t ht E hE
  have hkr' : ∃ p ∈ c'.inputs, p.name = kr := by
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hkr; exact ⟨p, hp, hpn⟩
  have hkc' : ∃ p ∈ c'.inputs, p.name = kc := by
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hkc; exact ⟨p, hp, hpn⟩
  refine ⟨Ec, hEc, ?_, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := hkr'
    obtain ⟨e, hl, hv⟩ := hproj p hp
    rw [h2] at hl; cases hl
    simp [evalExpr] at hv
    rw [← hv, hin2 y hy, Nat.sub_self, Nat.zero_add]
    exact inst_reset_zero cc m inp hok x y hcl t
  · obtain ⟨p, hp, rfl⟩ := hkc'
    obtain ⟨e, hl, hv⟩ := hproj p hp
    rw [h1] at hl; cases hl
    simp [evalExpr] at hv
    rw [← hv, hin2 x hx, Nat.sub_self, Nat.zero_add]


/-! copied from Tools/VedU2HierStmt.lean (`runHSTrace_open`): the shape hypothesis is `HierShapeK` -/

theorem runHSTrace_open_multi (d : Design) (arr : Module → List Stmt) (m : Module)
    (hA : AdmArr d m arr) (hS : HierShapeK d m = true)
    (seed : Nat → (String → Nat) → Env) (k : Nat) (st : HSt) (envs : List Env) (sts : List HSt)
    (hrun : runHSTrace d arr m seed k st = some (envs, sts)) :
    ∀ t, t < k → ∃ E S, envs[t]? = some E ∧ sts[t]? = some S ∧
      evalAssigns (declWidth m) (fun _ _ => 0) (arr m)
        (oracleSeed d E (arr m)
          (seed (k - 1 - t) (restrictTo (regOuts (arr m)) (S [])))) = some E := by
  intro t ht
  obtain ⟨E, S, h1, h2, hf⟩ := runHSTrace_cycle d arr m seed k st envs sts hrun t ht
  refine ⟨E, S, h1, h2, ?_⟩
  exact closed_fold_is_open d _ _ _ (instEvalS_laws d arr S (declWidth m)) (arr m) _ E hA.2.1
    (fun s hs => hierK_body hS s (hA.1.mem_iff.mp hs)) hf

/-! copied from Tools/VedU2HierKid.lean (`kid_inst`): the shape hypothesis is `HierShapeK` -/

theorem kid_inst_multi (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeK d m = true) (hA : AdmArr d m arr)
    (hwr : ∀ n ∈ wrsH d (arr m), n ∉ inNames m)
    (cc : Contract) (htie : cc.clkRst = designClkRst d m)
    (ins : Nat → String → Nat) (hok : InputsOk cc m ins) (K : Nat) (envs : List Env)
    (sts : List HSt)
    (hrun : runHSTrace d arr m (seedFwd m K ins) K (st0H d m) = some (envs, sts))
    (mn i : String) (cs : List (String × Expr)) (hin : Stmt.inst mn i cs ∈ m.body)
    (c : Module) (hf : findMod d mn = some c)
    (ck : Contract) (g : ck.table.Ty) (hU : U1Stmt ck c g)
    (hclkc : ck.clkRst = regClkRst c.body)
    (hconn : ∀ p ∈ c.inputs, ∃ x, cs.lookup p.name = some (Expr.ref x) ∧ x ∈ inNames m)
    (hdata : ∀ p ∈ ck.dataInputs, ∃ x, cs.lookup p.name = some (Expr.ref x) ∧
      (∃ q ∈ cc.dataInputs, q.name = x) ∧ declWidth m x = declWidth c p.name) :
    ∀ t, t < K → ∀ E, envs[t]? = some E → ∀ q ∈ c.outputs,
      ∃ x, cs.lookup q.name = some (Expr.ref x) ∧ E x = srcOf ck g (insCIn cs ins) q.name t := by
  obtain ⟨c', cenvs, cstates, hf', hrunM, hrunR, hcorr⟩ :=
    runHS_proj_multi d arr m hS hA ins K envs sts hrun mn i cs hin
  have hcc : c = c' := by rw [hf] at hf'; exact Option.some.inj hf'
  subst hcc
  obtain ⟨_, ⟨hcore, _⟩, _, _, hout⟩ := hU
  have hperm := hA.2.2 c (findMod_mem hf)
  have hinits : (regsOf c.body).map (fun r => (r.1, r.2.2.2)) = ck.inits := hcore.2.2.2.2.2.2.2.1
  have hst0 : st0Of c = st0 ck c := st0Of_eq_st0 ck c hinits
  -- the child stream is in range
  have hok' : InputsOk ck c (insCIn cs ins) := by
    refine ⟨?_, ?_⟩
    · intro t p hp
      obtain ⟨x, hl, ⟨q, hq, hqn⟩, hw⟩ := hdata p hp
      have h1 : insCIn cs ins t p.name = ins t x := by simp [insCIn, hl]
      rw [h1, ← hw]
      have := hok.1 t q hq
      rw [hqn] at this
      exact this
    · intro t kr hkr
      rw [hclkc] at hkr
      have hreg : regsOf c.body ≠ [] := by
        intro h0; simp [regClkRst, h0] at hkr
      obtain ⟨x, y, kc, kr', hrc, h1, h2, hcl, hx, hy, hne, hkc, hkr2⟩ :=
        instPair_tie d m (hierK_clk hS) mn i cs c hin hf hreg cc htie
      have hkk : (kc, kr') = kr := Option.some.inj (hrc.symm.trans hkr)
      subst hkk
      have : insCIn cs ins t kr' = ins t y := by simp [insCIn, h2]
      show insCIn cs ins t kr' = 0
      rw [this]
      exact hok.2 t (x, y) hcl
  -- the seeds agree at every executed cycle
  have hpre : ∀ t, t < K → ∀ E, envs[t]? = some E → ∀ n ∈ inNames c,
      insCIn cs ins t n = insCOf (declWidth m) cs envs t n := by
    intro t ht E hE n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    obtain ⟨x, hl, hx⟩ := hconn p hp
    have hEx := runHS_inputs d arr m hA hwr ins K K (Nat.le_refl K) _ envs sts hrun t ht E hE x hx
    simp [insCIn, insCOf, hl, hE, evalExpr, hEx]
  have hseed : ∀ j, j < K → seedFwd c K (insCOf (declWidth m) cs envs) j =
      seedFwd c K (insCIn cs ins) j := by
    intro j hj
    funext st n
    simp only [seedFwd]
    by_cases hn : (c.inputs.map (·.name)).contains n = true
    · rw [if_pos hn, if_pos hn]
      obtain ⟨E, Ec, S, Sc, hE, _⟩ := hcorr (K - 1 - j) (by omega)
      exact (hpre _ (by omega) E hE n (List.contains_iff_mem.mp hn)).symm
    · rw [if_neg hn, if_neg hn]
  obtain ⟨envs', hrun', hall⟩ := hout (arr c) hperm.1 hperm.2 (insCIn cs ins) hok' K
  have hcongr := runModule_congr_seed (declWidth c) (arr c)
    (seedFwd c K (insCOf (declWidth m) cs envs)) (seedFwd c K (insCIn cs ins)) K hseed
    (st0Of c) (fun _ _ => 0)
  rw [hcongr, hst0, hrun'] at hrunR
  have hce : envs' = cenvs := Option.some.inj hrunR
  intro t ht E hE q hq
  obtain ⟨E0, Ec, S, Sc, hE0, hEc, _, _, hproj⟩ := hcorr t ht
  have hEE : E = E0 := Option.some.inj (hE.symm.trans hE0)
  subst hEE
  obtain ⟨x, hl, hxv⟩ := hproj.2.1 q hq
  refine ⟨x, hl, ?_⟩
  have hqk : q ∈ ck.outputs := by rw [← hcore.2.2.2.2.2.1]; exact hq
  obtain ⟨env, he, hv⟩ := hall t ht q hqk
  rw [hce, hEc] at he
  have hee : env = Ec := (Option.some.inj he).symm
  subst hee
  rw [hxv]; exact hv


/-! copied from Tools/VedU2HierNet.lean (`kid_inst_net`): the shape hypothesis is `HierShapeK` -/

theorem kid_inst_net_multi (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeK d m = true) (hA : AdmArr d m arr)
    (hwr : ∀ n ∈ wrsH d (arr m), n ∉ inNames m)
    (cc : Contract) (htie : cc.clkRst = designClkRst d m)
    (ins : Nat → String → Nat) (hok : InputsOk cc m ins) (K : Nat) (envs : List Env)
    (sts : List HSt)
    (hrun : runHSTrace d arr m (seedFwd m K ins) K (st0H d m) = some (envs, sts))
    (mn i : String) (cs : List (String × Expr)) (hin : Stmt.inst mn i cs ∈ m.body)
    (c : Module) (hf : findMod d mn = some c)
    (ck : Contract) (g : ck.table.Ty) (hU : U1Stmt ck c g)
    (hclkc : ck.clkRst = regClkRst c.body)
    (hconn : ∀ p ∈ c.inputs, ∃ x, cs.lookup p.name = some (Expr.ref x) ∧
      (ck.dataInputs.any (·.name == p.name) = true ∨ x ∈ inNames m))
    (hrstnd : ∀ kr, ck.clkRst = some kr → ck.dataInputs.any (·.name == kr.2) = false)
    (F : Nat → String → Nat)
    (hrange : ∀ t, ∀ p ∈ ck.dataInputs, F t p.name < 2 ^ declWidth c p.name)
    (hrunF : ∀ t, t < K → ∀ E, envs[t]? = some E → ∀ p ∈ ck.dataInputs,
      ∃ x, cs.lookup p.name = some (Expr.ref x) ∧ E x = F t p.name) :
    ∀ t, t < K → ∀ E, envs[t]? = some E → ∀ q ∈ c.outputs,
      ∃ x, cs.lookup q.name = some (Expr.ref x) ∧
        E x = srcOf ck g (netIn ck cs ins F) q.name t := by
  obtain ⟨c', cenvs, cstates, hf', hrunM, hrunR, hcorr⟩ :=
    runHS_proj_multi d arr m hS hA ins K envs sts hrun mn i cs hin
  have hcc : c = c' := by rw [hf] at hf'; exact Option.some.inj hf'
  subst hcc
  obtain ⟨_, ⟨hcore, _⟩, _, _, hout⟩ := hU
  have hperm := hA.2.2 c (findMod_mem hf)
  have hinits : (regsOf c.body).map (fun r => (r.1, r.2.2.2)) = ck.inits := hcore.2.2.2.2.2.2.2.1
  have hst0 : st0Of c = st0 ck c := st0Of_eq_st0 ck c hinits
  -- the child stream is in range
  have hok' : InputsOk ck c (netIn ck cs ins F) := by
    refine ⟨?_, ?_⟩
    · intro t p hp
      have hd : ck.dataInputs.any (·.name == p.name) = true :=
        List.any_eq_true.mpr ⟨p, hp, by simp⟩
      have h1 : netIn ck cs ins F t p.name = F t p.name := by simp [netIn, hd]
      rw [h1]
      exact hrange t p hp
    · intro t kr hkr
      rw [hclkc] at hkr
      have hreg : regsOf c.body ≠ [] := by
        intro h0; simp [regClkRst, h0] at hkr
      obtain ⟨x, y, kc, kr', hrc, h1, h2, hcl, hx, hy, hne, hkc, hkr2⟩ :=
        instPair_tie d m (hierK_clk hS) mn i cs c hin hf hreg cc htie
      have hkk : (kc, kr') = kr := Option.some.inj (hrc.symm.trans hkr)
      subst hkk
      have hnd := hrstnd (kc, kr') (hclkc.trans hrc)
      have : netIn ck cs ins F t kr' = ins t y := by simp [netIn, hnd, insCIn, h2]
      show netIn ck cs ins F t kr' = 0
      rw [this]
      exact hok.2 t (x, y) hcl
  -- the seeds agree at every executed cycle
  have hpre : ∀ t, t < K → ∀ E, envs[t]? = some E → ∀ n ∈ inNames c,
      netIn ck cs ins F t n = insCOf (declWidth m) cs envs t n := by
    intro t ht E hE n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    obtain ⟨x, hl, hx⟩ := hconn p hp
    by_cases hd : ck.dataInputs.any (·.name == p.name) = true
    · obtain ⟨p', hp', hpn⟩ := List.any_eq_true.mp hd
      have hpn' : p'.name = p.name := by simpa using hpn
      obtain ⟨x', hl', hEx'⟩ := hrunF t ht E hE p' hp'
      rw [hpn'] at hl' hEx'
      have hxx : x' = x := by
        rw [hl] at hl'; exact (Expr.ref.inj (Option.some.inj hl')).symm
      subst hxx
      have h1 : netIn ck cs ins F t p.name = F t p.name := by simp [netIn, hd]
      rw [h1, ← hEx']
      simp [insCOf, hl, hE, evalExpr]
    · have hxin : x ∈ inNames m := hx.resolve_left hd
      have hEx := runHS_inputs d arr m hA hwr ins K K (Nat.le_refl K) _ envs sts hrun t ht E hE x hxin
      have hd' : ck.dataInputs.any (·.name == p.name) = false := by simpa using hd
      simp [netIn, hd', insCIn, insCOf, hl, hE, evalExpr, hEx]
  have hseed : ∀ j, j < K → seedFwd c K (insCOf (declWidth m) cs envs) j =
      seedFwd c K (netIn ck cs ins F) j := by
    intro j hj
    funext st n
    simp only [seedFwd]
    by_cases hn : (c.inputs.map (·.name)).contains n = true
    · rw [if_pos hn, if_pos hn]
      obtain ⟨E, Ec, S, Sc, hE, _⟩ := hcorr (K - 1 - j) (by omega)
      exact (hpre _ (by omega) E hE n (List.contains_iff_mem.mp hn)).symm
    · rw [if_neg hn, if_neg hn]
  obtain ⟨envs', hrun', hall⟩ := hout (arr c) hperm.1 hperm.2 (netIn ck cs ins F) hok' K
  have hcongr := runModule_congr_seed (declWidth c) (arr c)
    (seedFwd c K (insCOf (declWidth m) cs envs)) (seedFwd c K (netIn ck cs ins F)) K hseed
    (st0Of c) (fun _ _ => 0)
  rw [hcongr, hst0, hrun'] at hrunR
  have hce : envs' = cenvs := Option.some.inj hrunR
  intro t ht E hE q hq
  obtain ⟨E0, Ec, S, Sc, hE0, hEc, _, _, hproj⟩ := hcorr t ht
  have hEE : E = E0 := Option.some.inj (hE.symm.trans hE0)
  subst hEE
  obtain ⟨x, hl, hxv⟩ := hproj.2.1 q hq
  refine ⟨x, hl, ?_⟩
  have hqk : q ∈ ck.outputs := by rw [← hcore.2.2.2.2.2.1]; exact hq
  obtain ⟨env, he, hv⟩ := hall t ht q hqk
  rw [hce, hEc] at he
  have hee : env = Ec := (Option.some.inj he).symm
  subst hee
  rw [hxv]; exact hv

/-! copied from Tools/VedU2HierReg.lean (`outputsOnHS_of_stepR`): the shape hypothesis is `HierShapeK` -/

theorem outputsOnHS_of_stepR_multi (c : Contract) (m : Module) (d : Design)
    (arr : Module → List Stmt) (f : c.table.Ty)
    (hS : HierShapeK d m = true) (hA : AdmArr d m arr)
    (hsupp : ExprsSupp m (arr m)) (hch : ∀ x ∈ d.modules, ChildSucc x (arr x))
    (b0 : List Stmt) (hp : (arr m).Perm b0) (hw0 : WOH d b0) (hnd : (regOuts b0).Nodup)
    (hai0 : ∀ s ∈ b0, isAsgInstReg s = true)
    (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (hkid : ∀ ins, InputsOk c m ins → ∀ K envs sts,
      runHSTrace d arr m (seedFwd m K ins) K (st0H d m) = some (envs, sts) →
      ∀ mn i cs, Stmt.inst mn i cs ∈ m.body → ∀ t, t < K → ∀ E, envs[t]? = some E →
        ∀ y ∈ instOuts d mn cs, E y = Ow ins y t)
    (R : (Nat → String → Nat) → Nat → (String → Nat) → Prop)
    (h0 : ∀ ins, InputsOk c m ins → R ins 0 (st0Of m))
    (hstep : ∀ ins, InputsOk c m ins → ∀ t p, R ins t p →
      ∃ E nx, evalAssignsI (declWidth m) (oracleIE d (fun y => Ow ins y t)) b0
          (seedIn m ins t (restrictTo (regOuts b0) p)) = some E ∧
        regNexts (declWidth m) (fun _ _ => 0) b0 E = some nx ∧
        (∀ o ∈ c.outputs, E o.name = srcOf c f ins o.name t) ∧
        R ins (t + 1) (applyNexts p nx)) :
    OutputsOnHS c m d arr f := by
  intro ins hok K
  obtain ⟨envs, sts, hrun⟩ := runHS_exists_multi d arr m hS hA hsupp hch (seedFwd m K ins) K (st0H d m)
  refine ⟨envs, ?_, ?_⟩
  · have := runHSTrace_fst d arr m (seedFwd m K ins) K (st0H d m)
    rw [hrun] at this
    simp at this
    exact this.symm
  -- one cycle: the closed run's cycle is the open fold, so `hstep` applies
  have cyc : ∀ t, t < K → ∀ S E, sts[t]? = some S → envs[t]? = some E → R ins t (S []) →
      (∀ o ∈ c.outputs, E o.name = srcOf c f ins o.name t) ∧
      ∀ nx, regNexts (declWidth m) (fun _ _ => 0) (arr m) E = some nx →
        R ins (t + 1) (applyNexts (S []) nx) := by
    intro t ht S E hS' hE' hR
    obtain ⟨E', S', hE2, hS2, hfold⟩ := runHSTrace_cycle d arr m (seedFwd m K ins) K (st0H d m)
      envs sts hrun t ht
    rw [hE'] at hE2; rw [hS'] at hS2
    cases hE2; cases hS2
    have hseed : seedFwd m K ins (K - 1 - t) (restrictTo (regOuts (arr m)) (S []))
        = seedIn m ins t (restrictTo (regOuts b0) (S [])) := by
      rw [restrictTo_perm hp]
      exact seedFwd_time m K ins ht _
    rw [hseed] at hfold
    have hfold0 := evalAssignsI_perm d _ _ (instEvalS_laws d arr S (declWidth m)) hp hA.2.1 hw0 hfold
    have hmem : ∀ s, s ∈ b0 → s ∈ m.body := fun s hs => hA.1.mem_iff.mp (hp.mem_iff.mpr hs)
    have hor := fold_oracle d _ _ (instEvalS_laws d arr S (declWidth m)) (fun y => Ow ins y t) b0 _ E
      hw0 hfold0 (fun mn i cs hin y hy => hkid ins hok K envs sts hrun mn i cs (hmem _ hin) t ht E hE' y hy)
    obtain ⟨E1, nx1, hE1, hn1, hout, hR'⟩ := hstep ins hok t (S []) hR
    rw [hE1] at hor
    cases hor
    refine ⟨hout, ?_⟩
    intro nx hnx
    have hperm : nx.Perm nx1 := by
      have := regNexts_perm (declWidth m) (fun _ _ => 0) E hp
      rw [hnx, hn1] at this
      simpa [OPerm] using this
    have hkeys : (nx1.map Prod.fst).Nodup := by
      rw [regNexts_keys _ _ _ b0 nx1 hn1, nextKeys_eq_regOuts b0 hai0]; exact hnd
    have heq : applyNexts (S []) nx = applyNexts (S []) nx1 :=
      applyNexts_perm hperm ((hperm.map Prod.fst).nodup_iff.mpr hkeys) _
    rw [heq]; exact hR'
  -- the invariant along the trace
  have chain : ∀ t, t < K → ∃ S, sts[t]? = some S ∧ R ins t (S []) := by
    intro t
    induction t with
    | zero =>
      intro ht
      obtain ⟨hs0, _⟩ := runHSTrace_next d arr m (seedFwd m K ins) K (st0H d m) envs sts hrun
      exact ⟨st0H d m, hs0 ht, h0 ins hok⟩
    | succ t ih =>
      intro ht
      obtain ⟨S, hS', hR⟩ := ih (by omega)
      obtain ⟨_, hnx⟩ := runHSTrace_next d arr m (seedFwd m K ins) K (st0H d m) envs sts hrun
      obtain ⟨E, S2, S3, nx, hE2, hS2, hS3, hnx2, hS3r⟩ := hnx t ht
      rw [hS'] at hS2; cases hS2
      refine ⟨S3, hS3, ?_⟩
      rw [hS3r]
      exact (cyc t (by omega) S E hS' hE2 hR).2 nx hnx2
  intro t ht o ho
  obtain ⟨S, hS', hR⟩ := chain t ht
  obtain ⟨E, S2, hE2, hS2, _⟩ := runHSTrace_cycle d arr m (seedFwd m K ins) K (st0H d m) envs sts hrun t ht
  rw [hS'] at hS2; cases hS2
  exact ⟨E, hE2, (cyc t ht S E hS' hE2 hR).1 o ho⟩


/-! copied from Tools/VedU2HierState.lean (`outputsOnHS_of_stepRK`): the shape hypothesis is `HierShapeK` -/

theorem outputsOnHS_of_stepRK_multi (c : Contract) (m : Module) (d : Design)
    (arr : Module → List Stmt) (f : c.table.Ty)
    (hS : HierShapeK d m = true) (hA : AdmArr d m arr)
    (hsupp : ExprsSupp m (arr m)) (hch : ∀ x ∈ d.modules, ChildSucc x (arr x))
    (b0 : List Stmt) (hp : (arr m).Perm b0) (hw0 : WOH d b0) (hnd : (regOuts b0).Nodup)
    (hai0 : ∀ s ∈ b0, isAsgInstReg s = true)
    (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (R : (Nat → String → Nat) → Nat → (String → Nat) → Prop)
    (h0 : ∀ ins, InputsOk c m ins → R ins 0 (st0Of m))
    (hkid : ∀ ins, InputsOk c m ins → ∀ K envs sts,
      runHSTrace d arr m (seedFwd m K ins) K (st0H d m) = some (envs, sts) →
      ∀ t, t < K → ∀ S E, sts[t]? = some S → envs[t]? = some E → R ins t (S []) →
        ∀ mn i cs, Stmt.inst mn i cs ∈ m.body → ∀ y ∈ instOuts d mn cs, E y = Ow ins y t)
    (hstep : ∀ ins, InputsOk c m ins → ∀ t p, R ins t p →
      ∃ E nx, evalAssignsI (declWidth m) (oracleIE d (fun y => Ow ins y t)) b0
          (seedIn m ins t (restrictTo (regOuts b0) p)) = some E ∧
        regNexts (declWidth m) (fun _ _ => 0) b0 E = some nx ∧
        (∀ o ∈ c.outputs, E o.name = srcOf c f ins o.name t) ∧
        R ins (t + 1) (applyNexts p nx)) :
    OutputsOnHS c m d arr f := by
  intro ins hok K
  obtain ⟨envs, sts, hrun⟩ := runHS_exists_multi d arr m hS hA hsupp hch (seedFwd m K ins) K (st0H d m)
  refine ⟨envs, ?_, ?_⟩
  · have := runHSTrace_fst d arr m (seedFwd m K ins) K (st0H d m)
    rw [hrun] at this
    simp at this
    exact this.symm
  -- one cycle: the closed run's cycle is the open fold, so `hstep` applies
  have cyc : ∀ t, t < K → ∀ S E, sts[t]? = some S → envs[t]? = some E → R ins t (S []) →
      (∀ o ∈ c.outputs, E o.name = srcOf c f ins o.name t) ∧
      ∀ nx, regNexts (declWidth m) (fun _ _ => 0) (arr m) E = some nx →
        R ins (t + 1) (applyNexts (S []) nx) := by
    intro t ht S E hS' hE' hR
    obtain ⟨E', S', hE2, hS2, hfold⟩ := runHSTrace_cycle d arr m (seedFwd m K ins) K (st0H d m)
      envs sts hrun t ht
    rw [hE'] at hE2; rw [hS'] at hS2
    cases hE2; cases hS2
    have hseed : seedFwd m K ins (K - 1 - t) (restrictTo (regOuts (arr m)) (S []))
        = seedIn m ins t (restrictTo (regOuts b0) (S [])) := by
      rw [restrictTo_perm hp]
      exact seedFwd_time m K ins ht _
    rw [hseed] at hfold
    have hfold0 := evalAssignsI_perm d _ _ (instEvalS_laws d arr S (declWidth m)) hp hA.2.1 hw0 hfold
    have hmem : ∀ s, s ∈ b0 → s ∈ m.body := fun s hs => hA.1.mem_iff.mp (hp.mem_iff.mpr hs)
    have hor := fold_oracle d _ _ (instEvalS_laws d arr S (declWidth m)) (fun y => Ow ins y t) b0 _ E
      hw0 hfold0 (fun mn i cs hin y hy => hkid ins hok K envs sts hrun t ht S E hS' hE' hR mn i cs (hmem _ hin) y hy)
    obtain ⟨E1, nx1, hE1, hn1, hout, hR'⟩ := hstep ins hok t (S []) hR
    rw [hE1] at hor
    cases hor
    refine ⟨hout, ?_⟩
    intro nx hnx
    have hperm : nx.Perm nx1 := by
      have := regNexts_perm (declWidth m) (fun _ _ => 0) E hp
      rw [hnx, hn1] at this
      simpa [OPerm] using this
    have hkeys : (nx1.map Prod.fst).Nodup := by
      rw [regNexts_keys _ _ _ b0 nx1 hn1, nextKeys_eq_regOuts b0 hai0]; exact hnd
    have heq : applyNexts (S []) nx = applyNexts (S []) nx1 :=
      applyNexts_perm hperm ((hperm.map Prod.fst).nodup_iff.mpr hkeys) _
    rw [heq]; exact hR'
  -- the invariant along the trace
  have chain : ∀ t, t < K → ∃ S, sts[t]? = some S ∧ R ins t (S []) := by
    intro t
    induction t with
    | zero =>
      intro ht
      obtain ⟨hs0, _⟩ := runHSTrace_next d arr m (seedFwd m K ins) K (st0H d m) envs sts hrun
      exact ⟨st0H d m, hs0 ht, h0 ins hok⟩
    | succ t ih =>
      intro ht
      obtain ⟨S, hS', hR⟩ := ih (by omega)
      obtain ⟨_, hnx⟩ := runHSTrace_next d arr m (seedFwd m K ins) K (st0H d m) envs sts hrun
      obtain ⟨E, S2, S3, nx, hE2, hS2, hS3, hnx2, hS3r⟩ := hnx t ht
      rw [hS'] at hS2; cases hS2
      refine ⟨S3, hS3, ?_⟩
      rw [hS3r]
      exact (cyc t (by omega) S E hS' hE2 hR).2 nx hnx2
  intro t ht o ho
  obtain ⟨S, hS', hR⟩ := chain t ht
  obtain ⟨E, S2, hE2, hS2, _⟩ := runHSTrace_cycle d arr m (seedFwd m K ins) K (st0H d m) envs sts hrun t ht
  rw [hS'] at hS2; cases hS2
  exact ⟨E, hE2, (cyc t ht S E hS' hE2 hR).1 o ho⟩


/-! copied from Tools/VedU2HierStep.lean (`kid_step`): the shape hypothesis is `HierShapeK` -/

theorem kid_step_multi (d : Design) (arr : Module → List Stmt) (m : Module)
    (hS : HierShapeK d m = true) (hA : AdmArr d m arr)
    (hwr : ∀ n ∈ wrsH d (arr m), n ∉ inNames m)
    (cc : Contract) (htie : cc.clkRst = designClkRst d m)
    (ins : Nat → String → Nat) (hok : InputsOk cc m ins) (K : Nat) (envs : List Env)
    (sts : List HSt)
    (hrun : runHSTrace d arr m (seedFwd m K ins) K (st0H d m) = some (envs, sts))
    (mn i : String) (cs : List (String × Expr)) (hin : Stmt.inst mn i cs ∈ m.body)
    (c : Module) (hf : findMod d mn = some c) (hcomb : asgOnly c.body = true)
    (ck : Contract) (g : ck.table.Ty) (hU : U1Stmt ck c g)
    (hclkc : ck.clkRst = regClkRst c.body)
    (hconn : ∀ p ∈ c.inputs, ∃ x, cs.lookup p.name = some (Expr.ref x) ∧
      (ck.dataInputs.any (·.name == p.name) = true ∨ x ∈ inNames m))
    (hrstnd : ∀ kr, ck.clkRst = some kr → ck.dataInputs.any (·.name == kr.2) = false)
    (F : Nat → String → Nat)
    (hrange : ∀ t, ∀ p ∈ ck.dataInputs, F t p.name < 2 ^ declWidth c p.name)
    (t : Nat) (ht : t < K) (E : Env) (hE : envs[t]? = some E)
    (hrunF : ∀ p ∈ ck.dataInputs,
      ∃ x, cs.lookup p.name = some (Expr.ref x) ∧ E x = F t p.name) :
    ∀ q ∈ c.outputs,
      ∃ x, cs.lookup q.name = some (Expr.ref x) ∧
        E x = srcOf ck g (netIn ck cs ins F) q.name t := by
  obtain ⟨c', cenvs, cstates, hf', hrunM, hrunR, hcorr⟩ :=
    runHS_proj_multi d arr m hS hA ins K envs sts hrun mn i cs hin
  have hcc : c = c' := by rw [hf] at hf'; exact Option.some.inj hf'
  subst hcc
  obtain ⟨_, ⟨hcore, _⟩, _, _, hout⟩ := hU
  have hperm := hA.2.2 c (findMod_mem hf)
  have hinits : (regsOf c.body).map (fun r => (r.1, r.2.2.2)) = ck.inits := hcore.2.2.2.2.2.2.2.1
  have hst0 : st0Of c = st0 ck c := st0Of_eq_st0 ck c hinits
  have hasg : asgOnly (arr c) = true := asgOnly_perm hperm.1.symm hcomb
  -- the child stream is in range
  have hok' : InputsOk ck c (netIn ck cs ins F) := by
    refine ⟨?_, ?_⟩
    · intro t p hp
      have hd : ck.dataInputs.any (·.name == p.name) = true :=
        List.any_eq_true.mpr ⟨p, hp, by simp⟩
      have h1 : netIn ck cs ins F t p.name = F t p.name := by simp [netIn, hd]
      rw [h1]
      exact hrange t p hp
    · intro t kr hkr
      rw [hclkc] at hkr
      have hreg : regsOf c.body ≠ [] := by
        intro h0; simp [regClkRst, h0] at hkr
      obtain ⟨x, y, kc, kr', hrc, h1, h2, hcl, hx, hy, hne, hkc, hkr2⟩ :=
        instPair_tie d m (hierK_clk hS) mn i cs c hin hf hreg cc htie
      have hkk : (kc, kr') = kr := Option.some.inj (hrc.symm.trans hkr)
      subst hkk
      have hnd := hrstnd (kc, kr') (hclkc.trans hrc)
      have : netIn ck cs ins F t kr' = ins t y := by simp [netIn, hnd, insCIn, h2]
      show netIn ck cs ins F t kr' = 0
      rw [this]
      exact hok.2 t (x, y) hcl
  -- the seeds agree at the cycle `t`
  have hpre : ∀ n ∈ inNames c, netIn ck cs ins F t n = insCOf (declWidth m) cs envs t n := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    obtain ⟨x, hl, hx⟩ := hconn p hp
    by_cases hd : ck.dataInputs.any (·.name == p.name) = true
    · obtain ⟨p', hp', hpn⟩ := List.any_eq_true.mp hd
      have hpn' : p'.name = p.name := by simpa using hpn
      obtain ⟨x', hl', hEx'⟩ := hrunF p' hp'
      rw [hpn'] at hl' hEx'
      have hxx : x' = x := by
        rw [hl] at hl'; exact (Expr.ref.inj (Option.some.inj hl')).symm
      subst hxx
      have h1 : netIn ck cs ins F t p.name = F t p.name := by simp [netIn, hd]
      rw [h1, ← hEx']
      simp [insCOf, hl, hE, evalExpr]
    · have hxin : x ∈ inNames m := hx.resolve_left hd
      have hEx := runHS_inputs d arr m hA hwr ins K K (Nat.le_refl K) _ envs sts hrun t ht E hE x hxin
      have hd' : ck.dataInputs.any (·.name == p.name) = false := by simpa using hd
      simp [netIn, hd', insCIn, insCOf, hl, hE, evalExpr, hEx]
  have hs : seedFwd c K (insCOf (declWidth m) cs envs) (K - 1 - t) (st0Of c) =
      seedFwd c K (netIn ck cs ins F) (K - 1 - t) (st0Of c) := by
    funext n
    simp only [seedFwd]
    by_cases hn : (c.inputs.map (·.name)).contains n = true
    · rw [if_pos hn, if_pos hn]
      have h : K - 1 - (K - 1 - t) = t := by omega
      rw [h]
      exact (hpre n (List.contains_iff_mem.mp hn)).symm
    · rw [if_neg hn, if_neg hn]
  obtain ⟨envs', hrun', hall⟩ := hout (arr c) hperm.1 hperm.2 (netIn ck cs ins F) hok' K
  rw [← hst0] at hrun'
  have hloc := runModule_asg_local (declWidth c) (arr c) hasg
    (seedFwd c K (insCOf (declWidth m) cs envs)) (seedFwd c K (netIn ck cs ins F)) (fun _ _ => 0)
    (st0Of c) K cenvs envs' hrunR hrun' t ht hs
  intro q hq
  obtain ⟨E0, Ec, S, Sc, hE0, hEc, _, _, hproj⟩ := hcorr t ht
  have hEE : E = E0 := Option.some.inj (hE.symm.trans hE0)
  subst hEE
  obtain ⟨x, hl, hxv⟩ := hproj.2.1 q hq
  refine ⟨x, hl, ?_⟩
  have hqk : q ∈ ck.outputs := by rw [← hcore.2.2.2.2.2.1]; exact hq
  obtain ⟨env, he, hv⟩ := hall t ht q hqk
  rw [← hloc, hEc] at he
  have hee : env = Ec := (Option.some.inj he).symm
  subst hee
  rw [hxv]; exact hv

end Tools.VedU2Hier

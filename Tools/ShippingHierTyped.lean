import Tools.ShippingHierOptRunH

/-! # Width-typed linked runs

`fitX_of_runH` bounds the instance-driven wires of a linked run by a
syntactic mask on the child's output (`kidsMasked`: a constant or a slice).
A child the certified gate compiles drives its output port by a plain alias
(`out = _gen_out`, a mux of its inputs), so its outputs are bounded only
because everything it computes is: the run is WIDTH-TYPED. Every assignment
reads no output port and has the width of the name it writes (`widthOk`,
`widthOf r = we l`), each output port is assigned once by an expression no
wider than the port, each instance's inputs read parent wires no wider than
the child's ports and its outputs drive wires at least as wide. Then, from
inputs and a state that fit, every value of the run off the output ports
fits its declared width (`runModuleH_typed`), and in particular the
extracted inputs of the optimizer check do (`fitX_of_typed`). -/
namespace Tools.ShippingHierTyped
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.Reorder (refsOf evalExpr_congr writesOf stmtWrites)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingMachineLinked
open Tools.ShippingSeqOptSoundness (seedIn)

/-- Every name off `X` fits its width. -/
def BoundOff (we : WEnv) (X : List String) (env : Env) : Prop :=
  ∀ n, n ∉ X → env n < 2 ^ we n

/-- `r` reads no name of `X`. -/
def avoids (X : List String) (r : Expr) : Bool :=
  (refsOf r).all fun n => !X.contains n

theorem evalExpr_boundOff {we : WEnv} {X : List String} {env : Env} {r : Expr} {v : Nat}
    (hb : BoundOff we X env) (ha : avoids X r = true) (hok : Tools.ConeFold.widthOk we r = true)
    (hv : evalExpr we env r = some v) : v < 2 ^ widthOf we r := by
  let env' : Env := fun n => if n ∈ X then 0 else env n
  have hc : evalExpr we env r = evalExpr we env' r := by
    apply evalExpr_congr
    intro n hn
    have : n ∉ X := by
      have := List.all_eq_true.mp ha n hn
      simpa [List.contains_eq_mem] using this
    simp [env', this]
  rw [hc] at hv
  refine Tools.ConeFold.evalExpr_bounded we env' (fun n => ?_) r v hok hv
  by_cases hn : n ∈ X
  · simp [env', hn, Nat.two_pow_pos]
  · simp only [env', hn, if_false]; exact hb n hn

/-- An assignment of a width-typed body. -/
def assignTyped (we : WEnv) (X : List String) (l : String) (r : Expr) : Bool :=
  avoids X r && Tools.ConeFold.widthOk we r && (X.contains l || widthOf we r == we l)

/-- A statement of a width-typed child body (assignments typed, no memory). -/
def childStmtTyped (we : WEnv) (X : List String) : Stmt → Bool
  | .assign l r => assignTyped we X l r
  | .memory .. => false
  | _ => true

theorem boundOff_write {we : WEnv} {X : List String} {env : Env} {l : String} {r : Expr} {v : Nat}
    (hb : BoundOff we X env) (ht : assignTyped we X l r = true) (hv : evalExpr we env r = some v) :
    BoundOff we X (fun n => if n = l then v else env n) := by
  simp only [assignTyped, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.contains_eq_mem, decide_eq_true_eq] at ht
  obtain ⟨⟨ha, hok⟩, hl⟩ := ht
  intro n hn
  by_cases he : n = l
  · subst he
    simp only [if_true]
    rcases hl with hl | hl
    · exact absurd hl hn
    · rw [← hl]; exact evalExpr_boundOff hb ha hok hv
  · simp only [he, if_false]; exact hb n hn

/-- **A width-typed child fold** keeps the names off `X` within their widths,
and a name assigned once ends with its expression's value on such an
environment. -/
theorem evalAssigns_typed (we : WEnv) (mems : MEnv) (X : List String) :
    ∀ (body : List Stmt) (env0 env1 : Env), evalAssigns we mems body env0 = some env1 →
      body.all (childStmtTyped we X) = true → BoundOff we X env0 →
      BoundOff we X env1 ∧
      ∀ l r, Stmt.assign l r ∈ body → (writesOf body).count l = 1 →
        ∃ env, BoundOff we X env ∧ evalExpr we env r = some (env1 l)
  | [], env0, env1, h, _, hb => by
    simp only [evalAssigns, Option.some.injEq] at h
    subst h
    exact ⟨hb, fun _ _ hm => by cases hm⟩
  | st :: rest, env0, env1, h, ht, hb => by
    simp only [List.all_cons, Bool.and_eq_true] at ht
    obtain ⟨hst, hrest⟩ := ht
    cases st with
    | assign l' r' =>
      simp only [evalAssigns] at h
      cases hv : evalExpr we env0 r' with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, Option.bind_eq_bind, Option.bind_some] at h
        have hb' := boundOff_write hb hst hv
        obtain ⟨hB, hO⟩ := evalAssigns_typed we mems X rest _ env1 h hrest hb'
        refine ⟨hB, fun l r hm hc => ?_⟩
        have hcount : (writesOf (Stmt.assign l' r' :: rest)).count l =
            (if l' = l then 1 else 0) + (writesOf rest).count l := by
          simp only [writesOf, List.flatMap_cons, stmtWrites, List.count_append, List.count_singleton]
          by_cases he : l' = l <;> simp [he, beq_iff_eq]
        rw [hcount] at hc
        by_cases he : l' = l
        · subst he
          have h0 : (writesOf rest).count l' = 0 := by simp at hc; omega
          have hnot : l' ∉ writesOf rest := List.count_eq_zero.mp h0
          rcases List.mem_cons.mp hm with heq | hin
          · cases heq
            refine ⟨env0, hb, ?_⟩
            have hmf : Tools.ConeFold.memFree rest := by
              clear hO hB h hcount hc hm h0 hnot
              induction rest with
              | nil => trivial
              | cons s rs ih =>
                simp only [List.all_cons, Bool.and_eq_true] at hrest
                cases s <;> simp_all [Tools.ConeFold.memFree, childStmtTyped]
            rw [Tools.ConeFold.evalAssigns_frame we mems rest _ env1 h hmf l' hnot]
            simp [hv]
          · exfalso
            apply hnot
            unfold writesOf
            exact List.mem_flatMap.mpr ⟨_, hin, by simp [stmtWrites]⟩
        · simp only [he, if_false, Nat.zero_add] at hc
          rcases List.mem_cons.mp hm with heq | hin
          · cases heq; exact absurd rfl he
          · exact hO l r hin hc
    | register o c rk i iv =>
      simp only [evalAssigns] at h
      obtain ⟨hB, hO⟩ := evalAssigns_typed we mems X rest env0 env1 h hrest hb
      refine ⟨hB, fun l r hm hc => ?_⟩
      rcases List.mem_cons.mp hm with heq | hin
      · cases heq
      · exact hO l r hin (by simpa [writesOf, stmtWrites] using hc)
    | inst mn iname conns =>
      simp only [evalAssigns] at h
      obtain ⟨hB, hO⟩ := evalAssigns_typed we mems X rest env0 env1 h hrest hb
      refine ⟨hB, fun l r hm hc => ?_⟩
      rcases List.mem_cons.mp hm with heq | hin
      · cases heq
      · exact hO l r hin (by simpa [writesOf, stmtWrites] using hc)
    | memory => simp [childStmtTyped] at hst

/-- A width-typed child: typed statements, each output port assigned once by
an expression no wider than the port. -/
def childTyped (cwe : WEnv) (child : Module) : Bool :=
  child.body.all (childStmtTyped cwe (child.outputs.map (·.name))) &&
  child.outputs.all fun p => (writesOf child.body).count p.name == 1 &&
    child.body.any fun st => match st with
      | .assign l r => l == p.name && decide (widthOf cwe r ≤ p.ty.bitWidth)
      | _ => false

/-- An instance's connections: inputs read parent wires off `Xp` no wider
than the child's ports, outputs drive wires of `Xp` or at least as wide. -/
def connsTyped (W : WEnv) (Xp : List String) (child : Module) (cwe : WEnv)
    (conns : List (String × Expr)) : Bool :=
  (conns.all fun c => (child.outputs.map (·.name)).contains c.1 || match c.2 with
    | .ref w => !Xp.contains w && decide (W w ≤ cwe c.1)
    | _ => true) &&
  child.outputs.all fun p => match conns.lookup p.name with
    | some (.ref w) => Xp.contains w || decide (p.ty.bitWidth ≤ W w)
    | _ => true

/-- A width-typed linked body: typed assignments, typed children with typed
connections, no memory. -/
def kidsTyped (C : String → Option (Module × WEnv)) (W : WEnv) (Xp : List String)
    (body : List Stmt) : Bool :=
  body.all fun st => match st with
    | .assign l r => assignTyped W Xp l r
    | .inst mn _ conns => match C mn with
      | some (child, cwe) => childTyped cwe child && connsTyped W Xp child cwe conns
      | none => false
    | .memory .. => false
    | .register .. => true

theorem lookup_mem' {k : String} {e : Expr} :
    ∀ {l : List (String × Expr)}, l.lookup k = some e → (k, e) ∈ l
  | [], h => by cases h
  | (a, b) :: rest, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      cases h
      have : k = a := by simpa using hk
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem' h)

/-- The child's environment fed by typed connections is bounded off its outputs. -/
theorem connEnv_boundOff {W : WEnv} {Xp : List String} {child : Module} {cwe : WEnv}
    {conns : List (String × Expr)} {env : Env} (hb : BoundOff W Xp env)
    (hc : connsTyped W Xp child cwe conns = true) :
    BoundOff cwe (child.outputs.map (·.name)) (connEnv conns env) := by
  simp only [connsTyped, Bool.and_eq_true] at hc
  intro n hn
  unfold connEnv
  cases hl : conns.lookup n with
  | none => simp [Nat.two_pow_pos]
  | some e =>
    cases e with
    | ref w =>
      simp only
      have h1 := List.all_eq_true.mp hc.1 _ (lookup_mem' hl)
      simp only [List.contains_eq_mem, decide_eq_true_eq, hn, decide_false, Bool.false_or,
        Bool.and_eq_true, Bool.not_eq_true'] at h1
      obtain ⟨hw, hle⟩ := h1
      have hw' : w ∉ Xp := by simpa using hw
      exact Nat.lt_of_lt_of_le (hb w hw') (Nat.pow_le_pow_right (by omega) hle)
    | _ => simp [Nat.two_pow_pos]

/-- `bindOuts` keeps a pointwise property when every written value has it. -/
theorem bindOuts_pres (P : String → Nat → Prop) (conns : List (String × Expr)) (cres : Env) :
    ∀ (outs : List Port) (env : Env), (∀ n, P n (env n)) →
      (∀ p ∈ outs, ∀ w, conns.lookup p.name = some (.ref w) → P w (cres p.name)) →
      ∀ n, P n (bindOuts outs conns cres env n)
  | [], env, h, _, n => h n
  | p :: outs, env, h, hw, n => by
    show P n (bindOuts outs conns cres
      (match conns.lookup p.name with
       | some (.ref w) => fun n => if n = w then cres p.name else env n
       | _ => env) n)
    apply bindOuts_pres P conns cres outs _ ?_ (fun q hq w hl => hw q (List.mem_cons_of_mem _ hq) w hl)
    intro m
    cases hl : conns.lookup p.name with
    | none => exact h m
    | some e =>
      cases e with
      | ref w =>
        show P m (if m = w then cres p.name else env m)
        by_cases he : m = w
        · subst he; simp only [if_true]; exact hw p List.mem_cons_self m hl
        · simp only [he, if_false]; exact h m
      | _ => exact h m

/-- **The width-typed linked fold** keeps the parent's names off `Xp` within
their widths. -/
theorem evalAssignsH_typed (W : WEnv) (C : String → Option (Module × WEnv)) (mems : MEnv)
    (Xp : List String) :
    ∀ (body : List Stmt) (env0 env1 : Env), evalAssignsH W C mems body env0 = some env1 →
      kidsTyped C W Xp body = true → BoundOff W Xp env0 → BoundOff W Xp env1
  | [], env0, env1, h, _, hb => by
    simp only [evalAssignsH, Option.some.injEq] at h
    subst h; exact hb
  | st :: rest, env0, env1, h, ht, hb => by
    simp only [kidsTyped, List.all_cons, Bool.and_eq_true] at ht
    obtain ⟨hst, hrest⟩ := ht
    have hrest' : kidsTyped C W Xp rest = true := hrest
    cases st with
    | assign l r =>
      simp only [evalAssignsH] at h
      cases hv : evalExpr W env0 r with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, Option.bind_eq_bind, Option.bind_some] at h
        exact evalAssignsH_typed W C mems Xp rest _ env1 h hrest' (boundOff_write hb hst hv)
    | register o c rk i iv =>
      exact evalAssignsH_typed W C mems Xp rest env0 env1 h hrest' hb
    | memory => simp at hst
    | inst mn iname conns =>
      simp only [evalAssignsH] at h
      cases hC : C mn with
      | none => simp [hC] at h
      | some cp =>
        obtain ⟨child, cwe⟩ := cp
        simp only [hC, Bool.and_eq_true] at hst
        obtain ⟨hct, hcn⟩ := hst
        cases hE : evalAssigns cwe mems child.body (connEnv conns env0) with
        | none => simp [hC, hE] at h
        | some cres =>
          simp only [hC, hE, Option.bind_eq_bind, Option.bind_some] at h
          refine evalAssignsH_typed W C mems Xp rest _ env1 h hrest' ?_
          simp only [childTyped, Bool.and_eq_true] at hct
          obtain ⟨hcb, hco⟩ := hct
          obtain ⟨-, hO⟩ := evalAssigns_typed cwe mems _ child.body _ cres hE hcb
            (connEnv_boundOff hb hcn)
          -- each output port's value fits the port
          have hout : ∀ p ∈ child.outputs, cres p.name < 2 ^ p.ty.bitWidth := by
            intro p hp
            have h1 := List.all_eq_true.mp hco p hp
            simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h1
            obtain ⟨hcount, st', hst', hm⟩ := h1
            cases st' with
            | assign l r =>
              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
              obtain ⟨hl, hwd⟩ := hm
              subst hl
              obtain ⟨env, hbe, hev⟩ := hO _ r hst' hcount
              have ht := List.all_eq_true.mp hcb _ hst'
              simp only [childStmtTyped, assignTyped, Bool.and_eq_true] at ht
              exact Nat.lt_of_lt_of_le (evalExpr_boundOff hbe ht.1.1 ht.1.2 hev)
                (Nat.pow_le_pow_right (by omega) hwd)
            | _ => simp at hm
          simp only [connsTyped, Bool.and_eq_true] at hcn
          exact bindOuts_pres (fun n v => n ∉ Xp → v < 2 ^ W n) conns cres child.outputs env0
            hb (fun p hp w hl hw => by
              have h2 := List.all_eq_true.mp hcn.2 p hp
              simp only [hl, Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h2
              rcases h2 with h2 | h2
              · exact absurd h2 hw
              · exact Nat.lt_of_lt_of_le (hout p hp) (Nat.pow_le_pow_right (by omega) h2))

/-- Register updates are masked at the register's width. -/
theorem regNexts_bounded' {we : WEnv} {mems : MEnv} {envF : Env} :
    ∀ {body : List Stmt} {nexts : List (String × Nat)},
      body.all (fun st => match st with | .memory .. => false | _ => true) = true →
      regNexts we mems body envF = some nexts →
      ∀ pr ∈ nexts, pr.2 < 2 ^ we pr.1
  | [], _, _, h, pr, hpr => by cases h; cases hpr
  | st :: rest, nexts, hok, h, pr, hpr => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    cases st with
    | assign l r => exact regNexts_bounded' hok.2 h pr hpr
    | inst mn iname conns => exact regNexts_bounded' hok.2 h pr hpr
    | memory => simp at hok
    | register o c rr i iv =>
      obtain ⟨rstName, rk⟩ := rr
      simp only [regNexts, Option.bind_eq_bind] at h
      cases hv : evalExpr we envF i with
      | none => rw [hv] at h; cases h
      | some v =>
        rw [hv] at h
        simp only [Option.bind_some] at h
        cases hn : regNexts we mems rest envF with
        | none => rw [hn] at h; cases h
        | some rests =>
          rw [hn] at h
          simp only [Option.bind_some, Option.some.injEq] at h
          subst h
          rcases List.mem_cons.mp hpr with hpr | hpr
          · subst hpr
            by_cases hz : envF rstName ≠ 0
            · rw [if_pos hz]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
            · rw [if_neg hz]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
          · exact regNexts_bounded' hok.2 hn pr hpr

theorem kidsTyped_noMem {C : String → Option (Module × WEnv)} {W : WEnv} {Xp : List String} :
    ∀ {body : List Stmt}, kidsTyped C W Xp body = true →
      body.all (fun st => match st with | .memory .. => false | _ => true) = true
  | [], _ => rfl
  | st :: rest, h => by
    simp only [kidsTyped, List.all_cons, Bool.and_eq_true] at h ⊢
    refine ⟨?_, kidsTyped_noMem (body := rest) h.2⟩
    cases st <;> simp_all

/-- **A width-typed linked run** keeps every cycle's environment within the
declared widths off `Xp`, from seeds that do and a state that does. -/
theorem runModuleH_typed (W : WEnv) (C : String → Option (Module × WEnv)) (body : List Stmt)
    (Xp : List String) (seed : Nat → (String → Nat) → Env) (ht : kidsTyped C W Xp body = true)
    (hseed : ∀ t st, BoundOff W Xp st → BoundOff W Xp (seed t st)) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      runModuleH W C body seed k st mems = some envs → BoundOff W Xp st →
      ∀ j (hj : j < envs.length), BoundOff W Xp (envs[j]'hj)
  | 0, _, _, envs, h, _, j, hj => by
    simp only [runModuleH, Option.some.injEq] at h; subst h; cases hj
  | k + 1, st, mems, envs, h, hst, j, hj => by
    simp only [runModuleH] at h
    cases hS : stepModuleH W C body (seed k st) mems with
    | none => simp [hS] at h
    | some r =>
    obtain ⟨envF, nexts, mems', hF, hN, hM, rfl⟩ := Tools.ShippingHierOptRunH.stepModuleH_some hS
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleH W C body seed k (applyNexts st nexts) mems' with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    cases j with
    | zero => exact evalAssignsH_typed W C mems Xp body _ envF hF ht (hseed k st hst)
    | succ j =>
      refine runModuleH_typed W C body Xp seed ht hseed k _ mems' rest hR ?_ j
        (by simpa using hj)
      have hnb := regNexts_bounded' (kidsTyped_noMem ht) hN
      intro n hn
      simp only [applyNexts]
      cases hf : nexts.find? (fun p => p.1 == n) with
      | none => exact hst n hn
      | some pr =>
        have hmem := List.mem_of_find?_eq_some hf
        have hpred := List.find?_some hf
        simp only [beq_iff_eq] at hpred
        have hb := hnb pr hmem
        rw [hpred] at hb
        exact hb

/-- The decidable typing of a module with combinational children: its body
width-typed off its output ports, and no output port among the extracted
inputs of the optimizer check. -/
def hierTyped (C : String → Option (Module × WEnv)) (m : Module) : Bool :=
  kidsTyped C (declWidth m) (m.outputs.map (·.name)) m.body &&
  (Sparkle.IR.HierCheck.openIns m).all fun p => !(m.outputs.map (·.name)).contains p.name

/-- **The extracted inputs fit**, on a width-typed module, from inputs that
fit and an initial state that fits off the output ports. -/
theorem fitX_of_typed (ms : List Module) (m : Module) (ins : Nat → String → Nat)
    (hty : hierTyped (childMap ms) m = true)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    {T : Nat} {st : String → Nat} {mems : MEnv} {envs : List Env}
    (hrun : runModuleH (declWidth m) (childMap ms) m.body (seedIn m ins) T st mems = some envs)
    (hst : BoundOff (declWidth m) (m.outputs.map (·.name)) st) :
    ∀ j (hj : j < envs.length), ∀ x ∈ (Sparkle.IR.HierCheck.openIns m).map (·.name),
      (envs[j]'hj) x < 2 ^ declWidth m x := by
  simp only [hierTyped, Bool.and_eq_true] at hty
  have hB := runModuleH_typed (declWidth m) (childMap ms) m.body _ (seedIn m ins) hty.1
    (fun t st hb n hn => by
      simp only [seedIn]
      split
      · rename_i hi
        exact hinsFit t n (by simpa [List.contains_eq_mem] using hi)
      · exact hb n hn) T st mems envs hrun hst
  intro j hj x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have h2 := List.all_eq_true.mp hty.2 p hp
  exact hB j hj p.name (by simpa [List.contains_eq_mem] using h2)

end Tools.ShippingHierTyped

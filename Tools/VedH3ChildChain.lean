import Sparkle.IR.Semantics
import Sparkle.Core.Signal
import Tools.ConeFoldMem

/-!
# Chains of one's-complement 16-bit add stages (issue sparkle-ved-hier3-child)

`tcpHeaderChecksumSig` (and every checksum written with `IPv4.onesAdd16Sig`) is a chain of stages, each
the 7 statements of `Stg` (zero-extend both words to 17 bits, add, low 16 bits, carry bit, carry zero-extended,
add).  The generated script of `Tools/VedU1Entry.lean` unfolds the whole body at once: a stage uses its
sum twice, so the unfolded term is a tree of size `2^stages`.  Here each stage is proved ONCE
(`s1_eval`, `s2_eval`: `evalAssigns` of its statements, on any environment satisfying the width and
range hypotheses) and the chain is composed by induction (`chain_eval`): the value after the stages is
`onesAddN` folded over the words, linear in the number of stages.  The Signal side is rewritten stage by
stage with `onesStageSig_toNat`.  Untrusted like the script: the kernel checks everything.
-/

namespace Tools.VedH3ChildChain

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Core.Signal

def onesAddN (a b : Nat) : Nat := ((a + b) % 65536 + (a + b) / 65536) % 65536

structure Stg where
  a17 : String
  b17 : String
  s17 : String
  low : String
  carBit : String
  car16 : String
  s : String
  A : String
  B : String

def Stg.s1 (hi0 : String) (g : Stg) : List Stmt :=
  [ .assign g.a17 (.concat [.ref hi0, .ref g.A]),
    .assign g.b17 (.concat [.ref hi0, .ref g.B]),
    .assign g.s17 (.op .add [.ref g.a17, .ref g.b17]),
    .assign g.low (.slice (.ref g.s17) 15 0),
    .assign g.carBit (.slice (.ref g.s17) 16 16) ]

theorem s1_eval (we : WEnv) (mems : MEnv) (env : Env) (hi0 : String) (g : Stg)
    (hw : we hi0 = 1 ∧ we g.A = 16 ∧ we g.B = 16 ∧ we g.a17 = 17 ∧ we g.b17 = 17)
    (h0 : env hi0 = 0) (hA : env g.A < 2 ^ 16) (hB : env g.B < 2 ^ 16)
    (d1 : g.a17 ≠ hi0 ∧ g.a17 ≠ g.A ∧ g.a17 ≠ g.B)
    (d2 : g.b17 ≠ hi0 ∧ g.b17 ≠ g.B ∧ g.b17 ≠ g.a17)
    (d3 : g.s17 ≠ g.a17 ∧ g.s17 ≠ g.b17)
    (d4 : g.low ≠ g.s17) (d5 : g.carBit ≠ g.s17) (d6 : g.carBit ≠ g.low) :
    ∃ env', evalAssigns we mems (g.s1 hi0) env = some env' ∧
      env' g.low = (env g.A + env g.B) % 65536 ∧ env' g.carBit = (env g.A + env g.B) / 65536 ∧
      (∀ n, n ≠ g.a17 → n ≠ g.b17 → n ≠ g.s17 → n ≠ g.low → n ≠ g.carBit → env' n = env n) := by
  obtain ⟨w0, wA, wB, wa, wb⟩ := hw
  obtain ⟨d1a, d1b, d1c⟩ := d1
  obtain ⟨d2a, d2b, d2c⟩ := d2
  obtain ⟨d3a, d3b⟩ := d3
  have n1 := Ne.symm d1a
  have n2 := Ne.symm d1b
  have n3 := Ne.symm d1c
  have n4 := Ne.symm d2a
  have n5 := Ne.symm d2b
  have n6 := Ne.symm d2c
  have n7 := Ne.symm d3a
  have n8 := Ne.symm d3b
  have n9 := Ne.symm d4
  have n10 := Ne.symm d5
  have n11 := Ne.symm d6
  have hAm : env g.A % 65536 = env g.A := Nat.mod_eq_of_lt hA
  have hBm : env g.B % 65536 = env g.B := Nat.mod_eq_of_lt hB
  simp [Stg.s1, evalAssigns, evalExpr, evalExpr.go, evalList, evalOp, widthOf, w0, wA, wB, wa, wb, h0, mask,
    d1a, d1b, d1c, d2a, d2b, d2c, d3a, d3b, d4, d5, d6, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, Nat.shiftRight_eq_div_pow]
  refine ⟨by omega, ?_⟩
  intro n h1 h2 h3 h4 h5
  simp [h1, h2, h3, h4, h5]

def Stg.s2 (hi1 : String) (g : Stg) : List Stmt :=
  [ .assign g.car16 (.concat [.ref hi1, .ref g.carBit]),
    .assign g.s (.op .add [.ref g.low, .ref g.car16]) ]

theorem s2_eval (we : WEnv) (mems : MEnv) (env : Env) (hi1 : String) (g : Stg)
    (hw : we hi1 = 15 ∧ we g.carBit = 1 ∧ we g.low = 16 ∧ we g.car16 = 16)
    (h1 : env hi1 = 0) (hc : env g.carBit < 2) (hl : env g.low < 2 ^ 16)
    (d1 : g.car16 ≠ hi1 ∧ g.car16 ≠ g.carBit ∧ g.car16 ≠ g.low) (d2 : g.s ≠ g.car16) :
    ∃ env', evalAssigns we mems (g.s2 hi1) env = some env' ∧
      env' g.s = (env g.low + env g.carBit) % 65536 ∧
      (∀ n, n ≠ g.car16 → n ≠ g.s → env' n = env n) := by
  obtain ⟨w1, wc, wl, wr⟩ := hw
  obtain ⟨d1a, d1b, d1c⟩ := d1
  have n1 := Ne.symm d1a
  have n2 := Ne.symm d1b
  have n3 := Ne.symm d1c
  have n4 := Ne.symm d2
  have hcm : env g.carBit % 2 = env g.carBit := Nat.mod_eq_of_lt hc
  have hlm : env g.low % 65536 = env g.low := Nat.mod_eq_of_lt hl
  simp [Stg.s2, evalAssigns, evalExpr, evalExpr.go, evalList, evalOp, widthOf, w1, wc, wl, wr, h1, mask,
    d1a, d1b, d1c, d2, n1, n2, n3, n4]
  refine ⟨by omega, ?_⟩
  intro n h1 h2
  simp [h1, h2]

def Stg.written (g : Stg) : List String := [g.a17, g.b17, g.s17, g.low, g.carBit, g.car16, g.s]

/-- the width and name conditions of one stage -/
def Stg.ok (we : WEnv) (hi0 hi1 : String) (g : Stg) : Prop :=
  (we hi0 = 1 ∧ we g.A = 16 ∧ we g.B = 16 ∧ we g.a17 = 17 ∧ we g.b17 = 17) ∧
  (g.a17 ≠ hi0 ∧ g.a17 ≠ g.A ∧ g.a17 ≠ g.B) ∧ (g.b17 ≠ hi0 ∧ g.b17 ≠ g.B ∧ g.b17 ≠ g.a17) ∧
  (g.s17 ≠ g.a17 ∧ g.s17 ≠ g.b17) ∧ g.low ≠ g.s17 ∧ g.carBit ≠ g.s17 ∧ g.carBit ≠ g.low ∧
  (we hi1 = 15 ∧ we g.carBit = 1 ∧ we g.low = 16 ∧ we g.car16 = 16) ∧
  (g.car16 ≠ hi1 ∧ g.car16 ≠ g.carBit ∧ g.car16 ≠ g.low) ∧ g.s ≠ g.car16 ∧
  hi0 ∉ g.written ∧ hi1 ∉ g.written

/-- one stage: both halves -/
theorem stg_eval (we : WEnv) (mems : MEnv) (env : Env) (hi0 hi1 : String) (g : Stg)
    (hok : g.ok we hi0 hi1) (h0 : env hi0 = 0) (h1 : env hi1 = 0)
    (hA : env g.A < 2 ^ 16) (hB : env g.B < 2 ^ 16) :
    ∃ env', evalAssigns we mems (g.s1 hi0 ++ g.s2 hi1) env = some env' ∧
      env' g.s = onesAddN (env g.A) (env g.B) ∧
      (∀ n, n ∉ g.written → env' n = env n) := by
  obtain ⟨hw1, d1, d2, d3, d4, d5, d6, hw2, d7, d8, hn0, hn1⟩ := hok
  simp only [Stg.written, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn0 hn1
  obtain ⟨hw0, hwA, hwB, hwa, hwb⟩ := hw1
  obtain ⟨e1, e2, e3, e4, e5⟩ := hn0
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hn1
  obtain ⟨env1, hr1, v1, v2, fr1⟩ := s1_eval we mems env hi0 g ⟨hw0, hwA, hwB, hwa, hwb⟩ h0 hA hB d1 d2 d3 d4 d5 d6
  have hcm : (env g.A + env g.B) / 65536 < 2 := by omega
  obtain ⟨env2, hr2, v3, fr2⟩ := s2_eval we mems env1 hi1 g hw2
    (by rw [fr1 hi1 f1 f2 f3 f4 f5]; exact h1)
    (by rw [v2]; exact hcm) (by rw [v1]; exact Nat.mod_lt _ (by omega)) d7 d8
  refine ⟨env2, ?_, ?_, ?_⟩
  · rw [Tools.ConeFold.evalAssigns_append]
    simp only [hr1, Option.bind_eq_bind, Option.bind_some, hr2]
  · rw [v3, v1, v2]
    simp only [onesAddN]
  · intro n hn
    simp only [Stg.written, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
    obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hn
    rw [fr2 n g6 g7, fr1 n g1 g2 g3 g4 g5]

theorem foldl_congr_mem {α β : Type} (f g : α → β → α) :
    ∀ (l : List β) (a : α), (∀ x ∈ l, ∀ a, f a x = g a x) → l.foldl f a = l.foldl g a := by
  intro l
  induction l with
  | nil => intro a _; rfl
  | cons x xs ih =>
    intro a h
    simp only [List.foldl_cons]
    rw [h x List.mem_cons_self a]
    exact ih _ (fun y hy => h y (List.mem_cons_of_mem _ hy))

def chainBody (hi0 hi1 : String) (gs : List Stg) : List Stmt :=
  gs.flatMap fun g => g.s1 hi0 ++ g.s2 hi1

def lastName : String → List Stg → String
  | p, [] => p
  | _, g :: rest => lastName g.s rest

def writtenAll (gs : List Stg) : List String := gs.flatMap Stg.written

def chainOk (we : WEnv) (hi0 hi1 : String) : String → List Stg → Prop
  | _, [] => True
  | prev, g :: rest => g.A = prev ∧ g.ok we hi0 hi1 ∧ chainOk we hi0 hi1 g.s rest

theorem chain_eval (we : WEnv) (mems : MEnv) (hi0 hi1 : String) :
    ∀ (gs : List Stg) (prev : String) (env : Env), chainOk we hi0 hi1 prev gs →
      (∀ g ∈ gs, g.B ∉ writtenAll gs) → env hi0 = 0 → env hi1 = 0 → env prev < 2 ^ 16 →
      (∀ g ∈ gs, env g.B < 2 ^ 16) →
      ∃ env', evalAssigns we mems (chainBody hi0 hi1 gs) env = some env' ∧
        (∀ n, n ∉ writtenAll gs → env' n = env n) ∧
        env' (lastName prev gs) = gs.foldl (fun a g => onesAddN a (env g.B)) (env prev) := by
  intro gs
  induction gs with
  | nil =>
    intro prev env _ _ _ _ _ _
    exact ⟨env, rfl, fun _ _ => rfl, rfl⟩
  | cons g rest ih =>
    intro prev env hok hBW h0 h1 hp hBs
    obtain ⟨hA, hg, hrest⟩ := hok
    have hBg : g.B ∉ writtenAll (g :: rest) := hBW g List.mem_cons_self
    have hwg : g.written ⊆ writtenAll (g :: rest) := by
      intro n hn; simp only [writtenAll, List.flatMap_cons, List.mem_append]; exact Or.inl hn
    have hwr : writtenAll rest ⊆ writtenAll (g :: rest) := by
      intro n hn; simp only [writtenAll, List.flatMap_cons, List.mem_append]; exact Or.inr hn
    have hBgw : g.B ∉ g.written := fun h => hBg (hwg h)
    obtain ⟨env2, hr, v, fr⟩ := stg_eval we mems env hi0 hi1 g hg h0 h1 (hA ▸ hp)
      (hBs g List.mem_cons_self)
    obtain ⟨hw1, d1, d2, d3, d4, d5, d6, hw2, d7, d8, hn0, hn1⟩ := hg
    have hBrest : ∀ g' ∈ rest, g'.B ∉ writtenAll rest := by
      intro g' hg' h
      exact hBW g' (List.mem_cons_of_mem _ hg') (hwr h)
    obtain ⟨env', hr', fr', v'⟩ := ih g.s env2 hrest hBrest
      (by rw [fr hi0 hn0]; exact h0) (by rw [fr hi1 hn1]; exact h1)
      (by rw [v]; simp only [onesAddN]; exact Nat.mod_lt _ (by omega))
      (by
        intro g' hg'
        rw [fr g'.B (fun h => hBW g' (List.mem_cons_of_mem _ hg') (hwg h))]
        exact hBs g' (List.mem_cons_of_mem _ hg'))
    refine ⟨env', ?_, ?_, ?_⟩
    · simp only [chainBody, List.flatMap_cons]
      rw [Tools.ConeFold.evalAssigns_append]
      simp only [hr, Option.bind_eq_bind, Option.bind_some]
      exact hr'
    · intro n hn
      have h1 : n ∉ writtenAll rest := fun h => hn (hwr h)
      have h2 : n ∉ g.written := fun h => hn (hwg h)
      rw [fr' n h1, fr n h2]
    · simp only [lastName, List.foldl_cons]
      rw [v', v, hA]
      apply foldl_congr_mem
      intro g' hg' a
      rw [fr g'.B (fun h => hBW g' (List.mem_cons_of_mem _ hg') (hwg h))]

theorem xor_ones16 : ∀ a, a < 65536 → a ^^^ 65535 = 65535 - a := by
  intro a h
  have e := congrArg BitVec.toNat (BitVec.xor_allOnes (x := BitVec.ofNat 16 a))
  simp only [BitVec.toNat_xor, BitVec.toNat_allOnes, BitVec.toNat_not, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h] at e
  omega

theorem post_eval (we : WEnv) (mems : MEnv) (envC : Env) (sl o1 outn : String)
    (hw : we sl = 16) (hv : envC sl < 65536) (d1 : o1 ≠ sl) (d2 : outn ≠ o1) :
    ∃ envF, evalAssigns we mems
      [.assign o1 (.op .not [.ref sl]), .assign outn (.ref o1)] envC = some envF ∧
      envF outn = 65535 - envC sl := by
  have n1 := Ne.symm d1
  have hx := xor_ones16 _ hv
  have hm : (65535 - envC sl) % 65536 = 65535 - envC sl := Nat.mod_eq_of_lt (by omega)
  simp [evalAssigns, evalExpr, evalList, evalOp, widthOf, hw, mask, d1, d2, n1, hx, hm]

structure CData where
  pre : List Stmt
  g0 : Stg
  hi0 : String
  hi1 : String
  gs : List Stg
  o1 : String
  outn : String

/-- all stages, the first included -/
def CData.stages (D : CData) : List Stg := D.g0 :: D.gs

def CData.lastS (D : CData) : String := lastName D.g0.s D.gs

def CData.body (D : CData) : List Stmt :=
  D.pre ++ (D.g0.s1 D.hi0 ++ [.assign D.hi1 (.const 0 15)] ++ D.g0.s2 D.hi1) ++
    chainBody D.hi0 D.hi1 D.gs ++
    [.assign D.o1 (.op .not [.ref D.lastS]), .assign D.outn (.ref D.o1)]

/-- the conditions on the width environment and the names (decided by the kernel) -/
def CData.ok (D : CData) (we : WEnv) : Prop :=
  D.g0.ok we D.hi0 D.hi1 ∧ chainOk we D.hi0 D.hi1 D.g0.s D.gs ∧
  (∀ g ∈ D.stages, g.B ∉ writtenAll D.stages) ∧ D.hi1 ∉ D.g0.written ∧
  we D.lastS = 16 ∧ D.o1 ≠ D.lastS ∧ D.outn ≠ D.o1 ∧ D.hi0 ≠ D.hi1 ∧
  (∀ g ∈ D.stages, g.B ≠ D.hi1)

/-- the facts about the environment after the prelude -/
def CData.PreFacts (D : CData) (env1 : Env) : Prop :=
  env1 D.hi0 = 0 ∧ env1 D.g0.A < 2 ^ 16 ∧ ∀ g ∈ D.stages, env1 g.B < 2 ^ 16

theorem body_eval (we : WEnv) (mems : MEnv) (D : CData) (hok : D.ok we) (env0 env1 : Env)
    (hpre : evalAssigns we mems D.pre env0 = some env1) (hf : D.PreFacts env1) :
    ∃ envF, evalAssigns we mems D.body env0 = some envF ∧
      envF D.outn = 65535 - D.stages.foldl (fun a g => onesAddN a (env1 g.B)) (env1 D.g0.A) := by
  obtain ⟨hg0, hch, hBW, hh1, hwl, hd1, hd2, hh01, hBh1⟩ := hok
  obtain ⟨h0, hA0, hBs⟩ := hf
  have hg0' := hg0
  obtain ⟨hw1, d1, d2, d3, d4, d5, d6, hw2, d7, d8, hn0, hn1⟩ := hg0'
  have hBg0 : D.g0.B ∈ D.stages.map (·.B) := List.mem_map.2 ⟨D.g0, List.mem_cons_self, rfl⟩
  -- stage 0, the first half, then the constant, then the second half
  have hBsg : ∀ g ∈ D.stages, g.B ∉ writtenAll D.stages := hBW
  have hwg0 : D.g0.written ⊆ writtenAll D.stages := by
    intro n hn; simp only [CData.stages, writtenAll, List.flatMap_cons, List.mem_append]; exact Or.inl hn
  have hwr : writtenAll D.gs ⊆ writtenAll D.stages := by
    intro n hn; simp only [CData.stages, writtenAll, List.flatMap_cons, List.mem_append]; exact Or.inr hn
  simp only [Stg.written, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn0 hn1
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hn0
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hn1
  obtain ⟨hw0, hwA, hwB, hwa, hwb⟩ := hw1
  have hB0 : env1 D.g0.B < 2 ^ 16 := hBs D.g0 List.mem_cons_self
  obtain ⟨env_a, hra, vlow, vcar, fra⟩ :=
    s1_eval we mems env1 D.hi0 D.g0 ⟨hw0, hwA, hwB, hwa, hwb⟩ h0 hA0 hB0 d1 d2 d3 d4 d5 d6
  -- the constant
  let env_b : Env := fun n => if n = D.hi1 then 0 else env_a n
  have hconst : evalAssigns we mems [.assign D.hi1 (.const 0 15)] env_a = some env_b := by
    simp [evalAssigns, evalExpr, mask, env_b]
  have hb1 : env_b D.hi1 = 0 := by simp [env_b]
  have hbf : ∀ n, n ≠ D.hi1 → env_b n = env_a n := by intro n hn; simp [env_b, hn]
  have hblow : env_b D.g0.low = env_a D.g0.low := hbf _ (fun h => f4 h.symm)
  have hbcar : env_b D.g0.carBit = env_a D.g0.carBit := hbf _ (fun h => f5 h.symm)
  obtain ⟨env_c, hrc, vs, frc⟩ := s2_eval we mems env_b D.hi1 D.g0 hw2 hb1
    (by rw [hbcar, vcar]; omega) (by rw [hblow, vlow]; exact Nat.mod_lt _ (by omega)) d7 d8
  have hcA : env_c D.g0.s = onesAddN (env1 D.g0.A) (env1 D.g0.B) := by
    rw [vs, hblow, hbcar, vlow, vcar]; simp only [onesAddN]
  -- frames from env1 to env_c: every name that stage 0 and the constant do not write
  have hfc : ∀ n, n ∉ D.g0.written → n ≠ D.hi1 → env_c n = env1 n := by
    intro n h1 h2
    simp only [Stg.written, List.mem_cons, List.mem_nil_iff, or_false, not_or] at h1
    obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := h1
    rw [frc n g6 g7, hbf n h2, fra n g1 g2 g3 g4 g5]
  have hlt : ∀ (l : List Stg) (a : Nat), a < 65536 →
      l.foldl (fun a g => onesAddN a (env1 g.B)) a < 65536 := by
    intro l
    induction l with
    | nil => intro a h; exact h
    | cons g rest ih =>
      intro a _
      simp only [List.foldl_cons]
      exact ih _ (by simp only [onesAddN]; exact Nat.mod_lt _ (by omega))
  have hBgs : ∀ g ∈ D.gs, g.B ∉ writtenAll D.gs := fun g hg h =>
    hBsg g (List.mem_cons_of_mem _ hg) (hwr h)
  obtain ⟨env_d, hrd, frd, vd⟩ := chain_eval we mems D.hi0 D.hi1 D.gs D.g0.s env_c hch hBgs
    (by rw [hfc D.hi0 (by simp only [Stg.written, List.mem_cons, List.mem_nil_iff, or_false, not_or]; exact ⟨e1, e2, e3, e4, e5, e6, e7⟩) hh01]; exact h0)
    (by rw [frc D.hi1 f6 f7]; exact hb1)
    (by rw [hcA]; simp only [onesAddN]; exact Nat.mod_lt _ (by omega))
    (by
      intro g hg
      rw [hfc g.B (fun h => hBsg g (List.mem_cons_of_mem _ hg) (hwg0 h)) (hBh1 g (List.mem_cons_of_mem _ hg))]
      exact hBs g (List.mem_cons_of_mem _ hg))
  have hv : env_d D.lastS < 65536 := by
    have : env_d D.lastS = D.gs.foldl (fun a g => onesAddN a (env_c g.B)) (env_c D.g0.s) := vd
    rw [this]
    have hc : ∀ (l : List Stg) (a : Nat), a < 65536 →
        l.foldl (fun a g => onesAddN a (env_c g.B)) a < 65536 := by
      intro l
      induction l with
      | nil => intro a h; exact h
      | cons g rest ih =>
        intro a _
        simp only [List.foldl_cons]
        exact ih _ (by simp only [onesAddN]; exact Nat.mod_lt _ (by omega))
    exact hc _ _ (by rw [hcA]; simp only [onesAddN]; exact Nat.mod_lt _ (by omega))
  obtain ⟨envF, hrF, vF⟩ := post_eval we mems env_d D.lastS D.o1 D.outn hwl hv hd1 hd2
  refine ⟨envF, ?_, ?_⟩
  · simp only [CData.body, Tools.ConeFold.evalAssigns_append, hpre, Option.bind_eq_bind, Option.bind_some]
    rw [hra]
    simp only [Option.bind_some]
    rw [hconst]
    simp only [Option.bind_some]
    rw [hrc]
    simp only [Option.bind_some]
    rw [hrd]
    simp only [Option.bind_some]
    exact hrF
  · have vd' : env_d D.lastS = D.gs.foldl (fun a g => onesAddN a (env_c g.B)) (env_c D.g0.s) := vd
    have hfold : D.gs.foldl (fun a g => onesAddN a (env_c g.B)) (env_c D.g0.s) =
        D.stages.foldl (fun a g => onesAddN a (env1 g.B)) (env1 D.g0.A) := by
      simp only [CData.stages, List.foldl_cons]
      rw [hcA]
      apply foldl_congr_mem
      intro g hg a
      rw [hfc g.B (fun h => hBsg g (List.mem_cons_of_mem _ hg) (hwg0 h)) (hBh1 g (List.mem_cons_of_mem _ hg))]
    rw [vF, vd', hfold]

/-! ## The Signal side

`onesStageSig` is a copy of `IPv4.onesAdd16Sig` (the entry checks `IPv4.onesAdd16Sig a b = onesStageSig a b`
by `rfl` before using it); its value at a cycle is `onesBV` of the operands' values, definitionally. -/

def onesBV (a b : BitVec 16) : BitVec 16 :=
  let a17 : BitVec 17 := (0#1 : BitVec 1) ++ a
  let b17 : BitVec 17 := (0#1 : BitVec 1) ++ b
  let s17 : BitVec 17 := a17 + b17
  let low : BitVec 16 := BitVec.extractLsb' 0 16 s17
  let carBit : BitVec 1 := BitVec.extractLsb' 16 1 s17
  let car16 : BitVec 16 := (0#15 : BitVec 15) ++ carBit
  low + car16

@[inline] def onesStageSig {dom : Sparkle.Core.Domain.DomainConfig} (a b : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let a17 : Signal dom (BitVec 17) :=
    (Signal.pure (0#1 : BitVec 1) : Signal dom (BitVec 1)) ++ a
  let b17 : Signal dom (BitVec 17) :=
    (Signal.pure (0#1 : BitVec 1) : Signal dom (BitVec 1)) ++ b
  let s17 : Signal dom (BitVec 17) := a17 + b17
  let low    : Signal dom (BitVec 16) :=
    s17.map (BitVec.extractLsb' 0 16 ·)
  let carBit : Signal dom (BitVec 1)  :=
    s17.map (BitVec.extractLsb' 16 1 ·)
  let car16  : Signal dom (BitVec 16) :=
    (Signal.pure (0#15 : BitVec 15) : Signal dom (BitVec 15)) ++ carBit
  low + car16

theorem onesStageSig_val {dom : Sparkle.Core.Domain.DomainConfig} (a b : Signal dom (BitVec 16)) (t : Nat) :
    (onesStageSig a b).val t = onesBV (a.val t) (b.val t) := rfl

theorem onesBV_toNat (a b : BitVec 16) : (onesBV a b).toNat = onesAddN a.toNat b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [onesBV, onesAddN, BitVec.toNat_add, BitVec.toNat_append, BitVec.extractLsb'_toNat,
    BitVec.toNat_ofNat]
  simp only [Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or, Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow,
    Nat.reducePow, Nat.div_one]
  have hs : (a.toNat + b.toNat) % 131072 = a.toNat + b.toNat := Nat.mod_eq_of_lt (by omega)
  have hq : (a.toNat + b.toNat) / 65536 < 2 := by omega
  have hq2 : (a.toNat + b.toNat) / 65536 % 2 = (a.toNat + b.toNat) / 65536 := Nat.mod_eq_of_lt hq
  rw [hs, hq2]

theorem onesStageSig_toNat {dom : Sparkle.Core.Domain.DomainConfig} (a b : Signal dom (BitVec 16)) (t : Nat) :
    ((onesStageSig a b).val t).toNat = onesAddN (a.val t).toNat (b.val t).toNat := by
  rw [onesStageSig_val, onesBV_toNat]

/-! ## Decidability of the conditions (the kernel decides them for the module at hand) -/

instance (we : WEnv) (hi0 hi1 : String) (g : Stg) : Decidable (g.ok we hi0 hi1) := by
  unfold Stg.ok; infer_instance

def chainOkDec (we : WEnv) (hi0 hi1 : String) :
    (prev : String) → (gs : List Stg) → Decidable (chainOk we hi0 hi1 prev gs)
  | _, [] => isTrue trivial
  | prev, g :: rest =>
    have : Decidable (chainOk we hi0 hi1 g.s rest) := chainOkDec we hi0 hi1 g.s rest
    by unfold chainOk; infer_instance

instance (we : WEnv) (hi0 hi1 : String) (prev : String) (gs : List Stg) :
    Decidable (chainOk we hi0 hi1 prev gs) := chainOkDec we hi0 hi1 prev gs

instance (D : CData) (we : WEnv) : Decidable (D.ok we) := by
  unfold CData.ok; infer_instance

end Tools.VedH3ChildChain

import Tools.VerifiedCircuit

/-! An explicit typed statement language: let, next-state assignment, return,
and a delayed binding (interpreted, but refused by the one-register extractor).
Extraction is a total function, not a Lean.Expr metaprogram. The correspondence
to the shipping Signal runner is proved for every successful extraction. Parsing
or reflecting arbitrary Lean circuit-do definitions is still a separate boundary. -/

namespace Tools.VerifiedSource

open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.VerifiedBlock Tools.VerifiedState Tools.VerifiedCircuit Tools.CertifiedRoundtrip

abbrev Signals (dom : DomainConfig) (Γ : List Nat) :=
  ∀ i : Fin Γ.length, Signal dom (BitVec (Γ.get i))

def pushSignal {dom Γ a} (v : Signal dom (BitVec a)) (ρ : Signals dom Γ) :
    Signals dom (a :: Γ) := Fin.cases v ρ

/-- Capture avoidance when an earlier pending write crosses a let-binding. -/
def weaken {Γ w a} : CExpr Γ w → CExpr (a :: Γ) w
  | .const w v => .const w v
  | .var i => .var (Γ := a :: Γ) i.succ
  | .add x y => .add (weaken x) (weaken y)
  | .sub x y => .sub (weaken x) (weaken y)
  | .mux c x y => .mux (weaken c) (weaken x) (weaken y)
  | .eq x y => .eq (weaken x) (weaken y)
  | .and x y => .and (weaken x) (weaken y)
  | .or x y => .or (weaken x) (weaken y)
  | .xor x y => .xor (weaken x) (weaken y)
  | .mul x y => .mul (weaken x) (weaken y)
  | .shl x y => .shl (weaken x) (weaken y)
  | .shr x y => .shr (weaken x) (weaken y)
  | .lt x y => .lt (weaken x) (weaken y)
  | .le x y => .le (weaken x) (weaken y)
  | .cat x y => .cat (weaken x) (weaken y)
  | .slt x y => .slt (weaken x) (weaken y)
  | .sle x y => .sle (weaken x) (weaken y)
  | .slice x hi lo => .slice (weaken x) hi lo
  | .not x => .not (weaken x)
  | .neg x => .neg (weaken x)

theorem weaken_denote {Γ w a} (e : CExpr Γ w) (ρ : CEnv Γ) (v : BitVec a) :
    (weaken e).denote (pushValue v ρ) = e.denote ρ := by
  induction e <;> simp_all [weaken, CExpr.denote, pushValue]

def lift2 {dom α β γ} (f : α → β → γ) (x : Signal dom α) (y : Signal dom β) :
    Signal dom γ := Signal.map (fun p => f p.1 p.2) (bundle2 x y)

theorem lift2_val {dom α β γ} (f : α → β → γ)
    (x : Signal dom α) (y : Signal dom β) (t : Nat) :
    (lift2 f x y).val t = f (x.val t) (y.val t) := rfl

/-- Independent structural interpretation using shipping Signal combinators. -/
def expression {dom Γ w} (ρ : Signals dom Γ) : CExpr Γ w → Signal dom (BitVec w)
  | .const w v => Signal.pure (BitVec.ofNat w v)
  | .var i => ρ i
  | .add x y => lift2 (· + ·) (expression ρ x) (expression ρ y)
  | .sub x y => lift2 (· - ·) (expression ρ x) (expression ρ y)
  | .mux c x y => Signal.mux (Signal.map (fun v => v == 1#1) (expression ρ c))
      (expression ρ x) (expression ρ y)
  | .eq x y => lift2 (fun a b => if a = b then 1#1 else 0#1) (expression ρ x) (expression ρ y)
  | .and x y => lift2 (· &&& ·) (expression ρ x) (expression ρ y)
  | .or x y => lift2 (· ||| ·) (expression ρ x) (expression ρ y)
  | .xor x y => lift2 (· ^^^ ·) (expression ρ x) (expression ρ y)
  | .mul x y => lift2 (· * ·) (expression ρ x) (expression ρ y)
  | .shl x y => lift2 (fun a b => a <<< b.toNat) (expression ρ x) (expression ρ y)
  | .shr x y => lift2 (fun a b => a >>> b.toNat) (expression ρ x) (expression ρ y)
  | .lt x y => lift2 (fun a b => if a < b then 1#1 else 0#1) (expression ρ x) (expression ρ y)
  | .le x y => lift2 (fun a b => if a ≤ b then 1#1 else 0#1) (expression ρ x) (expression ρ y)
  | .cat x y => lift2 (· ++ ·) (expression ρ x) (expression ρ y)
  | .slt x y => lift2 (fun a b => if a.toInt < b.toInt then 1#1 else 0#1)
      (expression ρ x) (expression ρ y)
  | .sle x y => lift2 (fun a b => if a.toInt ≤ b.toInt then 1#1 else 0#1)
      (expression ρ x) (expression ρ y)
  | .slice x hi lo => Signal.map (fun v => v.extractLsb' lo (hi - lo + 1)) (expression ρ x)
  | .not x => Signal.map (~~~·) (expression ρ x)
  | .neg x => Signal.map (-·) (expression ρ x)

theorem expression_val {dom Γ w} (e : CExpr Γ w) (ρ : Signals dom Γ) (t : Nat) :
    (expression ρ e).val t = e.denote (fun i => (ρ i).val t) := by
  induction e <;> simp_all [expression, CExpr.denote, lift2_val, Signal.map,
    Signal.pure, Signal.mux]

inductive Program : List Nat → Nat → Nat → Type where
  | ret {Γ r w} (out : CExpr Γ w) : Program Γ r w
  | letE {Γ r w a} (name : String) (e : CExpr Γ a)
      (rest : Program (a :: Γ) r w) : Program Γ r w
  | next {Γ r w} (e : CExpr Γ r) (rest : Program Γ r w) : Program Γ r w
  | delay {Γ r w a} (name : String) (init : BitVec a) (e : CExpr Γ a)
      (rest : Program (a :: Γ) r w) : Program Γ r w

/-- Source statement semantics, including a real delayed binding. Result is
(output, pending write); return without a write leaves the pending value alone. -/
def Program.interpret {dom Γ r w} (p : Program Γ r w) (ρ : Signals dom Γ)
    (pending : Signal dom (BitVec r)) : Signal dom (BitVec w) × Signal dom (BitVec r) :=
  match p with
  | .ret out => (expression ρ out, pending)
  | .letE _ e rest => rest.interpret (pushSignal (expression ρ e) ρ) pending
  | .next e rest => rest.interpret ρ (expression ρ e)
  | .delay _ init e rest =>
    rest.interpret (pushSignal (Signal.register init (expression ρ e)) ρ) pending

/-- The accepted syntactic fragment has no additional registers and at most
one explicit next write. The latter agrees with the circuit-do duplicate-write
restriction rather than silently accepting last-write-wins source programs. -/
def Program.Supported {Γ r w} (p : Program Γ r w) (written : Bool) : Prop :=
  match p with
  | .ret _ => True
  | .letE _ _ rest => rest.Supported written
  | .next _ rest => written = false ∧ rest.Supported true
  | .delay _ _ _ _ => False

def Program.extract {Γ r w} (p : Program Γ r w) (pending : CExpr Γ r)
    (written : Bool := false) : Except String (Step Γ r w) :=
  match p with
  | .ret out => .ok (.ret pending out)
  | .letE name e rest =>
    (rest.extract (weaken pending) written).map (.bind name e)
  | .next e rest =>
    if written then .error "verified source: duplicate next-state assignment"
    else rest.extract e true
  | .delay _ _ _ _ => .error "verified source: delayed binding requires another register"

/-- Completeness for the precisely stated source fragment (naming and width
checks are a separate subsequent compiler stage). -/
theorem Program.extract_complete {Γ r w} (p : Program Γ r w) :
    ∀ pending written, p.Supported written → ∃ step, p.extract pending written = .ok step := by
  induction p with
  | ret out => intros; exact ⟨_, rfl⟩
  | letE name e rest ih =>
    intro pending written hs
    obtain ⟨step, h⟩ := ih (weaken pending) written hs
    exact ⟨.bind name e step, by simp [Program.extract, h, Except.map]⟩
  | next e rest ih =>
    intro pending written hs
    obtain ⟨hw, hs⟩ := hs
    subst written
    simpa [Program.extract] using ih e true hs
  | delay name init e rest ih => intros; contradiction

theorem Program.extract_supported {Γ r w} (p : Program Γ r w) :
    ∀ pending written step, p.extract pending written = .ok step → p.Supported written := by
  induction p with
  | ret _ => intros; trivial
  | letE name e rest ih =>
    intro pending written step h
    cases hx : rest.extract (weaken pending) written with
    | error err => simp [Program.extract, hx, Except.map] at h
    | ok tail => exact ih _ written tail hx
  | next e rest ih =>
    intro pending written step h
    cases written with
    | true => simp [Program.extract] at h
    | false => exact ⟨rfl, ih e true step h⟩
  | delay name init e rest ih =>
    intro pending written step h
    simp [Program.extract] at h

theorem Program.extract_iff_supported {Γ r w} (p : Program Γ r w)
    (pending : CExpr Γ r) (written : Bool) :
    (∃ step, p.extract pending written = .ok step) ↔ p.Supported written :=
  ⟨fun ⟨step, h⟩ => p.extract_supported pending written step h,
    p.extract_complete pending written⟩

/-- Pointwise extraction correctness with an arbitrary incoming pending
Signal. In particular, let-bindings after a write cannot capture that write. -/
theorem Program.extract_correct {dom Γ r w} (p : Program Γ r w) :
    ∀ (pending : CExpr Γ r) written step,
      p.extract pending written = .ok step →
      ∀ (ρ : Signals dom Γ) (pendingSignal : Signal dom (BitVec r)) t,
        pendingSignal.val t = pending.denote (fun i => (ρ i).val t) →
        ((p.interpret ρ pendingSignal).2.val t, (p.interpret ρ pendingSignal).1.val t) =
          step.denote (fun i => (ρ i).val t) := by
  induction p with
  | ret out =>
    intro pending written step h ρ ps t hp
    cases h
    simp [Program.interpret, Step.denote, hp, expression_val]
  | @letE Γ r w a name e rest ih =>
    intro pending written step h ρ ps t hp
    cases hx : rest.extract (weaken pending) written with
    | error err => simp [Program.extract, hx, Except.map] at h
    | ok tail =>
      have heq : Step.bind name e tail = step := by simpa [Program.extract, hx, Except.map] using h
      subst step
      have hp' : ps.val t = (weaken pending).denote
          (fun i => (pushSignal (expression ρ e) ρ i).val t) := by
        have henv : (fun i => (pushSignal (expression ρ e) ρ i).val t) =
            pushValue (e.denote (fun i => (ρ i).val t)) (fun i => (ρ i).val t) := by
          funext i
          exact Fin.cases (expression_val e ρ t) (fun _ => rfl) i
        rw [henv, weaken_denote]
        exact hp
      have res := ih (weaken pending) written tail hx
        (pushSignal (expression ρ e) ρ) ps t hp'
      have henv : (fun i => (pushSignal (expression ρ e) ρ i).val t) =
          pushValue (e.denote (fun i => (ρ i).val t)) (fun i => (ρ i).val t) := by
        funext i
        exact Fin.cases (expression_val e ρ t) (fun _ => rfl) i
      simpa only [Program.interpret, Step.denote, henv] using res
  | next e rest ih =>
    intro pending written step h ρ ps t hp
    cases written with
    | true => simp [Program.extract] at h
    | false =>
      exact ih e true step h ρ (expression ρ e) t (expression_val e ρ t)
  | delay name init e rest ih =>
    intro pending written step h
    simp [Program.extract] at h

structure Source (Γ : List Nat) (r w : Nat) where
  init : BitVec r
  program : Program (r :: Γ) r w

def currentRegister (Γ : List Nat) (r : Nat) : CExpr (r :: Γ) r :=
  .var (Γ := r :: Γ) ⟨0, by simp⟩

def Source.extract {Γ r w} (s : Source Γ r w) : Except String (Machine Γ r w) :=
  (s.program.extract (currentRegister Γ r)).map (fun step => ⟨s.init, step⟩)

/-- Operational source interpretation through actual register handles and the
shipping circuit runner. Reset is an explicit outer sampled-reset policy. -/
def Source.body {dom Γ r w} (s : Source Γ r w) (inputs : Signals dom Γ)
    (reset : Signal dom Bool) : Body dom r w := fun regs =>
  let reg := regs.1
  let pair := s.program.interpret (pushSignal reg.liveRead inputs) reg.liveRead
  Circuit.bind (Circuit.next reg (Signal.mux reset (Signal.pure s.init) pair.2))
    (fun _ => Circuit.pure' pair.1)

def Source.run {dom Γ r w} (s : Source Γ r w) (inputs : Signals dom Γ)
    (reset : Signal dom Bool) : Signal dom (BitVec w) :=
  runCircuitH (αs := [BitVec r]) (s.init, ()) (s.body inputs reset)

theorem Source.extract_complete {Γ r w} (s : Source Γ r w)
    (supported : s.program.Supported false) : ∃ m, s.extract = .ok m := by
  obtain ⟨step, h⟩ := s.program.extract_complete (currentRegister Γ r) false supported
  exact ⟨⟨s.init, step⟩, by rw [Source.extract, h]; rfl⟩

theorem Source.extract_init {Γ r w} (s : Source Γ r w) (m : Machine Γ r w)
    (h : s.extract = .ok m) : m.init = s.init := by
  cases hx : s.program.extract (currentRegister Γ r) with
  | error err => simp only [Source.extract, hx, Except.map] at h; contradiction
  | ok step =>
    have he : (⟨s.init, step⟩ : Machine Γ r w) = m := by
      simpa only [Source.extract, hx, Except.map, Except.ok.injEq] using h
    cases he
    rfl

/-- The former per-definition BodyMatches obligation, now discharged once for
EVERY successful extraction from this source statement language. -/
theorem Source.extract_bodyMatches {dom Γ r w} (s : Source Γ r w)
    (m : Machine Γ r w) (accepted : s.extract = .ok m)
    (inputs : Signals dom Γ) (reset : Signal dom Bool) :
    BodyMatches m (s.body inputs reset) (fun t i => (inputs i).val t) reset.val := by
  cases hx : s.program.extract (currentRegister Γ r) with
  | error err => simp only [Source.extract, hx, Except.map] at accepted; contradiction
  | ok step =>
    have he : (⟨s.init, step⟩ : Machine Γ r w) = m := by
      simpa only [Source.extract, hx, Except.map, Except.ok.injEq] using accepted
    cases he
    intro live t
    let q := Signal.map Prod.fst live
    let ρ := pushSignal q inputs
    have h := s.program.extract_correct _ false step hx ρ q t rfl
    have henv : (fun i => (ρ i).val t) =
        pushValue (live.val t).1 (fun i => (inputs i).val t) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [henv] at h
    constructor
    · exact congrArg Prod.snd h
    · change (if reset.val t then s.init else (s.program.interpret ρ q).2.val t) = _
      exact congrArg (fun next => if reset.val t then s.init else next) (congrArg Prod.fst h)

/-- End-to-end compiler entry point for the typed source statements. -/
def Source.compile {Γ r w} (s : Source Γ r w) (we : WEnv)
    (names : Fin Γ.length → String) (l : Layout) : Except String (List Stmt) :=
  match s.extract with
  | .error err => .error err
  | .ok m => m.compileChecked we names l

theorem Source.compile_complete {Γ r w} (s : Source Γ r w) (m : Machine Γ r w)
    (extracted : s.extract = .ok m) (we : WEnv)
    (names : Fin Γ.length → String) (l : Layout) (valid : m.Valid we names l) :
    s.compile we names l = .ok (m.compile names l) := by
  simp [Source.compile, extracted, m.compileChecked_complete we names l valid]

/-- Neither a Step nor a BodyMatches proof is an input to this theorem. All
successful source compilations preserve the shipping runner's Signal behavior. -/
theorem Source.compile_sound {dom Γ r w} (s : Source Γ r w)
    (we : WEnv) (names : Fin Γ.length → String) (l : Layout) (ir : List Stmt)
    (accepted : s.compile we names l = .ok ir)
    (inputs : Signals dom Γ) (reset : Signal dom Bool) (seed : Nat → Env → Env)
    (initial : Env)
    (hreg : ∀ t st, seed t st l.reg = st l.reg)
    (hrst : ∀ t st, seed t st l.reset = if reset.val t then 1 else 0)
    (hinp : ∀ t st i, seed t st (names i) = ((inputs i).val t).toNat)
    (hinit : initial l.reg = s.init.toNat) :
    RunCorrect (observe (s.run inputs reset)) we ir seed initial l.output := by
  cases hx : s.extract with
  | error err => simp [Source.compile, hx] at accepted
  | ok m =>
    have hc : m.compileChecked we names l = .ok ir := by
      simpa [Source.compile, hx] using accepted
    have h := compileChecked_signal_sound m (s.body inputs reset)
      (fun t i => (inputs i).val t) reset.val (s.extract_bodyMatches m hx inputs reset)
      we names l ir hc seed initial ⟨hreg, hrst, hinp⟩
      (by rw [s.extract_init m hx]; exact hinit)
    simpa only [Source.run, s.extract_init m hx] using h

/-- End-to-end proof-carrying output; the source/Step correspondence is NOT a
caller-supplied proof. Downstream optimizer/parser evidence remains explicit. -/
def Source.certify {dom Γ r w} (s : Source Γ r w)
    (we : WEnv) (names : Fin Γ.length → String) (l : Layout) (ir : List Stmt)
    (accepted : s.compile we names l = .ok ir)
    (inputs : Signals dom Γ) (reset : Signal dom Bool) (seed : Nat → Env → Env)
    (initial : Env)
    (hreg : ∀ t st, seed t st l.reg = st l.reg)
    (hrst : ∀ t st, seed t st l.reset = if reset.val t then 1 else 0)
    (hinp : ∀ t st i, seed t st (names i) = ((inputs i).val t).toNat)
    (hinit : initial l.reg = s.init.toNat)
    (text : String) (optimized reparsed : List Stmt) (parses : parseBody text = .ok reparsed)
    (hOpt : RunCorrect (observe (s.run inputs reset)) we optimized seed initial l.output)
    (hRT : RunCorrect (observe (s.run inputs reset)) we reparsed seed initial l.output) :
    Certificate (observe (s.run inputs reset)) :=
  ofReplay text parses
    (s.compile_sound we names l ir accepted inputs reset seed initial hreg hrst hinp hinit)
    hOpt hRT

end Tools.VerifiedSource

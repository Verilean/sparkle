import Tools.ShippingGen5SM1
import Tools.ShippingGen5ConstValueE
set_option autoImplicit false
-- FG circuit pilot S1 (Issue sparkle-fg-circuit-pilot). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # FG circuit pilot S1: the complete conclusion, the applied-unit Signal/BitVec denotation, the correspondence to the existing FG types

Strategy: `docs/FG-CIRCUIT-STRATEGY-2026-11-06.md` §4-§6. Result and open list: `docs/FG-CIRCUIT-PILOT.md`.

## 1. The conclusion (conceptual form, fixed first)

    compileCircuit env source params = .ok artifact
      → ∃ sourceMeaning, SourceDenotes env source params sourceMeaning
                         ∧ HasConcretePackage artifact ∧ ObservationsEqual sourceMeaning artifact

`compileCircuit … = .ok artifact` IS the existing entry run (`EntryWitness`: the start world, a `RunsTo` of `synthesizeCombinational[WithParameters]`,
`ReflectsAll`), `artifact` is its output `(b, D)`. `HasConcretePackage` is `TopShips` (the run of `b` under `runModuleTG` shows the package's
output streams for ALL input streams, ALL cycle counts `T`, with `clk`/`rst` as the inputs of `b` — the existing contract, rst/clk held at 0 and
registers starting at their reset values `f.init`). `ObservationsEqual` is the existing `ObsC` on the SAME package (`sh.obs m = p.src`).

`SourceDenotes` is defined from the SOURCE: the Lean declaration's own value `Expr` read by the applied-unit Signal/BitVec denotation `CD` below,
whose values are built from the very Lean constants (`Signal.register`, `Signal.loop`, `Signal.mux`, `+`, `BitVec.ofNat` …), never from the
generated IR or the package. It is the concrete `ConstValueRel` `CircCV`; `DeclConnect CircCV` is then the existing `DeclConnect`.

Named conditions that are NOT closed here (they are binders / hypotheses of the statement, not hidden): see `FGCircuitStmt` and
`docs/FG-CIRCUIT-PILOT.md` §Open.
-/
namespace Tools.ShippingFGCircuit
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG Tools.ShippingGen5ConstValueE
open Tools.ShippingEntryReadsLinked (envAt)

/-! ## 2. The applied-unit denotation of the Signal/BitVec core

A rule recognizes a WHOLE application (constant, universe levels, all arguments) and gives the value built from the same Lean constant on the
denotations of the arguments. No rule unfolds `Signal.*` / `BitVec.*` (the stop set), so no recursor / well-founded recursion enters. Type
arguments are consumed by `TD`, never turned into values; `Dyn` stays in `Type 0`. -/

def appN (c : Name) (ls : List Level) (args : List Expr) : Expr := mkAppN (.const c ls) args.toArray

-- the syntactic types that occur at the core: `Nat`, `Bool`, `BitVec w`, `Signal dom T`.
mutual
inductive TD : Val → Expr → Type → Prop
  | nat {ρ : Val} {e : Expr} (he : e = .const ``Nat []) : TD ρ e Nat
  | bool {ρ : Val} {e : Expr} (he : e = .const ``Bool []) : TD ρ e Bool
  | bitvec {ρ : Val} {e w : Expr} {n : Nat} (he : e = appN ``BitVec [] [w]) (hw : CD ρ w Nat n) : TD ρ e (BitVec n)
  | signal {ρ : Val} {e d t : Expr} {D : DomainConfig} {T : Type} (he : e = appN ``Signal [.zero] [d, t])
      (hd : CD ρ d DomainConfig D) (ht : TD ρ t T) : TD ρ e (Signal D T)

inductive CD : Val → Expr → (α : Type) → α → Prop
  | bvar {ρ : Val} {i : Nat} {en : Entry} (h : ρ[i]? = some en) : CD ρ (.bvar i) en.d.ty en.d.val
  /-- `(n : Nat)` as `@OfNat.ofNat Nat n (instOfNatNat n)`. -/
  | natLit {ρ : Val} {e : Expr} {n : Nat}
      (he : e = appN ``OfNat.ofNat [.zero] [.const ``Nat [], .lit (.natVal n), appN ``instOfNatNat [] [.lit (.natVal n)]]) :
      CD ρ e Nat n
  | domDefault {ρ : Val} {e : Expr} (he : e = .const ``Sparkle.Core.Domain.defaultDomain []) :
      CD ρ e DomainConfig defaultDomain
  | bvOfNat {ρ : Val} {e w k : Expr} {W K : Nat} (he : e = appN ``BitVec.ofNat [] [w, k])
      (hw : CD ρ w Nat W) (hk : CD ρ k Nat K) : CD ρ e (BitVec W) (BitVec.ofNat W K)
  | bvInhabited {ρ : Val} {e w : Expr} {W : Nat} (he : e = appN ``BitVec.instInhabited [] [w]) (hw : CD ρ w Nat W) :
      CD ρ e (Inhabited (BitVec W)) (inferInstance : Inhabited (BitVec W))
  | boolInhabited {ρ : Val} {e : Expr} (he : e = .const ``instInhabitedBool []) :
      CD ρ e (Inhabited Bool) (inferInstance : Inhabited Bool)
  | sigPure {ρ : Val} {e d t x : Expr} {D : DomainConfig} {T : Type} {a : T}
      (he : e = appN ``Signal.pure [.zero] [d, t, x]) (hd : CD ρ d DomainConfig D) (ht : TD ρ t T) (hx : CD ρ x T a) :
      CD ρ e (Signal D T) (Signal.pure a)
  | sigRegister {ρ : Val} {e d t i s : Expr} {D : DomainConfig} {T : Type} {a : T} {sv : Signal D T}
      (he : e = appN ``Signal.register [.zero] [d, t, i, s]) (hd : CD ρ d DomainConfig D) (ht : TD ρ t T)
      (hi : CD ρ i T a) (hs : CD ρ s (Signal D T) sv) : CD ρ e (Signal D T) (Signal.register a sv)
  | sigMux {ρ : Val} {e d t c a b : Expr} {D : DomainConfig} {T : Type} {cv : Signal D Bool} {av bv : Signal D T}
      (he : e = appN ``Signal.mux [.zero] [d, t, c, a, b]) (hd : CD ρ d DomainConfig D) (ht : TD ρ t T)
      (hc : CD ρ c (Signal D Bool) cv) (ha : CD ρ a (Signal D T) av) (hb : CD ρ b (Signal D T) bv) :
      CD ρ e (Signal D T) (Signal.mux cv av bv)
  /-- `a + b` on `Signal dom (BitVec w)`: `@HAdd.hAdd S S S (instHAddSignalBitVec dom w) a b`, `S := Signal dom (BitVec w)`. -/
  | sigAddBV {ρ : Val} {e d w a b : Expr} {D : DomainConfig} {W : Nat} {av bv : Signal D (BitVec W)}
      (he : e = appN ``HAdd.hAdd [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, appN ``BitVec [] [w]], appN ``Signal [.zero] [d, appN ``BitVec [] [w]],
         appN ``Signal [.zero] [d, appN ``BitVec [] [w]], appN ``Sparkle.Core.Signal.instHAddSignalBitVec [] [d, w], a, b])
      (hd : CD ρ d DomainConfig D) (hw : CD ρ w Nat W)
      (ha : CD ρ a (Signal D (BitVec W)) av) (hb : CD ρ b (Signal D (BitVec W)) bv) :
      CD ρ e (Signal D (BitVec W)) (@HAdd.hAdd _ _ _ (@Sparkle.Core.Signal.instHAddSignalBitVec D W) av bv)
  /-- `Signal.loop` (the pure `loopGo` fixpoint; `@[implemented_by]` is execution only). -/
  | sigLoop {ρ : Val} {e d t inst f : Expr} {D : DomainConfig} {T : Type} {iv : Inhabited T} {g : Signal D T → Signal D T}
      (he : e = appN ``Signal.loop [] [d, t, inst, f]) (hd : CD ρ d DomainConfig D) (ht : TD ρ t T)
      (hi : CD ρ inst (Inhabited T) iv) (hf : CD ρ f (Signal D T → Signal D T) g) :
      CD ρ e (Signal D T) (@Signal.loop D T iv g)
  | lam {ρ : Val} {e A body : Expr} {n : Name} {bi : BinderInfo} {TA T : Type} {f : TA → T}
      (he : e = .lam n A body bi) (hA : TD ρ A TA) (hb : ∀ a : TA, CD (⟨A, ⟨TA, a⟩⟩ :: ρ) body T (f a)) :
      CD ρ e (TA → T) f
end

/-- The concrete `ConstValueRel` of the circuit core: the declaration `X` of `env` is a (level-monomorphic) definition whose value `Expr` is
denoted by `CD` in the empty valuation. -/
def CircCV : ConstValueRel := fun env X α v =>
  ∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ CD [] d.value α v

/-! ## 3. The complete conclusion, typed

`SourceDenotes env X params sh m`: `m : sh.Ty` is the source meaning of the declaration `X` of `env` (params must be empty at S1: a
parametric root is outside this pilot), `sh` is the shape the existing recognizer `shapeOf` assigns to the declared type. -/

def SourceDenotes (env : Environment) (source : Name) (params : List (String × Nat)) (sh : SigShape) (m : sh.Ty) : Prop :=
  params = [] ∧ ∃ ci : ConstantInfo, env.find? source = some ci ∧ shapeOf ci = some sh ∧ CircCV env source sh.Ty m

variable {ι : Type} {dom : ι → DomainConfig}


/-! ## 3b. Domain-monomorphic roots

The existing recognizer `shapeOf` only accepts declarations whose type begins with a `(dom : DomainConfig)` binder. The three Signal roots of
`Tests.SignalLoopTest` are fixed at `defaultDomain`, so the pilot adds the monomorphic twin: same `SigShape`, positions counted from 0 (no domain
binder: this is the position convention of the generated `machineSource`, `bools 0` / `bits 0 8`), the domain fixed. -/

def monoScalar? : Lean.Expr → Option Scalar
  | .app (.app (.const ``Sparkle.Core.Signal.Signal _) (.const ``Sparkle.Core.Domain.defaultDomain [])) (.const ``Bool _) => some .bool
  | .app (.app (.const ``Sparkle.Core.Signal.Signal _) (.const ``Sparkle.Core.Domain.defaultDomain [])) (.app (.const ``BitVec _) wE) =>
    (canonicalNatLitValue? wE).bind fun n => if 0 < n then some (.bits n) else none
  | _ => none
def monoGo : List Scalar → Lean.Expr → Option SigShape
  | acc, .forallE _ ty b _ => (monoScalar? ty).bind fun k => monoGo (acc ++ [k]) b
  | acc, e => (monoScalar? e).map fun k => { args := acc, res := .one k }
def monoShapeOf (ci : ConstantInfo) : Option SigShape := if ci.levelParams.isEmpty then monoGo [] ci.type else none

/-- the source meaning of a monomorphic declaration: a function of the argument streams at `defaultDomain` -/
def MonoTy (sh : SigShape) : Type := ArgsTy defaultDomain sh.args (sh.res.Ty defaultDomain)

def monoObs (sh : SigShape) (m : MonoTy sh) (bools : Nat → Signal defaultDomain Bool)
    (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n)) : List (Nat → Nat) :=
  sh.res.obs (applyArgs bools bits sh.args 0 (sh.res.Ty defaultDomain) m)

def SourceDenotesMono (env : Environment) (source : Name) (params : List (String × Nat)) (sh : SigShape) (m : MonoTy sh) : Prop :=
  params = [] ∧ ∃ d : DefinitionVal, env.find? source = some (.defnInfo d) ∧ d.levelParams = [] ∧
    monoShapeOf (.defnInfo d) = some sh ∧ CD [] d.value (MonoTy sh) m

def ShapeMatchesMono (sh : SigShape) (d : Tools.ShippingMachineAuto.MachineData) (kD : Nat) : Prop :=
  (d.bsIn.take kD).map (·.2) = sh.args.map Scalar.binder ∧
  d.shape.layout.outs.map (fun o => (o.name, o.ty, o.width)) = sh.res.outPorts

/-- the same observation correspondence for a package over the fixed domain (`ι` arbitrary, `dom = fun _ => defaultDomain`) -/
def ObservationsEqualMono {ι : Type} (sh : SigShape) (m : MonoTy sh) (p : Pkg ι (fun _ => defaultDomain)) : Prop :=
  ShapeMatchesMono sh p.d p.kD ∧ ∀ i bools bits, monoObs sh m bools bits = p.src i bools bits

/-- The artifact side: the package, its height, the raw module — `TopShips` (the run of the printed module `b` under `runModuleTG`). -/
def HasConcretePackage (p : Pkg ι dom) (n : Nat) (declName : Name) (b raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) : Prop :=
  p.decl = declName ∧ TopShips p n declName b raw D

/-- The observation correspondence on the same package: ports/shape and, for all input streams, the source meaning's observed streams
(`Bool` as 0/1, `BitVec` as `toNat`) are the package's output streams (`p.src`), which `TopShips` ties to the IR run at every cycle. -/
def ObservationsEqual (sh : SigShape) (m : sh.Ty) (p : Pkg ι dom) : Prop :=
  ShapeMatches sh p.d p.kD ∧ ∀ i bools bits, sh.obs (dom := dom) m i bools bits = p.src i bools bits


/-! ## 4. The concretized primitives: value meaning, IR operation, temporal/reset mapping — PROVED, not tabulated

Each `CD` rule's value is the Lean constant itself, so "the meaning of the primitive" is Lean's own definition. What the pilot proves per primitive is
(a) its pointwise-in-time meaning (the equation the IR semantics must match) and (b) the agreement with the IR operation's semantics
(`Sparkle.IR.Semantics.evalExpr` / `regNexts`) on masked values. The per-cycle composition of these (state threading, `Signal.loop` as a register
feedback, the cycle order of `runModuleTG`) is the existing generator theorem `machine_trace_of_loop` / `machine_trace_of_data`, which the endpoints
instantiate (named in `docs/FG-CIRCUIT-PILOT.md` §Primitives). -/

section Prims
open Sparkle.IR.Semantics Sparkle.IR.AST

-- (a) value meaning
theorem pure_val {D : DomainConfig} {T : Type} (a : T) (t : Nat) : (Signal.pure a : Signal D T).val t = a := rfl
theorem register_val_zero {D : DomainConfig} {T : Type} (i : T) (s : Signal D T) : (Signal.register i s).val 0 = i := rfl
theorem register_val_succ {D : DomainConfig} {T : Type} (i : T) (s : Signal D T) (t : Nat) :
    (Signal.register i s).val (t + 1) = s.val t := rfl
theorem mux_val {D : DomainConfig} {T : Type} (c : Signal D Bool) (a b : Signal D T) (t : Nat) :
    (Signal.mux c a b).val t = if c.val t then a.val t else b.val t := rfl
theorem addBV_val {D : DomainConfig} {W : Nat} (a b : Signal D (BitVec W)) (t : Nat) :
    (@HAdd.hAdd _ _ _ (@Sparkle.Core.Signal.instHAddSignalBitVec D W) a b).val t = a.val t + b.val t := rfl
theorem loop_val_zero {D : DomainConfig} {T : Type} [Inhabited T] (i : T) (g : Signal D T → Signal D T) :
    (Signal.loop fun s => Signal.register i (g s)).val 0 = i := by
  show Signal.loopGo _ 0 = i
  rw [Signal.loopGo_eq]; rfl
/-- the feedback loop of a register over a pointwise next-state function steps by that function (the register-feedback reading of `Signal.loop`) -/
theorem loop_register_map_succ {D : DomainConfig} {T : Type} [Inhabited T] (i : T) (h : T → T) (t : Nat) :
    (Signal.loop (dom := D) fun s => Signal.register i (Signal.map h s)).val (t + 1) = h ((Signal.loop (dom := D) fun s => Signal.register i (Signal.map h s)).val t) := by
  show Signal.loopGo _ (t + 1) = h (Signal.loopGo _ t)
  rw [Signal.loopGo_eq]
  simp [Signal.register, Signal.map]

-- (b) agreement with the IR operations
theorem ir_const_agrees (we : WEnv) (env : Env) (w n : Nat) :
    evalExpr we env (.const (n : Int) w) = some (BitVec.ofNat w n).toNat := by
  have hk : 0 < 2 ^ w := Nat.two_pow_pos w
  simp only [evalExpr, mask, BitVec.toNat_ofNat]
  congr 1
  generalize 2 ^ w = k at hk ⊢
  have h1 : (((n:Int) % (k:Int) + (k:Int)) % (k:Int)) = ((n % k : Nat) : Int) := by
    have : ((n:Int) % (k:Int) + (k:Int)) = (n:Int) % (k:Int) + 1 * (k:Int) := by rw [Int.one_mul]
    rw [this, Int.add_mul_emod_self_right, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
    exact (by norm_cast : (n:Int) % (k:Int) = ((n % k : Nat) : Int))
  rw [h1, Int.toNat_natCast, Nat.mod_mod]

theorem ir_add_agrees {W : Nat} (x y : BitVec W) : mask W (x.toNat + y.toNat) = (x + y).toNat := by
  simp [mask, BitVec.toNat_add]

theorem ir_mux_agrees {T : Type} (c : Bool) (a b : T) :
    (if Tools.ShippingMuxLoweringSoundness.encodeBool c ≠ 0 then a else b) = if c then a else b := by
  cases c <;> simp [Tools.ShippingMuxLoweringSoundness.encodeBool]

/-- the IR register at reset low (`rst = 0`, the `TopShips` premise on `rst`) latches the masked input: the source `Signal.register`'s `s.val t` at `t+1` -/
theorem ir_register_step_rst0 (we : WEnv) (mems : MEnv) (out clk rst : String) (k : Sparkle.IR.Type.ResetKind) (input : Sparkle.IR.AST.Expr)
    (init : Int) (env : Env) (v : Nat) (hv : evalExpr we env input = some v) (hr : env rst = 0) :
    regNexts we mems [.register out clk (rst, k) input init] env = some [(out, mask (we out) v)] := by
  simp [regNexts, hv, hr]

/-- reset mapping: the reset VALUE of the IR register is the source `Signal.register`'s `init` at cycle 0 (`TopShips`: `st0 r = f.init`, the slot's init) -/
theorem ir_register_reset_value (we : WEnv) (mems : MEnv) (out clk rst : String) (k : Sparkle.IR.Type.ResetKind) (input : Sparkle.IR.AST.Expr)
    (init : Int) (env : Env) (v : Nat) (hv : evalExpr we env input = some v) (hr : env rst ≠ 0) :
    regNexts we mems [.register out clk (rst, k) input init] env = some [(out, encodeInit init (we out))] := by
  simp [regNexts, hv, hr]

end Prims

/-- One row per concretized primitive unit. The proofs listed are the semantic agreement (value + IR operation); the table itself carries no meaning. -/
structure PrimSpec where
  decl : Name
  levels : Nat
  args : String
  result : String
  valueMeaning : String
  irOp : String
  temporalReset : String
  proofs : List Name

def primTable : List PrimSpec := [
  { decl := ``OfNat.ofNat, levels := 1, args := "Nat, lit n, instOfNatNat n", result := "Nat", valueMeaning := "n",
    irOp := "none (compile-time width/value)", temporalReset := "static", proofs := [] },
  { decl := ``BitVec.ofNat, levels := 0, args := "w, n", result := "BitVec w", valueMeaning := "BitVec.ofNat w n",
    irOp := "Expr.const n w", temporalReset := "static", proofs := [``ir_const_agrees] },
  { decl := ``Signal.pure, levels := 1, args := "dom, T, a", result := "Signal dom T", valueMeaning := "fun _ => a",
    irOp := "Expr.const / ref", temporalReset := "same value at every cycle", proofs := [``pure_val, ``ir_const_agrees] },
  { decl := ``Signal.register, levels := 1, args := "dom, T, init, s", result := "Signal dom T",
    valueMeaning := "t=0: init; t+1: s t", irOp := "Stmt.register out clk (rst,k) in init",
    temporalReset := "cycle t ↔ IR cycle t; IR rst held 0 (TopShips); register starts at init (slot init)",
    proofs := [``register_val_zero, ``register_val_succ, ``ir_register_step_rst0, ``ir_register_reset_value] },
  { decl := ``Signal.mux, levels := 1, args := "dom, T, c, a, b", result := "Signal dom T",
    valueMeaning := "if c t then a t else b t", irOp := "Expr.op .mux [c,a,b] (Bool as 0/1)", temporalReset := "combinational",
    proofs := [``mux_val, ``ir_mux_agrees] },
  { decl := ``HAdd.hAdd, levels := 3, args := "S,S,S,instHAddSignalBitVec dom w,a,b (S = Signal dom (BitVec w))",
    result := "Signal dom (BitVec w)", valueMeaning := "a t + b t (BitVec add, mod 2^w)", irOp := "Expr.op .add [a,b] masked to w",
    temporalReset := "combinational", proofs := [``addBV_val, ``ir_add_agrees] },
  { decl := ``Signal.loop, levels := 0, args := "dom, T, Inhabited T, f", result := "Signal dom T",
    valueMeaning := "loopGo f (strong recursion on t; fixpoint for strictly causal f)",
    irOp := "register feedback: the loop variable is the register output wire",
    temporalReset := "t=0 is the register init; t+1 reads cycle t", proofs := [``loop_val_zero, ``loop_register_map_succ] } ]

/-- The FG-circuit conclusion at one entry `(b, D)` of the world `w`, with the package supplied by `P` (the generated table). -/
def FGCircuitConclusion (env : Environment) (P : Pkgs ι dom) (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (declName : Name) (parameters : List (String × Nat)) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) : Prop :=
  (∃ raw, Post b raw) ∧
  ∀ raw, Post b raw → ∃ (sh : SigShape) (m : sh.Ty) (p : Pkg ι dom) (n : Nat),
    P declName = some p ∧ SourceDenotes env declName parameters sh m ∧ HasConcretePackage p n declName b raw D ∧ ObservationsEqual sh m p

/-- `DeclConnect CircCV` at the top, a package and a successful top run give the conclusion's second part (no new content: the assembly). -/
theorem conclusion_of_declConnect {env : Environment} {P : Pkgs ι dom} {declName : Name} {p : Pkg ι dom}
    {parameters : List (String × Nat)} (hparams : parameters = [])
    {n : Nat} {b raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hP : P declName = some p) (hDC : DeclConnect CircCV env P (fun X => X = declName))
    (hT : TopShips p n declName b raw D) (hdecl : p.decl = declName) :
    ∃ (sh : SigShape) (m : sh.Ty) (p : Pkg ι dom) (n : Nat),
      P declName = some p ∧ SourceDenotes env declName parameters sh m ∧ HasConcretePackage p n declName b raw D ∧ ObservationsEqual sh m p := by
  rw [declConnect_eq] at hDC
  obtain ⟨ci, sh, v, hf, hs, hm, hcv, hobs⟩ := hDC declName rfl p hP
  exact ⟨sh, v, p, n, hP, ⟨hparams, ci, hf, hs, hcv⟩, ⟨hdecl, hT⟩, hm, hobs⟩

end Tools.ShippingFGCircuit

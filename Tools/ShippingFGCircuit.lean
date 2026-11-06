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

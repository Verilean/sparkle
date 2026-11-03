import Lean
import Tools.ShippingGen2Defs
import Tools.ShippingGen5DeclConnectAbs
set_option autoImplicit false
-- Built at 68f1be34d40e6754e38dd8fdb7055b2ec59bfd87 (agent build `kjob lake build Tests.Gen5.DeclConnectCheck`, exit 0, includes this file; no sorry; clean issue-linked build is the coder's). Axioms: standard only.

/-! # DC-CONNECT concrete units U-SHAPE1 / U-SHAPE2 / U-ROWS (scripts/gen5/DC_CONNECT_FREEZE.md rev5 §C.2, §C.8)

The shape/adapter vocabulary of `DeclConnect` on the actual source: `Scalar`, `ResShape`, `SigShape`, the recognizer `sigShape?` (a total
function of the declared type `Expr`), the observation `SigShape.obs`, the package-side match `ShapeMatches`, the agreement lemmas against
`telescopeKinds`/`machOuts?`/`machOutFields`, and `DeclConnect` as the instance of the accepted abstract `DCGen` (Part A).
Pure: no DG-SEM / DG-DATAOF / DG-ACC result, no `ConstValue` definition (`ConstValueRel` is only a type), no new law or TRUSTED boundary.
Rows U-ROWS are CONDITIONAL (explicit `hstep`), an intermediate Acc assembly, not completion. No sorry/axiom/native_decide. -/
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen2 Tools.ShippingMachineAuto

namespace Tools.ShippingGen5DeclConnect

inductive Scalar
  | bool
  | bits (n : Nat)
  deriving DecidableEq, Repr

def Scalar.Ty (D : DomainConfig) : Scalar → Type
  | .bool => Signal D Bool
  | .bits n => Signal D (BitVec n)
def Scalar.binder : Scalar → MixedGateBinder
  | .bool => .bool
  | .bits n => .bits n
def Scalar.hw : Scalar → Sparkle.IR.Type.HWType
  | .bool => .bit
  | .bits n => .bitVector n
def Scalar.width : Scalar → Nat
  | .bool => 1
  | .bits n => n
/-- The actual function's argument at telescope position `q`: `bools q` / `bits q n`. -/
def Scalar.arg {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (q : Nat) : (k : Scalar) → k.Ty D
  | .bool => bools q
  | .bits n => bits q n
/-- Observation of one result stream: Bool as 0/1, BitVec as `toNat`. -/
def Scalar.obs {D : DomainConfig} : (k : Scalar) → k.Ty D → (Nat → Nat)
  | .bool, s => fun t => Tools.ShippingMuxLoweringSoundness.encodeBool (s.val t)
  | .bits _, s => fun t => (s.val t).toNat

inductive ResShape
  | one (k : Scalar)
  | pair (ka kb : Scalar)
  deriving DecidableEq, Repr

def ResShape.Ty (D : DomainConfig) : ResShape → Type
  | .one k => k.Ty D
  | .pair a b => a.Ty D × b.Ty D
def ResShape.obs {D : DomainConfig} : (r : ResShape) → r.Ty D → List (Nat → Nat)
  | .one k, s => [k.obs s]
  | .pair a b, (x, y) => [a.obs x, b.obs y]
/-- The output ports a package must have, in `layout.outs` order: name, hardware type, width. -/
def ResShape.outPorts : ResShape → List (String × Sparkle.IR.Type.HWType × Nat)
  | .one k => [("out", k.hw, k.width)]
  | .pair a b => [("out_0", a.hw, a.width), ("out_1", b.hw, b.width)]
/-- The same ports as `machOuts?` returns them. -/
def ResShape.ports : ResShape → List (String × MixedGateBinder)
  | .one k => [("out", k.binder)]
  | .pair a b => [("out_0", a.binder), ("out_1", b.binder)]
def ResShape.ctor? : ResShape → Option Name
  | .one _ => none
  | .pair _ _ => some ``Prod.mk

/-- Shape of the actual type: the arguments AFTER the leading `DomainConfig` binder, and the result. -/
structure SigShape where
  args : List Scalar
  res : ResShape
  deriving DecidableEq, Repr

def ArgsTy (D : DomainConfig) : List Scalar → Type → Type
  | [], R => R
  | k :: ks, R => k.Ty D → ArgsTy D ks R
/-- The reference type: a function of the domain. -/
def SigShape.Ty (sh : SigShape) : Type := (D : DomainConfig) → ArgsTy D sh.args (sh.res.Ty D)

/-- Feed the reference streams: argument `k` at position `q` gets `k.arg bools bits q`; the domain binder is position 0, so the first call has `q = 1`. -/
def applyArgs {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) :
    (ks : List Scalar) → (q : Nat) → (R : Type) → ArgsTy D ks R → R
  | [], _, _, f => f
  | k :: ks, q, R, f => applyArgs bools bits ks (q + 1) R (f (k.arg bools bits q))

variable {ι : Type} {dom : ι → DomainConfig}

def SigShape.obs (sh : SigShape) (v : sh.Ty) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) : List (Nat → Nat) :=
  sh.res.obs (applyArgs bools bits sh.args 1 (sh.res.Ty (dom i)) (v (dom i)))

/-! ## The recognizer: a total function of the type `Expr` ALONE -/

def domAt (depth : Nat) : Lean.Expr → Bool
  | .bvar j => j + 1 == depth
  | _ => false
def scalar? (depth : Nat) : Lean.Expr → Option Scalar
  | .app (.app (.const ``Sparkle.Core.Signal.Signal _) d) (.const ``Bool _) =>
    if domAt depth d then some .bool else none
  | .app (.app (.const ``Sparkle.Core.Signal.Signal _) d) (.app (.const ``BitVec _) wE) =>
    if domAt depth d then (canonicalNatLitValue? wE).bind fun n => if 0 < n then some (.bits n) else none else none
  | _ => none
def resShape? (depth : Nat) : Lean.Expr → Option ResShape
  | .app (.app (.const ``Prod _) a) b => do
    let ka ← scalar? depth a
    let kb ← scalar? depth b
    pure (.pair ka kb)
  | e => (scalar? depth e).map .one
def sigGo : Nat → List Scalar → Lean.Expr → Option SigShape
  | depth, acc, .forallE _ ty b _ => (scalar? depth ty).bind fun k => sigGo (depth + 1) (acc ++ [k]) b
  | depth, acc, e => (resShape? depth e).map fun r => { args := acc, res := r }
def sigShape? : Lean.Expr → Option SigShape
  | .forallE _ ty b _ => if ty.isConstOf ``Sparkle.Core.Domain.DomainConfig then sigGo 1 [] b else none
  | _ => none
/-- The decision on a declaration: `levelParams` is a property of the constant, not of its type. -/
def shapeOf (ci : ConstantInfo) : Option SigShape := if ci.levelParams.isEmpty then sigShape? ci.type else none

/-- What the shape must match in the package (positional and exact on arguments; output ports in `layout.outs` order). -/
def ShapeMatches (sh : SigShape) (d : MachineData) (kD : Nat) : Prop :=
  (d.bsIn.take kD).map (·.2) = MixedGateBinder.domain :: sh.args.map Scalar.binder ∧
  d.shape.layout.outs.map (fun o => (o.name, o.ty, o.width)) = sh.res.outPorts

instance (sh : SigShape) (d : MachineData) (kD : Nat) : Decidable (ShapeMatches sh d kD) := by
  unfold ShapeMatches; infer_instance

/-! ## U-SHAPE2: unfolding equations and agreement with the compiler's own readers -/

theorem applyArgs_nil {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (q : Nat) (R : Type) (f : ArgsTy D [] R) : applyArgs bools bits [] q R f = f := rfl
theorem applyArgs_cons {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (k : Scalar) (ks : List Scalar) (q : Nat) (R : Type) (f : ArgsTy D (k :: ks) R) :
    applyArgs bools bits (k :: ks) q R f = applyArgs bools bits ks (q + 1) R (f (k.arg bools bits q)) := rfl

theorem outPorts_eq (r : ResShape) (slotsW : Nat) :
    r.outPorts = (machOutFields slotsW r.ports).map (fun o => (o.name, o.ty, o.width)) := by
  cases r with
  | one k => cases k <;> simp [ResShape.outPorts, ResShape.ports, machOutFields, Scalar.hw, Scalar.width, Scalar.binder, machHWType, machWidth]
  | pair a b => cases a <;> cases b <;> simp [ResShape.outPorts, ResShape.ports, machOutFields, Scalar.hw, Scalar.width, Scalar.binder, machHWType, machWidth]

theorem scalar?_kind {depth : Nat} {e : Lean.Expr} {k : Scalar} (h : scalar? depth e = some k) :
    mixedGateBinderKind? e = some k.binder := by
  unfold scalar? at h
  split at h
  · split at h
    · cases h; simp [mixedGateBinderKind?, Scalar.binder, Expr.isConstOf]
    · cases h
  · split at h
    · rename_i _ _ _ _ wE _
      cases hw : canonicalNatLitValue? wE with
      | none => simp [hw] at h
      | some n =>
        simp only [hw, Option.bind_some] at h
        split at h
        · cases h; simp [mixedGateBinderKind?, Scalar.binder, hw, Expr.isConstOf, *]
        · cases h
    · cases h
  · cases h

theorem sigGo_tele (e : Lean.Expr) : ∀ (depth : Nat) (acc : List Scalar) (sh : SigShape), sigGo depth acc e = some sh →
    ∃ rest, sh.args = acc ++ rest ∧ telescopeKinds e = some (rest.map Scalar.binder) := by
  induction e with
  | forallE n ty b bi ihty ihb =>
    intro depth acc sh h
    simp only [sigGo] at h
    cases hk : scalar? depth ty with
    | none => simp [hk] at h
    | some k =>
      simp only [hk, Option.bind_some] at h
      obtain ⟨rest, hr, ht⟩ := ihb (depth + 1) (acc ++ [k]) sh h
      refine ⟨k :: rest, by simp [hr], ?_⟩
      simp [telescopeKinds, scalar?_kind hk, ht]
  | _ =>
    all_goals
      intro depth acc sh h
      simp only [sigGo, Option.map_eq_some_iff] at h
      obtain ⟨r, _, rfl⟩ := h
      exact ⟨[], by simp, by simp [telescopeKinds]⟩

theorem sigShape?_telescope {ty : Lean.Expr} {sh : SigShape} (h : sigShape? ty = some sh) :
    telescopeKinds ty = some (MixedGateBinder.domain :: sh.args.map Scalar.binder) := by
  cases ty with
  | forallE n t b bi =>
    simp only [sigShape?] at h
    split at h
    · rename_i hd
      obtain ⟨rest, hr, ht⟩ := sigGo_tele b 1 [] sh h
      simp only [List.nil_append] at hr
      subst hr
      simp [telescopeKinds, mixedGateBinderKind?, hd, ht]
    · cases h
  | _ => simp [sigShape?] at h

theorem scalar?_outs (senv : StructEnv) {depth : Nat} {e : Lean.Expr} {k : Scalar} (h : scalar? depth e = some k) :
    machOuts? senv e = some (none, [("out", k.binder)]) := by
  unfold scalar? at h
  split at h
  · split at h
    · cases h; simp [machOuts?, mixedGateBinderKind?, Scalar.binder, Expr.isConstOf]
    · cases h
  · split at h
    · rename_i _ _ _ _ wE _
      cases hw : canonicalNatLitValue? wE with
      | none => simp [hw] at h
      | some n =>
        simp only [hw, Option.bind_some] at h
        split at h
        · cases h; simp [machOuts?, mixedGateBinderKind?, Scalar.binder, hw, Expr.isConstOf, *]
        · cases h
    · cases h
  · cases h

theorem resShape?_outs (senv : StructEnv) {depth : Nat} {e : Lean.Expr} {r : ResShape} (h : resShape? depth e = some r) :
    machOuts? senv e = some (r.ctor?, r.ports) := by
  unfold resShape? at h
  split at h
  · rename_i a b
    cases ha : scalar? depth a with
    | none => simp [ha] at h
    | some ka =>
      cases hb : scalar? depth b with
      | none => simp [ha, hb] at h
      | some kb =>
        simp [ha, hb] at h
        subst h
        have hA := scalar?_kind ha
        have hB := scalar?_kind hb
        cases ka <;> cases kb <;> simp [machOuts?, hA, hB, Scalar.binder, ResShape.ctor?, ResShape.ports]
  · rename_i hne
    cases hs : scalar? depth e with
    | none => simp [hs] at h
    | some k =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      subst h
      exact scalar?_outs senv hs

theorem sigGo_outs (senv : StructEnv) (e : Lean.Expr) : ∀ (depth : Nat) (acc : List Scalar) (sh : SigShape), sigGo depth acc e = some sh →
    machOuts? senv e = some (sh.res.ctor?, sh.res.ports) := by
  induction e with
  | forallE n ty b bi ihty ihb =>
    intro depth acc sh h
    simp only [sigGo] at h
    cases hk : scalar? depth ty with
    | none => simp [hk] at h
    | some k =>
      simp only [hk, Option.bind_some] at h
      simpa [machOuts?] using ihb (depth + 1) (acc ++ [k]) sh h
  | _ =>
    all_goals
      intro depth acc sh h
      simp only [sigGo, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      exact resShape?_outs senv hr

theorem sigShape?_machOuts (senv : StructEnv) {ty : Lean.Expr} {sh : SigShape} (h : sigShape? ty = some sh) :
    machOuts? senv ty = some (sh.res.ctor?, sh.res.ports) := by
  cases ty with
  | forallE n t b bi =>
    simp only [sigShape?] at h
    split at h
    · simpa [machOuts?] using sigGo_outs senv b 1 [] sh h
    · cases h
  | _ => simp [sigShape?] at h

/-! ## `DeclConnect` as the instance of the accepted abstract core (Part A, `Pk : Type u`) -/

/-- The relation `ConstValue` is only a TYPE here (the inductive `ConstValueE` is the DCF unit's, not written). -/
abbrev ConstValueRel := Environment → Name → (α : Type) → α → Prop

def MatchC (sh : SigShape) (p : Pkg ι dom) : Prop := ShapeMatches sh p.d p.kD
def ObsC (p : Pkg ι dom) (sh : SigShape) (v : sh.Ty) : Prop :=
  ∀ i bools bits, sh.obs (dom := dom) v i bools bits = p.src i bools bits

/-- `DeclConnect` at one name. -/
def DeclConnectAt (CV : ConstValueRel) (env₀ : Environment) (P : Pkgs ι dom) (X : Name) : Prop :=
  Tools.ShippingGen5DeclConnectAbs.DCAt (fun e n => e.find? n) CV shapeOf (fun sh p => MatchC sh p) (fun p sh v => ObsC p sh v) P env₀ X

def DeclConnect (CV : ConstValueRel) (env₀ : Environment) (P : Pkgs ι dom) (Tgt : Name → Prop) : Prop :=
  Tools.ShippingGen5DeclConnectAbs.DCGen (fun e n => e.find? n) CV shapeOf (fun sh p => MatchC sh p) (fun p sh v => ObsC p sh v) P env₀ Tgt

/-- The unfolding equation (statement written without `DCGen`/`DCAt`). -/
theorem declConnect_eq (CV : ConstValueRel) (env₀ : Environment) (P : Pkgs ι dom) (Tgt : Name → Prop) :
    DeclConnect CV env₀ P Tgt = (∀ X, Tgt X → ∀ p, P X = some p →
      ∃ (ci : ConstantInfo) (sh : SigShape) (v : sh.Ty), env₀.find? X = some ci ∧ shapeOf ci = some sh ∧ ShapeMatches sh p.d p.kD ∧
        CV env₀ X sh.Ty v ∧ ∀ i bools bits, sh.obs (dom := dom) v i bools bits = p.src i bools bits) := rfl

theorem declConnect_mono (CV : ConstValueRel) (env₀ : Environment) (P : Pkgs ι dom) {Tgt Tgt' : Name → Prop}
    (h : ∀ X, Tgt' X → Tgt X) : DeclConnect CV env₀ P Tgt → DeclConnect CV env₀ P Tgt' :=
  Tools.ShippingGen5DeclConnectAbs.dcGen_mono _ _ _ _ _ _ _ h

/-- Non-vacuity on the concrete instance: the empty relation does not satisfy `DeclConnect` at a target with a package. -/
theorem not_declConnect_of_empty (env₀ : Environment) (P : Pkgs ι dom) (Tgt : Name → Prop) {X : Name} {p : Pkg ι dom}
    (hT : Tgt X) (hP : P X = some p) : ¬ DeclConnect (fun _ _ _ _ => False) env₀ P Tgt :=
  Tools.ShippingGen5DeclConnectAbs.not_dcGen_of_empty _ _ _ _ _ _ _ hT hP

/-! ## U-ROWS (CONDITIONAL, INTERMEDIATE)

The Acc assembly of Part A (U6) at the concrete `DeclConnect`. The step `hstep` is the UNSUPPLIED content of the rows (existence of the
value `∃ α v, CV env₀ X α v`, unfolding of the body, shape/body, quote/eval agreement, `src = obs (stateLoop …)`, calls): it is an explicit
hypothesis, not a result. Nothing here supplies `CV`, `P`, the order `R`, or `Acc`. Reported as an assembly skeleton, not completion. -/
theorem declConnect_of_rows (CV : ConstValueRel) (env₀ : Environment) (P : Pkgs ι dom) (Tgt : Name → Prop) {R : Name → Name → Prop}
    (hAcc : ∀ X, Tgt X → Acc R X) (hclosed : ∀ X c, Tgt X → R c X → Tgt c)
    (hstep : ∀ X, Tgt X → (∀ c, R c X → Tgt c → DeclConnectAt CV env₀ P c) → DeclConnectAt CV env₀ P X) :
    DeclConnect CV env₀ P Tgt :=
  Tools.ShippingGen5DeclConnectAbs.dcGen_of_rows _ _ _ _ _ _ _ _ hAcc hclosed hstep

end Tools.ShippingGen5DeclConnect

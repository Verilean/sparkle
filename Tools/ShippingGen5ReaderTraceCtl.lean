import Tools.ShippingGen5ReaderTrace
import Tools.ShippingLetsReaderInv
import Tools.ShippingReaderFuelDefs
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceCtl, exit 0) on the tree of b450d6e5 (source content identical; this header is comment-only). Written against freeze rev2 `scripts/gen5/DG_READERTRACE_FREEZE_REV2.md`. Clean issue-linked build is the coder's. No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R1b: `GroupsPh / CtlPh / TrInv / callSt / callOut / PhPre / ExprPh / ChainPh / RootPh / PhPost / TracePre / TracePost / TraceGood` and five leaf lemmas

Statements are those of `DG_READERTRACE_FREEZE_REV2.md` §1. The definitions prove nothing about `readF`: `TraceGood nDecl (readF senv n)`, R-in / R-nl / R-dom for `readF` calls,
U-R2 onward, `PhFacts` and the real run / FG are not supplied here. "Unconditional" for the leaf lemmas means only that no new external law is added; they keep their `h` / `hn` / success hypotheses. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Sparkle.Compiler.MachInstOrigin Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

def GroupsPh (senv : StructEnv) (st : MachRead) : Prop :=
  ∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder),
     st.insts[k]? = some (c, js, r) → st.instOrigins[k]? = some (InstOrigin.field 0) →
     ∃ (kinds : List MixedGateBinder) (ty resTy : Lean.Expr) (args : List Lean.Expr) (ctor : Name)
       (fields : List (String × MixedGateBinder)),
       senv.instS c = some (kinds, ty) ∧ instRes ty args = some resTy ∧
       machOuts? senv resTy = some (some ctor, fields) ∧ k + fields.length ≤ st.insts.size

def CtlPh (senv : StructEnv) (nDecl : Nat) (st : MachRead) : Prop :=
  (∀ x ∈ st.loopWs.toList, x.1 + x.2.1 ≤ st.kinds.size) ∧
  (∀ x ∈ st.bareRegs.toList, x.2 < st.kinds.size) ∧
  (∀ x ∈ st.nested.toList, InRange nDecl st st.lets.size x.2.2.2.2.2 ∧ NoLoose 0 x.2.2.2.2.2) ∧
  DomPh nDecl st ∧
  LetsNoLoose st ∧
  GroupsPh senv st

def TrInv (senv : StructEnv) (nDecl : Nat) (st : MachRead) : Prop := FullInv nDecl st ∧ CtlPh senv nDecl st

def callSt : Call → MachRead
  | .conv _ _ _ st | .nested _ _ _ _ _ st | .inst _ _ _ _ _ _ st | .instS _ _ _ _ _ st
  | .chain _ _ st | .loopBody _ _ _ st | .loopRoot _ _ st => st

def callOut : (c : Call) → c.Res → MachRead
  | .conv .., p => (p : Lean.Expr × MachRead).2
  | .nested .., p => (p : Lean.Expr × MachRead).2
  | .inst .., p => (p : Lean.Expr × MachRead).2
  | .instS .., p => (p : Lean.Expr × MachRead).2
  | .chain .., p => (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead).2.2
  | .loopBody .., s => (s : MachRead)
  | .loopRoot .., p => (p : MachVal × MachRead).2

def PhPre (senv : StructEnv) (nDecl : Nat) : Call → Prop
  | .conv env d e st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (d + env.length + nDecl) e = true
  | .nested env dom _ _ body st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh dom = true ∧ BvarLt (env.length + nDecl) dom = true ∧
      NoPh body = true ∧ BvarLt (env.length + 1 + nDecl) body = true
  | .inst env _ org kinds res args st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧
      (∀ a ∈ args, NoPh a = true ∧ BvarLt (env.length + nDecl) a = true) ∧
      (org = InstOrigin.ord ∨
        ∃ cb aw dw, org = InstOrigin.mem cb aw dw ∧
          kinds = [MixedGateBinder.domain, .bits aw, .bits dw, .bool, .bits aw] ∧ res = .bits dw ∧ args.length = 5)
  | .instS env c kinds ty args st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧
      senv.instS c = some (kinds, ty) ∧ args.length = kinds.length ∧
      (∀ a ∈ args, NoPh a = true ∧ BvarLt (env.length + nDecl) a = true) ∧
      NoPh ty = true ∧ BvarLt (env.length + nDecl) ty = true
  | .chain env e st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (env.length + nDecl) e = true
  | .loopBody base env e st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (env.length + nDecl) e = true ∧
      (∀ regs, machLoopRegs (machLetTail e) = some regs → base + regs.length ≤ st.kinds.size)
  | .loopRoot env e st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (env.length + nDecl) e = true

abbrev ExprPh (senv : StructEnv) (nDecl d : Nat) (p : Lean.Expr × MachRead) : Prop :=
  TrInv senv nDecl p.2 ∧ InRange nDecl p.2 p.2.lets.size p.1 ∧ NoLoose d p.1

abbrev ChainPh (senv : StructEnv) (nDecl : Nat) (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead) : Prop :=
  TrInv senv nDecl p.2.2 ∧
  (∀ w ∈ p.1, w.1 < p.2.2.kinds.size ∧ InRange nDecl p.2.2 p.2.2.lets.size w.2) ∧
  InRange nDecl p.2.2 p.2.2.lets.size p.2.1 ∧ NoLoose 0 p.2.1

abbrev RootPh (senv : StructEnv) (nDecl : Nat) (p : MachVal × MachRead) : Prop :=
  TrInv senv nDecl p.2 ∧
  (∀ b n, p.1 = MachVal.state b n → b + n ≤ p.2.kinds.size) ∧
  (∀ v, p.1 = MachVal.val v → InRange nDecl p.2 p.2.lets.size v ∧ NoLoose 0 v)

def PhPost (senv : StructEnv) (nDecl : Nat) : (c : Call) → c.Res → Prop
  | .conv _ d _ _, p => ExprPh senv nDecl d (p : Lean.Expr × MachRead)
  | .nested .., p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .inst .., p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .instS .., p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .chain .., p => ChainPh senv nDecl (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead)
  | .loopBody .., s => TrInv senv nDecl (s : MachRead)
  | .loopRoot .., p => RootPh senv nDecl (p : MachVal × MachRead)

def TracePre (senv : StructEnv) (nDecl : Nat) (c : Call) : Prop := Pre c ∧ PhPre senv nDecl c

def TracePost (senv : StructEnv) (nDecl : Nat) (c : Call) (v : c.Res) : Prop :=
  Post c v ∧ FReachC nDecl (callSt c) (callOut c v) ∧ PhPost senv nDecl c v

def TraceGood (senv : StructEnv) (nDecl : Nat) (h : Hs) : Prop :=
  ∀ c, TracePre senv nDecl c → ∀ v, h c = some (some v) → TracePost senv nDecl c v

/-! ## Leaf lemmas -/

theorem trInv_empty {senv : StructEnv} {nDecl : Nat} : TrInv senv nDecl ({} : MachRead) := by
  refine ⟨fullInv_empty, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; simp at hx
  · intro x hx; simp at hx
  · intro x hx; simp at hx
  · intro d hd; simp at hd
  · intro j nm kd v hj; simp at hj
  · intro k c js r hk; simp at hk

theorem bindLetNamed_reach {nDecl : Nat} {st : MachRead} {nm : Name} {ty v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v') :
    FReachC nDecl st { st with lets := (machBindLetNamed nm ty v' st.lets).2 } ∧
    InRange nDecl { st with lets := (machBindLetNamed nm ty v' st.lets).2 } (machBindLetNamed nm ty v' st.lets).2.size
      (machBindLetNamed nm ty v' st.lets).1 ∧
    NoLoose 0 (machBindLetNamed nm ty v' st.lets).1 := by
  unfold machBindLetNamed
  split
  · exact ⟨FReachC.refl st, h, hn⟩
  · exact ⟨FReachC.refl st, h, hn⟩
  · split
    · next j hj =>
      exact ⟨FReachC.refl st, inRange_machLet (Array.findIdx?_eq_some_iff_getElem.mp hj).1, fun _ hh => (hh : False)⟩
    · refine ⟨reachC_letv st _ _ v' h, ?_, fun _ hh => (hh : False)⟩
      simp only [Array.size_push]
      exact inRange_machLet (Nat.lt_succ_self _)

theorem letIndex_reach {nDecl : Nat} {st : MachRead} {nm : Name} {kd : MixedGateBinder} {v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v') :
    FReachC nDecl st { st with lets := (machLetIndex nm kd v' st.lets).2 } ∧
    (machLetIndex nm kd v' st.lets).1 < (machLetIndex nm kd v' st.lets).2.size := by
  unfold machLetIndex
  split
  · next j => exact ⟨FReachC.refl st, h.2.2.2 j ⟨rfl, rfl⟩⟩
  · split
    · next j hj => exact ⟨FReachC.refl st, (Array.findIdx?_eq_some_iff_getElem.mp hj).1⟩
    · refine ⟨reachC_letv st _ _ v' h, ?_⟩
      simp only [Array.size_push]
      exact Nat.lt_succ_self _

theorem machInstCall?_spec {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr} (h : machInstCall? senv e = some (c, kinds, res, args)) :
    senv.inst c = some (kinds, res) ∧ args.length = kinds.length := by
  unfold machInstCall? at h
  split at h
  · next c' _ args' _ =>
    split at h
    · next kinds' res' hi =>
      split at h
      · next hl =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨hi, beq_iff_eq.mp hl⟩
      · simp at h
    · simp at h
  · simp at h

theorem machInstCallS?_spec {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr} (h : machInstCallS? senv e = some (c, kinds, ty, args)) :
    senv.instS c = some (kinds, ty) ∧ args.length = kinds.length := by
  unfold machInstCallS? at h
  split at h
  · next c' _ args' _ =>
    split at h
    · next kinds' ty' hi =>
      split at h
      · next hl =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨hi, beq_iff_eq.mp hl⟩
      · simp at h
    · simp at h
  · simp at h

end Tools.ShippingGen5ReaderTrace

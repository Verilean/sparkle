import Tools.ShippingGen5ReaderTraceCtl
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in Pod (kjob lake build Tests.Gen5.ReaderTraceCtlCheck, exit 0, 724 jobs) on the tree of the R1 fix (13 defs added to closure roots; this header line is the only later, comment-only change). Measured: TYPE 9 non-match defs/abbrevs + 5 leaf theorems = 14 compared (0 isDefEq fallbacks logged); MATCHDEF 4 defs x 7 ctors agree + 4 full-argument theorems (callSt_eq_exp, callOut_eq_exp, phPre_eq_exp, phPost_eq_exp); MUTANT 14 value/statement (10 def + 4 theorem; distinct from the 10 match-def mutants below) + 10 well-typed match-def mutants (each rejected at exactly the changed constructor), no ill-typed variant counted; AXIOMS 9 theorems standard only (trInv_empty [propext], machInstCall?_spec [propext,Quot.sound], ...); CLOSURE OK 3973 constants from 22 roots (13 defs + 9 theorems), all 18 target declarations (13 defs + 5 leaf theorems) asserted in seen, with 3 negative + 3 forbidden-root self-hit + 2 clean controls, UNKNOWN 3 negative / 1 clean; 3 intended sorry negatives print 3 warnings. Mutants are signature/defeq rejections, not semantic counterexamples. Clean build is the coder's. No sorry / axiom / native_decide in source; the intended sorry-based negatives of the closure controls are built in memory (no `sorry` token).
/-! # DG-READERTRACE U-R1b checks (Tools/ShippingGen5ReaderTraceCtl.lean)

TYPE: each def / theorem of `DG_READERTRACE_FREEZE_REV2.md` §1 is compared by `checkExpected` (`Tests/Gen3/ExpectedType.lean`) against an `Exp…` statement written here from the freeze text (own spelling).
Match defs (`callSt, callOut, PhPre, PhPost`): independent `Exp` match version + a FULL-argument agreement theorem (`cases c <;> rfl`), plus a per-constructor defeq comparer `ctorAgree`
(the SAME comparer for the real def and for mutants). Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples); ill-typed variants are not counted.
CLOSURE: value-closure walk, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceCtlCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Sparkle.Compiler.MachInstOrigin Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

section Expected

def ExpGroupsPh : StructEnv → MachRead → Prop := fun senv st =>
  ∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder),
     st.insts[k]? = some (c, js, r) → st.instOrigins[k]? = some (InstOrigin.field 0) →
     ∃ (kinds : List MixedGateBinder) (ty resTy : Lean.Expr) (args : List Lean.Expr) (ctor : Name)
       (fields : List (String × MixedGateBinder)),
       senv.instS c = some (kinds, ty) ∧ instRes ty args = some resTy ∧
       machOuts? senv resTy = some (some ctor, fields) ∧ k + fields.length ≤ st.insts.size

def ExpCtlPh : StructEnv → Nat → MachRead → Prop := fun senv nDecl st =>
  (∀ x ∈ st.loopWs.toList, x.1 + x.2.1 ≤ st.kinds.size) ∧
  (∀ x ∈ st.bareRegs.toList, x.2 < st.kinds.size) ∧
  (∀ x ∈ st.nested.toList, InRange nDecl st st.lets.size x.2.2.2.2.2 ∧ NoLoose 0 x.2.2.2.2.2) ∧
  DomPh nDecl st ∧ LetsNoLoose st ∧ GroupsPh senv st

def ExpTrInv : StructEnv → Nat → MachRead → Prop := fun senv nDecl st => FullInv nDecl st ∧ CtlPh senv nDecl st

def ExpExprPh : StructEnv → Nat → Nat → Lean.Expr × MachRead → Prop := fun senv nDecl d p =>
  TrInv senv nDecl p.2 ∧ InRange nDecl p.2 p.2.lets.size p.1 ∧ NoLoose d p.1

def ExpChainPh : StructEnv → Nat → List (Nat × Lean.Expr) × Lean.Expr × MachRead → Prop := fun senv nDecl p =>
  TrInv senv nDecl p.2.2 ∧
  (∀ w ∈ p.1, w.1 < p.2.2.kinds.size ∧ InRange nDecl p.2.2 p.2.2.lets.size w.2) ∧
  InRange nDecl p.2.2 p.2.2.lets.size p.2.1 ∧ NoLoose 0 p.2.1

def ExpRootPh : StructEnv → Nat → MachVal × MachRead → Prop := fun senv nDecl p =>
  TrInv senv nDecl p.2 ∧
  (∀ b n, p.1 = MachVal.state b n → b + n ≤ p.2.kinds.size) ∧
  (∀ v, p.1 = MachVal.val v → InRange nDecl p.2 p.2.lets.size v ∧ NoLoose 0 v)

def ExpTracePre : StructEnv → Nat → Call → Prop := fun senv nDecl c => Pre c ∧ PhPre senv nDecl c

def ExpTracePost : StructEnv → Nat → (c : Call) → c.Res → Prop := fun senv nDecl c v =>
  Post c v ∧ FReachC nDecl (callSt c) (callOut c v) ∧ PhPost senv nDecl c v

def ExpTraceGood : StructEnv → Nat → Hs → Prop := fun senv nDecl h =>
  ∀ c, TracePre senv nDecl c → ∀ v, h c = some (some v) → TracePost senv nDecl c v

-- independent match versions (own spelling)
def ExpCallSt : Call → MachRead
  | .conv _ _ _ s => s
  | .nested _ _ _ _ _ s => s
  | .inst _ _ _ _ _ _ s => s
  | .instS _ _ _ _ _ s => s
  | .chain _ _ s => s
  | .loopBody _ _ _ s => s
  | .loopRoot _ _ s => s

def ExpCallOut : (c : Call) → c.Res → MachRead
  | .conv .., p => Prod.snd (p : Lean.Expr × MachRead)
  | .nested .., p => Prod.snd (p : Lean.Expr × MachRead)
  | .inst .., p => Prod.snd (p : Lean.Expr × MachRead)
  | .instS .., p => Prod.snd (p : Lean.Expr × MachRead)
  | .chain .., p => Prod.snd (Prod.snd (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead))
  | .loopBody .., s => (s : MachRead)
  | .loopRoot .., p => Prod.snd (p : MachVal × MachRead)

def ExpPhPre (senv : StructEnv) (nDecl : Nat) : Call → Prop
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

def ExpPhPost (senv : StructEnv) (nDecl : Nat) : (c : Call) → c.Res → Prop
  | .conv _ d _ _, p => ExprPh senv nDecl d (p : Lean.Expr × MachRead)
  | .nested .., p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .inst .., p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .instS .., p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .chain .., p => ChainPh senv nDecl (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead)
  | .loopBody .., s => TrInv senv nDecl (s : MachRead)
  | .loopRoot .., p => RootPh senv nDecl (p : MachVal × MachRead)

theorem callSt_eq_exp : ∀ c : Call, callSt c = ExpCallSt c := by intro c; cases c <;> rfl
theorem callOut_eq_exp : ∀ (c : Call) (v : c.Res), callOut c v = ExpCallOut c v := by intro c; cases c <;> intro v <;> rfl
theorem phPre_eq_exp : ∀ (senv : StructEnv) (nDecl : Nat) (c : Call), PhPre senv nDecl c = ExpPhPre senv nDecl c := by
  intro senv nDecl c; cases c <;> rfl
theorem phPost_eq_exp : ∀ (senv : StructEnv) (nDecl : Nat) (c : Call) (v : c.Res), PhPost senv nDecl c v = ExpPhPost senv nDecl c v := by
  intro senv nDecl c; cases c <;> intro v <;> rfl

-- theorem statements
def ExpTrInvEmpty : Prop := ∀ {senv : StructEnv} {nDecl : Nat}, TrInv senv nDecl ({} : MachRead)
def ExpBindLetNamedReach : Prop := ∀ {nDecl : Nat} {st : MachRead} {nm : Name} {ty v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v'),
    FReachC nDecl st { st with lets := (machBindLetNamed nm ty v' st.lets).2 } ∧
    InRange nDecl { st with lets := (machBindLetNamed nm ty v' st.lets).2 } (machBindLetNamed nm ty v' st.lets).2.size
      (machBindLetNamed nm ty v' st.lets).1 ∧
    NoLoose 0 (machBindLetNamed nm ty v' st.lets).1
def ExpLetIndexReach : Prop := ∀ {nDecl : Nat} {st : MachRead} {nm : Name} {kd : MixedGateBinder} {v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v'),
    FReachC nDecl st { st with lets := (machLetIndex nm kd v' st.lets).2 } ∧
    (machLetIndex nm kd v' st.lets).1 < (machLetIndex nm kd v' st.lets).2.size
def ExpInstCallSpec : Prop := ∀ {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr} (h : machInstCall? senv e = some (c, kinds, res, args)),
    senv.inst c = some (kinds, res) ∧ args.length = kinds.length
def ExpInstCallSSpec : Prop := ∀ {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr} (h : machInstCallS? senv e = some (c, kinds, ty, args)),
    senv.instS c = some (kinds, ty) ∧ args.length = kinds.length

-- value mutants (non-match defs and theorems)
def MutCtlPhNoDom : StructEnv → Nat → MachRead → Prop := fun senv nDecl st =>
  (∀ x ∈ st.loopWs.toList, x.1 + x.2.1 ≤ st.kinds.size) ∧
  (∀ x ∈ st.bareRegs.toList, x.2 < st.kinds.size) ∧
  (∀ x ∈ st.nested.toList, InRange nDecl st st.lets.size x.2.2.2.2.2 ∧ NoLoose 0 x.2.2.2.2.2) ∧
  LetsNoLoose st ∧ GroupsPh senv st
def MutCtlPhNoGroups : StructEnv → Nat → MachRead → Prop := fun _ nDecl st =>
  (∀ x ∈ st.loopWs.toList, x.1 + x.2.1 ≤ st.kinds.size) ∧
  (∀ x ∈ st.bareRegs.toList, x.2 < st.kinds.size) ∧
  (∀ x ∈ st.nested.toList, InRange nDecl st st.lets.size x.2.2.2.2.2 ∧ NoLoose 0 x.2.2.2.2.2) ∧
  DomPh nDecl st ∧ LetsNoLoose st
def MutCtlPhNoLetsNoLoose : StructEnv → Nat → MachRead → Prop := fun senv nDecl st =>
  (∀ x ∈ st.loopWs.toList, x.1 + x.2.1 ≤ st.kinds.size) ∧
  (∀ x ∈ st.bareRegs.toList, x.2 < st.kinds.size) ∧
  (∀ x ∈ st.nested.toList, InRange nDecl st st.lets.size x.2.2.2.2.2 ∧ NoLoose 0 x.2.2.2.2.2) ∧
  DomPh nDecl st ∧ GroupsPh senv st
def MutGroupsPhLt : StructEnv → MachRead → Prop := fun senv st =>
  ∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder),
     st.insts[k]? = some (c, js, r) → st.instOrigins[k]? = some (InstOrigin.field 0) →
     ∃ (kinds : List MixedGateBinder) (ty resTy : Lean.Expr) (args : List Lean.Expr) (ctor : Name)
       (fields : List (String × MixedGateBinder)),
       senv.instS c = some (kinds, ty) ∧ instRes ty args = some resTy ∧
       machOuts? senv resTy = some (some ctor, fields) ∧ k < st.insts.size
def MutTracePostNoReach : StructEnv → Nat → (c : Call) → c.Res → Prop := fun senv nDecl c v =>
  Post c v ∧ PhPost senv nDecl c v
def MutTracePostNoPhPost : StructEnv → Nat → (c : Call) → c.Res → Prop := fun _ nDecl c v =>
  Post c v ∧ FReachC nDecl (callSt c) (callOut c v)
def MutTraceGoodNone : StructEnv → Nat → Hs → Prop := fun senv nDecl h =>
  ∀ c, TracePre senv nDecl c → ∀ v, h c = some none → TracePost senv nDecl c v
def MutTrInvFullOnly : StructEnv → Nat → MachRead → Prop := fun _ nDecl st => FullInv nDecl st
def MutExprPhNoLoose : StructEnv → Nat → Nat → Lean.Expr × MachRead → Prop := fun senv nDecl _ p =>
  TrInv senv nDecl p.2 ∧ InRange nDecl p.2 p.2.lets.size p.1 ∧ NoLoose 0 p.1
def MutTracePreNoPh : StructEnv → Nat → Call → Prop := fun _ _ c => Pre c
def MutLetIndexNoLt : Prop := ∀ {nDecl : Nat} {st : MachRead} {nm : Name} {kd : MixedGateBinder} {v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v'),
    FReachC nDecl st { st with lets := (machLetIndex nm kd v' st.lets).2 }
def MutBindLetNamedFReach : Prop := ∀ {nDecl : Nat} {st : MachRead} {nm : Name} {ty v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v'),
    FReach nDecl st { st with lets := (machBindLetNamed nm ty v' st.lets).2 } ∧
    InRange nDecl { st with lets := (machBindLetNamed nm ty v' st.lets).2 } (machBindLetNamed nm ty v' st.lets).2.size
      (machBindLetNamed nm ty v' st.lets).1 ∧
    NoLoose 0 (machBindLetNamed nm ty v' st.lets).1
def MutInstCallSNoLen : Prop := ∀ {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr} (h : machInstCallS? senv e = some (c, kinds, ty, args)),
    senv.instS c = some (kinds, ty)
def MutInstCallNoLen : Prop := ∀ {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr} (h : machInstCall? senv e = some (c, kinds, res, args)),
    senv.inst c = some (kinds, res)

-- match-def mutants (well-typed single changes; compared by `ctorAgree`)
def MutCallStConvEmpty : Call → MachRead
  | .conv _ _ _ _ => {}
  | .nested _ _ _ _ _ s => s
  | .inst _ _ _ _ _ _ s => s
  | .instS _ _ _ _ _ s => s
  | .chain _ _ s => s
  | .loopBody _ _ _ s => s
  | .loopRoot _ _ s => s

def MutCallOutConvInput : (c : Call) → c.Res → MachRead
  | .conv _ _ _ s, _ => s
  | .nested .., p => Prod.snd (p : Lean.Expr × MachRead)
  | .inst .., p => Prod.snd (p : Lean.Expr × MachRead)
  | .instS .., p => Prod.snd (p : Lean.Expr × MachRead)
  | .chain .., p => Prod.snd (Prod.snd (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead))
  | .loopBody .., s => (s : MachRead)
  | .loopRoot .., p => Prod.snd (p : MachVal × MachRead)

def MutCallOutChainEmpty : (c : Call) → c.Res → MachRead
  | .conv .., p => Prod.snd (p : Lean.Expr × MachRead)
  | .nested .., p => Prod.snd (p : Lean.Expr × MachRead)
  | .inst .., p => Prod.snd (p : Lean.Expr × MachRead)
  | .instS .., p => Prod.snd (p : Lean.Expr × MachRead)
  | .chain .., _ => {}
  | .loopBody .., s => (s : MachRead)
  | .loopRoot .., p => Prod.snd (p : MachVal × MachRead)

def MutPhPreInstSNoSig (senv : StructEnv) (nDecl : Nat) : Call → Prop
  | .instS env _ kinds ty args st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧
      args.length = kinds.length ∧
      (∀ a ∈ args, NoPh a = true ∧ BvarLt (env.length + nDecl) a = true) ∧
      NoPh ty = true ∧ BvarLt (env.length + nDecl) ty = true
  | c => ExpPhPre senv nDecl c

def MutPhPreInstMemOnly (senv : StructEnv) (nDecl : Nat) : Call → Prop
  | .inst env _ org kinds res args st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧
      (∀ a ∈ args, NoPh a = true ∧ BvarLt (env.length + nDecl) a = true) ∧
      (∃ cb aw dw, org = InstOrigin.mem cb aw dw ∧
          kinds = [MixedGateBinder.domain, .bits aw, .bits dw, .bool, .bits aw] ∧ res = .bits dw ∧ args.length = 5)
  | c => ExpPhPre senv nDecl c

def MutPhPreInstNoLen5 (senv : StructEnv) (nDecl : Nat) : Call → Prop
  | .inst env _ org kinds res args st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧
      (∀ a ∈ args, NoPh a = true ∧ BvarLt (env.length + nDecl) a = true) ∧
      (org = InstOrigin.ord ∨
        ∃ cb aw dw, org = InstOrigin.mem cb aw dw ∧
          kinds = [MixedGateBinder.domain, .bits aw, .bits dw, .bool, .bits aw] ∧ res = .bits dw)
  | c => ExpPhPre senv nDecl c

def MutPhPreConvNoD (senv : StructEnv) (nDecl : Nat) : Call → Prop
  | .conv env _ e st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (env.length + nDecl) e = true
  | c => ExpPhPre senv nDecl c

def MutPhPreLoopBodyNoBound (senv : StructEnv) (nDecl : Nat) : Call → Prop
  | .loopBody _ env e st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (env.length + nDecl) e = true
  | c => ExpPhPre senv nDecl c

def MutPhPostConvZero (senv : StructEnv) (nDecl : Nat) : (c : Call) → c.Res → Prop
  | .conv _ _ _ _, p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .nested .., p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .inst .., p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .instS .., p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .chain .., p => ChainPh senv nDecl (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead)
  | .loopBody .., s => TrInv senv nDecl (s : MachRead)
  | .loopRoot .., p => RootPh senv nDecl (p : MachVal × MachRead)

def MutPhPostLoopBodyFull (senv : StructEnv) (nDecl : Nat) : (c : Call) → c.Res → Prop
  | .conv _ d _ _, p => ExprPh senv nDecl d (p : Lean.Expr × MachRead)
  | .nested .., p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .inst .., p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .instS .., p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .chain .., p => ChainPh senv nDecl (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead)
  | .loopBody .., s => FullInv nDecl (s : MachRead)
  | .loopRoot .., p => RootPh senv nDecl (p : MachVal × MachRead)

end Expected

/-- The SAME per-constructor comparer for the real match def `f` and for every mutant `g` (both applied to `lead` fresh leading arguments, then a `Call`
built from fresh constructor arguments, then, when `withRes`, a fresh `c.Res` value): all 7 constructors must be defeq. Returns the failing constructors. -/
def ctorAgree (f g : Name) (nLead : Nat) (withRes : Bool) : MetaM (List Name) := do
  let callCtors : List Name := [``Call.conv, ``Call.nested, ``Call.inst, ``Call.instS, ``Call.chain, ``Call.loopBody, ``Call.loopRoot]
  let fTy ← inferType (mkConst f)
  let gTy ← inferType (mkConst g)
  unless (← isDefEq fTy gTy) do throwError "GEN5 CTLCHECK ctorAgree: signatures of {f} and {g} differ"
  let mut bad : List Name := []
  for ctor in callCtors do
    let ok ← forallTelescope (← inferType (mkConst ctor)) fun cargs _ => do
      let c := mkAppN (mkConst ctor) cargs
      forallBoundedTelescope fTy (some nLead) fun lead _ => do
        let mkApp' (n : Name) (extra : Array Expr) := mkAppN (mkConst n) (lead ++ #[c] ++ extra)
        if withRes then
          let resTy ← whnfR (mkApp (mkConst ``Call.Res) c)
          withLocalDeclD `v resTy fun v =>
            withoutModifyingState (isDefEq (mkApp' f #[v]) (mkApp' g #[v]))
        else
          withoutModifyingState (isDefEq (mkApp' f #[]) (mkApp' g #[]))
    unless ok do bad := bad ++ [ctor]
  pure bad

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``GroupsPh ``ExpGroupsPh
  checkExpected ``CtlPh ``ExpCtlPh
  checkExpected ``TrInv ``ExpTrInv
  checkExpected ``ExprPh ``ExpExprPh
  checkExpected ``ChainPh ``ExpChainPh
  checkExpected ``RootPh ``ExpRootPh
  checkExpected ``TracePre ``ExpTracePre
  checkExpected ``TracePost ``ExpTracePost
  checkExpected ``TraceGood ``ExpTraceGood
  logInfo m!"GEN5 CTLCHECK TYPE 9 non-match defs/abbrevs compared by value (GroupsPh, CtlPh, TrInv, ExprPh, ChainPh, RootPh, TracePre, TracePost, TraceGood)"
  checkExpected ``trInv_empty ``ExpTrInvEmpty
  checkExpected ``bindLetNamed_reach ``ExpBindLetNamedReach
  checkExpected ``letIndex_reach ``ExpLetIndexReach
  checkExpected ``machInstCall?_spec ``ExpInstCallSpec
  checkExpected ``machInstCallS?_spec ``ExpInstCallSSpec
  logInfo m!"GEN5 CTLCHECK TYPE 5 leaf theorems"
  -- match defs: real vs independent Exp, per constructor, same comparer
  for (f, g, nl, wr) in [(``callSt, ``ExpCallSt, 0, false), (``callOut, ``ExpCallOut, 0, true),
      (``PhPre, ``ExpPhPre, 2, false), (``PhPost, ``ExpPhPost, 2, true)] do
    let bad ← ctorAgree f g nl wr
    unless bad.isEmpty do throwError "GEN5 CTLCHECK CHECK FAILED: {f} disagrees with {g} at {bad}"
  logInfo m!"GEN5 CTLCHECK MATCHDEF 4 defs (callSt, callOut, PhPre, PhPost) x 7 constructors agree with the independent versions; whole-domain agreement is the 4 theorems callSt_eq_exp, callOut_eq_exp, phPre_eq_exp, phPost_eq_exp"
  -- value mutants
  checkMutant ``CtlPh ``MutCtlPhNoDom
  checkMutant ``CtlPh ``MutCtlPhNoGroups
  checkMutant ``CtlPh ``MutCtlPhNoLetsNoLoose
  checkMutant ``GroupsPh ``MutGroupsPhLt
  checkMutant ``TracePost ``MutTracePostNoReach
  checkMutant ``TracePost ``MutTracePostNoPhPost
  checkMutant ``TraceGood ``MutTraceGoodNone
  checkMutant ``TrInv ``MutTrInvFullOnly
  checkMutant ``ExprPh ``MutExprPhNoLoose
  checkMutant ``TracePre ``MutTracePreNoPh
  checkMutant ``letIndex_reach ``MutLetIndexNoLt
  checkMutant ``bindLetNamed_reach ``MutBindLetNamedFReach
  checkMutant ``machInstCallS?_spec ``MutInstCallSNoLen
  checkMutant ``machInstCall?_spec ``MutInstCallNoLen
  logInfo m!"GEN5 CTLCHECK MUTANT 14 statement/value mutants (10 def + 4 theorem) rejected"
  -- match-def mutants through ctorAgree against the independent version
  let mm : List (Name × Name × Nat × Bool × List Name) :=
    [ (``MutCallStConvEmpty, ``ExpCallSt, 0, false, [``Call.conv]),
      (``MutCallOutConvInput, ``ExpCallOut, 0, true, [``Call.conv]),
      (``MutCallOutChainEmpty, ``ExpCallOut, 0, true, [``Call.chain]),
      (``MutPhPreInstSNoSig, ``ExpPhPre, 2, false, [``Call.instS]),
      (``MutPhPreInstMemOnly, ``ExpPhPre, 2, false, [``Call.inst]),
      (``MutPhPreInstNoLen5, ``ExpPhPre, 2, false, [``Call.inst]),
      (``MutPhPreConvNoD, ``ExpPhPre, 2, false, [``Call.conv]),
      (``MutPhPreLoopBodyNoBound, ``ExpPhPre, 2, false, [``Call.loopBody]),
      (``MutPhPostConvZero, ``ExpPhPost, 2, true, [``Call.conv]),
      (``MutPhPostLoopBodyFull, ``ExpPhPost, 2, true, [``Call.loopBody]) ]
  let mut nm : Nat := 0
  for (g, ex, nl, wr, expectBad) in mm do
    -- the mutant must disagree with the independent version exactly at the changed constructor
    let bad ← ctorAgree g ex nl wr
    unless bad == expectBad do throwError "GEN5 CTLCHECK MATCHDEF MUTANT ACCEPTED/UNEXPECTED: {g} disagrees at {bad}, expected {expectBad}"
    nm := nm + 1
  logInfo m!"GEN5 CTLCHECK MATCHDEF MUTANT {nm} well-typed match-def mutants each rejected at exactly the changed constructor (signature/defeq rejection, not a semantic counterexample)"

def allThms : List Name := [``trInv_empty, ``bindLetNamed_reach, ``letIndex_reach, ``machInstCall?_spec, ``machInstCallS?_spec,
  ``callSt_eq_exp, ``callOut_eq_exp, ``phPre_eq_exp, ``phPost_eq_exp]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in allThms do checkAxioms n
  logInfo m!"GEN5 CTLCHECK AXIOMS {allThms.length} theorems checked (standard axioms only)"

-- the 13 U-R1b definitions (3 abbrev + 10 def), named explicitly; closure roots = these 13 + the 5 leaf theorems + the 4 match-agreement theorems = 22 names
-- of which the 18 declarations (13 defs + 5 leaf theorems) are the freeze targets that must all be in `seen`.
def allDefs : List Name := [``GroupsPh, ``CtlPh, ``TrInv, ``callSt, ``callOut, ``PhPre, ``PhPost,
  ``ExprPh, ``ChainPh, ``RootPh, ``TracePre, ``TracePost, ``TraceGood]
def leafThms : List Name := [``trInv_empty, ``bindLetNamed_reach, ``letIndex_reach, ``machInstCall?_spec, ``machInstCallS?_spec]
def closureRoots : List Name := allDefs ++ allThms

/-! ## Closure audit -/

def valueOfCI : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

partial def closureOf (env : Environment) (root : Name) : StateT (NameSet × NameSet) MetaM Unit := do
  if (← get).1.contains root then return
  modify fun (s, u) => (s.insert root, u)
  match env.find? root with
  | none => modify fun (s, u) => (s, u.insert root)
  | some ci =>
    for c in ci.type.getUsedConstants do closureOf env c
    match valueOfCI ci with
    | some v => for c in v.getUsedConstants do closureOf env c
    | none => pure ()
    match ci with
    | .inductInfo v => for c in v.ctors do closureOf env c
    | _ => pure ()

def forbiddenConsts : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler]

def closureHits (env : Environment) (roots : List Name) : MetaM (NameSet × NameSet × List Name) := do
  let (_, (seen, unk)) ← (roots.forM (closureOf env)).run ({}, {})
  pure (seen, unk, forbiddenConsts.filter seen.contains)

-- Negative controls (built in memory, no `sorry` token in this file): each must be detected; clean controls must not be.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let bad := mkApp2 (mkConst ``sorryAx [Level.zero]) tru (mkConst ``Bool.false)
    let ok := mkConst ``True.intro
    addDecl (.thmDecl { name := `ReaderTraceCtl.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceCtl.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceCtl.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceCtl.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceCtl.direct, `ReaderTraceCtl.viaHelper, `ReaderTraceCtl.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 CTLCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 CTLCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceCtl.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 CTLCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 CTLCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceCtl.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceCtl.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceCtl.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceCtl.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceCtl.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceCtl.Missing.nowhere do throwError "GEN5 CTLCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceCtl.viaHelperU, `ReaderTraceCtl.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceCtl.Missing.nowhere do throwError "GEN5 CTLCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceCtl.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 CTLCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 CTLCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless allDefs.length == 13 && leafThms.length == 5 do throwError "GEN5 CTLCHECK CLOSURE FAILED: expected 13 defs + 5 leaf theorems"
  for n in allDefs ++ leafThms do
    unless seen.contains n do throwError "GEN5 CTLCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 CTLCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 CTLCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 CTLCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 CTLCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (13 defs + 9 theorems); all 18 target declarations (13 defs + 5 leaf theorems) in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceCtlCheck

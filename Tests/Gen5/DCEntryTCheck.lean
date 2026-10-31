import Lean
import Tools.ShippingGen5DCEntryT
import Tests.Gen3.ExpectedType
import Tests.Gen5.DeclConnectCheck
set_option autoImplicit false
-- U-RUNT checks (scripts/gen5/DC_CONNECT_RUNT_FREEZE.md §4). Issue-linked clean build dc21v-0fcce4e7 exit 0 (751 jobs); approved at 0fcce4e7.
-- Counts (measured): TYPE 5 + self-comparison 5 (the 10 TYPE OK lines are not 10 independent comparisons); SOURCE-PIN 4 + PIN-NEG 4; MUT 39 (single change); BLOCK 0; CONJ 0; AX 5; CLOSURE 5 roots. 40 binder comparisons pass via isDefEq only because of local abbrevs (Dsg/WE/Chd/..), logged as GEN3 DEFEQ.

/-! # DC-CONNECT U-RUNT: checks

TYPE: `ExpCM`/`ExpSC`/`ExpRC`/`ExpKT`/`ExpRT` written from the prose of §3, plus constant-type pins of `stepModuleTG`, `runModuleTG`, `KSn`
and `NoRawBelow` (independent Expected types, compared binder by binder). MUTANT: well-typed single-change variants rejected by the SAME
comparator -- signature/defeq rejections, NOT semantic counterexamples. The freeze's depth-change mutant (`KSn .. (n+1)` on the right) is
ill-typed (the state `s : KT n` does not have type `KT (n+1)`), so it is NOT adopted and NOT counted. BLOCK: none. CONJ: none in the five
theorems; the source-pin negative controls are counted separately as PIN-NEG. -/
open Lean Meta Tests.Gen3.ExpectedType
open Tools.ShippingGen5DCEntryR (NoRawBelow)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingHierStateG (KStep KState KT KSn stepModuleTG runModuleTG)
open Sparkle.IR.Machine (moduleByName)

namespace Tests.Gen5.DCEntryTCheck

abbrev Mod := Sparkle.IR.AST.Module
abbrev Dsg := Sparkle.IR.AST.Design
abbrev Stm := Sparkle.IR.AST.Stmt
abbrev Exr := Sparkle.IR.AST.Expr
abbrev WE := Sparkle.IR.Semantics.WEnv
abbrev En := Sparkle.IR.Semantics.Env
abbrev Chd := String → Option (Mod × WE)

/-- EXPECTED: if D' agrees with D on every name other than rn, the child maps agree on every name other than rn. -/
def ExpCM : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn) (mn : String) (hne : mn ≠ rn), childMap D'.modules mn = childMap D.modules mn

/-- MUTANT: hlk dropped. -/
def MutCMnoHlk : Prop := ∀ {D D' : Dsg} {rn : String} (mn : String) (hne : mn ≠ rn), childMap D'.modules mn = childMap D.modules mn

/-- MUTANT: hlk for all mn. -/
def MutCMallMn : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, moduleByName D'.modules mn = moduleByName D.modules mn) (mn : String) (hne : mn ≠ rn), childMap D'.modules mn = childMap D.modules mn

/-- MUTANT: hne dropped. -/
def MutCMnoHne : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn) (mn : String) , childMap D'.modules mn = childMap D.modules mn

/-- MUTANT: conclusion sides swapped (D = D'). -/
def MutCMswapD : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn) (mn : String) (hne : mn ≠ rn), childMap D.modules mn = childMap D'.modules mn

/-- MUTANT: hlk direction swapped. -/
def MutCMhlkSwap : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D.modules mn = moduleByName D'.modules mn) (mn : String) (hne : mn ≠ rn), childMap D'.modules mn = childMap D.modules mn

/-- MUTANT: conclusion on D' both sides. -/
def MutCMdesign : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn) (mn : String) (hne : mn ≠ rn), childMap D'.modules mn = childMap D'.modules mn

/-- EXPECTED: congruence of the one-cycle step in the child map and the child step, on the instances of the body. -/
def ExpSC : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    (hch : ∀ (mn iname : String) (conns : List (String × Exr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Exr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Mod) (cwe : WE), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Exr)) (env : En) (s : σ), KS' c cwe cin env s = KS c cwe cin env s)
    (env0 : En) (s : KState σ),
    stepModuleTG KS' we ch' body env0 s = stepModuleTG KS we ch body env0 s

/-- MUTANT: hch dropped. -/
def MutSCnoHch : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    
    (hKS : ∀ (mn iname : String) (conns : List (String × Exr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Mod) (cwe : WE), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Exr)) (env : En) (s : σ), KS' c cwe cin env s = KS c cwe cin env s)
    (env0 : En) (s : KState σ),
    stepModuleTG KS' we ch' body env0 s = stepModuleTG KS we ch body env0 s

/-- MUTANT: hKS dropped. -/
def MutSCnoHks : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    (hch : ∀ (mn iname : String) (conns : List (String × Exr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    
    (env0 : En) (s : KState σ),
    stepModuleTG KS' we ch' body env0 s = stepModuleTG KS we ch body env0 s

/-- MUTANT: hch conclusion `ch mn = ch mn`. -/
def MutSChchSelf : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    (hch : ∀ (mn iname : String) (conns : List (String × Exr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Exr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Mod) (cwe : WE), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Exr)) (env : En) (s : σ), KS' c cwe cin env s = KS c cwe cin env s)
    (env0 : En) (s : KState σ),
    stepModuleTG KS' we ch' body env0 s = stepModuleTG KS we ch body env0 s

/-- MUTANT: in hKS, `ch' mn = some` instead of `ch mn = some`. -/
def MutSChksPrime : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    (hch : ∀ (mn iname : String) (conns : List (String × Exr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Exr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Mod) (cwe : WE), ch' mn = some (c, cwe) →
        ∀ (cin : List (String × Exr)) (env : En) (s : σ), KS' c cwe cin env s = KS c cwe cin env s)
    (env0 : En) (s : KState σ),
    stepModuleTG KS' we ch' body env0 s = stepModuleTG KS we ch body env0 s

/-- MUTANT: hKS conclusion with KS on both sides. -/
def MutSChksSame : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    (hch : ∀ (mn iname : String) (conns : List (String × Exr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Exr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Mod) (cwe : WE), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Exr)) (env : En) (s : σ), KS c cwe cin env s = KS c cwe cin env s)
    (env0 : En) (s : KState σ),
    stepModuleTG KS' we ch' body env0 s = stepModuleTG KS we ch body env0 s

/-- MUTANT: hKS conclusion sides swapped. -/
def MutSChksSwap : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    (hch : ∀ (mn iname : String) (conns : List (String × Exr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Exr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Mod) (cwe : WE), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Exr)) (env : En) (s : σ), KS c cwe cin env s = KS' c cwe cin env s)
    (env0 : En) (s : KState σ),
    stepModuleTG KS' we ch' body env0 s = stepModuleTG KS we ch body env0 s

/-- EXPECTED: congruence of the run in the child map and the child step, on the instances of the body. -/
def ExpRC : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    (hch : ∀ (mn iname : String) (conns : List (String × Exr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Exr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Mod) (cwe : WE), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Exr)) (env : En) (s : σ), KS' c cwe cin env s = KS c cwe cin env s)
    (seed : Nat → (String → Nat) → En),
    ∀ (T : Nat) (s : KState σ), runModuleTG KS' we ch' body seed T s = runModuleTG KS we ch body seed T s

/-- MUTANT: hch dropped. -/
def MutRCnoHch : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    
    (hKS : ∀ (mn iname : String) (conns : List (String × Exr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Mod) (cwe : WE), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Exr)) (env : En) (s : σ), KS' c cwe cin env s = KS c cwe cin env s)
    (seed : Nat → (String → Nat) → En),
    ∀ (T : Nat) (s : KState σ), runModuleTG KS' we ch' body seed T s = runModuleTG KS we ch body seed T s

/-- MUTANT: hKS dropped. -/
def MutRCnoHks : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    (hch : ∀ (mn iname : String) (conns : List (String × Exr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    
    (seed : Nat → (String → Nat) → En),
    ∀ (T : Nat) (s : KState σ), runModuleTG KS' we ch' body seed T s = runModuleTG KS we ch body seed T s

/-- MUTANT: hch conclusion `ch mn = ch mn`. -/
def MutRChchSelf : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    (hch : ∀ (mn iname : String) (conns : List (String × Exr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Exr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Mod) (cwe : WE), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Exr)) (env : En) (s : σ), KS' c cwe cin env s = KS c cwe cin env s)
    (seed : Nat → (String → Nat) → En),
    ∀ (T : Nat) (s : KState σ), runModuleTG KS' we ch' body seed T s = runModuleTG KS we ch body seed T s

/-- MUTANT: in hKS, `ch' mn = some` instead of `ch mn = some`. -/
def MutRChksPrime : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    (hch : ∀ (mn iname : String) (conns : List (String × Exr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Exr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Mod) (cwe : WE), ch' mn = some (c, cwe) →
        ∀ (cin : List (String × Exr)) (env : En) (s : σ), KS' c cwe cin env s = KS c cwe cin env s)
    (seed : Nat → (String → Nat) → En),
    ∀ (T : Nat) (s : KState σ), runModuleTG KS' we ch' body seed T s = runModuleTG KS we ch body seed T s

/-- MUTANT: hKS conclusion with KS on both sides. -/
def MutRChksSame : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    (hch : ∀ (mn iname : String) (conns : List (String × Exr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Exr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Mod) (cwe : WE), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Exr)) (env : En) (s : σ), KS c cwe cin env s = KS c cwe cin env s)
    (seed : Nat → (String → Nat) → En),
    ∀ (T : Nat) (s : KState σ), runModuleTG KS' we ch' body seed T s = runModuleTG KS we ch body seed T s

/-- MUTANT: hKS conclusion sides swapped. -/
def MutRChksSwap : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    (hch : ∀ (mn iname : String) (conns : List (String × Exr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Exr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Mod) (cwe : WE), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Exr)) (env : En) (s : σ), KS c cwe cin env s = KS' c cwe cin env s)
    (seed : Nat → (String → Nat) → En),
    ∀ (T : Nat) (s : KState σ), runModuleTG KS' we ch' body seed T s = runModuleTG KS we ch body seed T s

/-- MUTANT: T fixed to 0. -/
def MutRCzero : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    (hch : ∀ (mn iname : String) (conns : List (String × Exr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Exr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Mod) (cwe : WE), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Exr)) (env : En) (s : σ), KS' c cwe cin env s = KS c cwe cin env s)
    (seed : Nat → (String → Nat) → En),
    ∀ (s : KState σ), runModuleTG KS' we ch' body seed 0 s = runModuleTG KS we ch body seed 0 s

/-- MUTANT: body reversed on the left side. -/
def MutRCrev : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    (hch : ∀ (mn iname : String) (conns : List (String × Exr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Exr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Mod) (cwe : WE), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Exr)) (env : En) (s : σ), KS' c cwe cin env s = KS c cwe cin env s)
    (seed : Nat → (String → Nat) → En),
    ∀ (T : Nat) (s : KState σ), runModuleTG KS' we ch' body.reverse seed T s = runModuleTG KS we ch body seed T s

/-- MUTANT: body reversed on the left side. -/
def MutSCrev : Prop := ∀ {σ : Type} {KS KS' : KStep σ} {we : WE} {ch ch' : Chd} {body : List Stm}
    (hch : ∀ (mn iname : String) (conns : List (String × Exr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Exr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Mod) (cwe : WE), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Exr)) (env : En) (s : σ), KS' c cwe cin env s = KS c cwe cin env s)
    (env0 : En) (s : KState σ),
    stepModuleTG KS' we ch' body.reverse env0 s = stepModuleTG KS we ch body env0 s

/-- EXPECTED: the depth-n child step over D' equals the one over D on a module with NoRawBelow D rn n. -/
def ExpKT : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (child : Mod), NoRawBelow D rn n child →
      ∀ (cwe : WE) (cin : List (String × Exr)) (env : En) (s : KT n),
        KSn (childMap D'.modules) n child cwe cin env s = KSn (childMap D.modules) n child cwe cin env s

/-- MUTANT: hlk dropped. -/
def MutKTnoHlk : Prop := ∀ {D D' : Dsg} {rn : String},
    ∀ (n : Nat) (child : Mod), NoRawBelow D rn n child →
      ∀ (cwe : WE) (cin : List (String × Exr)) (env : En) (s : KT n),
        KSn (childMap D'.modules) n child cwe cin env s = KSn (childMap D.modules) n child cwe cin env s

/-- MUTANT: hlk for all mn. -/
def MutKTallMn : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (child : Mod), NoRawBelow D rn n child →
      ∀ (cwe : WE) (cin : List (String × Exr)) (env : En) (s : KT n),
        KSn (childMap D'.modules) n child cwe cin env s = KSn (childMap D.modules) n child cwe cin env s

/-- MUTANT: NoRawBelow hypothesis dropped. -/
def MutKTnoNrb : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (child : Mod), True →
      ∀ (cwe : WE) (cin : List (String × Exr)) (env : En) (s : KT n),
        KSn (childMap D'.modules) n child cwe cin env s = KSn (childMap D.modules) n child cwe cin env s

/-- MUTANT: NoRawBelow over D'. -/
def MutKTprime : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (child : Mod), NoRawBelow D' rn n child →
      ∀ (cwe : WE) (cin : List (String × Exr)) (env : En) (s : KT n),
        KSn (childMap D'.modules) n child cwe cin env s = KSn (childMap D.modules) n child cwe cin env s

/-- MUTANT: NoRawBelow at depth n+1. -/
def MutKTdepth : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (child : Mod), NoRawBelow D rn (n+1) child →
      ∀ (cwe : WE) (cin : List (String × Exr)) (env : En) (s : KT n),
        KSn (childMap D'.modules) n child cwe cin env s = KSn (childMap D.modules) n child cwe cin env s

/-- MUTANT: right side over D'. -/
def MutKTrhsD : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (child : Mod), NoRawBelow D rn n child →
      ∀ (cwe : WE) (cin : List (String × Exr)) (env : En) (s : KT n),
        KSn (childMap D'.modules) n child cwe cin env s = KSn (childMap D'.modules) n child cwe cin env s

/-- MUTANT: sides swapped. -/
def MutKTswap : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (child : Mod), NoRawBelow D rn n child →
      ∀ (cwe : WE) (cin : List (String × Exr)) (env : En) (s : KT n),
        KSn (childMap D.modules) n child cwe cin env s = KSn (childMap D'.modules) n child cwe cin env s

/-- MUTANT: NoRawBelow with the empty name. -/
def MutKTrn : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (child : Mod), NoRawBelow D "" n child →
      ∀ (cwe : WE) (cin : List (String × Exr)) (env : En) (s : KT n),
        KSn (childMap D'.modules) n child cwe cin env s = KSn (childMap D.modules) n child cwe cin env s

/-- EXPECTED: the run of a module over the D' child map equals the run over the D child map, given NoRawBelow D rn (n+1). -/
def ExpRT : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (we : WE) (seed : Nat → (String → Nat) → En) (T : Nat)
      (s : KState (KT n)),
      NoRawBelow D rn (n + 1) mc →
      runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) mc.body seed T s = runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) mc.body seed T s

/-- MUTANT: hlk dropped. -/
def MutRTnoHlk : Prop := ∀ {D D' : Dsg} {rn : String} ,
    ∀ (n : Nat) (mc : Mod) (we : WE) (seed : Nat → (String → Nat) → En) (T : Nat)
      (s : KState (KT n)),
      NoRawBelow D rn (n + 1) mc →
      runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) mc.body seed T s = runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) mc.body seed T s

/-- MUTANT: hlk for all mn. -/
def MutRTallMn : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (we : WE) (seed : Nat → (String → Nat) → En) (T : Nat)
      (s : KState (KT n)),
      NoRawBelow D rn (n + 1) mc →
      runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) mc.body seed T s = runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) mc.body seed T s

/-- MUTANT: NoRawBelow hypothesis dropped. -/
def MutRTnoNrb : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (we : WE) (seed : Nat → (String → Nat) → En) (T : Nat)
      (s : KState (KT n)),
      True →
      runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) mc.body seed T s = runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) mc.body seed T s

/-- MUTANT: NoRawBelow at depth n. -/
def MutRTdepth : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (we : WE) (seed : Nat → (String → Nat) → En) (T : Nat)
      (s : KState (KT n)),
      NoRawBelow D rn n mc →
      runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) mc.body seed T s = runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) mc.body seed T s

/-- MUTANT: NoRawBelow over D'. -/
def MutRTprime : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (we : WE) (seed : Nat → (String → Nat) → En) (T : Nat)
      (s : KState (KT n)),
      NoRawBelow D' rn (n + 1) mc →
      runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) mc.body seed T s = runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) mc.body seed T s

/-- MUTANT: right side over D'. -/
def MutRTrhsD : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (we : WE) (seed : Nat → (String → Nat) → En) (T : Nat)
      (s : KState (KT n)),
      NoRawBelow D rn (n + 1) mc →
      runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) mc.body seed T s = runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) mc.body seed T s

/-- MUTANT: body reversed on one side. -/
def MutRTrev : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (we : WE) (seed : Nat → (String → Nat) → En) (T : Nat)
      (s : KState (KT n)),
      NoRawBelow D rn (n + 1) mc →
      runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) mc.body.reverse seed T s = runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) mc.body seed T s

/-- MUTANT: sides swapped. -/
def MutRTswap : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (we : WE) (seed : Nat → (String → Nat) → En) (T : Nat)
      (s : KState (KT n)),
      NoRawBelow D rn (n + 1) mc →
      runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) mc.body seed T s = runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) mc.body seed T s

/-- MUTANT: T fixed to 0. -/
def MutRTzero : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (we : WE) (seed : Nat → (String → Nat) → En) 
      (s : KState (KT n)),
      NoRawBelow D rn (n + 1) mc →
      runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) mc.body seed 0 s = runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) mc.body seed 0 s

/-- MUTANT: NoRawBelow with the empty name. -/
def MutRTrn : Prop := ∀ {D D' : Dsg} {rn : String} (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn),
    ∀ (n : Nat) (mc : Mod) (we : WE) (seed : Nat → (String → Nat) → En) (T : Nat)
      (s : KState (KT n)),
      NoRawBelow D "" (n + 1) mc →
      runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) mc.body seed T s = runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) mc.body seed T s

/-! ## source pins: constant TYPES, written independently -/
def PinStep : Type 1 := ∀ {σ : Type} (KS : KStep σ) (we : WE) (children : Chd) (body : List Stm) (env0 : En) (s : KState σ),
  Option (En × KState σ)
def PinStepMut : Type 1 := ∀ {σ : Type} (KS : KStep σ) (we : WE) (children : Chd) (body : List Stm) (env0 : En) (s : KState σ),
  Option (En × σ)
def PinRun : Type 1 := ∀ {σ : Type} (KS : KStep σ) (we : WE) (children : Chd) (body : List Stm)
  (seed : Nat → (String → Nat) → En), Nat → KState σ → Option (List En)
def PinRunMut : Type 1 := ∀ {σ : Type} (KS : KStep σ) (we : WE) (children : Chd) (body : List Stm)
  (seed : Nat → (String → Nat) → En), Nat → KState σ → Option (List (List En))
def PinKSn : Type := ∀ (children : Chd) (n : Nat), KStep (KT n)
def PinKSnMut : Type := ∀ (children : Chd) (n : Nat), KStep (KT (n + 1))
def PinNRB : Type := ∀ (D : Dsg) (rn : String), Nat → Mod → Prop
def PinNRBMut : Type := ∀ (D : Dsg) (rn : String), Nat → Dsg → Prop

/-- the TYPE of constant `c` against the expected telescope `e` (a definition's value). -/
def checkPin (c e : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  let ex ← stmtOf e
  cmpTele s!"{c} (constant type)" ci.type ex
  logInfo m!"PIN OK {c} against {e}"
def checkPinNeg (c e : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  let ex ← stmtOf e
  let accepted ← withoutModifyingState do
    try cmpTele s!"{c} vs {e}" ci.type ex; pure true catch _ => pure false
  if accepted then throwError "PIN NEG ACCEPTED: {e} matches the type of {c}"
  logInfo m!"PIN NEG REJECTED {e} (against {c})"

def pins : List (Name × Name × Name) :=
  [(``stepModuleTG, ``PinStep, ``PinStepMut), (``runModuleTG, ``PinRun, ``PinRunMut), (``KSn, ``PinKSn, ``PinKSnMut),
   (``NoRawBelow, ``PinNRB, ``PinNRBMut)]
def table : List (Name × Name × List Name) :=
  [(``Tools.ShippingGen5DCEntryT.childMap_transport, ``ExpCM,
      [``MutCMnoHlk, ``MutCMallMn, ``MutCMnoHne, ``MutCMswapD, ``MutCMhlkSwap, ``MutCMdesign]),
   (``Tools.ShippingGen5DCEntryT.stepModuleTG_congr, ``ExpSC,
      [``MutSCnoHch, ``MutSCnoHks, ``MutSChchSelf, ``MutSChksPrime, ``MutSChksSame, ``MutSChksSwap, ``MutSCrev]),
   (``Tools.ShippingGen5DCEntryT.runModuleTG_congr, ``ExpRC,
      [``MutRCnoHch, ``MutRCnoHks, ``MutRChchSelf, ``MutRChksPrime, ``MutRChksSame, ``MutRChksSwap, ``MutRCzero, ``MutRCrev]),
   (``Tools.ShippingGen5DCEntryT.KSn_transport, ``ExpKT,
      [``MutKTnoHlk, ``MutKTallMn, ``MutKTnoNrb, ``MutKTprime, ``MutKTdepth, ``MutKTrhsD, ``MutKTswap, ``MutKTrn]),
   (``Tools.ShippingGen5DCEntryT.runModuleTG_transport, ``ExpRT,
      [``MutRTnoHlk, ``MutRTallMn, ``MutRTnoNrb, ``MutRTdepth, ``MutRTprime, ``MutRTrhsD, ``MutRTrev, ``MutRTswap, ``MutRTzero, ``MutRTrn])]

/-! ## closure -/
open Tests.Gen5.DeclConnectCheck (reach reachRaw violations)

def requiredOf : List (Name × List Name) :=
  [(``Tools.ShippingGen5DCEntryT.childMap_transport, [``childMap, ``moduleByName]),
   (``Tools.ShippingGen5DCEntryT.stepModuleTG_congr, [``stepModuleTG, ``Tools.ShippingHierStateG.evalAssignsKG]),
   (``Tools.ShippingGen5DCEntryT.runModuleTG_congr, [``runModuleTG, ``Tools.ShippingGen5DCEntryT.stepModuleTG_congr]),
   (``Tools.ShippingGen5DCEntryT.KSn_transport,
      [``KSn, ``Tools.ShippingHierStateG.succKS, ``NoRawBelow, ``Tools.ShippingGen5DCEntryT.stepModuleTG_congr,
       ``Tools.ShippingGen5DCEntryT.childMap_transport]),
   (``Tools.ShippingGen5DCEntryT.runModuleTG_transport,
      [``Tools.ShippingGen5DCEntryT.runModuleTG_congr, ``Tools.ShippingGen5DCEntryT.KSn_transport, ``NoRawBelow])]

def missingOf (r : Tests.Gen5.DeclConnectCheck.Reach) (req : List Name) : List Name := req.filter (!r.seen.contains ·)

/-- negative control: mentions `runModuleTG` but never the congruence lemma -/
def negNoLemma {σ : Type} (KS : KStep σ) (we : WE) (ch : Chd) (body : List Stm) (seed : Nat → (String → Nat) → En) (T : Nat)
    (s : KState σ) : Option (List En) := runModuleTG KS we ch body seed T s
/-- clean control: `runModuleTG_transport` through a helper -/
theorem cleanT {D D' : Dsg} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn)
    (n : Nat) (mc : Mod) (we : WE) (seed : Nat → (String → Nat) → En) (T : Nat) (s : KState (KT n))
    (h : NoRawBelow D rn (n + 1) mc) :
    runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) mc.body seed T s =
      runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) mc.body seed T s :=
  Tools.ShippingGen5DCEntryT.runModuleTG_transport hlk n mc we seed T s h

def ghostTy : Name := `Tests.Gen5.DCEntryTCheck.ghost_unknown_in_type
def ghostVal : Name := `Tests.Gen5.DCEntryTCheck.ghost_unknown_in_value
def fixEnv (env : Environment) : MetaM Environment := do
  let add (env : Environment) (n : Name) (ty v : Lean.Expr) : MetaM Environment :=
    match env.addDeclCore 0 (.defnDecl { name := n, levelParams := [], type := ty, value := v, hints := .abbrev, safety := .safe }) none (doCheck := false) with
    | .ok e => pure e
    | .error _ => throwError "fixture environment: could not add {n}"
  let nat := Lean.mkConst ``Nat
  let env ← add env `fixHelperTy (Lean.mkConst ghostTy) (Lean.mkConst ``Nat.zero)
  let env ← add env `fixHelperVal nat (Lean.mkConst ghostVal)
  let env ← add env `fixRootUsesTy nat (Lean.mkApp (Lean.mkConst ``id [1]) (Lean.mkConst `fixHelperTy))
  let env ← add env `fixRootUsesVal nat (Lean.mkApp (Lean.mkConst ``id [1]) (Lean.mkConst `fixHelperVal))
  add env `fixRootClean nat (Lean.mkConst ``Nat.zero)

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut nType : Nat := 0
  let mut nMut : Nat := 0
  let mut nPin : Nat := 0
  let mut nPinNeg : Nat := 0
  -- positive controls (self-comparison, not counted)
  for e in [``ExpCM, ``ExpSC, ``ExpRC, ``ExpKT, ``ExpRT] do withReducible <| checkExpected e e
  for (thm, e, ms) in table do
    withReducible <| checkExpected thm e
    nType := nType + 1
    for m in ms do
      withReducible <| checkMutant thm m
      nMut := nMut + 1
  for (c, e, m) in pins do
    withReducible <| checkPin c e
    nPin := nPin + 1
    withReducible <| checkPinNeg c m
    nPinNeg := nPinNeg + 1
  let targets := [``Tools.ShippingGen5DCEntryT.childMap_transport, ``Tools.ShippingGen5DCEntryT.stepModuleTG_congr,
    ``Tools.ShippingGen5DCEntryT.runModuleTG_congr, ``Tools.ShippingGen5DCEntryT.KSn_transport,
    ``Tools.ShippingGen5DCEntryT.runModuleTG_transport]
  for n in targets do checkAxioms n
  let mut nClosure : Nat := 0
  for (n, req) in requiredOf do
    let r ← reach env n
    unless r.axioms.isEmpty do throwError "CLOSURE FAILED {n}: axiom constants {r.axioms}"
    let v := violations env r
    unless v.isEmpty do throwError "CLOSURE FAILED {n}: forbidden {v}"
    let miss := missingOf r req
    unless miss.isEmpty do throwError "CLOSURE FAILED {n}: required constants not reached {miss}"
    nClosure := nClosure + 1
    logInfo m!"CLOSURE OK {n}: reached {r.seen.size}, opaque {r.opaques}, required {req}"
  let lemmaN := ``Tools.ShippingGen5DCEntryT.runModuleTG_congr
  let rn ← reach env ``negNoLemma
  unless (missingOf rn [lemmaN]).contains lemmaN do
    throwError "CLOSURE CONTROL NOT DETECTED negNoLemma"
  logInfo m!"CLOSURE CONTROL DETECTED negNoLemma (congruence lemma not reached)"
  let rc ← reach env ``cleanT
  unless (violations env rc).isEmpty && (missingOf rc [``Tools.ShippingGen5DCEntryT.KSn_transport, ``NoRawBelow]).isEmpty do
    throwError "CLOSURE CLEAN CONTROL FAILED"
  logInfo m!"CLOSURE CLEAN CONTROL OK cleanT"
  unless (violations env (← reach env ``Tests.Gen5.DeclConnectCheck.negDirect)).isEmpty == false do
    throwError "CLOSURE CONTROL NOT DETECTED negDirect (forbidden mention)"
  logInfo m!"CLOSURE CONTROL DETECTED negDirect (forbidden mention)"
  withoutModifyingEnv do
    setEnv (← fixEnv env)
    let envF ← getEnv
    for (root, ghost, what) in [(`fixRootUsesTy, ghostTy, "TYPE"), (`fixRootUsesVal, ghostVal, "VALUE")] do
      let raw ← reachRaw envF root
      unless raw.unknown == #[ghost] do
        throwError "UNKNOWN-NAME FIXTURE: expected exactly {ghost} unknown (the helper's {what}), got {raw.unknown}"
      let failed ← try let _ ← reach envF root; pure false catch _ => pure true
      unless failed do throwError "UNKNOWN-NAME FIXTURE: `reach` did not fail for {root}"
      logInfo m!"UNKNOWN-NAME FIXTURE DETECTED {root} (only the helper's {what} is unknown: {raw.unknown}), reach fails"
    let rcl ← reach envF `fixRootClean
    unless rcl.unknown.isEmpty do throwError "UNKNOWN-NAME FIXTURE CLEAN CONTROL FAILED"
    logInfo m!"UNKNOWN-NAME FIXTURE CLEAN CONTROL OK fixRootClean"
  let cur ← getEnv
  unless [`fixHelperTy, `fixHelperVal, `fixRootUsesTy, `fixRootUsesVal, `fixRootClean].all (cur.find? · |>.isNone) do
    throwError "fixture leaked into the environment"
  logInfo m!"COUNTS: TYPE {nType} (5 theorems; plus 5 self-comparisons not counted), SOURCE-PIN {nPin} (constant types of stepModuleTG, runModuleTG, KSn, NoRawBelow), PIN-NEG {nPinNeg} (changed expected pin rejected), MUTANT {nMut} (well-typed single change, signature/defeq rejection under withReducible, not semantic counterexamples), BLOCK 0, CONJ 0, AXIOMS {targets.length}, CLOSURE {nClosure} roots + 1 missing-requirement control + 1 forbidden-mention control + 1 clean control + unknown-name fixtures (2 detect: type-only, value-only; 1 clean)"
  logInfo m!"STATUS: NOT supplied by this unit: linking a core run's (raw, D) to a closeInsts equation (and hence to NoRawBelow), the lookup agreement hlk for compiler output, (a3), (b1), (b2), (c4 import), (c5), (c6), (c7), real EntryWitness, ReflectsAll, TopShips on D', O3, parametrised-route post-processing, Post adoption, FG"

end Tests.Gen5.DCEntryTCheck

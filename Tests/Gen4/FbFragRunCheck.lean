import Tools.ShippingGen4FbFragRun
import Tests.Gen4.FbPPCheck
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT (unit FB-22): written from scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §33.3/§33.4 (freeze 14e312de), independently of the proofs.
-- Text = §33.3/§33.4. Reuses `fbReach`/`auditOk`/`addFixture` of Tests.Gen4.FbPPCheck.
-- All TYPE/MUTANT comparisons run under `withReducible` (one comparator, as FbFragCheck).
-- Checks: TYPE (3 theorems), MUTANT (well-typed single changes; signature/defeq rejections, NOT semantic counterexamples),
-- value-closure audit (root judged itself; `missing` fails), controls (inside `withoutModifyingEnv`), AXIOMS.

namespace Tests.Gen4.FbFragRunCheck
open Lean Meta
open Tools.ShippingGen4FbFragRun
open Tests.Gen3.ExpectedType Tests.Gen4.FbPPCheck

def ExpRunExists : Prop :=
  ∀ {we : Sparkle.IR.Semantics.WEnv} {body : List Sparkle.IR.AST.Stmt}
    {seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env}
    (hA : body.all Sparkle.IR.RegDedup.isAssign = true)
    (st : String → Nat) (mems : Sparkle.IR.Semantics.MEnv),
    ∀ (T : Nat),
      (∀ j, j < T → ∃ e, Sparkle.IR.Semantics.evalAssigns we mems body (seed j st) = some e) →
      ∃ envs, Sparkle.IR.Semantics.runModule we body seed T st mems = some envs

def ExpCombRun : Prop :=
  ∀ {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {n : Nat} {mc : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {o : Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    {F : List Nat → Nat}
    (hpf : Tools.ShippingGen4FbPP.CombPortFacts mc bsC [o])
    (hA : mc.body.all Sparkle.IR.RegDedup.isAssign = true)
    (hfn : Tools.ShippingFirstGateChild.ChildFnR mc
      (fun vs => Tools.ShippingMachineChild.InRange vs (bsC.filter fun b => b.2 != .domain)) F)
    (hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j) (bsC.filter fun b => b.2 != .domain) →
        f j = F (vals j)),
    Tools.ShippingGen2.CombChildRunN ch dsn n mc bsC [o] S

def ExpFragRun : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : Tools.ShippingEntrySoundness.FExpr}
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName)
      mctx mref cctx cref w (b, design) w')
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref declName
      (Tools.ShippingEntrySoundness.quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {m : Nat}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs dn names n).filter fun x => x.2 != .domain) →
        f j = Tools.ShippingFirstGateChild.firstFn dn names n fe (vals j)),
    Tools.ShippingGen2.ChildRunN ch dsn m b (Tools.ShippingFirstGateChild.firstBs dn names n)
      [({ name := "out", lo := 0, width := n, ty := .bitVector n } : Sparkle.IR.Machine.OutField)] S

def MutRmeNoA : Prop :=
  ∀ {we : Sparkle.IR.Semantics.WEnv} {body : List Sparkle.IR.AST.Stmt}
    {seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env}
    
    (st : String → Nat) (mems : Sparkle.IR.Semantics.MEnv),
    ∀ (T : Nat),
      (∀ j, j < T → ∃ e, Sparkle.IR.Semantics.evalAssigns we mems body (seed j st) = some e) →
      ∃ envs, Sparkle.IR.Semantics.runModule we body seed T st mems = some envs

def MutRmeLe : Prop :=
  ∀ {we : Sparkle.IR.Semantics.WEnv} {body : List Sparkle.IR.AST.Stmt}
    {seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env}
    (hA : body.all Sparkle.IR.RegDedup.isAssign = true)
    (st : String → Nat) (mems : Sparkle.IR.Semantics.MEnv),
    ∀ (T : Nat),
      (∀ j, j ≤ T → ∃ e, Sparkle.IR.Semantics.evalAssigns we mems body (seed j st) = some e) →
      ∃ envs, Sparkle.IR.Semantics.runModule we body seed T st mems = some envs

def MutCcNoA : Prop :=
  ∀ {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {n : Nat} {mc : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {o : Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    {F : List Nat → Nat}
    (hpf : Tools.ShippingGen4FbPP.CombPortFacts mc bsC [o])
    
    (hfn : Tools.ShippingFirstGateChild.ChildFnR mc
      (fun vs => Tools.ShippingMachineChild.InRange vs (bsC.filter fun b => b.2 != .domain)) F)
    (hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j) (bsC.filter fun b => b.2 != .domain) →
        f j = F (vals j)),
    Tools.ShippingGen2.CombChildRunN ch dsn n mc bsC [o] S

def MutCcNoS : Prop :=
  ∀ {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {n : Nat} {mc : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {o : Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    {F : List Nat → Nat}
    (hpf : Tools.ShippingGen4FbPP.CombPortFacts mc bsC [o])
    (hA : mc.body.all Sparkle.IR.RegDedup.isAssign = true)
    (hfn : Tools.ShippingFirstGateChild.ChildFnR mc
      (fun vs => Tools.ShippingMachineChild.InRange vs (bsC.filter fun b => b.2 != .domain)) F)
    ,
    Tools.ShippingGen2.CombChildRunN ch dsn n mc bsC [o] S

def MutCcSeq : Prop :=
  ∀ {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {n : Nat} {mc : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {o : Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    {F : List Nat → Nat}
    (hpf : Tools.ShippingGen4FbPP.SeqPortFacts mc bsC [o])
    (hA : mc.body.all Sparkle.IR.RegDedup.isAssign = true)
    (hfn : Tools.ShippingFirstGateChild.ChildFnR mc
      (fun vs => Tools.ShippingMachineChild.InRange vs (bsC.filter fun b => b.2 != .domain)) F)
    (hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j) (bsC.filter fun b => b.2 != .domain) →
        f j = F (vals j)),
    Tools.ShippingGen2.CombChildRunN ch dsn n mc bsC [o] S

def MutCcEmpty : Prop :=
  ∀ {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {n : Nat} {mc : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {o : Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    {F : List Nat → Nat}
    (hpf : Tools.ShippingGen4FbPP.CombPortFacts mc bsC [o])
    (hA : mc.body.all Sparkle.IR.RegDedup.isAssign = true)
    (hfn : Tools.ShippingFirstGateChild.ChildFnR mc
      (fun vs => Tools.ShippingMachineChild.InRange vs (bsC.filter fun b => b.2 != .domain)) F)
    (hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j) (bsC.filter fun b => b.2 != .domain) →
        f j = F (vals j)),
    Tools.ShippingGen2.CombChildRunN ch dsn n mc bsC [] S

def MutCcF0 : Prop :=
  ∀ {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {n : Nat} {mc : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {o : Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    {F : List Nat → Nat}
    (hpf : Tools.ShippingGen4FbPP.CombPortFacts mc bsC [o])
    (hA : mc.body.all Sparkle.IR.RegDedup.isAssign = true)
    (hfn : Tools.ShippingFirstGateChild.ChildFnR mc
      (fun vs => Tools.ShippingMachineChild.InRange vs (bsC.filter fun b => b.2 != .domain)) F)
    (hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j) (bsC.filter fun b => b.2 != .domain) →
        f 0 = F (vals j)),
    Tools.ShippingGen2.CombChildRunN ch dsn n mc bsC [o] S

def MutFgNoN : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : Tools.ShippingEntrySoundness.FExpr}
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName)
      mctx mref cctx cref w (b, design) w')
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref declName
      (Tools.ShippingEntrySoundness.quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) 
    {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {m : Nat}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs dn names n).filter fun x => x.2 != .domain) →
        f j = Tools.ShippingFirstGateChild.firstFn dn names n fe (vals j)),
    Tools.ShippingGen2.ChildRunN ch dsn m b (Tools.ShippingFirstGateChild.firstBs dn names n)
      [({ name := "out", lo := 0, width := n, ty := .bitVector n } : Sparkle.IR.Machine.OutField)] S

def MutFgNoWf : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : Tools.ShippingEntrySoundness.FExpr}
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName)
      mctx mref cctx cref w (b, design) w')
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref declName
      (Tools.ShippingEntrySoundness.quoteDecl dn names n fe))
     (hn : 0 < n)
    {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {m : Nat}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs dn names n).filter fun x => x.2 != .domain) →
        f j = Tools.ShippingFirstGateChild.firstFn dn names n fe (vals j)),
    Tools.ShippingGen2.ChildRunN ch dsn m b (Tools.ShippingFirstGateChild.firstBs dn names n)
      [({ name := "out", lo := 0, width := n, ty := .bitVector n } : Sparkle.IR.Machine.OutField)] S

def MutFgNoEntry : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : Tools.ShippingEntrySoundness.FExpr}
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName)
      mctx mref cctx cref w (b, design) w')
    
    (hwf : fe.WF names.length n) (hn : 0 < n)
    {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {m : Nat}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs dn names n).filter fun x => x.2 != .domain) →
        f j = Tools.ShippingFirstGateChild.firstFn dn names n fe (vals j)),
    Tools.ShippingGen2.ChildRunN ch dsn m b (Tools.ShippingFirstGateChild.firstBs dn names n)
      [({ name := "out", lo := 0, width := n, ty := .bitVector n } : Sparkle.IR.Machine.OutField)] S

def MutFgNoS : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : Tools.ShippingEntrySoundness.FExpr}
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName)
      mctx mref cctx cref w (b, design) w')
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref declName
      (Tools.ShippingEntrySoundness.quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {m : Nat}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    ,
    Tools.ShippingGen2.ChildRunN ch dsn m b (Tools.ShippingFirstGateChild.firstBs dn names n)
      [({ name := "out", lo := 0, width := n, ty := .bitVector n } : Sparkle.IR.Machine.OutField)] S

def MutFgDz : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : Tools.ShippingEntrySoundness.FExpr}
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName)
      mctx mref cctx cref w (b, design) w')
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref declName
      (Tools.ShippingEntrySoundness.quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {m : Nat}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs dn names n).filter fun x => x.2 != .domain) →
        f j = Tools.ShippingFirstGateChild.firstFn dn names n fe (vals j)),
    Tools.ShippingGen2.ChildRunN ch dsn m (Sparkle.IR.ZeroWidth.dropZeroWidthModule b) (Tools.ShippingFirstGateChild.firstBs dn names n)
      [({ name := "out", lo := 0, width := n, ty := .bitVector n } : Sparkle.IR.Machine.OutField)] S

def MutFgM0 : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : Tools.ShippingEntrySoundness.FExpr}
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName)
      mctx mref cctx cref w (b, design) w')
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref declName
      (Tools.ShippingEntrySoundness.quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {m : Nat}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs dn names n).filter fun x => x.2 != .domain) →
        f j = Tools.ShippingFirstGateChild.firstFn dn names n fe (vals j)),
    Tools.ShippingGen2.ChildRunN ch dsn 0 b (Tools.ShippingFirstGateChild.firstBs dn names n)
      [({ name := "out", lo := 0, width := n, ty := .bitVector n } : Sparkle.IR.Machine.OutField)] S

def MutFgZero : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : Tools.ShippingEntrySoundness.FExpr}
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName)
      mctx mref cctx cref w (b, design) w')
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref declName
      (Tools.ShippingEntrySoundness.quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {m : Nat}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs dn names n).filter fun x => x.2 != .domain) →
        f j = (fun _ => 0) (vals j)),
    Tools.ShippingGen2.ChildRunN ch dsn m b (Tools.ShippingFirstGateChild.firstBs dn names n)
      [({ name := "out", lo := 0, width := n, ty := .bitVector n } : Sparkle.IR.Machine.OutField)] S

run_cmd Lean.Elab.Command.liftTermElabM do
  withReducible <| checkExpected ``runModule_assigns_exists ``ExpRunExists
  withReducible <| checkExpected ``combChildRunN_of_childFnR ``ExpCombRun
  withReducible <| checkExpected ``synthesizeCombinational_fragment_childRunN ``ExpFragRun
  withReducible <| checkMutant ``runModule_assigns_exists ``MutRmeNoA
  withReducible <| checkMutant ``runModule_assigns_exists ``MutRmeLe
  withReducible <| checkMutant ``combChildRunN_of_childFnR ``MutCcNoA
  withReducible <| checkMutant ``combChildRunN_of_childFnR ``MutCcNoS
  withReducible <| checkMutant ``combChildRunN_of_childFnR ``MutCcSeq
  withReducible <| checkMutant ``combChildRunN_of_childFnR ``MutCcEmpty
  withReducible <| checkMutant ``combChildRunN_of_childFnR ``MutCcF0
  withReducible <| checkMutant ``synthesizeCombinational_fragment_childRunN ``MutFgNoN
  withReducible <| checkMutant ``synthesizeCombinational_fragment_childRunN ``MutFgNoWf
  withReducible <| checkMutant ``synthesizeCombinational_fragment_childRunN ``MutFgNoEntry
  withReducible <| checkMutant ``synthesizeCombinational_fragment_childRunN ``MutFgNoS
  withReducible <| checkMutant ``synthesizeCombinational_fragment_childRunN ``MutFgDz
  withReducible <| checkMutant ``synthesizeCombinational_fragment_childRunN ``MutFgM0
  withReducible <| checkMutant ``synthesizeCombinational_fragment_childRunN ``MutFgZero

def frNew : List Name :=
  [``runModule_assigns_exists, ``combChildRunN_of_childFnR, ``synthesizeCombinational_fragment_childRunN]

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ghostN : Name := `Tests.Gen4.FbPPFixtureD.ghostName
  let ty0 : Lean.Expr := mkConst ``True
  -- control (a): absent root -> missing, audit not passed
  let r0 ← fbReach `Tests.Gen4.FbPPFixtureD.doesNotExistFr2
  if r0.missing.isEmpty || (← auditOk `Tests.Gen4.FbPPFixtureD.doesNotExistFr2) then
    throwError "FB22 AUDIT FAILED: absent root not reported"
  logInfo m!"FB22 RUN CONTROL absent root: missing {r0.missing.size}, audit not passed"
  -- control (b): forbidden root judged itself
  let rf ← fbReach ``Tools.ShippingMemo.memoInv_hit
  unless rf.hit == some [``Tools.ShippingMemo.memoInv_hit] do
    throwError "FB22 AUDIT FAILED: forbidden root not judged itself"
  logInfo m!"FB22 RUN CONTROL forbidden root Tools.ShippingMemo.memoInv_hit: flagged by the root rule"
  -- control (c): unknown name (i) in a helper value, (ii) in a helper TYPE only (root mentions neither); env restored
  let v ← withoutModifyingEnv do
    addFixture `Tests.Gen4.FbPPFixtureD.fr2HelperVal ty0 (mkConst ghostN)
    addFixture `Tests.Gen4.FbPPFixtureD.fr2RootVal ty0 (mkConst `Tests.Gen4.FbPPFixtureD.fr2HelperVal)
    addFixture `Tests.Gen4.FbPPFixtureD.fr2HelperTy (mkConst ghostN) (mkConst ``True.intro)
    addFixture `Tests.Gen4.FbPPFixtureD.fr2RootTy ty0
      (Lean.mkApp (Lean.mkLambda `_x .default ty0 (mkConst ``True.intro))
        (mkConst `Tests.Gen4.FbPPFixtureD.fr2HelperTy))
    addFixture `Tests.Gen4.FbPPFixtureD.fr2Clean ty0 (mkConst ``True.intro)
    let a ← fbReach `Tests.Gen4.FbPPFixtureD.fr2RootVal
    let b ← fbReach `Tests.Gen4.FbPPFixtureD.fr2RootTy
    let c ← fbReach `Tests.Gen4.FbPPFixtureD.fr2Clean
    pure (a.missing.contains ghostN, b.missing.contains ghostN, c.missing.size,
      (← auditOk `Tests.Gen4.FbPPFixtureD.fr2RootVal), (← auditOk `Tests.Gen4.FbPPFixtureD.fr2RootTy),
      (← auditOk `Tests.Gen4.FbPPFixtureD.fr2Clean))
  let (ga, gb, mc, oka, okb, okc) := v
  unless ga && !oka do throwError "FB22 AUDIT FAILED: helper-value ghost not reported"
  unless gb && !okb do throwError "FB22 AUDIT FAILED: helper-type-only ghost not reported"
  unless mc == 0 && okc do throwError "FB22 AUDIT FAILED: clean fixture not clean"
  if (← getEnv).contains `Tests.Gen4.FbPPFixtureD.fr2Clean then
    throwError "FB22 AUDIT FAILED: environment not restored"
  logInfo m!"FB22 RUN CONTROL unknown-name fixtures: ghostName in missing via helper value and via helper TYPE only; clean fixture clean"
  -- control (d): good real constant not flagged
  let rg ← fbReach ``Tools.ShippingGen4FbPP.ppRel_ports
  unless rg.hit.isNone && rg.missing.isEmpty do throwError "FB22 AUDIT FAILED: control ppRel_ports flagged"
  logInfo m!"FB22 RUN CONTROL good constant ppRel_ports: not flagged"
  for c in frNew do
    unless (← getEnv).contains c do throwError "FB22 AUDIT FAILED: intended name {c} missing"
    let r ← fbReach c
    if let some p := r.hit then throwError "FB22 AUDIT FAILED {c}: reaches Tools.ShippingMemo.* via {p}"
    unless r.missing.isEmpty do throwError "FB22 AUDIT NOT ESTABLISHED {c}: missing {r.missing}"
    logInfo m!"FB22 RUN REACH {c}: no Tools.ShippingMemo.* in the closure (visited {r.visited}, missing {r.missing.size}, opaque {r.opaques.size})"
  for c in frNew do
    checkAxioms c

end Tests.Gen4.FbFragRunCheck

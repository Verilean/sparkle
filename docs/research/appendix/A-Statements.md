# Appendix A: statements (verbatim from `2bcf256b`)

Signatures are copied verbatim from the files at the snapshot commit `2bcf256b`; proofs are omitted.
`file:line` is the line of the declaration. Where a statement mentions auxiliary definitions
(`ShapeCore`, `WidthStmt`, `HierShapeS`, ...), see the file. Read the notes in
[README.md](../README.md#the-guarantee-ladder) for what each rung does and does not give.

[Back to the research README](../README.md)

## `CorrStmt`

Port correspondence between the declaration's type and the contract. (`Tools/VedU1Contract.lean:295`)

```lean
def CorrStmt (c : Contract) : Prop :=
  c.table.binders.length = c.table.ins.length ∧
  c.inNames.length = c.table.ins.length ∧
  c.outNames.length = c.table.out.flat.length ∧
  (c.inNames ++ c.outNames ++ clkRstNames c).Nodup ∧
  (∀ p ∈ c.table.ins ++ c.table.out.flat, 0 < p.width)
```

## `OrderStmt`

Some arrangement assigns every wire before reading it; the body is a well-formed netlist. (`Tools/VedU1Contract.lean:464`)

```lean
def OrderStmt (m : Module) : Prop := ∃ b, OrderOk m b = true
```

## `OutputsStmt`

The order-free output statement: every well-ordered arrangement produces the declaration's outputs. (`Tools/VedU1Contract.lean:468`)

```lean
def OutputsStmt (c : Contract) (m : Module) (f : c.table.Ty) : Prop :=
  ∀ b, b.Perm m.body → Sparkle.IR.Reorder.WO [] b → OutputsOn c m b f
```

## `outputs_of_order`

From one checked arrangement to every arrangement. (`Tools/VedU1Contract.lean:474`)

```lean
theorem outputs_of_order {c : Contract} {m : Module} {f : c.table.Ty} (b0 : List Stmt)
    (h : OrderOk m b0 = true) (hout : OutputsOn c m b0 f) : OutputsStmt c m f := by
```

## `U1Stmt`

The statement `#ved_u1` / `#ved_u1_deep` register. (`Tools/VedU1Contract.lean:494`)

```lean
def U1Stmt (c : Contract) (m : Module) (f : c.table.Ty) : Prop :=
  CorrStmt c ∧ ShapeStmt c m ∧ WidthStmt c m ∧ OrderStmt m ∧ OutputsStmt c m f
```

## `PackedStmt`

`Signal d (A × B)` results (one packed port). (`Tools/VedU1Packed.lean:312`)

```lean
def PackedStmt (pc : PContract) (m : Module) (f : pc.tbl.Ty) : Prop :=
  PackCover pc ∧ U1Stmt pc.core m (packedF pc.tbl f) ∧ SlicesStmt pc m f
```

## `MemStmt`

Modules with memories (no instances). (`Tools/VedMem.lean:549`)

```lean
def MemStmt (c : Tools.VedU1Contract.Contract) (m : Module) (f : c.table.Ty) : Prop :=
  Tools.VedU1Contract.CorrStmt c ∧
  (Tools.VedU1Contract.ShapeCore c m ∧ instFree m.body = true) ∧
  Tools.VedU1Contract.WidthStmt c m ∧ OrderStmtM m ∧ Tools.VedU1Contract.OutputsStmt c m f
```

## `OutputsStmtHS`

The stateful closed hierarchical run exists and its outputs are the declaration's. (`Tools/VedU2HierStmt.lean:44`)

```lean
def OutputsStmtHS (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  ∀ arr, AdmArr d m arr → OutputsOnHS c m d arr f
```

## `U2HStmt`

Register-free parent with instances. (`Tools/VedU2HierStmt.lean:48`)

```lean
def U2HStmt (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  CorrStmt c ∧ ShapeCore c m ∧ c.clkRst = designClkRst d m ∧ HierShapeS d m = true ∧
  regsOf m.body = [] ∧ WidthStmt c m ∧ OrderHS d m ∧ (∀ x ∈ d.modules, OrderStmt x) ∧
  (∃ arr, AdmArr d m arr) ∧ OutputsStmtHS c m d f
```

## `U2HRStmt`

Parent with registers. (`Tools/VedU2HierReg.lean:38`)

```lean
def U2HRStmt (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  CorrStmt c ∧ ShapeCore c m ∧ c.clkRst = designClkRst d m ∧ HierShapeS d m = true ∧
  WidthStmt c m ∧ OrderHS d m ∧ (∀ x ∈ d.modules, OrderStmt x) ∧
  (∃ arr, AdmArr d m arr) ∧ OutputsStmtHS c m d f
```

## `Cdo.elab_general`

The general Signal-to-IR theorem over the closed deep grammar. (`Tools/DeepElab.lean:587`)

```lean
theorem Cdo.elab_general {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (names : Fin (Γr ++ Γi).length → String)
    (hinj : ∀ i j, names i = names j → i = j)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) (t : Nat) :
    ((c.outSig (dom := dom) inpS).val t).toNat
      = (evalExpr (weOfC names (fun j => (Γr ++ Γi).get j))
          (envOfC names (natJoin
            (c.irState names (fun t j => (inpS j).val t) t)
            (fun j => ((inpS j).val t).toNat)))
          (c.out.compile names)).getD 0 := by
```

## `runModule_perm`

Order-free meaning: all well-ordered arrangements agree. (`Sparkle/IR/ReorderInvariance.lean:1413`)

```lean
theorem runModule_perm (we : WEnv) {body body' : List Stmt}
    (hp : body.Perm body')
    (hWO : WO [] body) (hWO' : WO [] body')
    (hmem : (body.filterMap stmtMemName).Nodup)
    (hkeys : (nextKeys body).Nodup)
    (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv),
    runModule we body seed k st mems = runModule we body' seed k st mems := by
```

## `loop_val_unfold`

`Signal.loop` unfolding. (`Tools/VedU1Loop.lean:101`)

```lean
theorem loop_val_unfold {dom : DomainConfig} {α : Type} [Inhabited α]
    (F : Signal dom α → Signal dom α)
    (h0 : ∀ s₁ s₂ : Signal dom α, (F s₁).val 0 = (F s₂).val 0)
    (hS : ∀ (s₁ s₂ : Signal dom α) (t : Nat), s₁.val t = s₂.val t →
      (F s₁).val (t + 1) = (F s₂).val (t + 1)) (t : Nat) :
    (Signal.loop F).val t = (F (Signal.loop F)).val t := by
```

## `roundtrip_sem`

Expression-layer semantic roundtrip, on a fragment (rung 4). (`Tools/SVParser/RoundtripProof.lean:875`)

```lean
theorem roundtrip_sem {wof : String → Option Nat} {we : WEnv} {env : Env}
    {e : Sparkle.IR.AST.Expr} (h : SFrag wof we env e) :
    ∃ e', (emitAstExpr wof e).bind lowerT = some e'
      ∧ Sparkle.IR.Semantics.widthOf we e' = Sparkle.IR.Semantics.widthOf we e
      ∧ evalExpr we env e' = evalExpr we env e := by
```

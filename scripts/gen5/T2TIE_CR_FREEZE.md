# T2-TIE x DG-CLOSINGRUN connection — freeze r0 (docs only; no Lean yet)

Issue `sparkle-gen5-t2-tie`, branch `kjob/g5tt-cr1`, base `f3a29dbb` (DG-CLOSINGRUN r5 `f2e763d0` depth-0 shared block and r6 audit
improvement scoped approved). Nothing here claims T1, FG, M5 or Issue completion. "Not found" means only that this survey did not find
a supplier or route in the tree at `f3a29dbb`; it does not say the row is impossible or underivable. A conditional wrapper is not
counted as a supply. No new law/TRUSTED boundary, no FG change, no `GenWF` change, `stop_of_run` and all built files untouched.
Not elaborated: the types below were read off the built sources; they are checked only when the implementation is built.

## 1. The target hypothesis (built, `Tools/ShippingGen5T2Tie.lean:276`, `callTie_of_served`)

```
hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
  ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧                                           -- (C1) served result ships
  (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧    -- (C2) design contains r's modules
  Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧                      -- (C3) design contains r.1
  FieldRowAt p k r.1                                                                      -- (C4) field row
```
`FieldRowAt p k mc := if p.d.shape.instFields = [] then ∃ outP, mc.outputs = [outP] else p.d.shape.instFields.getD k "" ∈ mc.outputs.map (·.name)`.

## 2. Fields of `ClosingRun0` / `ClosingShared` (built, `Tools/ShippingGen5ClosingRun2.lean`)

`ClosingRun0.{run, start0, depth0, shared}`; `shared : ClosingShared L P Reach mctx cctx X p Gen w w' raw D` =
`∃ b ci envR envR' w5 w6 t t' d₀ children, RunReadsAt … ∧ Gen ci envR envR' ∧ InvAt … (dv w + 1) w5 ∧ MReturns (synthesizeMixedCertified …) (t, d₀) ∧
closeLets … = some t' ∧ ((insts = [] ∧ children = [] ∧ raw = closeMachine … ∧ D = d₀) ∨ (insts ≠ [] ∧ CloseCalls p.d.shape t (closeMachine p.d.shape.layout t') d₀ children raw D ∧ ChildrenShipsI L P Reach p.d.shape children)) ∧ MachineTraceLBX (PortsServed …) …`.
`ClosingRun.closingShared` (built) gives the same block from the older `ClosingRun`. The connection below uses only `shared`.

## 3. Correspondence table (call `k`, `hk : k < insts.length`, `child? = none` = ordinary call)

| conjunct | source in the block | built lemma used | status |
|---|---|---|---|
| (C1) `ShipsRes … (insts[k]).1 r`, `r := children[k]` | `ChildrenShipsI.2 k hk`: `children[k]? = some y ∧ (child? = some y ∨ (RealChildA ∧ (Reach c → ShipsRes c y)))`; first disjunct excluded by `child? = none`; `Reach c` from `T1HypND.closed X hR p hP k hk hnone` | `T1HypND.closed` | **supplied, one-output and group** (needs `hT`, `hR`, `hP`; group not implemented here, see below) |
| (C2) `∀ g ∈ r.2.modules, moduleByName D.modules g.name = some g` | `CloseCalls` left branch (`instFields = [] ∧ closeInsts … = some (raw, D)`) | `ShippingChildServe.closeInsts_acyclic` (`.2.2.2`) | **supplied for `instFields = []`** |
| (C3) `moduleByName D.modules r.1.name = some r.1` | same | `ShippingChildServe.closeInsts_names` (`.2`) | **supplied for `instFields = []`** |
| (C4) `FieldRowAt p k r.1` | same: a call statement `st ∈ raw.body` with `CallStmt … k args mc st`, `mc = children[k].1` | `ShippingMachineInst.closeInsts_calls`, `closeInsts_names`, `fieldRow_one_of_callStmt` (T2Tie.lean:178) | **supplied for `instFields = []`** |
| (C2)–(C4) for `instFields ≠ []` (group parent) | `CloseCalls` right branch (`closeInstsG`) | `closeInstsG_names`/`closeInstsG_serves` exist, but a field-row statement (`instFields.getD k "" ∈ mc.outputs.map name`) from `connsG` was not found | **未供給 / この調査で経路未発見.** Stays the named premise `hDG_CLOSINGRUN` of `callTie_of_served` |

Premises of `callTie_of_served` NOT from `ClosingRun0`, kept as premises: `hDG_GENP : P (insts[k]).1 = some q`, `hDG_SEM : GenExtAtCall p q k hk`,
`hDG_SEM_range : CallOutRange p q k hk` (DG-SEM / DG-GENP not supplied; `GeneratedAt` not in the tree).
Premises of `closingRun0_of_run` kept as premises (not supplied): `hrow`/`hrows` (via `hord`), `StepStmt`, `T1Hyp.dec`, `hGen`/`GeneratedAt`,
non-vacuity, depth-0 `stop`, `hIH`/`hKI` at depth 1.

## 4. Frozen statements (new file `Tools/ShippingGen5T2TieCR.lean`, namespace `Tools.ShippingGen5T2TieCR`)

Imports: `Tools.ShippingGen5ClosingRun2`, `Tools.ShippingGen5T2Tie`, `Tools.ShippingChildServe`. `set_option autoImplicit false`. Variables as in
`ClosingRun2`: `{ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref} {cref}`; opens as ClosingRun2 plus `Tools.ShippingGen2`.

```
theorem servedCall_of_closingShared_one
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D)
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) :
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1

theorem callTie_of_closingShared_one   -- composition with the built callTie_of_served; GENP/SEM/range stay premises
    {L P Reach DataOk hT mctx cctx X p hR hP Gen w w' raw D hsh h1 k hk hnone as above}
    (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk) :
    CallTie p q k hk

theorem callTie_of_closingRun0_one    -- the same from the built ClosingRun0 structure (uses `.shared` only)
    (h : ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D) … : CallTie p q k hk
```
(binders of the latter two are those of the first, in the same order, with `hsh` replaced by `h`/unchanged and `q`, `hDG_*` appended; all explicit in the
implementation. The `ClosingRun0` form adds nothing beyond `h.shared`.) Proof plan: `ClosingShared` unpacks; the `insts = []` branch is excluded by `hk`;
`CloseCalls` right branch is excluded by `h1`; `closeInsts_calls` gives `args child mc` with `children[k]? = some child` and `st ∈ raw.body` with
`CallStmt`; `closeInsts_names` gives `moduleByName D.modules child.1.name = some child.1`, hence `mc = child.1`; `ChildrenShipsI` gives `y = child` and `ShipsRes`
(first disjunct excluded by `hnone`, `Reach` by `hT.closed`); `closeInsts_acyclic` gives (C2); `fieldRow_one_of_callStmt` gives (C4); `dsn := D`, `r := child`.

## 5. Checks (Tests/Gen5/T2TieCRCheck.lean, written from this document, not from the implementation's signature)

Expected TYPE for the three theorems (independently written), compared by the same reducible comparator that the positive controls (the built
`callTie_of_served`, `closingRun0_of_run`) pass; well-typed one-point mutants (one binder: swap `k`/`hk` roles, drop `h1`, drop `hnone`, `dsn := D` vs a free `dsn`
on (C3), `FieldRowAt p k r.1` → `r.2`-less variant, `ShipsRes` → `ShipsAt`, `instFields = []` → `≠ []`) must be rejected — rejection is by signature/defeq, not a semantic
counterexample. Closure walker (unknown name = FAIL, with the r6 negative control), forbidden roots (`T1Hyp.dec`, `T1Hyp` projections), AXIOMS standard only, no `sorry`.
Not claimed: any supply of `hDG_GENP`/`hDG_SEM`/`hDG_SEM_range`, the group field row, or the OPEN rows of §3; this is a one-output-case connection of one hypothesis.

## 6. Asks for the reviewer

1. Is the one-output-only scope acceptable (group case stays the named premise)?
2. Is the composed `callTie_of_closingShared_one` fine as packaging that is NOT counted as supply of GENP/SEM?

import Tools.ShippingGen2Defs
set_option autoImplicit false
-- Built: g3dsc-1b840215 (clean snapshot, exit 0, standard axioms).
-- S1 combined: re-elaborated at 02e828fc in s1c-02e828fc (clean, exit 0, standard axioms).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # U-ARITY: call arity `(insts[k]).2.1.length = q.ports.length` from ONE trace witness
(scripts/gen3/UARITY_FREEZE.md, approved as a scoped freeze; issue `sparkle-gen3-uarity`)

A0-A7 exactly as UARITY_FREEZE.md §2 (statements) and §3 (routes).

**Scope (§4).** CONDITIONAL on an inhabitant `i : ι` (`ChildShips` gives `ChildRunN` only under `∀ i`). With empty `ι`, the
length cannot be extracted from the existing `ChildShips` along this route; no general non-derivability theorem is shown.
`CallDec`'s arity conjunct is OUTSIDE its `∀ i`, so `CallDec` is NOT claimed supplied here. `hnone` (ordinary origin) is
a premise. Nothing about widths is claimed: arity alone does not supply `callArgsOkAt` (it gives only the matching index
range; UARGW_PARENT_SURVEY.md supplies the parent side, UCHILD_PORTTYS_TABLE.md the child side, and only with
SRC-ARGW's width equality for the same call do they reach `callArgsOkAt`).

**AUDIT (§6).**
1. Expected types: compared mechanically in Tests/Gen3/ArityCheck.lean against independent `Expected…` statements, with
   meaning-changing mutants that must fail.
2. `#print axioms` / `checkAxioms` of every root there.
3. A7 has ONE `obtain` of the `MachineTraceLBX`: `wired` and `hx` share `ids`/`cache`.
4. This file references neither the group run lemma of ParentRunFactsA:410 nor the real-child predicate of
   ChildCacheA (grep for both names finds nothing here); `q` is identified only through `Option.some.inj` on `P`
   (in `argLen_of_shipsRes`).
5. No shared definition is changed (new file).

Header correction (non-semantic): `open Sparkle.Core.Domain` is added to the §2 header (`DomainConfig`). -/

namespace Tools.ShippingGen3Arity
open Lean hiding Module
open Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.Core.Domain
open Tools.ShippingGen2 Tools.ShippingMachineEntry Tools.ShippingMachineLinked
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingChildInv (Res)

/-- (A0) The `args` read from the instance list is call `k`'s argument list. -/
theorem insts_args_eq {shape : MachineShape} {k : Nat} (hk : k < shape.insts.length) {args : List Nat}
    (hargs : (shape.insts.map (·.2.1))[k]? = some args) :
    args = (shape.insts[k]).2.1 := by
  rw [List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some] at hargs
  exact (Option.some.inj hargs).symm

/-- (A1) The length conjunct of `ChildRunN`, both branches (Defs:67, MachineDepth:71). -/
theorem childRunN_argLen {children : String → Option (Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Design} {n : Nat} {mc : Module} {bsC : List (Name × MixedGateBinder)} {outsC : List OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (h : ChildRunN children dsn n mc bsC outsC S) :
    (argPorts mc).length = (bsC.filter fun b => b.2 != .domain).length := by
  rcases h with h | h <;> exact h.2.2.2.2.2.1

/-- (A2) `CallStmt` fixes the arity of the statement: the argument list and the module's argument ports. -/
theorem callStmt_argLen {nIn kI n k : Nat} {names : List String} {args : List Nat} {mc : Module} {st : Stmt}
    (h : Tools.ShippingMachineInst.CallStmt nIn kI n names k args mc st) :
    args.length = (argPorts mc).length := by
  obtain ⟨_, argWs, _, _, _, hmap, _, _, hlen, _⟩ := h
  have h1 : argWs.length = args.length := (Tools.ShippingMachineInst.mapM_some _ _ _ hmap).1
  have h2 : (argPorts mc).length = argWs.length := hlen
  exact h1.symm.trans h2.symm

/-- (A3) The same for `CallStmtG`. -/
theorem callStmtG_argLen {nIn kI n : Nat} {names : List String} {args : List Nat}
    {outs : List (Nat × String)} {mc : Module} {st : Stmt}
    (h : Tools.ShippingMachineInstG.CallStmtG nIn kI n names args outs mc st) :
    args.length = (argPorts mc).length := by
  obtain ⟨_, argWs, _, _, hmap, hlen, _⟩ := h
  have h1 : argWs.length = args.length := (Tools.ShippingMachineInst.mapM_some _ _ _ hmap).1
  have h2 : (argPorts mc).length = argWs.length := hlen
  exact h1.symm.trans h2.symm

/-- (A4) A shipping served result has as many argument ports as the package `q` that `P` selects. -/
theorem argLen_of_shipsRes {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) {c : Name} {q : Pkg ι dom} {mc : Module} {Dc D : Design}
    (i : ι)
    (hship : ShipsRes L P c (mc, Dc)) (hP : P c = some q)
    (hDc : ∀ g ∈ Dc.modules, moduleByName D.modules g.name = some g)
    (hmod : moduleByName D.modules mc.name = some mc) :
    (argPorts mc).length = q.ports.length := by
  obtain ⟨_, ⟨q', n', hq', _, hCS⟩, _⟩ := hship
  have hqq : q' = q := Option.some.inj (hq'.symm.trans hP)
  subst hqq
  exact childRunN_argLen (hCS.2 D hDc hmod i)

/-- **(A5) U-ARITY, one-output parent, fixed witnesses.** `hS` is `hx.2` of the trace's own `ids`/`cache`; `(k, args, mc,
st)` is the call's instance from the SAME `MachineWired`. The second conjunct exposes the successful `mapM`. -/
theorem callArity_one {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw : Module} {D : Design} {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    (hS : Served1P (ShipsRes L P) p.decl p.d.shape raw D ids cache)
    (hf0 : p.d.shape.instFields = []) (i : ι)
    {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    {q : Pkg ι dom} (hP : P (p.d.shape.insts[k]).1 = some q)
    {args : List Nat} {mc : Module} {st : Stmt}
    (hargs : (p.d.shape.insts.map (·.2.1))[k]? = some args) (hst : st ∈ raw.body)
    (hcs : Tools.ShippingMachineInst.CallStmt (machNIn p.d.shape) p.d.shape.insts.length
      p.d.shape.layout.slots.length ((machPorts p.decl ids cache p.d.shape.binders).map (·.name)) k args mc st)
    (hmod : moduleByName D.modules mc.name = some mc) :
    (p.d.shape.insts[k]).2.1.length = q.ports.length ∧
    ∀ (argWs : List String),
      args.mapM (fun j => ((machPorts p.decl ids cache p.d.shape.binders).map (·.name))[machNIn p.d.shape +
        p.d.shape.insts.length + p.d.shape.layout.slots.length + j]?) = some argWs →
      argWs.length = q.ports.length := by
  rcases hS hf0 k hk args mc st hargs hst hcs hmod with ⟨md, hmd, _⟩ | ⟨Dc, hship, hDc⟩
  · -- a memory-origin instance: excluded by `hnone`
    have hc := hnone.symm.trans hmd
    cases hc
  · have hA : (argPorts mc).length = q.ports.length := argLen_of_shipsRes L P i hship hP hDc hmod
    have hB : args.length = (argPorts mc).length := callStmt_argLen hcs
    refine ⟨?_, ?_⟩
    · exact (congrArg List.length (insts_args_eq hk hargs)).symm.trans (hB.trans hA)
    · intro argWs hm
      exact (Tools.ShippingMachineInst.mapM_some _ _ _ hm).1.trans (hB.trans hA)

/-- **(A6) U-ARITY, group parent, fixed witnesses.** `hS` is `hx.1`; `(st, args, outs, mc)` is call `k`'s group
statement from the SAME `MachineWired` (MachineEntry:720-724). -/
theorem callArity_group {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw : Module} {D : Design} {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    (hS : ServedGP (ShipsRes L P) p.decl p.d.shape raw D ids cache)
    (hfne : p.d.shape.instFields ≠ []) (i : ι)
    {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    {q : Pkg ι dom} (hP : P (p.d.shape.insts[k]).1 = some q)
    {args : List Nat} {outs : List (Nat × String)} {mc : Module} {st : Stmt}
    (hargs : (p.d.shape.insts.map (·.2.1))[k]? = some args) (hst : st ∈ raw.body)
    (hcs : Tools.ShippingMachineInstG.CallStmtG (machNIn p.d.shape) p.d.shape.insts.length
      p.d.shape.layout.slots.length ((machPorts p.decl ids cache p.d.shape.binders).map (·.name)) args outs mc st)
    (hkout : (k, p.d.shape.instFields.getD k "") ∈ outs)
    (hmod : moduleByName D.modules mc.name = some mc) :
    (p.d.shape.insts[k]).2.1.length = q.ports.length ∧
    ∀ (argWs : List String),
      args.mapM (fun j => ((machPorts p.decl ids cache p.d.shape.binders).map (·.name))[machNIn p.d.shape +
        p.d.shape.insts.length + p.d.shape.layout.slots.length + j]?) = some argWs →
      argWs.length = q.ports.length := by
  -- A3 on the un-destructured statement
  have hB : args.length = (argPorts mc).length := callStmtG_argLen hcs
  obtain ⟨outWs, argWs0, iname, hout, -, -, -, -, -, -, -, -, -, -, heq⟩ := hcs
  subst heq
  -- `ServedGP` at the SAME statement (`connsG` is verbatim CallStmtG's connection list). Build risk B1: the two
  -- pattern lambdas `fun (k, _) => …` / `fun (j, _) => …` are different auxiliary matchers; the fallbacks compare
  -- them pointwise.
  have hserv := hS hfne k hk mc iname argWs0 outs outWs hst
    (by
      first
        | exact hout
        | (refine Eq.trans ?_ hout
           congr 1
           funext e
           rcases e with ⟨j, f⟩
           rfl)
        | simpa using hout)
    ⟨_, hkout, rfl⟩ hmod
  rcases hserv with ⟨md, hmd, _⟩ | ⟨Dc, hship, hDc⟩
  · -- a memory-origin instance: excluded by `hnone`
    have hc := hnone.symm.trans hmd
    cases hc
  · have hA : (argPorts mc).length = q.ports.length := argLen_of_shipsRes L P i hship hP hDc hmod
    refine ⟨?_, ?_⟩
    · exact (congrArg List.length (insts_args_eq hk hargs)).symm.trans (hB.trans hA)
    · intro ws hm
      exact (Tools.ShippingMachineInst.mapM_some _ _ _ hm).1.trans (hB.trans hA)

/-- **(A7) U-ARITY from ONE `MachineTraceLBX` witness** (both parent kinds, by cases on `instFields`). This is the form
that discharges `hlenK` of Adapt:110 / :174. -/
theorem callArity_of_trace {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) {raw : Module} {D : Design}
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (i : ι) {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    {q : Pkg ι dom} (hP : P (p.d.shape.insts[k]).1 = some q) :
    (p.d.shape.insts[k]).2.1.length = q.ports.length := by
  -- AUDIT 3: ONE witness; `wired` and `hx` share `ids`/`cache`
  obtain ⟨_ids, _nd, _len, _cache, _regs, _rnd, _rlen, _lets, _llen, wired, hx, -⟩ := h
  obtain ⟨-, -, -, -, calls1, -, -, -, -, -, -, -, gCalls, -⟩ := wired
  by_cases hf0 : p.d.shape.instFields = []
  · obtain ⟨args, mc, st, hargs, hst, hmod, hcs⟩ := calls1 hf0 k hk
    exact (callArity_one L P p hx.2 hf0 i hk hnone hP hargs hst hcs hmod).1
  · obtain ⟨st, hst, args, outs, mc, hcs, hmod, hkout, hargs⟩ := gCalls hf0 k hk
    exact (callArity_group L P p hx.1 hf0 i hk hnone hP hargs hst hcs hkout hmod).1

end Tools.ShippingGen3Arity

# Finding H: two declarations whose names PRINT the same are joined into one module

Status: REPRODUCED on poc 50ffea04 at the level of the returned DESIGN (module list) for constructed
declarations with pathological names. Not simulated; not fixed. Analysis, the pure invariant and the three
steps of the coherence route: `docs/parallel/A-cache-coherence.md` (worker A, par/a-31).

## Cause (read, and consistent with the measured design)

The child cache is keyed by the declaration `Name`; a design is joined by the module-name STRING, first
occurrence kept. `Name.toString` does not escape under a `#` / `?` root: `«#ccp.k»` (one component) and
`«#ccp».k` (two components) both print `#ccp.k`.

## Measured (`Tests/Compiler/CacheCoherenceProbe.lean`, log-only, target-built)

Sources: `«#ccp.k» x := x + 1`, `«#ccp».k x := x + 2`, `nA x := «#ccp.k» x + x`, `nB x := «#ccp».k x + x`,
`nTop x := nA x + nB x`; `nDirect x := «#ccp.k» x + «#ccp».k x`.
- The two names print equal (`CACHECOH NAMES … equal=T`); the entry does not throw.
- After one outermost run the cache holds two entries printed `#ccp.k` with different modules
  (`COHERENT=F`, 8 clashes for `nTop`, 2 for `nDirect`).
- The returned design of `nTop` has ONE module named `#ccp.k`, the `x + 1` one; both `nA` and `nB`
  instantiate `#ccp.k`. So `nB` computes with the `+ 1` child where the source says `+ 2`. Same for
  `nDirect` (modules `[#ccp.k, nDirect]`, "named #ccp.k: 1", two instances of it).
- The machine-shaped and the memory-name variants (`mTop`; `mmTop`: a declaration named like a built
  memory module) are also incoherent (`COHERENT=F`).

## Scope and what is not established

Only declarations whose printed names coincide: names under a `#`/`?` root written with `«…»`, or a
declaration named exactly like a built memory module. No corpus declaration has such a name (not swept;
by the naming conventions in the repo). No simulation was run: whether such a module name is even emitted
as legal SystemVerilog was not checked. The wrong DESIGN is measured; a wrong simulated output is not.

## Consequence for the shared-descendant closing (`mixDeep`)

Cache coherence (equal names ⇒ equal modules) is FALSE of the present compiler in general, so step (b) of
the coherence route — preservation by `synthesizeChild` — cannot be proved as stated. Options, a decision
for the user (none taken): (1) a checked insert that REJECTS a clash (turns this finding into an error; it
shrinks the accepted inputs, unlike the guards so far); (2) make module names injective in the declaration
name (escape / mangle: changes emitted module names for such declarations only); (3) keep it as a
per-run decided side condition "the printed names of the reachable declarations are pairwise distinct"
(no compiler change; the endpoint keeps a decided data condition, and the finding stays a known hole).

```
20261013-144809-cachecoh: lake build Tests.Compiler.CacheCoherenceProbe Tools.ShippingCacheCoherent 
result=success
exit=0
memory_peak_file=917422080
an:248:0: CACHECOH NAMES: `#ccp.k / `#ccp.k print #ccp.k / #ccp.k: equal=T
an:248:0: CACHECOH NAMES: `#ccp.c / `#ccp.c print #ccp.c / #ccp.c: equal=T
an:248:0: CACHECOH N top Tests.Compiler.CacheCoherenceProbe.nTop: route=mixed threw=F
an:248:0: CACHECOH N ENTRY Tests.Compiler.CacheCoherenceProbe.nB: module=Tests.Compiler.CacheCoherenceProbe.nB design=[#ccp.k]
an:248:0: CACHECOH N ENTRY Tests.Compiler.CacheCoherenceProbe.nA: module=Tests.Compiler.CacheCoherenceProbe.nA design=[#ccp.k]
an:248:0: CACHECOH N ENTRY #ccp.k: module=#ccp.k design=[]
an:248:0: CACHECOH N ENTRY #ccp.k: module=#ccp.k design=[]
an:248:0: CACHECOH N COHERENT=F (8 clashes)
an:248:0: CACHECOH N DESIGN: modules=[#ccp.k,
an:248:0: CACHECOH N DESIGN MODULE #ccp.k STMT 0: assign _tmp_op_b_0 = Sparkle.IR.AST.Expr.const 1 8
an:248:0: CACHECOH N DESIGN MODULE #ccp.k STMT 1: assign _gen_out = Sparkle.IR.AST.Expr.op (Sparkle.IR.AST.Operator.add) [Sparkle.IR.AST.Expr.ref "_gen_x", Sparkle.IR.AST.Expr.ref "_tmp_op_b_0"]
an:248:0: CACHECOH N DESIGN MODULE #ccp.k STMT 2: assign out = Sparkle.IR.AST.Expr.ref "_gen_out"
an:248:0: CACHECOH N DESIGN MODULE Tests.Compiler.CacheCoherenceProbe.nA STMT 0: inst #ccp.k _tmp_inst__ccp_k_1 (._gen_x(Sparkle.IR.AST.Expr.ref "_gen_x"), .out(Sparkle.IR.AST.Expr.ref "_tmp_op_a_0"))
an:248:0: CACHECOH N DESIGN MODULE Tests.Compiler.CacheCoherenceProbe.nB STMT 0: inst #ccp.k _tmp_inst__ccp_k_1 (._gen_x(Sparkle.IR.AST.Expr.ref "_gen_x"), .out(Sparkle.IR.AST.Expr.ref "_tmp_op_a_0"))
an:248:0: CACHECOH Nd top Tests.Compiler.CacheCoherenceProbe.nDirect: route=mixed threw=F
an:248:0: CACHECOH Nd ENTRY #ccp.k: module=#ccp.k design=[]
an:248:0: CACHECOH Nd ENTRY #ccp.k: module=#ccp.k design=[]
an:248:0: CACHECOH Nd COHERENT=F (2 clashes)
an:248:0: CACHECOH Nd DESIGN: modules=[#ccp.k, Tests.Compiler.CacheCoherenceProbe.nDirect] named #ccp.k: 1
an:248:0: CACHECOH Nd DESIGN MODULE #ccp.k STMT 0: assign _tmp_op_b_0 = Sparkle.IR.AST.Expr.const 1 8
an:248:0: CACHECOH Nd DESIGN MODULE #ccp.k STMT 1: assign _gen_out = Sparkle.IR.AST.Expr.op (Sparkle.IR.AST.Operator.add) [Sparkle.IR.AST.Expr.ref "_gen_x", Sparkle.IR.AST.Expr.ref "_tmp_op_b_0"]
an:248:0: CACHECOH Nd DESIGN MODULE #ccp.k STMT 2: assign out = Sparkle.IR.AST.Expr.ref "_gen_out"
an:248:0: CACHECOH Mc top Tests.Compiler.CacheCoherenceProbe.mTop: route=machine-shape threw=F
an:248:0: CACHECOH Mc ENTRY #ccp.c: module=#ccp.c design=[]
an:248:0: CACHECOH Mc ENTRY #ccp.c: module=#ccp.c design=[]
an:248:0: CACHECOH Mc ENTRY Tests.Compiler.CacheCoherenceProbe.mB: module=Tests.Compiler.CacheCoherenceProbe.mB design=[#ccp.c]
an:248:0: CACHECOH Mc ENTRY Tests.Compiler.CacheCoherenceProbe.mA: module=Tests.Compiler.CacheCoherenceProbe.mA design=[#ccp.c]
an:248:0: CACHECOH Mc COHERENT=F (8 clashes)
an:248:0: CACHECOH Mc DESIGN: modules=[#ccp.c,
an:248:0: CACHECOH M top Tests.Compiler.CacheCoherenceProbe.mmTop: route=mixed threw=F
an:248:0: CACHECOH M ENTRY SparkleMem_combo_4_8: module=SparkleMem_combo_4_8 design=[]
an:248:0: CACHECOH M ENTRY Tests.Compiler.CacheCoherenceProbe.memKid: module=Tests.Compiler.CacheCoherenceProbe.memKid design=[SparkleMem_combo_4_8]
an:248:0: CACHECOH M COHERENT=F (2 clashes)
an:248:0: CACHECOH M DESIGN: modules=[SparkleMem_combo_4_8,
```

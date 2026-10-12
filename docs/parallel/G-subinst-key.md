# Finding G: sub-instance output cache is not keyed by the module being built

Status: REPRODUCED on poc fdd69046 on the real entry and in the limited simulation, for ONE constructed
source (`hTopWR`). Not fixed. Not run on `fix/nested-let-cache-build`. Reading and candidates:
`docs/parallel/B-cache-keys.md` (worker B, par/b-11; its predictions are marked there, and the ones for
`gTopWR` / `gTopRW` were REFUTED by the runs below).

## Source (Tests/Compiler/SubInstanceKeyTest.lean)

```lean
def kSD (x y) : SumDiff dom := { sm := x + y, df := x - y }      -- @[hardware_module], two outputs
def hW (x y) := (kSD x y).sm + (kSD x y).df                       -- @[hardware_module]
def hR (x y) := (kSD y x).sm + (kSD x y).df                       -- @[hardware_module]
def hTopWR (x y) := hW x y + hR x y
```

## Measured

- `hR` synthesised alone: two `kSD` instances. `hR` synthesised as a child of `hTopWR` after `hW`:
  ONE instance `kSD(y, x)`, and `out = sm + df` of that same instance — `(y+x)+(y−x)` instead of the
  source's `(y+x)+(x−y)`. No undeclared name, no self-assignment, no X.
- Simulation of the text written by the real design command, 94 cycles, against the Lean source:
  `hTopWR` differs with numbers (first difference: got 14, want 24); x-cycles 0. The entry with the
  front end off gives the same text as the command.
- `gTopWR`, `gTopRW` (the same shape with `let p := kSD …` bindings): nested module == alone module,
  simulation equals the source. `gW`, `gR` alone: equal.

## Cause (by reading, consistent with the measured text; not isolated by a fix)

`sparkleSubInstanceOutputs` maps (hash of the canonical call expression, port name) to a wire name and is
cleared at depth 0 only. `hW` leaves `(kSD x y, df) ↦ _tmp_sub_call_df_1`; in `hR` the call `kSD y x`
allocates the same wire names, and the projection shortcut returns the cached name for `(kSD x y).df`
without checking that the wire belongs to that call in this module.

## Not established

- Any corpus declaration with this pattern (two modules of one run calling the same multi-output child on
  identically named argument wires, projections applied directly to the calls).
- Behaviour on `fix/nested-let-cache-build` (its change does not touch this ref, by reading).
- A fix. Candidates are a decision for the user: save/restore this ref around a nested entry like the
  let caches, or key it by the module being built.
- The legacy one-output hit: the probe `SingleOutHitTest` shows only that an INJECTED stale entry is
  honoured by the legacy handler (`sIrr` honoured=T) and not by the certified arm (`sTag` honoured=F);
  that is an injected state, not a finding. Zeta marks left after the real runs: 0.

## Run records (cgrun, 3 GiB, swap 0)

```
20261013-034231-b11-subinst: lake build Tests.Compiler.SubInstanceKeyTest 
result=success
exit=0
memory_peak_file=316329984
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
```
```
20261013-034251-subinstkeysim: scripts/shipping-coverage/subinst_key_sim.sh 
result=success
exit=0
memory_peak_file=293994496
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
```
```
20261013-034301-b11-single: lake build Tests.Compiler.SingleOutHitTest 
result=success
exit=0
memory_peak_file=309436416
events: low 0 high 0 max 0 oom 0 oom_kill 0 oom_group_kill 0 
```

## Log excerpts

```
n:209:0: SUBINSTKEY WR CHILD Tests.Compiler.SubInstanceKeyTest.gW: nested==alone T kSD instances nested=1 alone=1 undeclared nested=[]
n:209:0: SUBINSTKEY WR CHILD Tests.Compiler.SubInstanceKeyTest.gR: nested==alone T kSD instances nested=2 alone=2 undeclared nested=[]
n:209:0: SUBINSTKEY WR DETECT: children whose nested module differs from their alone module or reads undeclared names: [] => collision=F
n:209:0: SUBINSTKEY RW CHILD Tests.Compiler.SubInstanceKeyTest.gW: nested==alone T kSD instances nested=1 alone=1 undeclared nested=[]
n:209:0: SUBINSTKEY RW CHILD Tests.Compiler.SubInstanceKeyTest.gR: nested==alone T kSD instances nested=2 alone=2 undeclared nested=[]
n:209:0: SUBINSTKEY RW DETECT: children whose nested module differs from their alone module or reads undeclared names: [] => collision=F
n:209:0: SUBINSTKEY hWR CHILD Tests.Compiler.SubInstanceKeyTest.hW: nested==alone T kSD instances nested=1 alone=1 undeclared nested=[]
n:209:0: SUBINSTKEY hWR CHILD Tests.Compiler.SubInstanceKeyTest.hR: nested==alone F kSD instances nested=1 alone=2 undeclared nested=[]
n:209:0: SUBINSTKEY hWR DETECT: children whose nested module differs from their alone module or reads undeclared names: [Tests.Compiler.SubInstanceKeyTest.hR] => collision=T
n:209:0: SUBINSTKEY hWR nested MODULE Tests.Compiler.SubInstanceKeyTest.hTopWR STMT 1: inst Tests.Compiler.SubInstanceKeyTest.hR _tmp_inst_Tests_Compiler_SubInstanceKeyTest_hR_3 (._gen_x(Sparkle.IR.AST.Expr.ref "_gen_x"), ._gen_y(Sparkle.IR.AST.Expr.ref "_gen_y"), .out(Sparkle.IR.AST.Expr.ref "_tmp_op_b_2"))
n:209:0: SUBINSTKEY hWR nested MODULE Tests.Compiler.SubInstanceKeyTest.hR: stmts=3 insts=[Tests.Compiler.SubInstanceKeyTest.kSD] kSDinsts=1 undeclared=[] undriven=[]
n:209:0: SUBINSTKEY hWR nested MODULE Tests.Compiler.SubInstanceKeyTest.hR STMT 0: inst Tests.Compiler.SubInstanceKeyTest.kSD _tmp_inst_Tests_Compiler_SubInstanceKeyTest_kSD_2 (._gen_x(Sparkle.IR.AST.Expr.ref "_gen_y"), ._gen_y(Sparkle.IR.AST.Expr.ref "_gen_x"), .sm(Sparkle.IR.AST.Expr.ref "_tmp_sub_call_sm_0"), .df(Sparkle.IR.AST.Expr.ref "_tmp_sub_call_df_1"))
n:209:0: SUBINSTKEY hWR nested MODULE Tests.Compiler.SubInstanceKeyTest.hR STMT 1: assign _gen_out = Sparkle.IR.AST.Expr.op (Sparkle.IR.AST.Operator.add) [Sparkle.IR.AST.Expr.ref "_tmp_sub_call_sm_0", Sparkle.IR.AST.Expr.ref "_tmp_sub_call_df_1"]
n:209:0: SUBINSTKEY hWR nested MODULE Tests.Compiler.SubInstanceKeyTest.hR STMT 2: assign out = Sparkle.IR.AST.Expr.ref "_gen_out"
SUBINSTKEYSIM Tests.Compiler.SubInstanceKeyTest.gTopWR: command==source T nofe==source T command==nofe T x-cycles command=0 nofe=0 cycles=94
SUBINSTKEYSIM Tests.Compiler.SubInstanceKeyTest.gTopRW: command==source T nofe==source T command==nofe T x-cycles command=0 nofe=0 cycles=94
SUBINSTKEYSIM Tests.Compiler.SubInstanceKeyTest.hTopWR: command==source F nofe==source F command==nofe T x-cycles command=0 nofe=0 cycles=94
  command/source: got [R1 1 14] want [R1 1 24]
  nofe/source: got [R1 1 14] want [R1 1 24]
SUBINSTKEYSIM Tests.Compiler.SubInstanceKeyTest.gW: command==source T nofe==source T command==nofe T x-cycles command=0 nofe=0 cycles=94
SUBINSTKEYSIM Tests.Compiler.SubInstanceKeyTest.gR: command==source T nofe==source T command==nofe T x-cycles command=0 nofe=0 cycles=94
199:0: SINGLEOUT SEEDED: legacy handler (sIrr) honoured=T; certified arm (sTag) honoured=F (an injected state, not a finding)
```

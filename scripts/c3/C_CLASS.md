# C3 — class C in design terms (SPECIFICATION ONLY; nothing here is proved)
Base checked out: par/c3-spec @ 99dcc0863f3fa157aea7daed19cb8da5cdbc087e (= accepted SRM33 final; contains int-srm8 1b1ac9dd + SRM31 66ca8024 + SRM32 fd4b7d89).
SRM37 (accepted, 130283ce) is NOT in this checkout; its signatures are read from commit 130283ce (`git show 130283ce:Tools/ShippingSrm37Fit.lean`) and labelled [130283ce].
The int-srm10 candidate c31383a1 (unvalidated integration candidate) is not used. No build, no kjob, no theorem evidence.

## C = "memory shared-leaf parents" (design-level description)
A Signal design `f` is in C iff:
1. Route: `f` is compiled by the machine route (`synthesizeCombinationalCore f [] false` with `MachineDefines … f d.shape`), and its machine data `d` passes the
   generator's Bool checks: `d.ok`, `d.callsOk nDecl`, slot-count `d.ss.length = d.shape.layout.slots.length`, domain binders after `nDecl` are not `.domain`,
   `d.shape.insts ≠ []`, `d.shape.instFields ≠ []`, `d.shape.layout.slots ≠ []`, output types `o.ty.bitWidth = o.width`, no memory in the parent body
   (the `topshareM_parentData.*` / `topshareM_nomem` facts are exactly these checks at one instance).
2. Children: every call of the parent targets a WRAPPER machine `wᵢ` (depth-1 sequential machine, machine route) which itself calls ONE shared MEMORY LEAF `leaf`
   (machine route, memory-only body as in `memLeafPC`, Tools/ShippingSrm4Callee.lean:54); depth of the instance tree `n = 2`.
3. Grouping: the parent's calls are grouped as the generator groups them (`QuadGroupFacts d nDecl`, Tools/ShippingQuadComposed.lean:680).
4. Boundary of the contract (kept as premises, not discharged): `O : RefLawsAOps MkRefd mref cref`, `RefLawsATele O.quiet mref cref`, `AdmCtx O.quiet mctx cctx`,
   `MachineDefines` of the parent, every wrapper and the leaf, `JQC O 0 w`.
Members today: topshareM (2 wrappers wrapM/wrapM3 over leafM) and topshareQ. C is NOT defined as {topshareM, topshareQ}: it is the structure below.

## Lean form of C (NEW definition, to be written in C4's unit; frozen here)
structure MemSharedLeafParent where
  decl      : Lean.Name                     -- the parent
  d         : MachineData
  nDecl     : Nat
  leafDecl  : Lean.Name
  leafD     : MachineData
  wrappers  : List (Lean.Name × MachineData) -- the callees, in call order
  ok        : d.ok = true
  callsOk   : d.callsOk nDecl = true
  slotsLen  : d.ss.length = d.shape.layout.slots.length
  domB      : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain
  insts     : d.shape.insts ≠ []
  instF     : d.shape.instFields ≠ []
  slotsNe   : d.shape.layout.slots ≠ []
  outTy     : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width
  noMem     : <the parent no-memory check of topshareM_nomem, as a Bool = true>
  callees   : <every instance target of d.shape is ``wᵢ for some (wᵢ, _) ∈ wrappers> (Bool check on d.shape.instTagged)
  wrapLeaf  : ∀ wd ∈ wrappers, <wd.2 is a depth-1 machine whose only callee is leafDecl> (Bool checks as in wrapM.machineData)
  leafMem   : <leafD is a memory-only leaf as required by memLeafPC> (Bool check)
  group     : QuadGroupFacts d nDecl                              -- see GAP G-GRP: should become a Bool check + soundness lemma
All fields except `group` are decidable data checks (discharged per design by `decide`/the generator); `group` is the one Prop field and is a named gap.

import Lean
import Tools.VedU1Contract
import Tools.VedU1StructSeqTac
import Tools.VedU1StructSlice

/-!
# Per-wire value lemmas of the source value (`ved.sseq.wireEqs`, sparkle-ved-multiout unit 12)

Class (a) measured on R184's `wPointOp` (unit 11): after `ved_ss_zeta` the source value `hvsrc : vsrc = Signal.val (applyIns … f) s` is a
DAG of 3,268 nodes, 1.35e8 as a tree, nesting depth 416, and the first `simp … at hvsrc` stops with "maximum recursion depth": the
unsupplied local statement is one VALUE LEMMA PER INTERNAL WIRE, `w_i.val s = e_i(w_j.val s, j < i)`, in which every earlier wire is an
opaque atom.

`ved_ss_wiresimp hvsrc [simp lemmas]` (default off, option `ved.sseq.wireEqs`; replaces the first `ved_ss_core_simp_big [..] at hvsrc`):

1. `applyIns ps ns ins f` in the value is unfolded by an explicit loop (`PTy.sig` arguments, `headBeta`), so the value is a CLOSED
   `Signal` term (no loose bound variables).
2. The closed `Signal`-typed sub-terms are visited once each (pointer-keyed cache, bottom-up).  A node whose height since the last cut
   reaches `ved.sseq.wireK` (default 8; the heights of the cut wires count 0) becomes a LET-BOUND local variable
   `ved_w_i : Signal dom α := c_i'` (`c_i'` over the earlier `ved_w_j` only; `MVarId.define`).  Let variables are opaque to `simp`
   (`zetaDelta := false`).  `hvsrc` is re-stated over them: `hvsrc : vsrc = Signal.val (… ved_w_i …) s`; its proof is the old
   `hvsrc` (the new type is definitionally the old one by zeta of the lets, which the kernel checks).
3. One value lemma per cut wire, `hV_i : ved_w_i.val s = (c_i').val s` (by `rfl`: zeta-delta), simplified by the stage's own simp set
   (`ved_ss_core_simp_big [..] at hV_i`): `hV_i : ved_w_i.val s = e_i`, `e_i` over `ved_w_j.val s` (atoms) only.
4. `hvsrc` is simplified by the same simp set (its depth is now bounded by the chunk height), then the atoms are replaced
   by their value lemmas, `simp only [hV_m, …, hV_1] at hvsrc` (the simp visits each DAG node once).
5. The `hV_i` and the let variables are cleared: the context is the one the unchanged stage would have produced.

Untrusted tactic: the kernel checks what it builds; nothing here is a statement, an axiom or a hypothesis of a final theorem.
Heights are counted over closed nodes only; the body `F` of a `Signal.loop F` is NOT entered (the loop is a leaf; its body is
handled by `hU` as before).
-/

namespace Tools.VedU1StructWireEqs

open Lean Meta Elab Tactic

/-- Default off: the first stage simp of the structure script goes through `ved_ss_wiresimp` (per-wire value lemmas). -/
register_option ved.sseq.wireEqs : Bool := {
  defValue := false
  descr := "ved.sseq.wireEqs: per-wire value lemmas for the source value (cut wires + hV_i), default off"
}

/-- Height at which a closed `Signal` node of the source value becomes a named wire. -/
register_option ved.sseq.wireK : Nat := {
  defValue := 8
  descr := "ved.sseq.wireK: Signal-node height at which ved_ss_wiresimp cuts a named wire (default 8)"
}

/-- `applyIns ps ns ins f` unfolded along the (literal) port list: one `PTy.sig` argument per port, `headBeta` each time -/
partial def applyInsUnfold (ps ns ins f : Expr) : MetaM Expr := do
  let ps' ← whnfD ps
  match ps'.getAppFnArgs with
  | (``List.nil, _) => return f
  | (``List.cons, #[_, p, rest]) =>
    let ns' ← whnfD ns
    let (hd, tl) ← match ns'.getAppFnArgs with
      | (``List.cons, #[_, h, t]) => pure (h, t)
      | _ => pure (mkStrLit "", ns')
    let arg ← mkAppM ``Tools.VedU1Contract.PTy.sig #[p, ins, hd]
    applyInsUnfold rest tl ins (mkApp f arg).headBeta
  | _ => throwError "ved_ss_wiresimp: the port list is not a literal list: {ps'}"

/-- Reducible constants of the monadic program (`circuit do`) that are unfolded when they are the head of a node. -/
def deltaHeads : Array Name :=
  #[`Sparkle.Core.mkRegList, `Sparkle.Core.mkHolds, `Sparkle.Core.packRegister]

/-- Head evaluation of a node of the program value: beta / iota / projections (`whnfCore` at reducible transparency, so that the
major premise of a `Prod.casesOn` such as `mkRegList …` is reduced to its pair), the structure projection functions of
non-class structures (`Prod.fst`, `PointOpOut.xOut`, `Reg.read`, …) and `deltaHeads`.  Class projections (`HSub.hSub`, `Functor.map`,
…: the operators of the signal DAG) and every other definition (`Signal.map`, `Signal.mux`, `bundle2`, …) are NOT unfolded:
what is left is an operator node with its (unevaluated) arguments. -/
partial def evalHead (e : Expr) : MetaM Expr := do
  let e1 ← withReducible (whnfCore e)
  if let .const c _ := e1.getAppFn then
    let env ← getEnv
    let isProj := (env.getProjectionFnInfo? c).any (fun i => !i.fromClass)
    if isProj || deltaHeads.contains c then
      if let some e2 ← withReducible (unfoldDefinition? e1) then
        return ← evalHead e2
  return e1

structure WS where
  cache : Std.HashMap Expr (Expr × Nat) := {}
  g : MVarId
  cuts : Array (FVarId × Expr) := #[]
  loops : Array FVarId := #[]
  maxH : Nat := 0

abbrev WM := StateRefT WS TacticM

def isSignalTy (ty : Expr) : Bool := ty.isAppOf ``Sparkle.Core.Signal.Signal

partial def visit (K : Nat) (e : Expr) : WM (Expr × Nat) := do
  if let some r := (← get).cache[e]? then return r
  let r ← visitCore K e
  modify fun s => { s with cache := s.cache.insert e r }
  return r
where
  visitCore (K : Nat) (e0 : Expr) : WM (Expr × Nat) := do
    let e ← if e0.isApp || e0.isProj then evalHead e0 else pure e0
    match e with
    | .mdata d b =>
      let (b', h) ← visit K b
      return (if b' == b then e else .mdata d b', h)
    | .proj n i b =>
      let (b', h) ← visit K b
      return (if b' == b then e else .proj n i b', h)
    | .lam n t b bi =>
      -- the thunk `fun _ => x` of `<*>` / `Seq.seq` (its body does not use the binder): entered; any other lambda is left alone
      if b.hasLooseBVars then return (e, 0)
      let (b', h) ← visit K b
      return (if b' == b then e else .lam n t b' bi, h)
    | .app .. =>
      let fn := e.getAppFn
      if fn.isConstOf ``Sparkle.Core.Signal.Signal.loop then
        -- the loop is a wire of its own (opaque to every simp below; its body `F` is never visited here); put back at the end
        if e.hasLooseBVars then return (e, 0)
        let g := (← get).g
        let ty ← g.withContext (inferType e)
        let n := (← get).cuts.size
        let g1 ← g.define (Name.mkSimple s!"ved_w{n}") ty e
        let (fv, g2) ← g1.intro1P
        modify fun s => { s with g := g2, cuts := s.cuts.push (fv, e), loops := s.loops.push fv }
        return (mkFVar fv, 0)
      let args := e.getAppArgs
      let mut h := 0
      let mut changed := false
      let (fn', hf) ← if fn.isConst then pure (fn, 0) else visit K fn
      h := max h hf
      changed := !(fn' == fn)
      let mut args' : Array Expr := #[]
      for a in args do
        let (a', ha) ← visit K a
        h := max h ha
        changed := changed || !(a' == a)
        args' := args'.push a'
      let e' := if changed then mkAppN fn' args' else e
      if e.hasLooseBVars || e.hasMVar then return (e', h)
      let g := (← get).g
      let ty ← g.withContext (inferType e)
      if isSignalTy ty then
        let h' := h + 1
        modify fun s => { s with maxH := max s.maxH h' }
        if h' ≥ K then
          let n := (← get).cuts.size
          let g1 ← g.define (Name.mkSimple s!"ved_w{n}") ty e'
          let (fv, g2) ← g1.intro1P
          modify fun s => { s with g := g2, cuts := s.cuts.push (fv, e') }
          return (mkFVar fv, 0)
        return (e', h')
      return (e', h)
    | _ => return (e, 0)

/-- `ved_ss_wiresimp h [lemmas]`: see the module docstring -/
elab "ved_ss_wiresimp " h:ident " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let some (_, lhs, rhs) := ty.eq? | throwError "ved_ss_wiresimp: {h} is not an equation"
  unless rhs.isAppOfArity ``Sparkle.Core.Signal.Signal.val 4 do
    throwError "ved_ss_wiresimp: the right side of {h} is not a `Signal.val`"
  let sig := rhs.getArg! 2
  let s := rhs.getArg! 3
  let t0 ← IO.monoMsNow
  -- `VED_MS_LOG` (diagnostics only): nothing is formatted when it is unset, and a failure to write never changes the outcome
  let logOn := (← IO.getEnv "VED_MS_LOG").isSome
  let logF : String → IO Unit := fun m => do
    if let some path ← IO.getEnv "VED_MS_LOG" then
      try
        let hd ← IO.FS.Handle.mk path .append
        hd.putStrLn m
        hd.flush
      catch _ => pure ()
  -- (1) `applyIns` unfolded: a closed signal term
  let sig1 ← if sig.isAppOfArity ``Tools.VedU1Contract.applyIns 5 then
      let a := sig.getAppArgs
      applyInsUnfold a[1]! a[2]! a[3]! a[4]!
    else pure sig
  if (← IO.getEnv "VED_WIRE_DUMP").isSome then
    logF s!"VED WIRES DUMP {(← ppExpr sig1).pretty.take 40000}"
  -- (2) the cut wires
  let K := ved.sseq.wireK.get (← getOptions)
  let g0 ← getMainGoal
  let ((sig2, _), st) ← (visit K sig1).run { g := g0 }
  let t1 ← IO.monoMsNow
  let rhs' := mkApp4 rhs.getAppFn (rhs.getArg! 0) (rhs.getArg! 1) sig2 s
  let tyNew ← mkEq lhs rhs'
  let g1 ← st.g.assert h.getId tyNew (mkFVar d.fvarId)
  let (hNew, g2) ← g1.intro1P
  let g3 ← g2.clear d.fvarId
  logF s!"VED WIRES {h.getId}: cuts={st.cuts.size} K={K} maxHeight={st.maxH} (applyIns unfolded={!(sig1 == sig)}) {t1 - t0}ms"
  replaceMainGoal [g3]
  -- (3) one value lemma per cut wire
  let mut hVs : Array Name := #[]
  let mut j := 0
  for (fv, _) in st.cuts do
    if st.loops.contains fv then
      j := j + 1
      continue
    let nm := Name.mkSimple s!"ved_hV{j}"
    let gcur ← getMainGoal
    let g' ← gcur.withContext do
      let w := mkFVar fv
      let d ← fv.getDecl
      let some v := d.value? | throwError "ved_ss_wiresimp: cut wire without a value"
      let lhsV ← mkAppM ``Sparkle.Core.Signal.Signal.val #[w, s]
      let rhsV ← mkAppM ``Sparkle.Core.Signal.Signal.val #[v, s]
      let gA ← gcur.assert nm (← mkEq lhsV rhsV) (← mkEqRefl lhsV)
      pure (← gA.intro1P).2
    replaceMainGoal [g']
    let hid := mkIdent nm
    if (← IO.getEnv "VED_WIRE_DUMP").isSome then
      let txt ← withMainContext do
        let dd ← fv.getDecl
        let f ← ppExpr (dd.value?.getD (mkConst ``True))
        pure (f.pretty.take 2500).toString
      logF s!"VED WIRES CUT {j}: {txt}"
    let stats ← if !logOn then pure "" else withMainContext do
      let dd ← fv.getDecl
      let v := dd.value?.getD (mkConst ``True)
      let (dg, tr) := Tools.VedU1StructSlice.dagTree v
      pure s!"dag={dg} tree={tr} depth={((Tools.VedU1StructSlice.depthOf v).run' {})}"
    -- simplified by the stage's own set; a lemma the simp removes (or cannot change) is left out of the rewrite list
    tryCatchRuntimeEx (evalTactic (← `(tactic| ved_ss_core_simp_big [$ls,*] at $hid:ident)))
      fun _ => do if logOn then logF s!"VED WIRES hV{j} ({stats}) simp failed"
    let has ← withMainContext do pure ((← getLCtx).findFromUserName? nm).isSome
    if has then hVs := hVs.push nm
    j := j + 1
  let t2 ← IO.monoMsNow
  -- (4) the value itself, then the atoms replaced by their value lemmas
  evalTactic (← `(tactic| ved_ss_core_simp_big [$ls,*] at $h:ident))
  let t3 ← IO.monoMsNow
  if hVs.size > 0 then
    let hids : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
      (hVs.reverse.map mkIdent).mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
    tryCatchRuntimeEx (evalTactic (← `(tactic| simp (config := { maxSteps := 4000000 }) only [$hids,*] at $h:ident)))
      fun _ => do if logOn then logF "VED WIRES atoms simp failed"
  let t4 ← IO.monoMsNow
  -- (5) the loops put back (`ved_ss_wit` looks for `Signal.loop F` in the value), the context as the unchanged stage leaves it
  for fv in st.loops do
    let gcur ← getMainGoal
    let dd ← gcur.withContext do getLocalDeclFromUserName h.getId
    let some (_, v) := (← gcur.withContext fv.getDecl).value?.map (fun v => (0, v)) | continue
    let ty' := (← instantiateMVars dd.type).replaceFVar (mkFVar fv) v
    replaceMainGoal [← gcur.replaceLocalDeclDefEq dd.fvarId ty']
  for nm in hVs.reverse do
    let gcur ← getMainGoal
    let some dd := (← gcur.withContext getLCtx).findFromUserName? nm | continue
    try replaceMainGoal [← gcur.clear dd.fvarId] catch _ => pure ()
  for (fv, _) in st.cuts.reverse do
    let gcur ← getMainGoal
    try replaceMainGoal [← gcur.clear fv] catch _ => pure ()
  logF s!"VED WIRES {h.getId}: value lemmas {t2 - t1}ms, simp of the value {t3 - t2}ms, atoms replaced {t4 - t3}ms, kept hV={hVs.size}"

end Tools.VedU1StructWireEqs

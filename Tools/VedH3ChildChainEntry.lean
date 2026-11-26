import Tools.VedU1Entry
import Tools.VedH3ChildChain

/-!
# Chains of one's-complement add stages: reading the body and the proof script
(issue sparkle-ved-hier3-child)

`chainDataOf?` reads a `CData` (Tools/VedH3ChildChain.lean) from the module of a register-free leaf whose body is
a prelude, a chain of `IPv4.onesAdd16Sig` stages (each the 7 statements of `Stg`, the first stage with the
constant `hi1` between its halves) and `~~~` of the last sum.  `buildChain` is the `ProofSrc.built` builder.
Reading only picks the script; the kernel checks that the module's body IS `CData.body`, `CData.ok`, the
prelude's values and, on the signal side, that `IPv4.onesAdd16Sig` is `onesStageSig` (`rfl`).
-/

namespace Tools.VedH3ChildChainEntry

open Lean Elab Term Meta Sparkle.IR.AST Sparkle.IR.Semantics Tools.VedU1Contract Tools.VedU1Entry Tools.VedH3ChildChain

deriving instance Lean.ToExpr for Stg
deriving instance Lean.ToExpr for CData

/-- a `|||` of two 16-bit values needs no `% 65536` (the prelude's masked `or` against the signal side's `|||`) -/
theorem or_mod_16 (a b : Nat) (ha : a < 65536) (hb : b < 65536) : (a ||| b) % 65536 = a ||| b :=
  Nat.mod_eq_of_lt (by simpa using Nat.or_lt_two_pow (n := 16) ha hb)

/-- the first half of a stage at the head of `ss` -/
def takeS1 : List Stmt → Option (String × String × String × String × String × String × String × String × List Stmt)
  | .assign a17 (.concat [.ref h0, .ref A]) :: .assign b17 (.concat [.ref h0', .ref B]) ::
    .assign s17 (.op .add [.ref a17', .ref b17']) :: .assign low (.slice (.ref s17') 15 0) ::
    .assign carBit (.slice (.ref s17'') 16 16) :: rest =>
    if h0 == h0' && a17 == a17' && b17 == b17' && s17 == s17' && s17 == s17'' then
      some (h0, A, B, a17, b17, s17, low, carBit, rest)
    else none
  | _ => none

/-- the second half of a stage at the head of `ss` -/
def takeS2 (hi1 low carBit : String) : List Stmt → Option (String × String × List Stmt)
  | .assign car16 (.concat [.ref h1, .ref cb]) :: .assign s (.op .add [.ref low', .ref car16']) :: rest =>
    if h1 == hi1 && cb == carBit && low' == low && car16' == car16 then some (car16, s, rest) else none
  | _ => none

/-- the stages after the first one: both halves back to back, `A` the previous sum -/
partial def takeStages (hi0 hi1 prev : String) (ss : List Stmt) (acc : Array Stg) : Array Stg × List Stmt :=
  match takeS1 ss with
  | some (h0, A, B, a17, b17, s17, low, carBit, rest) =>
    if h0 == hi0 && A == prev then
      match takeS2 hi1 low carBit rest with
      | some (car16, s, rest') =>
        takeStages hi0 hi1 s rest' (acc.push { a17, b17, s17, low, carBit, car16, s, A, B })
      | none => (acc, ss)
    else (acc, ss)
  | none => (acc, ss)

/-- the chain data of a module body, if it has the shape -/
def chainDataOf? (m : Sparkle.IR.AST.Module) : Option CData := do
  let body := m.body
  -- the first stage: the first `i` whose statements start a stage
  let mut found : Option (Nat × CData × List Stmt) := none
  for i in List.range body.length do
    if found.isNone then
      if let some (hi0, A, B, a17, b17, s17, low, carBit, rest) := takeS1 (body.drop i) then
        if let some (.assign hi1 (.const 0 15), rest1) := rest.head?.map (·, rest.tail) then
          if let some (car16, s, rest2) := takeS2 hi1 low carBit rest1 then
            let g0 : Stg := { a17, b17, s17, low, carBit, car16, s, A, B }
            let (gs, rest3) := takeStages hi0 hi1 s rest2 #[]
            found := some (i, { pre := body.take i, g0, hi0, hi1, gs := gs.toList, o1 := "", outn := "" }, rest3)
  let some (_, D0, rest3) := found | none
  match rest3 with
  | [.assign o1 (.op .not [.ref sl]), .assign outn (.ref o1')] =>
    guard (o1 == o1' && sl == D0.lastS)
    let D : CData := { D0 with o1, outn }
    guard (decide (D.body = body))
    guard (decide (D.ok (declWidth m)))
    pure D
  | _ => none

/-- the signal-side function the stages were written with -/
def stageFn : Name := `Sparkle.IP.Net.IPv4.onesAdd16Sig

/-- the data ports are all bit vectors (the chain route reads each input's range) -/
def dataWidths? (m : Sparkle.IR.AST.Module) : Option (List (String × Nat)) :=
  (dataPortsOf m (clkRstOf m)).mapM fun p => match p.ty with
    | .bitVector w => some (p.name, w)
    | _ => none

/-- `ProofSrc.built` builder -/
def buildChain (stmtDecl : Name) (nDom : Nat) (nm : Names) (m : Sparkle.IR.AST.Module) : TermElabM Syntax := do
  let clkRst := clkRstOf m
  let some D := chainDataOf? m | throwError "chain: the body is not an add-stage chain"
  let some ins := dataWidths? m | throwError "chain: a data input is not a bit vector"
  unless (← getEnv).contains stageFn do throwError "chain: {stageFn} is not in the environment"
  let dn := nm.mod.getPrefix ++ `ved_chain
  addDefn dn (Lean.mkConst ``CData) (toExpr D)
  let pn := nm.mod.getPrefix ++ `ved_ports
  addDefn pn (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Port)) (toExpr (dataPortsOf m clkRst))
  let Dc := mkCIdent dn
  let Pc := mkCIdent pn
  let C := mkCIdent nm.contract
  let M := mkCIdent nm.mod
  let O := mkCIdent nm.outs
  let B := mkCIdent nm.body
  let fI := mkCIdent stmtDecl
  let mut f : Term := fI
  if nDom > 0 then
    f ← `(@$fI)
    for _ in [0:nDom] do f ← `($f Sparkle.Core.Domain.defaultDomain)
  let insI := mkIdent `ins
  let sI := mkIdent `s
  let stg := mkCIdent stageFn
  -- per data input: its range and the seed value
  let mut inTacs : Array (TSyntax `tactic) := #[]
  let mut sdL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  let mut modL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for (n, w) in ins, k in List.range ins.length do
    let nS := Syntax.mkStrLit n
    let wN := Syntax.mkNumLit (toString w)
    let lim := Syntax.mkNumLit (toString (2 ^ w))
    let bI := mkIdent (Name.mkSimple s!"hb{k}")
    let sdI := mkIdent (Name.mkSimple s!"hsd{k}")
    inTacs := inTacs.push (← `(tactic| have $bI : $insI $sI $nS < $lim := by
        have h1 := hbnd ⟨$nS, .bitVector $wN⟩ (by simp [$Pc:ident])
        have h2 : declWidth $M $nS = $wN := by decide +kernel
        rw [h2] at h1; exact h1))
    inTacs := inTacs.push (← `(tactic| have $sdI : seedIn $M $insI $sI st $nS = $insI $sI $nS := by
        unfold seedIn; exact if_pos (by decide +kernel)))
    sdL := sdL.push (← `(Lean.Parser.Tactic.simpLemma| $sdI:term))
    let hwI := mkIdent (Name.mkSimple s!"hw{k}")
    inTacs := inTacs.push (← `(tactic| have $hwI : declWidth $M $nS = $wN := by decide +kernel))
    sdL := sdL.push (← `(Lean.Parser.Tactic.simpLemma| $hwI:term))
    modL := modL.push (← `(Lean.Parser.Tactic.simpLemma| Nat.mod_eq_of_lt $bI:term))
    if w ≤ 16 then
      let bwI := mkIdent (Name.mkSimple s!"hbw{k}")
      inTacs := inTacs.push (← `(tactic| have $bwI : $insI $sI $nS < 65536 := by omega))
      modL := modL.push (← `(Lean.Parser.Tactic.simpLemma| $bwI:term))
  let sds : Syntax.TSepArray [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] "," :=
    Syntax.TSepArray.ofElems (sdL.map fun x => (⟨x.raw⟩ : TSyntax _))
  let mods : Syntax.TSepArray [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] "," :=
    Syntax.TSepArray.ofElems (modL.map fun x => (⟨x.raw⟩ : TSyntax _))
  -- the declaration's own helper definitions (a constant such as `protoTcp`), unfolded at the end
  let hsA : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    (← helperConsts stmtDecl).mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  let hlp : Syntax.TSepArray [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] "," :=
    Syntax.TSepArray.ofElems ((hsA.map fun x => (⟨x.raw⟩ : TSyntax _)).push
      ⟨(← `(Lean.Parser.Tactic.simpErase| -Nat.reduceAdd)).raw⟩)
  `(by
    have hok : ($Dc).ok (declWidth $M) := by decide +kernel
    have hbody : ($M).body = ($Dc).body := by ved_kernel_rfl
    have hB : $B = ($M).body := rfl
    have hord : OrderOk $M $B = true := by decide +kernel
    refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨$B, hord⟩, ?_⟩
    apply outputs_of_order $B hord
    apply outputs_of_step $C $M $B $f $O (by decide +kernel) (fun _ _ _ => True)
    · intro _ _; trivial
    · intro $insI hin $sI st mems _
      have hdi : ($C).dataInputs = $Pc := by decide +kernel
      have hbnd : ∀ p ∈ $Pc, $insI $sI p.name < 2 ^ declWidth $M p.name := fun p hp => hin.1 $sI p (hdi ▸ hp)
      $inTacs*
      obtain ⟨env1, hpre, hf⟩ : ∃ env1, Sparkle.IR.Semantics.evalAssigns (declWidth $M) mems ($Dc).pre
            (seedIn $M $insI $sI st) = some env1 ∧ ($Dc).PreFacts env1 := by
        simp [Tools.VedH3ChildChain.CData.PreFacts, Tools.VedH3ChildChain.CData.stages, $Dc:ident,
          Sparkle.IR.Semantics.evalAssigns, Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalOp,
          Sparkle.IR.Semantics.evalExpr.go, Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.widthOf.go,
          Sparkle.IR.Semantics.widthOf, Sparkle.IR.Semantics.mask, $sds,*]
        omega
      obtain ⟨envF, hrun, hout⟩ := Tools.VedH3ChildChain.body_eval (declWidth $M) mems _ hok _ env1 hpre hf
      simp [Sparkle.IR.Semantics.evalAssigns, Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalOp,
        Sparkle.IR.Semantics.evalExpr.go, Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.widthOf.go,
        Sparkle.IR.Semantics.widthOf, Sparkle.IR.Semantics.mask, $sds,*, $Dc:ident] at hpre
      subst hpre
      have hasg : (($Dc).body).all Tools.VedU1Table.isAsg = true := by decide +kernel
      have hstep : stepModule (declWidth $M) $B (seedIn $M $insI $sI st) mems = some (envF, [], mems) := by
        rw [hB, hbody]
        simp only [stepModule, hrun, Tools.VedU1Table.regNexts_asg _ _ _ _ hasg,
          Tools.VedU1Table.memNexts_asg _ _ _ _ hasg, Option.bind_eq_bind, Option.bind_some]
      refine ⟨envF, [], mems, hstep, ?_, trivial⟩
      intro o ho
      simp only [$O:ident, List.mem_singleton] at ho
      subst ho
      simp [srcOf, $C:ident, contractOf, applyIns, OTy.obs, PTy.obs, PTy.sig]
      have hout' := hout
      rw [show ($Dc).outn = "out" from rfl] at hout'
      simp [Tools.VedH3ChildChain.CData.stages, $Dc:ident, $sds,*] at hout'
      rw [hout']
      have key : ∀ a b : Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain (BitVec 16),
          $stg:ident a b = Tools.VedH3ChildChain.onesStageSig a b := fun _ _ => rfl
      simp only [$fI:ident, key]
      simp [Tools.VedH3ChildChain.onesStageSig_toNat, Sparkle.Core.Signal.Signal.map, BitVec.toNat_not,
        BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Tools.VedU1Lemmas.pure_val, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_append, Tools.VedU1Lemmas.toNat_append', Tools.VedH3ChildChainEntry.or_mod_16, $hlp,*, $mods,*])

/-- the proof source for a leaf that is an add-stage chain (`none`: not of this shape) -/
def chainProofSrc? (cdecl : Name) (cdom : Nat) (cm : Sparkle.IR.AST.Module) : Option ProofSrc :=
  if (chainDataOf? cm).isSome && (dataWidths? cm).isSome then some (.built (buildChain cdecl cdom)) else none

end Tools.VedH3ChildChainEntry

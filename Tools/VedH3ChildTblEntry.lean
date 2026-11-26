import Tools.VedU1Entry
import Tools.VedH3ChildTbl

/-!
# Named constant-table leaves: reading the body and the proof script (issue sparkle-ved-hier3-child)

`ntblDataOf?` reads an `NData` (Tools/VedH3ChildTbl.lean) from the module of a register-free, one-input
leaf whose body is straight-line `const` / `ref` / `eq`-against-the-input / `mux` statements and that the
position-skeleton table route (`tblDataOf?`) does not take.  `buildNTbl` is the `ProofSrc.built` builder for
such a leaf; `childProofSrc` is the choice the hierarchical entries make for a combinational child.  Reading
only picks the script: the kernel checks that the module's body IS `NData.body`, `NData.ok`, and for every
input value that the value of the output position equals the declaration's own value.  Untrusted like the
script.
-/

namespace Tools.VedH3ChildTblEntry

open Lean Elab Term Meta Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1TableGen Tools.VedH3ChildTbl

open Tools.VedU1TableGen in
deriving instance Lean.ToExpr for Form
deriving instance Lean.ToExpr for NData

/-- The named table read from a register-free one-input module (`none`: not of this shape). -/
def ntblDataOf? (m : Sparkle.IR.AST.Module) (inp : String) : Option NData := do
  guard (m.body.length ≥ 2)
  let iw ← match m.inputs with | [⟨_, .bitVector n⟩] => some n | _ => none
  let w ← match m.outputs with | [⟨_, .bitVector n⟩] => some n | _ => none
  let mut pos : Std.HashMap String Nat := {}
  let mut names : Array String := #[]
  let mut i := 0
  for s in m.body do
    match s with
    | .assign l _ => pos := pos.insert l i; names := names.push l
    | _ => failure
    i := i + 1
  let mut fl : Array Form := #[]
  for s in m.body do
    let .assign _ e := s | failure
    let f ← match e with
      | .const v w' => if v < 0 then none else some (Form.const v.toNat w')
      | .ref n => (pos.get? n).map Form.alias
      | .op .eq [.ref a, .ref c] => if a == inp then (pos.get? c).map Form.eqIn else none
      | .op .mux [.ref c, .ref x, .ref y] => do
        let c' ← pos.get? c; let x' ← pos.get? x; let y' ← pos.get? y
        some (Form.mux c' x' y')
      | _ => none
    fl := fl.push f
  guard (iw ≤ 10)
  -- the wires of the module are the input and every position but the last
  guard (m.wires.map (·.name) == inp :: names.toList.dropLast)
  let fw := fl.foldl (fun a f => match f with | .const _ w' => max a w' | _ => a) 1
  let D0 : NData := { ns := names.toList, Fl := fl.toList, inp, iw, w, nse := names.toList.map enc, fw, rows := [] }
  guard (D0.ok = true)
  -- the value of every position at every input value, packed (the kernel re-checks each row)
  let rows := (List.range (2 ^ iw)).map fun x =>
    let vs := D0.Fl.foldl (fun (acc : List Nat) f => acc ++ [f.ev x (fun j => acc.getD j 0)]) []
    (vs.zipIdx.foldl (fun (r : Nat) (v, p) => r + ((v % 2 ^ fw) <<< (fw * p))) 0)
  let D : NData := { D0 with rows }
  guard (D.rowsOk = true)
  pure D

/-- `ProofSrc.built` builder: the script for the named table (`stmtDecl`: the declaration constant,
`nDom`: its domain arguments) -/
def buildNTbl (stmtDecl : Name) (nDom : Nat) (nm : Names) (m : Sparkle.IR.AST.Module) : TermElabM Syntax := do
  let clkRst := clkRstOf m
  let inNames := (dataPortsOf m clkRst).map fun p => p.name
  let some inp := inNames.head? | throwError "ntbl: no data input"
  let some D := ntblDataOf? m inp | throwError "ntbl: the body is not a named table"
  let dn := nm.mod.getPrefix ++ `ved_ntbl
  addDefn dn (Lean.mkConst ``NData) (toExpr D)
  let Dc := mkCIdent dn
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
  `(by
    have hD : ($Dc).ok = true := by decide +kernel
    have hR : ($Dc).rowsOk = true := by decide +kernel
    have hbody : ($M).body = ($Dc).body := by ved_kernel_rfl
    have hB : $B = ($M).body := rfl
    have hin : ($M).inputs.map (·.name) = [($Dc).inp] := by decide +kernel
    have hout : ∀ p ∈ ($M).outputs, p.name = "out" := by decide +kernel
    have hord : OrderOk $M $B = true := by
      rw [hB, hbody]
      exact Tools.VedH3ChildTbl.orderOk_ntbl $Dc hD $M hbody hin hout
    have hw : ($M).wires.map (·.name) = ($Dc).inp :: ($Dc).ns.dropLast := by decide +kernel
    have hnd : (($M).wires.map (·.name)).Nodup := by
      rw [hw]; exact Tools.VedH3ChildTbl.NData.nodup_wires $Dc hD
    have hregs : ∀ r ∈ regsOf ($M).body, ∃ p ∈ ($M).wires, p.name = r.1 ∧ scalar p.ty = true := by
      intro r hr
      rw [hbody, Tools.VedH3ChildTbl.NData.body, Tools.VedU1TableGen.regsOf_bodyN] at hr
      exact absurd hr (List.not_mem_nil)
    refine ⟨by decide +kernel, by decide +kernel, ⟨hnd, by decide +kernel, by decide +kernel, hregs⟩, ⟨$B, hord⟩, ?_⟩
    apply outputs_of_order $B hord
    apply outputs_of_step $C $M $B $f $O (by decide +kernel) (fun _ _ _ => True)
    · intro _ _; trivial
    · intro $insI hok $sI st mems _
      have hdi : ($C).dataInputs = [⟨($Dc).inp, .bitVector ($Dc).iw⟩] := by decide +kernel
      have hin1 : $insI $sI ($Dc).inp < 2 ^ declWidth $M ($Dc).inp :=
        hok.1 $sI ⟨($Dc).inp, .bitVector ($Dc).iw⟩ (by rw [hdi]; exact List.mem_singleton_self _)
      have hdw : declWidth $M ($Dc).inp = ($Dc).iw := by decide +kernel
      rw [hdw] at hin1
      rw [hB, hbody]
      obtain ⟨envF, hstep, hout'⟩ := Tools.VedH3ChildTbl.step_ntbl $Dc hD (declWidth $M) mems
        (seedIn $M $insI $sI st)
      refine ⟨envF, [], mems, hstep, ?_, trivial⟩
      intro o ho
      simp only [$O:ident, List.mem_singleton] at ho
      subst ho
      rw [hout']
      have hseed : seedIn $M $insI $sI st ($Dc).inp = $insI $sI ($Dc).inp := by simp [seedIn, hin]
      rw [hseed]
      simp [srcOf, $C:ident, contractOf, applyIns, OTy.obs, PTy.obs, PTy.sig]
      have hall : ∀ x, x < 2 ^ ($Dc).iw →
          ($Dc).out x = (($f ⟨fun _ => BitVec.ofNat ($Dc).iw x⟩).val 0).toNat := by
        decide +kernel
      refine Eq.trans (Tools.VedH3ChildTbl.NData.out_eq $Dc hD hR _ hin1).symm (Eq.trans (hall _ hin1) ?_)
      ved_kernel_rfl)

/-- the proof source of a combinational child: the named-table builder when the body has that shape and
the position-skeleton route does not take it, else the generated script -/
def childProofSrc (cdecl : Name) (cdom : Nat) (cm : Sparkle.IR.AST.Module) : ProofSrc :=
  let inNames := (dataPortsOf cm (clkRstOf cm)).map fun p => p.name
  match inNames with
  | [inp] =>
    if (tblDataOf? cm inp).isNone && (ntblDataOf? cm inp).isSome then .built (buildNTbl cdecl cdom) else .generated
  | _ => .generated

end Tools.VedH3ChildTblEntry

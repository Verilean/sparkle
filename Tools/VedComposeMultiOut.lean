import Tools.VedU1HierComp

/-! k-output instance step for a combinational leaf child (unit 11).

`instEval_leaf_multi` is `Tools.VedU1Hier.instEval_leaf` with the single output replaced by a list of
(output port, wire) pairs; the single-output lemma is its k = 1 instance (`instEval_leaf_of_multi`). -/

namespace Tools.VedComposeMultiOut

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier

/-- The value of output port `o` of child `c` on the given input values in arrangement `b`
(`0` when the fold fails; the composition lemma proves it does not). -/
def leafOutAt (c : Module) (b : List Stmt) (o : String) (vals : List Nat) : Nat :=
  ((evalAssigns (declWidth c) (fun _ _ => 0) b
      (seedOfVals (c.inputs.map (·.name)) vals)).map fun e => e o).getD 0

theorem leafOut_eq_leafOutAt (c : Module) (b : List Stmt) (vals : List Nat) :
    leafOut c b vals = leafOutAt c b (outNameOf c) vals := rfl

theorem mapM_refs (envC : Env) (ps : List (String × String)) :
    (ps.map (fun q => (q.1, Expr.ref q.2))).mapM (fun p =>
      match p.2 with
      | .ref x => some (x, envC p.1)
      | _ => none) = some (ps.map (fun q => (q.2, envC q.1))) := by
  induction ps with
  | nil => simp
  | cons q r ih =>
    simp only [List.map_cons, List.mapM_cons]
    rw [ih]; simp

/-- `outWrites` for a list of `(port, wire)` pairs. -/
theorem outWrites_multi (c : Module) (conns : List (String × Expr)) (envC : Env)
    (ps : List (String × String))
    (h : conns.filter (fun p => c.outputs.any (·.name == p.1)) =
      ps.map (fun q => (q.1, Expr.ref q.2))) :
    outWrites c conns envC = some (ps.map (fun q => (q.2, envC q.1))) := by
  unfold outWrites
  rw [h]
  exact mapM_refs envC ps

/-- THE k-OUTPUT INSTANCE STEP. -/
theorem instEval_leaf_multi (d : Design) (arr : Module → List Stmt) (we : WEnv) (mn iname : String)
    (conns : List (String × Expr)) (cm : Module) (xs : List String) (ps : List (String × String))
    (env : Env)
    (hres : findMod d mn = some cm) (hprim : cm.isPrimitive = false)
    (hall : conns.all (fun p => (cm.inputs ++ cm.outputs).any (·.name == p.1)) = true)
    (hin : (cm.inputs.map (·.name)).map (fun n => conns.lookup n) = xs.map (fun x => some (Expr.ref x)))
    (hout : conns.filter (fun p => cm.outputs.any (·.name == p.1)) =
      ps.map (fun q => (q.1, Expr.ref q.2)))
    (hass : assignOnly cm.body = true) (hperm : (arr cm).Perm cm.body)
    (hfuel : 0 < fuelOf d) (hsucc : LeafSucc cm (arr cm)) :
    instEval d (runAt d arr (fuelOf d)) we mn iname conns env
      = some (ps.map (fun q => (q.2, leafOutAt cm (arr cm) q.1 (xs.map env)))) := by
  have hasgA : assignOnly (arr cm) = true := assignOnly_perm hperm.symm hass
  have hleaf := assignOnly_leaf _ hasgA
  obtain ⟨seed0, E0, hE0⟩ := hsucc
  have hE0' : evalAssignsI (declWidth cm)
      (instEval d (runAt d arr (fuelOf d - 1)) (declWidth cm)) (arr cm) seed0 = some E0 := by
    rw [evalAssignsI_leaf _ _ (fun _ _ => 0) _ _ hleaf]; exact hE0
  obtain ⟨k, hk⟩ : ∃ k, fuelOf d = k + 1 := ⟨fuelOf d - 1, by omega⟩
  have hseed := childSeed_eq we env cm conns xs hin
  have hrun : ∀ seed, ∃ envC, runAt d arr (fuelOf d) cm seed = some envC ∧
      evalAssigns (declWidth cm) (fun _ _ => 0) (arr cm) seed = some envC := by
    intro seed
    obtain ⟨E', hE'⟩ := evalAssignsI_succ (declWidth cm)
      (instEval d (runAt d arr (fuelOf d - 1)) (declWidth cm)) _ seed0 E0 hleaf hE0' seed
    refine ⟨E', ?_, ?_⟩
    · rw [hk]
      simp only [runAt, assignOnly_comb _ hass, if_true]
      rw [hk] at hE'; simpa using hE'
    · rw [← evalAssignsI_leaf (declWidth cm) (instEval d (runAt d arr (fuelOf d - 1)) (declWidth cm))
        (fun _ _ => 0) _ _ hleaf]
      exact hE'
  obtain ⟨envC, hr1, hr2⟩ := hrun (seedOfVals (cm.inputs.map (·.name)) (xs.map env))
  unfold instEval
  simp only [hres, hprim, hall, hseed]
  simp only [Bool.false_eq_true, if_false, if_true]
  change ((runAt d arr (fuelOf d) cm (seedOfVals (cm.inputs.map (·.name)) (xs.map env))).bind
    fun envC => outWrites cm conns envC) = _
  rw [hr1]
  change outWrites cm conns envC = _
  rw [outWrites_multi cm conns envC ps hout]
  simp [leafOutAt, hr2]

/-- Control: the existing single-output instance step is the k = 1 case. -/
theorem instEval_leaf_of_multi (d : Design) (arr : Module → List Stmt) (we : WEnv)
    (mn iname : String)
    (conns : List (String × Expr)) (cm : Module) (xs : List String) (y : String) (env : Env)
    (hres : findMod d mn = some cm) (hprim : cm.isPrimitive = false)
    (hall : conns.all (fun p => (cm.inputs ++ cm.outputs).any (·.name == p.1)) = true)
    (hin : (cm.inputs.map (·.name)).map (fun n => conns.lookup n) = xs.map (fun x => some (Expr.ref x)))
    (hout : conns.filter (fun p => cm.outputs.any (·.name == p.1)) = [(outNameOf cm, Expr.ref y)])
    (hass : assignOnly cm.body = true) (hperm : (arr cm).Perm cm.body)
    (hfuel : 0 < fuelOf d) (hsucc : LeafSucc cm (arr cm)) :
    instEval d (runAt d arr (fuelOf d)) we mn iname conns env
      = some [(y, leafOut cm (arr cm) (xs.map env))] :=
  instEval_leaf_multi d arr we mn iname conns cm xs [(outNameOf cm, y)] env hres hprim hall hin
    hout hass hperm hfuel hsucc

/-- Per-output child theorem (any number of outputs): the child's real `U1Stmt` gives, for EVERY
output port `o` of the contract, `leafOutAt` at the observed arguments equal to that port's
observed value; `child_rel_out` is the one-output observation of the same fact. -/
theorem child_rel_outAt (cc : Contract) (cm : Module) (g : cc.table.Ty) (b : List Stmt)
    (hU : U1Stmt cc cm g) (hpa : b.Perm cm.body) (hwo : WO [] b)
    (hasg : assignOnly cm.body = true) (hclk : cc.clkRst = none)
    (args : ArgSigs cc.table.ins) (t : Nat) :
    ∀ o ∈ cc.outputs, leafOutAt cm b o.name (obsArgs cc.table.ins args t) =
      ((cc.outNames.zip (cc.table.out.obs ((applyArgs cc.table.ins g args).val t))).lookup o.name).getD 0 := by
  intro o ho
  obtain ⟨envC, hE, hO⟩ := child_rel cc cm g b hU hpa hwo hasg hclk args t
  obtain ⟨hcorr, ⟨hcore, _⟩, _⟩ := hU
  obtain ⟨hl1, hl2, hl3, _⟩ := hcorr
  have hinp : cm.inputs = cc.dataInputs := by
    rw [hcore.2.2.2.2.1]; simp [clkRstPorts, hclk]
  have hnames : cm.inputs.map (·.name) = cc.inNames := by rw [hinp]; exact dataInputs_names cc hl2
  simp only [leafOutAt, hnames, hE, Option.map_some, Option.getD_some]
  exact hO o ho

end Tools.VedComposeMultiOut

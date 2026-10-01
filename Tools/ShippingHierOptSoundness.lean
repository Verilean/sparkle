import Tools.ShippingHierSVSoundness
import Tools.ShippingOptSoundness

/-! # The optimizer on instance-bearing modules, validated by interface extraction

`checkedOptimize` keeps the optimizer's output unchecked on any body that is
not assignment-only, so a hierarchical parent reaches the printer through an
unvalidated pass. This file closes that step by translation validation with
the EXISTING combinational checker: drop the instance statements and declare
the instance-output wires as extra input ports (`openFlat`). In the
open-module view that changes nothing — an instance is a no-op and its
outputs are free — so `optCheck` on the two extracted modules validates the
optimizer on the original pair, and the linked meaning is carried across by
the bridge: the same oracle seeding is consistent for the optimized module
as soon as its instance statements are the original ones and every wire
they read keeps its value. -/
namespace Tools.ShippingHierOptSoundness

open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.OptCheck
open Sparkle.IR.Reorder (writesOf)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingSeqOptSoundness
open Tools.SVParser.EmitSem (seqCheck emitAssigns emitRegs emitMemWrites runModuleSV)
open Tools.ShippingSeqSVSoundness (seqNames seedIn_bounded)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingHierSVSoundness
open Tools.ShippingOptSoundness (optCheck_sound)

/-- The body without its instance statements. -/
def openBody (body : List Stmt) : List Stmt :=
  body.filter fun st =>
    match st with
    | .inst .. => false
    | _ => true

/-- Interface extraction: instance statements dropped, the given ports added
as inputs (the instance-output wires) and as outputs (assigned wires the
instances read). Declarations are untouched. -/
def openFlat (m : Module) (insX outsX : List Port) : Module :=
  { m with body := openBody m.body, inputs := m.inputs ++ insX,
           outputs := m.outputs ++ outsX }

/-- The open-module fold does not see instance statements. -/
theorem evalAssigns_openBody (we : WEnv) (mems : MEnv) :
    ∀ (body : List Stmt) (env : Env),
      evalAssigns we mems (openBody body) env = evalAssigns we mems body env
  | [], _ => rfl
  | .assign l r :: rest, env => by
    show evalAssigns we mems (.assign l r :: openBody rest) env = _
    show ((evalExpr we env r).bind fun v =>
        evalAssigns we mems (openBody rest) (fun n => if n = l then v else env n)) =
      ((evalExpr we env r).bind fun v =>
        evalAssigns we mems rest (fun n => if n = l then v else env n))
    cases evalExpr we env r with
    | none => rfl
    | some v =>
      simp only [Option.bind_some]
      exact evalAssigns_openBody we mems rest _
  | .inst mn iname conns :: rest, env => by
    show evalAssigns we mems (openBody rest) env = evalAssigns we mems rest env
    exact evalAssigns_openBody we mems rest env
  | .register o c rk i iv :: rest, env => by
    show evalAssigns we mems (.register o c rk i iv :: openBody rest) env = _
    show evalAssigns we mems (openBody rest) env = evalAssigns we mems rest env
    exact evalAssigns_openBody we mems rest env
  | .memory nm aw dw clk wa wd wen ra rd cr ew er :: rest, env => by
    show evalAssigns we mems
      (.memory nm aw dw clk wa wd wen ra rd cr ew er :: openBody rest) env = _
    cases cr with
    | false =>
      show evalAssigns we mems (openBody rest) env = evalAssigns we mems rest env
      exact evalAssigns_openBody we mems rest env
    | true =>
      show ((comboReads we mems nm aw dw ((ra, rd) :: er) env).bind fun env' =>
          evalAssigns we mems (openBody rest) env') =
        ((comboReads we mems nm aw dw ((ra, rd) :: er) env).bind fun env' =>
          evalAssigns we mems rest env')
      cases comboReads we mems nm aw dw ((ra, rd) :: er) env with
      | none => rfl
      | some env' =>
        simp only [Option.bind_some]
        exact evalAssigns_openBody we mems rest env'

/-- **The optimizer is validated on the open-module view**: an accepted
extracted pair runs to environments agreeing on every output and every
extracted output, from any seed fitting the extracted inputs. -/
theorem hier_opt_open {m o : Module} {insX outsX : List Port}
    (hchk : optCheck (openFlat m insX outsX) (openFlat o insX outsX) = true)
    {mems : MEnv} {init envM : Env}
    (hins : ∀ x ∈ (m.inputs ++ insX).map (·.name), init x < 2 ^ declWidth m x)
    (hevM : evalAssigns (declWidth m) mems m.body init = some envM) :
    ∃ envO, evalAssigns (declWidth o) mems o.body init = some envO ∧
      ∀ p ∈ m.outputs ++ outsX, envO p.name = envM p.name := by
  have hevM' : evalAssigns (declWidth (openFlat m insX outsX)) mems
      (openFlat m insX outsX).body init = some envM := by
    show evalAssigns (declWidth m) mems (openBody m.body) init = some envM
    rw [evalAssigns_openBody]
    exact hevM
  obtain ⟨envO, hevO, hout, -, -⟩ := optCheck_sound hchk (mems := mems) hins hevM'
  refine ⟨envO, ?_, hout⟩
  have hevO' : evalAssigns (declWidth o) mems (openBody o.body) init = some envO := hevO
  rw [evalAssigns_openBody] at hevO'
  exact hevO'

theorem lookup_ref_mem {k : String} {w : String} :
    ∀ (l : List (String × Expr)), l.lookup k = some (.ref w) → (k, Expr.ref w) ∈ l
  | [], h => by cases h
  | (a, b) :: rest, h => by
    by_cases hk : (k == a) = true
    · have : (some b : Option Expr) = some (.ref w) := by
        simpa [List.lookup, hk] using h
      cases this
      rw [eq_of_beq hk]
      exact List.mem_cons_self
    · have hk' : (k == a) = false := by simpa using hk
      have : rest.lookup k = some (.ref w) := by
        simpa [List.lookup, hk'] using h
      exact List.mem_cons_of_mem _ (lookup_ref_mem rest this)

/-- Consistency survives a change of body and environment that keeps the
instance statements and every wire they connect. -/
theorem consistent_transfer {children : String → Option (Module × WEnv)} {mems : MEnv}
    {bodyM bodyO : List Stmt} {envF envO : Env}
    (h : Consistent children mems bodyM envF)
    (hinst : ∀ mn iname conns, Stmt.inst mn iname conns ∈ bodyO →
      Stmt.inst mn iname conns ∈ bodyM)
    (hagree : ∀ mn iname conns, Stmt.inst mn iname conns ∈ bodyO →
      ∀ c ∈ conns, ∀ w, c.2 = .ref w → envO w = envF w) :
    Consistent children mems bodyO envO := by
  intro mn iname conns hm
  obtain ⟨child, cwe, envAt, cres, hc, hrun, hreads, houts⟩ :=
    h mn iname conns (hinst mn iname conns hm)
  refine ⟨child, cwe, envAt, cres, hc, hrun, ?_, ?_⟩
  · intro c hcm w hw hnot
    rw [hreads c hcm w hw hnot]
    exact (hagree mn iname conns hm c hcm w hw).symm
  · intro p hp w hw
    rw [hagree mn iname conns hm (p.name, .ref w) (lookup_ref_mem conns hw) w rfl]
    exact houts p hp w hw

/-- Decidable: every wire an instance of `o` connects is either an output /
extracted output of `m` (validated by the checker) or is written by neither
body (so it keeps its seeded value in both). -/
def connAgreeOk (m o : Module) (outsX : List Port) : Bool :=
  o.body.all fun st =>
    match st with
    | .inst _ _ conns =>
      conns.all fun c =>
        match c.2 with
        | .ref w =>
          ((m.outputs ++ outsX).map (·.name)).contains w ||
            (!(writesOf m.body).contains w && !(writesOf o.body).contains w)
        | _ => true
    | _ => true

/-- Decidable: the instance statements of `o` are instance statements of `m`. -/
def instsKept (m o : Module) : Bool :=
  o.body.all fun st =>
    match st with
    | .inst mn iname conns =>
      m.body.any fun st' =>
        match st' with
        | .inst mn' iname' conns' =>
          mn' == mn && iname' == iname &&
            decide (conns' = conns)
        | _ => false
    | _ => true

theorem instsKept_mem {m o : Module} (h : instsKept m o = true) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body →
      Stmt.inst mn iname conns ∈ m.body := by
  intro mn iname conns hm
  have := List.all_eq_true.mp h _ hm
  obtain ⟨st', hst', hp⟩ := List.any_eq_true.mp this
  cases st' with
  | inst mn' iname' conns' =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    subst h1 h2 h3
    exact hst'
  | assign l r => cases hp
  | register o' c rk i iv => cases hp
  | memory nm aw dw clk wa wd wen ra rd cr ew er => cases hp

theorem memFree_of_comb : ∀ (body : List Stmt), body.all combStmtI = true →
    Tools.ConeFold.memFree body
  | [], _ => trivial
  | .assign _ _ :: rest, h => by
    have h' : rest.all combStmtI = true := by
      simp only [List.all_cons, Bool.and_eq_true] at h; exact h.2
    show Tools.ConeFold.memFree rest
    exact memFree_of_comb rest h'
  | .inst .. :: rest, h => by
    have h' : rest.all combStmtI = true := by
      simp only [List.all_cons, Bool.and_eq_true] at h; exact h.2
    show Tools.ConeFold.memFree rest
    exact memFree_of_comb rest h'
  | .register .. :: rest, h => by simp [combStmtI] at h
  | .memory .. :: rest, h => by simp [combStmtI] at h

/-- **The linked meaning crosses the optimizer.** From a linked run of the
raw module `m`, the optimized module `o` — validated on the extracted pair,
with its instance statements kept — runs in the open-module view from the
SAME oracle seeding to an environment that agrees with the linked result on
every output and is consistent with the children. -/
theorem hier_opt_transfer {m o : Module} {insX outsX : List Port}
    {children : String → Option (Module × WEnv)}
    (hcombM : m.body.all combStmtI = true) (hcombO : o.body.all combStmtI = true)
    (hwf : linkedWF children m.body = true)
    (hchk : optCheck (openFlat m insX outsX) (openFlat o insX outsX) = true)
    (hkept : instsKept m o = true)
    (hconn : connAgreeOk m o outsX = true)
    {we0 : WEnv} (hwag0 : ∀ n ∈ seqNames m.body, we0 n = declWidth m n)
    {env0 envF : Env} {mems : MEnv}
    (hrun : evalAssignsH we0 children mems m.body env0 = some envF)
    (hins : ∀ x ∈ (m.inputs ++ insX).map (·.name),
      seedOuts children m.body envF env0 x < 2 ^ declWidth m x) :
    ∃ envO,
      evalAssigns (declWidth o) mems o.body (seedOuts children m.body envF env0) =
        some envO ∧
      (∀ p ∈ m.outputs, envO p.name = envF p.name) ∧
      Consistent children mems o.body envO := by
  have hrunD : evalAssignsH (declWidth m) children mems m.body env0 = some envF := by
    rw [← evalAssignsH_we_congr hcombM hwag0 env0]
    exact hrun
  have hopen := linked_open (declWidth m) children mems m.body env0 envF hwf hrunD
  have hcons := linked_consistent (declWidth m) children mems m.body env0 envF hwf hrunD
  obtain ⟨envO, hevO, hout⟩ := hier_opt_open hchk hins hopen
  refine ⟨envO, hevO, fun p hp => hout p (List.mem_append_left _ hp), ?_⟩
  refine consistent_transfer hcons (instsKept_mem hkept) ?_
  intro mn iname conns hm c hc w hw
  have hgate := List.all_eq_true.mp hconn _ hm
  have hgate' := List.all_eq_true.mp hgate c hc
  rw [hw] at hgate'
  have hgate'' : (((m.outputs ++ outsX).map (·.name)).contains w ||
      (!(writesOf m.body).contains w && !(writesOf o.body).contains w)) = true := hgate'
  rcases Bool.or_eq_true_iff.mp hgate'' with hin | hun
  · have hmem : w ∈ (m.outputs ++ outsX).map (·.name) := by
      simpa [List.contains_eq_mem] using hin
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hmem
    rw [← hpn]
    exact hout p hp
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hun
    have hnM : w ∉ writesOf m.body := by
      simpa [List.contains_eq_mem] using hun.1
    have hnO : w ∉ writesOf o.body := by
      simpa [List.contains_eq_mem] using hun.2
    rw [Tools.ConeFold.evalAssigns_frame _ mems o.body _ envO hevO
        (memFree_of_comb _ hcombO) w hnO,
      Tools.ConeFold.evalAssigns_frame _ mems m.body _ envF hopen
        (memFree_of_comb _ hcombM) w hnM]

/-- **The hierarchical post-pipeline, optimizer included.** The linked
evaluation of the raw module `m` is observed — at every output of `m` — by
the emitted Verilog of the OPTIMIZED module `o` and by the module parsed back
from its printed bytes, both run from the oracle seeding, and the result is
consistent with the children. The gates: the existing checker on the
extracted pair, instance statements kept, connection wires validated or
untouched, and the open-module layers' own checks on `o`. -/
theorem hier_shipping_transfer {m o : Module} {insX outsX : List Port}
    {body' bimg : List Stmt} {children : String → Option (Module × WEnv)}
    (hcombM : m.body.all combStmtI = true) (hcombO : o.body.all combStmtI = true)
    (hwf : linkedWF children m.body = true)
    (hchk : optCheck (openFlat m insX outsX) (openFlat o insX outsX) = true)
    (hkept : instsKept m o = true)
    (hconn : connAgreeOk m o outsX = true)
    -- emitted-SV and parsed-bytes premises, on the optimized module
    (hsv : seqCheck (Tools.SVParser.RoundtripProof.moduleWof o)
      (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof o)) o.body = true)
    (hwag : ∀ n ∈ seqNames o.body,
      declWidth o n = Tools.SVParser.EmitSem.weOf
        (Tools.SVParser.RoundtripProof.moduleWof o) n)
    (hok' : body'.all seqStmtOkI = true)
    (hcert : Tools.SVParser.RoundtripProof.semFragCheck o = true)
    (hI : Tools.SVParser.RoundtripProof.bodyImage
      (Tools.SVParser.RoundtripProof.moduleWof o) o.wires o.body = some bimg)
    (hchkR : Tools.SVParser.RoundtripProof.bodyReorderCheck body' bimg = true)
    -- the linked run of the raw module and the seeding's bounds
    {we0 : WEnv} (hwag0 : ∀ n ∈ seqNames m.body, we0 n = declWidth m n)
    {env0 envF : Env} {mems : MEnv}
    (hrun : evalAssignsH we0 children mems m.body env0 = some envF)
    (hins : ∀ x ∈ (m.inputs ++ insX).map (·.name),
      seedOuts children m.body envF env0 x < 2 ^ declWidth m x)
    (hB : Bounded (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof o))
      (seedOuts children m.body envF env0)) :
    ∃ envO,
      (∃ pairs regs mprog,
        emitAssigns (Tools.SVParser.RoundtripProof.moduleWof o) o.body = some pairs ∧
        emitRegs (Tools.SVParser.RoundtripProof.moduleWof o) o.body = some regs ∧
        emitMemWrites (Tools.SVParser.RoundtripProof.moduleWof o) o.body = some mprog ∧
        runModuleSV (Tools.SVParser.RoundtripProof.moduleWof o) pairs regs mprog
          (seedIn m (fun _ => seedOuts children m.body envF env0)) 1
          (seedOuts children m.body envF env0) mems = some [envO]) ∧
      runModule (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof o))
        body' (seedIn m (fun _ => seedOuts children m.body envF env0)) 1
        (seedOuts children m.body envF env0) mems = some [envO] ∧
      (∀ p ∈ m.outputs, envO p.name = envF p.name) ∧
      Consistent children mems o.body envO := by
  obtain ⟨envO, hevO, hout, hcons⟩ := hier_opt_transfer hcombM hcombO hwf hchk hkept
    hconn hwag0 hrun hins
  have hok := seqStmtOkI_of_comb hcombO
  have hrun1 : runModule (declWidth o) o.body
      (seedIn m (fun _ => seedOuts children m.body envF env0)) 1
      (seedOuts children m.body envF env0) mems = some [envO] := by
    simp only [runModule, stepModule, seedIn_const, hevO, regNexts_comb hcombO,
      memNexts_okI hok, Option.bind_eq_bind, Option.bind_some]
  refine ⟨envO, ?_, ?_, hout, hcons⟩
  · exact seq_run_to_svI hok hsv hwag _ (seedIn_bounded (fun _ x _ => hB x)) hB hrun1
  · exact seq_run_to_parsedI (m := m) hok hok' hcert hI hchkR hwag
      (ins := fun _ => seedOuts children m.body envF env0) (fun _ x _ => hB x) hB hrun1

end Tools.ShippingHierOptSoundness

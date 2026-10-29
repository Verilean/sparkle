import Tools.ShippingGen2CallField
import Tools.ShippingGen2CombKid
import Tools.ShippingGen2AComb
import Tools.ShippingGen2MemShips
import Tools.ShippingMachineExtB
set_option autoImplicit false

/-! # S4 consumer (G-ONEOUT), stage A: one-output parents on the A boundary
(scripts/gen2/S4_CONSUMER_FREEZE.md rev2, approved at 4ff583e9; §1, §2.5, §2.6, §3 stage A)

Scope: parents with `instFields = []`, `insts ≠ []` (and, for `oneOut_childShips`, `slots ≠ []`), closed by
`closeInsts`. Stage A only: the served consumer `machine_linked_callsServed1` (`ComposedHB … p.extBS`), its depth form
`oneOut_composedNW` (`ComposedNW n`) and the parent's `ChildShips` (`oneOut_childShips`). No width/bound/memory premise
(S4-WID, S4-BD, S4-MEM are stages B/C). A closing of stage A is not a completion of stage B/C, G-ONEOUT or M2.

**Residues of stage A (premises without a supplier here):** `h` (G-SERVED, `ServedShipsStmt`, Defs:251, not built);
`hdec` in the STRENGTHENED form (`CallDec` only, no `MemDec` disjunct: the §7 case restriction); `hext : ExtInS p`.

**AUDIT (same witness; freeze §2.6), as realised in `machine_linked_callsServed1`:**
1. `wired`, `hx` (= `ServedP (ShipsRes L P) p.decl p.d.shape raw D ids cache`) and `trace` come from the SAME `obtain`
   of the ONE `MachineTraceLBX` `h`. The `ids`/`cache` in `Served1P`'s `machPorts … ids cache` names and in
   `machine_linked_ofB`'s callback `CallStmt` are those `ids`/`cache`, definitionally (no rewriting). No second trace;
   no `Served1P` from another witness.
2. `trace` is passed WHOLE to `machine_linked_ofB` (its `∀ i bools bits T seed st0 mems` intact; not specialised).
3. `F := oneF P p i` is chosen AFTER `intro i`; the conclusion is used at that `i` only. `oneP` does not depend on `i`.
4. `OneOutCall`/`CallDec` are used at the `intro`'s `i bools bits`, never at a chosen element of `ι` (no `Nonempty ι`).
5. Differences from `machine_linked_callsRA` (the template): `X := ServedP (ShipsRes L P)` for `ServedRealA O`;
   `extB := p.extBS`; `hcalls`/`hfn` discharged (from `hdec` and the served evidence), not premises;
   `P F := oneP P p, oneF P p i`, chosen per `i`; premise `hkc` added; conclusion `ComposedHB … p.extBS` for
   `ComposedH`. Nothing else. -/
namespace Tools.ShippingGen2
-- Defs.lean:16-33, verbatim
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingQuadComposed (GenFacts)
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingMachineCallsLinkedT (valsOf MemFacts)
open Tools.ShippingMachineChild (InRange boolsOf bitsOf)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain
-- Defs.lean:122 (for `dv` in §3)
open Tools.ShippingChildBndCore (cv dv)

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## §1 Selecting the combinational branch (pure, small) -/

/-- `CallStmt`'s clock/reset refusal, as non-membership of the input names. -/
theorem callStmt_noClk {nIn kI n : Nat} {names : List String} {k : Nat} {args : List Nat}
    {mc : Sparkle.IR.AST.Module} {st : Stmt}
    (h : Tools.ShippingMachineInst.CallStmt nIn kI n names k args mc st) :
    "clk" ∉ mc.inputs.map (·.name) ∧ "rst" ∉ mc.inputs.map (·.name) := by
  obtain ⟨_, _, _, _, _, _, _, hclk, _⟩ := h
  constructor
  · intro hm
    obtain ⟨x, hx, hxn⟩ := List.mem_map.mp hm
    have h1 : (mc.inputs.any (fun p => p.name == "clk" || p.name == "rst")) = true :=
      List.any_eq_true.mpr ⟨x, hx, by simp [hxn]⟩
    exact Bool.false_ne_true (hclk.symm.trans h1)
  · intro hm
    obtain ⟨x, hx, hxn⟩ := List.mem_map.mp hm
    have h1 : (mc.inputs.any (fun p => p.name == "clk" || p.name == "rst")) = true :=
      List.any_eq_true.mpr ⟨x, hx, by simp [hxn]⟩
    exact Bool.false_ne_true (hclk.symm.trans h1)

/-- Without a clock input, a child run is the combinational one (as `childRunN_iff_seq`, AComb:28-30). -/
theorem combChildRunN_of_noClk {children : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn : Design} {n : Nat}
    {mc : Sparkle.IR.AST.Module} {bsC : List (Name × MixedGateBinder)} {outsC : List OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hclk : "clk" ∉ mc.inputs.map (·.name)) :
    ChildRunN children dsn n mc bsC outsC S → CombChildRunN children dsn n mc bsC outsC S :=
  fun h => h.elim (fun hs => absurd hs.2.2.1 hclk) id

/-- `kidsCombB`'s first conjunct at one instance: its module is assignments only. -/
theorem kidsCombB_assign {ms : List Sparkle.IR.AST.Module} {body : List Stmt} {mn iname : String}
    {conns : List (String × Sparkle.IR.AST.Expr)} {c : Sparkle.IR.AST.Module}
    (h : kidsCombB ms body = true) (hst : Stmt.inst mn iname conns ∈ body)
    (hc : moduleByName ms mn = some c) : c.body.all isAssign = true := by
  unfold Sparkle.IR.Machine.kidsCombB at h
  have h1 := List.all_eq_true.mp h _ hst
  cases hA : c.body.all Sparkle.IR.RegDedup.isAssign with
  | true => rfl
  | false => simp [hc, hA] at h1

/-- `hI` of the consumers from the data's `domB` row (`bsIn := binders.take nIn`, Auto:195). -/
theorem data_hI {p : Pkg ι dom} (h : MemParentDataOk p) : ∀ b ∈ p.d.bsIn.drop p.kD, b.2 ≠ .domain := by
  obtain ⟨hok, hco, -, -, hdom⟩ := h.rows
  have hkD := data_hkD p.d p.kD hok hco
  intro b hb
  refine hdom b ?_
  have hsplit : p.d.shape.binders = p.d.bsIn ++ p.d.shape.binders.drop p.d.nIn :=
    (List.take_append_drop p.d.nIn p.d.shape.binders).symm
  rw [hsplit, List.drop_append_of_le_length hkD]
  exact List.mem_append_left _ hb

/-! ## §2.5 The served consumer -/

/-- The argument condition of call `k`: in range for the callee package's ports (`Pkg.ports`, Pkg.lean:80-81). -/
def oneP (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) (v : List Nat) : Prop :=
  ∃ q, P ((p.d.shape.insts.map (·.1))[k]?.getD .anonymous) = some q ∧ InRange v q.ports

/-- The function of call `k` at index `i`: the callee's only output, at time 0, on the constant argument stream. -/
noncomputable def oneF (P : Pkgs ι dom) (p : Pkg ι dom) (i : ι) (k : Nat) (v : List Nat) : Nat :=
  match P ((p.d.shape.insts.map (·.1))[k]?.getD .anonymous) with
  | some q => ((q.S i (fun _ => v))[0]?.map (· 0)).getD 0
  | none => 0

/-- The callee name `oneP`/`oneF` read is call `k`'s. -/
theorem oneName_eq (p : Pkg ι dom) {k : Nat} (hk : k < p.d.shape.insts.length) :
    (p.d.shape.insts.map (·.1))[k]?.getD .anonymous = (p.d.shape.insts[k]).1 := by
  simp only [List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]

theorem oneName_some (P : Pkgs ι dom) (p : Pkg ι dom) {k : Nat} (hk : k < p.d.shape.insts.length)
    {q : Pkg ι dom} (hq : P (p.d.shape.insts[k]).1 = some q) :
    P ((p.d.shape.insts.map (·.1))[k]?.getD .anonymous) = some q := by
  rw [oneName_eq p hk]
  exact hq

theorem oneP_of (P : Pkgs ι dom) (p : Pkg ι dom) {k : Nat} (hk : k < p.d.shape.insts.length)
    {q : Pkg ι dom} (hq : P (p.d.shape.insts[k]).1 = some q) {v : List Nat} (hv : InRange v q.ports) :
    oneP P p k v := by
  unfold oneP
  exact ⟨q, oneName_some P p hk hq, hv⟩

theorem oneF_of (P : Pkgs ι dom) (p : Pkg ι dom) (i : ι) {k : Nat} (hk : k < p.d.shape.insts.length)
    {q : Pkg ι dom} (hq : P (p.d.shape.insts[k]).1 = some q) (v : List Nat) :
    oneF P p i k v = ((q.S i (fun _ => v))[0]?.map (· 0)).getD 0 := by
  have h := oneName_some P p hk hq
  unfold oneF
  split
  · rename_i q' hq'
    have hqq : q' = q := Option.some.inj (hq'.symm.trans h)
    rw [hqq]
  · rename_i hn
    exact absurd (hn.symm.trans h) (by simp)

/-- `ChildFn` is antitone in its argument condition and respects pointwise equality of the function on it. -/
theorem childFn_mono {mc : Sparkle.IR.AST.Module} {P P' : List Nat → Prop} {f f' : List Nat → Nat}
    (h : Tools.ShippingMachineCompose.ChildFn mc P f) (hP : ∀ v, P' v → P v) (hf : ∀ v, P' v → f v = f' v) :
    Tools.ShippingMachineCompose.ChildFn mc P' f' := by
  obtain ⟨outP, hout, hrun⟩ := h
  refine ⟨outP, hout, fun mems env hr hp => ?_⟩
  obtain ⟨cres, hc, hv⟩ := hrun mems env hr (hP _ hp)
  exact ⟨cres, hc, hv.trans (hf _ hp)⟩

/-- **The served consumer** (freeze §2.5-§2.6). -/
theorem machine_linked_callsServed1 (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hsimple : p.d.shape.instFields = [])
    (hkD : p.kD ≤ p.d.bsIn.length)
    (hI : ∀ b ∈ p.d.bsIn.drop p.kD, b.2 ≠ .domain)
    (hIlen : (p.d.bsIn.drop p.kD).length = p.d.shape.insts.length)
    (hSL : ∀ b ∈ p.d.slotBs ++ p.d.letBs, b.2 ≠ .domain)
    (hSlen : p.d.slotBs.length = p.d.shape.layout.slots.length)
    (hLlen : p.d.letBs.length = p.d.shape.layout.lets)
    (hNIn : machNIn p.d.shape = ((p.d.bsIn.take p.kD).filter (fun b => b.2 != .domain)).length)
    (hkc : kidsCombB D.modules raw.body = true)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k) :
    Tools.ShippingMachineShipsHierH.ComposedHB (fun _ _ => True) p.decl p.d p.kD raw D dom p.src p.extS p.extBS := by
  -- AUDIT 1: ONE witness
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, hx, trace⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, ?_⟩
  intro i bools bits T seed st0 mems hsrc hpass hrst hinit _
  -- the instance served to call `k` is a combinational run of the callee's package, assignments only
  have hserve : ∀ k (hk : k < p.d.shape.insts.length) (args : List Nat) (mc : Sparkle.IR.AST.Module) (st : Stmt),
      (p.d.shape.insts.map (·.2.1))[k]? = some args → st ∈ raw.body →
      Tools.ShippingMachineInst.CallStmt (machNIn p.d.shape) p.d.shape.insts.length
        p.d.shape.layout.slots.length
        ((machPorts p.decl ids cache p.d.shape.binders).map (·.name)) k args mc st →
      Sparkle.IR.Machine.moduleByName D.modules mc.name = some mc →
      ∀ q : Pkg ι dom, P (p.d.shape.insts[k]).1 = some q → CallDec p q k →
      mc.body.all isAssign = true ∧
        ∃ n', CombChildRunN (childMap D.modules) D n' mc (q.d.bsIn.take q.kD) q.d.shape.layout.outs (q.S i) := by
    intro k hk args mc st hargs hst hcs hmod q hq hcd
    have hA : mc.body.all isAssign = true := by
      obtain ⟨_, _, _, iname, _, _, _, _, _, _, _, _, _, hsteq⟩ := hcs
      rw [hsteq] at hst
      exact kidsCombB_assign hkc hst hmod
    refine ⟨hA, ?_⟩
    rcases hx.2 hsimple k hk args mc st hargs hst hcs hmod with ⟨md, hmd, _⟩ | ⟨Dc, hship, hDc⟩
    · -- a memory-origin instance: excluded by `CallDec`'s ordinary origin
      have h1 := hcd.1
      rw [List.getD_eq_getElem?_getD] at h1
      rw [h1] at hmd
      cases hmd
    · obtain ⟨_, q', n', hq', _, hcs'⟩ := hship
      have hqq : q' = q := Option.some.inj (hq'.symm.trans hq)
      subst hqq
      exact ⟨n', combChildRunN_of_noClk (callStmt_noClk hcs).1 (hcs' D hDc hmod i)⟩
  -- AUDIT 2/3: `trace` whole; `F := oneF P p i` after `intro i`
  refine Tools.ShippingMachineCompose.machine_linked_ofB (ι := ι) (dom := dom)
    (declName := p.decl) (d := p.d) (m := raw) (dsn := D)
    (src := p.src) (ext := p.extS) (extB := p.extBS) (lsrc := p.lsrc)
    nd len rnd rlen llen wired trace hsimple p.kD hkD hI hIlen hSL hSlen hLlen hNIn
    (oneP P p) (oneF P p i) i bools bits T seed st0 mems hsrc hpass hrst hinit ?_ ?_
  · -- every call's module computes `oneF P p i k` on `oneP P p k`
    intro k args mc st hargs hst hcs hmod
    have hk : k < p.d.shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hargs).1; simpa using this
    obtain ⟨q, hq, hcd⟩ := hdec k hk
    obtain ⟨hA, n', hcomb⟩ := hserve k hk args mc st hargs hst hcs hmod q hq hcd
    -- AUDIT 4: at the intro's `i bools bits`
    obtain ⟨_, _, _, _, hall⟩ := oneOutCall_of_callDec hsimple hcd
    obtain ⟨_, _, o, hsing, hS, _⟩ := hall i bools bits
    obtain ⟨_, _, outP, _, _, _, hout, _⟩ := hcs
    rw [hsing] at hcomb
    have hfn := childFn_of_combRun hcomb hA hout (fun v _ => hS v)
    have h1 := oneName_some P p hk hq
    refine childFn_mono hfn ?_ ?_
    · intro v hv
      unfold oneP at hv
      obtain ⟨q', hq', hin⟩ := hv
      have hqq : q' = q := Option.some.inj (hq'.symm.trans h1)
      rw [hqq] at hin
      exact hin
    · intro v _
      exact (oneF_of P p i hk hq v).symm
  · -- the source's call is `oneF P p i k` of its arguments
    intro k args j hargs hj
    have hk : k < p.d.shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hargs).1; simpa using this
    obtain ⟨q, hq, hcd⟩ := hdec k hk
    -- AUDIT 4: at the intro's `i bools bits`
    obtain ⟨_, args', hargs', _, hall⟩ := oneOutCall_of_callDec hsimple hcd
    have hae : args' = args := Option.some.inj (hargs'.symm.trans hargs)
    rw [hae] at hall
    obtain ⟨hbnd, hrng, o, hsing, hS, f, hf, hpos⟩ := hall i bools bits
    -- the instance of call `k` (the module's wiring), served as above
    obtain ⟨args'', mc, st, hargs'', hst, hmod, hcs⟩ := wired.2.2.2.2.1 hsimple k hk
    obtain ⟨hA, n', hcomb⟩ := hserve k hk args'' mc st hargs'' hst hcs hmod q hq hcd
    obtain ⟨g, hg⟩ := hS (valsOf (p.lsrc i bools bits) args j)
    have hfg : f j = g 0 :=
      combS_pointwise hcomb hA (valsOf (p.lsrc i bools bits) args) j 0 o f g
        (fun τ' _ => hrng τ') (by simp [hsing]) hf hg
    have hF : oneF P p i k (valsOf (p.lsrc i bools bits) args j) = g 0 := by
      rw [oneF_of P p i hk hq, hg, Option.map_some, Option.getD_some]
    refine ⟨?_, oneP_of P p hk hq (hrng j), hF.trans (hfg.symm.trans (hpos j).symm)⟩
    intro x hx
    obtain ⟨r, hr, hrx⟩ := List.getElem_of_mem hx
    obtain ⟨hl, g', hg'⟩ := hbnd r hr
    rw [← hrx]
    exact ⟨hl, (List.getElem?_eq_some_iff.mp hg').1⟩

/-! ## §3 Stage A -/

theorem oneOut_composedNW (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat) :
    Tools.ShippingMachineDepthRun.ComposedNW n p.decl p.d p.kD raw D dom p.src p.extS p.extBS := by
  obtain ⟨hok, hco, hslots, -, -⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hI := data_hI hdata
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  -- `kidsCombB` of the run, checked by its one-output closing
  have ranA := Tools.ShippingRanABridge.machineRanA_of_runJQC L.O hA L.T ran
  obtain ⟨_, _, _, _, _, _, _, _, hcl, _⟩ :=
    Tools.ShippingParentDesignA.core_closeInstsA L.O p.d hins hsimple ranA
  have hkc : kidsCombB D.modules raw.body = true := Tools.ShippingChildServe.closeInsts_kidsComb hcl
  exact Tools.ShippingMachineDepthHR.composedNWn_of_HB n (R := fun _ _ => True)
    (machine_linked_callsServed1 L P p h hsimple hkD hI hIlen hSL hSlen hLlen hNIn hkc hdec)
    (by unfold Tools.ShippingMachineDepthH.BoundH; intros; trivial)
    (Tools.ShippingMachineDepthHR.kidsComb_of_B hkc)

theorem oneOut_childShips (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hext : ExtInS p)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat) :
    ChildShips p (n + 1) b D := by
  obtain ⟨hok, hco, hslots, houtTy, -⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have hNW := oneOut_composedNW L P p hdata hins hsimple hA ran hdec h n
  have ranA := Tools.ShippingRanABridge.machineRanA_of_runJQC L.O hA L.T ran
  -- no self-instantiation, from the run's one-output closing (`closeInsts_acyclic`)
  have acyc : Tools.ShippingHierMono.NoInstOf raw.name raw.body ∧
      ∀ g ∈ D.modules, Tools.ShippingHierMono.NoInstOf raw.name g.body := by
    obtain ⟨_, _, _, _, _, _, _, _, hcl, _⟩ :=
      Tools.ShippingParentDesignA.core_closeInstsA L.O p.d hins hsimple ranA
    obtain ⟨_, h1, h2, _⟩ := Tools.ShippingChildServe.closeInsts_acyclic hcl
    exact ⟨h1, h2⟩
  have hI0 : 0 < p.d.shape.insts.length := by
    cases h : p.d.shape.insts with
    | nil => exact absurd h hins
    | cons _ _ => simp
  intro dsn hcons _ i
  have hEA : Tools.ShippingHierMono.ExtendsAway raw.name (childMap D.modules) (childMap dsn.modules) := by
    refine ⟨?_, ?_⟩
    · intro x r _ hD
      obtain ⟨g, hg, rfl⟩ := Tools.ShippingMachineDepthRun.childMap_some.mp hD
      have hm := Tools.ShippingHierPremisesBase.moduleByName_mem hg
      exact Tools.ShippingMachineDepthRun.childMap_some.mpr ⟨g, by rw [← hm.2]; exact hcons g hm.1, rfl⟩
    · intro x r hD
      obtain ⟨g, hg, rfl⟩ := Tools.ShippingMachineDepthRun.childMap_some.mp hD
      exact acyc.2 g (Tools.ShippingHierPremisesBase.moduleByName_mem hg).1
  exact Or.inl <| Tools.ShippingGen2C6.seqChildRunN_of_composedNW_run n houtTy (ok_outNameOk p.d hok) hsl hI0 hkD hIlen hSL
    hSlen hLlen hNIn hext.1 hext.2 i hNW hpost hEA acyc.1

end Tools.ShippingGen2

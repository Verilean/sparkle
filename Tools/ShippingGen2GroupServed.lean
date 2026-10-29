import Tools.ShippingGen2GroupComb
import Tools.ShippingGen2Connect
set_option autoImplicit false
-- WRITTEN, NOT BUILT (S3 stage B, scripts/gen2/S3_GROUP_FREEZE.md rev1 §4).

/-! # S3 stage B: the served consumer, `ComposedNW` and the parent's `ChildShips` for group parents
(scripts/gen2/S3_GROUP_FREEZE.md rev1 §4, approved D1(a)-D5)

* B1 `ordFactsRN_of_callDec`: `seqFactsRN_of_callDec` (Connect:120-147) with `hseq` DELETED and `PC` split into the two
  branches: `SeqFactsRN (seqPC …)` from C2 (`childRunN_iff_seq`, the `"clk" ∈` carried by `seqPC`) and
  `CombFactsRN (combPC …)` from `combChildRunN_of_noClk` (the `"clk" ∉` carried by `combPC`). `hdec` unchanged.
* B2 `groupHcalls_of_dec`: the per-entry premise of B3 from `StepStmt`'s `hdec` (Defs:309-310) VERBATIM.
* B3 `machine_linkedT_callsServedC`: `machine_linkedT_callsServed` (Consumer:30-105) with `hcalls` in the A6 form and
  `calls_hchildRNC` for `calls_hchildRN`; the `hsv` discharge verbatim.
* B4 `group_composedNW`, B5 `group_childShips` (`memParent_childShips`, MemShips:39-84, with `hmo`/`hmd` replaced by
  `hdec`, `h`; `pkg_memComposedNW` by B4). Scope (D4): group parents with slots, `ChildShips` only, fixed `n` (D5).

**Residues (premises, not supplied here):** `h` over `ServedP (ShipsAt L P n)` = G-SERVED + G-LIFT; `MemParentDataOk p`,
`ExtInS p` (DataOk rows); the case `hins`/`hfe`/`hsl`.

**AUDIT (freeze §7), as realised here:**
1. B3: `wired`, `hx` and `trace` come from ONE `obtain` of the single `MachineTraceLBX` `h` (Consumer:87 verbatim); the
   `ids`/`cache` are those of that obtain. B4/B5 pass their ONE `h` to B3 unchanged (no second trace).
2. B2/B3/B4: `hcalls` is built at the `intro`'d `i bools bits` (B3's own `hcalls i bools bits`, B4's lambda); no
   `Nonempty ι`, no chosen `i`.
3. No binder of type `∀ mc, ServedPC … c mc → "clk" ∈ …` (or its negation); `seqFactsRN_of_callDec` is not referenced. -/
namespace Tools.ShippingGen2
-- Connect.lean:14-34 verbatim
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

open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingChildInv (Res)
-- for `dv` in B5 (as MemShips:32)
open Tools.ShippingChildBndCore (cv dv)

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **B1: `CallDec` + the served child fact at height `n` ⇒ both branch facts** — `seqFactsRN_of_callDec`
(Connect:120) without `hseq`: the sequential branch is restricted to served modules WITH the clock (`seqPC`, C2), the
combinational one to those WITHOUT (`combPC`, `combChildRunN_of_noClk`). -/
theorem ordFactsRN_of_callDec {L : Laws mref cref} {P : Pkgs ι dom} {p q : Pkg ι dom} {k n : Nat} {c : Name}
    (dsn : Design) (body : List Stmt) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (hG : p.d.shape.instFields ≠ [])
    (hP : P c = some q) (hdec : CallDec p q k) :
    Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN (childMap dsn.modules) n p.d.shape dsn body
      (p.lsrc i bools bits) p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extBS i bools bits) (p.extS i bools bits)
      (pkgBsC P) (pkgOutsC P) (pkgS P i) (seqPC (ServedPC (ShipsAt L P n) dsn)) k c ∧
    CombFactsRN (childMap dsn.modules) n p.d.shape dsn body
      (p.lsrc i bools bits) p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extBS i bools bits) (p.extS i bools bits)
      (pkgBsC P) (pkgOutsC P) (pkgS P i) (combPC (ServedPC (ShipsAt L P n) dsn)) k c := by
  obtain ⟨hnone, args, hargs, hlen, hall⟩ := hdec
  obtain ⟨h4, h5, k', o, f, ho, hon, hf, hpos⟩ := hall i bools bits
  have hB : pkgBsC P c = q.d.bsIn.take q.kD := by simp [pkgBsC, hP]
  have hO : pkgOutsC P c = q.d.shape.layout.outs := by simp [pkgOutsC, hP]
  have hS : pkgS P i c = q.S i := by simp [pkgS, hP]
  refine ⟨⟨hnone, args, hargs, ?_, h4, ?_, k', o, f, ?_, (callField_group hG).mp hon, ?_, hpos⟩,
    ⟨hnone, args, hargs, ?_, h4, ?_, k', o, f, ?_, (callField_group hG).mp hon, ?_, hpos⟩⟩
  · -- sequential half (Connect:135-144 with `hseq mc hmc` replaced by the branch's own `"clk" ∈`)
    intro mc hmc
    have hclk : "clk" ∈ mc.inputs.map (·.name) := And.right hmc
    obtain ⟨hmod, Dc, ⟨_, q', hq', _, hcs⟩, hcons⟩ := And.left hmc
    rw [hP] at hq'
    cases hq'
    have h := (childRunN_iff_seq hclk).mp (hcs dsn hcons hmod i)
    rw [hB, hO, hS]
    refine ⟨h, ?_⟩
    rw [h.2.2.2.2.2.1, hlen]
    rfl
  · rw [hB]; exact h5
  · rw [hO]; exact ho
  · rw [hS]; exact hf
  · -- combinational half (the same, `combChildRunN_of_noClk` with the branch's own `"clk" ∉`)
    intro mc hmc
    have hclk : "clk" ∉ mc.inputs.map (·.name) := And.right hmc
    obtain ⟨hmod, Dc, ⟨_, q', hq', _, hcs⟩, hcons⟩ := And.left hmc
    rw [hP] at hq'
    cases hq'
    have h := combChildRunN_of_noClk hclk (hcs dsn hcons hmod i)
    rw [hB, hO, hS]
    refine ⟨h, ?_⟩
    rw [h.2.2.2.2.2.1, hlen]
    rfl
  · rw [hB]; exact h5
  · rw [hO]; exact ho
  · rw [hS]; exact hf

/-- **B2**: the per-entry premise of B3 from `StepStmt`'s decoding premise (Defs:309-310, verbatim). -/
theorem groupHcalls_of_dec {L : Laws mref cref} {P : Pkgs ι dom} {p : Pkg ι dom} (n : Nat) (dsn : Design)
    (body : List Stmt) (hG : p.d.shape.instFields ≠ [])
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k) :
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) k c,
      (p.d.shape.insts.map (·.1))[k]? = some c →
      MemFacts p.d.shape (p.lsrc i bools bits) p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extS i bools bits) k c ∨
      (Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN (childMap dsn.modules) n p.d.shape dsn body (p.lsrc i bools bits)
          p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extBS i bools bits) (p.extS i bools bits)
          (pkgBsC P) (pkgOutsC P) (pkgS P i) (seqPC (ServedPC (ShipsAt L P n) dsn)) k c ∧
       CombFactsRN (childMap dsn.modules) n p.d.shape dsn body (p.lsrc i bools bits)
          p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extBS i bools bits) (p.extS i bools bits)
          (pkgBsC P) (pkgOutsC P) (pkgS P i) (combPC (ServedPC (ShipsAt L P n) dsn)) k c) := by
  -- AUDIT 2: at the intro's `i bools bits`
  intro i bools bits k c hc
  have hk : k < p.d.shape.insts.length := by
    have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
  have hck : (p.d.shape.insts[k]).1 = c := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc; simpa using hc
  rcases hdec k hk with hmd | ⟨q, hq, hcd⟩
  · subst hck
    exact Or.inl (memFacts_of_memDec hmd i bools bits)
  · subst hck
    exact Or.inr (ordFactsRN_of_callDec (L := L) (n := n) dsn body i bools bits hG hq hcd)

end Tools.ShippingGen2

/-! ## B3: consumer 2 with both child branches (namespace of Consumer.lean, its opens verbatim) -/
namespace Tools.ShippingGen2Consumer
-- Consumer.lean:12-26 verbatim
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge
open Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierMono
open Tools.ShippingMachineDepth Tools.ShippingMachineDepthChild Tools.ShippingMachineDepthRun
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingEntrySoundness (RunsTo)
open Sparkle.IR.Machine (OutField SlotField moduleByName outNameOk)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildDepthC Tools.ShippingChildComposeC Tools.ShippingChildRunAKids
open Tools.ShippingChildRunAMain Tools.ShippingServedRealA Tools.ShippingChildTranslateA
open Tools.ShippingChildFrontCP Tools.ShippingMachineCallsLinkedT Tools.ShippingMachineCallsLinkedTN Tools.ShippingMachineCallsLinkedTNR
open Tools.ShippingChildBndCore Tools.ShippingChildBndInit Tools.ShippingMachineEntry

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **B3**: `machine_linkedT_callsServed` (Consumer:30) with the per-entry premise in the A6 form (both child
branches, `PC := ServedPC Q dsn` restricted per branch) and `calls_hchildRNC`. Otherwise verbatim. -/
theorem machine_linkedT_callsServedC (Q : Name → Res → Prop) (n : Nat) {declName : Name} {d : MachineData} {m : Module} {dsn : Design}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX
      (Tools.ShippingGen2.ServedP Q declName d.shape m dsn)
      declName d m dsn dom src ext extB lsrc)
    (hfe : d.shape.instFields ≠ [])
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hI : ∀ b ∈ d.bsIn.drop kD, b.2 ≠ .domain)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (bsC : Name → List (Name × MixedGateBinder)) (outsC : Name → List OutField)
    (S : ι → Name → (Nat → List Nat) → List (Nat → Nat))
    (hcalls : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) k c,
      (d.shape.insts.map (·.1))[k]? = some c →
      MemFacts d.shape (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD (ext i bools bits) k c ∨
      (SeqFactsRN (childMap dsn.modules) n d.shape dsn m.body (lsrc i bools bits) d.ls.length
        (d.bsIn.drop kD) kD (extB i bools bits) (ext i bools bits) bsC outsC (S i)
        (Tools.ShippingGen2.seqPC (Tools.ShippingGen2.ServedPC Q dsn)) k c ∧
       Tools.ShippingGen2.CombFactsRN (childMap dsn.modules) n d.shape dsn m.body (lsrc i bools bits) d.ls.length
        (d.bsIn.drop kD) kD (extB i bools bits) (ext i bools bits) bsC outsC (S i)
        (Tools.ShippingGen2.combPC (Tools.ShippingGen2.ServedPC Q dsn)) k c))
 :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = d.ss.length ∧
      ∃ lets : List String, lets.length = d.letBs.length ∧
      MachineWired declName d.shape ids cache m dsn regs lets ∧
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
        (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
        (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv)
        (kids : String → KT n),
        (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
          (fun j => (extB i bools bits j).val (T - 1 - t))
          (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seed t st)) →
        (∀ t st r, r ∈ regs → seed t st r = st r) →
        (∀ t st, seed t st "rst" = 0) → (∀ t st, seed t st "clk" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          d.shape.layout.slots[k]? = some f → st0 r = f.init) →
        -- the children start from reset
        (∀ (iname : String) (mc : Module), (∃ conns, Stmt.inst mc.name iname conns ∈ m.body) →
          moduleByName dsn.modules mc.name = some mc → ResetN dsn n mc (kids iname)) →
        ∃ envs, runModuleTG (KSn (childMap dsn.modules) n) (Tools.ShippingEntrySoundness.weOf m)
            (childMap dsn.modules) m.body seed T ⟨st0, mems, kids⟩ = some envs ∧
          envs.length = T ∧
          ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
            (envs[j]'hj) o.name = f j := by
  -- AUDIT 1: ONE obtain of the ONE trace
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, hx, trace⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, ?_⟩
  intro i bools bits T seed st0 mems kids hin hpass hrst hclk0 hinit hreset
  exact Tools.ShippingMachineLinkedTG.machine_linkedTG_of (KSn (childMap dsn.modules) n)
    (KSn_local (childMap dsn.modules) n) nd len rnd rlen llen wired trace hfe kD hkD hI hIlen hSL
    hSlen hLlen hNIn i bools bits T seed st0 mems kids hin hpass hrst hclk0 hinit
    (Tools.ShippingGen2.calls_hchildRNC (childMap dsn.modules) n d.shape dsn m.body (lsrc i bools bits) d.ls.length
      (d.bsIn.drop kD) kD (extB i bools bits) (ext i bools bits) bsC outsC (S i) _ _ _ T kids hreset
      (Tools.ShippingGen2.ServedPC Q dsn)
      (fun k c mc iname argWs outs outWs hc hnone hst hout hke hmod => by
        have hk : k < d.shape.insts.length := by
          have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
        have hck : (d.shape.insts[k]).1 = c := by
          rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc; simpa using hc
        rcases hx.1 hfe k hk mc iname argWs outs outWs hst hout hke hmod with ⟨md, hmd, _⟩ | ⟨Dc, hrc, hcons⟩
        · rw [hnone] at hmd; cases hmd
        · rw [hck] at hrc
          exact ⟨hmod, Dc, hrc, hcons⟩)
      (hcalls i bools bits))

end Tools.ShippingGen2Consumer

namespace Tools.ShippingGen2
-- Connect.lean:14-34 verbatim (again, for B4/B5)
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

open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildBndCore (cv dv)

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **B4**: the composed run at depth `n` of a group parent whose entries are `MemDec` or `CallDec`, from the ONE
trace over `ServedP (ShipsAt L P n)` (B3 at `Q := ShipsAt L P n`, B2). -/
theorem group_composedNW (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) {raw : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hfe : p.d.shape.instFields ≠ [])
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc) :
    Tools.ShippingMachineDepthRun.ComposedNW n p.decl p.d p.kD raw D dom p.src p.extS p.extBS := by
  obtain ⟨hok, hco, hslots, -, hdomB⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hI := Tools.ShippingQuadComposed.bsIn_drop_nodomain p.d p.kD hdomB
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  -- AUDIT 1: the ONE `h`, whole; AUDIT 2: `hcalls` at the lambda's `i bools bits`
  exact Tools.ShippingGen2Consumer.machine_linkedT_callsServedC (ShipsAt L P n) n h hfe p.kD hkD hI hIlen hSL
    hSlen hLlen hNIn (pkgBsC P) (pkgOutsC P) (pkgS P)
    (fun i bools bits k c hc => groupHcalls_of_dec (L := L) n D raw.body hfe hdec i bools bits k c hc)

/-- **B5: a group parent with slots ships as a child at `n + 1`** (`memParent_childShips`, MemShips:39-84, with
`hmo`/`hmd` replaced by `hdec`, `h` and `pkg_memComposedNW` by B4). -/
theorem group_childShips (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hext : ExtInS p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc) :
    ChildShips p (n + 1) b D := by
  obtain ⟨hok, hco, hslots, houtTy, -⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have hNW := group_composedNW L P p hdata hfe hdec n h
  have ranA := Tools.ShippingRanABridge.machineRanA_of_runJQC L.O hA L.T ran
  -- no self-instantiation, from the run's group closing (MemShips:59-68 verbatim)
  have acyc : Tools.ShippingHierMono.NoInstOf raw.name raw.body ∧
      ∀ g ∈ D.modules, Tools.ShippingHierMono.NoInstOf raw.name g.body := by
    obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ranA
    rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, -⟩
    · exact absurd hno hins
    rcases hcc with ⟨hf0, -⟩ | ⟨-, hG, -⟩
    · exact absurd hf0 hfe
    obtain ⟨_, h1, h2⟩ := Tools.ShippingChildServe.closeInstsG_acyclic hG
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

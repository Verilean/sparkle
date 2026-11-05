import Tools.ShippingGen5NameKids2
import Tools.ShippingGen5NameKids3
import Tools.ShippingGen5NameKids4
import Tools.ShippingGen5NameKids5
import Tools.ShippingGen5NameKids6
import Tools.ShippingGen5NameKids7
import Tools.ShippingGen5FG
import Tools.ShippingSrm15Graph
set_option autoImplicit false
-- NOT BUILT (no build run yet).
-- U-A1 of B-AUD: the 8 theorems of AUDIT_CARRIER_FREEZE §6 (types copied from the freeze), plus the carrier defs `SOf` / `AuditE*` of freeze §2 that the theorem types mention.
-- Premise delta 0: no new premise; E-1 / E-2 / E-5(hsp) / E-9 are derived from E-5 parts, E-7, E-8, E-6 and `GraphAgrees`, which stay premises (not supplied here).
-- No sorry / axiom / native_decide.

namespace Tools.ShippingGen5AuditCarrier
open Lean Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5FG
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingSrm7Rank (CallGraph callees declRank InClass kidModName)
open Tools.ShippingSrm15Graph (graphOf FirstOcc)
open Tools.ShippingMemCloses (memKey)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingGen5NameKids2 (MemTagsNamed kidNameAt hmemSame_of_memTagsNamed)
open Tools.ShippingGen5NameKids3 (GraphAgrees ReachSpans OrdPath ReachClosed hself_all_reached reach_of_ordEdges)
open Tools.ShippingEntrySoundness (RunsTo)
open Sparkle.IR.ModuleName (ofDecl)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- carrier S: the shape of the package -/
def SOf (P : Pkgs ι dom) : Name → Option MachineShape := fun c => (P c).map (fun q => q.d.shape)

section Rows
variable (P : Pkgs ι dom) (Reach : Name → Prop)

def AuditE1 : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∀ (k : Nat) (hk : k < sp.insts.length) (k' : Nat) (hk' : k' < sp.insts.length),
      memKey (originAt sp k) ≠ none → memKey (originAt sp k) = memKey (originAt sp k') →
      (sp.insts[k]'hk).1 = (sp.insts[k']'hk').1

def AuditE2 : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∀ (k : Nat) (hk : k < sp.insts.length), memKey (originAt sp k) = none → (sp.insts[k]'hk).1 ≠ c

def AuditE5 (ds : List (Name × MachineData)) (B : Nat) (top : Name) : Prop :=
  GraphAgrees (graphOf ds) Reach (SOf P) ∧ ReachSpans (graphOf ds) top Reach ∧
  InClass (graphOf ds) B top = true ∧
  (∀ c, Reach c → ∀ sp, SOf P c = some sp → MemTagsNamed sp)

def AuditE6 : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∃ (n : Nat) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo)
      (senv : StructEnv) (ai : Bool),
      Tools.ShippingReaderFuel.machineShapeF n sm ps ci senv ai = some (some sp)

def AuditE7 (ds : List (Name × MachineData)) : Prop :=
  ∀ c, Reach c → ∃ d : MachineData, FirstOcc ds c d ∧ SOf P c = some d.shape

def AuditE8 (ds : List (Name × MachineData)) (B : Nat) (top : Name) : Prop :=
  (ds.map Prod.fst).eraseDups.length = ds.length ∧
  (declRank (graphOf ds) B top).isSome = true

def AuditE9 (ds : List (Name × MachineData)) (top : Name) : Prop :=
  GraphAgrees (graphOf ds) (OrdPath (graphOf ds) top) (SOf P)
end Rows

section Derive
variable (P : Pkgs ι dom) (top : Name)

private theorem memKey_none_of_child {o : Sparkle.Compiler.MachInstOrigin.InstOrigin} (h : o.child? = none) :
    memKey o = none := by
  cases o with
  | ord => rfl
  | field i => rfl
  | mem cb aw dw => simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?] at h

theorem reachClosed_tgtRun : ReachClosed (TgtRun P top) (SOf P) := by
  intro c hc sp hS k hk hch
  simp only [SOf] at hS
  cases hP : P c with
  | none => rw [hP] at hS; cases hS
  | some q =>
    rw [hP] at hS
    have e : q.d.shape = sp := Option.some.inj hS
    subst e
    exact TgtRun.call hc hP k hk hch

theorem reachSpans_tgtRun {g : CallGraph} (hg : GraphAgrees g (TgtRun P top) (SOf P)) :
    ReachSpans g top (TgtRun P top) := by
  intro c hc
  induction hc with
  | top => exact OrdPath.refl
  | @call c' q hc' hq k hk ord ih =>
    have h1 := hg c' hc'
    simp only [SOf, hq] at h1
    exact OrdPath.step ih ⟨q.d.shape.instTagged, originAt q.d.shape k, h1,
      Tools.ShippingSrm12Corr.instTagged_mem_idx q.d.shape hk, memKey_none_of_child ord⟩

theorem tgtRun_iff_ordPath {g : CallGraph} (hg : GraphAgrees g (TgtRun P top) (SOf P)) (c : Name) :
    TgtRun P top c ↔ OrdPath g top c :=
  ⟨reachSpans_tgtRun P top hg c,
   fun h => reach_of_ordEdges hg (reachClosed_tgtRun P top) TgtRun.top h⟩

theorem auditE9_of_tgtRun {ds : List (Name × MachineData)}
    (hg : GraphAgrees (graphOf ds) (TgtRun P top) (SOf P)) : AuditE9 P ds top :=
  fun c hc => hg c ((tgtRun_iff_ordPath P top hg c).2 hc)

end Derive

section Derive2
variable (P : Pkgs ι dom) (Reach : Name → Prop)

theorem auditE1_of_E5 {ds B top} (h : AuditE5 P Reach ds B top) : AuditE1 P Reach :=
  fun c hc sp hS k hk k' hk' hne hkey =>
    hmemSame_of_memTagsNamed sp (h.2.2.2 c hc sp hS) k hk k' hk' hne hkey

theorem auditE2_of_E5 {ds B top} (h : AuditE5 P Reach ds B top) : AuditE2 P Reach :=
  fun c hc sp hS k hk hm => hself_all_reached (r := 0) h.2.2.1 h.1 h.2.1 c hc sp hS k hk hm

theorem auditE5_of_parts {ds B top} (hfo : AuditE7 P Reach ds) (hnr : AuditE8 ds B top)
    (hsp : ReachSpans (graphOf ds) top Reach) (hF : AuditE6 P Reach) : AuditE5 P Reach ds B top :=
  ⟨Tools.ShippingGen5NameKids5.graphAgrees_of_firstOcc hfo, hsp,
   Tools.ShippingGen5NameKids6.inClass_graphOf hnr.1 hnr.2,
   Tools.ShippingGen5NameKids4.hmem_of_machineShapeF hF⟩
end Derive2

/-- full chain for Reach := TgtRun: E-7, E-8, E-6 (and nothing about ReachSpans) give E-5, E-9 -/
theorem auditE5_tgtRun {P : Pkgs ι dom} {top : Name} {ds : List (Name × MachineData)} {B : Nat}
    (hfo : AuditE7 P (TgtRun P top) ds) (hnr : AuditE8 ds B top) (hF : AuditE6 P (TgtRun P top)) :
    AuditE5 P (TgtRun P top) ds B top ∧ AuditE9 P ds top := by
  have hg := Tools.ShippingGen5NameKids5.graphAgrees_of_firstOcc hfo
  exact ⟨auditE5_of_parts P _ hfo hnr (reachSpans_tgtRun P top hg) hF, auditE9_of_tgtRun P top hg⟩

end Tools.ShippingGen5AuditCarrier

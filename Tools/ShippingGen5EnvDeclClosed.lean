import Tools.ShippingGen5ConstValueESL
set_option autoImplicit false
/-! # `EnvDeclClosed` as an explicit, localisable hypothesis (issue sparkle-ledger-dd4-sound, SoundS3; draft §SoundS3)

What can be SAID about `EnvDeclClosed env` (every stored declaration type / definition value has `lbr = 0`):
* It is a fact about the environment, not about `PT`. It is never assumed here and never an axiom. Lean's kernel only admits declarations that are closed terms (no loose bound
  variable); that is an invariant of `Environment.addDecl`, but `Environment` is an opaque kernel object in core, so the invariant cannot be derived in Lean from the API.
* The invariant is stated on `Expr.looseBVarRange` (`KernelClosedInvariant`); the link to the structural `lbr` the proofs use is the named bridge `OblLbrZero`
  (`ShippingGen5ConstValueESoundK`, unresolved, never assumed). `envDeclClosed_of_kernel` is the implication between these named `Prop`s.
* The evidence that the hypothesis holds on the corpus is a META AUDIT (`Tests/Gen5/EnvDeclClosedAudit*.lean`), not a proof: it evaluates a transcription of `lbr` on the real declarations.
  `EnvDeclClosedOn env R` is the localised form, matching what an audit of a finite name set (the names reached from the roots) establishes.
No TRUSTED, axiom, `sorry`, `native_decide`. -/
namespace Tools.ShippingGen5EnvDeclClosed
open Lean Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueESL

/-- closedness of the stored declaration at one name -/
def DeclClosedAt (env : Environment) (c : Name) : Prop :=
  (∀ ci : ConstantInfo, env.find? c = some ci → lbr ci.type = 0) ∧
  (∀ d : DefinitionVal, env.find? c = some (.defnInfo d) → lbr d.value = 0)

/-- `EnvDeclClosed` restricted to the names in `R` -/
def EnvDeclClosedOn (env : Environment) (R : Name → Prop) : Prop := ∀ c, R c → DeclClosedAt env c

theorem envDeclClosedOn_univ_iff (env : Environment) : EnvDeclClosedOn env (fun _ => True) ↔ EnvDeclClosed env :=
  ⟨fun h => ⟨fun c ci hci => (h c trivial).1 ci hci, fun c d hd => (h c trivial).2 d hd⟩,
   fun h c _ => ⟨fun ci hci => h.1 c ci hci, fun d hd => h.2 c d hd⟩⟩

theorem envDeclClosedOn_mono {env : Environment} {R S : Name → Prop} (hRS : ∀ c, S c → R c) (h : EnvDeclClosedOn env R) : EnvDeclClosedOn env S :=
  fun c hc => h c (hRS c hc)

/-- a finite audited list of names is a localised closedness fact -/
theorem envDeclClosedOn_of_list {env : Environment} {L : List Name} (h : ∀ c ∈ L, DeclClosedAt env c) : EnvDeclClosedOn env (fun c => c ∈ L) :=
  fun c hc => h c hc

/-- the global fact needs every name the environment stores: a localised fact covering all stored names is the global one -/
theorem envDeclClosed_of_on {env : Environment} {R : Name → Prop} (h : EnvDeclClosedOn env R) (hall : ∀ c ci, env.find? c = some ci → R c) : EnvDeclClosed env :=
  ⟨fun c ci hci => (h c (hall c ci hci)).1 ci hci,
   fun c d hd => (h c (hall c _ hd)).2 d hd⟩

/-- The kernel's invariant, stated on Lean's own `looseBVarRange` (a hypothesis form, NOT assumed anywhere). -/
def KernelClosedInvariant (env : Environment) : Prop :=
  (∀ (c : Name) (ci : ConstantInfo), env.find? c = some ci → ci.type.looseBVarRange = 0) ∧
  (∀ (c : Name) (d : DefinitionVal), env.find? c = some (.defnInfo d) → d.value.looseBVarRange = 0)

/-- The kernel invariant gives `EnvDeclClosed` through the named bridge `OblLbrZero` (an implication between named `Prop`s). -/
theorem envDeclClosed_of_kernel {env : Environment} (hz : OblLbrZero) (h : KernelClosedInvariant env) : EnvDeclClosed env :=
  ⟨fun c ci hci => hz _ (h.1 c ci hci), fun c d hd => hz _ (h.2 c d hd)⟩

end Tools.ShippingGen5EnvDeclClosed

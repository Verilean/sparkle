import Lean
set_option autoImplicit false
/-! # Recursors as iota rules — DRAFT OF TYPES ONLY (D.D-4, issue sparkle-ledger-dd4-res; doc: scripts/gen5/PRIM_RESIDUE_FULL.md §3)

Definitions and inductive types only. No theorem, no `sorry`, no axiom. NOT part of any ledger row, not adopted.
It states the iota rule that `RecursorVal.rules` gives, as a SYNTACTIC step on a spine (like `unfold`), and the one extra
constructor `CVE.iota` that `Tools.ShippingGen5ConstValueE.CVE` would get. The motive (a `Sort u`-valued function) is
never a value of the relation: it stays inside the syntax, so the `Type 0` restriction of `Dyn` is not touched. -/
namespace Tools.ShippingGen5IotaDraft
open Lean

/-- The five parts of a recursor spine `rec params motives minors indices major extra…` (`none` if under-applied). -/
structure RecSpine where
  params : Array Expr
  motives : Array Expr
  minors : Array Expr
  indices : Array Expr
  major : Expr
  extra : Array Expr

def RecSpine.split (rv : RecursorVal) (args : Array Expr) : Option RecSpine :=
  let p := rv.numParams
  let m := rv.numMotives
  let n := rv.numMinors
  let i := rv.numIndices
  if h : p + m + n + i < args.size then
    some { params := args.extract 0 p, motives := args.extract p (p + m),
           minors := args.extract (p + m) (p + m + n), indices := args.extract (p + m + n) (p + m + n + i),
           major := args[p + m + n + i], extra := args.extract (p + m + n + i + 1) args.size }
  else none

/-- One iota step on a closed spine: the recursor `rv` applied to a major premise that is a constructor application
of `rule.ctor` with `rule.nfields` fields reduces to `rule.rhs` (levels instantiated, then applied to
params, motives, minors, fields — the rules' own argument order — then to the extra arguments). The kernel's `RecursorRule`.
(`k`-like recursors, `Eq.rec`, and structure eta are NOT covered: see the document.) -/
inductive IotaStep (env : Environment) : Expr → Expr → Prop
  | step {rv : RecursorVal} {ls : List Level} {args : Array Expr} {sp : RecSpine} {rule : RecursorRule}
      {cls : List Level}
      (hrv : env.find? rv.name = some (.recInfo rv))
      (hsp : RecSpine.split rv args = some sp)
      (hrule : rule ∈ rv.rules)
      (hctor : sp.major.getAppFn = .const rule.ctor cls)
      (hfields : sp.major.getAppNumArgs = rv.numParams + rule.nfields) :
      IotaStep env (mkAppN (.const rv.name ls) args)
        (mkAppN ((rule.rhs.instantiateLevelParams rv.levelParams ls).beta
          (sp.params ++ sp.motives ++ sp.minors ++ (sp.major.getAppArgs.extract rv.numParams sp.major.getAppNumArgs)))
          sp.extra)

/-- The constructor `CVE` would get: the redex and its iota-reduct have the same denotation (any `CVE`-like relation `R`
indexed by an expression and the denotation data `D`). Stated for a generic relation to keep this file independent of
`Tools.ShippingGen5ConstValueE`; in the real file `R := CVE PT env ρ · τ α v`. Premise-only: no derivation is claimed. -/
def IotaRule {D : Type 1} (env : Environment) (R : Expr → D → Prop) : Prop :=
  ∀ (e e' : Expr) (d : D), IotaStep env e e' → R e' d → R e d

/-- Exclusivity with `unfold`/`prim`/`app`: `iota` applies only to a spine whose head is a `recInfo` (the other rules
need `defnInfo`, a non-recursor, or a non-const head), so it adds no overlap. -/
def IotaExclusive (env : Environment) : Prop :=
  ∀ (e e' : Expr), IotaStep env e e' → ∃ (c : Name), e.getAppFn.constName? = some c ∧ ∃ rv, env.find? c = some (.recInfo rv)

end Tools.ShippingGen5IotaDraft

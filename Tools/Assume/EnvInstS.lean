import Tools.ShippingGen5ReaderTrace
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.Assume.EnvInstS, exit 0, 721 jobs) on the tree of this file's commit. Assumption module (statements only; no theorems).

/-! # Environment assumption: `instS` result field counts do not depend on the arguments (`InstSFieldsDet`)

**This file holds ONLY an assumption statement** — a `Prop` definition that proofs take as a hypothesis. It is not an
`axiom` and not a theorem. A change here is a change of what is assumed and needs reviewer approval; proof files must
not redefine it.

Design: `scripts/gen5/DG_READERTRACE_FREEZE_REV12.md` §2 (reviewer-approved, option A: type and domain as written there).

* What is assumed: for every `senv.instS c = some (kinds, ty)` and any two argument lists `args`, `args'` for which
  `instRes ty args = some r` and `instRes ty args' = some r'` and `machOuts?` succeeds on both result types, the two
  field lists have the same length. It is used only by the dedup arm of `instSStep` (the second call of a module with
  the same wire list shares the first call's output rows, so `k0 + fields.length ≤ insts.size` needs equal counts).
* Why not proved: `machOuts? senv r` reads the field table of the head constant of `r`; that this head constant does
  not depend on `args` is a kernel typing fact about declared types, and `Lean.Environment` is not modelled in this
  development. This investigation found no supplier or route for it in the development; that is not a claim that it
  is underivable, nor that the condition is true.
* Ledger: counted once as **FG +1** (shared environment fact of C0; DG-ENV `sparkle-gen5-dg-env` owns the placement,
  shared with it, not counted twice; separate from `SigTyClosed` and `EnvTypesFVarFree`). FG 103 → 104, T1 +0.
  Registered by the commit that adds this file. The option-B condition `SigResHeadConst` is not chosen. -/

namespace Tools.Assume.EnvInstS
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5ReaderTrace Tools.ShippingReaderFuel

/-- **ASSUMPTION `InstSFieldsDet` (FG +1).** Two instantiations of the same `instS` signature type have equally many fields.
* Domain: every `(c, kinds, ty)` with `senv.instS c = some (kinds, ty)` and any two argument lists; for
  `senv = structEnv env₀`, `env₀` is the single environment carried by DG-ENV's C0. -/
def InstSFieldsDet (senv : StructEnv) : Prop :=
  ∀ (c : Lean.Name) (kinds : List MixedGateBinder) (ty : Lean.Expr) (args args' : List Lean.Expr) (r r' : Lean.Expr)
    (o o' : Option Lean.Name) (fs fs' : List (String × MixedGateBinder)),
    senv.instS c = some (kinds, ty) → instRes ty args = some r → instRes ty args' = some r' →
    machOuts? senv r = some (o, fs) → machOuts? senv r' = some (o', fs') → fs.length = fs'.length

end Tools.Assume.EnvInstS

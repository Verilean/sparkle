import Tools.Prototype.ExtModelLetOk
import Tools.Prototype.ExtRootFloat

/-! # Unit EXT2 (1/N): the operation record `ExtOps`, an exact `Expr.eqv` model, and the ISOLATED reader phases that CALL it

STATUS: BUILT; run names and exits are kept in REPORT-EXT2.md and in the ledger L6c28 (docs/parallel/main-theorem-connection.md).

Scope. `ExtOps` collects the operations the model reader previously took from the shipped (extern / partial) code and the
LetOk proofs needed premises for: `Expr.liftLooseBVars`, `Expr.lowerLooseBVars`, `Expr.instantiate1`, `Expr.beta` (one argument),
`Expr.eqv` (`==`), `rootFloat` (`partial def`), `zeroLit` (the extern `Expr.replace`) and, for the slot reservation, `zetaAll` (`partial def`).
`shippedOps` are the shipped operations; `modelOps` the kernel-visible models (`liftM`, `lowerM`, `inst1M`, `betaM`, `eqvX`, `rootFloatS`, `zeroLitM`,
`zetaAllM`).
`xxxX O …` is the TEXT of the shipped reader phase `xxx` with the call sites of those operations turned into `O.…`
(the phases that do not call them are shared, not copied). `…X shippedOps` is the shipped phase (checked by `rfl`/short proofs below).

NOT replaced (still the shipped functions, listed in the report): `Expr.eqv` inside the shared let-table helpers `machBindLet`,
`machBindLetNamed`, `machBindLetAlias`, `machLetIndex` (the `findIdx? (·.2.2 == v')` tests), `machReserve`'s `zetaAll`,
`Expr.hasLooseBVars`, `Expr.getAppFn/getAppArgs`, `Expr.replace` elsewhere. None of these produces an expression that flows into the
reader's result except through a `Bool` test, and the proofs below hold for ANY answer of such a test.
No sorry / axiom / native_decide. -/

namespace Tools.Prototype.ExtReader
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
  Tools.Prototype.NormNodeModelLetOk Tools.Prototype.ReaderLfp Lean.Order
open Tools.ShippingReaderFuelShapeR5 Tools.ShippingReaderLenOk Tools.ShippingCloInv
open Tools.Prototype.ReaderTyped Tools.Prototype.StartDomOk Tools.Prototype.ReaderClosed
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMixedSourceBridge
open Tools.Prototype.RawNodeRangeLetOk Tools.Prototype.ReaderComposed Tools.Prototype.NormStepModel
open Tools.Prototype.ExtModelLetOk
open Sparkle.Compiler.MachRawSurface (projChain listElems)

/-! ## an EXACT model of `Expr.eqv` (alpha-equivalence: binder names / binder infos / `nonDep` ignored) -/

def levelEqX : Lean.Level → Lean.Level → Bool
  | .zero, .zero => true
  | .succ a, .succ b => levelEqX a b
  | .max a b, .max a' b' => levelEqX a a' && levelEqX b b'
  | .imax a b, .imax a' b' => levelEqX a a' && levelEqX b b'
  | .param n, .param n' => n == n'
  | .mvar i, .mvar j => i.name == j.name
  | _, _ => false

def levelsEqX : List Lean.Level → List Lean.Level → Bool
  | [], [] => true
  | a :: as, b :: bs => levelEqX a b && levelsEqX as bs
  | _, _ => false

/-- Model of `Expr.eqv` (`==` on `Expr`): binder names and binder infos are ignored; the `let` `nonDep` flag, constants, levels, literals and
`mdata` payloads are compared (the executed grid `Tests/Compiler/ExtReaderOpsAgreeTest.lean` found that the extern DOES compare `nonDep`).
Unlike `eqvM` (EXT; an over-approximation sufficient for the `LetOk` direction, one direction of `EqvCorr` only), this is intended as a
faithful model, so that a reader that CALLS it takes the same branches as one that calls the extern; agreement is tested, not proved. -/
def eqvX : Lean.Expr → Lean.Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar a, .fvar b => a.name == b.name
  | .mvar a, .mvar b => a.name == b.name
  | .sort l, .sort l' => levelEqX l l'
  | .const n ls, .const n' ls' => n == n' && levelsEqX ls ls'
  | .lit a, .lit b => a == b
  | .app f a, .app f' a' => eqvX f f' && eqvX a a'
  | .lam _ t b _, .lam _ t' b' _ => eqvX t t' && eqvX b b'
  | .forallE _ t b _, .forallE _ t' b' _ => eqvX t t' && eqvX b b'
  | .letE _ t v b nd, .letE _ t' v' b' nd' => nd == nd' && (eqvX t t' && eqvX v v' && eqvX b b')
  | .mdata m e, .mdata m' e' => m == m' && eqvX e e'
  | .proj s i e, .proj s' i' e' => s == s' && i == i' && eqvX e e'
  | _, _ => false

theorem letOk_eqvX (k : Nat) : ∀ (a b : Lean.Expr), eqvX a b = true → LetOk k b = true → LetOk k a = true := by
  intro a
  induction a with
  | fvar x =>
    intro b h hb
    cases b <;> simp only [eqvX] at h <;> try contradiction
    rename_i y
    have : x.name = y.name := eq_of_beq h
    have hxy : x = y := by cases x; cases y; simp_all
    subst hxy; exact hb
  | app f x ihf ihx =>
    intro b h hb
    cases b <;> simp only [eqvX] at h <;> try contradiction
    simp only [Bool.and_eq_true] at h
    simp only [LetOk, Bool.and_eq_true] at hb ⊢
    exact ⟨ihf _ h.1 hb.1, ihx _ h.2 hb.2⟩
  | lam n t b bi iht ihb =>
    intro c h hc
    cases c <;> simp only [eqvX] at h <;> try contradiction
    simp only [Bool.and_eq_true] at h
    simp only [LetOk, Bool.and_eq_true] at hc ⊢
    exact ⟨iht _ h.1 hc.1, ihb _ h.2 hc.2⟩
  | forallE n t b bi iht ihb =>
    intro c h hc
    cases c <;> simp only [eqvX] at h <;> try contradiction
    simp only [Bool.and_eq_true] at h
    simp only [LetOk, Bool.and_eq_true] at hc ⊢
    exact ⟨iht _ h.1 hc.1, ihb _ h.2 hc.2⟩
  | letE n t v b nd iht ihv ihb =>
    intro c h hc
    cases c <;> simp only [eqvX] at h <;> try contradiction
    simp only [Bool.and_eq_true] at h
    simp only [LetOk, Bool.and_eq_true] at hc ⊢
    exact ⟨⟨iht _ h.2.1.1 hc.1.1, ihv _ h.2.1.2 hc.1.2⟩, ihb _ h.2.2 hc.2⟩
  | mdata m e ih =>
    intro c h hc
    cases c <;> simp only [eqvX] at h <;> try contradiction
    simp only [Bool.and_eq_true] at h
    simp only [LetOk] at hc ⊢
    exact ih _ h.2 hc
  | proj sn i e ih =>
    intro c h hc
    cases c <;> simp only [eqvX] at h <;> try contradiction
    simp only [Bool.and_eq_true] at h
    simp only [LetOk] at hc ⊢
    exact ih _ h.2 hc
  | _ => intro c h hc; simp [LetOk]

/-- The `Expr.replace` function of `zeroLit` (the text of `ZeroLitAgrees`' right-hand side). -/
def zeroLitF (x : Lean.Expr) : Option Lean.Expr :=
  match x with
  | .app (.const ``BitVec.zero _) w =>
    (canonicalNatLitValue? w).map fun n => mkApp2 (.const ``BitVec.ofNat []) (inlNatLit n) (inlNatLit 0)
  | _ => none

/-- Structural model of `zeroLit` (`Expr.replace` ↦ `replaceNoCache`). -/
def zeroLitM (e : Lean.Expr) : Lean.Expr := e.replaceNoCache zeroLitF

theorem zeroLitF_ok (n : Nat) : ∀ x r, zeroLitF x = some r → LetOk n r = true := by
  intro x r hx
  unfold zeroLitF at hx
  split at hx
  · obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp hx
    simp only [mkApp2, LetOk, Bool.and_eq_true, Bool.true_and]
    exact ⟨letOk_natLit _ _, letOk_natLit _ _⟩
  · simp at hx

theorem letOk_zeroLitM (n : Nat) (e : Lean.Expr) (he : LetOk n e = true) : LetOk n (zeroLitM e) = true :=
  replaceNoCache_ok n zeroLitF (zeroLitF_ok n) e he

/-- Model of `rootFloat`: the TOTAL model `rootFloatS` (LC6; termination PROVED there; its fuel model `rootFloatN` is shown adequate in
`ExtRootFloat`). The shipped `partial def` agrees with it only under the premise `RootFloatAgrees` (OPEN). -/
def rootFloatM (e : Lean.Expr) : Lean.Expr := rootFloatS e

theorem letOk_rootFloatM (e : Lean.Expr) (he : LetOk 0 e = true) : LetOk 0 (rootFloatM e) = true :=
  rootFloatS_ok 0 e he

/-- Fuel model of `zetaAll` (`partial def`; every `let` substituted). The fuel bounds the nesting depth; exhaustion answers the subterm
unchanged (an OPEN divergence from the shipped `partial def`). The answer only feeds `machSlotKinds` / `machInits`, which return kinds
and numbers, never an expression of the result. -/
def zetaAllN : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | k + 1, .letE _ _ v b _ => zetaAllN k (inst1M b v 0)
  | k + 1, .app f a => .app (zetaAllN k f) (zetaAllN k a)
  | _ + 1, e => e

def zetaAllFuel : Nat := 1000000

def zetaAllM (e : Lean.Expr) : Lean.Expr := zetaAllN zetaAllFuel e

/-! ## the operation record -/

structure ExtOps where
  lift : Lean.Expr → Nat → Nat → Lean.Expr
  lower : Lean.Expr → Nat → Nat → Lean.Expr
  inst1 : Lean.Expr → Lean.Expr → Lean.Expr
  beta : Lean.Expr → Lean.Expr → Lean.Expr
  eqv : Lean.Expr → Lean.Expr → Bool
  rootFloat : Lean.Expr → Lean.Expr
  zeroLit : Lean.Expr → Lean.Expr
  zetaAll : Lean.Expr → Lean.Expr

/-- The shipped operations (extern / `partial def`). -/
def shippedOps : ExtOps where
  lift e s d := e.liftLooseBVars s d
  lower e s d := e.lowerLooseBVars s d
  inst1 b a := b.instantiate1 a
  beta f a := f.beta #[a]
  eqv a b := a == b
  rootFloat := Sparkle.Compiler.MachRawSurface.rootFloat
  zeroLit := Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue?
  zetaAll := Sparkle.Compiler.MachRawSurface.zetaAll

/-- The kernel-visible models. -/
def modelOps : ExtOps where
  lift := liftM
  lower := lowerM
  inst1 b a := inst1M b a 0
  beta := betaM
  eqv := eqvX
  rootFloat := rootFloatM
  zeroLit := zeroLitM
  zetaAll := zetaAllM

/-- What the proofs use about the operations (the `LetOk` ranges); a HYPOTHESIS for an arbitrary `O`, PROVED for `modelOps`. -/
structure OpsOk (O : ExtOps) : Prop where
  lift : ∀ e s d, LetOk 0 e = true → LetOk 0 (O.lift e s d) = true
  lower : ∀ e s d, LetOk 0 e = true → LetOk 0 (O.lower e s d) = true
  inst1 : ∀ n b a, LetOk n b = true → LetOk n a = true → LetOk n (O.inst1 b a) = true
  beta : ∀ f a, LetOk 0 f = true → LetOk 0 a = true → LetOk 0 (O.beta f a) = true
  eqv : ∀ a b, O.eqv a b = true → LetOk 0 b = true → LetOk 0 a = true
  rootFloat : ∀ v, LetOk 0 v = true → LetOk 0 (O.rootFloat v) = true
  zeroLit : ∀ n e, LetOk n e = true → LetOk n (O.zeroLit e) = true

/-- **PROVED, no premise**: the models satisfy every range the reader proofs use. -/
theorem modelOps_ok : OpsOk modelOps where
  lift e s d he := by show LetOk 0 (liftM e s d) = true; rw [letOk_liftM]; exact he
  lower e s d he := by show LetOk 0 (lowerM e s d) = true; rw [letOk_lowerM]; exact he
  inst1 n b a hb ha := letOk_inst1M n ha b 0 hb
  beta f a hf ha := letOk_betaM 0 f a hf ha
  eqv a b h hb := letOk_eqvX 0 a b h hb
  rootFloat v hv := letOk_rootFloatM v hv
  zeroLit n e he := letOk_zeroLitM n e he

/-- `Expr.eqv` on the `ws` lists of the reader state (`List (Nat × Expr)`). -/
def eqvWs (O : ExtOps) : List (Nat × Lean.Expr) → List (Nat × Lean.Expr) → Bool
  | [], [] => true
  | (i, a) :: xs, (j, b) :: ys => i == j && O.eqv a b && eqvWs O xs ys
  | _, _ => false

theorem eqvWs_shipped : ∀ xs ys : List (Nat × Lean.Expr), eqvWs shippedOps xs ys = (xs == ys)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | (i, a) :: xs, (j, b) :: ys => by
    have ih := eqvWs_shipped xs ys
    have h1 : (((i, a) : Nat × Lean.Expr) == (j, b)) = (i == j && a == b) := rfl
    have h2 : shippedOps.eqv a b = (a == b) := rfl
    simp only [eqvWs, List.cons_beq_cons, ih, h1, h2, Bool.and_assoc]

/-! ## the reader phases that call the operations -/

def domGuardX {κ : Type} {R : κ → Type} {β : Type} (O : ExtOps) (o : Option Lean.Expr) (dom' : Lean.Expr)
    (k : FM κ R (Option β)) : FM κ R (Option β) :=
  match o with
  | some d0 => if !O.eqv d0 dom' then FM.pure none else k
  | none => k

theorem satp_domGuardX (O : ExtOps) {α : Type} {h : Hs} {P : α → Prop} {o : Option Lean.Expr} {dom' : Lean.Expr}
    {k : BM (Option α)} (hk : SatP h P k) : SatP h P (domGuardX O o dom' k) := by
  cases o with
  | none => exact hk
  | some d0 =>
    first
      | exact satp_ite satp_failO hk
      | (simp only [domGuardX]; exact satp_ite satp_failO hk)

/-- `machReserve` with `zetaAll` ↦ `O.zetaAll` and the domain test `!=` ↦ `!O.eqv`. -/
def machReserveX (O : ExtOps) (natOf : Lean.Expr → Option Nat) (dom' αs initsE body : Lean.Expr)
    (st : MachRead) : Option (Nat × MachRead) := do
  let kinds ← machSlotKinds (O.zetaAll αs)
  if kinds.isEmpty then none else
  let inits ← machInits natOf kinds (O.zetaAll initsE)
  match st.dom with
  | some d => if !O.eqv d dom' then none else pure ()
  | none => pure ()
  let base := st.kinds.size
  some (base, { st with
    kinds := st.kinds ++ kinds.toArray
    inits := st.inits ++ inits.toArray
    names := st.names ++ (machSlotNames st.runs.size body kinds base).toArray
    dom := some dom'
    runs := st.runs.push (base, kinds.length) })

def instResX (O : ExtOps) : Lean.Expr → List Lean.Expr → Option Lean.Expr
  | e, [] => some e
  | .forallE _ _ b _, a :: as => instResX O (O.inst1 b a) as
  | _, _ => none

def convStepX (O : ExtOps) (senv : StructEnv) : List MachVal → Nat → Lean.Expr → MachRead →
    BM (Option (Lean.Expr × MachRead))
  | env, d, .bvar j, st => FM.pure (convBvar env d j st)
  | env, d, e@(.app f a), st =>
    match regView? e.getAppFn e.getAppArgs with
    | some (dom, α, init, x) =>
      if d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty then failO else
      match st.bareRegs.find? (fun p => O.eqv p.1 e) with
      | some (_, k) => okO (machSlot k, st)
      | none =>
      optK (machSlotKind? α) fun kind =>
      optK (machInit? senv.natOf kind init) fun initN =>
      bindO (cConv env 0 dom st) fun (dom', st) =>
      domGuardX O st.dom dom'
        (let base := st.kinds.size
         let st := { st with
           kinds := st.kinds.push kind, inits := st.inits.push initN
           names := st.names.push (Name.mkSimple s!"reg{base}"), dom := some dom'
           bareRegs := st.bareRegs.push (e, base) }
         bindO (cConv env 0 x st) fun (x', st) =>
         okO (machSlot base, { st with ws := st.ws.push (base, x') }))
    | none =>
    match machLoopRead? env d (.app f a) with
    | some i => FM.pure (if i < st.kinds.size then some (machSlot i, st) else none)
    | none =>
    match machRunApp? (.app f a) with
    | some (dom, αs, initsE, body) =>
      if d != 0 then failO else cNested env dom αs initsE body st
    | none =>
    match machInstCall? senv (.app f a) with
    | some (c, kinds, res, args) =>
      if d != 0 then failO else cInst env c .ord kinds res args st
    | none =>
    match machInstCallS? senv (.app f a) with
    | some (c, kinds, ty, args) =>
      if d != 0 then failO else cInstS env c kinds ty args st
    | none =>
    match Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e)
        (.app f a) with
    | some (combo, aw, dw, dom, ops) =>
      if d != 0 then failO else
        bindO (cInst env (Sparkle.Compiler.MachMemory.memChildName combo aw dw)
            (.mem combo aw dw) [.domain, .bits aw, .bits dw, .bool, .bits aw] (.bits dw)
            (dom :: ops) st)
          fun (v, st) => okO (v, { st with instStruct := true })
    | none =>
    match machReadV env d (.app f a) with
    | some i => FM.pure (if i < st.kinds.size then some (machSlot i, st) else none)
    | none =>
      bindO (cConv env d f st) fun (f', st) =>
      bindO (cConv env d a st) fun (a', st) =>
      okO (Sparkle.Compiler.MachRawSurface.bundleIota (machProjIota senv.proj (.app f' a')), st)
  | env, d, .lam nm t b bi, st =>
    bindO (cConv env d t st) fun (t', st) =>
    bindO (cConv env (d + 1) b st) fun (b', st) =>
    okO (.lam nm t' b' bi, st)
  | env, d, .forallE nm t b bi, st =>
    bindO (cConv env d t st) fun (t', st) =>
    bindO (cConv env (d + 1) b st) fun (b', st) =>
    okO (.forallE nm t' b' bi, st)
  | env, d, .letE nm ty v b nd, st =>
    if d != 0 then failO else
    match O.rootFloat v with
    | .letE n2 t2 v2 w nd2 =>
      cConv env 0
        (.letE n2 t2 v2 (.letE nm (O.lift ty 0 1) w (O.lift b 1 1) nd) nd2) st
    | v =>
    if v.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
      bindO (cLoopRoot env v st) fun (mv, st) => cConv (mv :: env) 0 b st
    else
    match machTailV env 0 v with
    | some p => cConv (.regs p :: env) 0 b st
    | none =>
      match machHandleV env 0 v with
      | some i => cConv (.handle i :: env) 0 b st
      | none =>
        bindO (cConv env 0 v st) fun (v', st) =>
          let (x, lets) := machBindLet nm ty v' st.lets
          cConv (.val x :: env) 0 b { st with lets := lets }
  | _, _, .mdata .., _ => failO
  | _, _, .proj .., _ => failO
  | _, _, e, st => okO (e, st)
def nestedProbeX (O : ExtOps) (env : List MachVal) (dom' αs initsE body : Lean.Expr) (st : MachRead) :
    (Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr) →
      BM (Option (Lean.Expr × MachRead))
  | (base, d, a, ini, ws, v) =>
    if O.eqv d dom' && O.eqv a αs && O.eqv ini initsE then
      FM.bind (cChain (.regs base :: env) body st) fun r =>
      FM.pure (match r with
        | some (ws', v', st') => if eqvWs O ws' ws && O.eqv v' v then some (v, st') else none
        | none => none)
    else FM.pure none

/-- `machNested` (4016–4037). -/
def nestedStepX (O : ExtOps) (senv : StructEnv) (env : List MachVal) (dom αs initsE body : Lean.Expr)
    (st : MachRead) : BM (Option (Lean.Expr × MachRead)) :=
  if st.inInner then failO else
  bindO (cConv env 0 dom st) fun (dom', st) =>
  FM.bind (findSomeO (nestedProbeX O env dom' αs initsE body st) st.nested.toList) fun shared =>
  match shared with
  | some r => okO r
  | none =>
    optK (machReserveX O senv.natOf dom' αs initsE body st) fun (base, st) =>
    let outer := st.inInner
    bindO (cChain (.regs base :: env) body { st with inInner := true }) fun (ws, v, st) =>
    okO (v, { st with ws := st.ws ++ ws.toArray, inInner := outer,
                       nested := st.nested.push (base, dom', αs, initsE, ws, v) })
def instArgX (O : ExtOps) (env : List MachVal) (k : Nat) :
    List Nat × MachRead → MixedGateBinder × Lean.Expr → BM (Option (List Nat × MachRead))
  | (js, st), (kind, arg) =>
    bindO (cConv env 0 arg st) fun (v', st) =>
    FM.pure (match kind with
      | .domain =>
        match st.dom with
        | some d => if !O.eqv d v' then none else some (js, st)
        | none => some (js, { st with dom := some v' })
      | _ =>
        let (j, lets) := machLetIndex (Name.mkSimple s!"inst{k}_arg{js.length}") kind v' st.lets
        some (js ++ [j], { st with lets := lets }))

/-- `machInstance` (patched compiler: the call-entry origin `org`; the
dedup also compares the stored origin, the push also pushes `org`). -/
def instStepX (O : ExtOps) (env : List MachVal) (c : Name) (org : Sparkle.Compiler.MachInstOrigin.InstOrigin)
    (kinds : List MixedGateBinder)
    (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead) :
    BM (Option (Lean.Expr × MachRead)) :=
  optK (instEntry res st) fun st =>
  let k := st.insts.size
  bindO (foldO (instArgX O env k) (([] : List Nat), st) (kinds.zip args)) fun (js, st) =>
  FM.pure (match st.insts.zipIdx.findIdx? (fun (i, k') => i.1 == c && i.2.1 == js &&
      st.instOrigins[k']? == some org) with
    | some k' => some (machInstOut k', st)
    | none => some (machInstOut k, { st with insts := st.insts.push (c, js, res),
                                             instFields := st.instFields.push "out"
                                             instOrigins := st.instOrigins.push org }))

/-- `machInstanceS`'s first `foldlM` function (4091–4101). -/
def instSArgX (O : ExtOps) (env : List MachVal) :
    List Nat × MachRead → MixedGateBinder × Lean.Expr → BM (Option (List Nat × MachRead))
  | (js, st), (kind, arg) =>
    bindO (cConv env 0 arg st) fun (v', st) =>
    FM.pure (match kind with
      | .domain =>
        match st.dom with
        | some d => if !O.eqv d v' then none else some (js, st)
        | none => some (js, { st with dom := some v' })
      | _ =>
        let (j, lets) := machLetIndex (Name.mkSimple s!"inst{st.insts.size}_arg{js.length}")
          kind v' st.lets
        some (js ++ [j], { st with lets := lets }))
def instSStepX (O : ExtOps) (senv : StructEnv) (env : List MachVal) (c : Name) (kinds : List MixedGateBinder)
    (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead) :
    BM (Option (Lean.Expr × MachRead)) :=
  if st.inInner then failO else
  optK (instResX O ty args) fun resTy =>
  optK (machOuts? senv resTy) fun r =>
  match r with
  | (some ctor, fields) =>
    if fields.isEmpty || fields.any (fun f => f.2 == .domain) then failO else
    bindO (foldO (instSArgX O env) (([] : List Nat), st) (kinds.zip args)) fun (js, st) =>
    bindO (foldO (instSParam env) (([] : List Lean.Expr), st) resTy.getAppArgs.toList)
      fun (params, st) =>
    let lvls := resTy.getAppFn.constLevels!
    match st.insts.zipIdx.findIdx? (fun (i, k') => i.1 == c && i.2.1 == js &&
        st.instOrigins[k']? == some (.field 0)) with
    | some k0 =>
      okO (mkAppN (.const ctor lvls)
        (params.toArray ++ ((List.range fields.length).map fun i => machInstOut (k0 + i)).toArray),
        st)
    | none =>
      okO (mkAppN (.const ctor lvls)
        (params.toArray ++
          ((List.range fields.length).map fun i => machInstOut (st.insts.size + i)).toArray),
        { st with
          insts := st.insts ++ (fields.map fun f => (c, js, f.2)).toArray
          instFields := st.instFields ++ (fields.map (·.1)).toArray
          instStruct := true
          instOrigins := st.instOrigins ++
            ((List.range fields.length).map Sparkle.Compiler.MachInstOrigin.InstOrigin.field).toArray })
  | (none, _) => failO
def chainStepX (O : ExtOps) (senv : StructEnv) : List MachVal → Lean.Expr → MachRead →
    BM (Option (List (Nat × Lean.Expr) × Lean.Expr × MachRead))
  | env, .app (.app (.app (.app (.const ``Sparkle.Core.Circuit.pure' _) _) _) _) v, st =>
    bindO (cConv env 0 v st) fun (v', st) => okO ([], v', st)
  | env, .app (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Circuit.bind _) _) _) _) _)
      (.app (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Circuit.next _) _) _) _) _)
        h) rhs)) (.lam _ _ rest _), st =>
    -- the old text evaluates `machConv rhs` together with `machHandleV h`
    FM.bind (cConv env 0 rhs st) fun r =>
    match machHandleV env 0 h, r with
    | some i, some (rhs', st) =>
      if i < st.kinds.size then
        bindO (cChain (.unit :: env) rest st) fun (ws, v, st) => okO ((i, rhs') :: ws, v, st)
      else failO
    | _, _ => failO
  | env, .letE nm ty v b nd, st =>
    match O.rootFloat v with
    | .letE n2 t2 v2 w nd2 =>
      cChain env
        (.letE n2 t2 v2 (.letE nm (O.lift ty 0 1) w (O.lift b 1 1) nd) nd2) st
    | v =>
    if v.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
      bindO (cLoopRoot env v st) fun (mv, st) => cChain (mv :: env) b st
    else
    match machTailV env 0 v with
    | some p => cChain (.regs p :: env) b st
    | none =>
      match machHandleV env 0 v with
      | some i => cChain (.handle i :: env) b st
      | none =>
        bindO (cConv env 0 v st) fun (v', st) =>
          let (x, lets) := machBindLet nm ty v' st.lets
          cChain (.val x :: env) b { st with lets := lets }
  | _, _, _ => failO
def loopProbeX (O : ExtOps) (env : List MachVal) (body : Lean.Expr) (n : Nat) (st : MachRead) :
    Nat × Nat × List (Nat × Lean.Expr) → BM (Option (Nat × MachRead))
  | (b0, n0, ws0) =>
    if n0 != n then FM.pure none else
    FM.bind (cLoopBody b0 (.state b0 n :: env) body { st with ws := #[] }) fun r =>
    FM.pure (match r with
      | some st' => if eqvWs O st'.ws.toList ws0 then some (b0, { st' with ws := st.ws }) else none
      | none => none)

/-- `machLoopRoot` (4193–4230). -/
def loopRootStepX (O : ExtOps) (senv : StructEnv) (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    BM (Option (MachVal × MachRead)) :=
  match loopView? e with
  | some (dom, body) =>
    if st.inInner then failO else
    optK (machLoopRegs (machLetTail body)) fun regs =>
    if regs.any loopRegBad then failO else
    optK (regs.mapM loopRegKind) fun kinds =>
    optK ((kinds.zip regs).mapM (loopRegInit senv.natOf)) fun inits =>
    bindO (cConv env 0 dom st) fun (dom', st) =>
    domGuardX O st.dom dom'
      (let n := kinds.length
       FM.bind (findSomeO (loopProbeX O env body n st) st.loopWs.toList) fun shared =>
       match shared with
       | some (b0, st') => okO (.state b0 n, st')
       | none =>
         let base := st.kinds.size
         let depth := st.loopDepth
         let st := { st with
           kinds := st.kinds ++ kinds.toArray
           inits := st.inits ++ inits.toArray
           names := st.names ++ ((List.range n).map fun i =>
             Name.mkSimple s!"loop{st.loops.size}_r{i}").toArray
           dom := some dom'
           loops := st.loops.push (base, n)
           nestedLoops := if depth ≥ 1 then st.nestedLoops + 1 else st.nestedLoops
           loopDepth := depth + 1 }
         let before := st.ws.size
         bindO (cLoopBody base (.state base n :: env) body st) fun st =>
         okO (.state base n,
           { st with loopWs := st.loopWs.push (base, n, (st.ws.toList.drop before)),
                     loopDepth := depth }))
  | none => failO

/-- The block's body with the operations turned into `O`: one step of each of the seven functions. -/
def stepX (O : ExtOps) (senv : StructEnv) : (c : Call) → BM (RB c)
  | .conv env d e st => convStepX O senv env d e st
  | .nested env dom αs initsE body st => nestedStepX O senv env dom αs initsE body st
  | .inst env c org kinds res args st => instStepX O env c org kinds res args st
  | .instS env c kinds ty args st => instSStepX O senv env c kinds ty args st
  | .chain env e st => chainStepX O senv env e st
  | .loopBody base env e st => loopBodyStep base env e st
  | .loopRoot env e st => loopRootStepX O senv env e st

def readFX (O : ExtOps) (senv : StructEnv) (n : Nat) : Hs := fuel (stepX O senv) n

/-! ## compactness -/

theorem compact_domGuardX {κ : Type} {R : κ → Type} {β : Type} (O : ExtOps) (o : Option Lean.Expr) (dom' : Lean.Expr)
    {k : FM κ R (Option β)} (hk : Compact k) : Compact (domGuardX O o dom' k) := by
  unfold domGuardX
  repeat' (first | exact hk | exact compact_pure _ | split)

macro "compact_baseX" : tactic => `(tactic| first
  | with_reducible exact compact_cConv
  | with_reducible exact compact_cNested
  | with_reducible exact compact_cInst
  | with_reducible exact compact_cInstS
  | with_reducible exact compact_cChain
  | with_reducible exact compact_cLoopBody
  | with_reducible exact compact_cLoopRoot
  | with_reducible exact compact_okO _
  | with_reducible exact compact_failO
  | with_reducible exact compact_pure _
  | with_reducible exact compact_call _
  | with_reducible apply compact_bindO
  | with_reducible apply compact_bind
  | with_reducible apply compact_optK
  | with_reducible apply compact_domGuardX
  | with_reducible apply compact_foldO
  | with_reducible apply compact_findSomeO
  | intro _
  | split
  | dsimp only)

theorem compact_nestedProbeX (O : ExtOps) (env : List MachVal) (dom' αs initsE body : Lean.Expr)
    (st : MachRead) (p : Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr) :
    Compact (nestedProbeX O env dom' αs initsE body st p) := by
  unfold nestedProbeX
  repeat' compact_baseX

theorem compact_instArgX (O : ExtOps) (env : List MachVal) (k : Nat) (s : List Nat × MachRead)
    (a : MixedGateBinder × Lean.Expr) : Compact (instArgX O env k s a) := by
  unfold instArgX
  repeat' compact_baseX

theorem compact_instSArgX (O : ExtOps) (env : List MachVal) (s : List Nat × MachRead)
    (a : MixedGateBinder × Lean.Expr) : Compact (instSArgX O env s a) := by
  unfold instSArgX
  repeat' compact_baseX

theorem compact_loopProbeX (O : ExtOps) (env : List MachVal) (body : Lean.Expr) (n : Nat) (st : MachRead)
    (p : Nat × Nat × List (Nat × Lean.Expr)) : Compact (loopProbeX O env body n st p) := by
  unfold loopProbeX
  repeat' compact_baseX

macro "compact_allX" : tactic => `(tactic| repeat' (first
  | with_reducible exact compact_nestedProbeX _ _ _ _ _ _ _ _
  | with_reducible exact compact_instArgX _ _ _ _ _
  | with_reducible exact compact_instSArgX _ _ _ _
  | with_reducible exact compact_instSParam _ _ _
  | with_reducible exact compact_loopNext _ _ _ _
  | with_reducible exact compact_loopProbeX _ _ _ _ _ _
  | compact_baseX))

set_option maxHeartbeats 1000000 in
theorem compact_convStepX (O : ExtOps) (senv : StructEnv) (env : List MachVal) (d : Nat) (e : Lean.Expr)
    (st : MachRead) : Compact (convStepX O senv env d e st) := by
  unfold convStepX
  compact_allX

theorem compact_nestedStepX (O : ExtOps) (senv : StructEnv) (env : List MachVal)
    (dom αs initsE body : Lean.Expr) (st : MachRead) :
    Compact (nestedStepX O senv env dom αs initsE body st) := by
  unfold nestedStepX
  compact_allX

theorem compact_instStepX (O : ExtOps) (env : List MachVal) (c : Name)
    (org : Sparkle.Compiler.MachInstOrigin.InstOrigin) (kinds : List MixedGateBinder)
    (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead) :
    Compact (instStepX O env c org kinds res args st) := by
  unfold instStepX
  compact_allX

theorem compact_instSStepX (O : ExtOps) (senv : StructEnv) (env : List MachVal) (c : Name)
    (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead) :
    Compact (instSStepX O senv env c kinds ty args st) := by
  unfold instSStepX
  compact_allX

set_option maxHeartbeats 1000000 in
theorem compact_chainStepX (O : ExtOps) (senv : StructEnv) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) : Compact (chainStepX O senv env e st) := by
  unfold chainStepX
  compact_allX

set_option maxHeartbeats 1000000 in
theorem compact_loopRootStepX (O : ExtOps) (senv : StructEnv) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) : Compact (loopRootStepX O senv env e st) := by
  unfold loopRootStepX
  compact_allX

theorem compact_stepX (O : ExtOps) (senv : StructEnv) : ∀ c : Call, Compact (stepX O senv c) := by
  intro c
  cases c with
  | conv env d e st => exact compact_convStepX O senv env d e st
  | nested env dom αs initsE body st => exact compact_nestedStepX O senv env dom αs initsE body st
  | inst env c org kinds res args st => exact compact_instStepX O env c org kinds res args st
  | instS env c kinds ty args st => exact compact_instSStepX O senv env c kinds ty args st
  | chain env e st => exact compact_chainStepX O senv env e st
  | loopBody base env e st => exact compact_loopBodyStep base env e st
  | loopRoot env e st => exact compact_loopRootStepX O senv env e st

/-! ## the executable block with the operations `O` -/

/-- Kernel-visible block: `partial_fixpoint` of `stepX O senv`. -/
def execBlockX (O : ExtOps) (senv : StructEnv) (c : Call) : Option (RB c) :=
  (stepX O senv c).run (execBlockX O senv)
partial_fixpoint monotonicity by
  intro h₁ h₂ hle c
  exact Fn_mono (stepX O senv) h₁ h₂ hle c

theorem execBlockX_eq_lfp (O : ExtOps) (senv : StructEnv) : execBlockX O senv = lfp (stepX O senv) := by
  unfold Tools.Prototype.ReaderLfp.lfp
  with_unfolding_all rfl

theorem execBlockX_iff (O : ExtOps) (senv : StructEnv) {c : Call} {r : RB c} :
    execBlockX O senv c = some r ↔ ∃ n, readFX O senv n c = some r := by
  rw [execBlockX_eq_lfp]
  exact lfp_iff_fuel (compact_stepX O senv)

/-! ## `machReserveX` (the slot reservation of a nested machine) -/

/-- `machReserveX`, written with `Option.bind` and `if` only (the text of `machReserveSpec`). -/
def machReserveSpecX (O : ExtOps) (natOf : Lean.Expr → Option Nat) (dom' αs initsE body : Lean.Expr)
    (st : MachRead) : Option (Nat × MachRead) :=
  (machSlotKinds (O.zetaAll αs)).bind fun kinds =>
    if kinds.isEmpty then none else
    (machInits natOf kinds (O.zetaAll initsE)).bind fun inits =>
      if st.dom.any (fun d => !O.eqv d dom') then none else
      some (st.kinds.size, reserved st dom' body kinds inits)

theorem machReserveX_eq_spec (O : ExtOps) (natOf : Lean.Expr → Option Nat) (dom' αs initsE body : Lean.Expr)
    (st : MachRead) :
    machReserveX O natOf dom' αs initsE body st = machReserveSpecX O natOf dom' αs initsE body st := by
  unfold machReserveX machReserveSpecX
  cases machSlotKinds (O.zetaAll αs) with
  | none => first | rfl | simp
  | some kinds =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    by_cases hc : kinds.isEmpty = true
    · first
        | (simp only [if_pos hc]; done)
        | (simp [hc]; done)
    · simp only [if_neg hc]
      cases machInits natOf kinds (O.zetaAll initsE) with
      | none => first | rfl | simp
      | some inits =>
        cases st.dom with
        | none =>
          first
            | rfl
            | (simp [reserved]; done)
        | some d0 =>
          by_cases hd : (!O.eqv d0 dom') = true
          · first
              | (simp only [Option.bind_some, Option.bind_none, Option.any_some, if_pos hd]; done)
              | (simp [hd, reserved]; done)
              | rfl
          · first
              | (simp only [Option.bind_some, Option.any_some, if_neg hd]; rfl)
              | (simp only [Option.bind_some, Option.any_some, if_neg hd]; done)
              | (simp [hd, reserved]; done)
              | rfl

/-- **What `machReserveX` returns**: the state `reserved st dom' body kinds inits`, for kinds and reset values it read, and the
domain guard it passed (`O.eqv d dom'` for the stored domain `d`). -/
theorem machReserveX_some {O : ExtOps} {natOf : Lean.Expr → Option Nat} {dom' αs initsE body : Lean.Expr}
    {st : MachRead} {base : Nat} {st' : MachRead}
    (hr : machReserveX O natOf dom' αs initsE body st = some (base, st')) :
    ∃ (kinds : List MixedGateBinder) (inits : List Nat),
      machSlotKinds (O.zetaAll αs) = some kinds ∧
      machInits natOf kinds (O.zetaAll initsE) = some inits ∧
      base = st.kinds.size ∧ st' = reserved st dom' body kinds inits ∧
      ∀ d, st.dom = some d → O.eqv d dom' = true := by
  rw [machReserveX_eq_spec] at hr
  unfold machReserveSpecX at hr
  obtain ⟨kinds, hks, hr⟩ := Option.bind_eq_some_iff.mp hr
  replace hr := ite_none_some hr
  obtain ⟨inits, hin, hr⟩ := Option.bind_eq_some_iff.mp hr
  by_cases hb : (st.dom.any fun d => !O.eqv d dom') = true
  · rw [if_pos hb] at hr
    cases hr
  · rw [if_neg hb] at hr
    have hp := Prod.mk.inj (Option.some.inj hr)
    refine ⟨kinds, inits, hks, hin, hp.1.symm, hp.2.symm, ?_⟩
    intro d hd
    refine Classical.byContradiction fun hne => ?_
    apply hb
    rw [hd, Option.any_some]
    cases hh : O.eqv d dom'
    · rfl
    · exact absurd hh hne

/-! ## the shipped operations give the shipped phases -/

theorem domGuardX_shipped {κ : Type} {R : κ → Type} {β : Type} (o : Option Lean.Expr) (dom' : Lean.Expr)
    (k : FM κ R (Option β)) : domGuardX shippedOps o dom' k = domGuard o dom' k := by
  cases o <;> rfl

theorem instResX_shipped : ∀ (e : Lean.Expr) (as : List Lean.Expr), instResX shippedOps e as = instRes e as
  | e, [] => rfl
  | .forallE _ _ b _, a :: as => by
    simp only [instResX, instRes]; exact instResX_shipped _ as
  | .bvar _, _ :: _ => rfl
  | .fvar _, _ :: _ => rfl
  | .mvar _, _ :: _ => rfl
  | .sort _, _ :: _ => rfl
  | .const _ _, _ :: _ => rfl
  | .app _ _, _ :: _ => rfl
  | .lam _ _ _ _, _ :: _ => rfl
  | .letE _ _ _ _ _, _ :: _ => rfl
  | .lit _, _ :: _ => rfl
  | .mdata _ _, _ :: _ => rfl
  | .proj _ _ _, _ :: _ => rfl


/-! ## the raw-surface node rewriter and the normaliser with the operations `O` -/

/-- The `let rec build` of `rawNode`, lifted to a top-level function with the operations `O`. -/
def rawBuildX (O : ExtOps) (k : Nat) (regs body : Lean.Expr) (tys : List Lean.Expr) :
    List (Nat × Name × Lean.Expr) → Option Lean.Expr
  | [] => some body
  | (j, nm, t) :: rest => do
    -- under j earlier lets
    let v ← projChain (O.lift regs 0 j) (tys.map (fun t => O.lift t 0 j)) j (j + 1 == k)
    let r ← rawBuildX O k regs body tys rest
    some (.letE nm t v r false)

/-- One raw-surface node, rewritten (the text of `MachRawSurface.rawNode`, its `lift/lower/beta` calls turned into `O`). -/
def rawNodeX (O : ExtOps) (prodMatch : Name → Option Nat) (e : Lean.Expr) : Option Lean.Expr :=
  match e.getAppFn, e.getAppArgs with
  -- `Circuit.read r` → `r.fst`
  | .const ``Sparkle.Core.Circuit.read _, #[dom, S, τ, W, r] =>
    some (mkApp3 (.const ``Prod.fst [.zero, .zero])
      (mkApp2 (.const ``Sparkle.Core.Signal.Signal [.zero]) dom τ)
      (mkApp4 (.const ``Sparkle.Core.Circuit.Slot []) dom S W τ) r)
  -- `bind m k` at the Circuit monad → `Circuit.bind m k`
  | .const ``Bind.bind _, #[m, inst, α, β, x, k] =>
    match m.getAppFn, m.getAppArgs, inst.getAppFn with
    | .const ``Sparkle.Core.Circuit _, #[dom, S], .const ``Monad.toBind _ =>
      some (mkAppN (.const ``Sparkle.Core.Circuit.bind []) #[dom, S, α, β, x, k])
    | _, _, _ => none
  -- `pure a` at the Circuit monad → `Circuit.pure' a`
  | .const ``Pure.pure _, #[m, inst, α, a] =>
    match m.getAppFn, m.getAppArgs, inst.getAppFn with
    | .const ``Sparkle.Core.Circuit _, #[dom, S], .const ``Applicative.toPure _ =>
      some (mkAppN (.const ``Sparkle.Core.Circuit.pure' []) #[dom, S, α, a])
    | _, _, _ => none
  -- `(as.forM f) >>= k` over a literal list → `f a₁; …; f aₙ; k ()`, the
  -- binds nested to the right (the reader monad's laws hold by evaluation)
  | .const ``Sparkle.Core.Circuit.bind _, #[dom, S, _, β, x, k] =>
    match x.getAppFn, x.getAppArgs with
    | .const ``List.forM _, #[_, _, _, as, f] =>
      match listElems as with
      | none => none
      | some xs =>
        let punit := Lean.Expr.const ``PUnit [.succ .zero]
        let n := xs.length
        -- the `i`-th statement sits under `i` new binders, the continuation under `n`
        let tail := O.beta (O.lift k 0 n) (.const ``PUnit.unit [.succ .zero])
        let stmts := xs.zipIdx.map fun (a, i) =>
          (O.beta (O.lift f 0 i) (O.lift a 0 i), i)
        some (stmts.foldr (fun (st, i) rest => mkAppN (.const ``Sparkle.Core.Circuit.bind [])
          #[O.lift dom 0 i, O.lift S 0 i, punit, O.lift β 0 i, st,
            .lam `_ punit rest .default]) tail)
    | _, _ => none
  -- `as.forM f` over a literal list → `f a₁; …; f aₙ; pure ()` (its
  -- definition unfolded; the binds become `Circuit.bind` above)
  | .const ``List.forM _, #[m, inst, _, as, f] =>
    match listElems as with
    | none => none
    | some xs =>
      let punit := Lean.Expr.const ``PUnit [.succ .zero]
      let done := mkAppN (.const ``Pure.pure [.zero, .zero])
        #[m, mkApp2 (.const ``Applicative.toPure [.zero, .zero]) m
          (mkApp2 (.const ``Monad.toApplicative [.zero, .zero]) m inst), punit,
          .const ``PUnit.unit [.succ .zero]]
      let n := xs.length
      let stmts := xs.zipIdx.map fun (a, i) =>
        (O.beta (O.lift f 0 i) (O.lift a 0 i), i)
      some (stmts.foldr (fun (st, i) rest => mkAppN (.const ``Bind.bind [.zero, .zero])
        #[O.lift m 0 i, mkApp2 (.const ``Monad.toBind [.zero, .zero]) (O.lift m 0 i)
            (O.lift inst 0 i), punit, punit, st, .lam `_ punit rest .default])
        (O.lift done 0 n))
  -- a pair-destructuring matcher → the `let`s of the projections
  | .const n _, args =>
    match prodMatch n with
    | some k =>
      if args.size != 3 then none else
      let regs := args[1]!
      let alt := args[2]!
      -- the alternative's k binders: names and types (the shipped, operation-free `rawNode.peel`)
      match Sparkle.Compiler.MachRawSurface.rawNode.peel k alt [] with
      | none => none
      | some (binders, body) =>
        -- the component types at the alternative's context: binder i sits
        -- under i earlier binders (non-dependent, so lowered back)
        let tys := (binders.zipIdx).map fun ((_, t), i) => O.lower t i i
        -- build `let v₁ := …; …; let vₖ := …; body`
        rawBuildX O k regs body tys ((List.range k).zip binders |>.map fun (j, (nm, t)) => (j, nm, t))
    | none => none
  | _, _ => none

/-- `normStepP` with `rawNode` ↦ `rawNodeX O` and `instantiate1` ↦ `O.inst1`. -/
def normStepX (O : ExtOps) (node : StructEnv → Lean.Expr → Lean.Expr) (senv : StructEnv) : Lean.Expr → NM Lean.Expr
  | e@(.app f a) =>
    match ashrView? e.getAppFn e.getAppArgs with
    | some (dom, nE, x, y) =>
      match canonicalNatLitValue? nE with
      | some n =>
        if n == 0 then FM.pure e else
        FM.bind (FM.call x) fun x' => FM.bind (FM.call y) fun y' =>
        FM.pure (Sparkle.Compiler.MachSignOps.ashrE inlNatLit
          (fun m a b => machSigBin m ((machSigInst m).getD .anonymous) dom n a b)
          dom n x' y')
      | none => FM.pure e
    | none =>
    match rawNodeX O senv.prodMatch e with
    | some e' => FM.call e'
    | none =>
      FM.bind (FM.call f) fun f' => FM.bind (FM.call a) fun a' =>
      FM.pure (node senv (.app f' a'))
  | .lam n t b bi => FM.bind (FM.call b) fun b' => FM.pure (.lam n t b' bi)
  | .letE n t v b nd =>
    if t.isConstOf ``Nat then FM.call (O.inst1 b v)
    else if (machBits? t).isSome && !v.hasLooseBVars then FM.call (O.inst1 b v)
    else FM.bind (FM.call v) fun v' => FM.bind (FM.call b) fun b' => FM.pure (.letE n t v' b' nd)
  | e => FM.pure e

def machNormFX (O : ExtOps) (node : StructEnv → Lean.Expr → Lean.Expr) (n : Nat) (senv : StructEnv) (e : Lean.Expr) :
    Option Lean.Expr :=
  @fuel Lean.Expr (fun _ => Lean.Expr) (normStepX O node senv) n e

set_option maxHeartbeats 1000000 in
theorem compact_normStepX (O : ExtOps) (node : StructEnv → Lean.Expr → Lean.Expr) (senv : StructEnv) (e : Lean.Expr) :
    Compact (normStepX O node senv e) := by
  unfold normStepX
  repeat' compact_base

/-- Kernel-visible normaliser with the operations `O` and the node rewriter `node`. -/
def execNormX (O : ExtOps) (node : StructEnv → Lean.Expr → Lean.Expr) (senv : StructEnv) (e : Lean.Expr) :
    Option Lean.Expr :=
  (normStepX O node senv e).run (execNormX O node senv)
partial_fixpoint monotonicity by
  intro h₁ h₂ hle c
  exact Fn_mono (κ := Lean.Expr) (R := fun _ => Lean.Expr) (normStepX O node senv) h₁ h₂ hle c

theorem execNormX_eq_lfp (O : ExtOps) (node : StructEnv → Lean.Expr → Lean.Expr) (senv : StructEnv) :
    execNormX O node senv = lfp (κ := Lean.Expr) (R := fun _ => Lean.Expr) (normStepX O node senv) := by
  unfold Tools.Prototype.ReaderLfp.lfp
  with_unfolding_all rfl

theorem execNormX_iff (O : ExtOps) (node : StructEnv → Lean.Expr → Lean.Expr) (senv : StructEnv) {e r : Lean.Expr} :
    execNormX O node senv e = some r ↔ ∃ n, machNormFX O node n senv e = some r := by
  rw [execNormX_eq_lfp]
  exact lfp_iff_fuel (κ := Lean.Expr) (R := fun _ => Lean.Expr) (compact_normStepX O node senv)

/-! ## the shipped operations give the shipped phases (evidence by `rfl` / short proofs) -/

theorem nestedProbeX_shipped (env : List MachVal) (dom' αs initsE body : Lean.Expr) (st : MachRead) :
    nestedProbeX shippedOps env dom' αs initsE body st = nestedProbe env dom' αs initsE body st := by
  funext p
  obtain ⟨base, d, a, ini, ws, v⟩ := p
  unfold nestedProbeX nestedProbe
  simp only [eqvWs_shipped]
  rfl

theorem loopProbeX_shipped (env : List MachVal) (body : Lean.Expr) (n : Nat) (st : MachRead) :
    loopProbeX shippedOps env body n st = loopProbe env body n st := by
  funext p
  obtain ⟨b0, n0, ws0⟩ := p
  unfold loopProbeX loopProbe
  simp only [eqvWs_shipped]
  rfl

theorem instArgX_shipped (env : List MachVal) (k : Nat) :
    instArgX shippedOps env k = instArg env k := by
  funext s a
  rfl

theorem instSArgX_shipped (env : List MachVal) :
    instSArgX shippedOps env = instSArg env := by
  funext s a
  rfl

theorem convStepX_shipped (senv : StructEnv) : convStepX shippedOps senv = convStep senv := by
  funext env d e st
  cases e <;> rfl

theorem machReserveX_shipped : machReserveX shippedOps = machReserve := by
  funext natOf dom' αs initsE body st
  rfl

theorem nestedStepX_shipped (senv : StructEnv) : nestedStepX shippedOps senv = nestedStep senv := by
  funext env dom αs initsE body st
  unfold nestedStepX nestedStep
  simp only [nestedProbeX_shipped, machReserveX_shipped]
  rfl

theorem instStepX_shipped : instStepX shippedOps = instStep := by
  funext env c org kinds res args st
  unfold instStepX instStep
  simp only [instArgX_shipped]
  rfl

theorem instSStepX_shipped (senv : StructEnv) : instSStepX shippedOps senv = instSStep senv := by
  funext env c kinds ty args st
  unfold instSStepX instSStep
  have : ∀ ty args, instResX shippedOps ty args = instRes ty args := instResX_shipped
  simp only [instSArgX_shipped, this]
  rfl

theorem chainStepX_shipped (senv : StructEnv) : chainStepX shippedOps senv = chainStep senv := by
  funext env e st
  rfl

theorem loopRootStepX_shipped (senv : StructEnv) : loopRootStepX shippedOps senv = loopRootStep senv := by
  funext env e st
  unfold loopRootStepX loopRootStep
  simp only [loopProbeX_shipped, domGuardX_shipped]
  rfl

theorem stepX_shipped (senv : StructEnv) (c : Call) : stepX shippedOps senv c = step senv c := by
  cases c with
  | conv env d e st =>
    show convStepX shippedOps senv env d e st = convStep senv env d e st
    rw [convStepX_shipped]
  | nested env dom αs initsE body st =>
    show nestedStepX shippedOps senv env dom αs initsE body st = nestedStep senv env dom αs initsE body st
    rw [nestedStepX_shipped]
  | inst env c org kinds res args st =>
    show instStepX shippedOps env c org kinds res args st = instStep env c org kinds res args st
    rw [instStepX_shipped]
  | instS env c kinds ty args st =>
    show instSStepX shippedOps senv env c kinds ty args st = instSStep senv env c kinds ty args st
    rw [instSStepX_shipped]
  | chain env e st =>
    show chainStepX shippedOps senv env e st = chainStep senv env e st
    rw [chainStepX_shipped]
  | loopBody base env e st => rfl
  | loopRoot env e st =>
    show loopRootStepX shippedOps senv env e st = loopRootStep senv env e st
    rw [loopRootStepX_shipped]

theorem execBlockX_shipped (senv : StructEnv) : execBlockX shippedOps senv = execBlock senv := by
  rw [execBlockX_eq_lfp, execBlock_eq_lfpBlock]
  have : stepX shippedOps senv = step senv := funext (stepX_shipped senv)
  rw [this]
  rfl


/-! ## the wrapper with the operations `O` -/

/-- `shapeMid` with `rootFloat` ↦ `O.rootFloat` and `zeroLit` ↦ `O.zeroLit`. -/
def shapeMidX (O : ExtOps) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : ShapeMid :=
  let e := machLoopAsLet (O.rootFloat (O.zeroLit (inlFoldNat en)))
  let (rootLets, sel, run?, root) := machRoot senv.proj e []
  let wrap? : Option (Lean.Expr × Array Lean.Expr) := match run?, p.ctor? with
    | none, some c =>
      if root.getAppFn.isConstOf c && p.outs.length == 1 then
        let args := root.getAppArgs
        match args.back? with
        | some r => if (machRunApp? r).isSome then some (root.getAppFn, args.pop) else none
        | none => none
      else none
    | _, _ => none
  let run? := match wrap? with
    | some _ => root.getAppArgs.back?
    | none => run?
  { rootLets := rootLets, sel := sel, root := root, wrap? := wrap?,
    run? := run?.bind machRunApp? }

theorem shapeMidX_shipped (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) :
    shapeMidX shippedOps senv p en = shapeMid senv p en := rfl

/-- The wrapper: `shapeW` with `shapeMid` ↦ `shapeMidX O`. -/
def shapeWX (O : ExtOps) (symbolicMode : Bool) (parameters : List (String × Nat)) (ci : ConstantInfo)
    (senv : StructEnv) (allowInsts : Bool) : WM (Option MachineShape) :=
  optK (shapePre symbolicMode parameters ci senv) fun p =>
  FM.bind (wNorm p.e) fun en =>
  let m := shapeMidX O senv p en
  bindO (shapeStart senv m) fun st =>
  bindO (foldO (shapeRootLet senv) (([] : List MachVal), st) m.rootLets) fun (env, st) =>
  bindO (shapeBody m env st) fun (st, v) =>
  FM.pure (shapePost allowInsts p m st v)

theorem shapeWX_shipped (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv) (ai : Bool) :
    shapeWX shippedOps sm ps ci senv ai = shapeW sm ps ci senv ai := rfl

/-- The call table of the model reader: the normaliser `execNormX O machNormNodeM`, the block `execBlockX O`. -/
def xtabX (O : ExtOps) (senv : StructEnv) : (c : WCall) → Option (WCall.Res c)
  | .norm e => execNormX O machNormNodeM senv e
  | .blk c => execBlockX O senv c

/-- **The reader with the operations `O`** (the node rewriter is the LC19 model `machNormNodeM`). For `O := modelOps` this is the
MODEL reader `machineShapeXM`: its phases CALL the models, not the shipped extern / partial operations. -/
def machineShapeX (O : ExtOps) (symbolicMode : Bool) (parameters : List (String × Nat)) (ci : Lean.ConstantInfo)
    (senv : StructEnv) (allowInsts : Bool := true) : Option (Option MachineShape) :=
  (shapeWX O symbolicMode parameters ci senv allowInsts).run (xtabX O senv)

/-- The normaliser, shapeMid and reader of the MODEL operations (same argument lists as the NMI ones, so the conclusion check can
substitute them constant by constant). -/
def execNormXM (senv : StructEnv) (e : Lean.Expr) : Option Lean.Expr := execNormX modelOps machNormNodeM senv e
def shapeMidXM (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : ShapeMid := shapeMidX modelOps senv p en
def machineShapeXM (symbolicMode : Bool) (parameters : List (String × Nat)) (ci : Lean.ConstantInfo)
    (senv : StructEnv) (allowInsts : Bool := true) : Option (Option MachineShape) :=
  machineShapeX modelOps symbolicMode parameters ci senv allowInsts

end Tools.Prototype.ExtReader

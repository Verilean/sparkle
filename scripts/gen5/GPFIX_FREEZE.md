# GPFIX: FG のパッケージ carrier `GP` を `genP` に固定し、D.T-1 / C.SM-7 / D.D-3 を除く

Issue: `sparkle-ledger-gpfix`（親 `sparkle-ledger-shorten`）。ユーザー判断: 2026-11-05 案 A（`scripts/gen5/GP_FIX_DECISION.md`、par/fg-ledger-sync）。
base: 67d8e441（par/gpfix = kjob/rt187 04db3763（AC9KIT）に par/rk1 113cd51b（FGLedgerPremisesStmtR）を局所 merge。衝突は lakefile.lean だけで、両側の lean_lib を残した）。
実装: `Tools/ShippingGenFGLedgerPremisesG.lean`。検査: `Tests/Gen5/GPFixCheck.lean`。台帳（受入済み）: FG 83 / T1 57。この文書は台帳を変えない。

## 0. 減算表

| 項目 | 内容 |
|---|---|
| 消える台帳 ID | D.T-1（`h_D_T1 : … → GenExtAtCall p q k hk`、リーフ TY-I）、D.D-3（carrier `GP`、リーフ UN-K）、C.SM-7（`genExtAtCall_of_genSem` の `hord`、PA 非リーフ） |
| 消える条件 | `FGLedgerPremisesStmtG`（`GP := genGP lvl hs genData₀` に固定し、`h_D_T1` の束縛変数を除いた文）と `fgLedgerPremisesStmtG_of_R : FGLedgerPremisesStmtR → FGLedgerPremisesStmtG` の受理（reviewer: 前提の除去と数え方）、exact-head build exit 0 |
| 入る束縛変数 | `lvl : Lean.Expr → Nat`、`initsOf`、`genData₀ : (env : Environment) → (E : ConstantInfo) → Option (GenData (dataOfAt lvl) E (structEnv env))`（非 Prop の値）と `hs : DataOfSound (dataOfAt lvl) initsOf`（C.SM-1、既存の行。AC9KIT の `hs` と同じ型） |
| 残る条件 | `FGLedgerPremisesStmtR` の他の束縛変数（C.EN-4、C.RK-6、C.CV-4、`h_A_P06`、`h_D_T4`、carrier `ReflectsAll` `Post` `CV`、`L`）。O2（`∃ p, GP env declName = some p`）は結論のままで、`genP` の被覆（C.AC-4 / C.SM-1 の被覆半分）は FG の証明の仕事として残る |
| 台帳への効果 | リーフ −2（D.T-1、D.D-3）、非リーフ −1（C.SM-7）で FG 83 → 80。C.DG-1（`P = genP env₀`）が定義で成り立つ分は reviewer の判断（この単位では数えない） |
| 新しい TRUSTED / law / コンパイラ変更 | なし |

## 1. 根拠（証明の道）

* `genKit lvl hs env g₀` = AC9KIT の `accKit%` と同じ `mkKit (dataOfAt lvl) (GenData …) (·.d) g₀ ordCallees₀ (GenData.genSem hs) …`（env を引数にした）。
* `hF` = `factsOf_genS_assembled'' hs (genData₀ env)`（`Tools/ShippingGen5AccGenDataKit.lean:41`）。`genGP lvl hs genData₀ env := genP (genKit …) hF`。
* `h_D_T1` の証明: `genP_generated`（`Tools/ShippingGen5AccGenP.lean:96`）が `genP` の各 `p` に `∃ E g, p.toSem = K.genSem (semOf (genP K hF)) c g` を与える。`K.genSem` は定義で `GenData.genSem hs`、それは定義で `genSemI Q X (g.toIn hs)`（`Tools/ShippingGen5SemGenData.lean:40-44`）。`genExtAtCall_of_genSem`（`Tools/ShippingGen5SemExtPkg.lean:17`）の `hq` と `hord` は `h_D_T1` の前件そのもの（`originOf d k := d.shape.instOrigins.getD k .ord`、定義）。

## 2. 凍結する文

```lean
noncomputable def genGP {ι : Type} {dom : ι → DomainConfig} (lvl : Lean.Expr → Nat)
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound (dataOfAt lvl) initsOf)
    (genData₀ : (env : Environment) → (E : ConstantInfo) → Option (GenData (dataOfAt lvl) E (structEnv env))) :
    Environment → Pkgs ι dom

theorem hDT1_of_genGP … : ∀ env c, ∀ p, genGP lvl hs genData₀ env c = some p → ∀ k hk,
    (p.d.shape.instOrigins.getD k .ord).child? = none →
    ∀ q, genGP lvl hs genData₀ env (p.d.shape.insts[k]).1 = some q → GenExtAtCall p q k hk

-- FGLedgerPremisesStmtG: FGLedgerPremisesStmtR の字面で、(GP : Environment → Pkgs ι dom) の行を
--   (lvl) {initsOf} (hs) (genData₀) に替え、本体の GP を genGP lvl hs genData₀ に置き換え、h_D_T1 の前件を除いたもの

theorem fgLedgerPremisesStmtG_of_R : FGLedgerPremisesStmtR → FGLedgerPremisesStmtG
```

## 3. 検査（`Tests/Gen5/GPFixCheck.lean`）

* 構造比較（Expr の `==`、DD7Check rev2 と同じ一つの telescope の walk）: `FGLedgerPremisesStmtR` と `FGLedgerPremisesStmtG` の外側の束縛変数で、消えたのが `GP` だけ、入ったのが `lvl initsOf hs genData₀` だけ。内側の前件で、`h_D_T1` に当たる 1 個が消え、他（`h_A_P06`、`h_D_T4`）は `GP := genGP …` の代入の下で `==`。
* `hs` の型が `accServed0_of_cover_gatesK` の `hs` の型と `==`（C.SM-1 と同じ行）。
* 対照: 例外なしの比較は不合格。axioms は標準の 3 つだけ。

## 4. 主張しないこと

* FG の証明、O2 の被覆、C.DG-1 の除去、`genData₀` の具体的な構成。

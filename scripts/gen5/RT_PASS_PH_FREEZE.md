# RT pass_ph freeze rev2（`sparkle-rt-pass-ph`）: 不変量を束縛の下の `BvarLt L` に一般化する

対象 Issue: `sparkle-rt-pass-ph`（子 `-betaall` の rt112 の指摘を受けた改訂）。base: `par/rt-pass-ph-skel` 0533a8c7。rev1: `96cc7386`（reviewer 承認は文書・型の提案まで）。
この文書は **仮定が変わる（強くなる）** ので reviewer の承認が要る（§3、§6）。承認が出るまで Lean 実装には進まない。Lean のソースは編集していない（scratch のみ、§4。scratch は `scripts/gen5/RT_PASS_PH_REV2_SCRATCH{1,2}.lean.txt` に **コンパイル対象外のテキスト** として残した）。

結果の位置づけ: 条件付き・中間結果。`pass_ph` はまだ証明していない。示したのは (i) 一般化した型が `set_option autoImplicit false` の下で elaborate すること、(ii) `beta_goodL` / `headBetaM_goodL` / `beta_target`（rev1 で未証明だった）が **sorry なしで証明できたこと**（axioms: propext / Classical.choice / Quot.sound）、だけ。ほかの補題は型のみ（本体 `sorry`、scratch）。

## 0. 要約

* 問題の確認: `G e := NoPh e ∧ BvarLt 0 e` は束縛の下で弱すぎる。**betaAll だけでなく、passM/passStep、reduceHead（`letE` の本体）も束縛の下へ再帰する**（§1）。したがって L の一般化は BetaAll に限らず Iota・Pass の文にも及ぶ。
* 解決の形: 補題を `∀ L, NoPh e → BvarLt L e → … BvarLt L r` に一般化（`GL L e`）。`PassPh'` / `pass_ph` / `passWith_ph` の **最終の文は L = 0 のまま**でよい（§2.3）。
* 仮定: `HeadBetaAgrees0` では足りない（L > 0 の入力に使う箇所がある）。`headBeta` と `headBetaSpec` の一致を loose bvar つきで **論理の中で証明する経路はこの調査では見つからなかった**（§3 (b)）。よって新しい仮定の形 `HeadBetaAgreesL`（`∀ L e, NoPh e → BvarLt L e → e.headBeta = headBetaSpec e`）が要る。`HeadBetaAgreesL → HeadBetaAgrees0` は 1 行の定理。台帳の扱いは 2 案（§3、§6、reviewer の判断）。
* `BetaNonTargetAgrees`（rev1 の T1 +1 候補）は **L 版が要らない**（文が `NoPh` / `BvarLt` を含まず、もともと L に依らない、§3 (c)）。
* rev1 の `beta_target` は **証明できた**（scratch）。`BetaNonTargetAgrees` の側（非ラムダ頭）だけが仮定として残る。
* 台帳: FG 94 / T1 54（今回 FG −0 +0 / T1 −0 +0）。条件付き台帳は §6。

## 1. (1) pass の各部が束縛の下へ再帰するか（`Sparkle/Compiler/MachRecUnfold.lean`）

「束縛の下へ再帰」= 入力の `BvarLt L` から部分項に `BvarLt (L+1)` しか出ない再帰。「L 一般化」= その部分が呼ぶ補題・自身の文を `∀ L` にする必要。

| 部分 | 行 | 束縛の下へ再帰 | L 一般化 | 理由 |
|---|---|---|---|---|
| `headBetaM` | 98–105 | しない（`f.beta args` は引数代入。再帰は結果への `headBetaM`） | **要る** | `betaAll`（L ≥ 0 の任意の位置）・`iota`・`reduceHead` から L > 0 の `e` で呼ばれる |
| `iota` | 109–158 | しない | **要る** | `reduceMatcher?` / `unfoldCall?` / `reduceHead` 経由で L > 0 の項に呼ばれる。結果は `mkAppN (閉じた rhs / d.value) (L の引数)` |
| `ctorApp?` | 34–51 | しない | **要る**（`fields` は `e` の引数） | 閉じた `natLitE` は L に依らない |
| `reduceMatcher?` | 162–172 | しない | **要る** | `iota` を呼ぶ |
| `reduceHead` | 176–190 | **する**（183–185: `letE` の本体 `b` へ。`BvarLt (L+1)`） | **要る**（再帰そのものが L+1 を使う） | rev1 の見落とし |
| `betaAll` | 195–210 | **する**（207 `lam`、208 `letE` の本体） | **要る**（rt112 の指摘） | `headBetaM` も L > 0 で呼ぶ |
| `betaSpine` | 214–219 | しない（spine の各要素は L のまま） | **要る** | `betaAll` を呼ぶ |
| `unfoldCall?` | 225–233 | しない | **要る** | 入力は `passStep` の `e'`（L > 0 でありうる）。`v` は `DeclValuePh` + `ilp_ph` で **閉じている**（`G 0` → 任意の L へ単調） |
| `listLit?` | 245–267 | しない（253: `letE` の `b.instantiate1 v`、`BvarLt (L+1)` の `b` に `v : BvarLt L` を代入 → `BvarLt L`） | **要る**（`inst1Spec_bvarLt` を `m = m′ = L` で使う） | `evalNode?` が L > 0 の `e` で呼ぶ |
| `natVal?` / `boolVal?` | 274–300 | しない | 不要（戻りは `Nat` / `Bool`、式を返さない） | |
| `evalNode?` | 303–323 | しない | **要る** | 戻りは `a` / `b` / `xs.headD d`（引数）または `mkListLit α xs` |
| `passM` | 341–347 | しない（メモの出し入れ） | **要る**（メモの不変量の形、§2.2） | |
| `passStep` | 350–381 | **する**（369 `lam`、370–378 `letE` の本体 `b`、377 は `instantiate1 v′` で L） | **要る** | |
| `passSpine` | 384–392 | しない | **要る** | |
| `relevant` / `relevantClosure` | 397–431 | — | 不要（式を変えない） | |

L 一般化が **不要** なのは `natVal?` / `boolVal?` / `relevant*` だけ。`G` の `L = 0` で足りるのは最終の `pass_ph`（§2.3）。

## 2. (2) 一般化した補題の完全型

`GL L e := NoPh e = true ∧ BvarLt L e = true`。下の型はすべて scratch（`Tools.ScratchPassPhL`、`kjob lake build` exit 0、`set_option autoImplicit false`、本体は `sorry`）で elaborate 済み。`HeadBetaAgreesL` の定義と、証明まで通した 3 補題（`beta_goodL`、`headBetaM_goodL`、`beta_target`）は §4。

```lean
namespace Tools.PassPhL
open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern Sparkle.Compiler.MachRecUnfold
open Tools.PassPh (RecRulePhU BetaNonTargetAgrees)

def GL (L : Nat) (e : Lean.Expr) : Prop := NoPh e = true ∧ BvarLt L e = true

def HeadBetaAgreesL : Prop :=
  ∀ (L : Nat) (e : Lean.Expr), NoPh e = true → BvarLt L e = true → e.headBeta = headBetaSpec e

theorem headBetaAgreesL_zero : HeadBetaAgreesL → HeadBetaAgrees0 := fun h e hn hb => h 0 e hn hb

theorem betaAll_goodL (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel L : Nat) (e r : Lean.Expr), GL L e → betaAll fuel e = .ok r → GL L r
theorem betaSpine_goodL (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel L : Nat) (e h : Lean.Expr) (args : Array Lean.Expr), GL L e → betaSpine fuel e = .ok (h, args) →
      GL L h ∧ ∀ a ∈ args, GL L a
theorem ctorApp_goodL : ∀ (L : Nat) (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (e : Lean.Expr)
    (cv : Lean.ConstructorVal) (fs : Array Lean.Expr), GL L e →
    ctorApp? env natLit? e = some (cv, fs) → ∀ f ∈ fs, GL L f
theorem rec_arm_goodUL : ReplaceAgrees →
    ∀ (env : Lean.Environment), RecRulePhU env →
    ∀ (p : Lean.Name) (rv : Lean.RecursorVal), env.find? (p.str "rec") = some (Lean.ConstantInfo.recInfo rv) →
    ∀ (c : Lean.Name) (rule : Lean.RecursorRule), rv.rules.find? (fun x => x.ctor == c) = some rule →
    ∀ (L : Nat) (ls : List Lean.Level) (pre fields rest : Array Lean.Expr),
      (∀ a ∈ pre, GL L a) → (∀ a ∈ fields, GL L a) → (∀ a ∈ rest, GL L a) →
      GL L (mkAppN (mkAppN (mkAppN (rule.rhs.instantiateLevelParams rv.levelParams ls) pre) fields) rest)
theorem iota_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel L : Nat) (e r : Lean.Expr), GL L e → iota env natLit? fuel e = ExceptT.mk (some (.ok r)) → GL L r
theorem reduceMatcher?_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (L : Nat) (e r : Lean.Expr), GL L e → reduceMatcher? env natLit? e = ExceptT.mk (some (.ok r)) → GL L r
theorem reduceHead_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel L : Nat) (e r : Lean.Expr), GL L e → reduceHead env natLit? fuel e = ExceptT.mk (some (.ok r)) → GL L r
theorem listLit?_goodL (hi1 : Inst1Agrees) (natLit? : Lean.Expr → Option Nat) :
    ∀ (fuel L : Nat) (e α : Lean.Expr) (xs : List Lean.Expr), GL L e →
      listLit? natLit? fuel e = ExceptT.mk (some (.ok (α, xs))) → GL L α ∧ ∀ x ∈ xs, GL L x
theorem evalNode?_goodL (hi1 : Inst1Agrees) (natLit? : Lean.Expr → Option Nat) :
    ∀ (L : Nat) (e r : Lean.Expr), GL L e → evalNode? natLit? e = ExceptT.mk (some (.ok r)) → GL L r
theorem unfoldCall?_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (L : Nat) (e r : Lean.Expr), GL L e → unfoldCall? env natLit? isUser e = ExceptT.mk (some (.ok r)) → GL L r

def MemoGoodL (s : Std.HashMap Lean.Expr Lean.Expr) : Prop :=
  ∀ (k v : Lean.Expr), s.get? k = some v → ∀ L, GL L k → GL L v

theorem passM_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e r : Lean.Expr) (s s' : Std.HashMap Lean.Expr Lean.Expr), MemoGoodL s →
      (passM env natLit? isUser fuel e).run.run s = (Except.ok r, s') → MemoGoodL s' ∧ ∀ L, GL L e → GL L r
theorem passStep_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e r : Lean.Expr) (s s' : Std.HashMap Lean.Expr Lean.Expr), MemoGoodL s →
      (passStep env natLit? isUser fuel e).run.run s = (Except.ok r, s') → MemoGoodL s' ∧ ∀ L, GL L e → GL L r
theorem passSpine_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e h : Lean.Expr) (args : Array Lean.Expr) (s s' : Std.HashMap Lean.Expr Lean.Expr),
      MemoGoodL s → (passSpine env natLit? isUser fuel e).run.run s = (Except.ok (h, args), s') →
      MemoGoodL s' ∧ ∀ L, GL L e → GL L h ∧ ∀ a ∈ args, GL L a
theorem passWith_ph (natLit? : Lean.Expr → Option Nat) :
    ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env →
    ReplaceAgrees → Inst1Agrees → HeadBetaAgreesL → BetaNonTargetAgrees →
    ∀ (fuel : Nat) (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      passWith fuel env natLit? isUser e = .ok r → NoPh r = true ∧ BvarLt 0 r = true
theorem pass_ph (natLit? : Lean.Expr → Option Nat) :
    ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env →
    ReplaceAgrees → Inst1Agrees → HeadBetaAgreesL → BetaNonTargetAgrees →
    ∀ (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      pass env natLit? isUser e = .ok r → NoPh r = true ∧ BvarLt 0 r = true

-- 証明まで通したもの（§4）:
-- theorem beta_goodL (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
--     ∀ (L : Nat) (f : Expr) (args : Array Expr), GL L f → (∀ a ∈ args, GL L a) → GL L (f.beta args)
-- theorem headBetaM_goodL (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
--     ∀ (fuel L : Nat) (e r : Expr), GL L e → headBetaM fuel e = .ok r → GL L r
-- theorem mkAppN_goodL : ∀ (L : Nat) (f : Expr) (as : Array Expr), GL L f → (∀ a ∈ as, GL L a) → GL L (mkAppN f as)
-- theorem beta_target : ∀ (f : Expr) (args : Array Expr),
--     f.isHeadBetaTargetFn false = true → ¬f.isApp = true → f.beta args = (mkAppN f args).headBeta
end Tools.PassPhL
```

### 2.1 補題の使い方の要点
* `rnc_ph2` は rev1 の Rec グループですでに L 一般（そのまま使える）。`ilp_ph`（`G 0` の入力で `G 0`）は閉じた項（`d.value`、`rule.rhs`）にだけ使い、`bvarLt_mono` で任意の L へ持ち上げる。
* 束縛の下の 3 箇所の手当て: `betaAll` の `lam`/`letE`（`GL (L+1) b` を IH に渡す）、`reduceHead` の `letE`、`passStep` の `lam`/`letE`。`letE` の zeta（`listLit?` 253、`passStep` 377）は `inst1Spec_bvarLt b v 0 L L`（`BvarLt (L+1) b`、`BvarLt L v`）→ `BvarLt L`。`v.hasLooseBVars = false` の条件は証明に使わない（`GL L v` で足りる）。

### 2.2 メモの不変量（`MemoGoodL`）
rev1 の `MemoGood`（`G k → G v`）は L ごとに壊れる（束縛の下で作ったメモの値を、別の深さで使う）。rev2 は **メモの各エントリに L の全称を持たせる**:

* `MemoGoodL s := ∀ k v, s.get? k = some v → ∀ L, GL L k → GL L v`。
* `passM_goodL` の結論は `MemoGoodL s′ ∧ ∀ L, GL L e → GL L r`。**`G` の仮定なしで** `MemoGoodL s′` が出る形（部分項への再帰呼びで `GL` を仮定しない）にして、エントリ `(e, r)` の追加では `∀ L` を `intro L` で示す。
* これは rev1 より強い帰納法の主張（証明は未着手、Pass の最大の不確かさは rev1 と同じく `PM` の `bind` 展開）。

### 2.3 最終の文は L = 0 のままでよいか
**よい。** 消費側の inline-compose の `PassPh`（`par/rt-inline-compose:Tools/ShippingGen5ReaderTraceInlineCompose.lean` 17–21 行）は `NoPh e ∧ BvarLt 0 e` の入力・出力で、`rounds_ph` / `userInliner_ph` が呼ぶのも最上位の式。`pass_ph` / `passWith_ph` は `GL 0` を取り、`passM_goodL` の `L = 0` を使う。`PassPh'` の文（rev1 §1）は仮定 `HeadBetaAgrees0` を `HeadBetaAgreesL` に替える以外は同じ。

## 3. (3) 仮定の扱い

### (b) `headBeta` と `headBetaSpec` の一致を loose bvar つきで証明できるか — **この調査では経路が見つからなかった**
`headBetaSpec`（`Tools/Assume/AbbrevExtern.lean`）は `betaRev.go` の制御を写し、`instantiate` / `instantiateRange` を `instSpec` で写したモデル。`headBeta` の本体 `betaRev` は `partial def`（論理に本体がない）で、`instantiate*` は extern。したがって `L = 0` でも `L > 0` でも **論理の中で `headBeta = headBetaSpec` を導く材料がない**（`L = 0` の一致が T1L-74 として仮定になっているのと同じ理由）。`L > 0` を `L = 0` の一致から導く経路（loose bvar を fvar に置換して同じ項に帰着する等）も、`betaRev` に等式がないため、この調査では見つからなかった。不可能とは言わない。

モデル自体は `L > 0` で成り立つと読める（読みであって証明ではない）: C++ `instantiate_core` は `bvar vidx`（`vidx ≥ offset`）を、`vidx < offset + n` なら代入値（`lift_loose_bvars` で持ち上げ）に、そうでなければ `vidx − n` に下げる。`instSpec` は同じ 3 分岐（`i < off` / `i − off < e − b` / それ以外 `i − (e − b)`）。`L = 0` の仮定が成り立つ根拠（`kernel/instantiate.cpp` の読み）は `L > 0` の項（loose bvar が範囲 `L` 内）でもそのまま読める。

### (a) 新しい仮定 `HeadBetaAgreesL`
```lean
def HeadBetaAgreesL : Prop :=
  ∀ (L : Nat) (e : Lean.Expr), NoPh e = true → BvarLt L e = true → e.headBeta = headBetaSpec e
theorem headBetaAgreesL_zero : HeadBetaAgreesL → HeadBetaAgrees0 := fun h e hn hb => h 0 e hn hb   -- scratch で通った
```
* 配置の案: 新規 `Tools/Assume/BetaExtern.lean`（`AbbrevExtern.lean` は abbrev-s1 の文なので編集しない）。`BetaNonTargetAgrees` もここに置く。
* `HeadBetaAgrees0` を使う既存の証明（`headBeta_good`、`inlAbbrevs_ph`）は **そのまま通る**（`headBetaAgreesL_zero` で `HeadBetaAgreesL` から取れる）。

T1 台帳への影響（reviewer が選ぶ。どちらも数は **受理されるまで台帳に入れない**）:

| 案 | 内容 | T1 台帳 | 条件付き台帳（`BetaNonTargetAgrees` +1 を含む） |
|---|---|---|---|
| (i) 置換 | T1L-74 の行の文を `HeadBetaAgreesL` に **強める**（`HeadBetaAgrees0` は定理になる） | T1L-74 は ±0（行の文の変更）。**台帳の数は変わらない**が、受理済みの仮定の強化なので、承認が要る（ユーザーが採用した U-2 の文の変更にあたると reviewer が見るなら、判断資料を作ってユーザー判断） | T1 55 |
| (ii) 追加 | T1L-74 は残し、`HeadBetaAgreesL` を **別の行として +1** | T1 +1 | T1 56 |

どちらでも FG は変わらない。(i) は行数が増えない代わりに受理済みの文を変える。(ii) は文を変えない代わりに、`HeadBetaAgreesL` が `HeadBetaAgrees0` を含むので **冗長な行が 1 つ残る**。coder の推奨: (i)（含意が 1 行で、`L = 0` の特別扱いを台帳に残す理由がない）。ただし受理済みの文を変えるので **reviewer の判断に委ねる**（ユーザー判断が要るかどうかも含めて）。

### (c) `BetaNonTargetAgrees`（T1 +1 候補）の L 版
**要らない。** 文は `isHeadBetaTargetFn false f = false → f.beta args = mkAppN f args` で、`NoPh` / `BvarLt` を含まず L に依らない（`f` の形だけ）。`beta_goodL` はこの等式のあとに `mkAppN_goodL` で `GL L` を取る。読み（`betaRev` の非ラムダ頭の枝は空の `instantiateRange` で `f` を返す）は loose bvar があっても同じ（`n = sz`、範囲が空）。

## 4. (4) scratch での elaborate と証明
* `Tools.ScratchPassPhL`（型、本体 `sorry`）と `Tools.ScratchPassPhL2`（証明）。`kjob lake build` exit 0。ビルド済みの Pod で `ScratchPassPhL` は初回 ~10 分（依存の再ビルド）、`ScratchPassPhL2` は ~40 秒。
* **証明まで通ったもの（sorry なし、`#print axioms` = propext / Classical.choice / Quot.sound）**: `instSpec_bvarLtL`、`instSpec_noPhL`、`getAppFn_goodL`、`getAppRevArgs_goodL`、`mkAppRevRange_goodL` 相当、`betaDone_goodL`、`betaGo_goodL`、`headBetaSpec_goodL`、`headBeta_goodL`（`HeadBetaAgreesL` から）、`mkAppN_goodL`、`consumeMData_goodL`、`getAppArgs_goodL`、**`beta_target`**（rev1 で未証明。`getAppFn` / `getAppRevArgs` の private を `unfold_priv` で展開）、**`beta_goodL`**、**`headBetaM_goodL`**。コードは `scripts/gen5/RT_PASS_PH_REV2_SCRATCH2.lean.txt`（`SCRATCH1` の型の上に書いたもの。実装では Tools/PassPh/Beta.lean に移せる）。
* 証明したのは `HeadBetaAgreesL` と `BetaNonTargetAgrees` の下での保存であって、これらの仮定が成り立つことではない。mutant は使っていない（この freeze は型・補題の文の提案で、Check はまだ無い）。
* 未着手（型のみ）: `betaAll_goodL`、`betaSpine_goodL`、`rec_arm_goodUL`、`ctorApp_goodL`、`iota_goodL`、`reduceMatcher?_goodL`、`reduceHead_goodL`、`listLit?_goodL`、`evalNode?_goodL`、`unfoldCall?_goodL`、`passM/passStep/passSpine_goodL`、`passWith_ph`、`pass_ph`。

## 5. (5) rev1 からの差分

| 項目 | rev1 | rev2 |
|---|---|---|
| 不変量 | `G e := NoPh ∧ BvarLt 0` | `GL L e := NoPh ∧ BvarLt L`、補題は `∀ L`（最終の `pass_ph` / `passWith_ph` は `L = 0` のまま） |
| 仮定 `HeadBetaAgrees0` | pass_ph の仮定 | **`HeadBetaAgreesL` に置換**（`L = 0` の特殊化が `HeadBetaAgrees0`）。T1 台帳は §3 の 2 案 |
| `BetaNonTargetAgrees` | T1 +1 候補 | 変更なし（L 版は不要） |
| `beta_target` | 未証明 | scratch で証明済み |
| メモ不変量 | `MemoGood`（`G k → G v`） | `MemoGoodL`（各エントリ `∀ L`）、`passM_goodL` は `G` を仮定せず `MemoGoodL s′` を返す |
| 束縛の下の再帰を持つ箇所 | betaAll のみ想定 | betaAll・reduceHead（`letE`）・passStep（`lam`/`letE`）（§1） |
| `ilp_ph` / `rnc_ph2` | `G` | 変更なし（閉じた項に使い単調で持ち上げ） |
| `mkAppN_good` / `ctorApp_good` / `rec_arm_goodU` / `listLit?_good` | `G` | `GL L` 版（`*_goodL`、`rec_arm_goodUL`） |
| §4 持ち込み、`RecRulePhU` の扱い、inline-compose との関係（§3 rev1） | | 変更なし（`PassPh` を外すときの `rounds_ph` の仮説に `HeadBetaAgreesL` が入る） |
| 台帳 | FG 94 / T1 54（0/0）、条件付き T1 55 | FG 94 / T1 54（0/0）、条件付き T1 55（案 i）または 56（案 ii） |

## 6. 並列の作業への影響

| 作業 | 状態 | rev2 で |
|---|---|---|
| Beta（rt109b、`sparkle-rt-pass-ph-beta`） | `G` 版の 3 補題 | **置き換え**。`G` 版は `GL 0` の特殊化で出る。scratch の証明（`SCRATCH2`）をそのまま使える。無駄になるのは `L = 0` 専用に書いた部分 |
| BetaAll（rt112） | blocked | **解除**（`betaAll_goodL` / `betaSpine_goodL` の文が確定。`headBetaM_goodL` の上で測度 `(fuel, sizeOf, k)` の帰納） |
| Rec（2f6e198c、完了） | `G` 版、sorry なし | **`rnc_ph2` / `ilp_ph` はそのまま**。`mkAppN_good` / `ctorApp_good` / `rec_arm_goodU` は `GL L` 版へ（閉じた rhs + 引数の `mkAppN` なので小さな改訂。`mkAppN_goodL` は scratch にある） |
| ListLit（48f1a95c、完了） | `G` 版、sorry なし | `listLit?_goodL` へ。`inst1Spec_bvarLt` の `m = m′ = 0` を `m = m′ = L` に替える機械的な改訂 |
| Iota（rt113） | `G` 版の文 | **文を `GL L` 版へ**（`reduceHead` の `letE` が L+1 を要する）。着手前なら rev2 を待つ。着手済みなら `L = 0` の部分は捨てる |
| Pass（rt114） | `MemoGood` | **`MemoGoodL` に替える**（§2.2）。`unfoldCall?_goodL` / `evalNode?_goodL` も `GL L` |

## 7. reviewer に確認してほしい点
1. 不変量の一般化（`GL L`、補題 `∀ L`、最終は `L = 0`）の形と、`MemoGoodL`（§2.2）。
2. **仮定 `HeadBetaAgrees0` → `HeadBetaAgreesL`**（§3）。案 (i) 置換（T1L-74 の文の強化、数は ±0）か、案 (ii) 追加（T1 +1）か。受理済みの仮定の変更なのでユーザー判断が要るか。
3. `BetaNonTargetAgrees` を rev1 のまま（L 版なし）にすること。
4. `HeadBetaAgreesL` / `BetaNonTargetAgrees` の配置（新規 `Tools/Assume/BetaExtern.lean`、`AbbrevExtern.lean` は編集しない）。
5. §6 の並列作業の切り替え（特に Rec / ListLit の完了済み補題の `GL L` 化）。

## rev3（2026-11-03、coder）: memo の保存に要る `Expr.eqv` の振る舞いの仮定

根拠: `scripts/gen5/RT_PASS_PH_MEMO.md`（rt120、69c0dcc0）と scratch `RT_PASS_PH_MEMO_scratch.lean.txt`（`kjob lake env lean` で elaborate、sorry / axiom なし）。

**問題.** `passM` の memo は `Std.HashMap Expr Expr`。`Expr` の `BEq` は extern の `Expr.eqv` で、core には `EquivBEq Expr` も `LawfulHashable Expr` も無い（`#synth` が失敗する）。`Std` の `getElem?_insert` などは、この 2 つを要る。

さらに、hit したときと insert の後の不変量 `MemoGoodL` には、`e == k` から `GL L k → GL L e`（またはその逆）を得る事実が要る。`EquivBEq` は `==` の反射・対称・推移しか言わないので、それだけでは足りない（MEMO §2）。

- 既存の T1L-72 `ExprEqvAtom` は atom にしか効かない。
- `KeySound`（`a == b → a = b`）は、`Expr.eqv` が binder 名を無視するので偽の見込み。

**仮定（案 A、推奨。T1 +1 の 1 行に束ねる）.** `Tools/Assume/ExprEqvGL.lean` に置く（新規）:

```lean
/-- `Expr.eqv`（extern）は alpha 同値で、`hash` と整合し、`GL L`（NoPh ∧ BvarLt L）を保つ。
    NoPh（fvar の tag）と BvarLt（bvar の番号と binder の深さ）は binder 名に依存しない。C++ の実装についての仮定。 -/
structure ExprEqvLaws : Prop where
  equiv : EquivBEq Lean.Expr
  lawfulHash : LawfulHashable Lean.Expr
  pres : ∀ a b : Lean.Expr, (a == b) = true → ∀ L, GL L a → GL L b
```

型クラスの instance は、仮定の中の値から `haveI` で局所的に作る（大域の instance は足さない）。

**使い道.**
- `memoGoodL_insert`（ExprEqvLaws と MemoGoodL s と `∀ L, GL L e → GL L r` から MemoGoodL (s.insert e r)）
- `memoGoodL_hit`（定義そのもの）
- `memoGoodL_empty`

これらを `Tools/PassPh/Defs.lean` 相当に置く。`passM_goodL` / `passStep_goodL` / `passSpine_goodL` / `passWith_ph` / `pass_ph` の仮説に `(hEq : ExprEqvLaws)` を足す。

**文の差分（rev2 から）.** 上の 5 つの補題の仮説に `hEq : ExprEqvLaws` を 1 つ足すだけ。結論は不変。`PassPh'` の最終の文にも `ExprEqvLaws →` が 1 つ加わる。

**台帳.**
- 受入済みは変えない（FG 94 / T1 54）。
- 条件付きの見込みは T1 +1（ExprEqvLaws）。rev2 までの見込み T1 55（BetaNonTargetAgrees +1、HeadBetaAgreesL は T1L-74 の置き換えで ±0）と合わせて、**T1 56**（受理されたとき）。
- 案 B（3 行に分けて T1 +3）は推奨しない。同じ extern `Expr.eqv` の 1 つの性質の束で、使い道は MemoGoodL の保存だけであるため。

**代替（仮定を増やさない）.** この調査では見つからなかった（MEMO §3, §5）:
- `toList` の形でも `EquivBEq` が要り、hit 側の `GL L e → GL L k` も残る。
- memo を別実装に差し替えるのは、compiler の編集になる。

**reviewer に確認してほしい点.**
1. 案 A（1 行）でよいか。
2. `pres` の妥当性の読み（binder 名を無視する alpha 同値が `NoPh` / `BvarLt` を保つ）。
3. 型クラスを structure の field として持つ形でよいか。

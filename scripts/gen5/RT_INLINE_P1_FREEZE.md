# RT inline P1 freeze: `inlineDefs` 系の `NoPh ∧ BvarLt` 保存（新前提なし）

Issue: `sparkle-rt-inline-p1`（親 `sparkle-gen5-dg-readertrace`）。base: `par/rt-inline-survey` d2b23b6b。調査: `scripts/gen5/RT_INLINE_SURVEY.md` §1.2 / §4。
**台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。** 共通ルールの分担により、台帳前提を増やさない単位なので reviewer には出さない（review にしない）。

## 1. 範囲

* 対象: `Sparkle/Compiler/Elab.lean` の `inlLift` / `inlSubst` / `inlBeta` / `inlSpine` / `inlMap` / `inlDropBinder` / `inlCanonLam` / `inlCanonPi` / `inlSignalMapOfFunctor` / `inlSignalApplicative` / `inlHeadCtor` / `inlineDefs` と `userDefinition?` が `NoPh ∧ BvarLt` を保つこと。
* 新しい前提なし: `Tools.Assume.EnvDeclValue.DeclValuePh`（`Tools/ShippingGen5ReaderTraceDirect.lean` で定義済みの候補。`Tools/Assume/` には登録しない）を**定理の仮説として取るだけ**。`inlineDefs_ph` 自体は `defs` についての仮説 `hd`（`defs n = some v → NoPh v ∧ BvarLt 0 v`）だけを取り、`userDefinition?_ph` が `DeclValuePh` から `hd` を与える。
* 範囲外（作らない）: `relevantClosure` の真の腕（`rounds` / `MachRecUnfold.pass`）、`inlAbbrevs`（`Expr.replace` / `headBeta`）、`userInliner` 全体の合成。`RecRulePh`、U-1 / U-2 / U-3 は必要としない（この単位の範囲では出番がない）。
* 既存の `inlSpine_ph`（引数だけの版、`ShapeIn` 側）とは別名で `inlSpineAll_ph`（頭も含む）を足す。Elab.lean、共有定義、コンパイラは編集しない。
* 新規 Lean: `Tools/ShippingGen5ReaderTraceInlineP1.lean`（`lakefile.lean` に `lean_lib` を 2 つ足す: 本体と Check）。名前空間は `Tools.ShippingGen5ReaderTrace`。`set_option autoImplicit false`。

## 2. 完全型

以下は scratch（同ファイルを `sorry` 付きの文だけで `autoImplicit false` の下に elaborate）の `#check` 出力を写したもの。`open Lean Sparkle.Compiler.Elab`。`BvarLt` / `NoPh` は `Tools/ShippingGen5ReaderTrace.lean` の定義。

```
foldl_app_ph : ∀ (L : Nat) (h : Expr) (args : List Expr),
  NoPh h = true ∧ BvarLt L h = true →
    (∀ (a : Expr), a ∈ args → NoPh a = true ∧ BvarLt L a = true) →
      NoPh (List.foldl Expr.app h args) = true ∧ BvarLt L (List.foldl Expr.app h args) = true
inlLift_ph : ∀ (k c : Nat) (e : Expr) (b L : Nat) (e' : Expr) (b' : Nat),
  NoPh e = true → BvarLt L e = true → inlLift k c e b = some (e', b') → NoPh e' = true ∧ BvarLt (L + k) e' = true
inlSubst_ph : ∀ (xs : Array Expr) (L : Nat),
  (∀ (x : Expr), x ∈ xs → NoPh x = true ∧ BvarLt L x = true) →
    ∀ (d : Nat) (e : Expr) (b : Nat) (e' : Expr) (b' : Nat),
      NoPh e = true →
        BvarLt (d + xs.size + L) e = true →
          inlSubst xs d e b = some (e', b') → NoPh e' = true ∧ BvarLt (d + L) e' = true
inlBeta_ph : ∀ (L : Nat) (v : Expr) (acc : Array Expr) (args : List Expr) (b : Nat) (e' : Expr) (b' : Nat),
  (∀ (x : Expr), x ∈ acc → NoPh x = true ∧ BvarLt L x = true) →
    (∀ (a : Expr), a ∈ args → NoPh a = true ∧ BvarLt L a = true) →
      NoPh v = true →
        BvarLt (acc.size + L) v = true → inlBeta acc v args b = some (e', b') → NoPh e' = true ∧ BvarLt L e' = true
inlSpineAll_ph : ∀ (L : Nat) (e : Expr) (acc : List Expr) (h : Expr) (args : List Expr),
  NoPh e = true →
    BvarLt L e = true →
      (∀ (a : Expr), a ∈ acc → NoPh a = true ∧ BvarLt L a = true) →
        inlSpine e acc = (h, args) →
          (NoPh h = true ∧ BvarLt L h = true) ∧ ∀ (a : Expr), a ∈ args → NoPh a = true ∧ BvarLt L a = true
inlMap_ph : ∀ (f : Expr → Nat → Option (Expr × Nat)) (L : Nat),
  (∀ (a : Expr) (b : Nat) (a' : Expr) (b' : Nat),
      NoPh a = true → BvarLt L a = true → f a b = some (a', b') → NoPh a' = true ∧ BvarLt L a' = true) →
    ∀ (xs : List Expr) (b : Nat) (xs' : List Expr) (b' : Nat),
      (∀ (x : Expr), x ∈ xs → NoPh x = true ∧ BvarLt L x = true) →
        inlMap f xs b = some (xs', b') → ∀ (x : Expr), x ∈ xs' → NoPh x = true ∧ BvarLt L x = true
inlDropBinder_ph : ∀ (e : Expr) (c M : Nat) (e' : Expr),
  c ≤ M → NoPh e = true → BvarLt (M + 1) e = true → inlDropBinder c e = some e' → NoPh e' = true ∧ BvarLt M e' = true
inlCanonLam_ph : ∀ (e : Expr) (k L : Nat),
  NoPh e = true → BvarLt L e = true → NoPh (inlCanonLam k e) = true ∧ BvarLt L (inlCanonLam k e) = true
inlCanonPi_ph : ∀ (e : Expr) (L : Nat),
  NoPh e = true → BvarLt L e = true → NoPh (inlCanonPi e) = true ∧ BvarLt L (inlCanonPi e) = true
inlSignalMapOfFunctor_ph : ∀ (L : Nat) (e e' : Expr),
  NoPh e = true → BvarLt L e = true → inlSignalMapOfFunctor e = some e' → NoPh e' = true ∧ BvarLt L e' = true
inlSignalApplicative_ph : ∀ (L : Nat) (n : Name) (ls : List Level) (args : List Expr) (e' : Expr),
  (∀ (a : Expr), a ∈ args → NoPh a = true ∧ BvarLt L a = true) →
    inlSignalApplicative n ls args = some e' → NoPh e' = true ∧ BvarLt L e' = true
inlHeadCtor_ph : ∀ (defs : Name → Option Expr),
  (∀ (n : Name) (v : Expr), defs n = some v → NoPh v = true ∧ BvarLt 0 v = true) →
    ∀ (ctor : Name) (fuel : Nat) (e : Expr) (b L : Nat) (as : List Expr) (b' : Nat),
      NoPh e = true →
        BvarLt L e = true →
          inlHeadCtor defs ctor fuel e b = some (as, b') → ∀ (a : Expr), a ∈ as → NoPh a = true ∧ BvarLt L a = true
inlineDefs_ph : ∀ (defs : Name → Option Expr) (projs : Name → Option (Name × Nat × Nat)),
  (∀ (n : Name) (v : Expr), defs n = some v → NoPh v = true ∧ BvarLt 0 v = true) →
    ∀ (fuel : Nat) (e : Expr) (b L : Nat) (e' : Expr) (b' : Nat),
      NoPh e = true →
        BvarLt L e = true → inlineDefs defs projs fuel e b = some (e', b') → NoPh e' = true ∧ BvarLt L e' = true
userDefinition?_ph : ∀ (env : Environment),
  Assume.EnvDeclValue.DeclValuePh env →
    ∀ (n : Name) (v : Expr), userDefinition? env n = some v → NoPh v = true ∧ BvarLt 0 v = true
inlineDefs_user_ph : ∀ (env : Environment),
  Assume.EnvDeclValue.DeclValuePh env →
    ∀ (L : Nat) (e : Expr),
      NoPh e = true →
        BvarLt L e = true →
          NoPh
                (match inlineDefs (userDefinition? env) (userProjection? env) inlineDepth e inlineBudget with
                | some (e', snd) => e'
                | none => e) =
              true ∧
            BvarLt L
                (match inlineDefs (userDefinition? env) (userProjection? env) inlineDepth e inlineBudget with
                | some (e', snd) => e'
                | none => e) =
              true
```

注: `inlineDefs_user_ph` の `match` は `userInliner` 内の局所関数 `inl` の本体と同じ形（`inlineDefs (userDefinition? env) (userProjection? env) inlineDepth e inlineBudget`、`none` なら `e`）を書き出したもの。`userInliner` そのものは扱わない。

## 3. 証明方針（実装メモ）

* `inlLift_ph`: `e` の構造と予算 `b` の帰納、`c` と `L` を一般化。`bvar i` は `i<c` なら `i<L`、そうでなければ `i+k<L+k`。binder は `L+1`、`c+1`。
* `inlSubst_ph`: `d` と `L` を一般化。`i<d`、`d ≤ i < d+xs.size`（`xs` の要素。`d>0` なら `inlLift_ph` で `L+d`）、それ以外は仮定 `BvarLt (d+xs.size+L)` と矛盾。`mdata` / `proj` は `none`。
* `inlBeta_ph`: `args` の帰納で `acc` を伸ばす（`BvarLt` の下界は `acc.size+L`）。最後は `inlSubst_ph`（`d=0`）と `foldl_app_ph`。
* `inlHeadCtor_ph` / `inlineDefs_ph`: fuel 帰納。`defs` の値は `bvarLt_mono` で `BvarLt L`。`inlMap_ph` は fuel の IH を渡す。`inlSignalApplicative_ph` は `inlDropBinder_ph`（`c=0 ≤ L`）、`inlCanonLam_ph`、`inlCanonPi_ph`。
* 定義の等式補題を他モジュールから生成しないよう `unfold` より `show` / `delta` / `simp only [f]` を優先する。

## 4. 検証計画 / 主張しないこと

* 部品ごとに `kjob lake build Tools.ShippingGen5ReaderTraceInlineP1` を 1 つずつ。Check は `Tests/Gen5/ReaderTraceInlineP1Check.lean`（TYPE: この文書の `#check` と独立に書いた `Exp…`、MUTANT は signature / defeq での棄却で意味的反例ではない、AXIOMS 標準、CLOSURE、COUNTS）。
* この定理群が示すのは「`DeclValuePh env` のもとで `inlineDefs` の出力が `NoPh ∧ BvarLt L`」だけ。`DeclValuePh` が受理されるソースで成り立つことは示さない（候補のまま）。`userInliner` 全体（`rounds` / `inlAbbrevs`）の保存は示さない。
* 新しい条件（`RecRulePh`、U-1 / U-2 など）が必要になったらここに追記して止まり、note で coder に返す。

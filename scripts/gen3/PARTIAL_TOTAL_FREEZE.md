# PARTIAL_TOTAL_FREEZE — Sparkle 自身の partial def 3 件を全域化して定理にする（freeze、文書のみ）

Issue: sparkle-n3-partial-total。base: par/n3agree-m3 ad5f7704。Lean 実装は未着手（この文書の承認後）。
ユーザー判断（2026-11-01）: 3 件は実コンパイルで使われる。計算を変えずに partial を外し、既存モデルとの一致を定理にする。停止が示せない関数だけを名前付き仮定として Tools/Assume/ に残す。

原文・モデルの場所（kjob/g3aw-a24 8fff703c）:

| 台帳 | 原文 | モデル |
|---|---|---|
| T1L-52 `RootFloatAgrees` | Tools/ShippingLetsExternSpec.lean:237 `∀ e, LetOk 0 e = true → rootFloat e = rootFloatS e` | 同:188 `rootFloatS`（`liftSpec`、測度 `nu`、停止証明済み） |
| T1L-58 `LiftScalarCorr senv` | Tools/Prototype/LiftScalarModelLetOk.lean:350 `machLiftScalarN … = some (w,r) → ∃ fuel, liftN … fuel e = some (w,r)` | 同:128 `liftN`（`liftStep` を fuel で回す） |
| T1L-59 `BoolMapCorr senv` | Tools/Prototype/BoolMapModelLetOk.lean:100 `machBoolMap … = some r → boolMapModel (machLiftScalarN senv dom [(wa,a)]) dom body = some r` | 同:29 `boolMapModel`（構造再帰・全域） |

## 結論（scratch の結果）

scratch（/build/scratch-ptot1、ソースツリーの外のコピー）で、3 件とも partial を外した版が `Sparkle.Compiler.Elab` ごと elaborate して build 成功（全域化の差分 約 40 行、この文書末尾）。

| 関数 | 結果 | 停止の根拠 |
|---|---|---|
| machBoolMap | 通った。`partial` を消すだけ（本体は無変更） | 構造再帰（`!` の引数 `x` は `.app (.const c _) x` の部分項） |
| machLiftScalarN | 通った。`partial` を消し、`termination_by e => sizeOf e` と `decreasing_by` を付け、`ashr` 腕だけ書き換え | 全再帰呼び出しが部分項（x, y）。`ashr` 腕は元は再構成した項 `sshiftRight nE x (toNat nE y)` に再帰しており sizeOf が増えるため、`sshiftRight` 腕の本体をその場に展開（結果は同一、下記） |
| rootFloat | 通った。ただし fuel 版（下記）。測度による WF 定義は通せない | 測度 `nu` が `liftLooseBVars`（C++ extern、opaque）で保存されることをカーネルで言えない |

通らなかった点: `rootFloat` を `termination_by`（測度 nu）で直接書く案。`liftLooseBVars` が opaque のため `nu (liftLooseBVars t 0 1) = nu t` が証明できず、decreasing が閉じない（この調査で試した範囲。他の測度は試していない）。

## 1. 全域版の定義案

### 1.1 machBoolMap（Elab.lean:4831）
`partial def` → `def`。本体は一字も変えない。計算は同じ。

### 1.2 machLiftScalarN（Elab.lean:4652〜）
- `partial` を外す。`termination_by e => sizeOf e`、`decreasing_by all_goals (simp_wf; first | omega | (simp [hs]; omega))`。
- `sshiftRight` 腕の内側 `match s with` を `match hs : s with` に（`toNat` 腕の `y ⊂ s` を decreasing に渡す。計算は同じ）。
- `Signal.ashr` 腕（4739〜4742）: 元は `machLiftScalarN … (sshiftRight nE x (toNat nE y))` を呼ぶ。これを、その呼び出しが通る `sshiftRight` 腕の本体を `s := toNat nE y` で展開した形に置換。
  同一性の確認（手で追った）: (a) 再構成した項は 4 引数の `sshiftRight` で、それより前の腕（`.bvar`、6 引数の腕、`BitVec.append`、`extractLsb'`、`not`、`signExtend`）に当たらない。(b) `!x.hasLooseBVars` のときの `machLiftConst` は再構成項 `e'` に対して呼ぶ（`y` の loose bvar も `e'` の `hasLooseBVars` に反映される）。(c) `canonicalNatLitValue? mE != some n` は `mE = nE`、`n ← canonicalNatLitValue? nE` なので常に偽（展開後も同じ条件を残した）。(d) `s` の `_` 腕（`toNat` 以外）は `s` が `toNat` なので到達しない。
  これは検査（下記 2）と証明（下記 3）で確かめる。手での確認は証拠にしない。
- 他に新定義なし。

### 1.3 rootFloat（MachRawSurface.lean:198）
`liftLooseBVars` が extern なので fuel 版にする（`liftN` が既に fuel 版なのと同じ方針）。

```
def rootFloatF : Nat → Expr → Expr        -- 元の 3 腕と同じ式、再帰は k で
def rootFloat (e) := rootFloatF (rootFloatNu e + 1) e
```
`rootFloatNu` は `rootFloatS` の測度 `nu`（`nsz` 含む）と同じ式。各再帰で `nu` が 1 以上減るので、`liftLooseBVars` が `nu` を保つ限り燃料は尽きない。尽きた場合の結果は入力 `e` のまま（元の partial なら続行する分岐）。燃料が尽きないことは「`liftLooseBVars` は構造を保つ」ことに依存し、これは既存の前提 `LiftAgrees`（T1 台帳に既にある行）で与える。つまり新しい前提は増えない。
rootFloat の呼び出しは `rootFloat v` の形のまま（Elab.lean:3990/4155/5088 は無変更）。

## 2. 計算が同じことの検査（検査であって証明ではない）

1. 置き換え前（base）と後（candidate）で、既存の回路記述をまとめて変換し、生成 Verilog の文字列を比較する。
   - corpus: `scripts/shipping-coverage/run.sh` の pass 1 が対象にする `#synthesizeVerilog` 等を含む Tests / IP / Examples の全ファイル。
   - 比較: `PASSES=1 scripts/shipping-coverage/run.sh WORK_BASE` と `…WORK_CAND`（各 SHA で `lake build Tests.AllTests` 後）、`scripts/shipping-coverage/compare_outputs.py WORK_BASE/out WORK_CAND/out`。identical / renumbered / different を報告し、different があれば合格にしない。
   - 差異の見え方: `ashr` 腕は書き換えたので、`ashr` を使う設計（ShippingSignOps 系、RV32 など）が corpus に入っていることを `grep` で確認して数を報告する。入っていなければ、`ashr` を含む入力 Expr を直接 `Tests/Compiler/` の一致テスト（`ExtModelAgreeTest` の形）に加える。
2. 単体: base の関数と candidate の関数を同じプロセスで呼べないので、`Tests/Compiler/LiftScalarModelAgreeTest.lean` / `BoolMapModelAgreeTest.lean` / `ExtModelAgreeTest.lean`（g3aw-a24 にある）の格子を candidate でも走らせ、期待値（base で採った出力）と `Expr.equal` で比較する。
3. コンパイル時間: 同じ corpus で `SPARKLE_PROFILE=1`（run.sh の pass 1 が /tmp/sparkle-profile.log に出す）を base / candidate それぞれ取り、ファイルごとの合計時間と全体を比べる。期待: rootFloat は入力ごとに `nu` を 1 回走査するだけ、WF 定義は実行時は通常の再帰と同じコードにコンパイルされるので差は出ない見込み。差が出たら数を報告する（予測は結果の根拠にしない）。ログ・測定データはソースツリーに置かない。

mutant について: 以降の書き換え案が仕様を変えていないかを調べるために signature / defeq で棄却する検査を使う場合、それは名前や型の違いでの棄却であって、意味的な反例ではない。

## 3. 一致定理の型案（新規ファイル Tools/PartialTotal/…lean に置く。compiler は編集しない）

モデルは g3aw-a24 の定義を新規ファイルに移して使う（`liftSpec`、`rootFloatS`、`liftN`/`liftStep`、`boolMapModel`）。台帳の原文と同じ型で証明する。

```lean
-- T1L-59: 等式（原文より強い。原文は → のみ）
theorem boolMap_eq (senv) (dom a) (wa) :
  ∀ body, machBoolMap senv dom a wa body
        = boolMapModel (machLiftScalarN senv dom [(wa, a)]) dom body
theorem boolMapCorr (senv) : BoolMapCorr senv     -- 上から

-- T1L-58
theorem liftScalarCorr (senv) : LiftScalarCorr senv
  -- ∀ dom vars e w r, machLiftScalarN senv dom vars e = some (w, r) → ∃ fuel, liftN senv dom vars fuel e = some (w, r)

-- T1L-52（LiftAgrees の下。LiftAgrees は既存の別行で、ここでは増やさない）
theorem rootFloatAgrees (hl : LiftAgrees) : RootFloatAgrees
  -- ∀ e, LetOk 0 e = true → rootFloat e = rootFloatS e
```

証明の筋道:
- boolMap_eq: `body` の帰納法（`Expr.app f x`）。`machBoolMap` / `boolMapModel` の等式補題を開き、`!` 腕は IH、`==` 腕は同一式（`lift := machLiftScalarN senv dom [(wa,a)]` で一致）、残りは `none`。scratch で `unfold machBoolMap boolMapModel; split <;> simp_all` により candidate に対して証明が通ることを確認した（この 1 件のみ確認、他は未実施）。
- liftScalarCorr: `machLiftScalarN` の WF 等式補題（`unfold machLiftScalarN`）が使えるようになる。`sizeOf e` についての強い帰納法で、各腕が `liftStep` の腕と同じ式、再帰呼び出し `machLiftScalarN … x` を `∃ fuel` の IH で置き、`liftN (max k₁ k₂ + 1)` を取る（fuel 単調性補題 `liftN_mono` が要る。g3aw-a24 に無ければ新規に証明）。`ashr` 腕は展開形なので `liftStep` の `ashr` 腕（元は `self` 呼び出し）とは 1 段の差があり、`liftN` 側で `ashr` 腕を `sshiftRight` 腕に 1 段進めて一致させる（`liftN (k+2)` で同じ）。見込みの難所はここと、腕の数が多いこと（9 腕程度）。
- rootFloatAgrees: `rootFloatF k e = rootFloatS e` を `k > nu e`、`LetOk 0 e` のもとで `k` についての帰納法で示す。`LiftAgrees` で `liftLooseBVars = liftSpec`（`LetOk 0` を保つ: `liftSpec_ok` があるので帰納法で維持される）、`nu_liftSpec` / `nsz_liftSpec`（g3aw-a24 にある）で燃料の十分性。これは `rootFloatS` の停止証明と同じ計算。

## 4. 台帳差分

| 行 | 変更 |
|---|---|
| T1L-52 RootFloatAgrees | 定理に変わる（T1 -1）。ただし `LiftAgrees`（既存の T1 行）に依存する形。LiftAgrees は残る |
| T1L-58 LiftScalarCorr | 定理に変わる（T1 -1） |
| T1L-59 BoolMapCorr | 定理に変わる（T1 -1） |

見込み: 台帳: FG 102 / T1 57（今回 FG -0 +0 / T1 -3 +0）。停止が示せず仮定に残る関数はない（3 件とも停止が通った。rootFloat は extern 由来の LiftAgrees を介する）。新しい前提・law・TRUSTED 境界の追加なし、FG の変更なし。
注意: 実際の件数は実装後に数え直す。`partial def = モデル` の名前付き仮定を Tools/Assume/ に追加する必要は今のところ出ていない。

## 5. compiler 変更の範囲

| ファイル | 行（base） | 変更 |
|---|---|---|
| Sparkle/Compiler/Elab.lean | 4652 | `partial def machLiftScalarN` → `def`（+ `termination_by` / `decreasing_by` を `| e => machLiftConst senv dom e` の直後に 2 行） |
| 同 | 4726 | `match s with` → `match hs : s with` |
| 同 | 4738〜4741 | `ashr` 腕を `sshiftRight` 腕の展開形に置換（+10 行） |
| 同 | 4831 | `partial def machBoolMap` → `def` |
| Sparkle/Compiler/MachRawSurface.lean | 198〜206 | `partial def rootFloat` を `rootFloatNsz` / `rootFloatNu` / `rootFloatF` / `rootFloat`（薄い包み）に置換（+約 20 行） |

- 呼び出し元: `rootFloat` の呼び出し（Elab.lean:3990, 4155, 5088）は無変更（名前・型・引数同じ）。`machLiftScalarN` / `machBoolMap` の呼び出し元（Elab.lean:4768, 4806, 4815, 4911 ほか）も型が同じなので無変更。
- 実行時の違い: WF 定義は `partial` と違い等式補題を持つが、コンパイル後のコードは再帰関数。`machLiftScalarN` の `ashr` 腕は再構成 → 再入が無くなる分だけ軽い。`rootFloat` は 1 回の走査（`nu`）が増える。
- Elab.lean を小さく保つ方針: Elab.lean は新しい定義を足さない（既存関数の in-place 編集のみ、実質 +13 行）。新規定義は rootFloat 側の 3 つ（MachRawSurface.lean、すでに rootFloat がある小さい別ファイル）と、定理・モデルを置く新規ファイルに限る。`machLiftScalarN` は Elab 内の他の定義に依存していて別ファイルに移せない（Elab を import する側のファイルからは差し替えられない）ので in-place にする。
- 禁止事項との関係: Tools/ShippingGen2Defs.lean、T1Hyp、T1HypND には触れない。`Elab*.lean` の編集は本件の目的そのもの（ユーザー判断 2026-11-01 で承認済み）だが、reviewer がこの freeze を承認するまで編集しない。

## 6. 実装手順（承認後）と受理

1. 新規ファイル（定理 + モデル）を skeleton として先に出す（型は上記のまま）。
2. compiler 側の 5 箇所を編集し、キャッシュ付き target build で `Sparkle.Compiler.Elab` と依存する Tools/Tests が通ることを確認。
3. 2 章の検査を実行して結果を note に書く（different が 1 件でもあれば止めて報告）。
4. 定理を証明（manifest 付き proof-accept で受理）。clean build は最終受理・統合のときのみ。

## 付録: scratch で通った差分（そのまま）

```diff
diff --git a/Sparkle/Compiler/Elab.lean b/Sparkle/Compiler/Elab.lean
index f796bd4..61b4717 100644
--- a/Sparkle/Compiler/Elab.lean
+++ b/Sparkle/Compiler/Elab.lean
@@ -4649,7 +4649,7 @@ def machNormAp (e : Lean.Expr) : Lean.Expr :=
     operators, a concatenation, a slice as a `map` of `extractLsb'`, `not` as
     `allOnes ^^^ ·`, constants as `Signal.pure` of their literal. Returns the
     width and the Signal expression. -/
-partial def machLiftScalarN (senv : StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) :
+def machLiftScalarN (senv : StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) :
     Lean.Expr → Option (Nat × Lean.Expr)
   | .bvar i => vars[i]?
   | e@(.app (.app (.app (.app (.app (.app (.const m _) t1) t2) t3) inst) x) y) =>
@@ -4723,7 +4723,7 @@ partial def machLiftScalarN (senv : StructEnv) (dom : Lean.Expr) (vars : List (N
     if n == 0 then none else
     let (wx, x') ← machLiftScalarN senv dom vars x
     if wx != n then none else
-    let y' ← match s with
+    let y' ← match hs : s with
       | .app (.app (.const ``BitVec.toNat _) mE) y => do
         if canonicalNatLitValue? mE != some n then none else
         let (wy, y') ← machLiftScalarN senv dom vars y
@@ -4735,9 +4735,19 @@ partial def machLiftScalarN (senv : StructEnv) (dom : Lean.Expr) (vars : List (N
     some (n, Sparkle.Compiler.MachSignOps.ashrE inlNatLit
       (fun m a b => machSigBin m ((machSigInst m).getD .anonymous) dom n a b) dom n x' y')
   -- the DSL's `ashr a b` is `a.sshiftRight b.toNat` (its definition)
-  | .app (.app (.app (.const ``Sparkle.Core.Signal.ashr _) nE) x) y =>
-    machLiftScalarN senv dom vars
-      (mkApp3 (.const ``BitVec.sshiftRight []) nE x (mkApp2 (.const ``BitVec.toNat []) nE y))
+  | .app (.app (.app (.const ``Sparkle.Core.Signal.ashr _) nE) x) y => do
+    let e' := mkApp3 (.const ``BitVec.sshiftRight []) nE x (mkApp2 (.const ``BitVec.toNat []) nE y)
+    if !x.hasLooseBVars then machLiftScalarN.machLiftConst senv dom e' else
+    let n ← canonicalNatLitValue? nE
+    if n == 0 then none else
+    let (wx, x') ← machLiftScalarN senv dom vars x
+    if wx != n then none else
+    let y' ← do
+      if canonicalNatLitValue? nE != some n then none else
+      let (wy, y') ← machLiftScalarN senv dom vars y
+      if wy != n then none else some y'
+    some (n, Sparkle.Compiler.MachSignOps.ashrE inlNatLit
+      (fun m a b => machSigBin m ((machSigInst m).getD .anonymous) dom n a b) dom n x' y')
   -- `-x` is `0 - x` (by the definitions of `BitVec.neg` and `BitVec.sub`)
   | e@(.app (.app (.app (.const ``Neg.neg _) (.app (.const ``BitVec _) nE)) _) x) => do
     if !x.hasLooseBVars then machLiftConst senv dom e else
@@ -4754,6 +4764,8 @@ partial def machLiftScalarN (senv : StructEnv) (dom : Lean.Expr) (vars : List (N
     some (n, machSigBin ``HXor.hXor ``Sparkle.Core.Signal.instHXorSignalBitVec dom n
       (machPureE dom n (machBVLit n (2 ^ n - 1))) x')
   | e => machLiftConst senv dom e
+termination_by e => sizeOf e
+decreasing_by all_goals (simp_wf; first | omega | (simp [hs]; omega))
 where
   /-- A closed constant: its literal, as `Signal.pure`. -/
   machLiftConst (senv : StructEnv) (dom e : Lean.Expr) : Option (Nat × Lean.Expr) :=
@@ -4828,7 +4840,7 @@ def machNormApLift (senv : StructEnv) (e : Lean.Expr) : Lean.Expr :=
 /-- A `Bool`-valued lambda over a `BitVec` Signal `a` of width `wa`: an
     equality of lifted operands (`x == y`, `Signal.beq`), under `!`
     (`~~~`, the Signal's Bool complement). -/
-partial def machBoolMap (senv : StructEnv) (dom a : Lean.Expr) (wa : Nat) :
+def machBoolMap (senv : StructEnv) (dom a : Lean.Expr) (wa : Nat) :
     Lean.Expr → Option Lean.Expr
   | .app (.const c _) x =>
     if c == ``Bool.not || c == ``not then do
diff --git a/Sparkle/Compiler/MachRawSurface.lean b/Sparkle/Compiler/MachRawSurface.lean
index bc4a2ed..a08ba4b 100644
--- a/Sparkle/Compiler/MachRawSurface.lean
+++ b/Sparkle/Compiler/MachRawSurface.lean
@@ -195,17 +195,37 @@ of a `let`'s value:
 `f (let x := v; b)` is `let x := v; f b` (zeta on both sides) — a projection
 of a `let` block (`(let s := Signal.loop …; bundle2 r d).fst`, an unfolded
 `projN! (dividerQ …) 2 0`) becomes a block whose root is the projection. -/
-partial def rootFloat : Lean.Expr → Lean.Expr
-  -- `let x := (let y := v; w); b` is `let y := v; let x := w; b`
+-- Termination measure of rootFloatF: the value of a `let` / the argument of an application counts double.
+def rootFloatNsz : Lean.Expr → Nat
+  | .app f a => rootFloatNsz f + rootFloatNsz a + 1
+  | .lam _ t b _ => rootFloatNsz t + rootFloatNsz b + 1
+  | .forallE _ t b _ => rootFloatNsz t + rootFloatNsz b + 1
+  | .letE _ t v b _ => rootFloatNsz t + rootFloatNsz v + rootFloatNsz b + 1
+  | .mdata _ e => rootFloatNsz e + 1
+  | .proj _ _ e => rootFloatNsz e + 1
+  | _ => 1
+
+def rootFloatNu : Lean.Expr → Nat
+  | .letE _ _ v b _ => 2 * rootFloatNsz v + rootFloatNu b + 1
+  | .app f a => rootFloatNsz f + rootFloatNu a + 1
+  | _ => 0
+
+/-- `rootFloat` with a fuel (the same arms and results). -/
+def rootFloatF : Nat → Lean.Expr → Lean.Expr
+  | 0, e => e
+  | k + 1, e =>
+  match e with
   | .letE n t (.letE n2 t2 v2 w nd2) b nd =>
-    rootFloat (.letE n2 t2 v2 (.letE n (t.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2)
-  | .letE n t v b nd => .letE n t v (rootFloat b) nd
+    rootFloatF k (.letE n2 t2 v2 (.letE n (t.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2)
+  | .letE n t v b nd => .letE n t v (rootFloatF k b) nd
   | e@(.app f a) =>
     match a with
-    | .letE n t v b nd => .letE n t v (rootFloat (.app (f.liftLooseBVars 0 1) b)) nd
+    | .letE n t v b nd => .letE n t v (rootFloatF k (.app (f.liftLooseBVars 0 1) b)) nd
     | _ => e
   | e => e
 
+def rootFloat (e : Lean.Expr) : Lean.Expr := rootFloatF (rootFloatNu e + 1) e
+
 /-- `BitVec.zero n` at a literal width is the literal `BitVec.ofNat n 0` (the
 canonical literal form; both reduce to the same value). -/
 def zeroLit (natE : Nat → Lean.Expr) (natLit? : Lean.Expr → Option Nat) (e : Lean.Expr) : Lean.Expr :=
```

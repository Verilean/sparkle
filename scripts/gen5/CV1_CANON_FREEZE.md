# CV1_CANON_FREEZE — C.CV-1 の右辺を `machCanonAp` 正規化に変える（D4 選択肢 1）の型の freeze

Issue `sparkle-gd-w3check`、agent gdw3d。base `par/d4-decision` efa7da8f。文書のみ（Lean をソースツリーに書いていない）。
台帳: FG 104 / T1 54（今回 FG -0 +0 / T1 -0 +0）。C.CV-1 は **行の文の変更**で行数 ±0。条件付き・未計上のまま（補題が未証明のため）。
ユーザー判断（2026-11-01）: D4 = 選択肢 1。これは方針の決定であり、補題が証明済みという意味ではない。回路の出力と保証の範囲は変えない。

## 0. 範囲と禁止事項の確認
* 新しい Lean は新規ファイル（提案名 `Tools/ShippingGen5Cover3Canon.lean`、lakefile への lean_lib 追加のみ）。`Cover3.lean` の既存 `LetQuoteEq` / `rowC_of_reader` は変えない。
* 新しい TRUSTED 境界・law・axiom・sorry は無し。コンパイラ / 共有定義（Elab*.lean、ShippingGen2Defs、T1Hyp*）は編集しない。FG は縮小しない、GenWF は強化しない。
* 台帳の行は 1 行の文を差し替えるだけ（FG 104 のまま）。reviewer の承認が要る freeze（台帳の行の文の変更）。

## 1. 新しい文 `LetQuoteEqC`（完全な型）
`Cover3.lean:693` の `LetQuoteEq` の右辺を `machCanonAp` で包んだもの。他は 1 字も変えない。
```lean
def LetQuoteEqC (d : MachineData) (st : MachRead) : Prop :=
  ∀ (j : Nat) (hj : j < d.ls.length) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) →
    quote d.dom (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.bpos i))
                (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.vpos i)) (d.ls[j]'hj).2
      = machCanonAp (machClose st.insts.size st.kinds.size st.lets.size 0 v)
```
`machCanonAp`（`Sparkle/Compiler/Elab.lean:5013`）は `.app` だけを降り、`Signal.ap (Signal.map f a) b` の `f` の lam 束縛名を `x1 x2 …`、型の forallE 名を `a` にする。束縛名以外（bvar・定数・構造）は変えない。

## 2. 台帳の行 C.CV-1 の新旧の文（行数 ±0）
* 旧（`scripts/gen2/premise_ledger/C_M5dg.md` §8 CV-1、`kjob/fgnext2` 500c0370）:
  `LetQuoteEq (d : MachineData) (st : MachRead) : Prop := ∀ j hj nm kd v, st.lets[j]? = some (nm, kd, v) → quote d.dom (…bpos…) (…vpos…) (d.ls[j]'hj).2 = machClose st.insts.size st.kinds.size st.lets.size 0 v`
* 新: 同じ文で、右辺だけ `machCanonAp (machClose st.insts.size st.kinds.size st.lets.size 0 v)`（上の §1 の `LetQuoteEqC`）。
* 理由: GD_W3CHECK3（08623644）で、`dataOfAt = some d` となる w3 / inst1 の実行で旧文の j=0 が偽（ラムダ束縛名の違いだけ。計算で確認、Lean の反証定理ではない）。同じ実行で新文の等式（`machCanonAp (保存値)` = quote）は真と印字済み。
* 旧文が偽になる実行は、旧文を前提にした定理を適用したときの根拠だけを失わせる。受理済みの定理は壊れない。

## 3. 後続の使い方: `rowC_of_reader_canon`（型）
`rowC_of_reader`（`Cover3.lean:814`）の `hq : LetQuoteEq d st` を `hqC : LetQuoteEqC d st` に替えた版。結論・他の仮定は同一。
```lean
theorem rowC_of_reader_canon {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv (kDOf d) st)
    (hqC : LetQuoteEqC d st) (hnl : LetsNoLoose st)
    (hb : ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length) (hv : ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length) :
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true
```
`rowC_of_reader` が `hq` を使うのは 1 か所（`Cover3.lean:844`、`readsOfQuoteStmt` の引数）だけ。ゆえに証明は、`readsOfQuoteStmt` の前提 `quote … = machClose …` を `= machCanonAp (machClose …)` に替えた版 `readsOfQuoteStmtC`（下の (b)）に差し替えるだけ。`rowC_of_reader` 本体の証明は流用（コピー）する予定。

## 4. 必要な補題の型
すべて下の「§6 scratch」で型として elaborate することを確認した（本体は `sorry`、ソースツリー外）。証明は未実施。

### (a) 可換性: `machCanonAp` と field の取り出し
* (a1) `machClose` との可換（`witness` で `shapePost` の `machField … (machClose … v)` を `machCanonAp` に通すのに使う）:
```lean
theorem machCanonAp_machClose (kI n k d : Nat) (e : Lean.Expr) :
    machCanonAp (machClose kI n k d e) = machClose kI n k d (machCanonAp e)
```
* (a2) `machField` との可換（`dom` が `machCanonAp` で動かないことが条件。`machDom?` が返す `dom'` は `.bvar` か `.const` なので、この仮定自体は `machDom?` の結果に対して別途示す）:
```lean
theorem machCanonAp_machField (dom : Lean.Expr) (hdom : machCanonAp dom = dom)
    (kd : MixedGateBinder) (e : Lean.Expr) :
    (machField dom kd e).map (fun p => (p.1, machCanonAp p.2)) = machField dom kd (machCanonAp e)
```
* (a3) `machPack`（packed の分解）との可換:
```lean
theorem machCanonAp_machPack (dom : Lean.Expr) (hdom : machCanonAp dom = dom)
    (fs : List (Nat × Lean.Expr)) :
    (machPack dom fs).map (fun p => (p.1, machCanonAp p.2)) = machPack dom (fs.map fun p => (p.1, machCanonAp p.2))
```
見込み（確認していない）: `machCanonAp` は `.app` だけを降り、ノード処理は `Signal.ap` / `Signal.map` の定数頭にしか反応しない。`machField` / `machPack` / `machConcatE` / `machBoolBits` / `machLitE` の頭は `Signal.mux` / `HAppend.hAppend` / `Signal.pure` / `BitVec.ofNat` なので、各ノードで恒等になるはず。`machClose` は fvar → bvar と深さだけで束縛名を変えない。いずれも構造帰納法で通ると見込むが、**証明は未実施**。`shapePost` の `body := machCanonAp packed` との接続は既存の `shapePost_pack`（`Tools/Prototype/ReaderFixpointTyped.lean:133`、PROVED 済み）を使う想定。

### (b) 不感性: `readsOfQuoteStmt` がラムダ名の付け替えで変わらない
`readsOfQuoteStmt`（`Cover3:281`）が `hq` から取り出す情報は `LooseOcc 0 (machClose …) b`（束縛されない bvar の位置）だけ。`LooseOcc` は lam / forallE の名前を見ない（`Cover3:26`）。よって不感性の核は次:
```lean
theorem looseOcc_machCanonAp (d : Nat) (e : Lean.Expr) (b : Nat) :
    LooseOcc d (machCanonAp e) b ↔ LooseOcc d e b
```
これを使って `readsOfQuoteStmtC` を `readsOfQuoteStmt` から導く（証明はコピー + `hq` の差し替え）:
```lean
def ReadsOfQuoteStmtC : Prop :=
  ∀ (dom : Lean.Expr) (nDecl kI n k : Nat) (bpos vpos : Nat → Nat) (okP : Nat → Bool)
    {s : SType} (t : Term s) (v : Lean.Expr),
    PhInRange nDecl kI n k v →
    (∀ j, bpos j < nDecl + kI + n + k) → (∀ j, vpos j < nDecl + kI + n + k) →
    (∀ b, ¬ LooseOcc 0 v b) →
    quote dom (fun j => inputExpr (nDecl + kI + n + k) (bpos j))
      (fun j => inputExpr (nDecl + kI + n + k) (vpos j)) t = machCanonAp (machClose kI n k 0 v) →
    (∀ p, MentionPos nDecl kI n k v p → okP p = true) →
    Tools.ShippingMachineRef.reads (fun j => okP (bpos j)) (fun j => okP (vpos j)) t = true

theorem readsOfQuoteStmtC : ReadsOfQuoteStmtC
```
`readsOfQuoteStmt` の中で `hq` が使われるのは `LooseOcc 0 (machClose …) b` を得る 1 か所（`rw [← hq]; exact hl`）だけ。`reads_of_quote_loose` の呼び出しは `t` と `dom` だけに依存し、`v` の名前には依存しない。

## 5. 未確認の点（条件付きとして明示）
* 補題 (a1)(a2)(a3)(b) は**型が elaborate することだけ確認、証明が通るかは未確認**。通らなければ C.CV-1 の新文は条件付きのまま（その場合は decision で戻す）。
* 本番の fuel（実 pipeline が `machineShape?` に供給する値）は未確認。GD_W3CHECK3 の `st` は `machineShape?` の複製（body 一致 true）由来。
* loop 経路（`lets.push` の path 2 / 3）は未実行。確認済みなのは path 1（w3）と path 4（inst1）のみ。
* `machCanonAp` の冪等性は未証明（この freeze の補題は冪等性を必要としない設計。使うことになったら別 freeze）。
* `LetQuoteEqC d st` 自体が全 reader 到達 run で真かは未確認（w3 / inst1 / 対照 w3c の計算で真と確認しただけ）。witness 証明 `letQuoteEqC_witness`（W3 本体）は別単位で、本 freeze の範囲外。
* mutant / 反例について: GD_W3CHECK2/3 の反例は reader 複製上の計算による棄却であって、Lean の反証定理ではない。

## 6. scratch での型確認（ソースツリー外）
* `Tools.ShippingGen5Cover3` を import した scratch で §1 `LetQuoteEqC`、§3 `rowC_of_reader_canon`、§4 の各補題型を `sorry` 付きで書き、`kjob lake env lean` が **エラー無し（sorry 警告のみ）** で elaborate。
* w3 / inst1 で新文の等式が真: GD_W3CHECK3（08623644、reviewer が範囲限定で承認済み）で `machCanonAp(stored) = quote` が true、対照 w3c も true と印字済み。今回再計算はしていない。
* 本 freeze の承認後に Lean を書く。承認後の実装は新規ファイルに置き、`sorry` / axiom は使わない。補題が証明できなければ、その時点で decision に戻す。

## 7. 承認を求める点（reviewer）
1. 台帳 C.CV-1 の行の文を §2 のとおり変えること（FG 104 のまま、行数 ±0）。
2. §1 / §3 / §4 の型。
3. 未確認の点（§5）を条件付きとして C.CV-1 に残す扱い。

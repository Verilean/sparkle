# GD_W3_WITNESS — W3 本体 `letQuoteEqC_witness` の型と証明の筋道（Lean 実装前）

Issue `sparkle-gd-w3check`、agent gdw3f。base `par/w3-base` 0501ea26。文書のみ。新しい前提なし（台帳 FG 104 / T1 54、今回 FG -0 +0 / T1 -0 +0）。共通ルール 14 により、承認済み文（LetQuoteEqC, freeze 7f45fb24）の中で前提を増やさない単位なので review に出さない。C.CV-1 を消せるかの判定は reviewer。

## 1. 完全な型（新規ファイル `Tools/ShippingGen5GDW3.lean`、namespace `Tools.ShippingGen5GDW3`）
`hbr` は G1 / W1 と同じ inline 仮説（C.CV-4。仮定のまま、ここでは証明しない）。
```lean
theorem letQuoteEqC_witness_from
    (hbr : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp → ∃ n, machineShapeF n false [] E senv true = some (some sp))
    {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (hd : dataOfFrom lvl E senv sp tin fl = some d) :
    ∃ n p en st0 env st1 st v, StateSideWitness E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st ∧ LetQuoteEqC d st

theorem letQuoteEqC_witness   -- 上と同じ結論、hd : dataOfAt lvl E senv sp = some d
```
* 結論は G1 の `StateSideWitness`、W1 の `ShapeAgree d st`、W3 の `LetQuoteEqC d st` が **同じ `st`**（確認 (d)）。`shapeAgree_witness(_from)`（GDCover1）の結論に `LetQuoteEqC d st` を足した形。
* `LetQuoteEqC` は `Tools/ShippingGen5Cover3Canon.lean` の定義（承認済み、954bc981）をそのまま使う。

## 2. 証明の筋道（`shapeAgree_witness_from` の witness `st` に対して）
`w : StateSideWitness`（`shapePost true p (shapeMid …) st v = some sp`、`shapePre … = some p`、`sp.layout.lets = st.lets.size`、`sp.layout.slots.length = st.kinds.size`）と `dataOfFrom_sound`（`d.shape = sp`、`d.ok`、`sp.body = quote d.dom … d.packed`）から。
1. `shapePre_outs_ne` で `p.outs ≠ []`、`shapePost_pack` で `dom' lfs outF slotF P`: `st.lets.toList.mapM (machField dom' kd (machClose … v)) = some lfs`、`machPack dom' (lfs ++ outF ++ slotF) = some (w,P)`、`sp.body = machCanonAp P`。
2. `peel`（`typed_letsAlias` と同じ呼び方）: 各 let `j` で `machCanonAp lfs[j].2 = quote d.dom bB bV (d.letFields[j]).2`（`lfs.length = d.letFields.length` は `ShapeAgree.lets` と `mapM_get`）。
3. `mapM_get` で `lfs[j] = machField dom' kd (machClose … v)`（`st.lets[j]? = some (nm,kd,v)`）。
4. **kind と sort の結び付け**（Bool let の確認 (b)）: `sp.binders = A ++ st.lets.toList.map (nm,kd)`（`shapePost` の `binders`。新補題 `shapePost_binders`）。`d.ok` の `layout.lets = letBs.length` で `A.length = nIn + |ss|`。`ok_letsTyped`（`LetsTyped`）から `d.K (nIn+|ss|+j) = some (d.ls[j]).1`。よって `sortOf kd = some (d.ls[j]).1`。
5. 場合分け:
   * `kd = .bits w`: `machField = (w, machClose … v)`、`d.ls[j] = ⟨.bits w, t⟩`、`toField = ⟨w,t⟩`。2 の等式から `quote … t = machCanonAp (machClose … v)`。
   * `kd = .bool`: `machField = (1, machBoolBits dom' (machClose … v))`、`machCanonAp_machBoolBits`（承認済み (a)）で `mux` の第 3 引数が `machCanonAp (machClose … v)`。`d.ls[j] = ⟨.bool, t⟩`、`toField = mux t 1 0`、`quote (mux t _ _)` の同じ位置が `quote t`。`Expr.app` の単射（`peel` と同じ `injection`）で `quote t = machCanonAp (machClose … v)`。`dom'` と `d.dom` が同じであることは**使わない**（リテラル引数は比べない）。
   * `kd = .domain`: `sortOf = none` で矛盾。
6. `quote` の束縛数: `d.shape.binders.length = kDOf d + |insts| + |kinds| + |lets|`（`d.ok` の行と `ShapeAgree`: `nIn ≥ |insts|`、`ss.length = kinds.size`、`ls.length = lets.size`）で `LetQuoteEqC` の `inputExpr` の引数に一致させる。

## 3. 範囲（loop path 2/3、本番 fuel）
* **loop path 2/3 は範囲に含まれる**（`lets.push` の経路ごとの場合分けをしないため）。証明は最終 `st` の `shapePost` の成功と `dataOfAt` の構造検査だけを使い、`st.lets` がどの経路で作られたかを見ない。経路 2/3 の `Signal.loop` 本体で作られた let も、最終 `shapePost` を通った `st` の一部であれば同じ式で扱われる。**ただしこれは経路を実行して確かめた結果ではなく、証明の構造からの読み取り**。Lean の定理が通れば、定理の仮説（`hbr`, `h`, `hd`）の範囲で全経路に効く。
* **本番 fuel は範囲外（仮説 `hbr` に残る）**。`hbr` は C.CV-4 のままで、`n` は存在量化。実 pipeline の fuel が `hbr` の `n` を与えるかはこの単位では確かめない。
* 範囲に含まれない: `dataOfAtP`（G3 / D3 の carrier）、`FullInv` / `LetsNoLoose`、`dataOf` と `dataOfAt` の同一視、`hbr` の証明。
* 反例の扱い: GD_W3CHECK3 の計算反例（binder 名）は旧 `LetQuoteEq` に対するもので、この定理は新文 `LetQuoteEqC` を示す。mutant は signature / defeq での棄却であって意味的反例ではない。

## 4. 確認 (a)〜(e) の状態（roadmap §4 W3）
| | 内容 | 状態 |
|---|---|---|
| (a) | 冪等補題 | 不要（`LetQuoteEqC` は `machCanonAp` 付き。D4 選択肢 1） |
| (b) | Bool let | §2-5 の場合分けで Lean 証明済み（`letQuoteEqC_of_post`、Pod build）。Bool let は `machBoolBits` の条件引数への injection で `quote t = machCanonAp (machClose … v)` |
| (c) | C.CV-1 の binder / domain の一致 | `LetQuoteEqC` と `rowC_of_reader_canon` は承認済み（954bc981）。台帳行の原文との再読は reviewer |
| (d) | W1 と同じ `st` | 結論の型で同一（§1） |
| (e) | carrier | `dataOfAt`（W1 と同じ）。`dataOfAtP` は範囲外 |
C.CV-1 を消せるかは、Lean が通り、clean build と reviewer の判定が済んでからの話で、この文書では条件付き・未計上のまま。

## 5. Check（他の単位と同じ形）
`Tests/Gen5/GDW3Check.lean`（新規）: 独立 Expected TYPE、正負対照、mutant（signature/defeq 棄却）、closure（sorryAx 等が無いこと）、`#print axioms` が標準のみ、COUNTS 行。

## 6. 実装結果（Lean、Pod の target build。clean build は coder）
* 新規 `Tools/ShippingGen5GDW3.lean`（`shapePost_binders`、`letsTyped_get`、`machCanonAp_machBoolBits'`、`letQuoteEqC_of_post`、`letQuoteEqC_witness_from`、`letQuoteEqC_witness`）、`Tests/Gen5/GDW3Check.lean`、lakefile に lean_lib 2 件。共有定義・既存ファイルは未変更。sorry / axiom / native_decide なし。
* `letQuoteEqC_of_post` の仮説は `p.outs ≠ []`、`shapePost` の成功、`d.shape = sp`、`d.ok`、`d.shape.body = quote …`、`ShapeAgree d st` のみ。経路（`lets.push` の 4 箇所）は見ない。
* `machCanonAp_machBoolBits'` は `dom` が `machCanonAp` で動かない仮定を要らない形（右辺は `machBoolBits (machCanonAp dom) (machCanonAp e)`）。承認済みの `machCanonAp_machBoolBits`（`hdom` 付き）は使っていない。
* Check の `checkExpected` は `hbr` の binder（`Cv4` の再記述）と結論（`LetQuoteEqC` と `ExpLetQuoteEqC`、`StateSideWitness` と `ExpSswBody`）の一致を、定義の展開を挟んだ isDefEq で受理している（Check の出力に "accepted by isDefEq (NOT syntactic)" と出る）。構文的一致ではない。
* 未確認のまま: `hbr`（C.CV-4）の証明、本番 fuel が `hbr` の `n` を与えること、`dataOfAtP`、`FullInv` / `LetsNoLoose`、実行（reader を走らせた）での経路 2/3 の確認。C.CV-1 を消す判定は reviewer。

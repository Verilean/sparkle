# M4 再開の供給調査: B.F-4 `hS` / B.F-8 `ChildRunN` / 非 machine route の D.E-12 `hno`/`htop`

- Issue: `sparkle-gen4-fallback-supply`（ユーザー 2026-11-03「M4を再開して」）。agent rt150。base: par/fb-resume = 4519e2fb。
- 種別: 調査文書のみ（Lean のソースは編集していない。Lean の build も elaborate もしていない。§6）。
- 台帳: FG 92 / T1 57（今回 0/0）。この文書は台帳の数を変えない。§5 の「見込み」は未受理の見込みで、受入済みではない。
- 読んだもの: `scripts/gen2/GENERAL_SPEC.md`、`Tools/ShippingGen2Defs.lean`、`scripts/gen2/premise_ledger/B_M4.md` と `D_M5t2.md`（par/fg-ledger-sync e5025b28）、`scripts/gen4/FALLBACK_SUPPLY_FREEZE.md`、`Tools/ShippingGen4FbFragRun.lean`、`Sparkle/Compiler/Elab.lean`（entry 5252-5700, 2200-2260, 2934-2975, 6590-6640, 8929-8935, 9120-9135）、`Sparkle/IR/Machine.lean`（`closeInsts`, `designWith`）、`Sparkle/IR/ModuleNameCheck.lean`、`Tools/ShippingDesignWriterRun.lean`、`Tools/ShippingLegacySemContract.lean`、`Tools/ShippingLegacySemMemoWalk.lean`（`outer_miss`）、`Tools/ShippingMemoInv.lean`、`docs/parallel/G2-legacy.md` §5、`git show 7feca8b0:scripts/gen5/AUD_UA7D_FREEZE.md`、`git show kjob/g4gate-g3c:Tools/ShippingGen4FirstLeaf.lean`（59b68658）。
- 「見つからなかった」は、上のファイルを読んだ範囲で供給元・経路が見つからなかったという意味で、不可能・導出不能とは言っていない。mutant は signature/defeq での棄却であって意味的反例ではない。

## 0. 結論（先に）

1. **B.F-4 `hS`**: first-gate fragment については、`hS` は gate 側の既存定義で**定義により払える形**がある。`FirstLeaf.ifaceOf`（kjob/g4gate-g3c@59b68658, `Tools/ShippingGen4FirstLeaf.lean`）は `S := fun _ => gateS (firstBs …) (ofF n fe) …` と**定義**し、`firstFn_eq_gateVal : firstFn … = g4_gateVal …` は `rfl`、`gateS` と `g4_gateVal` は同じ式。`firstLeaf_childShips` は `hS` 型の仮説を持たない。したがって FB-22 の `hS` の内容は「パッケージの `S` が `firstFn` と一致する」ではなく、「**interface として `ifaceOf` を選ぶ**（`Q f.decl = some f.ifaceOf`、台帳 B.G-9 の `hQ`）」に移る。これは払ったのではなく**付け替え**（B.G-9 に既にある行）。文の変更なので freeze が要る（§5）。**Pkg（T1Hyp.pkg）の `q.S` と `firstFn` の対応**を示す経路は見つからなかった（`T1Hyp.defines` は `MachineDefines` を要求するので、first-gate 宣言には `Pkg` が無い。§1.2）。
2. **B.F-8 core `ChildRunN`**: first-gate fragment 以外で `ChildRunN`（core `raw`）を実 run から払う供給元は見つからなかった。legacy 成功には `LegacySem` が要り、その中心の `ReachesInline` は**現行コンパイラでは cacheable な呼び出しで証明できない**と `Tools/ShippingLegacySemContract.lean` と `docs/parallel/G2-legacy.md` §5 が書いている（expression cache の shim の変更が要る）。memo hit は K4（nested で `childCache` に無い memo entry の存在）が未証明。→ **供給可否は未決。コンパイラ変更が要るかはユーザー判断の材料（§4）**。
3. **D.E-12 非 machine route**: outermost の core run（`Start` は depth 0、E5 が cache/memo を空にする）では、route は {gate（certified / mixed）, machine, R4→legacy} で、**memo hit は outermost では起きない**（`outer_miss`、ただし `RefLawsM` が前提。§3.2）。`htop` は全 route で `CircuitM.init (ofDecl declName)` から構成上成り立つように読める（定理は見つからなかった）。`hno` は「子の design に親と同名のモジュールが入らない」で、**acyclic な呼び出しグラフの下で成り立つように読める**が、acyclicity を run から出す補題は見つからなかった。**反例は見つからなかった**（scratch 未実施、§6）。
4. **台帳の見込み**（§5）: B.F-4 = 条件付き −1（freeze 承認と B.G-9 の `hQ` に依存。受入済みは 0）、B.F-8 = 0、D.E-12 の非 machine 分 = 0（移動した義務で、まだ行ではない）。

## 1. B.F-4 `hS`

### 1.1 正確な文（Lean から写した）

`Tools/ShippingGen4FbFragRun.lean`（4519e2fb）。binder 名 `hS`、`synthesizeCombinational_fragment_childRunN` の仮説:
```lean
(hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs dn names n).filter fun x => x.2 != .domain) →
        f j = Tools.ShippingFirstGateChild.firstFn dn names n fe (vals j))
```
`{S : (Nat → List Nat) → List (Nat → Nat)}` は定理の暗黙引数（自由）。`combChildRunN_of_childFnR` では `firstFn …` が `F`、`firstBs …` が `bsC` の一般形。

**閉包（どの run・どの reach の上の全称か）**: `hS` は run にも `Reach` にも依存しない。`S` が自由変数で、`vals` `f` `j` だけを全称にする。run `hr`・`entry`・`hwf`・`hn` は別の仮説。つまり `hS` は「この `S` について」の文で、`S` がどこから来るかは文に無い。結論は `ChildRunN ch dsn m b (firstBs …) [out] S`（`ChildShips q` の `q.S` の位置）。

### 1.2 供給元の調査

| 候補 | 場所 | 払えるか |
|---|---|---|
| `FirstLeaf.ifaceOf` の `S` 定義 | kjob/g4gate-g3c@59b68658 `Tools/ShippingGen4FirstLeaf.lean`（`ifaceOf`、`firstFn_eq_gateVal`） | `S` を **定義** すれば `hS` の結論は `rfl` 層（読んだだけ、elaborate していない）。`firstLeaf_childShips`（同ファイル）は `hS` を持たず、`RealChildA O f.decl y`（= `synthesizeCombinational` の実 run）と `entry` から `ChildShipsI f.ifaceOf n y.1 y.2` を出す |
| `T1Hyp.pkg` の `q.S` | `Tools/ShippingGen2Defs.lean:195-204` | `T1Hyp.defines` が `MachineDefines … c q.d.shape` を要求するので、first-gate 宣言（`machineShape?` を経由しない route 1）には `Pkg` が無い。`q.S` を fragment の `firstFn` に結ぶ補題は見つからなかった |
| GENERAL_SPEC の `Pk declName = some p`（FG の `Pk`） | FG の ∃ 側 | `Pk` が fragment 宣言にどんな `p` を与えるか、この調査では見つからなかった |

つまり FB-22 の `hS` は、**fallback 側が `Pkg` の `S` を前提にしていた**から現れた仮説で、gate 側の `ChildIface`（`S` を構成で持つ）を使えば現れない。足りない事実を Lean の型で書くと（これは新しい前提ではなく、B.G-9 の既存の `hQ` の型）:
```lean
-- 台帳 B.G-9（ShippingGen4FirstLeaf.lean `firstLeaf_shipsResI`）
hQ : Q f.decl = some f.ifaceOf
```
**証明の道筋と大きさ**: 新規ファイルに、FB-22 の結論を `ChildShipsI f.ifaceOf n b design` の形で再述する橋（`firstLeaf_childShips` を実 run `hr`（`b` は core の post-processed）に当てる。`b = dropZeroWidth raw ∨ b = mergeChecked …` の PPRel 腕は FB-22 の `FbPPRun` が既にある）。小さい（FB-22 と同程度の 30〜80 行）。ただし `firstLeaf_childShips` は `RealChildA`（core の post なし `y`）に対して述べ、FB-22 は PPRel 後の `b` を扱うので、両者の `y` が同じ run の同じ post-processed 結果であることの確認が要る（読んだだけで未確認）。

### 1.3 `hS` が払えない側

非 fragment（machine shape があり closeLets/closeInsts が拒否した宣言、legacy へ落ちる）には `Pkg` があり `q.S` は source 由来の関数。`ChildRunN` の `q.S` との一致が必要で、それは §2（legacy の意味保証）の内容。`hS` という独立の文では払えない。

## 2. B.F-8 core `ChildRunN`

### 2.1 正確な文

`Tools/ShippingGen4FbDzRun.lean`（4519e2fb）の `childRunN_dz_instFree`（:17）、`childRunN_dz_postReady`（:75）の仮説:
```lean
h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S      -- core の raw
hbody hin hout hwe : out.body = raw.body ∧ …                      -- 後処理の形
hf : instFree raw.body   (または hpr : PostReady raw k, hk : 0 < k)
```
`ChildRunN`（`Tools/ShippingGen2Defs.lean:78`）= `SeqChildRunN … ∨ CombChildRunN …`。閉包: `ch₁ dsn₁ n raw bsC outsC S` は定理の自由変数。`CombChildRunN` 側は `∀ T ins s vals, … ResetN dsn n mc s → ∃ envs, RunOn … = some envs ∧ …`。run や `Reach` は文にない（`raw` が具体的にどの run の結果かを文は知らない）。

### 2.2 供給元

| route | 候補 | 結果 |
|---|---|---|
| first-gate fragment | FB-22 `synthesizeCombinational_fragment_childRunN`（4519e2fb）。gate 側は `firstLeaf_childShips`（59b68658） | **post-processed `b` に対して**は払える（§1 の条件の下）。**core `raw` に対して**は、FB-22 は `raw` の `ChildRunN` を作らず、`b` を直接作る |
| gate（mixed）葉 | `gate_combChildRunN`（59b68658 ほか） | gate 側の台帳（G-1〜G-9）。この調査の外 |
| machine | T1 側（`ChildKeepsInv` 等） | T1 台帳 |
| legacy（R4 の落ち先） | `legacyTail_keepsInv`（FbTailInv, 保持系）| 保持（Keeps）のみ。**意味（ChildRunN）は見つからなかった**。`LegacySem`（`Tools/ShippingLegacySemContract.lean`）は「STATED, NOT PROVED」 |
| memo hit | `memoInv_hit`（`Tools/ShippingMemoInv.lean`）| 述語 `Φ` を取る一般補題。`Φ` を `ChildRunN` にする `ArmObligations` / `MemoSound` は「statements only」（`ShippingMemoInv.lean` header）。K4 未証明 |

### 2.3 足りない事実と、コンパイラ変更が要るか

legacy: `Tools/ShippingLegacySemContract.lean` の「Premises that remain」の `ReachesInline rec ctx e` は、「expression cache（entry が常に有効にする）がある状態では **cacheable な呼び出しに対しては証明できない**（shim が `IO.Ref` の map の値を検証せずに返す。`Returns` は world を言わない）」と書いてある。`docs/parallel/G2-legacy.md` §5 の「Requested changes」はコンパイラの shim（`Rec.translateExprToWireCached` と let/loop/single-output の各 cache）を `cacheLookupValidated` + `recordTranslation` に変えることを求めている。Lean の型で書くと、足りない事実（新しい仮定の形で）:
```lean
-- ShippingLegacySemContract.lean（premise 1）
ReachesInline rec ctx e   -- 現行コンパイラのままでは cacheable な e に対して証明できないと header が言う
```
この調査では、これを**新しい仮定にする**か**コンパイラ変更で消す**かは決められない（どちらも禁止事項または reviewer/ユーザー承認の対象）。**払える/払えないの判断はしない**。legacy 成功全体（`ChildRunN` の `S` との一致）は、`LegacyDom`（input、certified fragment、unfolding の 3 constructor だけ。FALLBACK_SUPPLY_FREEZE.md U4）より広い式（instance、register、memory、loop、multi-output）を含む宣言に対しては、供給元が見つからなかった。

大きさ: 現在の `LegacyArm` は 1 constructor（inline unfold）で、全 legacy handler を足すには constructor が handler 数だけ要る。本調査では handler 数を数えていない。

## 3. D.E-12 `hno` / `htop`（非 machine route）

### 3.1 文

`Tools/ShippingDesignWriterRun.lean:119` の `writer_prints_endpoint_artifact` の仮説:
```lean
(hno : ∀ x ∈ D.modules, x.name ≠ raw.name)
(htop : D.topModule = raw.name)
```
`hcore : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w2`。AUD_UA7D_FREEZE.md（7feca8b0, 承認）の `AuditE12G` は、`Reach declName`、`P declName = some q`、`MachineTaken … n declName q.d.shape raw D` を前件に足した guard 付き。非 machine route はその外で、この M4 の義務。

### 3.2 route ごとの読み（Elab.lean の読解。定理ではない）

outermost core run（`synthesizeCombinationalCoreWith`, depth 0）:
- `CircuitM.init (ofDecl declName)` が `module := Module.empty (ofDecl declName)` と `design := Design.empty (ofDecl declName)`（`topModule := ofDecl declName`, `modules := []`）を作る（Builder.lean:59-62）。route 1 の `synthesizeCertified` / `synthesizeMixedCertified` と legacy の `bindInputsLegacy … finishSynth` は、この `CircuitM.init` から `finishSynth` で終わる。`finishSynth` は `(addClockResetIfSequential module).finalize` と `finalCircuitState.design` を返す。`topModule` を変更する箇所は Elab.lean 内で見つからなかった（grep: `topModule` は Builder.lean の `init` だけ）。→ **`htop` は構成上成り立つように読める**（`finalize`/`addClockReset` が `name` を保つことは確認していない）。
- `hno`（design の module に raw と同名が無い）: design には `addModuleToDesign` で子とその transitive module だけが入る（Elab.lean 6620-6630。`existing.contains` で重複は足さない）。子は `synthesizeCombinational name`（`name` は呼ばれた宣言）の結果。親と同名が入るのは、子の名前または子の design が `ofDecl declName` を持つとき、すなわち**呼び出しの循環**か、`ofDecl` の衝突（`encode (.decl n)` が単射でない場合。単射性はこの調査では読んでいない）。循環は、親が `sparkleChildCache` にも memo にも未登録のまま再入するので、再帰が `sparkleSynthDepthLimit` に当たって throw する（Elab.lean 5465-5466）ように読める。**成功 run では循環が無い**を run から出す補題は見つからなかった。→ `hno` は「成り立つように読めるが、証明の道筋は acyclicity の補題（depth-limit が throw する経路）で、未供給」。
- machine route（closeInsts）: `Machine.closeInsts` が `noInstOfB m.name`（design 内のモジュールが親を instantiate しない）を検査する（Machine.lean:423）。`noRawBelow_of_closeInsts`/`noRawBelow_of_coreRun`（74343ad8, agent build のみ）が `NoRawBelow` を出す。これが machine route の guard 済み分（台帳 D.D-7）。
- **memo hit**: outermost では `sparkleSubModuleCache` が depth 0 の入口で `{}` にされてから memo を読む（Elab.lean 5540 のリセットの後に、`synthesizeFromConst` 内の 5334-5338）。`outer_miss`（`Tools/ShippingLegacySemMemoWalk.lean:495`）がこれを定理にしているが、**`L : RefLawsM mref cref`（`Laws` とは別の bundle、`mval`/`memoGet`/`memoSet` の heap law）を前提にする**。`Laws`（`O` と `T` の 2 field）にこの bundle が入るかは、新しい law になるかどうかの判断が要る（FALLBACK_SUPPLY_FREEZE.md §0 R3 の (a)/(b)）。この調査では決めない。

nested（子）run では memo hit が起こりうる（K4）。ただし E-12 は FG の top の core run についての補助事実で、子の `hno`/`htop` は子の `ShipsRes`/`ChildShips` 側（`ChildShips` の `Dc`）の別の条件。

### 3.3 反例

**意味的反例は見つからなかった**（静的な読解のみ。scratch は実施していない、§6）。成り立たない可能性が残る箇所:
1. `ofDecl` の非単射（異なる宣言が同名 module になる）: 読んでいない。`ModuleNameCheck.check` は「別の raw 名が正規化後に衝突しない」を検査するが、**同じ raw 名の repeated use は許す**（ModuleNameCheck.lean:15, 21-23）ので、`finishSynth` の成功は `hno` を含意しない。
2. `Machine.designWith` は同名の module を足さない（`acc.any (·.name == c.name)` で skip）。子の design に親と同名の module が元から入っていると、親と同名のものが design に残る。これは 1 の裏。

## 4. ユーザー判断の候補（この調査では決めない）

- (a) legacy の意味保証のために `Rec.translateExprToWireCached` 系の shim を変更する（コンパイラ変更、禁止対象）。
- (b) `RefLawsM`（memo の heap law）を `Laws` に加える、または memo-miss を別の方法で出す（新 law）。
- (c) `ofDecl` の単射性を TRUSTED にするか証明するか。
判断資料（影響・選択肢・コスト・推奨・可逆性）は、reviewer が (a)〜(c) の範囲を決めた後に別文書で書く。判断しない場合: B.F-8 は未供給のまま。

## 5. 台帳の見込み（R0 行単位。束ねた行の部分供給は 0。最終定理の仮説に既に消した行を戻さない）

| 行 | 現状 | 見込み | 条件 | 受入済みの変化 |
|---|---|---|---|---|
| B.F-4 `hS` | 未供給の義務 | **条件付き −1**（FG 側） | (1) FB-22 の結論を `ChildShipsI f.ifaceOf` の形に再述する freeze が承認される、(2) その結果 `hS` が仮説から消える、(3) `hQ`（B.G-9）が増えないこと。B.G-9 の行は既存で、数は動かさない | 0（今回） |
| B.F-8 `ChildRunN` | 未供給の義務 | 0 | fragment 以外の供給元が見つからなかった。legacy は §2.3、memo は K4 | 0 |
| D.E-12 非 machine 分 | M4 の義務に移動（7feca8b0） | 0 | `hno` の acyclicity 補題と `RefLawsM` 前提（§3.2）が決まるまで行を数えない | 0 |
| 新しい仮定 | — | この調査が増やす数 0 | `RefLawsM` / `ofDecl` 単射 / shim 変更は上の判断が出るまで行にしない | 0 |

台帳: FG 92 / T1 57（今回 FG -0 +0 / T1 -0 +0）。条件付き台帳: B.F-4 の −1（上記条件、未受理）。

## 6. 検証と限界

- この調査は文書のみ。Lean のソースを編集していない。**Lean の build も scratch の elaborate も実施していない**（この worktree の base 4519e2fb には gate の `firstLeaf_*`（59b68658）が無く、§1 の `rfl` 層の主張は読解のみ）。elaborate で確かめるなら、gate の branch を import できる base が要る。
- §3 の route ごとの読解は `Sparkle/Compiler/Elab.lean` の読みで、定理ではない。反例が見つからなかったことは成立の証拠ではない。
- 数字（行数・行番号）は 4519e2fb の Elab.lean に対するもの。

## 7. 次（reviewer の番になりうる点）

1. §1.2 の再述 freeze を起こしてよいか（B.F-4 を B.G-9 へ付け替える。台帳の前提の付け替えなので reviewer の承認が要る）。
2. §4 の (a)〜(c) のどれを M4 の範囲として扱うか（新 law / コンパイラ変更の判断はユーザー）。
3. `hno` を FG の M4 義務の行にするか（行の追加は台帳の変更で、承認が要る）。

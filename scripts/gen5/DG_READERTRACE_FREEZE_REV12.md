# DG-READERTRACE freeze rev12 — U-R8 (`instSStep`): 新しい名前付き条件 `InstSFieldsDet`（+1 の候補）の判断依頼。Lean なし、未 elaborate

Issue `sparkle-gen5-dg-readertrace`。Base: `kjob/rt15`（rev11 `04f680b7` への reviewer 指摘 (1)(2) を反映した版。U-R7 まで: `a446824c`）。`DG_READERTRACE_FREEZE_REV5.md` の単位表 U-R8、`..._REV10.md` の続き。
用語: 「見つからなかった」は「この調査で辿った経路では見つからなかった」の意味で、不可能・導出不能の主張ではない。mutant は signature / defeq での棄却で意味的反例ではない。条件付きの結果は中間結果。

**この rev12 が台帳に与える差分: なし**（現在値 **FG 103 / T1 54**。根拠: 台帳 §12 の par/fg-ledger-sync 3b459613 = FG 102、par/t1-ledger-sync 5e915142 = T1 54、SigTyClosed の登録 4d6b9719 で FG +1 → FG 103。今回 FG -0 +0 / T1 -0 +0）。§2 の `InstSFieldsDet` の +1 は**承認前の候補**で現在値には入れていない。案 A が承認された場合は FG 103 → 104（FG +1 / T1 差分 0）。承認までこの条件を Lean に置かない。（rev11 の「FG 102」は SigTyClosed 計上前の値で誤り。FG 107 / T1 58 は午前の旧表示。）

## 0. 何が止まっているか（前提知識なしの説明）
`instSStep`（構造体を返すハードウェアモジュールの呼び出し）は、同じモジュール `c` を同じ引数の wire `js` で 2 回呼ぶと、2 回目は 1 回目の出力を共有する（dedup）。共有した出力は `machInstOut (k0 + i)`（`i < fields.length`）で、これが範囲内（`< insts.size`）であることを trace が要る。1 回目が登録した行の数 `fields₀.length` と 2 回目の `fields.length` が等しくないと、`k0 + fields.length ≤ insts.size` が言えない。`fields` は `machOuts? senv (instRes ty args)` が返す。`instRes ty args` の**結果型の先頭定数**が引数 `args` に依存しなければ両者は等しい（`machOuts?` は先頭定数の `senv.fields` を見るだけ）が、結果型の先頭が束縛変数だった場合は引数で変わりうる。結果型の先頭が束縛変数でないことは、宣言された型が型付けされている（カーネルの事実）から出るはずだが、この development は `Lean.Environment` をモデル化しておらず、この調査で辿った経路では供給元が見つからなかった。

## 1. 前提なしで進められる部分（rev10 と同じ扱い。承認済みの文の中）
```lean
-- Inst1Ph は既存の Inst1Agrees(T1L-51)から補題で出ている(ace83337: inst1Ph_of_agrees)
theorem instRes_ph (hI : Inst1Ph) {L : Nat} : ∀ (args : List Lean.Expr) (ty r : Lean.Expr),
    NoPh ty = true → BvarLt L ty = true → (∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true) →
    instRes ty args = some r → NoPh r = true ∧ BvarLt L r = true
```
`PhPre instS` は `NoPh ty ∧ BvarLt (env.length + nDecl) ty` を既に持つ（U-R4e2 の `machInstCallS?_ty_ph` と `bvarLt_mono` から dispatch 側が渡す）ので、`SigTyPh` は `instS_trace` の仮説に出てこない。`instSArg` の fold は U-R7 の `instFold_trace` と同形（名前の式だけ違う）。`resTy.getAppArgs` の Ph は `phArgs_getAppArgs`（Reg）。

## 2. 新しい名前付き条件（承認前の候補。Lean に置かない）
```lean
def InstSFieldsDet (senv : StructEnv) : Prop :=
  ∀ (c : Lean.Name) (kinds : List MixedGateBinder) (ty : Lean.Expr) (args args' : List Lean.Expr) (r r' : Lean.Expr)
    (o o' : Option Lean.Name) (fs fs' : List (String × MixedGateBinder)),
    senv.instS c = some (kinds, ty) → instRes ty args = some r → instRes ty args' = some r' →
    machOuts? senv r = some (o, fs) → machOuts? senv r' = some (o', fs') → fs.length = fs'.length
```
（rev0 / rev1 で `PhFacts` の一員として既に型を書いていたものと同じ。domain: `structEnv env₀` の `instS` 表の全ての `(c, kinds, ty)` と、その `ty` に対する任意の 2 つの引数列。）
* 台帳の扱い（候補）: `SigTyClosed` と同じく C0 の共有環境の事実で、**FG +1**（DG-ENV `sparkle-gen5-dg-env` と配置を同期。`EnvTypesFVarFree` / `SigTyClosed` とは別の名前付き条件）。T1 に数えるか FG に数えるかは reviewer 判断。
* 使い方: `instSStep` の dedup 腕だけ。miss 腕（新しい行の追加）は `GroupsPh` の新しい行の witness が呼び出し自身の `kinds, ty, args, resTy, ctor, fields` で済むので条件を使わない。

## 2b. `SigResHeadConst` と `InstSFieldsDet` の論理的関係（案 B の説明。Lean では未証明）
* 想定する関係: **`SigResHeadConst` ⇒ `InstSFieldsDet`**（`SigResHeadConst` の方が強い条件、`InstSFieldsDet` の方が弱い）。理由: `machOuts? senv r` は `r` の先頭定数の `senv.fields` を見るだけ、という §0 の観察（この文書では未 elaborate、Lean で証明する単位になる）。先頭定数が `args` に依らなければ `fs.length = fs'.length`。
* 逆 `InstSFieldsDet` ⇒ `SigResHeadConst` は**成り立たない**（成り立つとは主張しない）: 先頭が束縛変数で `args` ごとに別の構造体になっても、それらの field 数が偶然等しければ `InstSFieldsDet` は真で `SigResHeadConst` は偽。mutant ではなく構成の見取り図で、意味的反例を Lean で作ったものではない。
* したがって案 B は「より弱い形」ではなく「**より強いが根拠の説明が単純な形**」への取り替え。以前の「弱い形に強める」の表現は撤回する。
* 追加負担: A = 条件 1 個（`InstSFieldsDet`）、その使い道は dedup arm のみ。B = 条件 1 個（`SigResHeadConst`）に加え、**`SigResHeadConst → InstSFieldsDet` の補題を Lean で証明する単位が 1 つ増える**（`machOuts?` の先頭定数の読み出しの議論）。条件自体は B の方が真であることの根拠（カーネルの型付け）を言いやすいが、この development は `Lean.Environment` をモデル化していないので、どちらも「真である」とは主張しない。
* 台帳への効果は A・B とも FG +1 / T1 0。判断者は強弱（B は強い・根拠が単純、A は最小・直接）で選ぶ。推奨は引き続き A（追加の証明単位が無く、rev0/rev1 から名前がある）。

## 3. 選択肢
| 選択肢 | 内容 | 台帳 | 影響 |
|---|---|---|---|
| **A（推奨）** | `InstSFieldsDet` を §2 の型で FG +1（DG-ENV と同期）。`instS_trace` はこれを名前付き仮説として取る | FG +1（現在値 103 → 104 の見込み、T1 差分 0。SigTyClosed と別） | U-R8 以降（U-R11 の dispatch）が条件付きで進む。条件が真であることは主張しない。後から外せる（Lean 側は別ファイルの名前付き仮説） |
| B | 条件を `SigResHeadConst`（`instS` 表の各 `(c, kinds, ty)` について、`ty` に対し `instRes ty args = some r` となる全ての `args` で、`r` の先頭定数が `args` に依らない。例: `ty` の先頭が束縛変数でない）に**取り替え**、`InstSFieldsDet` を補題にする | FG +1（B を採るなら A は不要。103→104、T1 差分 0） | §2b の関係を参照。条件が**強く**なる代わりに、中身が kernel の型付けの事実に近い。追加負担は §2b |
| C | 条件を置かず U-R8 と dispatch（U-R11）を止める | ±0 | `TraceGood senv nDecl (readF senv n)` が閉じない（中間結果のまま）。U-R9 / U-R10（loopBody / loopRoot）は独立なので進められる |

推奨は A（rev0/rev1 で既に名前を付けていた条件で、最小）。判断しない場合は C（U-R8 と U-R11 が止まる。U-R9 / U-R10 は進める）。可逆性: 行を足すだけで、取り下げ可。

## 4. U-R8 の型（承認後に Lean へ。新ファイル `Tools/ShippingGen5ReaderTraceInstS.lean`）
```lean
theorem instS_trace (senv : StructEnv) (nDecl n : Nat) (hI : Inst1Ph) (hD : InstSFieldsDet senv)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (c : Name) (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.instS env c kinds ty args st))
    (r : (Call.instS env c kinds ty args st).Res)
    (hv : (instSStep senv env c kinds ty args st).run (readF senv n) = some (some r)) :
    FReachC nDecl st (callOut (Call.instS env c kinds ty args st) r) ∧
    PhPost senv nDecl (Call.instS env c kinds ty args st) r
```
`Inst1Ph` は `inst1Ph_of_agrees (h : Inst1Agrees)`（既存 T1L-51）で出す。他に新しい前提は無い。

## 5. この rev12 が主張しないこと
`InstSFieldsDet` が真であること、`SigTyClosed` と同じ DG-ENV の枠で扱えること（owner との同期は承認後）、`instS_trace` の成立、型の elaborate。新しい law / TRUSTED 境界 / コンパイラ・共有定義の変更 / FG の縮小 / `GenWF` の強化は含まない。

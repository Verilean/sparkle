# DG-READERTRACE freeze rev21.1（`Expr.eqv` を小さな明示的仮定 `EqvAtom` にし、`DomKeepF` を前向きに合成する。文書のみ）

**改訂履歴。** rev21（297fda68）→ **rev21.1**（reviewer 変更依頼）: (1) `EqvAtom` を右側限定 `∀ a b, DomShape b → (a == b) = true → a = b` に変更（§1、guard の左右順の引用は §1.1）。(2) `domKeepF_seq` の `hE`（証明に使わない仮説）を署名から外した。(3) 変えた型を scratch（`autoImplicit false`）で再 elaborate し #check を写し直した（§5）。(4) scratch で `domKeepF_seq`・書込み 1 回の補題 `domKeepF_write`・`domForm_shape` を sorry なしで証明し、型と証明の成立を確かめた（§5。証明の Lean はコミットしない）。(5) `domForm_iff`（両向き、sorry）は実際に使う向きだけの `domForm_shape : DomForm d → DomShape d` に置き換え、証明済み。台帳は変わらない（0/0）。

対象 Issue: `sparkle-rt-rev20`（親 `sparkle-gen5-dg-readertrace`）。base: `par/rt-rev20` 25233fee（rev20 freeze + 補遺）。根拠: `DG_READERTRACE_FREEZE_REV20.md`、`..._REV20_ADDENDUM.md`、`RT_DOM_SURVEY.md` §1.3。
**台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。** `EqvAtom` は**未登録の候補**（承認後に T1 +1 の見込み、未計数）。Lean の source tree は編集していない。コンパイラ・共有定義・TRUSTED 境界・law・FG/保証は変えず、`GenWF` も強化しない。
用語: 「見つからなかった」は「この調査で辿った経路では見つからなかった」で、不可能の主張ではない。scratch の elaborate は**型が通ること**の確認で、証明が通ること・仮定が真であることの確認ではない。C++ の読取りは証明ではない（下記 §2 の限界）。

## 0. 要約

* 補遺の穴は、dom 書込み 3 箇所（conv bare register / `machReserve` / loopRoot）の検査 `d != dom'`（= `Expr.eqv`、opaque）から `dom' = d` が取れないこと。
* 案: (1) 仮定 `EqvAtom`（**右辺**が `_machIn` fvar か `defaultDomain` const なら `==` は項の等しさ）を `Tools/Assume/` に置く。(2) `DomKeep` を弱めた `DomKeepF`（`DomForm d' → d' = d`）にして前向きに合成する。(3) `machineShapeF_reach'` は最終 dom の `DomForm` から開始 dom の `DomForm` を得る。
* この案は**成り立つ見込み**（§3 の合成、§2 の C++ 読取り）。ただし `EqvAtom` は T1 の仮定 1 つ増（承認が要る）。D-a（FG +1）より仮定は小さく、C++ の事実で、run の性質ではない（§6）。

## 1. 仮定 `EqvAtom`（案、`Tools/Assume/ExprEqv.lean` に置く。登録は承認後）

```lean
def DomShape (d : Lean.Expr) : Prop :=
  (∃ i : Nat, d = Lean.Expr.fvar ⟨.num (.str .anonymous "_machIn") i⟩) ∨
  (∃ ls : List Lean.Level, d = Lean.Expr.const ``Sparkle.Core.Domain.defaultDomain ls)

def EqvAtom : Prop := ∀ a b : Lean.Expr, DomShape b → (a == b) = true → a = b
```

* **DomForm との関係。** rev20 の `DomForm d := ∃ r, machDom? 0 d = some r`（`machDom?` は `Elab.lean:4269`）は `machDom?` の 2 腕（`.fvar ⟨.num (.str .anonymous "_machIn") i⟩` と `.const defaultDomain ls`）の成功と同値（本文で使うのは `DomForm d → DomShape d` の向きだけで、`domForm_shape` として scratch で sorry なしに証明した。逆向きは使わないので出さない）。`Tools/Assume/` の仮定の文は `machDom?` の定義に依らない `DomShape` で書く（仮定の文が proof 側の定義に依存しないため）。
* **狭めた理由。** 一般の `Expr` について `eqv` は alpha 同値（binder 名・binder 情報を無視、`Expr.lean:809` の docstring）なので `a == b → a = b` は偽。**右辺**が atom（binder を含まない）のときだけ主張する。`StartDomOk.lean` の既存 `ExprEqvAtom`（右側が fvar / const の任意の atom）より**さらに狭い**（`DomShape` の 2 形のみ）。左辺は任意の `Expr`。使わない向き（左辺だけが `DomShape`）は仮定しない。既存の `ExprEqvAtom` は prototype にあり、本 freeze は新しい仮定を別名で出す（既存を置き換えない。台帳での扱いは reviewer / coder の判断）。
* **使い所。** 書込み 1 回の検査（`d0 != dom'` が `false` = `d0 == dom'`）。`DomForm dom'` のときだけ `d0 = dom'` を得る。左辺 `d0` は状態に保持された dom で、形の仮定は要らない。

### 1.1 guard の左右の順（3 箇所それぞれ）

`BEq Expr` は `Expr.eqv`（`a != b` は `!(a == b)`）。3 つの書込み箇所はいずれも **左 = 状態に既にある dom（`d` / `d0`）、右 = これから書く `dom'`**。`EqvAtom` の `b` は右、つまり書込み後の dom `dom'`（出力側）で、`DomForm dom'`（= 出力の `DomForm d'`、`d' := dom'`）から `DomShape dom'` を得る（`domForm_shape`）。

| 箇所 | Elab（`Sparkle/Compiler/Elab.lean`） | 書込み |
|---|---|---|
| `machReserve`（nested） | 3709: `| some d => if d != dom' then none else pure ()` | 3716: `dom := some dom'` |
| conv bare register | 3928: `| some d0 => if d0 != dom' then none else pure ()` | 3933: `dom := some dom'` |
| loopRoot | 4216: `| some d0 => if d0 != dom' then none else pure ()` | 4235: `dom := some dom'` |

Defs（reader の写し）: `Tools/ShippingReaderFuelDefs.lean:138` `domGuard`: `| some d0 => if d0 != dom' then FM.pure none else k`（左 `d0` = 状態、右 `dom'` = 書込み）。`machReserve` の写しは `Tools/ShippingReaderLenOkReserve.lean:141` `if st.dom.any (fun d => d != dom') then none else`（同じ順）。3 箇所の読取り側の写し（`ShippingReaderFuelVerbatim.lean:192, 461`）も `d0 != dom'`。この調査では、左右が逆の guard は見つからなかった。

## 2. 真である根拠（C++ の読取り。証明ではない）

toolchain v4.32.1 に C++ 本体は同梱されない（`StartDomOk2.lean` ヘッダのとおり `src/kernel` が無い）。このため **upstream の tag `v4.32.1`**（`https://raw.githubusercontent.com/leanprover/lean4/v4.32.1/src/kernel/expr_eq_fn.cpp` と `level.cpp`）を読んだ。ビルドされた binary がこの source から作られたこと（commit 文字列 `f054605a…` の一致のみ確認済み、`N3Extern.lean` ヘッダ）は未確認。`lean_expr_eqv` は `expr_eq_fn<false>` を呼ぶ（`expr_eq_fn.cpp:147-149`）。

`apply(a, b, depth, root)`（`expr_eq_fn.cpp:55-`）の関係する部分:

```
if (is_eqp(a, b))          return true;                 // 同じ object
if (hash(a) != hash(b))    return false;
if (a.kind() != b.kind())  return false;                // 種類が違えば false
switch (a.kind()) {
case expr_kind::FVar: return fvar_name(a) == fvar_name(b);          // 63 行
...
case expr_kind::Const:                                               // 95-98 行
    return const_name(a) == const_name(b) &&
           compare(const_levels(a), const_levels(b),
                   [](level const & l1, level const & l2) { return l1 == l2; });
```

* **fvar の腕。** `a` が `.fvar ⟨_machIn.i⟩` で `a == b` が `true` なら、`is_eqp` のとき同一、そうでなければ `b.kind() = FVar` かつ `fvar_name(a) == fvar_name(b)`。したがって `b = .fvar ⟨同じ名前⟩`。`FVarId` は名前 1 つの structure なので `a = b`。名前の `==` は C++ の `name::operator==`（構造比較）で、この点の source（`util/name.cpp`）は**今回は読んでいない**。
* **const の腕。** `kind` が `Const` で、`const_name` が等しく、`const_levels` が長さの等しい list で各要素が `l1 == l2`。`level` の `operator==`（`level.cpp:125-150`）は `kind` が違えば `false`、`hash` が違えば `false`、`Zero` は `true`、`Param`/`MVar` は `level_id`（名前）の等しさ、`Max`/`IMax`/`Succ` は深さの一致と子の `==` の再帰。**構造的な比較**で、`is_equivalent`（`lean_level_eqv`、別 extern）ではない。したがって level が構造的に等しい list になり、名前と合わせて `a = b`（Lean 側の `Level` の cached `data` は構造から決まる computed field で、項の等しさに別の自由度を足さない、という前提を使う）。
* **mdata。** `kind` が `MData` と `FVar` で違えば `false`。`md fv == fv` が `false` であることは `Tests/Compiler/ExprEqvAtomTest.lean`（実行で確認済み）と一致する。
* **他の形との比較。** `a` が atom でも `b` が `app`/`lam` 等なら `kind` 違いで `false`。`b = bvar/lit/sort/mvar` なら `kind` 違いで `false`。
* **hash は十分条件の方向に影響しない。** `hash` の比較は `false` を返す方向にだけ働く（`true` の結論を弱めない）。
* 限界: (i) 読んだ source と実際に実行される binary の一致、(ii) `name` の `==` の source、(iii) `Level.data` の扱いの前提。`EqvAtom` は**仮定**であり、この読取りは根拠のメモで、証明ではない。

## 3. 弱めた形 `DomKeepF` と合成

```lean
def DomKeepF (h : Hs) : Prop :=
  ∀ (c : Call) (v : c.Res), h c = some (some v) →
    ∀ d : Lean.Expr, (callSt c).dom = some d →
      ∃ d' : Lean.Expr, (callOut c v).dom = some d' ∧ (DomForm d' → d' = d)

theorem readF_domKeepF (hE : EqvAtom) (senv : StructEnv) (n : Nat) : DomKeepF (readF senv n)
theorem domKeepF_seq {d d1 d2 : Lean.Expr}
    (h1 : DomForm d1 → d1 = d) (h2 : DomForm d2 → d2 = d1) : DomForm d2 → d2 = d
```

* **書込み 1 回。** 検査後の書込みは `some dom'`、検査は `d == dom'`（§1.1 のとおり右が `dom'`）。`DomForm dom'` なら `EqvAtom`（右側限定、`b := dom'`）で `d = dom'`、よって `d' := dom'`、`d' = d`。検査を通らなければ失敗（`none`）で `h c = some (some v)` に反する。
* **合成。** `d1`（前半の出力）に対し `DomForm d1 → d1 = d`、後半（入力 `dom = some d1`）に対し `DomForm d2 → d2 = d1`。`DomForm d2` なら `d2 = d1`、したがって `DomForm d1`、したがって `d1 = d`、`d2 = d`。**前向き**にだけ合成する（途中の dom が `DomForm` である必要がない）。これが `DomKeep`（等式を直接保つ）と違い `eqv` 同値な別の項を許す点。
* **腕の扱い**（rev20 §1 の 7 腕の表の差分だけ）: conv bare register / `machReserve` / loopRoot は上記の「書込み 1 回」。inst / instS は補遺のとおり状態不変（`d' := d`）、`none` 枝は入力が `some d` では到達しない。chain / loopBody / conv の他の腕は帰納仮定と `domKeepF_seq`、record 更新は `dom` を保つ。nested は `machConv`（帰納仮定）→ `machReserve`（書込み 1 回）→ `machChain`（帰納仮定）を `domKeepF_seq` で 2 回。
* **右側限定で足りることの確認。** `EqvAtom` を使う箇所は書込み 1 回の 3 箇所だけで、そこでは右辺が `dom'`（`DomForm` の仮説が付くのも `dom'`）。`domKeepF_seq` は `hE` を使わず、`DomForm d2 → d2 = d1` から `d2 = d1` を得て `d1` を書き換えるだけ（scratch で証明済み、axiom は `propext` のみ）。chain / loopBody / record 更新は `eqv` を使わない。この読みで足りない箇所は見つからなかった（腕の証明自体は未実施）。
* 証明は**未実施**。詰まったら止めて coder に報告（自動受理しない）。

## 4. `machineShapeF_reach'` の流れ

```lean
theorem machineShapeF_reach' ... (hE : EqvAtom) (hT : TraceGood senv nDecl (readF senv n))
    (h : machineShapeF n sm ps ci senv ai = some (some sp))
    (hIn : ShapeInputs' nDecl senv sm ps ci n) : ∃ p en st0 env st1 st v, …（結論は `machineShapeF_reach` と同一）
```

1. `machineShapeF_state_side h` で `p en st0 env st1 st v` と `h0 … h3`（`h3 : shapePost … st v = some sp`）。
2. `hIn p en …` で `hrl hrun hroot`。
3. **`hform : ∀ d, st0.dom = some d → DomForm d` の用意。** `st0.dom = some d` に対し `rootLets_domKeepF`（`h1`）で `∃ d1, st1.dom = some d1 ∧ (DomForm d1 → d1 = d)`、`shapeBody_domKeepF`（`h2`）で `∃ d2, st.dom = some d2 ∧ (DomForm d2 → d2 = d1)`。`shapePost_domForm h3 hd2 : DomForm d2`（`shapePost` は `domE ← st.dom <|> machTypeDom? …` の `st.dom = some d2` 側から `machDom? … d2` の成功を要する、`Elab.lean:5173-5175`）。`domKeepF_seq` で `d2 = d`、よって `DomForm d`。
4. `shapeStart_trace' … hform` で `R0 C0`（rev20 §2 と同じ型）。以降（`rootLets_trace` / `shapeBody_trace`）と結論は既存の `machineShapeF_reach` と同一。`run? = none` のとき `st0 = {}`、`dom = none` で `hform` は空虚。
5. rev20 と違う点は、`machineShapeF_reach'` が `(hE : EqvAtom)` を取ること**だけ**。`DomKeep` は `DomKeepF` に置き換わる。

## 5. scratch の elaborate（rev21.1 で再実施）

`Scratch/Rev21Sig.lean`（worktree 内、**コミットしない**。`lakefile.lean` の `lean_lib «Scratch.Rev21Sig»` もコミットしない）を `kjob lake build Scratch.Rev21Sig` で elaborate: `Build completed successfully (791 jobs)`、exit 0（Pod 内）。`set_option autoImplicit false`、import は `Tools.ShippingGen5ReaderTraceDirect` のみ。警告は `declaration uses \`sorry\`` 7 件（意図した型のみの定理）と既存ファイルの lint のみ、エラーなし。
**sorry なしで証明が通ったもの:** `domForm_shape`（`DomForm d → DomShape d`）、`domKeepF_seq`（`hE` なし）、`domKeepF_write`（`EqvAtom`（右側限定）を仮説にとる書込み 1 回の補題。`(d != dom') = false → DomForm dom' → dom' = d`）。`#print axioms` はいずれも `[propext]` のみ（sorry・`Classical`・`native_decide` なし）。これは**型と、これら 3 つの証明が成立すること**の確認で、`readF_domKeepF` 以下（`sorry`）の証明や `EqvAtom` が真であることの確認ではない。証明の Lean はコミットしない（コピーは非コミットの scratch のみ）。
rev20 と共通の `MidInputs'` / `ShapeInputs'` / `shapeStart_trace'` は rev20 の文書（承認済み）と同文で再掲。`machineShapeF_reach'` は `hE` を足した rev21 のまま。

ソース（`#check` / `#print` を含む全文）:

```lean
import Tools.ShippingGen5ReaderTraceDirect
set_option autoImplicit false

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover5 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingReaderFuelShapeR5 Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv Tools.ShippingReaderLenOk

def DomShape (d : Lean.Expr) : Prop :=
  (∃ i : Nat, d = Lean.Expr.fvar ⟨.num (.str .anonymous "_machIn") i⟩) ∨
  (∃ ls : List Lean.Level, d = Lean.Expr.const ``Sparkle.Core.Domain.defaultDomain ls)

def EqvAtom : Prop := ∀ a b : Lean.Expr, DomShape b → (a == b) = true → a = b

def DomForm (d : Lean.Expr) : Prop := ∃ r, machDom? 0 d = some r

theorem domForm_shape (d : Lean.Expr) : DomForm d → DomShape d := by
  rintro ⟨r, h⟩
  unfold machDom? at h
  split at h
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩
  · cases h

def DomKeepF (h : Hs) : Prop :=
  ∀ (c : Call) (v : c.Res), h c = some (some v) →
    ∀ d : Lean.Expr, (callSt c).dom = some d →
      ∃ d' : Lean.Expr, (callOut c v).dom = some d' ∧ (DomForm d' → d' = d)

theorem readF_domKeepF (hE : EqvAtom) (senv : StructEnv) (n : Nat) : DomKeepF (readF senv n) := by
  sorry

theorem domKeepF_seq {d d1 d2 : Lean.Expr}
    (h1 : DomForm d1 → d1 = d) (h2 : DomForm d2 → d2 = d1) : DomForm d2 → d2 = d := by
  intro hf
  have e := h2 hf
  subst e
  exact h1 hf

theorem domKeepF_write (hE : EqvAtom) {d dom' : Lean.Expr} (hb : (d != dom') = false) :
    DomForm dom' → dom' = d := by
  intro hf
  have hb' : (d == dom') = true := by
    cases hh : (d == dom') <;> simp_all [bne]
  exact (hE d dom' (domForm_shape dom' hf) hb').symm

theorem shapeRootLet_domKeepF (senv : StructEnv) (n : Nat) (hK : DomKeepF (readF senv n))
    (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr)
    {s' : List MachVal × MachRead} (hr : (shapeRootLet senv s a).run (wtab senv n) = some (some s'))
    (d : Lean.Expr) (hd : s.2.dom = some d) :
    ∃ d', s'.2.dom = some d' ∧ (DomForm d' → d' = d) := by
  sorry

theorem rootLets_domKeepF (senv : StructEnv) (n : Nat) (hK : DomKeepF (readF senv n)) :
    ∀ (l : List (Name × Lean.Expr × Lean.Expr)) (env : List MachVal) (st : MachRead)
      {env' : List MachVal} {st' : MachRead},
    (foldO (shapeRootLet senv) (env, st) l).run (wtab senv n) = some (some (env', st')) →
    ∀ d : Lean.Expr, st.dom = some d → ∃ d', st'.dom = some d' ∧ (DomForm d' → d' = d) := by
  sorry

theorem shapeBody_domKeepF (senv : StructEnv) (n : Nat) (hK : DomKeepF (readF senv n))
    (m : ShapeMid) (env : List MachVal) (st1 : MachRead) {st : MachRead} {v : Lean.Expr}
    (hr : (shapeBody m env st1).run (wtab senv n) = some (some (st, v)))
    (d : Lean.Expr) (hd : st1.dom = some d) :
    ∃ d', st.dom = some d' ∧ (DomForm d' → d' = d) := by
  sorry

theorem shapePost_domForm {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr}
    {sp : MachineShape} (h : shapePost ai p m st v = some sp)
    {d : Lean.Expr} (hd : st.dom = some d) : DomForm d := by
  sorry

def MidInputs' (nDecl : Nat) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  p.bs.length ≤ nDecl ∧
  (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), (shapeMid senv p en).rootLets[k]? = some x →
      NoPh x.2.2 = true ∧ BvarLt (k + nDecl) x.2.2 = true) ∧
  (∀ (dom αs ie b : Lean.Expr), (shapeMid senv p en).run? = some (dom, αs, ie, b) →
      NoPh dom = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + nDecl) dom = true ∧
      NoPh b = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + 1 + nDecl) b = true) ∧
  ((shapeMid senv p en).run? = none →
      NoPh (shapeMid senv p en).root = true ∧
      BvarLt ((shapeMid senv p en).rootLets.length + nDecl) (shapeMid senv p en).root = true)

def ShapeInputs' (nDecl : Nat) (senv : StructEnv) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo)
    (n : Nat) : Prop :=
  ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p → machNormF n senv p.e = some en →
    MidInputs' nDecl senv p en

theorem shapeStart_trace' (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (m : ShapeMid)
    (hdom : ∀ dom αs ie b, m.run? = some (dom, αs, ie, b) →
        NoPh dom = true ∧ BvarLt (m.rootLets.length + nDecl) dom = true)
    {st0 : MachRead} (hr : (shapeStart senv m).run (wtab senv n) = some (some st0))
    (hform : ∀ d : Lean.Expr, st0.dom = some d → DomForm d) :
    FReachC nDecl ({} : MachRead) st0 ∧ ShapeCarry senv nDecl [] st0 := by
  sorry

theorem machineShapeF_reach' {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape} {nDecl : Nat} (hE : EqvAtom)
    (hT : TraceGood senv nDecl (readF senv n))
    (h : machineShapeF n sm ps ci senv ai = some (some sp))
    (hIn : ShapeInputs' nDecl senv sm ps ci n) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size ∧
      FReachC nDecl ({} : MachRead) st0 ∧ FReachC nDecl st0 st1 ∧ FReachC nDecl st1 st ∧
      TrInv senv nDecl st ∧
      ((shapeMid senv p en).wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v) := by
  sorry

#check @DomShape
#check @EqvAtom
#check @domForm_shape
#check @DomKeepF
#check @readF_domKeepF
#check @domKeepF_seq
#check @domKeepF_write
#print axioms domKeepF_seq
#print axioms domKeepF_write
#print axioms domForm_shape
#check @shapeRootLet_domKeepF
#check @rootLets_domKeepF
#check @shapeBody_domKeepF
#check @shapePost_domForm
#check @shapeStart_trace'
#check @machineShapeF_reach'
end Tools.ShippingGen5ReaderTrace
```

`#check` / `#print` の出力（そのまま）:

```
info: Scratch/Rev21Sig.lean:117:0: DomShape : Expr → Prop
info: Scratch/Rev21Sig.lean:118:0: EqvAtom : Prop
info: Scratch/Rev21Sig.lean:119:0: domForm_shape : ∀ (d : Expr), DomForm d → DomShape d
info: Scratch/Rev21Sig.lean:120:0: DomKeepF : Hs → Prop
info: Scratch/Rev21Sig.lean:121:0: readF_domKeepF : EqvAtom → ∀ (senv : StructEnv) (n : Nat), DomKeepF (readF senv n)
info: Scratch/Rev21Sig.lean:122:0: @domKeepF_seq : ∀ {d d1 d2 : Expr}, (DomForm d1 → d1 = d) → (DomForm d2 → d2 = d1) → DomForm d2 → d2 = d
info: Scratch/Rev21Sig.lean:123:0: domKeepF_write : EqvAtom → ∀ {d dom' : Expr}, (d != dom') = false → DomForm dom' → dom' = d
info: Scratch/Rev21Sig.lean:124:0: 'Tools.ShippingGen5ReaderTrace.domKeepF_seq' depends on axioms: [propext]
info: Scratch/Rev21Sig.lean:125:0: 'Tools.ShippingGen5ReaderTrace.domKeepF_write' depends on axioms: [propext]
info: Scratch/Rev21Sig.lean:126:0: 'Tools.ShippingGen5ReaderTrace.domForm_shape' depends on axioms: [propext]
info: Scratch/Rev21Sig.lean:127:0: shapeRootLet_domKeepF : ∀ (senv : StructEnv) (n : Nat),
  DomKeepF (readF senv n) →
    ∀ (s : List MachVal × MachRead) (a : Name × Expr × Expr) {s' : List MachVal × MachRead},
      (shapeRootLet senv s a).run (wtab senv n) = some (some s') →
        ∀ (d : Expr), s.snd.dom = some d → ∃ d', s'.snd.dom = some d' ∧ (DomForm d' → d' = d)
info: Scratch/Rev21Sig.lean:128:0: rootLets_domKeepF : ∀ (senv : StructEnv) (n : Nat),
  DomKeepF (readF senv n) →
    ∀ (l : List (Name × Expr × Expr)) (env : List MachVal) (st : MachRead) {env' : List MachVal} {st' : MachRead},
      (foldO (shapeRootLet senv) (env, st) l).run (wtab senv n) = some (some (env', st')) →
        ∀ (d : Expr), st.dom = some d → ∃ d', st'.dom = some d' ∧ (DomForm d' → d' = d)
info: Scratch/Rev21Sig.lean:129:0: shapeBody_domKeepF : ∀ (senv : StructEnv) (n : Nat),
  DomKeepF (readF senv n) →
    ∀ (m : ShapeMid) (env : List MachVal) (st1 : MachRead) {st : MachRead} {v : Expr},
      (shapeBody m env st1).run (wtab senv n) = some (some (st, v)) →
        ∀ (d : Expr), st1.dom = some d → ∃ d', st.dom = some d' ∧ (DomForm d' → d' = d)
info: Scratch/Rev21Sig.lean:130:0: @shapePost_domForm : ∀ {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Expr} {sp : MachineShape},
  shapePost ai p m st v = some sp → ∀ {d : Expr}, st.dom = some d → DomForm d
info: Scratch/Rev21Sig.lean:131:0: shapeStart_trace' : ∀ (senv : StructEnv) (nDecl n : Nat),
  TraceGood senv nDecl (readF senv n) →
    ∀ (m : ShapeMid),
      (∀ (dom αs ie b : Expr),
          m.run? = some (dom, αs, ie, b) → NoPh dom = true ∧ BvarLt (m.rootLets.length + nDecl) dom = true) →
        ∀ {st0 : MachRead},
          (shapeStart senv m).run (wtab senv n) = some (some st0) →
            (∀ (d : Expr), st0.dom = some d → DomForm d) → FReachC nDecl { } st0 ∧ ShapeCarry senv nDecl [] st0
info: Scratch/Rev21Sig.lean:132:0: @machineShapeF_reach' : ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {senv : StructEnv}
  {ai : Bool} {sp : MachineShape} {nDecl : Nat},
  EqvAtom →
    TraceGood senv nDecl (readF senv n) →
      machineShapeF n sm ps ci senv ai = some (some sp) →
        ShapeInputs' nDecl senv sm ps ci n →
          ∃ p en st0 env st1 st v,
            shapePre sm ps ci senv = some p ∧
              machNormF n senv p.e = some en ∧
                (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
                  (foldO (shapeRootLet senv) ([], st0) (shapeMid senv p en).rootLets).run (wtab senv n) =
                      some (some (env, st1)) ∧
                    (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
                      shapePost ai p (shapeMid senv p en) st v = some sp ∧
                        st.LenOk ∧
                          sp.insts = st.insts.toList ∧
                            sp.instOrigins = st.instOrigins.toList ∧
                              sp.layout.slots.length = st.kinds.size ∧
                                sp.layout.lets = Array.size st.lets ∧
                                  FReachC nDecl { } st0 ∧
                                    FReachC nDecl st0 st1 ∧
                                      FReachC nDecl st1 st ∧
                                        TrInv senv nDecl st ∧
                                          ((shapeMid senv p en).wrap? = none →
                                            InRange nDecl st (Array.size st.lets) v ∧ NoLoose 0 v)
```

## 6. 比較表: `EqvAtom`（T1 +1）と D-a（`DomAtomicRun`、FG +1）

| 観点 | 案 EqvAtom + DomKeepF | D-a（`DomAtomicRun`、`RT_DOM_SURVEY` §1.3） |
|---|---|---|
| 台帳 | T1 +1（候補、未計数、承認後に登録） | FG +1（見込み、未計数） |
| 仮定の内容 | C++ extern `lean_expr_eqv` の事実（atom との比較）。入力・run に依らない | 受理された run の**性質**（成功した run の run dom が atomic）。供給元は generator 側の知識で、この調査では供給経路が見つかっていない |
| 範囲 | `DomShape` の 2 形のみ。一般の `Expr` は主張しない | `machineShapeF … = some _` の全入力に対する universal |
| 根拠の確かめ方 | upstream の source 2 ファイルの該当行を引用でき、`ExprEqvAtomTest` の実行結果と一致（§2）。限界は binary 一致など | run の実体（generator・入力）に依存。事実としての確認は個別の入力ごと |
| 証明の追加量 | `DomKeepF`（7 腕、書込み 1 回 + `domKeepF_seq`）+ `hform` 供給。`TraceGood` は変えない | 腕の証明は不要。`MidInputs` の `DomAtomic dom` を run 仮定で供給 |
| `hdom` binder の除去 | 消える。ただし**台帳の行は元から無いので減らない**（FG/T1 の減算 0） | 消える（`DomAtomicRun` に付け替わる）。台帳の行は減らない（+1） |
| 可逆性 | 仮定を後から証明（C++ 検証）か撤回（D-a / D に戻す）できる | 同様。別 freeze で戻せる |
| 今回 | 0/0（候補、未登録） | 0/0 |

どちらも `hdom` binder の除去は**台帳の行を減らさない**。`EqvAtom` は T1 +1、D-a は FG +1 で、行は増える。

**推奨: 案 EqvAtom + DomKeepF。** 理由: (1) 仮定が入力に依らない C++ の事実で、source の該当行（fvar の名前比較、const の名前 + level の構造比較）で根拠が述べられ、実行テストとも合う。D-a は run の性質で供給元が未発見。(2) 範囲が `DomShape` の 2 形に限られ、binder 名を無視する alpha 同値の一般論に触れない。(3) 補遺の穴（`d != dom'` が opaque）にだけ正確に対応し、`TraceGood` など承認済みの文は変えない。(4) 既存の prototype `ExprEqvAtom`（`StartDomOk.lean`）と同種の仮定で、方針（ユーザー方針「C++/opaque の振る舞いは小さな明示的仮定にして、合成法則はそこから証明する」）に合う。
代替: D-a（別の freeze）、または (D) 現状維持（`DomAtomic dom` の既存版 rev19 が残る）。判断しない場合は (D)。

## 7. 主張しないこと / 台帳

`EqvAtom` が真であること（§2 は読取り。binary 一致・`name` の `==`・`Level.data` は未確認）、`readF_domKeepF` / `shapePost_domForm` / `machineShapeF_reach'` が証明できること（scratch は `sorry`。`domForm_shape` / `domKeepF_seq` / `domKeepF_write` は scratch で証明済みだが、本実装ではない）、`ShapeInputs'` が受理されたソースで供給されること、`hnD`、C.EN-6。mutant は使っていない。コンパイラ・共有定義・TRUSTED 境界・law は変えていない。`EqvAtom` の登録（T1 +1）はこの freeze の承認後で、今は未登録。
台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0。`EqvAtom` は未登録の候補で T1 +1 見込み、未計数）。

## 8. reviewer への依頼（台帳の追加にあたるので review に出す）

1. §1 の `EqvAtom` / `DomShape` の文と、`Tools/Assume/` に置く方針（T1 +1 の候補）。
2. §2 の C++ 読取りの根拠と限界の書き方。
3. §1 の右側限定 `EqvAtom` と §1.1 の guard 順、§3 の `DomKeepF` の型と `domKeepF_seq`（`hE` なし）、§4 の `machineShapeF_reach'`（`hE` の追加）。
4. §6 の推奨（案 EqvAtom）。承認されたら coder が `EqvAtom` を登録し、rt30 系の実装に進む。

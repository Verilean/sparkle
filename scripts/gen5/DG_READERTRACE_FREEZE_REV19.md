# DG-READERTRACE freeze rev19（rev18 df2fd8ef の変更依頼への修正: `shapeInputs_of_direct` の省略なし完全型。文書のみ）

対象 Issue: `sparkle-gen5-dg-readertrace`。base: `kjob/rt23` df2fd8ef（`DG_READERTRACE_FREEZE_REV18.md`）。
rev18 の §1 の署名だけを置き換える。それ以外（非 inline の `CiDirect` 枝に狭めること、inline 枝は未解消、`rootFloatAgrees hla` で `RootFloatAgrees` を導く順序、S1 / S2 は新しい前提に数えない、`UserInlinerPh` は採らない）は rev18 のまま。
台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。**Lean の source tree は編集していない。**

## 0. 指摘と対応

rev18 の `shapeInputs_of_direct` は (i) `hdom` が `…` で省略、(ii) `ci` / `sm` / `ps` / `nDecl` / `n` の binder が署名内に無かった。
rev19 は (i) `hdom` を全称変数・前件・結果まで展開、(ii) 全 binder を明示（implicit は `{}`）した 1 つの署名を、**scratch で `set_option autoImplicit false` のもとで elaborate**し、`#check` の出力を一字一句写す。

## 1. elaborate の方法（再現可能な範囲）

* scratch: `git archive df2fd8ef` を `/tmp` 配下のスクラッチ領域に展開し、`git init` した別コピー。`Scratch/Rev19Sig.lean` を追加し `lakefile.lean` に `lean_lib «Scratch.Rev19Sig»` を追記。source tree の worktree には置かず、コミットしない。
* `kjob lake build Scratch.Rev19Sig`: `Build completed successfully (774 jobs)`、exit 0、15m27s（キャッシュ無しの初回。警告の理由）。
* 出力した警告は `declaration uses \`sorry\``（`shapeInputs_of_direct` の本体 `sorry`、意図どおり）と既存ファイルの未使用 simp 引数 lint のみ。エラーなし。
* `set_option autoImplicit false` を scratch の先頭に置いた。使った名前はすべて (a) 既存の定義（`ShapeInputs` `ShapePre` `shapePre` `shapeMid` `machNormF` `machNormNode` `structEnv` `DomAtomic` `NoPh` `BvarLt` `LiftAgrees` `Inst1Agrees` `Tools.Assume.N3Extern.ZeroLitAgrees0` `rawNode` `packTupleInputs` `tupleInput?` `unpackE` `natE`）か、(b) rev16 / rev18 の条件（下の §2）。他の名前はない。
* 本文は `sorry` のまま。型の elaborate だけで、証明は未実施。

## 2. 条件の完全型（scratch のソース、elaborate 済み）

N1（rev16 §2.1）、N2-b（rev16 §3.1。twin `lamDepth` / `packTupleInputsF` を含む）、N3-b（rev16 §4.2）、`CiDirect`（rev18 §1）を、rev16 / rev18 の本文どおり scratch に置いた。ソース全文:

```lean
namespace Tools.Assume.EnvDeclValue
open Lean Tools.ShippingGen5ReaderTrace
def DeclValuePh (env : Lean.Environment) : Prop :=
  ∀ (n : Lean.Name) (d : Lean.DefinitionVal),
    env.find? n = some (.defnInfo d) → NoPh d.value = true ∧ BvarLt 0 d.value = true
end Tools.Assume.EnvDeclValue

namespace Tools.ShippingGen5ReaderTracePack
open Lean Sparkle.Compiler.MachTupleIn Tools.ShippingGen5ReaderTrace
def lamDepth : Lean.Expr → Nat
  | .lam _ _ b _ => lamDepth b + 1
  | _ => 0
def packTupleInputsF : Nat → Lean.Expr → Lean.Expr
  | k + 1, .lam nm ty b bi =>
    match tupleInput? ty with
    | some (dom, ws) =>
      let n := ws.foldl (· + ·) 0
      let ty' := mkApp2 (.const ``Sparkle.Core.Signal.Signal [.zero]) dom (mkApp (.const ``BitVec []) (natE n))
      let b' := (b.liftLooseBVars 1 1).instantiate1 (unpackE (dom.liftLooseBVars 0 1) ws (.bvar 0))
      .lam nm ty' (packTupleInputsF k b') bi
    | none => .lam nm ty (packTupleInputsF k b) bi
  | _, e => e
end Tools.ShippingGen5ReaderTracePack

namespace Tools.Assume.PackTupleBridge
open Lean Tools.ShippingGen5ReaderTrace
def PackTupleInputsBridge : Prop :=
  ∀ e : Lean.Expr, NoPh e = true → BvarLt 0 e = true →
    Sparkle.Compiler.MachTupleIn.packTupleInputs e = Tools.ShippingGen5ReaderTracePack.packTupleInputsF (Tools.ShippingGen5ReaderTracePack.lamDepth e) e
end Tools.Assume.PackTupleBridge

namespace Tools.Assume.NormNodePh
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5ReaderTrace
def RawNodePh (senv : StructEnv) : Prop :=
  ∀ (L : Nat) (f a e' : Lean.Expr),
    NoPh f = true → NoPh a = true → BvarLt L f = true → BvarLt L a = true →
    Sparkle.Compiler.MachRawSurface.rawNode senv.prodMatch (.app f a) = some e' →
    NoPh e' = true ∧ BvarLt L e' = true
def NormNodePh (senv : StructEnv) : Prop :=
  ∀ (L : Nat) (f a : Lean.Expr),
    NoPh f = true → NoPh a = true → BvarLt L f = true → BvarLt L a = true →
    NoPh (machNormNode senv (.app f a)) = true ∧ BvarLt L (machNormNode senv (.app f a)) = true
end Tools.Assume.NormNodePh

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.ShippingReaderFuel

def CiDirect (env : Lean.Environment) (ci : Lean.ConstantInfo) : Prop :=
  ∃ c : Lean.Name, env.find? c = some ci

theorem shapeInputs_of_direct
    (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    {ci : Lean.ConstantInfo} (hci : CiDirect env ci)
    (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env))
    (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    {nDecl : Nat} {sm : Bool} {ps : List (String × Nat)} {n : Nat}
    (hdom : ∀ (p : ShapePre) (en : Lean.Expr),
      shapePre sm ps ci (structEnv env) = some p → machNormF n (structEnv env) p.e = some en →
      ∀ (dom αs ie b : Lean.Expr), (shapeMid (structEnv env) p en).run? = some (dom, αs, ie, b) → DomAtomic dom)
    (hbs : ∀ p : ShapePre, shapePre sm ps ci (structEnv env) = some p → p.bs.length ≤ nDecl) :
    ShapeInputs nDecl (structEnv env) sm ps ci n := by
  sorry

end Tools.ShippingGen5ReaderTrace

```

（`CiDirect` と `shapeInputs_of_direct` は `namespace Tools.ShippingGen5ReaderTrace` 内、`open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.ShippingReaderFuel`。上の抜粋の末尾の `#check` / `#print` 行は §3 に載せるため除いてある。）

## 3. elaborate した署名（`#check` の出力そのまま）

```
info: Scratch/Rev19Sig.lean:70:0: CiDirect : Environment → ConstantInfo → Prop
info: Scratch/Rev19Sig.lean:71:0: shapeInputs_of_direct : Assume.N3Extern.ZeroLitAgrees0 →
  LiftAgrees →
    Inst1Agrees →
      ∀ (env : Environment),
        Assume.EnvDeclValue.DeclValuePh env →
          ∀ {ci : ConstantInfo},
            CiDirect env ci →
              Assume.PackTupleBridge.PackTupleInputsBridge →
                Assume.NormNodePh.RawNodePh (structEnv env) →
                  Assume.NormNodePh.NormNodePh (structEnv env) →
                    ∀ {nDecl : Nat} {sm : Bool} {ps : List (String × Nat)} {n : Nat},
                      (∀ (p : ShapePre) (en : Expr),
                          shapePre sm ps ci (structEnv env) = some p →
                            machNormF n (structEnv env) p.e = some en →
                              ∀ (dom αs ie b : Expr),
                                (shapeMid (structEnv env) p en).run? = some (dom, αs, ie, b) → DomAtomic dom) →
                        (∀ (p : ShapePre), shapePre sm ps ci (structEnv env) = some p → p.bs.length ≤ nDecl) →
                          ShapeInputs nDecl (structEnv env) sm ps ci n
info: Scratch/Rev19Sig.lean:72:0: def Tools.ShippingGen5ReaderTrace.CiDirect : Environment → ConstantInfo → Prop :=
fun env ci => ∃ c, env.find? c = some ci
info: Scratch/Rev19Sig.lean:76:0: EnvDeclValue.DeclValuePh : Lean.Environment → Prop
info: Scratch/Rev19Sig.lean:78:0: PackTupleBridge.PackTupleInputsBridge : Prop
info: Scratch/Rev19Sig.lean:80:0: NormNodePh.RawNodePh : Sparkle.Compiler.Elab.StructEnv → Prop
info: Scratch/Rev19Sig.lean:82:0: NormNodePh.NormNodePh : Sparkle.Compiler.Elab.StructEnv → Prop
info: Scratch/Rev19Sig.lean:83:0: def Tools.ShippingLetsReaderInv.LiftAgrees : Prop :=
∀ (e : Lean.Expr),
  Tools.ShippingLetsReaderInv.LetOk 0 e = true →
    e.liftLooseBVars 0 1 = Tools.ShippingLetsReaderInv.liftSpec e 0 1 ∧
      e.liftLooseBVars 1 1 = Tools.ShippingLetsReaderInv.liftSpec e 1 1
```

`#check @CiDirect` の行（70:0）から `#print LiftAgrees`（83:0）までの出力。`ci` は `CiDirect env ci` の直前に束縛される implicit。`{nDecl} {sm} {ps} {n}` は `hdom` の前に束縛される implicit で、`hdom` / `hbs` / 結論の `ShapeInputs nDecl (structEnv env) sm ps ci n` がそれらを使う。

## 4. N1〜N3 の条件の署名への接続

| 署名の binder | 型 | 出所 | 署名内での役割 |
|---|---|---|---|
| `hz` | `Assume.N3Extern.ZeroLitAgrees0` | 既存（T1L-54、N4-a） | `shapeMid_ph`（U-R12c）の引数 |
| `hla` | `LiftAgrees` | 既存（T1L-50） | `rootFloatAgrees hla`（ptot-m4 統合後）で `RootFloatAgrees` を導く、`packTupleInputsF_ph` の `lift` |
| `hi1` | `Inst1Agrees` | 既存（T1L-51） | `packTupleInputsF_ph` / `machNormF_ph` の `instantiate1` |
| `env`, `hv : DeclValuePh env` | N1-a（rev16 §2.1） | 新規候補（未登録） | `hci` と合わせて `hdecl`（`ci = .defnInfo d → NoPh d.value ∧ BvarLt 0 d.value`）を作る |
| `ci`, `hci : CiDirect env ci` | rev18 §1 | 名前付き入力（行にしない） | `c` を取り `env.find? c = some ci`。`ci = .defnInfo d` なら `hv c d` |
| `hbr : PackTupleInputsBridge` | N2-b（rev16 §3.1） | 新規候補（未登録） | `d.value`（`NoPh ∧ BvarLt 0`）で `packTupleInputs = packTupleInputsF (lamDepth ·) ·`、`packTupleInputsF_ph` へ |
| `hraw : RawNodePh (structEnv env)`, `hnode : NormNodePh (structEnv env)` | N3-b（rev16 §4.2） | 新規候補（未登録、2 件） | `machNormF_ph`（`hi1` と合わせ）で `hnorm`（`machNormF n senv e = some en → NoPh en ∧ BvarLt L en`）を作る |
| `nDecl`, `sm`, `ps`, `n`, `hdom`, `hbs` | 既存の定義の引数 | `hdom` は DomAtomic（D-b 待ちで未供給）、`hbs` は未供給 | `ShapeInputs` の入力。実装済みの `shapeInputs_of`（`ShapeIn.lean:463`）の `hdom` / `hbs` と同じ型（`senv := structEnv env`） |

実装済みの `shapeInputs_of`（`hdecl` / `hpack` / `hnorm` を仮説に取る）との関係: `hdecl` ← `hv` + `hci`、`hpack` ← `hbr` + `packTupleInputsF_ph`、`hnorm` ← `hraw` + `hnode` + `hi1` + `machNormF_ph`。この 3 つの導出補題（`packTupleInputsF_ph`、`machNormF_ph` と `hdecl` の組み立て）は**未証明・未 elaborate**。署名の型の確認までが本 freeze。

## 5. 台帳

| 項目 | 今回 |
|---|---|
| FG | ±0（N1-a +1 / N2-b +1 / N3-b +2 は承認後に登録する見込みの候補。未登録・未計数） |
| T1 | ±0（`LiftAgrees` / `Inst1Agrees` / `ZeroLitAgrees0` は既存の行） |

台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。

## 6. 主張しないこと

`hci`・`hv`・`hbr`・`hraw`・`hnode`・`hdom`・`hbs` が実際の run で供給されること、inline 枝、`GetEnvFrame` / 2 回の `getEnv` の同一性、`shapeInputs_of_direct` の証明、`ShapeInputs` の供給、C.RT-2 等の減算、N1〜N3 の登録、`UserInlinerPh`。scratch の elaborate は型が通ることの確認で、条件が真であることの確認ではない。`rootFloatAgrees` は ptot-m4 にあり、署名には現れない（本体で使う）。この調査では供給元・経路が見つからなかったものは、導出不能の意味ではない。コンパイラ・共有定義・TRUSTED 境界・law は変えていない。mutant は使っていない。

## 7. reviewer への依頼

1. §3 の署名が、binder を省略せず exact type として固定できるか。
2. §2 の条件の型が rev16 / rev18 の承認済みの文と一致しているか。
3. §4 の接続表。

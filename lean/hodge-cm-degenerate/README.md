# lean/hodge-cm-degenerate

The Hodge conjecture for degenerate CM-type abelian varieties: the discrete core (combinatorics, discriminants, divisors, secants, design inequalities).

ホッジ予想：退化 CM 型のアーベル多様体と例外ホッジ類（組合せ・判別式・因子・割線・設計の不等式）。名前空間 `Principia.CMHodge`。

## 対応する記事・論文

- 記事：https://computoergosum.com/principia/hodge-cm-degenerate.html（このリポジトリの `articles/hodge-cm-degenerate.html`）

## 中身

- モジュール 46 本・`#print axioms` の対象の定理 980 本
- Lean 4 `leanprover/lean4:v4.33.1`（`lean-toolchain`）・Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`（`lake-manifest.json` で固定）
- `sorry` 0・`native_decide` 不使用。**定理名は一つも変えていない**

## 建て方

```
lake exe cache get              # Mathlib のビルド済みキャッシュ
LEAN_NUM_THREADS=1 lake build Principia
```

**一本ずつ建てること。**証明の中に kernel へ大きな計算を閉じ込めるものがあり、lake の既定は CPU の数だけ同時に建てるので、`LEAN_NUM_THREADS=1` で絞る。**RAM は 16 GB を見込む。**

## 公理

各モジュールの末尾（または主題の `Chk` モジュール）に `#print axioms` が置いてあり、建てると依拠する公理がそのまま出力される。`axioms-hodge-cm-degenerate.txt` はその出力をモジュールごとに並べたもの（980 行）。

- 全行が `propext`・`Classical.choice`・`Quot.sound`（Lean / Mathlib の標準三公理）の**部分集合**
- `sorryAx` 0 件・`Lean.ofReduceBool`（`native_decide`）0 件

| 公理 | 定理の本数 |
|---|---:|
| `[propext, Classical.choice, Quot.sound]` | 771 |
| `[propext]` | 126 |
| `[propext, Quot.sound]` | 48 |
| （公理なし） | 35 |

## 入口から外したモジュール

入口の `Principia.lean` はモジュールを `import` するだけのファイルである。次の 4 本は、入口が読み込む本と同じ名前空間に同名の宣言（単独で検査できるよう写した定義・補題）を持ち、同時には読み込めないので、入口からは `import` しない。`lakefile.lean` の ``globs := #[.andSubmodules `Principia]`` により、`lake build Principia` はこれらも含めて全モジュールを建てる。

- `Principia.CMHodge.CMHodgeDegenerate`
- `Principia.CMHodge.CMHodgeLevelOne`
- `Principia.CMHodge.CMHodgeNormal`
- `Principia.CMHodge.CMHodgeWeilType`

衝突した宣言の組は次のとおり。

- `Principia.CMHodge.CMHodgeClasses`・`Principia.CMHodge.CMHodgeLevelOne`：`CMHodge.adm`
- `Principia.CMHodge.CMHodgeClasses`・`Principia.CMHodge.CMHodgeNormal`：`CMHodge.inS`
- `Principia.CMHodge.CMHodgeDegenerate`・`Principia.CMHodge.CMHodgeLevelOne`：`CMHodge.L1`
- `Principia.CMHodge.CMHodgeDivisor`・`Principia.CMHodge.CMHodgeNormal`：`CMHodge.wt`
- `Principia.CMHodge.CMHodgeLevelOne`・`Principia.CMHodge.CMHodgeProductCurve`・`Principia.CMHodge.CMHodgeWeilType`：`CMHodge.SM`
- `Principia.CMHodge.CMHodgeProductCurve`・`Principia.CMHodge.CMHodgeWeilType`：`CMHodge.SM_is_cm_type`・`CMHodge.bit`・`CMHodge.sumR`

`CMHodgeDegenerate` は、さらに `CMHodgeClasses` と自動生成のインスタンス名 `CMHodge.instDecidableAdm` が重なるため入口から外してある。

## Lean の外にあるもの

機械検査が保証するのは「書いてある命題からその結論が出ること」だけである。命題が意図した内容を書けているか、その主張が世の中で新しいかについて、機械は何も言わない。

Lean に入っているのは、有限集合の数え上げ・整数の線形条件・パーマネントの正値性・実符号座標の場所勘定・多項式の正値性の証明書といった離散的な核だけである。ホッジ構造・代数的サイクル・連接層・消滅定理などの幾何は入っておらず、それらを使う段は紙である。証明書を探すのに使った浮動小数の LP も Lean の外で、主張にはしていない。

各モジュールの冒頭のコメントに、何を Lean の中に入れ、何を外に置いたかを書いてある。

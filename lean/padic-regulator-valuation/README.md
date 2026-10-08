# lean/padic-regulator-valuation

p-adic heights on elliptic curves: the arithmetic layer of the valuation of the p-adic regulator at anomalous primes.

楕円曲線の p 進高さと正準高さの付値（異常素点での p 進レギュレーターの付値の、算術の段）。名前空間 `Principia.PadicHeight`。

## 対応する記事・論文

- 論文：https://computoergosum.com/principia/papers/padic-regulator-valuation.pdf（このリポジトリの `papers/padic-regulator-valuation/`）

## 中身

- モジュール 30 本・`#print axioms` の対象の定理 356 本
- Lean 4 `leanprover/lean4:v4.33.1`（`lean-toolchain`）・Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`（`lake-manifest.json` で固定）
- `sorry` 0・`native_decide` 不使用。**定理名は一つも変えていない**

## 建て方

```
lake exe cache get              # Mathlib のビルド済みキャッシュ
LEAN_NUM_THREADS=1 lake build Principia
```

**一本ずつ建てること。**証明の中に kernel へ大きな計算を閉じ込めるものがあり、lake の既定は CPU の数だけ同時に建てるので、`LEAN_NUM_THREADS=1` で絞る。**RAM は 16 GB を見込む。**

## 公理

各モジュールの末尾（または主題の `Chk` モジュール）に `#print axioms` が置いてあり、建てると依拠する公理がそのまま出力される。`axioms-padic-regulator-valuation.txt` はその出力をモジュールごとに並べたもの（356 行）。

- 全行が `propext`・`Classical.choice`・`Quot.sound`（Lean / Mathlib の標準三公理）の**部分集合**
- `sorryAx` 0 件・`Lean.ofReduceBool`（`native_decide`）0 件

| 公理 | 定理の本数 |
|---|---:|
| `[propext, Classical.choice, Quot.sound]` | 225 |
| `[propext, Quot.sound]` | 99 |
| `[propext]` | 30 |
| （公理なし） | 2 |

## 入口から外したモジュール

入口の `Principia.lean` はモジュールを `import` するだけのファイルである。次の 1 本は、入口が読み込む本と同じ名前空間に同名の宣言（単独で検査できるよう写した定義・補題）を持ち、同時には読み込めないので、入口からは `import` しない。`lakefile.lean` の ``globs := #[.andSubmodules `Principia]`` により、`lake build Principia` はこれらも含めて全モジュールを建てる。

- `Principia.PadicHeight.Valuation13`

## Lean の外にあるもの

機械検査が保証するのは「書いてある命題からその結論が出ること」だけである。命題が意図した内容を書けているか、その主張が世の中で新しいかについて、機械は何も言わない。

Lean に入っているのは算術の段（高さの分解・Fermat 商・線形代数・重みと留数の勘定）である。幾何の入力（形式群・Mazur–Tate のシグマ関数・局所高さの分解など）は Lean の言明の中で仮定として入る。論文 §5 の数値は PARI/GP による計算で、Lean の外である。

各モジュールの冒頭のコメントに、何を Lean の中に入れ、何を外に置いたかを書いてある。

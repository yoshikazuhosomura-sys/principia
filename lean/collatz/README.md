# lean/collatz

The Collatz map: the critical multiplier, measures, ladder heights, branch survival and forbidden words.

コラッツ写像（臨界の乗数・測度・階段の高さ・枝の生死・禁止語）。名前空間 `Principia.Collatz`。

## 対応する記事・論文

- 記事：https://computoergosum.com/principia/collatz.html

## 中身

- モジュール 7 本・`#print axioms` の対象の定理 108 本
- Lean 4 `leanprover/lean4:v4.33.1`（`lean-toolchain`）・Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`（`lake-manifest.json` で固定）
- `sorry` 0・`native_decide` 不使用。**定理名は一つも変えていない**

## 建て方

```
lake exe cache get              # Mathlib のビルド済みキャッシュ
LEAN_NUM_THREADS=1 lake build Principia
```

**一本ずつ建てること。**証明の中に kernel へ大きな計算を閉じ込めるものがあり、lake の既定は CPU の数だけ同時に建てるので、`LEAN_NUM_THREADS=1` で絞る。**RAM は 16 GB を見込む。**

## 公理

各モジュールの末尾（または主題の `Chk` モジュール）に `#print axioms` が置いてあり、建てると依拠する公理がそのまま出力される。`axioms-collatz.txt` はその出力をモジュールごとに並べたもの（108 行）。

- 全行が `propext`・`Classical.choice`・`Quot.sound`（Lean / Mathlib の標準三公理）の**部分集合**
- `sorryAx` 0 件・`Lean.ofReduceBool`（`native_decide`）0 件

| 公理 | 定理の本数 |
|---|---:|
| `[propext, Classical.choice, Quot.sound]` | 77 |
| `[propext, Quot.sound]` | 24 |
| （公理なし） | 4 |
| `[propext]` | 3 |

## 入口から外したモジュール

無い。入口の `Principia.lean` が全モジュールを `import` する。

## Lean の外にあるもの

機械検査が保証するのは「書いてある命題からその結論が出ること」だけである。命題が意図した内容を書けているか、その主張が世の中で新しいかについて、機械は何も言わない。

コラッツ予想そのものは Lean の中に無い。入っているのは有限の、あるいは初等的な言明（臨界の乗数の唯一性・測度の恒等式・階段と枝の数え上げ・禁止語）だけで、それらを動機づける数値実験は Lean の外である。

各モジュールの冒頭のコメントに、何を Lean の中に入れ、何を外に置いたかを書いてある。

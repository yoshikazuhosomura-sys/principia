# lean/gp3-hamiltonian-count

Generalized Petersen graphs: for odd n ≥ 7, n divides the number of Hamiltonian cycles of GP(n,3).

一般化ペテルセングラフ：奇数 n ≥ 7 で n ∣ #HC(GP(n,3))。名前空間 `Principia.GeneralizedPetersen`。

## 対応する記事・論文

- 論文：https://computoergosum.com/principia/papers/gp3-hamiltonian-count.pdf（このリポジトリの `papers/gp3-hamiltonian-count/`）

## 中身

- モジュール 7 本・`#print axioms` の対象の定理 188 本
- Lean 4 `leanprover/lean4:v4.33.1`（`lean-toolchain`）・Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`（`lake-manifest.json` で固定）
- `sorry` 0・`native_decide` 不使用。**定理名は一つも変えていない**

## 建て方

```
lake exe cache get              # Mathlib のビルド済みキャッシュ
LEAN_NUM_THREADS=1 lake build Principia
```

**一本ずつ建てること。**証明の中に kernel へ大きな計算を閉じ込めるものがあり、lake の既定は CPU の数だけ同時に建てるので、`LEAN_NUM_THREADS=1` で絞る。**RAM は 16 GB を見込む。**

## 公理

各モジュールの末尾（または主題の `Chk` モジュール）に `#print axioms` が置いてあり、建てると依拠する公理がそのまま出力される。`axioms-gp3-hamiltonian-count.txt` はその出力をモジュールごとに並べたもの（188 行）。

- 全行が `propext`・`Classical.choice`・`Quot.sound`（Lean / Mathlib の標準三公理）の**部分集合**
- `sorryAx` 0 件・`Lean.ofReduceBool`（`native_decide`）0 件

| 公理 | 定理の本数 |
|---|---:|
| `[propext, Classical.choice, Quot.sound]` | 156 |
| `[propext, Quot.sound]` | 21 |
| `[propext]` | 8 |
| （公理なし） | 3 |

## 入口から外したモジュール

無い。入口の `Principia.lean` が全モジュールを `import` する。

## Lean の外にあるもの

機械検査が保証するのは「書いてある命題からその結論が出ること」だけである。命題が意図した内容を書けているか、その主張が世の中で新しいかについて、機械は何も言わない。

主定理（`GeneralizedPetersen.Descent.gp3_dvd_hc_odd`）と n = 7, …, 15 の五つの値が Lean に入っている。一般の n の証明に核計算は入っていない（小さい n の値の検査は核計算）。n ≤ 23 の全列挙と既知の表との一致は Lean の外の計算である。

各モジュールの冒頭のコメントに、何を Lean の中に入れ、何を外に置いたかを書いてある。

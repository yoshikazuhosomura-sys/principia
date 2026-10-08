# lean/erdos-827

Erdős problem #827: a machine-checked proof that n₄ = 7 (distinct circumradii), stated as `sInf {N | IsGood N} = 7`.

エルデシュ問題 #827（外接半径が相異なる 4 点）。`n₄ = 7` の機械検査された証明。名前空間 `Principia.DistinctCircumradii`。

## 対応する記事・論文

- 論文：https://computoergosum.com/principia/papers/erdos827-distinct-circumradii.pdf（このリポジトリの `papers/erdos827-distinct-circumradii/`）

## 中身

- モジュール 100 本・`#print axioms` の対象の定理 2414 本
- Lean 4 `leanprover/lean4:v4.33.1`（`lean-toolchain`）・Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`（`lake-manifest.json` で固定）
- `sorry` 0・`native_decide` 不使用。**定理名は一つも変えていない**

## 建て方

```
lake exe cache get              # Mathlib のビルド済みキャッシュ
LEAN_NUM_THREADS=1 lake build Principia
```

**一本ずつ建てること。**証明の中に kernel へ大きな計算を閉じ込めるものがあり、lake の既定は CPU の数だけ同時に建てるので、`LEAN_NUM_THREADS=1` で絞る。**RAM は 16 GB を見込む。**

## 公理

各モジュールの末尾（または主題の `Chk` モジュール）に `#print axioms` が置いてあり、建てると依拠する公理がそのまま出力される。`axioms-erdos-827.txt` はその出力をモジュールごとに並べたもの（2414 行）。

- 全行が `propext`・`Classical.choice`・`Quot.sound`（Lean / Mathlib の標準三公理）の**部分集合**
- `sorryAx` 0 件・`Lean.ofReduceBool`（`native_decide`）0 件

| 公理 | 定理の本数 |
|---|---:|
| `[propext, Classical.choice, Quot.sound]` | 2368 |
| `[propext, Quot.sound]` | 39 |
| `[propext]` | 7 |

## 入口から外したモジュール

無い。入口の `Principia.lean` が全モジュールを `import` する。

## Lean の外にあるもの

機械検査が保証するのは「書いてある命題からその結論が出ること」だけである。命題が意図した内容を書けているか、その主張が世の中で新しいかについて、機械は何も言わない。

鎖の全体（下界・上界・35 類の全数性・34 類の非実現・繋ぎ）が Lean の一本の言明で、仮定は無い。Lean の外にあるのは、探索木を Lean の部分木定理として書き出す証明書の生成と、枝の数・実測の記録だけである。census は機械の計算であって人が読み通せる形ではない。

各モジュールの冒頭のコメントに、何を Lean の中に入れ、何を外に置いたかを書いてある。

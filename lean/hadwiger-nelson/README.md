# lean/hadwiger-nelson

Unit-distance graphs: non-realisability of candidate classes (n = 10, 11, 16) and lower-bound witnesses for f(α), the largest unit-distance graph with independence number ≤ α.

単位距離グラフ：候補類の非実現（n = 10, 11, 16）と、独立数を抑えた単位距離グラフの下界の証人と族（ハドヴィガー・ネルソン系）。名前空間 `Principia.UnitDistance`・`Principia.HadwigerNelson`。

## 対応する記事・論文

- 記事：https://computoergosum.com/principia/hadwiger-nelson.html

## 中身

- モジュール 43 本・`#print axioms` の対象の定理 182 本
- Lean 4 `leanprover/lean4:v4.33.1`（`lean-toolchain`）・Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`（`lake-manifest.json` で固定）
- `sorry` 0・`native_decide` 不使用。**定理名は一つも変えていない**

## 建て方

```
lake exe cache get              # Mathlib のビルド済みキャッシュ
LEAN_NUM_THREADS=1 lake build Principia
```

**一本ずつ建てること。**証明の中に kernel へ大きな計算を閉じ込めるものがあり、lake の既定は CPU の数だけ同時に建てるので、`LEAN_NUM_THREADS=1` で絞る。**RAM は 16 GB を見込む。**

## 公理

各モジュールの末尾（または主題の `Chk` モジュール）に `#print axioms` が置いてあり、建てると依拠する公理がそのまま出力される。`axioms-hadwiger-nelson.txt` はその出力をモジュールごとに並べたもの（182 行）。

- 全行が `propext`・`Classical.choice`・`Quot.sound`（Lean / Mathlib の標準三公理）の**部分集合**
- `sorryAx` 0 件・`Lean.ofReduceBool`（`native_decide`）0 件

| 公理 | 定理の本数 |
|---|---:|
| `[propext, Classical.choice, Quot.sound]` | 161 |
| `[propext, Quot.sound]` | 16 |
| `[propext]` | 4 |
| （公理なし） | 1 |

## 入口から外したモジュール

無い。入口の `Principia.lean` が全モジュールを `import` する。

## Lean の外にあるもの

機械検査が保証するのは「書いてある命題からその結論が出ること」だけである。命題が意図した内容を書けているか、その主張が世の中で新しいかについて、機械は何も言わない。

Lean の外に残るのは組合せの側である——候補の列挙の完全性・枡ごとの同型判定・最小次数の導出。証明書の生成器（三辺測量の区間演算と分枝限定を出力する Python）も Lean の外で、Lean は出力された証明書を検査する。`f(α)` そのものの定義と最大性の主張も Lean の外に置いてある。

各モジュールの冒頭のコメントに、何を Lean の中に入れ、何を外に置いたかを書いてある。

# lean/erdos-169

Erdős problem #169: explicit 3-AP-free and 4-AP-free sets whose reciprocal sums exceed the known records (f(3) ≥ 3.0085385, f(4) ≥ 4.4397534742).

エルデシュ問題 #169（3-AP / 4-AP を含まない集合の逆数和）。逆数和が既知の記録を超える二つの明示的な集合。名前空間 `Principia.APFree`。

## 対応する記事・論文

- 記事：https://computoergosum.com/principia/erdos-169.html
- 論文：https://computoergosum.com/principia/papers/erdos169-ap-free-reciprocal-sums.pdf（このリポジトリの `papers/erdos169-ap-free-reciprocal-sums/`）

## 中身

- モジュール 64 本・`#print axioms` の対象の定理 223 本
- Lean 4 `leanprover/lean4:v4.33.1`（`lean-toolchain`）・Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`（`lake-manifest.json` で固定）
- `sorry` 0・`native_decide` 不使用。**定理名は一つも変えていない**

## 建て方

```
lake exe cache get              # Mathlib のビルド済みキャッシュ
LEAN_NUM_THREADS=1 lake build Principia
```

**一本ずつ建てること。**証明の中に kernel へ大きな計算を閉じ込めるものがあり、lake の既定は CPU の数だけ同時に建てるので、`LEAN_NUM_THREADS=1` で絞る。**RAM は 16 GB を見込む。**

## 公理

各モジュールの末尾（または主題の `Chk` モジュール）に `#print axioms` が置いてあり、建てると依拠する公理がそのまま出力される。`axioms-erdos-169.txt` はその出力をモジュールごとに並べたもの（223 行）。

- 全行が `propext`・`Classical.choice`・`Quot.sound`（Lean / Mathlib の標準三公理）の**部分集合**
- `sorryAx` 0 件・`Lean.ofReduceBool`（`native_decide`）0 件

| 公理 | 定理の本数 |
|---|---:|
| `[propext, Classical.choice, Quot.sound]` | 138 |
| `[propext]` | 35 |
| （公理なし） | 31 |
| `[propext, Quot.sound]` | 19 |

## 入口から外したモジュール

無い。入口の `Principia.lean` が全モジュールを `import` する。

## Lean の外にあるもの

機械検査が保証するのは「書いてある命題からその結論が出ること」だけである。命題が意図した内容を書けているか、その主張が世の中で新しいかについて、機械は何も言わない。

Lean の外に置いたのは、段の選び方（対数尺度の上の動的計画法。浮動小数の見積りを使うが、下界の正しさには関わらない）と、Walker の Kempner 集合の逆数和の値そのもの（整数演算で幅 10⁻³² に挟んだもの）、および二つの和のより細かい値である。

各モジュールの冒頭のコメントに、何を Lean の中に入れ、何を外に置いたかを書いてある。

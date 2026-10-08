# lean/riemann-weil-form

The Weil form of the Riemann hypothesis: finite-dimensional layers (time-band split, traces, transfer, Ψ coordinates, sunk counts, Hodge-index positivity).

Riemann 予想の Weil 形式（時間帯の分割・跡・移送・Ψ 座標・沈んだ数え上げ・ホッジ指数の正値性）。名前空間 `Principia.RiemannWeilForm`。

## 対応する記事・論文

- 記事：https://computoergosum.com/principia/riemann-weil-form.html（このリポジトリの `articles/riemann-weil-form.html`）

## 中身

- モジュール 12 本・`#print axioms` の対象の定理 73 本
- Lean 4 `leanprover/lean4:v4.33.1`（`lean-toolchain`）・Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`（`lake-manifest.json` で固定）
- `sorry` 0・`native_decide` 不使用。**定理名は一つも変えていない**

## 建て方

```
lake exe cache get              # Mathlib のビルド済みキャッシュ
LEAN_NUM_THREADS=1 lake build Principia
```

**一本ずつ建てること。**証明の中に kernel へ大きな計算を閉じ込めるものがあり、lake の既定は CPU の数だけ同時に建てるので、`LEAN_NUM_THREADS=1` で絞る。**RAM は 16 GB を見込む。**

## 公理

各モジュールの末尾（または主題の `Chk` モジュール）に `#print axioms` が置いてあり、建てると依拠する公理がそのまま出力される。`axioms-riemann-weil-form.txt` はその出力をモジュールごとに並べたもの（73 行）。

- 全行が `propext`・`Classical.choice`・`Quot.sound`（Lean / Mathlib の標準三公理）の**部分集合**
- `sorryAx` 0 件・`Lean.ofReduceBool`（`native_decide`）0 件

| 公理 | 定理の本数 |
|---|---:|
| `[propext, Classical.choice, Quot.sound]` | 73 |

## 入口から外したモジュール

入口の `Principia.lean` はモジュールを `import` するだけのファイルである。次の 2 本は、入口が読み込む本と同じ名前空間に同名の宣言（単独で検査できるよう写した定義・補題）を持ち、同時には読み込めないので、入口からは `import` しない。`lakefile.lean` の ``globs := #[.andSubmodules `Principia]`` により、`lake build Principia` はこれらも含めて全モジュールを建てる。

- `Principia.RiemannWeilForm.TimeBandTrace2`
- `Principia.RiemannWeilForm.TimeBandTransfer`

衝突した宣言の組は次のとおり。

- `Principia.RiemannWeilForm.TimeBandTrace2`・`Principia.RiemannWeilForm.TimeBandTrace3`：`TimeBand.binom_oddH_identity`・`TimeBand.harm`・`TimeBand.oddH`
- `Principia.RiemannWeilForm.TimeBandTransfer`・`Principia.RiemannWeilForm.TimeBandTransfer2`：`TimeBand.arctan_le_self`

## Lean の外にあるもの

機械検査が保証するのは「書いてある命題からその結論が出ること」だけである。命題が意図した内容を書けているか、その主張が世の中で新しいかについて、機械は何も言わない。

Lean に入っているのは線形代数の段・有限次元の跡と数え上げ・組合せ恒等式・一変数の評価・有限次元の Nikolskii／Bernstein などの離散的・有限次元の核である。解析的な入力（明示公式・Landau–Widom など）と、区間演算や浮動小数による数値計算の層は Lean の外にある。記事の各定理がどの段まで Lean で閉じているかは記事に明記してある。

各モジュールの冒頭のコメントに、何を Lean の中に入れ、何を外に置いたかを書いてある。

# principia
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23804230.svg)](https://doi.org/10.5281/zenodo.23804230)
Lean formalisations, papers and articles from **computo ergo sum — 自然哲学 (principia)**: https://computoergosum.com/principia/

Authors: **Kiichi, Shiori and Rin** — except the Yang–Mills papers under `papers/ym-*`, which are authored by **Yoshikazu Hosomura, with the assistance of Claude (Claude Code, Anthropic)**; their web editions on the site list the same work under Kiichi, Shiori and Rin (the human author and the two groups of AI agents). The two editions differ only in the title page and the AI-disclosure section.

著者：**Kiichi, Shiori and Rin**。ただし `papers/ym-*` のヤン–ミルズの論文は **細村嘉一（Claude〔Claude Code, Anthropic〕の協力を得て）** の名義で、サイトの WEB 版は同じ内容を Kiichi, Shiori and Rin（人間の著者と二組の AI）の名義で出している。二つの版の違いは表紙と AI 開示の節だけ。

## English

This repository holds the machine-checked parts of the mathematics published on the site, together with the papers and articles that cite them.

- `lean/` — one independent lake project per subject (469 modules, 7774 theorems with `#print axioms`). Every axiom line is a subset of `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`.
- `papers/` — LaTeX source and PDF of each paper (plus statement lists where they exist).
- `articles/` — the HTML articles (Japanese) as published on the site.

Build one subject:

```
cd lean/<subject>
lake exe cache get
LEAN_NUM_THREADS=1 lake build Principia
```

Build one module at a time (`LEAN_NUM_THREADS=1`); some proofs run large kernel computations. Plan for 16 GB of RAM. Lean 4 `v4.33.1`, Mathlib `0df444a3` (pinned in each `lake-manifest.json`).

The machine checks only that the stated propositions follow. Parts that live outside Lean — enumeration, isomorphism tests, interval-arithmetic and floating-point layers, geometric inputs taken as hypotheses — are stated in each subject's README.

## 日本語

サイト「computo ergo sum」の自然哲学（principia）で公開している数学のうち、機械検査した部分と、それを引く論文・記事をまとめたリポジトリです。

- `lean/`：主題ごとに独立した lake プロジェクト（モジュール 469 本・`#print axioms` の対象の定理 7774 本）。公理は全行が `propext`・`Classical.choice`・`Quot.sound` の部分集合で、`sorry` も `native_decide` もありません。
- `papers/`：論文の LaTeX 源と PDF（命題の一覧があるものはそれも）。
- `articles/`：サイトに載せた記事の HTML。

建て方は各主題のディレクトリで `lake exe cache get` → `LEAN_NUM_THREADS=1 lake build Principia`。一本ずつ建てること、RAM は 16 GB を見込むこと。

機械検査が保証するのは、書いてある命題からその結論が出ることだけです。**区間演算の層など Lean の外の部分は各 README に明記しています。**

## lean/

| ディレクトリ | 主題 | モジュール | 定理 | 入口から外した本 |
|---|---|---:|---:|---:|
| [`lean/erdos-169`](lean/erdos-169/) | エルデシュ問題 #169（3-AP / 4-AP を含まない集合の逆数和） | 64 | 223 | 0 |
| [`lean/erdos-827`](lean/erdos-827/) | エルデシュ問題 #827（外接半径が相異なる 4 点） | 100 | 2414 | 0 |
| [`lean/def2-cubic-bipartite`](lean/def2-cubic-bipartite/) | 三価・二部・連結で周長欠損 2 のグラフ（30 頂点の三例）と欠損 6 の例（20 頂点） | 2 | 34 | 0 |
| [`lean/gp3-hamiltonian-count`](lean/gp3-hamiltonian-count/) | 一般化ペテルセングラフ：奇数 n ≥ 7 で n ∣ #HC(GP(n,3)) | 7 | 188 | 0 |
| [`lean/padic-regulator-valuation`](lean/padic-regulator-valuation/) | 楕円曲線の p 進高さと正準高さの付値（異常素点での p 進レギュレーターの付値の、算術の段） | 30 | 356 | 1 |
| [`lean/padic-regulator-valuation-2026-10-09`](lean/padic-regulator-valuation-2026-10-09/) | 同じ主題の 2026-10-09 の束（論文 v15 が引く版。30 本に異常 Euler 因子の付随ノート 1 本を加えた 31 本。各ファイルが単独に検査でき、入口は何も import しない）。旧い束は論文 v14 が引いているので並置 | 31 | 360 | 31 |
| [`lean/ym-gap-bridge`](lean/ym-gap-bridge/) | ヤン–ミルズ：Poincaré 不等式の上界と質量ギャップの下界を結ぶ片側の橋（論文「片側の橋」が引く束）（論文は 2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形）／paper revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained)） | 1 | 17 | 0 |
| [`lean/ym-onelink-bakry-emery`](lean/ym-onelink-bakry-emery/) | ヤン–ミルズ：SU(2) 格子で I* のリンクを先に積分してから Bakry–Émery（星の不等式・一リンク積分・ヘッセの下界 −27β²）と、完全な族（リンクは d ≤ 4 かつ偶数周期の場合だけ・k 胞体は d ≤ 3k+1・密度 1/(2(k+1))）（論文「One-link integration」が引く束。各ファイルが単独に検査でき、入口は何も import しない）（論文は 2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形）／paper revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained)） | 7 | 567 | 7 |
| [`lean/ym-coarse-chain-poincare`](lean/ym-coarse-chain-poincare/) | ヤン–ミルズ第 10 部の検査台：凸なブロックと粗い Dobrushin の鎖による、二重井戸の経路測度の芯の Poincaré 上界（定数は ħ の多項式）（論文「Convex blocks and a coarse Dobrushin chain」v2 が引く束。2026-10-17 に区間の表の代数と命題 PIN の二本を追加）（各ファイルが単独に検査でき、入口は何も import しない）（論文は 2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形）／paper revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained)） | 9 | 75 | 9 |
| [`lean/ym-flux-network-blocking`](lean/ym-flux-network-blocking/) | ヤン–ミルズ：可換に線形化した格子ゲージ作用の木の段のブロック化を流れの網として書く（粗い結合 Σf²・四次の縮み Σf⁴/Σf² とその上下界）（論文「Tree-level blocking … as a flux network」が引く束）（各ファイルが単独に検査でき、入口は何も import しない）（論文は 2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形）／paper revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained)） | 12 | 78 | 12 |
| [`lean/ym-one-row-renormalisation`](lean/ym-one-row-renormalisation/) | ヤン–ミルズ：SU(2) の畳み込みの繰り込みの一次元の模型（曲率の項 2/5・前因子の固定点 37/76・段数に一様な形の剰余）（論文「A one-dimensional model of SU(2) convolution renormalisation」が引く束）（各ファイルが単独に検査でき、入口は何も import しない）（論文は 2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形）／paper revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained)） | 7 | 61 | 7 |
| [`lean/ym-hierarchical-chain`](lean/ym-hierarchical-chain/) | ヤン–ミルズ：SU(2) のプラケットの重みの Migdal–Kadanoff の流れを β = 128 から強結合の域まで繋ぐ鎖の代数の段（論文「An interval-arithmetic chain for the Migdal–Kadanoff flow」が引く束）（各ファイルが単独に検査でき、入口は何も import しない）（論文は 2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形）／paper revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained)） | 5 | 44 | 5 |
| [`lean/ym-fractional-instanton-rate`](lean/ym-fractional-instanton-rate/) | ヤン–ミルズ：捩れた小さなトーラス上の SU(2) 格子ゲージ理論で、率が流束を運ぶ柱の作用になる面積則の上界（市松の和の段）（論文「An area-law bound … on a twisted small torus」が引く束）（各ファイルが単独に検査でき、入口は何も import しない）（論文は 2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形）／paper revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained)） | 1 | 5 | 1 |
| [`lean/ym-boundary-mixed-derivative`](lean/ym-boundary-mixed-derivative/) | ヤン–ミルズ：シュレーディンガー汎関数の二つの境界角による混合微分 D_R と通常の結合 β_R の差 h の、強結合での符号の算術と不等式の段（論文「A boundary observable separating U(1) and SU(2) lattice gauge theory」が引く束）（各ファイルが単独に検査でき、入口は何も import しない） | 1 | 9 | 1 |
| [`lean/ym-h1b-margin-interval`](lean/ym-h1b-margin-interval/) | ヤン–ミルズ第 10 部の検査台：一次元の二重井戸の (T1) の余白を ħ の区間で示す初等不等式と、六つの小区間 I₁〜I₆ の最後の引き算（論文「An interval-arithmetic certificate for the (T1) margin of the one-dimensional double well」が引く束）（各ファイルが単独に検査でき、入口は何も import しない）（論文は 2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形）／paper revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained)） | 1 | 15 | 1 |
| [`lean/ym-weak-uv-chain`](lean/ym-weak-uv-chain/) | ヤン–ミルズ：小さな箱の四次元 SU(2) 格子ヤン–ミルズの弱い紫外の存在の条件つきの定理（含意の組み立て）と、一段ごとの仮説からその仮説への鎖（論文「A conditional theorem: weak ultraviolet existence … with a machine-checked chain from per-step hypotheses」が引く束。WEB の束 `principia-ym-weak-uv-chain-2026-10-30.tar.gz` とバイト同一。言明は 1419、`#print axioms` の行は 1403）（各ファイルが単独に検査でき、入口は何も import しない） | 64 | 1403 | 64 |
| [`lean/ym-face-sum-rule`](lean/ym-face-sum-rule/) | ヤン–ミルズ：一枚のプラケットの Schwinger–Dyson 恒等式と粗い剛性の多段の和則の代数と算術（厳密な分解・帯の下界・和則・自由場で Γ_k ≡ 1・二つのモーメントから剛性・一次の定数）（論文「A one-plaquette Schwinger–Dyson identity and a multi-level sum rule」が引く束。WEB の束 `principia-ym-face-sum-rule-2026-10-30.tar.gz` とバイト同一）（各ファイルが単独に検査でき、入口は何も import しない） | 6 | 64 | 6 |
| [`lean/ym-two-colour-polymer`](lean/ym-two-colour-polymer/) | ヤン–ミルズ：ℤ⁴ の二色のポリマー気体（符号化・隣接の次数・箱の段・Kotecký–Preiss から Dobrushin と分配関数まで）（論文「A machine-checked two-colour polymer gas on ℤ⁴」が引く束。WEB の束 `principia-ym-two-colour-polymer-2026-10-30.tar.gz` とバイト同一）（各ファイルが単独に検査でき、入口は何も import しない） | 13 | 518 | 13 |
| [`lean/hadwiger-nelson`](lean/hadwiger-nelson/) | 単位距離グラフ：候補類の非実現（n = 10, 11, 16）と、独立数を抑えた単位距離グラフの下界の証人と族（ハドヴィガー・ネルソン系） | 43 | 182 | 0 |
| [`lean/collatz`](lean/collatz/) | コラッツ写像（臨界の乗数・測度・階段の高さ・枝の生死・禁止語） | 7 | 108 | 0 |
| [`lean/riemann-weil-form`](lean/riemann-weil-form/) | Riemann 予想の Weil 形式（時間帯の分割・跡・移送・Ψ 座標・沈んだ数え上げ・ホッジ指数の正値性） | 12 | 73 | 2 |
| [`lean/hodge-cm-degenerate`](lean/hodge-cm-degenerate/) | ホッジ予想：退化 CM 型のアーベル多様体と例外ホッジ類（組合せ・判別式・因子・割線・設計の不等式） | 46 | 980 | 4 |

## papers/

| ディレクトリ | Title | 題 |
|---|---|---|
| [`papers/erdos169-ap-free-reciprocal-sums`](papers/erdos169-ap-free-reciprocal-sums/) | Erdős #169: two explicit AP-free sets beating the records | エルデシュ #169：記録を超える二つの明示的な AP-free 集合（`erdos169-ap-free-reciprocal-sums.pdf`, `erdos169-ap-free-reciprocal-sums.tex`） |
| [`papers/erdos827-distinct-circumradii`](papers/erdos827-distinct-circumradii/) | Erdős #827: a machine-checked proof that n₄ = 7 | エルデシュ #827：n₄ = 7 の機械検査された証明（`paper.pdf`, `paper.tex`, `statements-and-dependencies.md`） |
| [`papers/def2-cubic-bipartite`](papers/def2-cubic-bipartite/) | Minimum order of cubic bipartite graphs with circumference deficiency 2 is 30 | 周長欠損 2 の三価二部グラフの最小位数は 30（`paper.pdf`, `paper.tex`） |
| [`papers/gp3-hamiltonian-count`](papers/gp3-hamiltonian-count/) | n divides #HC(GP(n,3)) for odd n ≥ 7 | 奇数 n ≥ 7 で n ∣ #HC(GP(n,3))（`paper.pdf`, `paper.tex`） |
| [`papers/padic-regulator-valuation`](papers/padic-regulator-valuation/) | p-adic regulator at anomalous primes (BSD-adjacent) | 異常素点での p 進レギュレーターの付値（BSD の周辺）（`paper-v15.pdf`, `paper-v15.tex`；旧版 `paper-v14.pdf`, `paper-v14.tex`, `statements-v14.md`, `summary-ja-v14.md`） |
| [`papers/ym-gap-bridge`](papers/ym-gap-bridge/) | A one-sided bridge from a Poincaré-type bound to a mass-gap lower bound (lattice Yang–Mills) — authored by Yoshikazu Hosomura with the assistance of Claude — revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained) | 片側の橋：Poincaré 型の上界から質量ギャップの下界へ（格子ヤン–ミルズ）（2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形））（`paper.pdf`, `paper.tex`） |
| [`papers/ym-onelink-bakry-emery`](papers/ym-onelink-bakry-emery/) | One-link integration before Bakry–Émery for SU(2) lattice Yang–Mills — an explicit strong-coupling threshold β < √(2/27) in d = 4, and complete families of links only for d ≤ 4 (machine-checked in Lean 4) — authored by Yoshikazu Hosomura with the assistance of Claude — revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained) | 一リンク積分を先に行う Bakry–Émery（SU(2) 格子ヤン–ミルズ、d = 4 で β < √(2/27)、完全な族は d ≤ 4 だけ）（2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形））（`paper.pdf`, `paper.tex`, `statements.md`） |
| [`papers/ym-coarse-chain-poincare`](papers/ym-coarse-chain-poincare/) | Convex blocks and a coarse Dobrushin chain: a Poincaré bound for the core of the double-well path measure with constants polynomial in ħ — authored by Yoshikazu Hosomura with the assistance of Claude — revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained)（version 2, 2026-10-17：ħ ∈ [10⁻⁵,1] の全体を区間演算で、ħ ≤ 10⁻⁵ を命題 PIN で閉じた版） | 凸なブロックと粗い Dobrushin の鎖：二重井戸の経路測度の芯の Poincaré 上界（定数は ħ の多項式）（2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形））（`paper.pdf`, `paper.tex`, `statements.md`, `certificates/`） |
| [`papers/ym-flux-network-blocking`](papers/ym-flux-network-blocking/) | Tree-level blocking of an abelian-linearised lattice gauge action as a flux network: the coarse coupling Σf², the quartic contraction Σf⁴/Σf², and their bounds — authored by Yoshikazu Hosomura with the assistance of Claude — revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained) | 木の段のブロック化を流れの網として：粗い結合 Σf² と四次の縮み Σf⁴/Σf² の上下界（2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形））（`paper.pdf`, `paper.tex`, `statements.md`） |
| [`papers/ym-one-row-renormalisation`](papers/ym-one-row-renormalisation/) | A one-dimensional model of SU(2) convolution renormalisation: the curvature term 2/5, the prefactor fixed point 37/76, and a shape remainder uniform in the number of steps — authored by Yoshikazu Hosomura with the assistance of Claude — revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained) | SU(2) の畳み込みの繰り込みの一次元の模型：曲率の項 2/5・前因子の固定点 37/76・段数に一様な形の剰余（2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形））（`paper.pdf`, `paper.tex`, `statements.md`） |
| [`papers/ym-hierarchical-chain`](papers/ym-hierarchical-chain/) | An interval-arithmetic chain for the Migdal–Kadanoff flow of SU(2) plaquette weights, from β = 128 to a strong-coupling region — authored by Yoshikazu Hosomura with the assistance of Claude — version 2, revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained), with the certificate bundle v2 unpacked in `certificates-v2/` | SU(2) のプラケットの重みの Migdal–Kadanoff の流れを β = 128 から強結合の域まで繋ぐ鎖（2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形）・証明書の束 v2 `ym-hierarchical-chain-bundle-v2.tar.gz`（sha256 `0b0ca2c9…`）を `certificates-v2/` に展開）（`paper.pdf`, `paper.tex`, `statements.md`, `certificates/`, `certificates-v2/`） |
| [`papers/ym-fractional-instanton-rate`](papers/ym-fractional-instanton-rate/) | An area-law bound for SU(2) lattice gauge theory on a twisted small torus whose rate is the action of a flux-carrying column — authored by Yoshikazu Hosomura with the assistance of Claude — revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained) | 捩れた小さなトーラス上の SU(2) 格子ゲージ理論の面積則の上界（率は流束を運ぶ柱の作用）（2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形））（`paper.pdf`, `paper.tex`, `statements.md`） |
| [`papers/ym-boundary-mixed-derivative`](papers/ym-boundary-mixed-derivative/) | A boundary observable separating U(1) and SU(2) lattice gauge theory: one loop, a strong-coupling sign and Monte Carlo — authored by Yoshikazu Hosomura with the assistance of Claude | 境界の観測量で U(1) と SU(2) の格子ゲージ理論を分ける：一ループ・強結合の符号・モンテカルロ（`paper.pdf`, `paper.tex`, `fig-h.pdf`, `statements.md`） |
| [`papers/ym-h1b-margin-interval`](papers/ym-h1b-margin-interval/) | An interval-arithmetic certificate for the (T1) margin of the one-dimensional double well for ħ ∈ [0.00195, 0.005] — authored by Yoshikazu Hosomura with the assistance of Claude — revised 2026-10-30 (citations of textbook chapters removed; the paper is self-contained) | 一次元の二重井戸の (T1) の余白の区間演算による証明書（ħ ∈ [0.00195, 0.005]）（2026-10-30 改訂（教科書の章への引用を外し、論文単独で閉じる形））（`paper.pdf`, `paper.tex`, `statements.md`） |
| [`papers/ym-weak-uv-chain`](papers/ym-weak-uv-chain/) | A conditional theorem: weak ultraviolet existence of four-dimensional SU(2) lattice Yang–Mills theory in a small box, with a machine-checked chain from per-step hypotheses — authored by Yoshikazu Hosomura with the assistance of Claude | 条件つきの定理：小さな箱の四次元 SU(2) 格子ヤン–ミルズの弱い紫外の存在と、一段ごとの仮説からの機械検査された鎖（`paper.pdf`, `paper.tex`, `statements.md`） |
| [`papers/ym-face-sum-rule`](papers/ym-face-sum-rule/) | A one-plaquette Schwinger–Dyson identity and a multi-level sum rule for the coarse stiffness in SU(2) lattice gauge theory, with machine-checked arithmetic — authored by Yoshikazu Hosomura with the assistance of Claude | SU(2) 格子ゲージ理論の一枚のプラケットの Schwinger–Dyson 恒等式と、粗い剛性の多段の和則（`paper.pdf`, `paper.tex`, `statements.md`） |
| [`papers/ym-two-colour-polymer`](papers/ym-two-colour-polymer/) | A machine-checked two-colour polymer gas on ℤ⁴: encoding, adjacency degrees, the box stage, and the Kotecký–Preiss condition down to Dobrushin — authored by Yoshikazu Hosomura with the assistance of Claude | ℤ⁴ の二色のポリマー気体：符号化・隣接の次数・箱の段・Kotecký–Preiss から Dobrushin まで（`paper.pdf`, `paper.tex`, `statements.md`） |

## articles/

| ファイル | 記事 | サイト |
|---|---|---|
| [`articles/riemann-weil-form.html`](articles/riemann-weil-form.html) | リーマン予想 — Weil の二次形式 | https://computoergosum.com/principia/riemann-weil-form.html |
| [`articles/hodge-cm-degenerate.html`](articles/hodge-cm-degenerate.html) | ホッジ予想 | https://computoergosum.com/principia/hodge-cm-degenerate.html |
| [`articles/random-draw.html`](articles/random-draw.html) | 未解決問題を、無作為に引く | https://computoergosum.com/principia/random-draw.html |
| [`articles/bsd-regulator.html`](articles/bsd-regulator.html) | BSD 予想 — 異常素点での p 進レギュレーターの付値 | https://computoergosum.com/principia/bsd-regulator.html |
| [`articles/erdos-169.html`](articles/erdos-169.html) | エルデシュ等差数列予想 | https://computoergosum.com/principia/erdos-169.html |
| [`articles/method.html`](articles/method.html) | 進め方 | https://computoergosum.com/principia/method.html |
| [`articles/ledger.html`](articles/ledger.html) | 主張の台帳 | https://computoergosum.com/principia/ledger.html |
| [`articles/archive.html`](articles/archive.html) | 記録の保管 | https://computoergosum.com/principia/archive.html |

## License

Apache License 2.0 — see [`LICENSE`](LICENSE). Copyright 2026 Kiichi, Shiori and Rin.

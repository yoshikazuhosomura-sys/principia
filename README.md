# principia
[![DOI](https://zenodo.org/badge/1409514158.svg)](https://doi.org/10.5281/zenodo.23296340)

Lean formalisations, papers and articles from **computo ergo sum — 自然哲学 (principia)**: https://computoergosum.com/principia/

Authors: **Kiichi, Shiori and Rin** — except the Yang–Mills papers under `papers/ym-*`, which are authored by **Yoshikazu Hosomura, with the assistance of Claude (Claude Code, Anthropic)**; their web editions on the site list the same work under Kiichi, Shiori and Rin (the human author and the two groups of AI agents). The two editions differ only in the title page and the AI-disclosure section.

著者：**Kiichi, Shiori and Rin**。ただし `papers/ym-*` のヤン–ミルズの論文は **細村嘉一（Claude〔Claude Code, Anthropic〕の協力を得て）** の名義で、サイトの WEB 版は同じ内容を Kiichi, Shiori and Rin（人間の著者と二組の AI）の名義で出している。二つの版の違いは表紙と AI 開示の節だけ。

## English

This repository holds the machine-checked parts of the mathematics published on the site, together with the papers and articles that cite them.

- `lean/` — one independent lake project per subject (343 modules, 4935 theorems with `#print axioms`). Every axiom line is a subset of `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`.
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

- `lean/`：主題ごとに独立した lake プロジェクト（モジュール 343 本・`#print axioms` の対象の定理 4935 本）。公理は全行が `propext`・`Classical.choice`・`Quot.sound` の部分集合で、`sorry` も `native_decide` もありません。
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
| [`lean/ym-gap-bridge`](lean/ym-gap-bridge/) | ヤン–ミルズ：Poincaré 不等式の上界と質量ギャップの下界を結ぶ片側の橋（論文「片側の橋」が引く束） | 1 | 17 | 0 |
| [`lean/ym-onelink-bakry-emery`](lean/ym-onelink-bakry-emery/) | ヤン–ミルズ：SU(2) 格子で I* のリンクを先に積分してから Bakry–Émery（星の不等式・一リンク積分・ヘッセの下界 −27β²）と、完全な族（リンクは d ≤ 4 かつ偶数周期の場合だけ・k 胞体は d ≤ 3k+1・密度 1/(2(k+1))）（論文「One-link integration」が引く束。各ファイルが単独に検査でき、入口は何も import しない） | 7 | 567 | 7 |
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
| [`papers/ym-gap-bridge`](papers/ym-gap-bridge/) | A one-sided bridge from a Poincaré-type bound to a mass-gap lower bound (lattice Yang–Mills) — authored by Yoshikazu Hosomura with the assistance of Claude | 片側の橋：Poincaré 型の上界から質量ギャップの下界へ（格子ヤン–ミルズ）（`paper.pdf`, `paper.tex`） |
| [`papers/ym-onelink-bakry-emery`](papers/ym-onelink-bakry-emery/) | One-link integration before Bakry–Émery for SU(2) lattice Yang–Mills — an explicit strong-coupling threshold β < √(2/27) in d = 4, and complete families of links only for d ≤ 4 (machine-checked in Lean 4) — authored by Yoshikazu Hosomura with the assistance of Claude | 一リンク積分を先に行う Bakry–Émery（SU(2) 格子ヤン–ミルズ、d = 4 で β < √(2/27)、完全な族は d ≤ 4 だけ）（`paper.pdf`, `paper.tex`, `statements.md`） |

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

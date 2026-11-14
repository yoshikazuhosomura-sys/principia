# principia
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24232749.svg)](https://doi.org/10.5281/zenodo.24232749)

Lean formalisations, papers and articles from **computo ergo sum — 自然哲学 (principia)**: https://computoergosum.com/principia/

Authors: **Kiichi, Shiori and Rin** — except the withdrawn paper `papers/ym-weak-uv-chain` and its Lean project `lean/ym-weak-uv-chain`, which are authored by **Yoshikazu Hosomura, with the assistance of Claude (Claude Code, Anthropic)**.

著者：**Kiichi, Shiori and Rin**。ただし、取り下げた論文 `papers/ym-weak-uv-chain` と、その Lean の束 `lean/ym-weak-uv-chain` は **細村嘉一（Claude〔Claude Code, Anthropic〕の協力を得て）** の名義。

## English

This repository holds the machine-checked parts of the mathematics published on the site, together with the papers and articles that cite them.

- `lean/` — one independent lake project per subject (345 modules, 5605 theorems with `#print axioms`). Every axiom line is a subset of `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`.
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

## Moved

- **Yang–Mills.** The Yang–Mills papers (`papers/ym-*`, except `ym-weak-uv-chain`) and their Lean projects (`lean/ym-*`, except `ym-weak-uv-chain`) are now kept in the repository [lattice-yang-mills](https://github.com/yoshikazuhosomura-sys/lattice-yang-mills), in the versions revised on 2026-11-14 and 2026-11-15. The versions that were here remain in release v1.1.0 of this repository and in its Zenodo record.
- **p-adic heights.** The paper on the p-adic regulator at anomalous primes (`papers/padic-regulator-valuation`) and its Lean projects (`lean/padic-regulator-valuation`, `lean/padic-regulator-valuation-2026-10-09`) are now kept, revised and split into two papers, in the repository [padic-height-anomalous](https://github.com/yoshikazuhosomura-sys/padic-height-anomalous). The versions that were here remain in release v1.1.0.
- **Withdrawn.** `papers/ym-weak-uv-chain` was withdrawn on 2026-11-13. Its notice ([`WITHDRAWN.md`](papers/ym-weak-uv-chain/WITHDRAWN.md)) and its Lean project `lean/ym-weak-uv-chain` stay in this repository.

## 日本語

サイト「computo ergo sum」の自然哲学（principia）で公開している数学のうち、機械検査した部分と、それを引く論文・記事をまとめたリポジトリです。

- `lean/`：主題ごとに独立した lake プロジェクト（モジュール 345 本・`#print axioms` の対象の定理 5605 本）。公理は全行が `propext`・`Classical.choice`・`Quot.sound` の部分集合で、`sorry` も `native_decide` もありません。
- `papers/`：論文の LaTeX 源と PDF（命題の一覧があるものはそれも）。
- `articles/`：サイトに載せた記事の HTML。

建て方は各主題のディレクトリで `lake exe cache get` → `LEAN_NUM_THREADS=1 lake build Principia`。一本ずつ建てること、RAM は 16 GB を見込むこと。

機械検査が保証するのは、書いてある命題からその結論が出ることだけです。**区間演算の層など Lean の外の部分は各 README に明記しています。**

## 移したもの

- **ヤン–ミルズ。** ヤン–ミルズの論文（`papers/ym-*`。`ym-weak-uv-chain` を除く）と、その Lean の束（`lean/ym-*`。同じく除く）は、2026-11-14 と 2026-11-15 に改訂した版を、リポジトリ [lattice-yang-mills](https://github.com/yoshikazuhosomura-sys/lattice-yang-mills) に置いています。ここに在った版は、このリポジトリの v1.1.0 と、その Zenodo の記録に残っています。
- **p 進高さ。** 異常素点での p 進レギュレーターの論文（`papers/padic-regulator-valuation`）と、その Lean の束（`lean/padic-regulator-valuation`・`lean/padic-regulator-valuation-2026-10-09`）は、改訂して二本に分けた形で、リポジトリ [padic-height-anomalous](https://github.com/yoshikazuhosomura-sys/padic-height-anomalous) に置いています。ここに在った版は v1.1.0 に残っています。
- **取り下げ。** `papers/ym-weak-uv-chain` は 2026-11-13 に取り下げました。告知（[`WITHDRAWN.md`](papers/ym-weak-uv-chain/WITHDRAWN.md)）と Lean の束 `lean/ym-weak-uv-chain` は、このリポジトリに残しています。

## lean/

| ディレクトリ | 主題 | モジュール | 定理 | 入口から外した本 |
|---|---|---:|---:|---:|
| [`lean/erdos-169`](lean/erdos-169/) | エルデシュ問題 #169（3-AP / 4-AP を含まない集合の逆数和） | 64 | 223 | 0 |
| [`lean/erdos-827`](lean/erdos-827/) | エルデシュ問題 #827（外接半径が相異なる 4 点） | 100 | 2414 | 0 |
| [`lean/def2-cubic-bipartite`](lean/def2-cubic-bipartite/) | 三価・二部・連結で周長欠損 2 のグラフ（30 頂点の三例）と欠損 6 の例（20 頂点） | 2 | 34 | 0 |
| [`lean/gp3-hamiltonian-count`](lean/gp3-hamiltonian-count/) | 一般化ペテルセングラフ：奇数 n ≥ 7 で n ∣ #HC(GP(n,3)) | 7 | 188 | 0 |
| [`lean/ym-weak-uv-chain`](lean/ym-weak-uv-chain/) | ヤン–ミルズ：小さな箱の四次元 SU(2) 格子ヤン–ミルズの弱い紫外の存在の条件つきの定理（含意の組み立て）と、一段ごとの仮説からその仮説への鎖（論文「A conditional theorem: weak ultraviolet existence … with a machine-checked chain from per-step hypotheses」が引く束。WEB の束 `principia-ym-weak-uv-chain-2026-10-30.tar.gz` とバイト同一。言明は 1419、`#print axioms` の行は 1403）（各ファイルが単独に検査でき、入口は何も import しない）（**この束を引く論文は 2026-11-13 に取り下げた**。[`WITHDRAWN.md`](papers/ym-weak-uv-chain/WITHDRAWN.md)。束の定理は、Lean の言明のとおりのことだけを述べる） | 64 | 1403 | 64 |
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
| [`papers/ym-weak-uv-chain`](papers/ym-weak-uv-chain/) | **Withdrawn on 2026-11-13** — A conditional theorem: weak ultraviolet existence of four-dimensional SU(2) lattice Yang–Mills theory in a small box, with a machine-checked chain from per-step hypotheses (2026-10-30). Reasons: [`WITHDRAWN.md`](papers/ym-weak-uv-chain/WITHDRAWN.md) | **2026-11-13 に取り下げ**。条件つきの定理：小さな箱の四次元 SU(2) 格子ヤン–ミルズの弱い紫外の存在（2026-10-30）。理由は [`WITHDRAWN.md`](papers/ym-weak-uv-chain/WITHDRAWN.md)。公開した時点のファイルは版 v1.1.0 に残る |

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

# Withdrawn — 取り下げ

**"A conditional theorem: weak ultraviolet existence of four-dimensional SU(2) lattice Yang–Mills theory in a small box, with a machine-checked chain from per-step hypotheses" (2026-10-30) was withdrawn by the author on 2026-11-13.**

Reasons:

1. An existence result for four-dimensional lattice Yang–Mills theory, stronger than the conditional statement aimed at here, has since been made public as a Lean formalization together with a committee assessment (code: <https://github.com/yang-mills-group/OpenAI-YM-20261028>; assessment: <https://github.com/yang-mills-group/YM>, 2026-11-10). The per-step hypotheses of this paper concern a different renormalization design and are not implied by that result.
2. After publication, two defects were found in the paper. In the appendix on the polymer gas, the text defines compatibility of polymers as "not adjacent", while the cited Lean statements use "supports do not meet", so those Lean statements do not cover the gas described in the text. In the main chain theorem, the part about the effective coupling and the part about the family of measures are connected only in the prose, not inside the formal statement.

No corrected version will be issued. Please do not cite the paper for its stated conditional theorem. The files as published (`paper.tex`, `paper.pdf`, `statements.md`) remain in release v1.1.0 of this repository and in the corresponding Zenodo record.

---

この論文（2026-10-30）は、2026-11-13 に著者が取り下げました。

理由：

1. この論文が目指した条件つきの言明より強い、四次元の格子ヤン–ミルズ理論の存在の結果が、Lean による形式化と委員会の評価書として公開されました（2026-11-10。上のリンク）。この論文の一段ごとの仮説は、別の繰り込みの設計についてのもので、その結果からは従いません。
2. 公開のあと、論文に二つの傷が見つかりました。ポリマーの気体の付録で、本文は両立を「隣接しない」と定義していますが、引いている Lean の言明は「台が交わらない」で測っており、本文の気体に当たっていません。主な鎖の定理では、実効の結合についての部分と、測度の族についての部分が、形式の言明の中ではなく、本文の説明でだけ繋がっています。

訂正版は出しません。この論文を、そこに述べた条件つきの定理の根拠として引用しないでください。公開した時点のファイル（`paper.tex`・`paper.pdf`・`statements.md`）は、このリポジトリの版 v1.1.0 と、対応する Zenodo の記録に残っています。

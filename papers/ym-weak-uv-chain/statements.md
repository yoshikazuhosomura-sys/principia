# statements — A conditional theorem: weak ultraviolet existence of four-dimensional SU(2) lattice Yang–Mills theory in a small box, with a machine-checked chain from per-step hypotheses（2026-10-30）

設定：SU(2)・Wilson 作用・物理的な大きさ L の周期的な四次元トーラス、格子間隔 a_n = L/(M·2ⁿ)。観測量はブロック変数（平行移動の局所的でゲージ共変な平均＋四元数の単位球への動径の引き戻し、Definition 2.1 の (B1)〜(B5)）の有界連続でゲージ不変な関数。ν_{n,m} は細かい格子 n の測度をブロック写像で段 m に押し出したもの。
札：**Lean**／**紙**／**計**＝浮動小数の計算（主張にしない）／**典**＝引用／**仮**＝仮定（前提）。
Lean の束：`lean/ym-weak-uv-chain/`（64 本・1419 言明・1403 の `#print axioms` 行、WEB の束 `principia-ym-weak-uv-chain-2026-10-30.tar.gz`、sha256 `69976db4…`）。

**全体の形は含意である。** 四次元で示された前提は一つもなく、紫外の安定性は示さない。

| 論文の番号 | 言明（条件は同じ行） | 札 | Lean |
|---|---|---|---|
| Def 2.1 | 許されるブロック写像 (B1) 連続 (B2) ゲージ共変 (B3) 局所 (B4)(B5) 合成と対称性 | 定義（(B1)(B2)(B5) の例は Lean） | `LatticeBlockReflection`：`blockmap_equivariant`・`continuous_blockmap`・`invariant_pullback` ほか |
| Def 2.3 | 反射の面 P と正の時刻の観測量 𝒜_m(P) | 定義 | — |
| 仮説 (H-β)・(H-reg)・(H-sf)・(H-Cauchy) | 有効結合の一段の上下界と連続性・ブロック相関の並進の同程度連続性・各段の小さな場の事象の確率の下界・（任意で）s_n の増分の和の有限性 | 仮 | — |
| Thm 4.1（弱い紫外の存在、条件つき） | (St1)〜(St8) と (H-β)・(H-reg)・(H-sf) の下で (W0) 一ループの窓 4/γ₀² + 2bn ≤ β_n ≤ 4/γ₀² + 6bn で有効結合を γ₀ に合わせられる (W1) 部分列で全ての段の弱収束と射影的な整合 (W2) OS0（ブロックの形）：極限 S は有界・一様連続に一意に延びる (W3) OS1（箱の形）：トーラスの並進と超立方群で不変 (W4) OS2：反射正値性 (W5) 非退化 ν_m(C_m) ≥ 1 − η_m。(H-Cauchy) があれば部分列なしで収束し極限は一意。(W1)(W4) と (W3) の二進の並進・超立方群の不変性は仮説なしで成り立つ（コンパクト性の型） | 紙＋Lean（含意の組み立て） | `WeakUltravioletExistence.weak_uv_skeleton`・`exists_bare_inverse_coupling` ほか（論文 Table 5） |
| Lemma 4.2（サイトの反射、分解した形） | 有限測度 μ₀, ν、k ≥ 0、有界可測な h, φ で ∫ φ(U₀,U₊)φ(U₀,U₋) k h(U₀,U₊) h(U₀,U₋) d(μ₀⊗ν⊗ν) ≥ 0 | Lean | `LatticeBlockReflection.site_reflection_positive`・`site_reflection_positive_measure` |
| Def 5.1 | 動く不変区間つきの結合の段 (S1)〜(S6)（u_{k+1} = u_k − b + r^sf + r^lf、\|r^sf\| ≤ δ + C₂/u、大きな場のポリマー気体の活性の漸化と結合に依存してよい係数・不変な上界） | 定義（Lean の構造） | `ChainMovingActivity.CouplingStepsMovingD`・`CouplingStepsMoving` |
| Def 5.2 | 二段の小さな場の事象（ブロックごとのプラケット変数と背景の点の変数の閾値） | 定義 | — |
| Thm 5.3（鎖） | Def 5.1 の段、各段の一枚のプラケットと点の稀さ、並進の modulus の分解 τ_n + Ω から (i) (H-β)（u_k − 3b/2 ≤ u_{k+1} ≤ u_k − b/2）と z_k ≤ W(u_k) (ii) ν_{n,m}(G_m) ≥ 1 − \|R_m\|(n_p P₁ + n_pt S_bg) (iii) (H-reg)。さらに u₀(x) = x・連続性・G_m ⊆ C_m（閉）・(St1)〜(St8) なら Thm 4.1 の (W0)〜(W5) が η_m = \|R_m\|(n_p P₁ + n_pt S_bg) で成り立つ | Lean | `ChainMovingActivity.chain_end_to_end_moving`（`rarity_two_stage`・`hbeta_of_steps_movingD`・`equicontinuous_of_split`・`chain_to_hypotheses_moving`） |
| §5.1（細かい台からの反射正値性、合成） | (RP1)〜(RP3)（細かい格子の反射正値性・ブロック写像と反射の可換・格子の値の表示）から 𝒜_m(P) の有限の n での反射正値性と (St7) の行列の半正定値。定数係数の鎖との合成を一つの宣言に | Lean（(RP1)〜(RP3) は前提 10） | `ChainEndToEndFineSupport.chain_end_to_end_fine_support`・`reflection_positive_of_fine`・`positivity_of_fine` |
| Table 4（十の前提） | 1 一段の剰余の二次の型 2 窓の条件 3 大きな場の重み 4 一枚のモーメントと稀さ 5 対数の閾値と動く区間 6 有効結合の定義と連続性 (C) 7 格子に一様な小さな場の事象 8 背景の上界 9 プラケットの段の大きな場の気体（(H-sum) とラベルの和） 10 (RP-supp) | 仮（形・同値・算術の一部は Lean、数値は計） | 論文 Table 6 |
| Lemma A.1（連続性 (C)） | コンパクトな配位空間・有限測度・連続な作用で Z_f(x) は連続、Z > 0、E_x[f] は連続。したがって繰り込んだ結合と差の結合は連続 | Lean | `GibbsContinuity.continuous_gibbs_expectation`・`continuousOn_effective_coupling`・`DifferenceContinuity.continuous_difference_coupling` |
| 窓の条件 | Lipschitz の形で窓が存在 ⇔ c₀/u ≤ κ²/(8α)、κ = 1 − τ − ℓ/u。鋭い形 4αc₀/u ≤ κ² | Lean | `KernelMarginStages.window_necessary`・`window_sufficient`・`SharpWindow.sharp_necessary`・`sharp_sufficient` |

言わないこと（§7）：四次元の格子ヤン–ミルズの紫外の安定性は示さない（十の前提も (H-β)・(H-reg)・(H-sf)・(H-Cauchy) も四次元で示していない、Thm 5.3 は含意）・Thm 4.1 のうち仮説なしで成り立つ部分はコンパクト性の型で、問題文がその存在の部分の解としない型・クラスタ性・真空の一意性・無限体積・回転不変性・局所場・非自明性・質量ギャップには何も言わない（極限は部分列・ブロック写像・r₀・γ₀ に依存しうる）・前提の数値の形が成り立つか、どの β で成り立つかは主張しない（付録の数は浮動小数・一ループ・自由場の計算）・Bałaban の系列は要旨と序論の水準でだけ読み、前提 3 の再生する大きな場の重みとの対応は確かめていない・証明が公開されていない他の仕事の発表の内容には触れない。

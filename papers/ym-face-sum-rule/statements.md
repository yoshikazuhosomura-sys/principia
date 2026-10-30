# statements — A one-plaquette Schwinger–Dyson identity and a multi-level sum rule for the coarse stiffness in SU(2) lattice gauge theory, with machine-checked arithmetic（2026-10-30）

設定：SU(2)・Wilson 作用・有限の周期格子、y = β(1 − cos ψ)。粗い格子は線形の平均の規則（付録 A）でブロックした格子。剛性 Γ は ρ(y) ∝ √(y(2−y/β)) exp(−∫₀^y (1+Γ)) で定義する。
札：**紙**＝手で示す／**Lean**＝代数・算術を Lean で検査／**計**＝浮動小数の計算（運動量和・数値積分・モンテカルロ、主張の根拠にしない）／**典**＝文献の値の引用／**仮**＝仮定。
Lean の束：`lean/ym-face-sum-rule/`（6 本・64 定理、WEB の束 `principia-ym-face-sum-rule-2026-10-30.tar.gz`、sha256 `f7839e8d…`）。

| 論文の番号 | 言明（条件は同じ行） | 札 | Lean |
|---|---|---|---|
| Prop 3.1（一枚） | ψ_p が (0,π) に密度を持ち Γ が連続なら、全ての β と有限の周期格子で ρ(ψ) ∝ sin²ψ exp(−β∫(1+Γ)sin φ dφ)、y で書けば上の一次元の形。Γ ≡ 1 なら結合 2β の一枚と同じ分布、β → ∞ で Gamma(3/2, 1/2) | 紙 | — |
| Prop 3.2（多段） | 粗いプラケットの角 ψ_P が滑らかで密度 ρ_k を持ち、ā, b̄, F̄ が連続（ā > 0、両端で āρ_k → 0）なら、ρ_k = (C/ā) exp∫(b̄ − F̄)/ā、粗い剛性は 1+Γ_k = ((F̄−b̄)/ā + (ln ā)′ + 2cot ψ)/(β_k sin ψ) | 紙 | — |
| Lemma 3.3（厳密な分解） | b̄ = 2āB_k cot ψ と書くと 1+Γ_k = R_k − (B_k−1)h_k(y) + (ln ā_k)_y、h_k = 2(1−y/β_k)/(y(2−y/β_k))、0 ≤ h_k ≤ 1/y（0 < y ≤ β_k） | Lean | `CoarseStiffness.decomposition`・`h_from_angle`・`h_nonneg`・`h_le_inv` |
| Lemma 3.4（帯の下界） | [y₀,y₁] で R_k ≥ r₀・B_k−1 ≤ η・(ln ā)_y ≥ −λ なら Γ_k ≥ r₀ − 1 − η/y₀ − λ（直接 (B_k−1)h_k ≤ δ なら ≥ r₀ − 1 − δ − λ） | Lean | `gamma_lower`・`gamma_lower_direct` |
| Lemma 3.5（裾） | y ≥ y₀ で Γ_k ≥ Γ_min > −1 なら P(y > t) ≤ C₀ √t e^{−αt}/α (1 + 1/(2αt))、α = 1+Γ_min | 紙 | — |
| Thm 4.1（和則） | Pd = d・d_{pℓ}² = 1 なら Σ_q d_{pℓ}d_{qℓ}P_{pq} = 1、P_pp > 0 なら 1 + Σ_{q≠p} d_{pℓ}d_{qℓ}P_{pq}/P_pp = 1/P_pp | Lean | `FaceSumRule.sum_rule`・`sum_rule_split`・`normalized`（`row_identity`・`proj_fixes`） |
| Prop 4.2（自由場・全ての段・全ての線形の規則） | 自由場の一成分で θ_P = (K dA)_P（K 線形）とすると ā = (KddᵀKᵀ)_PP、F̄ = āθ_P/Var θ_P、R_k = 1/P_pp = d/2。三成分では ā は定数・B_k = 1 で Γ_k ≡ d/2 − 1 = 1（四次元） | 紙（行列の段は Lean） | `CoarseStiffness.transpose_fix`・`free_force_pairing`・`free_ratio`・`four_dim_ratio` |
| Prop 5.1（二つのモーメントが剛性を決める） | 一次で Γ(y) = 1 − (c₀ − c₁y)/β のとき w₂ = (3/8)(c₀−1/4) − (15/32)c₁、v₂ = (15/16)(c₀−1/4) − (45/32)c₁、逆に c₁ = 32w₂/3 − 64v₂/15、c₀ = 1/4 + 8w₂/3 + 5c₁/4。βK = −(5/12)c₁、分散の伸縮は c₁ を動かさない、y = u − κu²/β なら c₁ = 4κ（余弦だけで 2/3） | Lean | `FaceMoment.gamma_moments`・`gamma_covariances`・`forward`・`inverse`・`kurtosis`・`rescaling_keeps_slope`・`slope_of_kappa`・`cosine_only` |
| §5.2 w₂ | 二ループの係数 w₂ = 0.151383（文献の Q₁, Q₂ と式）。P₁ ∈ [0.1549333902, 0.1549333903] なら 0.15138 ≤ w₂ ≤ 0.15139、w₂ − 1/8 ∈ [0.0263, 0.0264] | 典＋計（P₁ の数値積分）＋Lean（算術） | `LevelConstants.w2_value`・`w2_split`・`w2_gap` |
| §5.2 細かい面の傾き | c₁ = 1/3 を仮定（モンテカルロ 0.311・0.331）。このとき c₀ = 2/3 + 8w₂/3、c₀ = 1 ⇔ w₂ = 1/8、c₀ ≤ 1.0704 | 仮＋計＋Lean（算術） | `FaceMoment.fine_intercept`・`fine_intercept_one`・`LevelConstants.fine_constants` |
| §5.3 粗い傾き | 揃った（可換な）部分から c₁^{(k)} = 2/3 − 64γ_P（概略） | 紙（概略）＋Lean（代数） | `equal_paths`・`cubic_to_y`・`slope_of_gamma` |
| §5.4・Table 1 | 付録 A の規則で r₁ = 1.1237・r₂ = 1.2327、c₁^{(1)} = 1.1733・c₁^{(2)} = 1.2084（32⁴ の運動量和）。一次で最初の二段に Γ_k ≥ 1 − C/β_k、C ≤ 2.259、β_k ≥ 10C で Γ_min ≥ 0.9 | 計（定数）＋Lean（算術） | `band_lower`・`threshold`・`LevelConstants.coarse_constants`・`thresholds` |

言わないこと（§7）：相互作用のある理論の上界は何も示さない（Γ_min ≥ 1 − C/β_k は O(β_k⁻²) の剰余を制御しない一次の言明、一次の補正のアフィンの形は概略、c₁ = 1/3 は仮定）・r_k, γ_P, c₁^{(k)} は一つの規則の最初の二段の浮動小数の運動量和で k に一様な有界性は示さない・w₂ は引用した Q₁, Q₂ の上・モンテカルロは整合の確認だけ・Schwinger–Dyson の恒等式も和則も新規とは言わない。
`CoarseStiffnessFirstOrder.lean` は同じ上界の前の帳簿で、論文では使わない。

# padic-regulator-valuation（2026-10-09）

p-adic heights on elliptic curves: the arithmetic layer of the valuation of the p-adic regulator at anomalous primes, with the companion note on the anomalous Euler factor.

楕円曲線の p 進高さと p 進レギュレーターの付値（異常素点）の、算術の段の Lean 4 による形式化。論文「The valuation of the p-adic regulator at anomalous primes」（草稿 v15）の §6「What is proved in Lean and what is not」が名を挙げる 31 本のファイルを、そのままの名で収める。

## 中身

- `PadicRegulatorValuation/` の下に 31 本。どれも `import Mathlib` だけから単独で検査が通る（互いに import しない）
  - `PadicHeightValuation.lean`, `PadicHeightValuation2.lean`, …, `PadicHeightValuation29.lean`（29 本）
  - `PadicHeightValuationCanonical.lean`
  - `AnomalousEulerFactor.lean`（付随ノートの分）
- ファイル名と名前空間は論文の §6 に書いたとおり：`PadicHeight`（ファイル 1–22）、`PadicHeightStar`（23）、`PadicHeightLayer`（24）、`PadicHeightCM`（25）、`PadicHeightLeading`（26）、`PadicDepthHeight`・`PadicSurjectivity`・`PadicClosureIndex`・`PadicNullModel`（27）、`PadicCofactor`・`PadicClosureCollapse`・`PadicPairLaw`・`PadicTwoRoutes`（28）、`PadicTranslateLinear`・`PadicTranslateDigit`・`PadicInverseLedger`（29）、`PadicCanonicalHeight`（Canonical）、`AnomalousEuler`（AnomalousEulerFactor）。**定理名は一つも変えていない**
- `#print axioms` の対象の定理 360 本（30 本の高さのファイルで 356・付随ノートで 4）
- Lean 4 `leanprover/lean4:v4.33.1`（`lean-toolchain`）・Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`（タグ `v4.33.1` の指す commit。`lakefile.lean` と `lake-manifest.json` で固定）
- `sorry` 0・`native_decide` 0・`sorryAx` 0

入口の `PadicRegulatorValuation.lean` は何も import しない。31 本は単独で検査できるよう同じ名の補題を言い直しているものがあり（例：`PadicHeight.sq_dvd_pow_add_sub` はファイル 11 と 13 の両方にある）、一つの環境に同時には読み込めないためである。`lakefile.lean` の ``globs := #[.andSubmodules `PadicRegulatorValuation]`` により、`lake build` は 31 本を一本ずつ建てる。

## 建て方

```
lake exe cache get                 # Mathlib のビルド済みキャッシュ
LEAN_NUM_THREADS=1 lake build
```

一本だけ確かめるときは、建てたあとで

```
lake env lean PadicRegulatorValuation/PadicHeightValuation5.lean
```

各ファイルの末尾に主な定理の `#print axioms` が置いてあり、検査するとその定理が依拠する公理がそのまま出力される。

## 公理

`axioms.txt` は 31 本をそれぞれ `lake env lean` で単独に検査したときの `#print axioms` の出力を、モジュールごとに並べたもの（360 行）。長い行は Lean が改行して出すので、`axioms.txt` では一行に繋いである。

- 全行が `propext`・`Classical.choice`・`Quot.sound`（Lean / Mathlib の標準三公理）の**部分集合**
- `sorryAx` 0 件・`Lean.ofReduceBool`（`native_decide`）0 件・エラー 0 件
- 31 本とも終了コード 0。警告はリンターの助言だけ（ファイル 2・5・22・23。未使用の変数・`simpa` の代わりに `simp`・`Try this`）

| 公理 | 定理の本数 |
|---|---:|
| `[propext, Classical.choice, Quot.sound]` | 226 |
| `[propext, Quot.sound]` | 102 |
| `[propext]` | 30 |
| （公理なし） | 2 |

## Lean の中にあるもの、外にあるもの

機械検査が保証するのは「書いてある命題からその結論が出ること」だけである。命題が意図した内容を書けているか、その主張が世の中で新しいかについて、機械は何も言わない。

**中にあるもの**：算術の段。高さの分解・Fermat 商・行列式と双線形代数・重みと留数の勘定・桁の比較・整数の合同式。言明はすべて整数・行列・有限和・p 進合同についてのものである。

**仮定として入るもの**：幾何と p 進解析。Mathlib には p 進シグマ関数・等分多項式・Vélu の公式・Tate 曲線・形式群がないので、それらから来る事実（例：二つの速さ `v_p(ΔΘ) = j − 1` と `v_p(Δz) = 1 + j`、局所高さの分解、核多項式の式 (R′)）は Lean の言明の中で仮定として入る。各ファイルの冒頭のコメントに、何を Lean に入れ、何を外に置いたかを書いてある。

**外にあるもの**：

- 論文 §5 の数値（PARI/GP による計算。`ellpadics2` との照合、箱ごとの高さ・行列式・桁の表）。等級は [computation]
- 原典の言明（Kato・Skinner–Urban・Schneider・Perrin-Riou・Greenberg–Vatsal・Mazur–Tate–Teitelbaum など。論文 §6 の「sources」の段）。等級は [known]。命題 V（§6）は p 進 BSD の類似を仮定する条件つきの命題で、Lean にあるのはその四つの場合の整数の算術だけ（ファイル 26）
- 付随の言明一覧（`statements-v15.md`）の C4–C20 は計算・既知の定理の組み合わせ・記録の行で、Lean の名を持たない（列は「—」）。最後の C20 は「原典で確かめていないもの」の記録であって言明ではなく、この束のどのファイルとも対応しない

## 論文の定理との対応

論文 v15 §6 の表（61 行・Lean の名 316 個）を、この束の宣言と機械的に照合した。316 個すべてが表に書かれたファイルの中に宣言として見つかる（見つからない名 0）。表の 61 行が触れるファイルは 31 本全部である。

| 論文の言明 | Lean の名 | ファイル |
|---|---|---|
| Theorem A | `norm_det_div_sq_le` | `PadicHeightValuation` |
| Theorem B, step 3 | `fermatQuot_sub_iff_of_sq_eq_cube`, `dvd_three_mul_sub_two_mul`, `sub_ne_zero_of_two_mul_eq_three_mul` | `PadicHeightValuation2`, `PadicHeightValuation8` |
| Theorem B, the model with p ∣ a₁ | `sq_sub_cube_dvd_of_dvd_a1`, `sq_sub_cube_dvd_of_sq_dvd_psi` | `PadicHeightValuation8` |
| Lemmas 4′ and 5 | `eval_sub_eval_dvd_sq` | `PadicHeightValuation2` |
| Corollary D | `sq_dvd_pow_sub_one_of_isPow` | `PadicHeightValuation3` |
| Corollary E | `sq_dvd_alpha_sub_beta_of_isPow` | `PadicHeightValuation3` |
| Theorem H | `fermatQuot_scale` | `PadicHeightValuation4` |
| Theorem J | `dvd_det_of_col_dvd`, `pow_succ_dvd_det_of_col` | `PadicHeightValuation4` |
| Main theorem, linear algebra | `regulator_valuation_of_split_anomalous` | `PadicHeightValuation5` |
| Main theorem (ii), equivalence | `regulator_valuation_of_split_anomalous_iff_split` | `PadicHeightValuation5` |
| §4.6 (2), the single slope and the affine zero | `slope_of_rho`, `fermatQuot_deform`, `affine_zero_unique`, `lambda_eq_zero_iff_split`, `lambda_dichotomy` | `PadicHeightValuation5` |
| §4.6 (3), the weight count and the Newton polygon | `weight_split`, `twelve_dvd_weight`, `sum_pole_orders`, `cusp_sum_eq_m`, `mul_compl_le_half_mul_half`, `eq_C_mul_of_dvd_of_natDegree_eq` | `PadicHeightValuation6` |
| §4.6 (4), the residues | `inv_one_sub_add_inv_one_sub_inv`, `first_term_residue`, `second_term_leading_ne_zero`, `residues_do_not_cancel`, `twelve_mul_sum_cusp_orders` | `PadicHeightValuation7` |
| Theorem S, the ledger | `exists_shift_dvd_a1`, `add_val_exactly_one`, `not_dvd_of_val_one` | `PadicHeightValuation8` |
| Main theorem (⟹ of (i)) | `quadratic_value_mem_of_entries_mem` | `PadicHeightValuation8` |
| Theorem R, the linear algebra (R0) | `bilin_rank_one_of_zero_iff`, `not_dvd_of_congr_ne_zero` | `PadicHeightValuation9` |
| Corollary R′, the determinant | `det_conj_diagonal`, `det_conj_diagonal_one_p`, `reg_eq_of_det_eq` | `PadicHeightValuation9` |
| Theorem R_s, the linear algebra (R0s) and rank ≤ 2 | `bilin_eq_of_vanishing_on_hyperplane`, `bilin_zero_of_mem_radical`, `gram_det_three_eq_zero` | `PadicHeightValuation10` |
| Corollary R′_s, the determinant | `det_two_dvd_iff`, `pow_dvd_det_of_offdiag_block` | `PadicHeightValuation10` |
| Proposition R″_s, the second Fermat quotient | `fermatQuot2_add`, `dvd_three_mul_sub_two_mul_two`, `split_const_eq` | `PadicHeightValuation10` |
| Proposition R⁗ (the slope) and Corollary R⁗′ | `eval_shift_of_deriv_eq`, `sq_dvd_pow_add_sub`, `fermatQuot2_move`, `lambda2_affine`, `lambda2_const_of_slope_zero`, `lambda2_lift_bijective`, `lambda2_unique_zero_lift`, `b_eq_slope_mul_kappa` | `PadicHeightValuation11`, `PadicHeightValuation13` |
| Lemma 7, the first digit of the x-coordinate | `eval_shift_first_digit`, `first_digit_eq`, `eval_shift_depth_two`, `first_digit_ne_zero_iff` | `PadicHeightValuation12` |
| Theorem K and Corollary K′, the bilinear algebra and the three layers | `master`, `master_symm`, `master_add_left`, `master_smul_left`, `master_vanish_on_ker_chi`, `master_mem_radical`, `master_eq_of_gam_eq_smul`, `master_offdiag_ne_iff`, `master_diag_eq_zero_iff`, `master_bad_class_unique`, `det_three_layer`, `det_eq_zero_of_rank_one_block`, `det_sq_dvd_iff` | `PadicHeightValuation12` |
| Proposition 9, the second digit under lifting | `X_pow_four_dvd_sub_trunc`, `eval_quartic_dvd`, `eval_shift_second_digit`, `fermatQuot_second_move` | `PadicHeightValuation13` |
| Proposition 10, the bad lift and the layers | `root_factor`, `dvd_iff_dvd_sub_root`, `unique_bad_class`, `exists_bad_class` | `PadicHeightValuation13` |
| Theorem N, the ledger and the cancellation of a₁ | `second_digit_zero_iff`, `second_digit_criterion`, `a1_correction_cancels` | `PadicHeightValuation13` |
| Corollary N′ and the three-fold split at the second digit | `dvd_iff_dvd_first`, `sq_dvd_sub_crit`, `val_one_of_crit_ne`, `sq_dvd_of_crit`, `trichotomy`, `min_two_ne_iff`, `min_two_eq_of_two_le`, `exists_same_data_diff_val`, `q2_additive`, `scaling_shift_square` | `PadicHeightValuation14` |
| Corollary N⁽³⁾ and Corollary N″, the four-fold split | `inv_pred_cube`, `neg_inv_pred_cube`, `q2_quotient`, `q2_quotient_dvd`, `sq_cube_step`, `denominator_third_digit`, `cube_dvd_sub_crit`, `cube_dvd_of_crit`, `not_cube_dvd_of_crit_ne`, `cube_dvd_iff_crit`, `quadrichotomy`, `exists_same_second_diff_third`, `min_three_ne_iff`, `min_three_eq_of_three_le` | `PadicHeightValuation15` |
| Proposition 12, Corollary N⁽⁴⁾ and Corollary N‴, the five-fold split | `low_terms_vanish`, `p_mult_second_digit`, `w_local`, `inv_x_correction`, `w_ne_zero_iff`, `inv_pred_quartic`, `neg_inv_pred_quartic`, `denominator_fourth_digit`, `theta_eta_cancels`, `cubic_term_vanishes`, `fourth_digit_reduction`, `quartic_dvd_iff_crit`, `exists_same_third_diff_fourth`, `min_four_ne_iff`, `min_four_eq_of_four_le`, `quintichotomy` | `PadicHeightValuation16` |
| Theorem G′ (the sensitivity) and the sharpness in Theorem G″ | `pow_sub_pow_expand`, `exists_exact_part`, `unit_pow_diff_exact`, `shift_depth_exact`, `shift_depth_dvd`, `quotient_by_p_sq`, `theta_sensitivity_exact`, `theta_digit_determined`, `three_layers_determine`, `layer_three_moves_digit_two`, `layer_digit_correspondence`, `nondegeneracy_needed` | `PadicHeightValuation17` |
| §4.12, v_p(ψ_p′(x(T))) = 1 exactly, and (ND) as a condition on ψ_p mod p³ | `sq_valuation_one`, `psi_deriv_valuation_one`, `bracket_divisible`, `nd_iff_bracket`, `nd_of_bracket_exact` | `PadicHeightValuation18` |
| Proposition 16, the weight of Res_x(G, ψ_p mod p) and m_p = m_K + m_S | `resultant_weight`, `resultant_weight_split`, `m_p_integral`, `m_g_integral`, `m_K_add_m_S`, `resultant_weight_K`, `resultant_weight_S`, `twentyfour_dvd_sq_sub_one` | `PadicHeightValuation18` |
| Theorem ND, the step "the constant is non-zero ⟹ (ND)" | `ne_zero_of_const_mul_pow`, `eval_ne_zero_of_isCoprime`, `nondegeneracy_summary`, `nd_iff_S_ne_zero` | `PadicHeightValuation18` |
| §3.14, D kills Δ₀; the cusp count of §4.13; c_S ≠ 0 given γ_p ≠ 0; the chain rule for D | `serre_deriv_disc_zero`, `gauss_sum_closed`, `min_sum_closed`, `cusp_ord_total`, `resultant_weight_dPsi`, `m_S_eq`, `weight_two_p_vanishes`, `pow_card_self`, `cS_ne_zero`, `deriv_zero`, `deriv_one`, `deriv_sum`, `deriv_pow_succ`, `deriv_eval_chain` | `PadicHeightValuation19` |
| Lemma 13, and the reduction of Proposition 15 to (R′) ∧ (L) | `isogeny_A1`, `isogeny_A1_domain`, `isogeny_A2_core`, `isogeny_A2`, `deriv_eval_of_factor`, `residue_iff`, `const_mod_p_deriv`, `lead_cancel`, `lc_difference`, `deg_K_eq`, `weight_L`, `two_n_add_one_eq_zero` | `PadicHeightValuation20` |
| §4.13(b), (c): the balanced exponents, D²H/DH = 2κ − 1, the telescoped sum, i ↦ p − i | `balanced_repr`, `D_eval_zero`, `D2_eval_zero`, `log_deriv_ratio`, `telescope_term`, `telescope_sum`, `residue_value`, `residue_value_zmod`, `sign_flip_invariance` | `PadicHeightValuation21` |
| Proposition 16, m_K, its weight, and ε_p = −1 ⟺ p ≡ 3 (mod 8) | `ordq_total`, `weight_ResK`, `mK_even`, `exponent_two_nsq`, `exponent_case_1mod4`, `exponent_case_3mod4`, `sign_exponent`, `eps_cases` | `PadicHeightValuation21` |
| Proposition R⁺, the p-part of the reduction and Hasse's two cases | `card_cases`, `two_p_forces_five`, `sq_not_dvd`, `dvd_of_unit_mul`, `dvd_of_unit_sq_mul` | `PadicHeightValuation22` |
| The coefficients of σ_p in a general model, and the depth of a term of a logarithm | `sigma_third_coeff`, `sigma_fourth_coeff`, `padicVal_eq_zero_of_lt`, `log_term_depth_small`, `log_term_depth_five`, `log_term_depth_ne_five`, `log_term_factor`, `five_fifth_term` | `PadicHeightValuation22` |
| Proposition 16, the constant c_p in one line | `cp_one_line` | `PadicHeightValuation22` |
| Proposition 17, the coefficients of ℒ and the reparametrisation in t | `mu2_eq`, `mu4_eq`, `mu6_eq`, `mu6_no_b2_cube`, `lambda3_eq` | `PadicHeightValuation23` |
| Proposition 18, the digit at which each term is visible | `lambda_depth_mono`, `lambda_depth_m2_e2`, `x_form_suffices`, `val_thirty`, `val_three_sixty`, `val_thirty_seven`, `mu6_visible_at_ten`, `theta_depth_j5_p5`, `theta_depth_j5_p7`, `log_term_j10_five`, `log_term_j10_seven` | `PadicHeightValuation23` |
| Proposition 19 and Theorem G⁽ᵏ⁾, the depth of a layer and the growth of the data | `layer_depth`, `data_count_linear` | `PadicHeightValuation23` |
| Proposition 20 and Theorem G⁽ᵏ⁾, the two rates and the minimality at every k | `theta_rate_digit`, `ledger_rate_digit`, `gap_is_e`, `ledger_lags`, `ledger_lags_general`, `uniform_in_k`, `exact_pred_not_at`, `no_cancel`, `at_most_one_vanishes`, `layer_is_needed`, `fermat_digit`, `fermat_digits_needed`, `data_count`, `data_count_step` | `PadicHeightValuation24` |
| Proposition 20 (iii), the boundary row and the CM cells | `ledger_lags_any_m`, `cm_lags_ten`, `m1_leads_iff`, `m1_leads_of_unit_c`, `boundary_cancel_m1`, `boundary_cancel_pow`, `boundary_cancel_of_card`, `boundary_p7_m3`, `boundary_p7_exception`, `boundary_m1_vs_m3_p7`, `cm_prime_mod_three`, `cm_no_anomalous_of_mod_two`, `cm_seven_nineteen`, `cm_not_thirteen`, `cm_ledger_invisible_before_eleventh`, `cm_no_local_invariant_before_eleventh`, `layer_is_needed_cm`, `cm_gap_at_k` | `PadicHeightValuation25` |
| Corollary K′(i) and Corollary R′_s at r = 2, as linear algebra | `prime_dvd_det_two_iff`, `det_two_split_ne_zero_iff`, `exists_pair_eq_one`, `onto_iff_det_ne_zero`, `onto_iff_reduced_det_ne_zero` | `PadicHeightValuation26` |
| Proposition V (§6, conditional), the integer arithmetic of its four cases | `leading_val_ge_rank`, `rank_le_leading_val`, `leading_val_eq_rank_of_nonsplit_rank_one`, `leading_val_gt_rank_of_split_le_one`, `leading_val_eq_rank_iff_of_normal`, `exists_two_ranks_same_leading_val`, `admissible_leading_two_of_rank_le_two` | `PadicHeightValuation26` |
| Lemma 23, depth and height | `log_denom_ge`, `height_ge_of_depth`, `depth_lt_of_height_lt` | `PadicHeightValuation27` |
| Proposition 24, the surjectivity of (χ, γ) from one shallow element of ker χ | `surjective_pair_iff`, `surjective_of_shallow_kernel_element` | `PadicHeightValuation27` |
| Proposition 24ᶜ, the lower bound R ≥ β(E) | `beta_le_remainder_of_local_bounds` | `PadicHeightValuationCanonical` |
| Proposition 24ᶜ, depth against canonical height | `canonical_ge_of_depth`, `depth_lt_of_canonical_lt` | `PadicHeightValuationCanonical` |
| Proposition 24ᶜ, the surjectivity | `surjective_of_canonical_lt_four_log_add_beta`, `surjective_of_naive_or_canonical`, `surjective_pair_iff'` | `PadicHeightValuationCanonical` |
| §3.15, the constants m_ℓ at I_N | `four_mul_comp_le_sq`, `comp_le_half` | `PadicHeightValuationCanonical` |
| The difference of the two slacks | `remainder_sub_slack` | `PadicHeightValuationCanonical` |
| §5.12, the index of the p-adic closure and the null model for det(χ, γ) | `index_zero_iff`, `index_ge_two_iff`, `index_le`, `det_zero_iff`, `card_det_zero_of_ne`, `card_det_zero_of_fst_eq_zero`, `density_det_zero` | `PadicHeightValuation27` |
| Lemma 23′, the slack | `cofactor_log_le`, `cofactor_eq_one_of_slack_lt`, `max_eq_iff` | `PadicHeightValuation28` |
| §3.15, small closures: the layers factor through χ | `factor_through_chi`, `two_ne_zero_of_ne_two`, `diag_ne_zero` | `PadicHeightValuation28` |
| Proposition 20 (v) read on a pair of points, and a count of §5.12 | `exact_of_deeper`, `pair_law_j3`, `pair_law_F_leads`, `card_two_routes` | `PadicHeightValuation28` |
| Proposition 21, steps (2)–(4) and parts (i)–(iii) | `ratio_of_ker_le`, `vanish_of_chi_zero`, `translate_quadratic`, `second_difference`, `shift_quadratic`, `ledger_digit`, `kappa_ne_zero`, `separates`, `counterexample_digits` | `PadicHeightValuation29` |
| Proposition 22, the inversion at k = 2 | `inverse_n3` | `PadicHeightValuation29` |
| The Euler factor at an anomalous prime (companion note) | `ap_of_anomalous`, `unit_root_identity`, `sub_one_associated_p`, `sub_one_associated_p_of_pred` | `AnomalousEulerFactor` |

各行の条件（仮定）は論文の当該の言明と、Lean の言明の仮定にそのまま書いてある。表の一行を「Lean で確定」と読まないこと：幾何の入力は Lean の言明の仮定であり、論文の言明の等級は [paper; arithmetic step in Lean] のように混ざる（等級が混ざるときは弱いほうが支配する）。

## 検査の記録

2026-10-09、Lean 4 v4.33.1・Mathlib `0df444a3`。31 本を一本ずつ `lake env lean <file>` で検査：終了コード 0 が 31 本、`#print axioms` の 360 行すべてが標準三公理の部分集合、`sorryAx` 0。出力は `axioms.txt`。

`lake build` によるパッケージとしての建て試しは、この記録には含まれない。

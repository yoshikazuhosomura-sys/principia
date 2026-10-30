# 言明と札（P4・一列四枚の繰り込み模型）

論文：`paper.tex`／`paper.pdf`（18 頁・表 1・2・3・5〈番号 4 は §8 の対応表 longtable が消費し、見出しは無い〉・主定理三つ・付録 A〈一ループの結合の導出〉・B〈一段の定数の導出〉。2026-10-30 改訂：教科書の章への引用を外し、模型・一ループの結合・一段の定数を §2 の表 1 と付録 A・B に置いて単独で閉じる形）。札：［Lean］Lean で閉じた（標準三公理）／［紙］紙の初等的な証明／［主項］Laplace の主項（at leading order (Laplace)）／［計］計算機の値（computed）。条件は各行に。

| 論文 | 言明 | 条件 | 札 | Lean |
|---|---|---|---|---|
| 式 (1)・表 1 | w = ∫ G(U) f(W_aU⁻¹) f(U⁻¹W_b) dU、G = f∗f | 一列四枚・W_a=P₁P₂P₃・W_b=P₂P₃P₄ 固定 | 紙（有限群の版は Lean） | `four_plaquette_constrained`（有限群・可換半環）・`four_plaquette_of_semigroup`（p_s⋆p_t=p_{s+t}） |
| 式 (3) | 木の比 κ_ab/κ_a = 2（三枚では 1） | 可換化したガウスの最小化 | Lean | `tree_lower_four`・`tree_attained_four`・`shape_four`・`shape_three` |
| 式 (6)・付録 A.1 | Wilson：40κ_a=β−1、20κ_ab=β−½、比 2(β−½)/(β−1)+O(β⁻²) | SU(2)・一列四枚・二次 | 主項 | — |
| 式 (7)・付録 A.2 | 熱核：比 2+2t/3+O(t²)。U(1) Villain は全 t で 2 | 同上（Villain は巻き数の項を除く） | 主項（Villain は紙） | — |
| 表 2 | 比の値（Wilson 2.3211…2.0322、熱核 2.2090…2.0214、β=4…32） | θ≤0.3・二経路 8e−12 | 計 | — |
| 定理 1 | κ_a=E[F′(log G)′]/24、κ_ab=E[F′²]/24、比 2 ⇔ E[F′(F′−2(log G)′)]=0、十分条件 G∝e^{F/2} | SU(2) の類関数・F, log G ∈ C²[0,π]・端の項 0 | 紙（初等） | 代数のみ：`kappa_a_of_ibp`・`kappa_ab_eq`・`ratio_two_iff`・`ratio_eq_two_add`（E₁≠0） |
| 命題 4.1 | D = 2/5 + (24/5)(q/B) + O(1/B)、E₁ = (3/5)B、U(1) は (24/25)q/B | 恒等元に集中する作用 | 主項 | 代入のみ：`one_loop_D`・`one_loop_D_u1`（B≠0） |
| §4 系 | γ 族は c<3 で D>8/25／基本＋随伴は ρ=−1/4 で D=0／各点の平方根は一ループで無い | 一ループの式の上 | Lean（代数） | `gamma_family_one_loop_lower`・`fund_adj_one_loop_root`（β≠0・1+2ρ≠0）・`no_pointwise_sqrt_one_loop` |
| §4 数値 | ρ*(β) は β≥12 で在る（−0.3180@16 … −0.2516@512）・β≤10 の格子で無い・γ 族の D は全点正 | 格子の上 | 計 | — |
| 補題 5.1 | 畳み込み・積・平方根の合成則（g=h−log P が平坦に運ばれる） | B→∞・比を固定 | 主項（三角の恒等式は Lean） | `transverse_hessian`・`convolution_prefactor` |
| 定理 2(i) | B′=B/5、ψ^{2k} の形の座標は (4^k+1)/5^{2k−1} 倍、(q/B)′=(17/125)(q/B) | 対角の定義 | 主項 | `tree_quadratic_split`・`tree_value_at_saddle` |
| 定理 2(ii) | γ′_k=((4^k+1)/25^k)(γ_k−1)+(1+25^{−k})/2、ψ⁴ で (17γ+296)/625・固定点 37/76・熱核 → 313/625 | 同上 | 主項（代数は Lean） | `step_k2`・`step_k2_fixed_iff`・`step_k2_contract`・`fixed_point_general`・`fixed_point_k3/k4`・`half_sub_gamma_star`・`step_k2_heat` |
| 定理 2(iii) | 類の上で比 2+(2/3)/B | 命題 3.1 の上 | 主項 | `ratio_coefficient` |
| 定理 2(iv) | 比 2 の線 q/B=−1/12 の像 −17/1500・ρ′=−53/356・ずれ 9/89・像の D=216/625 | 同上 | 主項（代数は Lean） | `rho_of_ratio`・`refit_solution`・`refit_unique`・`image_rho`・`image_gap`・`image_one_loop_D` |
| §6・付録 B 一次の項 | ψ⁴ の 1/B 項 −(8/3125)h₂+(42/125)h₃−14/140625・類で (γ′₂−37/76)B→−591986/69290625・c=11168/15625 | 二次のキュムラントまで | 紙（算術は Lean） | `first_order_at_fixed_point`・`quadratic_shape_coefficient` |
| 命題 6.2・表 3・表 5・付録 B | r′ ≤ (17/625)r + C/B、B′≤B/5、C=0.0108（r≤0.05）・0.00355（r≤0.01）・0.00182（類の上）、B_min=1000 の列 | 射影の模型（ψ⁸ まで）・解析的な主部分・B≥32 | 紙＋計（定数） | 部品のみ：`pow_sub_pow_norm_le`・`saddle_ratio_le`・`saddle_ratio_three`・`keff_half_le`・`cov_eigen` |
| 定理 3 | B₀..B_{N−1}≥32・r₀≤r_box なら r_n≤r_box かつ r_n ≤ λⁿr₀ + C/((5−λ)B_n)、λ=17/625 | 命題 6.2 の一段の不等式を仮定（定数は計） | Lean（組み立て） | `uv_uniform`・`stays_in_box` |
| 補題 6.3 | 残りが C/(a+ck)²+Dq^k なら総和は C(1/a²+1/(ca))+D/(1−q) | — | Lean | `uniform_deviation` ほか |
| §6 箱の外 | Wilson 出発（x=1/24）は段 1 で上界を破る（λ̄/λ=1.018→1.001）・負の x は内 | B₀=32…512 | 計 | — |
| §6 U(1) | 非斉次項が消え r′ ≤ (17/625+0.06/B)r | 平坦 | 読（計算した係数から読む） | — |

Lean：7 モジュール・`#print axioms` 61 行（9+8+9+8+12+9+6）すべて `[propext, Classical.choice, Quot.sound]`。Lean v4.33.1。

## 番号の注

表の節・命題・補題の番号は本文（v2）の番号に揃えた（§2 模型・§3 一ループ・§4 定理 1・§5 定理 2・§6 定理 3・付録 A・B）。表の番号は v2 で模型の表（表 1）が加わったため一つずつ後ろにずれた（比の値＝表 2、定数 C＝表 3、C の内訳＝表 5。番号 4 は対応表 longtable が消費する）。

## 単独で閉じる形（v2）

模型の定義・一ループの結合（Wilson・熱核）・一段の剰余の定数は、教科書の章を引かずに本文 §2 の表 1 と付録 A（A.1 Wilson・A.2 熱核）・付録 B（持ち上げた一段・一次の項・明示部分・剰余・数値、表 5）で導く。教科書 [KSR] は序で「読むのに要らない日本語の広い解説」として一度挙げるだけ。

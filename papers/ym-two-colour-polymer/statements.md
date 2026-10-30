# statements — A machine-checked two-colour polymer gas on ℤ⁴: encoding, adjacency degrees, the box stage, and the Kotecký–Preiss condition down to Dobrushin（2026-10-30）

設定：ℤ⁴ のプラケット（面）とリンクの有限の集まり Λ_F, Λ_L、面の集まり（クラスタ）X ∈ 𝒳 と実の活性 z(X)。二色＝細い面（thin）と欠陥のリンク（defect）。(H-2col) は活性の積の形の仮定、(H-sum) は箱ごとの和の形の仮定。(KP) は Kotecký–Preiss の条件、(D) は Dobrushin の条件。
札：**Lean**＝全て Lean で検査（ℤ⁴ の有限の数え上げは `decide +kernel`）／**仮**＝仮定（活性の上界は全て定理の仮定）。
Lean の束：`lean/ym-two-colour-polymer/`（13 本・518 の `#print axioms` 行、WEB の束 `principia-ym-two-colour-polymer-2026-10-30.tar.gz`、sha256 `d3899029…`）。束の中の写し（隣に置いた他のファイルの写し）を除いた相異なる言明は 163（論文の Table 1）。

| 論文の番号 | 言明（条件は同じ行） | 札 | Lean |
|---|---|---|---|
| Lemma 3.1 | 近傍 nb(p) が有限で隣接を含み、x(p)∏_{q∈nb(p)}(1+τ(q)) ≤ τ(p) なら、全ての有限の U, R で W_g(U,R) ≤ ∏_{r∈R} τ(r) | Lean | `Wg_le` |
| Prop 3.2（二色の一点の和） | \|z(C)\| ≤ ∏ ε_col(q) と ε_b e^{a_b}(1+θ₀)^{d_b0}(1+θ₁)^{d_b1} ≤ θ_b（b = 0,1）から、点 p を含む連結な C の和 ≤ θ_col(p)、根の集合 S と交わる C の和も同様 | Lean | （§3 の二色の和、`TwoColorPolymerSum`・`TwoColorEncoding`） |
| Lemma 3.3（数の固定） | 次数 (20,48,72,122)・(a₀,a₁) = (2,12)・(θ₀,θ₁) = (1/20, 10⁻⁴) で、ε₀ ≤ 2.5·10⁻³・ε₁ ≤ 1.5·10⁻¹¹ なら Prop 3.2 の二つの不等式が成り立ち、θ₀ + 4θ₁ ≤ 1 | Lean | `lattice_fix`・`lattice_face_total` |
| Lemma 4.1（符号化） | 有限の X ⊆ F について (i) X が連結なら enc(X) は連結、(ii) 細い部分と欠陥の集合から X を復元でき、符号が等しければそれらも等しい、ほか（大きさ・ラベルの和の上界） | Lean | `enc_connected`・`decode`・`enc_eq`・`thin_disjoint`・`card_le_enc`・`label_sum_le` |
| Prop 4.2（符号化した和） | (H-2col) の下で、全ての符号が満たす述語 Q について Σ_X \|z(X)\|e^{2\|X\|} ≤ Σ_{C 連結, Q(C)} ∏ x_w(q) | Lean | `encoded_sum_le` |
| §5 次数 | ℤ⁴ で面の面近傍 20・面の欠陥近傍 44・欠陥の面近傍 66・欠陥の欠陥近傍 122・面のリンク 4（決定手続きで数えた）、近傍の包含 | Lean（`decide +kernel`） | `card_nbFF0`・`card_nbFL0`・`card_nbLF0`・`card_nbLL0`・`card_links0`・`lattice_hnb`・`lattice_hdeg` |
| Thm 5.1（面の段） | ℤ⁴・(H-2col)・ε₀ ≤ 2.5·10⁻³・ラベルの和 ≤ 1.5·10⁻¹¹e¹² で (KP)、さらに \|X\| ≥ 1・\|z(X)\|e^{2\|X\|} ≤ e − 1 なら全ての X で (D) | Lean（活性は仮） | `lattice_kp_site`・`lattice_dobrushin` |
| §5 広い隣接 | 立方体を挟む平行な面を隣接に加えると次数 24・44・66・122、ε₀ ≤ 2.1·10⁻³ で同様 | Lean | `Lattice24KP`：`card_nbFF24_0` ほか・`lattice24_fix` |
| §6 箱 | 箱 2b + {0,1}⁴ は 16 点・96 面・64 リンク、箱の隣接の次数 ≤ 20、連結なクラスタの箱の像は連結 | Lean | `card_corners`・`card_boxFaces`・`card_boxOff`・`box_degree`・`box_image_connected` |
| Thm 6.1（箱の和＝面のクラスタの和） | 全ての箱 b で、箱の気体の b を含むポリマーの和は、箱の像が b を含む面のクラスタの和に等しい。したがって箱の形の (H-sum) は箱の気体の (KP) そのもの（積の仮定なし） | Lean | `box_hsite_eq_face_sum`・`box_hsite_of_face_sum` |
| Thm 6.2（橋） | KP の重みなしの (H-2col)・ラベルの和 ≤ ε_L・θ の二つの不等式の下で、箱 b の面と交わるクラスタの和 ≤ 96θ₀ + 384θ₁ | Lean | `box_event_bridge` |
| Thm 7.1（KP ⇒ Dobrushin） | \|supp γ\| ≥ 1・(KP)・\|z(γ)\|e^{2\|supp γ\|} ≤ e − 1 なら全ての γ で (D) | Lean | `KPToDobrushin.dobrushin_cond_of_kp` |
| Thm 7.2（分配関数） | 対称な非両立の関係・符号を問わない実の活性の有限の気体で (D) なら Z(Γ) > 0、e^{−a(γ)}Z(Γ∖γ) ≤ Z(Γ)、Z(Γ) ≥ exp(−Σa)、log Z の下界 | Lean | `PolymerGasDobrushin.dobrushin`・`Z_ge_exp`・`log_Z_ge` |
| Thm 7.3（合成） | 箱の像の台が空でなく、箱の形の (H-sum) が全ての箱で成り立てば、箱の気体は (D) を満たし、分配関数の下界が成り立つ | Lean（(H-sum) は仮） | `BoxGasFromFaceSum.box_dobrushin_of_face_sum`・`box_gas_partition_of_face_sum` |

言わないこと（§11）：どの格子ゲージ模型の活性の上界も示さない（仮定の数 2.5·10⁻³・1.5·10⁻¹¹・2.55·10⁻³・10⁻⁹・2.6·10⁻⁵・2.1·10⁻³ は十分条件の閾値で見積もりではない）・(H-2col)、ラベルの和の上界、(H-sum) は仮定で、動機の SU(2) 模型で成り立つとは言わない・大きな場の展開がこの種のポリマー気体を与えることは形式化していない・箱の段の欠陥を含む対の次数 (81,81,80) は上界、Lemma 3.3 の 48・72 は決定した 44・66 の上界・クラスタの数え上げは標準の型で、ラベルつきの欠陥リンクの二色の符号化が既知かどうかは知らない。
`BoxConnectivity.lean` は論文では使わない。

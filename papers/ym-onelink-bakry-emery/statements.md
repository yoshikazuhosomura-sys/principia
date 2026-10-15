# Statements — One-link integration before Bakry–Émery for SU(2) lattice Yang–Mills

The main statements of the note, with their hypotheses, the Lean declaration (module of the bundle
`lean/ym-onelink-bakry-emery/`) and a one-line Japanese rendering. Grades: **[Lean]** = a theorem of
the bundle, checked with `lake env lean` (no `sorry`, no `native_decide`, every `#print axioms` line a
subset of `propext`, `Classical.choice`, `Quot.sound`); **[paper]** = proved or sketched on paper only.

主定理の言明と条件の一覧。各行の日本語は一行訳（条件を落とさない）。

| # | Statement (with hypotheses) | Lean declaration (module) | Grade | 日本語の一行訳 |
|---|---|---|---|---|
| Thm 1(i) | On `(ℤ/L)⁴`, `L` even and `2 ≠ 0` in `ZMod L` (i.e. `L ≥ 3`), for any measure `μ` with `IsHaarS3 μ` and every field `W` on the links outside `I*` with `‖W e‖ = 1`: integrating the star links gives `∫ exp(−S_W) = exp(−Φ(W))` | `WilsonOneLink.integral_star_links` (`OneLink.LatticeGaugeOneLink`) | [Lean] | 偶数周期 L ≥ 3 の 4 次元トーラスで、単位四元数上の任意の Haar 確率測度について、I* の外の単位ノルムの場に対し、星のリンクの積分は exp(−Φ) に因子分解する |
| Thm 1(ii) | Same lattice (`2 ∣ L`, `3 ≤ L`); for every `U, X` with `‖U e‖ = 1`, `(X e).re = 0` and **every real β**: `−27β² Σ‖X e‖² ≤ (d²/dτ²) Φ(pert U X τ)` at `τ = 0` | `StaplePerturbation.hess_gauge` (`OneLink.LatticeGaugeOneLink`) | [Lean] | 偶数周期 L ≥ 3 で、単位ノルムの配置と純虚の接ベクトルの任意の組と任意の β について、Φ の測地線に沿う二階微分は −27β²Σ‖X‖² 以上 |
| Thm 4.1 | `E` a real inner-product space, `s_i` unit (`i = 1..6`), `M = Σ s_j`, `‖u_i‖² ≤ ‖a_i+b_i+c_i‖²`, `‖v_i‖² ≤ ‖M‖² − ⟨s_i,M⟩²` ⇒ the star inequality with constant 18 | `StarInequality.star_S` (`OneLink.LatticeGaugeOneLink`) | [Lean] | 六本の単位ベクトルと仮定の二つのノルム不等式のもとで、星の不等式（定数 18）が成り立つ |
| Lemma 5.1 | `L` even: every plaquette contains exactly one link of `I*`; `2 ≠ 0` in `ZMod L`: each link not in `I*` lies in exactly six stars, and the 18 slots of a star are distinct | `CompleteFamilyLattice.plaq_unique`, `.star_count`, `.Es_card` | [Lean] | 偶数周期で各プラケットは I* のリンクをちょうど一本含み、2 ≠ 0 のとき I* の外のリンクはちょうど六つの星に属し、星の 18 個の枠は相異なる |
| Thm 2 | On `ℤ^d` (no periodicity assumed), `5 ≤ d` ⇒ no family `J` with every plaquette containing exactly one link | `PerfectFamily.no_perfectZ_of_five` (`OneLink.PerfectFamily`) | [Lean] | 周期を仮定しない ℤ^d で、d ≥ 5 なら完全な族は存在しない |
| Thm 2 (ex.) | Complete families on `ℤ^d` exist for `d = 2, 3, 4` | `PerfectFamily.perfect_I2`, `perfect_I3`, `perfect_I4` (`decide`) | [Lean] | d = 2, 3, 4 では完全な族が存在する（具体例を decide で検査） |
| Thm 2′(i) = 6.6(ii) | On `(ℤ/L)^d`, `L ≥ 1`, `2 ≤ d`: a complete family of links exists **iff** `d ≤ 4` and `2 ∣ L` | `PerfectFamily.perfectK_one_iff` (`OneLink.PerfectFamilyEdges`) | [Lean] | 周期 L ≥ 1・d ≥ 2 のトーラスで、リンクの完全な族が存在するのは d ≤ 4 かつ L が偶数のとき、かつそのときに限る |
| Thm 6.4(i) | `k + 1 ≤ d`, `L ≥ 1`, `I` complete family of `k`-cells ⇒ `2(k+1)·|I| = C(d,k)·L^d`, density exactly `1/(2(k+1))` | `PerfectFamily.card_supportK_of_perfectK`, `density_of_perfectK` (`OneLink.PerfectFamilyPeriodic`) | [Lean] | k+1 ≤ d・L ≥ 1 で、k 胞体の完全な族の大きさは C(d,k)L^d/(2(k+1))、密度はちょうど 1/(2(k+1)) |
| Thm 6.4(ii) | Same hypotheses; for every `(k+1)`-set `T` of directions: `2·Σ_{ν∈T} |I_{T∖ν}| = L^d` | `PerfectFamily.two_mul_sum_card_slice` (`OneLink.PerfectFamilyPeriodic`) | [Lean] | 同じ仮定で、方向の (k+1) 元集合ごとに切片の和の二倍が L^d に等しい |
| Thm 6.4(iii) | Same hypotheses ⇒ `2(k+1) ∣ C(d,k)·L^d` and `2 ∣ L` | `PerfectFamily.two_mul_succ_dvd_of_perfectK`, `two_dvd_of_perfectK` | [Lean] | 同じ仮定で 2(k+1) は C(d,k)L^d を割り、L は偶数 |
| Thm 6.5 | `1 ≤ k`, `k + 1 ≤ d`, `L ≥ 1`, complete family of `k`-cells ⇒ `d ≤ 3k+1` (any period) | `PerfectFamily.perfectK_d_le`, `no_perfectK_of_lt` (`OneLink.PerfectFamilyPeriodic`) | [Lean] | k ≥ 1・k+1 ≤ d・任意の周期で、k 胞体の完全な族があれば d ≤ 3k+1 |
| Thm 6.5 (sharp) | `2 ∣ L` ⇒ a complete family of links exists in `d = 4 = 3·1+1` | `PerfectFamily.bound_sharp_k1` (`OneLink.PerfectFamilyEdges`) | [Lean] | L が偶数なら d = 4 でリンクの完全な族が存在し、k = 1 で上界は達成される |
| Thm 6.6(i) | `L` odd, `k + 1 ≤ d` (any `k`, `k ≥ 1` not needed) ⇒ no complete family of `k`-cells | `PerfectFamily.no_perfectK_of_odd` | [Lean] | 周期が奇数なら、どの k・どの d ≥ k+1 でも完全な族は存在しない |
| Thm 6.6(iii) | `k = 2`, `d = 4`: a complete family exists iff `2 ∣ L` | `PerfectFamily.perfectK_k2_d4_iff` | [Lean] | k = 2・d = 4 では、完全な族の存在は L が偶数であることと同値 |
| Thm 6.6(iv) | `d = k + 2`, every `k`: a complete family exists at period 2, and lifts to every even period | `PerfectFamily.exists_perfect` (`OneLink.PerfectFamilyConstruction`) with `perfectK_of_perfect` (`OneLink.PerfectFamilyPeriodic`) | [Lean] | d = k+2 ではすべての k で周期 2 の完全な族があり、任意の偶数周期へ持ち上がる |
| Thm 6.6(v) | `k = 4, d = 9` requires `10 ∣ L`; `k = 5, d = 8` requires `6 ∣ L` | `PerfectFamily.no_perfectK_k4_d9_ten`, `no_perfectK_k5_d8_six` | [Lean] | k = 4・d = 9 では 10 ∣ L が、k = 5・d = 8 では 6 ∣ L が必要 |
| Thm 6.2 | `(ℤ/L)^d`, `I` with every plaquette containing **at most** one link ⇒ `|I| ≤ L^d`; for `0 < d`, density `≤ 1/d` | `PlaquettePacking.card_edgeSet_le`, `density_le_rat` (`OneLink.PlaquetteCounting`) | [Lean] | 各プラケットが高々一本しか含まない族の大きさは頂点数以下で、d > 0 なら密度は 1/d 以下 |
| Cor 3(a) | `β < √(2/27)`, `K′ = 2 − 27β²`: the marginal `μ′ ∝ exp(−Φ)` has Bakry–Émery curvature `≥ K′`, hence LSI and Poincaré uniformly in volume and boundary condition | — | [paper] (standard facts: bi-invariant geodesics, Ric = 2 on S³, Bakry–Émery) | β < √(2/27) で周辺測度の Bakry–Émery 曲率は K′ 以上、よって体積と境界条件に一様な対数 Sobolev・Poincaré 不等式（紙・標準的事実に依拠） |
| Cor 3(b) | Same `β`: uniqueness of the infinite-volume Wilson measure and exponential decay of covariances with `m = 2K′/(3e⁴A)`, `A ≤ β²(99 + 243β²)` | — | [paper, sketch] (the argument of [SZZ, §4] transported; not written out line by line) | 同じ β で無限体積測度の一意性と共分散の指数減衰（紙の略証のみ・[SZZ, §4] の移植で、逐行には書いていない） |

What is not claimed (§10 of the note): nothing about the continuum limit or the Clay problem; the bound
`d ≤ 3k+1` is not claimed sharp for `k ≥ 2`, and §6 is not a classification; the sharper arithmetic test
via Gottlieb's theorem is on paper only. 主張しないこと：連続極限・Clay 問題については何も主張しない。
k ≥ 2 で d ≤ 3k+1 が最良とは主張せず、§6 は分類ではない。Gottlieb の定理による強い判定は紙のみ。

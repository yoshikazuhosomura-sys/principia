import Mathlib

/-!
# 分裂の異常素点での高さ行列の `mod p` の形——階数は 2 以下

前のファイル（`PadicHeightValuation9`）は**非分裂**の場合を扱った。そこでは
`p·h_p` の `mod p` の零点集合が**ちょうど**超平面 `Λ_0` で、双線形形式は `c·χ⊗χ`（階数 1）になった。

本ファイルは**分裂**の場合である。分裂では高さ行列 `M_Λ` 自身が `Z_p` 整で（主定理 (i)）、
紙にある事実は一つだけになる：

* `P ∈ Λ_0` なら `v_p(h_p(P)) ≥ 1`（補題 2）。

すなわち二次形式 `x ↦ h_p(x) mod p` は超平面 `Λ_0/pΛ` の上で消える——が、そこ**だけ**で
消えるとは限らない。この一方向の仮定だけから出るのが主定理

  `bilin_eq_of_vanishing_on_hyperplane` :  `B x y = B x v · χ y + χ x · B y v − B v v · χ x χ y`

である。右辺は `χ` と一次形式 `B(·, v)` の二つだけで書けているから、
`B` の階数は **2 以下**（`bilin_zero_of_mem_radical`・`gram_det_three_eq_zero`）。
非分裂の「ちょうど 1」に対して分裂は「2 以下」であり、
`ρ_1 := rank (M_Λ mod p) ∈ {0,1,2}` が `v_p(Reg_p) ≥ r − ρ_1` を与える。

残りは記帳と、分裂側の定数 `a = h_p(e₁) mod p` を**二次の Fermat 商**に結びつける算術の段である。
分裂では一次の Fermat 商 `λ` が消える（系 D）ので、二段目
`q⁽²⁾(u) := (u^{p−1} − 1)/p²` が定義でき、その部分群の上で加法的になる
（`fermatQuot2_add`）。`ω² ≡ φ³ (mod p³)` からは一段目と同じ関係 `2B ≡ 3A (mod p)` が出る
（`dvd_three_mul_sub_two_mul_two`）。

幾何・`p` 進解析（`σ` 関数・除法多項式・Vélu・高さの対自身）は Lean に載っていない。
載っているのは**線形代数・行列式の記帳・合同の算術**である。
-/

namespace PadicHeight

/-! ## 1. 二次形式が超平面の上で消えるなら、双線形形式の階数は 2 以下 -/

/-- **主定理（分裂版）。** 標数 `≠ 2` の体上の対称双線形形式 `B` が、線形形式 `χ` の核の上で
`B x x = 0` を満たすならば、`B` は `χ` と一次形式 `B(·, v)` だけで書ける：

> `B x y = B x v * χ y + χ x * B y v − B v v * (χ x * χ y)`。

（適用：`B = h_p mod p`、`χ` は還元指標、`v` は `χ v = 1` なる点。分裂のとき
`M_Λ mod p` はこの形であり、`Λ_0` 上で消えるが階数は 1 とは限らない。） -/
theorem bilin_eq_of_vanishing_on_hyperplane {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (h2 : (2 : K) ≠ 0) (B : V →ₗ[K] V →ₗ[K] K) (hsymm : ∀ x y, B x y = B y x)
    (χ : V →ₗ[K] K) (v : V) (hv : χ v = 1)
    (hzero : ∀ x, χ x = 0 → B x x = 0) :
    ∀ x y, B x y = B x v * χ y + χ x * B y v - B v v * (χ x * χ y) := by
  -- 核の上では双線形形式そのものが消える（標数 ≠ 2）
  have hWW : ∀ w w' : V, χ w = 0 → χ w' = 0 → B w w' = 0 := by
    intro w w' hw hw'
    have hs : χ (w + w') = 0 := by simp [hw, hw']
    have h0 : B (w + w') (w + w') = 0 := hzero _ hs
    have hexp : B (w + w') (w + w') = B w w + B w' w' + 2 * B w w' := by
      simp only [map_add, LinearMap.add_apply]
      rw [hsymm w' w]
      ring
    rw [hexp, hzero w hw, hzero w' hw'] at h0
    have h2b : (2 : K) * B w w' = 0 := by linear_combination h0
    rcases mul_eq_zero.1 h2b with h | h
    · exact absurd h h2
    · exact h
  intro x y
  have hwx : χ (x - χ x • v) = 0 := by simp [hv]
  have hwy : χ (y - χ y • v) = 0 := by simp [hv]
  have hxy0 : B (x - χ x • v) (y - χ y • v) = 0 := hWW _ _ hwx hwy
  have hexp : B (x - χ x • v) (y - χ y • v)
      = B x y - χ y * B x v - χ x * B v y + χ x * χ y * B v v := by
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hexp] at hxy0
  have hvy : B v y = B y v := hsymm v y
  rw [hvy] at hxy0
  linear_combination hxy0

/-- **階数 2 以下、根基の形。** 上の形の `B` について、`χ x = 0` かつ `B x v = 0` ならば
`x` は `B` の根基に入る。すなわち `ker χ ∩ ker B(·,v) ⊆ rad B` で、`rank B ≤ 2`。 -/
theorem bilin_zero_of_mem_radical {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {B : V →ₗ[K] V →ₗ[K] K} {χ : V →ₗ[K] K} {v : V}
    (hB : ∀ x y, B x y = B x v * χ y + χ x * B y v - B v v * (χ x * χ y))
    (x : V) (hx1 : χ x = 0) (hx2 : B x v = 0) : ∀ y, B x y = 0 := by
  intro y
  rw [hB x y, hx1, hx2]
  ring

/-- **階数 2 以下、行列式の形。** 上の形の `B` については、任意の三点の Gram 行列式が消える
（`Matrix.det_fin_three` を展開した式をそのまま書いてある）。 -/
theorem gram_det_three_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {B : V →ₗ[K] V →ₗ[K] K} {χ : V →ₗ[K] K} {v : V}
    (hB : ∀ x y, B x y = B x v * χ y + χ x * B y v - B v v * (χ x * χ y)) (x y z : V) :
    B x x * (B y y * B z z - B y z * B z y)
      - B x y * (B y x * B z z - B y z * B z x)
      + B x z * (B y x * B z y - B y y * B z x) = 0 := by
  rw [hB x x, hB x y, hB x z, hB y x, hB y y, hB y z, hB z x, hB z y, hB z z]
  ring

/-! ## 2. 行列式の記帳 -/

/-- **階数 2 の枡（`r = 2`）。** `Λ_0` の上で高さが `p` で割れる（`M₂₂ = p·c`）とき、
`p ∤ Reg_p` ⟺ `p ∤ M₁₂`。すなわち `v_p(Reg_p) = 0 ⟺ ρ_1 = 2`。 -/
theorem det_two_dvd_iff {p a b c : ℤ} (hp : Prime p) :
    p ∣ a * (p * c) - b * b ↔ p ∣ b := by
  constructor
  · intro h
    have h1 : p ∣ a * (p * c) := ⟨a * c, by ring⟩
    have h2 : p ∣ b * b := by
      have : b * b = a * (p * c) - (a * (p * c) - b * b) := by ring
      rw [this]
      exact dvd_sub h1 h
    exact (hp.dvd_mul.1 h2).elim id id
  · intro h
    have h1 : p ∣ a * (p * c) := ⟨a * c, by ring⟩
    exact dvd_sub h1 (h.mul_left b)

/-- **一般の階数の下界。** `M` の `(i,j)` 成分が `i ≠ 0` かつ `j ≠ 0` のとき `p` で割れるなら、
`p^m ∣ det M`（`M` は `(m+2)×(m+2)`）。Leibniz 展開の各項で「割れない」因子は
行 `0` と列 `0` の二つだけだから、残る `m` 個が `p` を出す。
適用：分裂の枡で `Λ_0 × Λ_0` ブロックが `pZ_p` に入る ⟹ `v_p(Reg_p) ≥ r − 2`。 -/
theorem pow_dvd_det_of_offdiag_block {R : Type*} [CommRing R] {m : ℕ} (p : R)
    (M : Matrix (Fin (m + 2)) (Fin (m + 2)) R)
    (h : ∀ i j : Fin (m + 2), i ≠ 0 → j ≠ 0 → p ∣ M i j) :
    p ^ m ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  refine Finset.dvd_sum ?_
  intro σ _
  refine Dvd.dvd.mul_left ?_ _
  set S : Finset (Fin (m + 2)) := {0, σ.symm 0} with hS
  have hSc : S.card ≤ 2 := by
    rw [hS]
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  have hcard : m ≤ (Finset.univ \ S).card := by
    have h3 : (Finset.univ \ S).card + S.card = m + 2 := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
      simpa using hh
    omega
  have hdvd : p ^ (Finset.univ \ S).card ∣ ∏ i ∈ Finset.univ \ S, M (σ i) i := by
    rw [← Finset.prod_const]
    refine Finset.prod_dvd_prod_of_dvd _ _ ?_
    intro i hi
    have hnot : i ∉ S := (Finset.mem_sdiff.1 hi).2
    have hi1 : i ≠ 0 := by
      intro h0
      exact hnot (by rw [hS, h0]; exact Finset.mem_insert_self _ _)
    have hi2 : σ i ≠ 0 := by
      intro h0
      have hii : i = σ.symm 0 := by rw [← h0]; simp
      exact hnot (by rw [hS, hii]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    exact h _ _ hi2 hi1
  have hsplit : (∏ i ∈ Finset.univ \ S, M (σ i) i) ∣ ∏ i, M (σ i) i :=
    ⟨∏ i ∈ S, M (σ i) i, (Finset.prod_sdiff (Finset.subset_univ S)).symm⟩
  exact dvd_trans (dvd_trans (pow_dvd_pow p hcard) hdvd) hsplit

/-! ## 3. 二次の Fermat 商 -/

/-- **二次の Fermat 商は加法的**（一次が消える単数のなす部分群の上で）。
`u^{p−1} = 1 + p²a`・`v^{p−1} = 1 + p²b` なら `(uv)^{p−1} = 1 + p²(a + b + p²ab)`、
すなわち `q⁽²⁾(uv) ≡ q⁽²⁾(u) + q⁽²⁾(v) (mod p)`。 -/
theorem fermatQuot2_add {R : Type*} [CommRing R] (p a b u v : R) (n : ℕ)
    (hu : u ^ n = 1 + p ^ 2 * a) (hv : v ^ n = 1 + p ^ 2 * b) :
    (u * v) ^ n = 1 + p ^ 2 * (a + b + p ^ 2 * (a * b)) := by
  rw [mul_pow, hu, hv]
  ring

/-- **二段目でも `2B ≡ 3A`。** `p ∣ a₁`・`e ≥ 2` の模型では `ω² ≡ φ³ (mod p³)`（各項の付値 ≥ 3）。
`φ^{p−1} = 1 + p²A`・`ω^{p−1} = 1 + p²B` と合わせると、一段目と同じ関係が二段目にも出る。
これが `q⁽²⁾(α/β) = −λ⁽²⁾`（`λ⁽²⁾ := A/2`）の算術の芯である。 -/
theorem dvd_three_mul_sub_two_mul_two {p A B : ℤ} (hp : p ≠ 0)
    (h : p ^ 3 ∣ (1 + p ^ 2 * B) ^ 2 - (1 + p ^ 2 * A) ^ 3) : p ∣ 3 * A - 2 * B := by
  obtain ⟨k, hk⟩ := h
  have key : p ^ 2 * (2 * B - 3 * A + p ^ 2 * (B ^ 2 - 3 * A ^ 2) - p ^ 4 * A ^ 3)
      = p ^ 2 * (p * k) := by linear_combination hk
  have hY : 2 * B - 3 * A + p ^ 2 * (B ^ 2 - 3 * A ^ 2) - p ^ 4 * A ^ 3 = p * k :=
    mul_left_cancel₀ (pow_ne_zero 2 hp) key
  exact ⟨-(k - p * (B ^ 2 - 3 * A ^ 2) + p ^ 3 * A ^ 3), by linear_combination -hY⟩

/-- 分裂側の定数の記帳：`n² · a = 2 λ⁽²⁾` で `p ∤ n` なら `a = 2 λ⁽²⁾ / n²`。 -/
theorem split_const_eq {p : ℕ} [Fact p.Prime] {n a l : ZMod p} (hn : n ≠ 0)
    (h : n ^ 2 * a = 2 * l) : a = 2 * l / n ^ 2 := by
  field_simp
  linear_combination h

end PadicHeight

#print axioms PadicHeight.bilin_eq_of_vanishing_on_hyperplane
#print axioms PadicHeight.bilin_zero_of_mem_radical
#print axioms PadicHeight.gram_det_three_eq_zero
#print axioms PadicHeight.det_two_dvd_iff
#print axioms PadicHeight.pow_dvd_det_of_offdiag_block
#print axioms PadicHeight.fermatQuot2_add
#print axioms PadicHeight.dvd_three_mul_sub_two_mul_two
#print axioms PadicHeight.split_const_eq
